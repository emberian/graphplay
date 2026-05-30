"""Run all generator probes on the trained tiny attention-only models.

For each task we train the tiny model, extract S_raw = qkᵀ/√d (the unmasked score
GENERATOR, rank ≤ d_head), the masked score S_masked, and A = softmax(S_masked).
Then we run probes 1-5 and emit a JSON of per-(task,layer,head) verdicts.
"""

from __future__ import annotations

import json
import os

import numpy as np

from extract_qk import train_task, extract_S_and_A
import gen_probe as gp

HERE = os.path.dirname(os.path.abspath(__file__))

# longer sequences than the task defaults give a cleaner rank-≤-d separation
TASKS = ["induction", "averaging", "recall", "local"]


def _finite_S(S_masked: np.ndarray) -> np.ndarray:
    """Replace -inf (causal mask) with a large-negative finite value so the
    equitable / color / log probes can run. Use min finite minus a margin."""
    finite = S_masked[np.isfinite(S_masked)]
    fill = float(finite.min()) - 10.0 if finite.size else -1e9
    out = S_masked.copy()
    out[~np.isfinite(out)] = fill
    return out


def probe_matrix_pair(S_raw, S_masked, A, d_head, tag):
    """Run probes 1-4 on one head's (S_raw, S_masked, A)."""
    S_m = _finite_S(S_masked)
    res = {
        "tag": tag,
        "d_head": d_head,
        "n": int(A.shape[0]),
        # 1. rank baseline (KNOWN)
        "rank_S_raw": gp.generator_rank(S_raw),
        "rank_S_masked": gp.generator_rank(S_m),
        "rank_A": gp.generator_rank(A),
        # 2. equitable (NEW) — generator vs A
        "equitable": gp.equitable_compare(S_m, A),
        "equitable_Sraw": gp.equitable_defect(S_raw),
        # 3. coherent / color / circulant-toeplitz (NEW)
        "coherent_S": gp.coherent_algebra_probe(S_raw),
        "coherent_A": gp.coherent_algebra_probe(A),
        "tc_S": gp.toeplitz_circulant_defect(S_raw),
        "tc_A": gp.toeplitz_circulant_defect(A),
        # 4. matrix log of A (NEW) — sparse Hamiltonian?
        "logA": gp.matrix_log_A(A),
        "sparsity_Sraw": gp.sparsity_profile(S_raw, "S_raw"),
        "sparsity_A": gp.sparsity_profile(A, "A"),
    }
    return res


def main(epochs=40, n_examples=64, do_butterfly=True):
    all_results = {}
    for task in TASKS:
        print(f"=== training {task} ===")
        model, Xte, acc, structure, vocab = train_task(
            task, epochs=epochs, verbose=False)
        print(f"  acc={acc:.3f}  needs={structure}")
        layers = extract_S_and_A(model, Xte, n_examples=n_examples)
        task_res = {"acc": float(acc), "needs": structure, "heads": []}
        for li, layer in enumerate(layers):
            H = layer["S_raw"].shape[0]
            for hi in range(H):
                tag = f"{task}_L{li}H{hi}"
                r = probe_matrix_pair(
                    layer["S_raw"][hi], layer["S_masked"][hi], layer["A"][hi],
                    layer["d_head"], tag)
                if do_butterfly:
                    # butterfly fit on A and S_raw (one representative head only
                    # done at the driver level to keep cost bounded)
                    pass
                task_res["heads"].append(r)
        all_results[task] = task_res

    # butterfly: run once per task on the most-interesting head (layer 1 head 0),
    # for both A and S_raw — it's the expensive probe.
    print("=== butterfly fits (tiny) ===")
    for task in TASKS:
        model, Xte, acc, structure, vocab = train_task(task, epochs=epochs)
        layers = extract_S_and_A(model, Xte, n_examples=n_examples)
        layer = layers[-1]
        A = layer["A"][0]
        S = layer["S_raw"][0]
        bf_A = gp.butterfly_fit(A, n_iter=300)
        bf_S = gp.butterfly_fit(S, n_iter=300)
        all_results[task]["butterfly_A"] = bf_A
        all_results[task]["butterfly_S"] = bf_S
        print(f"  {task}: butterfly A best_err={bf_A['best_err']:.3f} "
              f"S best_err={bf_S['best_err']:.3f} "
              f"(depth={bf_A['depth']}, dense_params={bf_A['dense_params']}, "
              f"per_depth={bf_A['params_per_depth']})")

    out_path = os.path.join(HERE, "tiny_results.json")
    with open(out_path, "w") as f:
        json.dump(_clean(all_results), f, indent=2)
    print(f"wrote {out_path}")
    return all_results


def _clean(obj):
    """Strip numpy arrays / make JSON-serializable; keep scalars and small lists."""
    if isinstance(obj, dict):
        return {k: _clean(v) for k, v in obj.items() if k != "partition"}
    if isinstance(obj, (list, tuple)):
        return [_clean(v) for v in obj]
    if isinstance(obj, np.ndarray):
        if obj.size <= 64:
            return obj.tolist()
        return f"<ndarray shape={obj.shape}>"
    if isinstance(obj, (np.floating, np.integer)):
        return obj.item()
    return obj


if __name__ == "__main__":
    main()
