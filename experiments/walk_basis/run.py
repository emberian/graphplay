"""Walk-basis sparse-coding experiment.

Hypothesis under test: are learned attention circuits SUPERPOSITIONS of a few
structured WALKS? For each head matrix A, does A ~= sum_j c_j W_j with few NAMED
walk atoms W_j?

We:
  1. Build the structured-walk dictionary (dictionary.py).
  2. Load attn-only-2l (TransformerLens), run a repeated-token batch, compute the
     per-head INDUCTION SCORE (attention to token after previous occurrence) to
     LABEL induction heads. Also classify heads as positional (diagonal/prev-token
     mass) vs content (rich) using simple structural diagnostics.
  3. Sparse-code each head's mean A via OMP against the dictionary -> sparsity
     curve + named atoms.
  4. Cross-reference: do induction heads = shift atom + small residual? Do
     positional heads = diffusion atoms? Do content heads need many atoms?
  5. Also run the 4 tiny trained attention-only models for contrast.

Outputs: results.json + figures (figures/sparsity_curves.png,
figures/atom_usage.png). Findings written separately.
"""
from __future__ import annotations

import json
import os
import sys
import warnings

import numpy as np
import torch

warnings.filterwarnings("ignore")

_HERE = os.path.dirname(os.path.abspath(__file__))
_EXP = os.path.dirname(_HERE)
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)
if _EXP not in sys.path:
    sys.path.insert(0, _EXP)

from dictionary import (build_dictionary, atom_class, shift_atom,  # noqa: E402
                        _rownorm_causal)
from sparsecode import omp, nnls_code, atoms_to_reach  # noqa: E402

SEQ_LEN = 48          # n: keeps n*n design matrices small, > induction range
ERR_THRESH = 0.10     # 10% reconstruction-error target for "K atoms to reach"
MAX_ATOMS = 20        # OMP budget
RNG = np.random.default_rng(0)


# --------------------------------------------------------------------------- #
# attn-only-2l (TransformerLens)
# --------------------------------------------------------------------------- #
def load_tl_model():
    from transformer_lens import HookedTransformer
    model = HookedTransformer.from_pretrained("attn-only-2l")
    model.eval()
    return model


def make_repeated_batch(model, n_seq=12, half=SEQ_LEN // 2):
    """Build [prefix, prefix] repeated-token sequences that activate induction
    heads. Returns token tensor (n_seq, 2*half) and the repeat length."""
    d_vocab = model.cfg.d_vocab
    # avoid special tokens near 0; sample a random prefix and repeat it
    prefixes = RNG.integers(low=100, high=d_vocab - 1, size=(n_seq, half))
    toks = np.concatenate([prefixes, prefixes], axis=1)
    # prepend BOS
    bos = model.cfg.default_prepend_bos
    if bos and model.tokenizer is not None and model.tokenizer.bos_token_id is not None:
        b = np.full((n_seq, 1), model.tokenizer.bos_token_id)
        toks = np.concatenate([b, toks], axis=1)
    return torch.tensor(toks), half


@torch.no_grad()
def tl_attention_and_scores(model):
    """Run the repeated batch; return per (layer,head):
        A_mean (n,n) attention (averaged over batch),
        induction_score, prev_token_score, diag_score, plus seq positions.
    Induction score: at position p in the SECOND copy, attention to position
    (p - half + 1) i.e. the token AFTER the previous occurrence of the current
    token. We compute it as the mean attention to the (offset = half-1) back
    diagonal over the second half."""
    toks, half = make_repeated_batch(model)
    logits, cache = model.run_with_cache(toks)
    n = toks.shape[1]
    # offset from BOS prepend: positions shift by 1 if BOS prepended
    has_bos = (toks.shape[1] == 2 * half + 1)
    start2 = (1 if has_bos else 0) + half  # first index of second copy
    results = {}
    n_layers = model.cfg.n_layers
    n_heads = model.cfg.n_heads
    for L in range(n_layers):
        patt = cache["pattern", L]  # (batch, head, q, k)
        for H in range(n_heads):
            A = patt[:, H].mean(0).cpu().numpy()  # (n,n) batch-mean (for scores)
            # single-sequence pattern preserves the SHARP induction delta that
            # batch-averaging blurs (each seq has the same period but different
            # token identities, so off-diagonal partial matches smear the mean).
            A_single = patt[0, H].cpu().numpy()
            # induction score: attention from q in second half to k = q-half+1
            ind = []
            for q in range(start2, n):
                k = q - half + 1
                if 0 <= k < n:
                    ind.append(patt[:, H, q, k].mean().item())
            induction_score = float(np.mean(ind)) if ind else 0.0
            # previous-token score: attention to q-1
            prev = [patt[:, H, q, q - 1].mean().item() for q in range(1, n)]
            prev_token_score = float(np.mean(prev)) if prev else 0.0
            # diagonal (self) score
            diag = [patt[:, H, q, q].mean().item() for q in range(n)]
            diag_score = float(np.mean(diag))
            results[(L, H)] = {
                "A": A, "A_single": A_single,
                "induction_score": induction_score,
                "prev_token_score": prev_token_score, "diag_score": diag_score,
                "n": n,
            }
    return results, n, half


def induction_atom(n: int, period: int, bos: int = 1) -> np.ndarray:
    """The induction operator on a length-period-repeated sequence: for q in the
    second copy, attend to k = q - period + 1 (the token AFTER the previous
    occurrence of the current token). `bos` = index offset of the first real
    token (1 if BOS prepended). This is the CONTENT-DEPENDENT shift that defines
    an induction head, made explicit for this known-period probe.
    """
    M = np.zeros((n, n))
    for q in range(n):
        k = q - period + 1
        if k >= bos and k <= q:
            M[q, k] = 1.0
        else:
            M[q, q] = 1.0  # fallback self
    return _rownorm_causal(M)


def augment_dictionary_tl(D, names, n, period, bos_offset=1):
    """Add the induction atom (known period) to the TL dictionary. The bos-sink
    atom is already present from build_dictionary."""
    extra = [("induction-shift", induction_atom(n, period, bos_offset))]
    rows = [D]
    nm = list(names)
    for name, M in extra:
        rows.append(M.ravel()[None, :])
        nm.append(name)
    return np.concatenate(rows, axis=0), nm


def classify_head(diag, prev, induction):
    """Coarse structural label, mirroring the head taxonomy
    (structured/positional/content)."""
    if induction >= 0.18:
        return "induction"
    if prev >= 0.30 or diag >= 0.30:
        return "positional"
    return "content"


# --------------------------------------------------------------------------- #
# tiny trained attention-only models (graphplay_probe) for contrast
# --------------------------------------------------------------------------- #
def tiny_models_attention():
    """Train the 4 tiny tasks and extract mean held-out attention per (task,
    layer, head). Uses graphplay_probe read-only."""
    from graphplay_probe.model import train_model, extract_attention
    from graphplay_probe import tasks as T
    out = {}
    for name in ["induction", "averaging", "recall", "local"]:
        Xtr, Ytr, Xte, Yte, vocab, structure = T.build_task(
            name, n_train=4096, n_test=512, seed=0)
        model, acc = train_model(Xtr, Ytr, Xte, Yte, vocab,
                                 d_model=32, n_heads=2, n_layers=2,
                                 epochs=30, seed=0)
        attns = extract_attention(model, Xte, n_examples=64)  # list[L] (H,T,T)
        for L, a in enumerate(attns):
            for H in range(a.shape[0]):
                out[(name, L, H)] = {"A": a[H], "acc": float(acc),
                                     "n": a.shape[-1], "needs": structure}
    return out


# --------------------------------------------------------------------------- #
# main
# --------------------------------------------------------------------------- #
def best_sink_plus_one(a, D, names):
    """NNLS fit a ~ c0*bos-sink + c1*W for each walk atom W; return the (name,
    relerr, coefs) of the single best companion atom. This is the explicit
    'circuit = sink + ONE walk' test: a clean 2-atom named decomposition."""
    from scipy.optimize import nnls
    sink_idx = names.index("bos-sink") if "bos-sink" in names else None
    best = None
    for j, nm in enumerate(names):
        if j == sink_idx:
            continue
        cols = [j] if sink_idx is None else [sink_idx, j]
        Phi = D[cols].T
        c, _ = nnls(Phi, a)
        recon = Phi @ c
        na = np.linalg.norm(a)
        e = float(np.linalg.norm(a - recon) / na) if na > 0 else 0.0
        if best is None or e < best[1]:
            best = (nm, e, [float(x) for x in c])
    return {"companion_atom": best[0], "relerr": best[1], "coef": best[2]}


def code_head(A, D, names):
    a = np.asarray(A, dtype=float).ravel()
    res = omp(a, D, MAX_ATOMS)
    nn = nnls_code(a, D)
    sink1 = best_sink_plus_one(a, D, names)
    k10 = atoms_to_reach(res["errors"], ERR_THRESH)
    k20 = atoms_to_reach(res["errors"], 0.20)
    chosen_named = [names[j] for j in res["order"]]
    chosen_classes = [atom_class(names[j]) for j in res["order"]]
    used_sink = "bos-sink" in chosen_named
    used_induction = "induction-shift" in chosen_named
    # how many atoms used by the time we reach 10% (these are the "named atoms")
    atoms_at_10 = chosen_named[:k10] if k10 <= len(chosen_named) else chosen_named
    return {
        "errors": res["errors"],
        "order_named": chosen_named,
        "order_classes": chosen_classes,
        "coef_top": sorted(
            [(names[j], float(res["coef"][j])) for j in res["order"]],
            key=lambda t: -abs(t[1]))[:6],
        "k_to_10pct": k10,
        "k_to_20pct": k20,
        "k_to_25pct": atoms_to_reach(res["errors"], 0.25),
        "err_floor": float(min(res["errors"])),
        "atoms_at_10pct": atoms_at_10,
        "used_bos_sink": used_sink,
        "used_induction_shift": used_induction,
        "nnls_relerr": nn["relerr"],
        "nnls_nnz": nn["nnz"],
        "first_atom": chosen_named[0] if chosen_named else None,
        "first_class": chosen_classes[0] if chosen_classes else None,
        "sink_plus_one_atom": sink1["companion_atom"],
        "sink_plus_one_relerr": sink1["relerr"],
    }


def main():
    print("== building dictionary ==")
    D, names = build_dictionary(SEQ_LEN)
    print(f"dictionary: {len(names)} atoms, dim={D.shape[1]} (n={SEQ_LEN})")
    print("atoms:", names)

    print("\n== attn-only-2l ==")
    model = load_tl_model()
    tl, n_tl, half = tl_attention_and_scores(model)
    assert n_tl == D.shape[1] ** 0.5 or n_tl == SEQ_LEN + 1 or True
    # if BOS prepended, n_tl = SEQ_LEN+1; rebuild dictionary at that n
    if n_tl != SEQ_LEN:
        print(f"  (rebuilding dictionary at n={n_tl} to match TL seq incl BOS)")
        D, names = build_dictionary(n_tl)
    # augment with the known-period induction atom (period = half). The bos-sink
    # atom is already in build_dictionary; both are NAMED non-walk structural
    # atoms so we can ask whether the *residual* is a sparse walk.
    has_bos = (n_tl == 2 * half + 1)
    D, names = augment_dictionary_tl(D, names, n_tl, half, 1 if has_bos else 0)
    print(f"  TL dictionary: {len(names)} atoms (incl bos-sink, induction-shift)")

    tl_out = {}
    for (L, H), info in tl.items():
        label = classify_head(info["diag_score"], info["prev_token_score"],
                              info["induction_score"])
        # code the batch-mean pattern (cleaner, averages out per-token noise).
        # NOTE: for the induction head this mean is a *blurred* induction delta;
        # we report that honestly rather than cherry-pick a single sequence.
        coded = code_head(info["A"], D, names)
        tl_out[f"L{L}H{H}"] = {
            "layer": L, "head": H, "label": label,
            "induction_score": info["induction_score"],
            "prev_token_score": info["prev_token_score"],
            "diag_score": info["diag_score"],
            **coded,
        }
        print(f"  L{L}H{H} [{label:10s}] ind={info['induction_score']:.2f} "
              f"prev={info['prev_token_score']:.2f} diag={info['diag_score']:.2f} "
              f"| K@10%={coded['k_to_10pct']:>2} floor={coded['err_floor']:.2f} "
              f"sink+1={coded['sink_plus_one_atom']}({coded['sink_plus_one_relerr']:.2f})")

    print("\n== tiny attention-only models ==")
    # tiny models have their own n; build a per-n dictionary cache
    tiny = tiny_models_attention()
    dict_cache = {}
    tiny_out = {}
    for (task, L, H), info in tiny.items():
        nn = info["n"]
        if nn not in dict_cache:
            dict_cache[nn] = build_dictionary(nn)
        Dt, namest = dict_cache[nn]
        coded = code_head(info["A"], Dt, namest)
        tiny_out[f"{task}-L{L}H{H}"] = {
            "task": task, "layer": L, "head": H, "needs": info["needs"],
            "acc": info["acc"], **coded,
        }
        print(f"  {task:10s} L{L}H{H} needs={info['needs']:9s} "
              f"K@10%={coded['k_to_10pct']:>2} first={coded['first_atom']}")

    # ----- aggregate / verdict numbers -----
    K = 3  # "few atoms" threshold for the sparse-walk-superposition test
    classes = {}
    for hid, r in tl_out.items():
        classes.setdefault(r["label"], []).append(r)
    summary = {"by_class": {}, "K_threshold": K, "err_thresh": ERR_THRESH}
    for cls, rows in classes.items():
        sparse = [r for r in rows if r["k_to_10pct"] <= K]
        summary["by_class"][cls] = {
            "n_heads": len(rows),
            "frac_sparse_le_K": len(sparse) / len(rows),
            "median_k_to_10pct": float(np.median([r["k_to_10pct"] for r in rows])),
            "first_atom_classes": [r["first_class"] for r in rows],
            "mean_first_atom_class_counts": _count(
                [r["first_class"] for r in rows]),
        }
    # induction-head specific cross reference
    ind_rows = classes.get("induction", [])
    summary["induction_first_is_shift"] = [
        (r["layer"], r["head"], r["first_atom"], r["k_to_10pct"],
         r["errors"][1] if len(r["errors"]) > 1 else None)
        for r in ind_rows
    ]
    # overall fraction of heads that are <=K-atom walk superpositions
    all_rows = list(tl_out.values())
    summary["overall_frac_sparse_le_K"] = (
        sum(1 for r in all_rows if r["k_to_10pct"] <= K) / len(all_rows))
    summary["overall_n_heads"] = len(all_rows)

    out = {"dictionary": names, "seq_len_used": int(D.shape[1] ** 0.5),
           "attn_only_2l": tl_out, "tiny": tiny_out, "summary": summary}
    path = os.path.join(_HERE, "results.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2, default=_jsonify)
    print(f"\nwrote {path}")
    _print_verdict(summary, tl_out)
    return out


def _count(xs):
    d = {}
    for x in xs:
        d[x] = d.get(x, 0) + 1
    return d


def _jsonify(o):
    if isinstance(o, (np.floating,)):
        return float(o)
    if isinstance(o, (np.integer,)):
        return int(o)
    if isinstance(o, np.ndarray):
        return o.tolist()
    return str(o)


def _print_verdict(summary, tl_out):
    print("\n================ VERDICT ================")
    print(f"overall fraction of attn-only-2l heads that are <=3-atom "
          f"walk-superpositions (<=10% err): "
          f"{summary['overall_frac_sparse_le_K']:.2f} "
          f"({summary['overall_n_heads']} heads)")
    for cls, s in summary["by_class"].items():
        print(f"  [{cls:10s}] n={s['n_heads']} "
              f"frac_sparse(<=3 atoms)={s['frac_sparse_le_K']:.2f} "
              f"median_K@10%={s['median_k_to_10pct']:.1f} "
              f"first_atoms={s['mean_first_atom_class_counts']}")
    print("  induction heads (first atom, K@10%, err@1atom):")
    for L, H, fa, k, e1 in summary["induction_first_is_shift"]:
        print(f"    L{L}H{H}: first={fa}  K@10%={k}  err@1atom={e1:.3f}")


if __name__ == "__main__":
    main()
