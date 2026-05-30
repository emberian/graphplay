"""Generator probes on SmolLM2-135M.

We run one forward pass on a real text batch, capture per-(layer,head) the
pre-softmax score generator S = q kᵀ/√d (rank ≤ d_head by construction, with
d_head ≈ 64 ≪ n = seq_len) and A = softmax(S). Then probes 1-5.

This is the decisive setting: unlike the tiny model (n≈d), here n ≫ d, so
"generator is low-rank" is a REAL reduction and the question "is it ALSO
equitable / coherent / circulant / sparse-log / butterfly" is sharp.
"""

from __future__ import annotations

import json
import math
import os

import numpy as np
import torch

import gen_probe as gp

HERE = os.path.dirname(os.path.abspath(__file__))
MODEL_ID = "HuggingFaceTB/SmolLM2-135M"

TEXT = (
    "The theory of quantum walks studies the evolution of a particle on a graph. "
    "A continuous-time quantum walk is governed by the adjacency matrix as a "
    "Hamiltonian. Perfect state transfer occurs when the walk moves a state "
    "from one vertex to another with probability one. The equitable partition of "
    "a graph collapses vertices into cells with uniform connection structure, and "
    "the quotient inherits the spectrum. Attention in transformers can be read as "
    "a weighted graph whose generator is the query-key score matrix."
)


def get_S_A(seq_len=64, layers_to_probe=None):
    from transformers import AutoModelForCausalLM, AutoTokenizer

    tok = AutoTokenizer.from_pretrained(MODEL_ID)
    model = AutoModelForCausalLM.from_pretrained(MODEL_ID, torch_dtype=torch.float32)
    model.eval()

    ids = tok(TEXT, return_tensors="pt")["input_ids"][:, :seq_len]
    n = ids.shape[1]

    cfg = model.config
    n_layers = cfg.num_hidden_layers
    n_heads = cfg.num_attention_heads
    n_kv = getattr(cfg, "num_key_value_heads", n_heads)
    d_head = cfg.hidden_size // n_heads
    group = n_heads // n_kv

    if layers_to_probe is None:
        layers_to_probe = [0, n_layers // 2, n_layers - 1]

    # hook q_proj / k_proj outputs per decoder layer
    caps = {}

    def mk(name):
        def hook(mod, inp, out):
            caps[name] = out.detach()
        return hook

    handles = []
    decoder_layers = model.model.layers
    for li in layers_to_probe:
        attn = decoder_layers[li].self_attn
        handles.append(attn.q_proj.register_forward_hook(mk(f"q{li}")))
        handles.append(attn.k_proj.register_forward_hook(mk(f"k{li}")))

    with torch.no_grad():
        model(ids)
    for h in handles:
        h.remove()

    # rotary embeddings: SmolLM2 applies RoPE to q,k. To keep S faithful we apply
    # the model's rotary embedding to the captured q,k before forming qkᵀ.
    # We fetch cos/sin from the rotary module.
    rotary = model.model.rotary_emb
    pos = torch.arange(n).unsqueeze(0)
    # position_ids -> cos,sin
    dummy = torch.zeros(1, n, cfg.hidden_size)
    cos, sin = rotary(dummy, pos)

    def apply_rope(x):  # x: (1,H,T,dh)
        return _apply_rotary(x, cos, sin)

    causal = torch.triu(torch.ones(n, n), diagonal=1).bool()

    out = {}
    for li in layers_to_probe:
        q = caps[f"q{li}"].reshape(1, n, n_heads, d_head).transpose(1, 2)
        k = caps[f"k{li}"].reshape(1, n, n_kv, d_head).transpose(1, 2)
        q = apply_rope(q)
        k = apply_rope(k)
        # expand kv heads to query heads (GQA)
        k = k.repeat_interleave(group, dim=1)
        S_raw = (q @ k.transpose(-1, -2)) / math.sqrt(d_head)  # 1,H,T,T
        S_masked = S_raw.masked_fill(causal, float("-inf"))
        A = torch.softmax(S_masked, dim=-1)
        out[li] = {
            "S_raw": S_raw[0].cpu().numpy(),
            "S_masked": S_masked[0].cpu().numpy(),
            "A": A[0].cpu().numpy(),
            "d_head": d_head,
        }
    out["_meta"] = {"n": n, "n_layers": n_layers, "n_heads": n_heads,
                    "n_kv": n_kv, "d_head": d_head}
    return out


def _rotate_half(x):
    x1, x2 = x[..., : x.shape[-1] // 2], x[..., x.shape[-1] // 2:]
    return torch.cat((-x2, x1), dim=-1)


def _apply_rotary(x, cos, sin):
    cos = cos.unsqueeze(1)  # 1,1,T,dh
    sin = sin.unsqueeze(1)
    return x * cos + _rotate_half(x) * sin


def _finite_S(S_masked):
    finite = S_masked[np.isfinite(S_masked)]
    fill = float(finite.min()) - 10.0 if finite.size else -1e9
    out = S_masked.copy()
    out[~np.isfinite(out)] = fill
    return out


def main(seq_len=64, heads_per_layer=4):
    data = get_S_A(seq_len=seq_len)
    meta = data.pop("_meta")
    print("meta:", meta)
    results = {"meta": meta, "heads": []}
    for li, layer in data.items():
        H = layer["S_raw"].shape[0]
        n = layer["A"].shape[1]  # (H, T, T) -> T is the matrix dimension
        for hi in range(min(H, heads_per_layer)):
            S_raw = layer["S_raw"][hi]
            S_m = _finite_S(layer["S_masked"][hi])
            A = layer["A"][hi]
            tag = f"L{li}H{hi}"
            r = {
                "tag": tag, "n": n, "d_head": layer["d_head"],
                "rank_S_raw": gp.generator_rank(S_raw),
                "rank_S_masked": gp.generator_rank(S_m),
                "rank_A": gp.generator_rank(A),
                "equitable": gp.equitable_compare(S_m, A),
                "equitable_Sraw": gp.equitable_defect(S_raw),
                "coherent_S": gp.coherent_algebra_probe(S_raw),
                "coherent_A": gp.coherent_algebra_probe(A),
                "tc_S": gp.toeplitz_circulant_defect(S_raw),
                "tc_A": gp.toeplitz_circulant_defect(A),
                "logA": gp.matrix_log_A(A),
                "sparsity_Sraw": gp.sparsity_profile(S_raw, "S_raw"),
                "sparsity_A": gp.sparsity_profile(A, "A"),
            }
            results["heads"].append(r)
            rr = r
            print(f"{tag}: n={n} d={layer['d_head']} | rank S_raw={rr['rank_S_raw']['rank_eps']} "
                  f"A={rr['rank_A']['rank_eps']} | eqS_raw r={rr['equitable_Sraw']['r_cells']} "
                  f"def={rr['equitable_Sraw']['defect_eq']:.2f} | "
                  f"colorsS={rr['coherent_S']['n_colors_natural']} colorsA={rr['coherent_A']['n_colors_natural']} | "
                  f"toepS={rr['tc_S']['toeplitz_defect']:.2f} toepA={rr['tc_A']['toeplitz_defect']:.2f} | "
                  f"logA ok={rr['logA'].get('reliable')} band1={rr['logA'].get('band_w1_mass',-1):.2f}")

    # butterfly on a couple representative heads (expensive at n=64)
    print("=== butterfly (last layer, head 0) ===")
    last = max(k for k in data.keys())
    A = data[last]["A"][0]
    S = data[last]["S_raw"][0]
    bf_A = gp.butterfly_fit(A, n_iter=300)
    bf_S = gp.butterfly_fit(S, n_iter=300)
    results["butterfly_A"] = bf_A
    results["butterfly_S"] = bf_S
    print(f"  A best_err={bf_A['best_err']:.3f} S best_err={bf_S['best_err']:.3f} "
          f"depth={bf_A['depth']} dense={bf_A['dense_params']} per_depth={bf_A['params_per_depth']}")

    out_path = os.path.join(HERE, "smollm_results.json")
    with open(out_path, "w") as f:
        json.dump(_clean(results), f, indent=2)
    print(f"wrote {out_path}")
    return results


def _clean(obj):
    if isinstance(obj, dict):
        return {k: _clean(v) for k, v in obj.items() if k != "partition"}
    if isinstance(obj, (list, tuple)):
        return [_clean(v) for v in obj]
    if isinstance(obj, np.ndarray):
        return obj.tolist() if obj.size <= 80 else f"<ndarray {obj.shape}>"
    if isinstance(obj, (np.floating, np.integer)):
        return obj.item()
    return obj


if __name__ == "__main__":
    main()
