"""Two follow-up probes sharpening the headline.

A. Forced-coarse equitable defect: the exact 1-WL gives all-singletons on
   continuous weights (vacuous). residual_lab forced r cells via spectral
   clustering and measured the defect there. We replicate that on BOTH S and A
   to ask: at a FORCED coarse base, is the generator MORE equitable-compressible
   than A? (defect_eq(S, r) vs defect_eq(A, r) over an r-sweep.)

B. Banded-log sweep: across ALL 30 SmolLM2 layers / all heads, how banded is the
   reliable matrix-log of A? This is the one live "sparse Hamiltonian" signal.
"""

from __future__ import annotations

import json
import math
import os

import numpy as np
import torch

import gen_probe as gp
from graphplay_probe.probe import spectral_partition, quotient_lift
from run_smollm import get_S_A, _finite_S, MODEL_ID, TEXT

HERE = os.path.dirname(os.path.abspath(__file__))


def forced_defect(M: np.ndarray, r: int) -> float:
    norm = float(np.linalg.norm(M)) + 1e-30
    part = spectral_partition(M, r)
    M_eq, _ = quotient_lift(M, part)
    return float(np.linalg.norm(M - M_eq) / norm)


def probe_A_forced_equitable(seq_len=64):
    """For a spread of heads, compare forced-r equitable defect of S vs A."""
    data = get_S_A(seq_len=seq_len)
    data.pop("_meta")
    rs = [2, 4, 8, 16]
    rows = []
    for li, layer in data.items():
        H = layer["S_raw"].shape[0]
        for hi in range(min(H, 4)):
            S = _finite_S(layer["S_masked"][hi])
            A = layer["A"][hi]
            row = {"tag": f"L{li}H{hi}"}
            for r in rs:
                row[f"S_r{r}"] = forced_defect(S, r)
                row[f"A_r{r}"] = forced_defect(A, r)
                # low-rank control: equitable-r lift has rank <= r, so the FAIR
                # baseline for "did equitable beat low-rank" is the rank-r SVD
                # residual of the SAME matrix. If equitable_defect ~ lowrank_resid
                # then the compressibility is JUST low-rank, not equitable.
                row[f"S_lr{r}"] = _lowrank_resid(S, r)
                row[f"A_lr{r}"] = _lowrank_resid(A, r)
            rows.append(row)
    return rs, rows


def _lowrank_resid(M: np.ndarray, k: int) -> float:
    norm = float(np.linalg.norm(M)) + 1e-30
    U, s, Vt = np.linalg.svd(M, full_matrices=False)
    Mk = (U[:, :k] * s[:k]) @ Vt[:k]
    return float(np.linalg.norm(M - Mk) / norm)


def banded_log_all_layers(seq_len=64):
    """Compute matrix-log bandedness of A for ALL layers/heads of SmolLM2."""
    from transformers import AutoModelForCausalLM, AutoTokenizer

    tok = AutoTokenizer.from_pretrained(MODEL_ID)
    model = AutoModelForCausalLM.from_pretrained(
        MODEL_ID, dtype=torch.float32, attn_implementation="eager")
    model.eval()
    ids = tok(TEXT, return_tensors="pt")["input_ids"][:, :seq_len]
    n = ids.shape[1]
    cfg = model.config
    n_heads = cfg.num_attention_heads
    n_kv = getattr(cfg, "num_key_value_heads", n_heads)
    d_head = cfg.hidden_size // n_heads
    group = n_heads // n_kv

    with torch.no_grad():
        out = model(ids, output_attentions=True)
    atts = out.attentions  # tuple[layer] of (1,H,T,T) already softmaxed
    rows = []
    for li, A_layer in enumerate(atts):
        Al = A_layer[0].cpu().numpy()
        for hi in range(Al.shape[0]):
            la = gp.matrix_log_A(Al[hi])
            if la.get("ok") and la.get("reliable"):
                rows.append({
                    "tag": f"L{li}H{hi}",
                    "band_w1": la["band_w1_mass"],
                    "band_w2": la["band_w2_mass"],
                    "rank": la["rank_eps"],
                    "gini": la["gini"],
                    "recon_err": la["recon_err"],
                })
    return rows


def main():
    print("=== A. forced-coarse equitable: S vs A ===")
    rs, rows = probe_A_forced_equitable()
    # aggregate: mean defect per r
    agg = {}
    for r in rs:
        sv = np.mean([row[f"S_r{r}"] for row in rows])
        av = np.mean([row[f"A_r{r}"] for row in rows])
        slr = np.mean([row[f"S_lr{r}"] for row in rows])
        alr = np.mean([row[f"A_lr{r}"] for row in rows])
        agg[r] = {"S_eq": float(sv), "A_eq": float(av),
                  "S_lowrank": float(slr), "A_lowrank": float(alr)}
        print(f"  r={r:2d}: eq(S)={sv:.3f} lowrank(S)={slr:.3f} | "
              f"eq(A)={av:.3f} lowrank(A)={alr:.3f}  "
              f"| equitable beats its own low-rank on S? "
              f"{'YES' if sv < slr - 0.02 else 'no (==low-rank)'}")

    print("=== B. banded matrix-log across all 30 layers ===")
    blog = banded_log_all_layers()
    if blog:
        b1 = np.array([r["band_w1"] for r in blog])
        b2 = np.array([r["band_w2"] for r in blog])
        print(f"  {len(blog)} reliable-log heads of 270")
        print(f"  band_w1 mass: mean={b1.mean():.2f} median={np.median(b1):.2f} "
              f"max={b1.max():.2f} frac>0.5={np.mean(b1>0.5):.2f}")
        print(f"  band_w2 mass: mean={b2.mean():.2f} median={np.median(b2):.2f}")
    else:
        print("  no reliable logs")

    res = {"forced_equitable": {"rs": rs, "agg": agg, "rows": rows},
           "banded_log": blog}
    with open(os.path.join(HERE, "followup_results.json"), "w") as f:
        json.dump(res, f, indent=2)
    print("wrote followup_results.json")
    return res


if __name__ == "__main__":
    main()
