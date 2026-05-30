"""Figures for the generator probe."""

from __future__ import annotations

import json
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
FIG = os.path.join(HERE, "figures")
os.makedirs(FIG, exist_ok=True)


def load(name):
    with open(os.path.join(HERE, name)) as f:
        return json.load(f)


def fig_rank_and_equitable():
    """Panel 1: rank(S) vs rank(A) (the known low-rank baseline).
       Panel 2: equitable-vs-lowrank on the generator (the new negative)."""
    sm = load("smollm_results.json")
    fu = load("followup_results.json")
    fig, axes = plt.subplots(1, 3, figsize=(16, 4.5))

    # Panel 1: rank baseline
    tags = [h["tag"] for h in sm["heads"]]
    rS = [h["rank_S_raw"]["rank_eps"] for h in sm["heads"]]
    rA = [h["rank_A"]["rank_eps"] for h in sm["heads"]]
    d = sm["heads"][0]["d_head"]
    n = sm["heads"][0]["n"]
    x = np.arange(len(tags))
    ax = axes[0]
    ax.bar(x - 0.2, rS, 0.4, label="rank(S=QKᵀ)", color="#2b8cbe")
    ax.bar(x + 0.2, rA, 0.4, label="rank(A)", color="#e34a33")
    ax.axhline(d, ls="--", c="k", lw=1, label=f"d_head={d}")
    ax.axhline(n, ls=":", c="gray", lw=1, label=f"n={n}")
    ax.set_xticks(x); ax.set_xticklabels(tags, rotation=90, fontsize=7)
    ax.set_ylabel("numerical rank (ε=1e-2)")
    ax.set_title("PROBE 1 (KNOWN): generator rank ≤ d ≪ A's rank\n"
                 "the low-rank generator story — baseline, confirmed")
    ax.legend(fontsize=8)

    # Panel 2: equitable vs low-rank on S and A (the NEW negative)
    ax = axes[1]
    rs = fu["forced_equitable"]["rs"]
    agg = fu["forced_equitable"]["agg"]
    seq = [str(r) for r in rs]
    Seq = [agg[str(r)]["S_eq"] for r in rs]
    Slr = [agg[str(r)]["S_lowrank"] for r in rs]
    Aeq = [agg[str(r)]["A_eq"] for r in rs]
    ax.plot(seq, Seq, "o-", c="#2b8cbe", label="equitable defect(S)")
    ax.plot(seq, Slr, "s--", c="#2b8cbe", alpha=0.6, label="low-rank resid(S) [control]")
    ax.plot(seq, Aeq, "o-", c="#e34a33", label="equitable defect(A)")
    ax.set_xlabel("forced cells / rank r")
    ax.set_ylabel("relative-Frobenius residual")
    ax.set_title("PROBE 2 (NEW): generator equitable?  NO.\n"
                 "equitable(S) > low-rank(S): equitable adds NOTHING beyond low-rank")
    ax.legend(fontsize=8)

    # Panel 3: color counts S vs A
    ax = axes[2]
    cS = [h["coherent_S"]["n_colors_natural"] for h in sm["heads"]]
    cA = [h["coherent_A"]["n_colors_natural"] for h in sm["heads"]]
    nn = sm["heads"][0]["n"]
    ax.bar(x - 0.2, cS, 0.4, label="colors(S)", color="#2b8cbe")
    ax.bar(x + 0.2, cA, 0.4, label="colors(A)", color="#e34a33")
    ax.axhline(nn * nn, ls="--", c="k", lw=1, label=f"n²={nn*nn} (max)")
    ax.set_xticks(x); ax.set_xticklabels(tags, rotation=90, fontsize=7)
    ax.set_ylabel("distinct entry colors")
    ax.set_title("PROBE 3 (NEW): coherent/color count.  NO.\n"
                 "S has MORE colors than A — generator is LESS, not more, structured")
    ax.legend(fontsize=8)

    fig.tight_layout()
    p = os.path.join(FIG, "01_rank_equitable_color.png")
    fig.savefig(p, dpi=110)
    print("wrote", p)


def fig_log_and_butterfly():
    fu = load("followup_results.json")
    sm = load("smollm_results.json")
    fig, axes = plt.subplots(1, 2, figsize=(12, 4.5))

    # Panel A: banded-log distribution
    ax = axes[0]
    blog = fu["banded_log"]
    b1 = np.array([r["band_w1"] for r in blog])
    ax.hist(b1, bins=24, color="#756bb1", edgecolor="k")
    ax.axvline(np.median(b1), c="r", ls="--", label=f"median={np.median(b1):.2f}")
    ax.axvline(0.5, c="k", ls=":", label=f"frac>0.5 = {np.mean(b1>0.5):.0%}")
    ax.set_xlabel("band-w1 mass fraction of log(A)")
    ax.set_ylabel("# heads (of 226 reliable)")
    ax.set_title("PROBE 4 (NEW): is log(A) a sparse/banded Hamiltonian?\n"
                 "PARTLY — bimodal: ~28% of heads strongly banded, most are not")
    ax.legend(fontsize=8)

    # Panel B: butterfly error vs depth, A vs S
    ax = axes[1]
    bfA = sm["butterfly_A"]; bfS = sm["butterfly_S"]
    dA = np.arange(1, len(bfA["err_by_depth"]) + 1)
    ax.plot(dA, bfA["err_by_depth"], "o-", c="#e34a33", label="butterfly fit of A")
    ax.plot(dA, bfS["err_by_depth"], "s-", c="#2b8cbe", label="butterfly fit of S")
    ax.axhline(0.0, c="k", lw=0.5)
    ax.set_xlabel("butterfly product depth (factors)")
    ax.set_ylabel("relative-Frobenius error")
    ax.set_title("PROBE 5 (NEW): butterfly product factorization\n"
                 "PARTLY — A fits better than S but neither reaches ~0 (not exact butterfly)")
    ax.legend(fontsize=8)

    fig.tight_layout()
    p = os.path.join(FIG, "02_log_butterfly.png")
    fig.savefig(p, dpi=110)
    print("wrote", p)


if __name__ == "__main__":
    fig_rank_and_equitable()
    fig_log_and_butterfly()
