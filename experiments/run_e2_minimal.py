"""E2-minimal — the go/no-go headline experiment for the explanatory program.

For each tiny task (induction/sparse, averaging/low-rank, recall/sparse,
local/banded) we:
  1. train a 2-layer attention-only transformer to convergence,
  2. extract the held-out attention A* per (layer, head),
  3. run the equitable-decomposition probe over a sweep of cell-counts r,
  4. overlay the submanifold residuals (low-rank-k, banded-w, fixed-sparse).

Prediction under test: the residual is small / low-rank for the structure the
task NEEDS, and large where a mismatched variant's bet would fail. The figure
``figures/e2_minimal.png`` is the go/no-go.

Run:  python run_e2_minimal.py
"""

from __future__ import annotations

import json
import os

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from graphplay_probe import decompose, matched_submanifold_residuals
from graphplay_probe.model import train_model, extract_attention
from graphplay_probe.tasks import TASKS, build_task

# DOF budget (free real params retained by each structured fit) for the *fair*
# submanifold competition. ~2n keeps the bets cheap & comparable across tasks.
MATCHED_BUDGET_FACTOR = 2  # budget = factor * n

NEEDED_TO_MANIFOLD = {
    "sparse": "fixed-sparse",
    "low-rank": "low-rank",
    "banded": "banded",
    "equitable": "equitable",
}

HERE = os.path.dirname(os.path.abspath(__file__))
FIGDIR = os.path.join(HERE, "figures")
os.makedirs(FIGDIR, exist_ok=True)

# which submanifold each task BETS its needed-structure lives in
STRUCTURE_TO_MANIFOLD = {
    "sparse": "fixed-sparse",
    "low-rank": "low-rank",
    "banded": "banded",
    "equitable": "equitable",
}


def relnorm(R, A):
    a = np.linalg.norm(A)
    return float(np.linalg.norm(R) / a) if a > 0 else 0.0


def analyze_task(name, seed=0, verbose=True):
    """Train, extract A*, probe every (layer,head). Returns a record dict."""
    Xtr, Ytr, Xte, Yte, vocab, structure = build_task(name, seed=seed)
    T = Xtr.shape[1]
    if verbose:
        print(f"\n=== {name}  (needs: {structure})  T={T} vocab={vocab} ===")
    model, acc = train_model(
        Xtr, Ytr, Xte, Yte, vocab,
        d_model=32, n_heads=2, n_layers=2, epochs=100, lr=3e-3,
        seed=seed, verbose=verbose,
    )
    nparams = model.num_params()
    if verbose:
        print(f"  params={nparams}  test_acc={acc:.3f}")

    attns = extract_attention(model, Xte, n_examples=64)  # list[layer] (H,T,T)
    n_layers = len(attns)
    n_heads = attns[0].shape[0]

    # cell-count sweep: a spread up to ~T
    r_sweep = sorted({2, 3, 4, 6, 8, max(2, T // 3), max(2, T // 2)})
    r_sweep = [r for r in r_sweep if r < T]

    record = {
        "task": name,
        "needs": structure,
        "acc": acc,
        "nparams": nparams,
        "T": T,
        "r_sweep": r_sweep,
        "layers": [],
    }

    for L in range(n_layers):
        for H in range(n_heads):
            A = attns[L][H]  # (T,T) row-stochastic (lower-triangular for causal)
            out = decompose(A, r_sweep)
            # equitable defect curve over r (relative Frobenius)
            eq_curve = [out["defect_eq"][r] for r in r_sweep]
            rankR_curve = [out["rank_R"][r] for r in r_sweep]
            # submanifold residual curves (relative Frobenius)
            ks = sorted(out["lowrank_resid_norm"].keys())
            ws = sorted(out["banded_resid_norm"].keys())
            lr_curve = [(k, out["lowrank_resid_norm"][k]) for k in ks]
            band_curve = [(w, out["banded_resid_norm"][w]) for w in ws]
            sparse_resid = out["sparse_resid_norm"]
            # FAIR competition: all four submanifolds at a *matched* DOF budget.
            budget = MATCHED_BUDGET_FACTOR * A.shape[0]
            best = matched_submanifold_residuals(A, budget)
            record["layers"].append({
                "L": L, "H": H,
                "eq_curve": eq_curve,
                "rankR_curve": rankR_curve,
                "lowrank_curve": lr_curve,
                "banded_curve": band_curve,
                "sparse_resid": sparse_resid,
                "best": best,
                "A": A,
            })
            if verbose:
                bstr = "  ".join(f"{k}={v:.2f}" for k, v in best.items()
                                 if not k.startswith("_"))
                print(f"  L{L}H{H}: {bstr}  "
                      f"(k={best['_k']},w={best['_w']},m={best['_m']},r={best['_r']})")
    return record


def make_figure(records, path):
    """Grid: one column per task.
    Row 1: equitable defect vs r (per head) + submanifold residual markers.
    Row 2: rank_eps(R) vs r (per head).
    Row 3: a representative attention heatmap (layer with sharpest head).
    """
    ntask = len(records)
    fig, axes = plt.subplots(3, ntask, figsize=(4.2 * ntask, 11), squeeze=False)

    for c, rec in enumerate(records):
        r_sweep = rec["r_sweep"]
        needed = rec["needs"]
        target_manifold = STRUCTURE_TO_MANIFOLD.get(needed, needed)

        # ---- row 0: equitable defect vs r ----
        ax = axes[0][c]
        for ly in rec["layers"]:
            ax.plot(r_sweep, ly["eq_curve"], marker="o", alpha=0.8,
                    label=f"L{ly['L']}H{ly['H']}")
        # overlay matched-budget submanifold residuals as horizontal lines
        # (lowest residual = the structure A* actually lives in)
        manifolds = ["low-rank", "banded", "fixed-sparse", "equitable"]
        agg = {}
        for key in manifolds:
            agg[key] = np.min([ly["best"][key] for ly in rec["layers"]])
        colors = {"low-rank": "tab:green", "banded": "tab:orange",
                  "fixed-sparse": "tab:red", "equitable": "tab:blue"}
        for key in manifolds:
            val = agg[key]
            star = " *" if key == target_manifold else ""
            ax.axhline(val, ls="--", lw=1.6, color=colors.get(key, "gray"),
                       alpha=0.8, label=f"{key}={val:.2f}{star}")
        ax.set_title(f"{rec['task']}\nneeds: {needed}  (acc={rec['acc']:.2f})",
                     fontsize=10)
        ax.set_xlabel("r (cells)")
        ax.set_ylabel("rel. residual ‖R‖/‖A‖")
        ax.set_ylim(-0.02, 1.05)
        ax.legend(fontsize=6, loc="upper right", ncol=2)

        # ---- row 1: rank_eps(R) vs r ----
        ax = axes[1][c]
        for ly in rec["layers"]:
            ax.plot(r_sweep, ly["rankR_curve"], marker="s", alpha=0.8,
                    label=f"L{ly['L']}H{ly['H']}")
        ax.set_xlabel("r (cells)")
        ax.set_ylabel("rank_ε(R)")
        ax.set_title("residual numerical rank", fontsize=9)
        ax.legend(fontsize=6)

        # ---- row 2: representative attention heatmap ----
        ax = axes[2][c]
        # pick the head with the lowest residual on its needed manifold
        best_key = target_manifold
        ly = min(rec["layers"], key=lambda l: l["best"][best_key])
        im = ax.imshow(ly["A"], cmap="viridis", aspect="auto")
        ax.set_title(f"A* L{ly['L']}H{ly['H']}  "
                     f"({best_key}={ly['best'][best_key]:.2f})", fontsize=9)
        ax.set_xlabel("key pos"); ax.set_ylabel("query pos")
        fig.colorbar(im, ax=ax, fraction=0.046)

    fig.suptitle("E2-minimal: equitable & submanifold residuals of trained "
                 "attention A*  (low residual = A* lives in that structure)",
                 fontsize=12)
    fig.tight_layout(rect=[0, 0, 1, 0.97])
    fig.savefig(path, dpi=130)
    plt.close(fig)
    print(f"\nsaved figure -> {path}")


def verdict(records):
    """For each task, is the needed-structure residual the SMALLEST among the
    competing submanifold bets, on the best-matching head? That's the prediction."""
    lines = []
    matches = 0
    manifolds = ["low-rank", "banded", "fixed-sparse", "equitable"]
    TOL = 0.05   # near-tie tolerance (overlapping manifolds, e.g. band ⊂ sparse)
    SMALL = 0.30  # "the residual is small" absolute threshold
    for rec in records:
        needed = rec["needs"]
        target = NEEDED_TO_MANIFOLD[needed]
        # aggregate over heads: the BEST head for each manifold (a task succeeds
        # if *some* head realizes the needed structure)
        compete = {key: min(ly["best"][key] for ly in rec["layers"])
                   for key in manifolds}
        best_val = min(compete.values())
        winner = min(compete, key=compete.get)
        target_val = compete[target]
        # PREDICTION (honest, tolerant): the needed manifold's residual is
        # (a) small in absolute terms AND (b) within TOL of the best bet.
        is_small = target_val <= SMALL
        is_top = (target_val - best_val) <= TOL
        ok = is_small and is_top
        matches += ok
        # rank of the residual on the needed manifold's best head
        best_head = min(rec["layers"], key=lambda l: l["best"][target])
        ridx = rec["r_sweep"].index(4) if 4 in rec["r_sweep"] else 0
        lines.append({
            "task": rec["task"], "needs": needed, "acc": rec["acc"],
            "bets": {k: round(v, 3) for k, v in compete.items()},
            "winner": winner, "predicted": target,
            "target_resid": round(target_val, 3),
            "is_small": bool(is_small), "is_top": bool(is_top),
            "match": bool(ok),
            "rankR_at_r4": best_head["rankR_curve"][ridx],
        })
    return matches, lines


def main():
    records = []
    for name in ["induction", "averaging", "recall", "local"]:
        records.append(analyze_task(name, seed=0))

    figpath = os.path.join(FIGDIR, "e2_minimal.png")
    make_figure(records, figpath)

    matches, lines = verdict(records)
    print("\n================ E2-minimal verdict ================")
    for L in lines:
        tag = "MATCH" if L["match"] else (
            "MISS(not-small)" if not L["is_small"] else "MISS(not-top)")
        print(f"{L['task']:>10} needs={L['needs']:>9} acc={L['acc']:.2f}  "
              f"bets={L['bets']}  target={L['predicted']}({L['target_resid']}) "
              f"{tag}  rank(R@r4)={L['rankR_at_r4']}")
    print(f"\nmatch-metric: needed-structure residual is small & top-tier in "
          f"{matches}/{len(lines)} tasks")

    # persist machine-readable summary
    with open(os.path.join(HERE, "e2_summary.json"), "w") as f:
        json.dump({"matches": matches, "n": len(lines), "tasks": lines}, f, indent=2)
    return matches, lines


if __name__ == "__main__":
    main()
