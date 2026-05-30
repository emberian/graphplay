"""Figures for the walk-basis experiment.

  figures/sparsity_curves.png : OMP reconstruction error vs #atoms, one curve per
      attn-only-2l head, colored by class (content/positional/induction), plus the
      tiny-model clean cases (induction-task / local-task heads).
  figures/atom_usage.png : (a) bar of err-floor by head class, (b) the named
      best 'sink + one walk atom' companion per head, (c) the induction-head
      decomposition (sink + induction-shift + residual) as matrices.
"""
from __future__ import annotations

import json
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
FIG = os.path.join(_HERE, "figures")
os.makedirs(FIG, exist_ok=True)

CLASS_COLOR = {"content": "#888888", "positional": "#1f77b4",
               "induction": "#d62728"}


def load():
    with open(os.path.join(_HERE, "results.json")) as f:
        return json.load(f)


def sparsity_curves(d):
    fig, axes = plt.subplots(1, 2, figsize=(13, 5))
    ax = axes[0]
    for hid, r in d["attn_only_2l"].items():
        e = r["errors"]
        ax.plot(range(len(e)), e, color=CLASS_COLOR.get(r["label"], "k"),
                alpha=0.55, lw=1.4)
    # legend proxies
    for cls, col in CLASS_COLOR.items():
        n = sum(1 for r in d["attn_only_2l"].values() if r["label"] == cls)
        ax.plot([], [], color=col, label=f"{cls} (n={n})", lw=2)
    ax.axhline(0.10, ls="--", color="green", lw=1, label="10% target")
    ax.set_xlabel("# walk atoms (OMP)")
    ax.set_ylabel("relative reconstruction error")
    ax.set_title("attn-only-2l: sparsity curves by head class\n"
                 "(dict incl. bos-sink + induction-shift named atoms)")
    ax.set_ylim(0, 1.0)
    ax.legend(fontsize=8)
    ax.grid(alpha=0.3)

    ax = axes[1]
    # tiny model clean cases: best head per task
    tiny = d["tiny"]
    by_task = {}
    for r in tiny.values():
        by_task.setdefault(r["task"], []).append(r)
    cols = {"induction": "#d62728", "local": "#2ca02c",
            "averaging": "#9467bd", "recall": "#ff7f0e"}
    for task, rows in by_task.items():
        best = min(rows, key=lambda r: r["k_to_10pct"])
        e = best["errors"]
        ax.plot(range(len(e)), e, color=cols.get(task, "k"), lw=2,
                marker="o", ms=3,
                label=f"{task} (needs {best['needs']}, first={best['first_atom']})")
    ax.axhline(0.10, ls="--", color="green", lw=1)
    ax.set_xlabel("# walk atoms (OMP)")
    ax.set_ylabel("relative reconstruction error")
    ax.set_title("tiny trained attention-only models\n"
                 "(known-structure tasks; best head per task)")
    ax.set_ylim(0, 1.0)
    ax.legend(fontsize=8)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    p = os.path.join(FIG, "sparsity_curves.png")
    fig.savefig(p, dpi=130)
    plt.close(fig)
    return p


def atom_usage(d):
    rows = list(d["attn_only_2l"].values())
    fig, axes = plt.subplots(1, 2, figsize=(13, 5))

    # (a) err floor by head, grouped by class, annotated with best companion atom
    ax = axes[0]
    order = sorted(rows, key=lambda r: (r["label"], r["err_floor"]))
    ys = np.arange(len(order))
    floors = [r["err_floor"] for r in order]
    colors = [CLASS_COLOR.get(r["label"], "k") for r in order]
    ax.barh(ys, floors, color=colors)
    labels = [f"L{r['layer']}H{r['head']} [{r['label'][:4]}] "
              f"+{r['sink_plus_one_atom']}" for r in order]
    ax.set_yticks(ys)
    ax.set_yticklabels(labels, fontsize=7)
    ax.axvline(0.10, ls="--", color="green", lw=1, label="10%")
    ax.axvline(0.25, ls=":", color="orange", lw=1, label="25%")
    ax.set_xlabel("OMP error floor (full dictionary)")
    ax.set_title("Best named 'sink + ONE walk atom' companion per head\n"
                 "(bar = full-dictionary error floor)")
    ax.legend(fontsize=8)
    ax.grid(alpha=0.3, axis="x")

    # (b) k-to-reach-threshold per class (median + spread)
    ax = axes[1]
    classes = {}
    for r in rows:
        classes.setdefault(r["label"], []).append(r)
    cls_names = list(classes.keys())
    x = np.arange(len(cls_names))
    for off, (thr, key, c) in enumerate([
            (0.10, "k_to_10pct", "#2ca02c"),
            (0.25, "k_to_25pct", "#ff7f0e")]):
        meds = [np.median([r[key] for r in classes[cn]]) for cn in cls_names]
        ax.bar(x + off * 0.35, meds, width=0.35,
               label=f"median K@{int(thr*100)}%", color=c)
    ax.set_xticks(x + 0.17)
    ax.set_xticklabels(cls_names)
    ax.set_ylabel("# atoms to reach error threshold")
    ax.set_title("Atoms needed by head class\n"
                 "(K=20 = never reached within budget)")
    ax.legend(fontsize=8)
    ax.grid(alpha=0.3, axis="y")
    fig.tight_layout()
    p = os.path.join(FIG, "atom_usage.png")
    fig.savefig(p, dpi=130)
    plt.close(fig)
    return p


if __name__ == "__main__":
    d = load()
    p1 = sparsity_curves(d)
    p2 = atom_usage(d)
    print("wrote", p1)
    print("wrote", p2)
