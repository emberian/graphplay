"""Render the Circuit Atlas figures from results.json:
  * atlas_heatmap.png   -- the HEADLINE layer x head grid colored by circuit type
  * type_distribution.png -- how many heads of each circuit type, overall + per layer
  * residual_heatmap.png -- per-head reconstruction error floor (irreducibility)
  * induction_map.png    -- induction score per head (sanity: middle layers?)
"""
from __future__ import annotations

import json
import os

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap, BoundaryNorm
from matplotlib.patches import Patch

_HERE = os.path.dirname(os.path.abspath(__file__))
FIG = os.path.join(_HERE, "figures")
os.makedirs(FIG, exist_ok=True)

# circuit-type -> (integer code, color)
TYPE_ORDER = ["sink", "prev-token", "shift", "induction", "positional", "content"]
TYPE_COLOR = {
    "sink":       "#444444",   # dark grey  (BOS attention sink)
    "prev-token": "#1f77b4",   # blue       (shift-1)
    "shift":      "#17becf",   # cyan       (shift-k, k>1)
    "induction":  "#d62728",   # red        (induction-shift)
    "positional": "#2ca02c",   # green      (diffusion / cell / identity)
    "content":    "#f0e442",   # yellow     (irreducible)
}
TYPE_CODE = {t: i for i, t in enumerate(TYPE_ORDER)}


def load():
    with open(os.path.join(_HERE, "results.json")) as f:
        return json.load(f)


def grid(data, key):
    L, H = data["n_layers"], data["n_heads"]
    g = np.full((L, H), np.nan)
    for hid, h in data["heads"].items():
        g[h["layer"], h["head"]] = key(h)
    return g


def fig_atlas(data):
    L, H = data["n_layers"], data["n_heads"]
    codes = np.full((L, H), np.nan)
    for h in data["heads"].values():
        codes[h["layer"], h["head"]] = TYPE_CODE[h["rep"]["circuit_type"]]
    cmap = ListedColormap([TYPE_COLOR[t] for t in TYPE_ORDER])
    norm = BoundaryNorm(np.arange(-0.5, len(TYPE_ORDER) + 0.5), cmap.N)

    fig, ax = plt.subplots(figsize=(max(6, H * 0.42), max(7, L * 0.24)))
    ax.imshow(codes, aspect="auto", cmap=cmap, norm=norm,
              interpolation="nearest")
    ax.set_xlabel("head")
    ax.set_ylabel("layer")
    ax.set_title(f"Circuit Atlas — {data['model']}\n"
                 f"{L} layers x {H} heads, walk-basis circuit type per head")
    ax.set_xticks(range(H))
    ax.set_yticks(range(0, L, max(1, L // 18)))
    # KV-group separators (GQA)
    g = data["kv_group"]
    for x in range(g, H, g):
        ax.axvline(x - 0.5, color="white", lw=0.6, alpha=0.5)
    legend = [Patch(facecolor=TYPE_COLOR[t], label=t) for t in TYPE_ORDER]
    ax.legend(handles=legend, bbox_to_anchor=(1.01, 1.0), loc="upper left",
              fontsize=8, title="circuit type")
    fig.tight_layout()
    p = os.path.join(FIG, "atlas_heatmap.png")
    fig.savefig(p, dpi=130, bbox_inches="tight")
    plt.close(fig)
    return p


def fig_distribution(data):
    from collections import Counter
    L = data["n_layers"]
    counts = Counter(h["rep"]["circuit_type"] for h in data["heads"].values())
    total = sum(counts.values())

    # per-layer stacked
    per_layer = np.zeros((L, len(TYPE_ORDER)))
    for h in data["heads"].values():
        per_layer[h["layer"], TYPE_CODE[h["rep"]["circuit_type"]]] += 1

    fig, (ax0, ax1) = plt.subplots(1, 2, figsize=(15, 6),
                                   gridspec_kw={"width_ratios": [1, 2]})
    # overall bar
    ts = [t for t in TYPE_ORDER if counts.get(t, 0) > 0]
    vals = [counts[t] for t in ts]
    ax0.bar(ts, vals, color=[TYPE_COLOR[t] for t in ts])
    for i, v in enumerate(vals):
        ax0.text(i, v, f"{v}\n{100*v/total:.0f}%", ha="center", va="bottom",
                 fontsize=9)
    ax0.set_title(f"Overall circuit-type counts (N={total} heads)")
    ax0.set_ylabel("# heads")
    ax0.tick_params(axis="x", rotation=35)

    # per-layer stacked bars (layer on x)
    bottom = np.zeros(L)
    x = np.arange(L)
    for ci, t in enumerate(TYPE_ORDER):
        ax1.bar(x, per_layer[:, ci], bottom=bottom, color=TYPE_COLOR[t],
                label=t, width=0.9)
        bottom += per_layer[:, ci]
    ax1.set_title("Circuit-type composition by layer")
    ax1.set_xlabel("layer")
    ax1.set_ylabel("# heads")
    ax1.legend(fontsize=8, ncol=3, loc="upper center")
    ax1.set_xlim(-0.6, L - 0.4)
    fig.tight_layout()
    p = os.path.join(FIG, "type_distribution.png")
    fig.savefig(p, dpi=130, bbox_inches="tight")
    plt.close(fig)
    return p


def fig_residual(data):
    floor = grid(data, lambda h: h["rep"]["err_floor"])
    fig, ax = plt.subplots(figsize=(max(6, data["n_heads"] * 0.42),
                                    max(7, data["n_layers"] * 0.24)))
    im = ax.imshow(floor, aspect="auto", cmap="magma_r", vmin=0, vmax=1,
                   interpolation="nearest")
    ax.set_xlabel("head"); ax.set_ylabel("layer")
    ax.set_title(f"Residual / irreducibility — OMP error floor (≤{data['max_atoms']} atoms)\n"
                 "dark = well-explained by walks, bright = irreducible/content")
    fig.colorbar(im, ax=ax, label="reconstruction error floor")
    fig.tight_layout()
    p = os.path.join(FIG, "residual_heatmap.png")
    fig.savefig(p, dpi=130, bbox_inches="tight")
    plt.close(fig)
    return p


def fig_induction(data):
    ind = grid(data, lambda h: h["rep"]["induction_score"])
    sink = grid(data, lambda h: h["rep"]["sink_score"])
    prev = grid(data, lambda h: h["rep"]["prev_token_score"])
    fig, axs = plt.subplots(1, 3, figsize=(18, max(6, data["n_layers"] * 0.22)))
    for ax, g, title, cm in [
        (axs[0], ind, "induction score", "Reds"),
        (axs[1], prev, "prev-token score", "Blues"),
        (axs[2], sink, "BOS/col-0 sink score", "Greys"),
    ]:
        im = ax.imshow(g, aspect="auto", cmap=cm, vmin=0,
                       vmax=max(0.2, np.nanpercentile(g, 99)),
                       interpolation="nearest")
        ax.set_title(title); ax.set_xlabel("head"); ax.set_ylabel("layer")
        fig.colorbar(im, ax=ax, fraction=0.046)
    fig.suptitle(f"Head-role scores — {data['model']} (repeated-token probe)")
    fig.tight_layout()
    p = os.path.join(FIG, "score_maps.png")
    fig.savefig(p, dpi=130, bbox_inches="tight")
    plt.close(fig)
    return p


def main():
    data = load()
    print("atlas      ->", fig_atlas(data))
    print("dist       ->", fig_distribution(data))
    print("residual   ->", fig_residual(data))
    print("scores     ->", fig_induction(data))


if __name__ == "__main__":
    main()
