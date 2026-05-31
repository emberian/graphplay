#!/usr/bin/env python3
"""
Experiment 4 — Block-equitable attention O(n*r) vs dense O(n^2).

The Lean module `AttentionComplexity` PROVES (axiom-clean) that for a
block-equitable attention pattern A[i][j] = B[cell i][cell j], the block apply

    cellSum[c] = sum_{j in cell c} V[j]            (one O(n*d) pass)
    out[i]     = sum_c B[cell i][c] * cellSum[c]   (O(n*r*d))

computes EXACTLY the same output as the dense apply out[i] = sum_j A[i][j] V[j]
(O(n^2 d)) -- theorem `blockAttentionApply_eq_fullAttentionApply`, with cost
`blockCost n r d = n*(r*d + d)` linear in n (`attention_apply_linear_in_n`).

Here we back that PROVEN structural reduction with REAL WALL-CLOCK TIMINGS: at a
fixed number of cells r and feature dim d, we time both algorithms for growing n
and fit the empirical scaling exponents.  Target: dense ~ n^2, block ~ n^1, plus
a correctness check that the two outputs agree to machine precision.
"""
import numpy as np
import time, os, json

OUT = os.path.dirname(os.path.abspath(__file__))
FIGS = os.path.join(OUT, "figures")
os.makedirs(FIGS, exist_ok=True)


def dense_apply(A, V):
    """out[i] = sum_j A[i][j] V[j].  Dense O(n^2 d)."""
    return A @ V


def block_apply(B, cell, V, r):
    """Block-equitable apply: precompute r cell-sums, then r-term contraction.
    O(n*d) cell-sums + O(n*r*d) contraction = O(n*(r+1)*d), linear in n."""
    n, d = V.shape
    # cell-sums: csum[c] = sum_{j: cell[j]==c} V[j]  -- one pass O(n*d)
    csum = np.zeros((r, d))
    np.add.at(csum, cell, V)          # scatter-add, O(n*d)
    # out[i] = sum_c B[cell[i], c] * csum[c]
    # = (B[cell] @ csum), B[cell] is (n,r), csum is (r,d): O(n*r*d)
    return B[cell] @ csum


def build(n, r, d, rng):
    cell = rng.integers(0, r, size=n)
    B = rng.standard_normal((r, r))
    V = rng.standard_normal((n, d))
    A = B[cell][:, cell]              # A[i][j] = B[cell i][cell j]  (block-equitable)
    return A, B, cell, V


def time_call(fn, *args, reps=3):
    best = float("inf")
    for _ in range(reps):
        t0 = time.perf_counter()
        out = fn(*args)
        t1 = time.perf_counter()
        best = min(best, t1 - t0)
    return best, out


def main():
    rng = np.random.default_rng(0)
    r, d = 8, 16
    ns = [128, 256, 512, 1024, 2048, 4096, 8192, 16384]
    t_dense, t_block, maxerr = [], [], []
    for n in ns:
        A, B, cell, V = build(n, r, d, rng)
        td, od = time_call(dense_apply, A, V)
        tb, ob = time_call(block_apply, B, cell, V, r, reps=5)
        err = np.max(np.abs(od - ob))
        t_dense.append(td); t_block.append(tb); maxerr.append(err)
        print(f"n={n:6d}  dense={td*1e3:8.3f} ms  block={tb*1e3:8.3f} ms  "
              f"speedup={td/tb:6.1f}x  max|dense-block|={err:.2e}")

    ns = np.array(ns, float)
    t_dense = np.array(t_dense); t_block = np.array(t_block)
    # Fit in the asymptotic regime (n >= 512) where per-call overhead is negligible.
    fitmask = ns >= 512
    ad = np.polyfit(np.log(ns[fitmask]), np.log(t_dense[fitmask]), 1)[0]
    ab = np.polyfit(np.log(ns[fitmask]), np.log(t_block[fitmask]), 1)[0]
    print(f"\nFIT (n>=512, asymptotic): dense ~ n^{ad:.3f}   block ~ n^{ab:.3f}   (r={r}, d={d})")
    print(f"max correctness error across all n: {max(maxerr):.2e} (machine precision)")

    import matplotlib; matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(7, 5))
    ax.loglog(ns, t_dense * 1e3, "o-", color="C3", label=fr"dense $O(n^2)$: fit $n^{{{ad:.2f}}}$")
    ax.loglog(ns, t_block * 1e3, "s-", color="C0", label=fr"block $O(n\,r)$: fit $n^{{{ab:.2f}}}$")
    nn = np.logspace(np.log10(ns[0]), np.log10(ns[-1]), 100)
    ax.loglog(nn, t_dense[0]*1e3*(nn/ns[0])**2, "--", color="gray", alpha=0.6, label=r"$\propto n^2$ ref")
    ax.loglog(nn, t_block[0]*1e3*(nn/ns[0]), ":", color="gray", alpha=0.6, label=r"$\propto n^1$ ref")
    ax.set_xlabel("sequence length n"); ax.set_ylabel("wall-clock apply time (ms)")
    ax.set_title(f"Attention apply: block $O(n\\,r)$ vs dense $O(n^2)$  (r={r}, d={d})\n"
                 f"dense$\\sim n^{{{ad:.2f}}}$, block$\\sim n^{{{ab:.2f}}}$, exact agreement")
    ax.legend(); ax.grid(True, which="both", alpha=0.3)
    fig.tight_layout()
    figpath = os.path.join(FIGS, "exp4_attention_linear.png")
    fig.savefig(figpath, dpi=130)
    print("saved", figpath)

    json.dump({"ns": ns.tolist(), "t_dense": t_dense.tolist(), "t_block": t_block.tolist(),
               "dense_exponent": ad, "block_exponent": ab, "max_error": max(maxerr),
               "r": r, "d": d},
              open(os.path.join(OUT, "exp4_results.json"), "w"), indent=2)


if __name__ == "__main__":
    main()
