#!/usr/bin/env python3
"""
Experiment 3 — The d>4 lattice dimension threshold (Childs-Goldstone).

CTQW spatial search on the d-dimensional PERIODIC lattice Z_L^d.  Childs-Goldstone
(quant-ph/0306054) proved the threshold:

    d > 4 : optimal,   T* ~ sqrt(N),  peak success -> O(1)
    d = 4 : marginal,  T* ~ sqrt(N log N),  peak ~ 1/log N  (loses a sqrt(log) factor)
    d <= 3: NOT optimal, peak success -> 0 as N grows (no quadratic speedup)

This is the open Lean clause `lattice_search_dimension_threshold`
(`IsOptimalCTQWSearch (latticeGraph d L) w <-> 4 < d`), whose proof needs the
Childs-Goldstone spectral integral  int d^k / sum_a (1-cos k_a)  (IR-convergence,
dimension-4-critical).

We DEMONSTRATE the threshold by direct simulation: build the full lattice search
Hamiltonian H = -gamma A - |w><w| on Z_L^d (small L), optimize gamma per (d,L),
find the peak success probability and time-to-peak.  We then look at how the PEAK
SUCCESS PROBABILITY scales with N across dimensions: it should stay O(1) for d>=5,
be marginal at d=4, and DECAY for d<=3.

Sizes are modest because the full Hilbert space is N=L^d (no equitable reduction
here -- the lattice's distance partition is NOT equitable on a generic torus, so we
simulate the full graph).  We use eigh on the dense N x N Hamiltonian.
"""
import numpy as np
import itertools, os, json
from scipy.optimize import minimize_scalar

OUT = os.path.dirname(os.path.abspath(__file__))
FIGS = os.path.join(OUT, "figures")
os.makedirs(FIGS, exist_ok=True)


def lattice_adjacency(d, L):
    """Adjacency of the periodic torus Z_L^d (nearest neighbour, +-1 per axis)."""
    N = L ** d
    coords = list(itertools.product(range(L), repeat=d))
    index = {c: i for i, c in enumerate(coords)}
    A = np.zeros((N, N))
    for c in coords:
        i = index[c]
        for axis in range(d):
            for s in (+1, -1):
                cc = list(c); cc[axis] = (cc[axis] + s) % L; cc = tuple(cc)
                A[i, index[cc]] = 1.0
    return A


def search_H(A, gamma, w):
    H = -gamma * A.copy()
    H[w, w] += -1.0
    return H


def success_curve(A, gamma, w, ts):
    N = A.shape[0]
    H = search_H(A, gamma, w)
    evals, evecs = np.linalg.eigh(H)
    psi0 = np.full(N, 1.0 / np.sqrt(N), dtype=complex)   # uniform initial state
    c = evecs.conj().T @ psi0
    probs = np.empty_like(ts)
    for i, t in enumerate(ts):
        psi = evecs @ (np.exp(-1j * evals * t) * c)
        probs[i] = abs(psi[w]) ** 2
    return probs


def find_peak(A, gamma, w, ncoarse=3000):
    N = A.shape[0]
    tmax = 3.0 * np.sqrt(N)
    ts = np.linspace(0, tmax, ncoarse)
    p = success_curve(A, gamma, w, ts)
    idx = int(np.argmax(p))
    t0 = ts[max(0, idx - 4)]; t1 = ts[min(len(ts) - 1, idx + 4)]
    tsf = np.linspace(t0, t1, 1500)
    pf = success_curve(A, gamma, w, tsf)
    j = int(np.argmax(pf))
    return tsf[j], pf[j]


def best_over_gamma(A, w, deg):
    """Maximize peak success over gamma (critical tuning around 1/deg).  Reuse the
    eigendecomposition is not possible (H depends on gamma), so for large N we use a
    coarser time scan during the gamma search, then a fine scan at the optimum."""
    N = A.shape[0]
    ncoarse = 3000 if N <= 1500 else 1200
    def negpeak(g):
        if g <= 0:
            return 0.0
        return -find_peak(A, g, w, ncoarse=ncoarse)[1]
    res = minimize_scalar(negpeak, bounds=(0.1 / deg, 5.0 / deg),
                          method="bounded", options={"xatol": 1e-4, "maxiter": 30})
    g = res.x
    T, pk = find_peak(A, g, w)
    return g, T, pk


def main():
    # For each dimension, a couple of side lengths (keep N <= ~4000 for dense eigh).
    config = {
        2: [10, 16, 24, 32, 40],         # N = 100..1600
        3: [4, 5, 6, 7, 8],              # N = 64..512
        4: [3, 4, 5],                    # N = 81..625
        5: [3, 4],                       # N = 243..1024
        6: [3, 4],                       # N = 729..4096
    }
    results = {}
    for d, Ls in config.items():
        deg = 2 * d
        rows = []
        for L in Ls:
            if L <= 2:
                continue
            A = lattice_adjacency(d, L)
            N = A.shape[0]
            w = 0
            g, T, pk = best_over_gamma(A, w, deg)
            rows.append((N, L, g, T, pk))
            print(f"d={d}  L={L:2d}  N={N:5d}  deg={deg}  gamma*={g:.4f}  T*={T:8.3f}  peak={pk:.5f}")
        results[d] = rows
    print()

    # Fit, per dimension, peak ~ N^beta (how success scales): beta<0 => decays (no speedup),
    # beta ~ 0 => constant success (optimal).  Also fit T* ~ N^alpha.
    import matplotlib; matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, (ax1, ax3) = plt.subplots(1, 2, figsize=(12, 4.8))
    summary = {}
    colors = {2: "C3", 3: "C1", 4: "C5", 5: "C0", 6: "C2"}
    betas = {}
    for d, rows in results.items():
        Ns = np.array([r[0] for r in rows], float)
        Ts = np.array([r[3] for r in rows], float)
        Pk = np.array([r[4] for r in rows], float)
        beta = float(np.polyfit(np.log(Ns), np.log(Pk), 1)[0]) if len(Ns) >= 2 else float("nan")
        alpha = float(np.polyfit(np.log(Ns), np.log(Ts), 1)[0]) if len(Ns) >= 2 else float("nan")
        summary[d] = {"Ns": Ns.tolist(), "Tstar": Ts.tolist(), "peak": Pk.tolist(),
                      "peak_exponent_beta": beta, "Tstar_exponent_alpha": alpha}
        betas[d] = beta
        lbl = f"d={d} (deg {2*d})"
        bstr = "n/a" if np.isnan(beta) else f"{beta:+.2f}"
        ax1.loglog(Ns, Pk, "o-", color=colors[d],
                   label=f"{lbl}: peak " + r"$\propto N^{" + bstr + r"}$")
        print(f"d={d}: peak ~ N^{beta:+.3f}   T* ~ N^{alpha:.3f}")

    ax1.set_xlabel("N = $L^d$"); ax1.set_ylabel("peak success probability")
    ax1.set_title("Lattice search: peak success vs N\n"
                  r"(decays for $d\leq 3$, ~const for $d\geq 5$)")
    ax1.legend(fontsize=8); ax1.grid(True, which="both", alpha=0.3)

    # Right panel: the THRESHOLD itself -- peak-scaling exponent beta vs dimension d.
    # beta < 0 => peak decays => NO quadratic speedup; beta ~ 0 => constant => optimal.
    dd = sorted(b for b in betas if not np.isnan(betas[b]))
    bb = [betas[d] for d in dd]
    ax3.axhline(0.0, color="green", ls="--", alpha=0.7, label=r"$\beta=0$: optimal (const success)")
    ax3.axvline(4.0, color="red", ls=":", alpha=0.7, label="Childs-Goldstone $d=4$ threshold")
    ax3.plot(dd, bb, "o-", ms=9, color="k")
    for d in dd:
        ax3.annotate(f"{betas[d]:+.2f}", (d, betas[d]), textcoords="offset points",
                     xytext=(6, 6), fontsize=8)
    ax3.set_xlabel("lattice dimension d"); ax3.set_ylabel(r"peak-scaling exponent $\beta$")
    ax3.set_title("The $d>4$ threshold: success $\\propto N^\\beta$\n"
                  r"$\beta<0$ (no speedup) for $d\leq 3$, $\beta\to 0$ for $d\geq 5$")
    ax3.legend(fontsize=8); ax3.grid(True, alpha=0.3)
    fig.tight_layout()
    figpath = os.path.join(FIGS, "exp3_lattice_threshold.png")
    fig.savefig(figpath, dpi=130)
    print("saved", figpath)

    json.dump(summary, open(os.path.join(OUT, "exp3_results.json"), "w"), indent=2)


if __name__ == "__main__":
    main()
