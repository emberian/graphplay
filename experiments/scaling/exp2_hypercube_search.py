#!/usr/bin/env python3
"""
Experiment 2 — Quantum spatial search on the SPARSE Boolean hypercube Q_d.

THE HEADLINE: Q_d has N = 2^d vertices but degree only d = log2(N) (sparse,
physically buildable), and Childs-Goldstone (quant-ph/0306054) proved CTQW
spatial search on Q_d is optimal O(sqrt(N)).  This is exactly the open Lean
clause `hypercube_search_optimal_timing` (the O(sqrt(N)) TIMING), whose
structural half (Hamming-distance equitable reduction to a (d+1)-dim chain) is
proven axiom-clean as `hypercube_sparse_search_reduction`.

We DEMONSTRATE the timing numerically by exploiting precisely that equitable
reduction: H = -gamma*A(Q_d) - |w><w| collapses, on the Hamming-distance-from-w
cell-uniform subspace, to a (d+1)-dimensional weighted "collapsed Hamming chain".
The chain's adjacency (in the cell-COUNT-normalized orthonormal basis) is the
Krawtchouk/Hahn tridiagonal:

    cell k has C(d,k) vertices; a distance-k vertex has (d-k) up-edges (to k+1)
    and k down-edges (to k-1).  On the orthonormal shell basis e_k = |cell k>/sqrt(C(d,k)),
    the symmetric reduced adjacency is  A~[k,k+1] = A~[k+1,k] = sqrt((d-k)*(k+1)).

Optimal coupling: gamma = 1/d  (the per-vertex degree is d; the uniform state is
the top eigenvector of A with eigenvalue d, and Childs-Goldstone optimal gamma is
1/d, the reciprocal degree, in the leading large-d regime).  The marked vertex is
w (cell 0); the oracle in the shell basis is -|e_0><e_0| (cell 0 is the single
vertex w, C(d,0)=1).  Initial state = uniform |s> over all N vertices, which in the
shell basis has amplitude sqrt(C(d,k)/N) on e_k.

We find T*(N) and peak success |<w|psi(t)>|^2, fit T* vs N = 2^d.

CLAIM target: T* propto sqrt(N) on a host of degree log2(N).
"""
import numpy as np
import os, json
from math import comb

OUT = os.path.dirname(os.path.abspath(__file__))
FIGS = os.path.join(OUT, "figures")
os.makedirs(FIGS, exist_ok=True)


def reduced_search_H(d, gamma):
    """(d+1)x(d+1) Hermitian reduced search generator on orthonormal shell basis.
    H~ = -gamma * A~  -  oracle(|e_0><e_0|).
    A~ tridiagonal with A~[k,k+1] = sqrt((d-k)*(k+1)).
    """
    m = d + 1
    A = np.zeros((m, m))
    for k in range(d):
        v = np.sqrt((d - k) * (k + 1))
        A[k, k + 1] = v
        A[k + 1, k] = v
    H = -gamma * A
    H[0, 0] += -1.0  # oracle -|w><w|, w = cell 0 (single vertex)
    return H


def initial_state(d):
    """Uniform |s> over N=2^d vertices, expressed in orthonormal shell basis:
    amplitude on e_k is sqrt(C(d,k)/N)."""
    N = 2 ** d
    return np.array([np.sqrt(comb(d, k) / N) for k in range(d + 1)], dtype=complex)


def success_curve(d, gamma, ts):
    H = reduced_search_H(d, gamma)
    evals, evecs = np.linalg.eigh(H)
    psi0 = initial_state(d)
    c = evecs.conj().T @ psi0
    probs = np.empty_like(ts)
    for i, t in enumerate(ts):
        psi = evecs @ (np.exp(-1j * evals * t) * c)
        probs[i] = abs(psi[0]) ** 2   # |<e_0|psi>|^2 = success on w
    return probs


def find_peak(d, gamma):
    N = 2 ** d
    tmax = 4.0 * np.sqrt(N)
    ts = np.linspace(0, tmax, 8000)
    p = success_curve(d, gamma, ts)
    idx = int(np.argmax(p))
    t0 = ts[max(0, idx - 4)]; t1 = ts[min(len(ts) - 1, idx + 4)]
    tsf = np.linspace(t0, t1, 4000)
    pf = success_curve(d, gamma, tsf)
    j = int(np.argmax(pf))
    return tsf[j], pf[j]


def optimal_gamma(d):
    """Childs-Goldstone spatial search needs gamma tuned to a CRITICAL value gamma_c
    (the value at which the marked-state energy aligns with the uniform-state energy,
    producing the avoided crossing / two-level Rabi).  We find it numerically: the
    optimal gamma maximizes the peak success probability.  This is the honest,
    physical tuning procedure (no closed form assumed)."""
    from scipy.optimize import minimize_scalar
    def negpeak(g):
        if g <= 0:
            return 0.0
        _, pk = find_peak(d, g)
        return -pk
    # search around 1/d (leading order); bracket generously
    res = minimize_scalar(negpeak, bounds=(0.2 / d, 4.0 / d), method="bounded",
                          options={"xatol": 1e-5})
    return res.x


def main():
    ds = list(range(4, 11))   # d = 4..10  -> N = 16..1024
    Tstar, peak, Ns, gammas = [], [], [], []
    for d in ds:
        N = 2 ** d
        gamma = optimal_gamma(d)   # critical coupling, tuned numerically
        T, pk = find_peak(d, gamma)
        Ns.append(N); Tstar.append(T); peak.append(pk); gammas.append(gamma)
        print(f"d={d:2d}  N={N:5d}  degree={d:2d}=log2N  gamma*={gamma:.5f} (1/d={1/d:.5f})  "
              f"T*={T:9.4f}  (pi/2)sqrt(N)={np.pi/2*np.sqrt(N):9.4f}  peak={pk:.5f}")

    Ns = np.array(Ns, float); Tstar = np.array(Tstar); peak = np.array(peak)
    a, logC = np.polyfit(np.log(Ns), np.log(Tstar), 1)
    C = np.exp(logC)
    resid = np.log(Tstar) - (a * np.log(Ns) + logC)
    rms = np.sqrt(np.mean(resid ** 2))
    se_a = rms / (np.std(np.log(Ns)) * np.sqrt(len(Ns)))
    print(f"\nFIT: T* = {C:.4f} * N^{a:.4f} (+-{se_a:.4f}), log-log RMS={rms:.4e}")
    print(f"target exponent 0.5 (sqrt(N) on a degree-log2(N) host).")

    import matplotlib; matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 4.5))
    ax1.loglog(Ns, Tstar, "o", ms=8, label="measured $T^*(N)$")
    nn = np.logspace(np.log10(Ns[0]), np.log10(Ns[-1]), 200)
    ax1.loglog(nn, C * nn ** a, "-", label=fr"fit $T^*={C:.3f}\,N^{{{a:.3f}}}$")
    ax1.loglog(nn, np.pi / 2 * np.sqrt(nn), "--", color="gray", label=r"$(\pi/2)\sqrt{N}$ ref")
    ax1.set_xlabel("N = $2^d$  (degree = $d=\\log_2 N$)")
    ax1.set_ylabel("time-to-peak $T^*$")
    ax1.set_title(f"Hypercube $Q_d$ search:  $T^*\\propto N^{{{a:.3f}\\pm{se_a:.3f}}}$")
    ax1.legend(); ax1.grid(True, which="both", alpha=0.3)

    ax2.semilogx(Ns, peak, "s-", ms=8, color="C2")
    ax2.set_xlabel("N"); ax2.set_ylabel("peak success probability")
    ax2.set_title("hypercube search peak success"); ax2.grid(True, alpha=0.3)
    fig.tight_layout()
    figpath = os.path.join(FIGS, "exp2_hypercube_search.png")
    fig.savefig(figpath, dpi=130)
    print("saved", figpath)

    json.dump({"Ns": Ns.tolist(), "ds": ds, "Tstar": Tstar.tolist(),
               "peak": peak.tolist(), "fit_exponent": a, "fit_se": se_a,
               "fit_C": C, "loglog_rms": rms},
              open(os.path.join(OUT, "exp2_results.json"), "w"), indent=2)


if __name__ == "__main__":
    main()
