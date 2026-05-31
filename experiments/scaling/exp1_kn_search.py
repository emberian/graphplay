#!/usr/bin/env python3
"""
Experiment 1 — Quantum spatial search on the complete graph K_n.

CTQW spatial search Hamiltonian:  H = -gamma * A(K_n) - |w><w|,
with the Childs-Goldstone optimal coupling gamma = 1/n (the uniform-state
eigenvalue of A(K_n)/n; for K_n, A = J - I so the optimal gamma is 1/n).

We exploit the EXACT 2-dim invariant subspace span{|w>, |u>} (marked vertex
and uniform-over-the-rest), reducing the N=n dynamics to a 2x2 Hermitian
generator -- mirroring the Lean `completeGraph_2d_block` / `reducedH n`.
The 2x2 reduced generator (unnormalized basis {|w>,|u>}) is

    M2 = [[ -1,           -gamma*(n-1) ],
          [ -gamma,       -gamma*(n-2) ]]

and the success amplitude is  <w| exp(-i t H) |w> = (exp(-i t M2))_{00}.
We diagonalize the *orthonormalized* 2x2 block to get the survival/transition
probability on the marked vertex, scan t, and find the first time-to-peak T*(n)
and the peak success probability.

CLAIM target: T* propto sqrt(n), peak -> 1 (matching the Lean exact amplitude
sqrt((n-1)/n) at t ~ (pi/2) sqrt(n)).
"""
import numpy as np
import scipy.linalg as sla
import json, os

OUT = os.path.dirname(os.path.abspath(__file__))
FIGS = os.path.join(OUT, "figures")
os.makedirs(FIGS, exist_ok=True)


def reduced_block(n):
    """Exact 2x2 reduced search generator on the ORTHONORMAL {|w>, |u_hat>} basis.

    |w> normalized (norm 1). |u> = sum_{v!=w} |v>, norm sqrt(n-1); |u_hat> = |u>/sqrt(n-1).
    H = -gamma*A - |w><w|, gamma = 1/n.
    A|w> = |u> = sqrt(n-1)|u_hat>.
    A|u_hat> = ((n-2)|u> + (n-1)|w>)/sqrt(n-1) = (n-2)|u_hat> + sqrt(n-1)|w>.
    Oracle |w><w|: |w>->|w>, |u_hat>->0.
    So in {|w>,|u_hat>}:
      H|w>      = -gamma*sqrt(n-1)|u_hat> - |w>
      H|u_hat>  = -gamma*( sqrt(n-1)|w> + (n-2)|u_hat> )
    """
    g = 1.0 / n
    s = np.sqrt(n - 1.0)
    H = np.array([
        [-1.0,          -g * s],
        [-g * s,        -g * (n - 2.0)],
    ], dtype=complex)
    # Hermitian by construction (off-diagonals equal real).
    return H


def success_prob_curve(n, ts):
    """Success probability |<w|psi(t)>|^2 starting from |w> ... actually we start
    from the uniform state |s> = (1/sqrt(n)) sum_v |v>, the standard spatial-search
    initial state. In the {|w>,|u_hat>} basis, |s> = (1/sqrt(n))|w> + (sqrt(n-1)/sqrt(n))|u_hat>.
    Success = |<w|psi(t)>|^2 = |(exp(-iHt) psi0)_0|^2.
    """
    H = reduced_block(n)
    evals, evecs = np.linalg.eigh(H)
    psi0 = np.array([1.0 / np.sqrt(n), np.sqrt((n - 1.0) / n)], dtype=complex)
    # precompute in eigenbasis
    c = evecs.conj().T @ psi0  # coefficients
    probs = np.empty_like(ts)
    for k, t in enumerate(ts):
        phase = np.exp(-1j * evals * t)
        psi = evecs @ (phase * c)
        probs[k] = abs(psi[0]) ** 2
    return probs


def find_peak(n):
    # Search window: T* ~ (pi/2) sqrt(n); scan generously to 3*sqrt(n).
    tmax = 3.0 * np.sqrt(n)
    ts = np.linspace(0, tmax, 6000)
    p = success_prob_curve(n, ts)
    idx = int(np.argmax(p))
    # refine with a local fine scan around the coarse peak
    t0 = ts[max(0, idx - 5)]
    t1 = ts[min(len(ts) - 1, idx + 5)]
    tsf = np.linspace(t0, t1, 4000)
    pf = success_prob_curve(n, tsf)
    j = int(np.argmax(pf))
    return tsf[j], pf[j]


def main():
    ns = [16, 32, 64, 128, 256, 512, 1024]
    Tstar, peak = [], []
    for n in ns:
        T, pk = find_peak(n)
        Tstar.append(T)
        peak.append(pk)
        print(f"n={n:5d}  T*={T:9.4f}  (pi/2)sqrt(n)={np.pi/2*np.sqrt(n):9.4f}  peak={pk:.6f}  sqrt((n-1)/n)^2={(n-1)/n:.6f}")

    ns = np.array(ns, float)
    Tstar = np.array(Tstar)
    peak = np.array(peak)

    # Fit T* = C * n^a  (log-log linear fit)
    a, logC = np.polyfit(np.log(ns), np.log(Tstar), 1)
    C = np.exp(logC)
    resid = np.log(Tstar) - (a * np.log(ns) + logC)
    rms = np.sqrt(np.mean(resid ** 2))
    # std error of slope
    nfit = len(ns)
    sx = np.std(np.log(ns))
    se_a = rms / (sx * np.sqrt(nfit))
    print(f"\nFIT: T* = {C:.4f} * n^{a:.4f}  (+-{se_a:.4f}), log-log RMS resid={rms:.4e}")
    print(f"Expected exponent 0.5 (sqrt(N)); expected C ~ pi/2 = {np.pi/2:.4f}")

    # Plot
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 4.5))
    ax1.loglog(ns, Tstar, "o", ms=8, label="measured $T^*(n)$")
    nn = np.linspace(ns[0], ns[-1], 200)
    ax1.loglog(nn, C * nn ** a, "-", label=fr"fit $T^*={C:.3f}\,n^{{{a:.3f}}}$")
    ax1.loglog(nn, np.pi / 2 * np.sqrt(nn), "--", color="gray", label=r"theory $(\pi/2)\sqrt{n}$")
    ax1.set_xlabel("n  (= N, vertices of $K_n$)")
    ax1.set_ylabel("time-to-peak $T^*$")
    ax1.set_title(f"K_n CTQW search:  $T^* \\propto n^{{{a:.3f}\\pm{se_a:.3f}}}$")
    ax1.legend(); ax1.grid(True, which="both", alpha=0.3)

    ax2.semilogx(ns, peak, "s-", ms=8, color="C2", label="peak success prob")
    ax2.semilogx(ns, (ns - 1) / ns, "--", color="gray", label=r"Lean exact $(n-1)/n$")
    ax2.set_xlabel("n"); ax2.set_ylabel("peak success probability")
    ax2.set_ylim(0.9, 1.005)
    ax2.set_title("peak success $\\to 1$"); ax2.legend(); ax2.grid(True, alpha=0.3)
    fig.tight_layout()
    figpath = os.path.join(FIGS, "exp1_kn_search.png")
    fig.savefig(figpath, dpi=130)
    print("saved", figpath)

    json.dump({
        "ns": ns.tolist(), "Tstar": Tstar.tolist(), "peak": peak.tolist(),
        "fit_exponent": a, "fit_se": se_a, "fit_C": C, "loglog_rms": rms,
    }, open(os.path.join(OUT, "exp1_results.json"), "w"), indent=2)


if __name__ == "__main__":
    main()
