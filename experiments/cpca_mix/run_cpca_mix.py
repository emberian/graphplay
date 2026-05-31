"""
run_cpca_mix.py — the CPCA-MIX experiment.

Measure CTQW uniform-mixing time under three phasings of a structured attention
host, across n and across two host families:

  H_0    unsigned real-symmetric host
  H_chi  cross-constant U(1) edge signing (the CPCA active edge phase)
  H_free free per-pair random phases (control)

Outputs:
  - figures/mixing_curves_<family>.png   (D(t) for the three phasings, per family)
  - figures/k4_reference.png             (exact Levine pi/(3 sqrt 3) check)
  - figures/tau_ratio_vs_n.png           (speedup ratio scan)
  - results.json                         (all measured numbers)
"""

import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

import cpca_lib as L


# ---------------------------------------------------------------------------
# 0.  The exact K_4 Levine reference (anchors the whole story)
# ---------------------------------------------------------------------------

def k4_reference():
    Bchi = L.levine_k4_signing()              # chiral K_4, B^2 = 3I
    H0 = L.host_complete(4)                    # unsigned K_4
    tau_star = np.pi / (3 * np.sqrt(3))        # 0.604600...

    # exact uniform distance of chiral K4 at tau_star (should be ~0)
    Dchi_star = L.uniform_distance(Bchi, tau_star)

    # curves
    T = 2.5
    ts = np.linspace(1e-6, T, 2000)
    Dchi = L.uniform_distance_curve(Bchi, ts)
    D0 = L.uniform_distance_curve(H0, ts)

    # best achievable distance on [0,T] for unsigned K4
    D0_min, t0_min = L.min_uniform_distance(H0, T, n_grid=4000)
    Dchi_min, tchi_min = L.min_uniform_distance(Bchi, T, n_grid=4000)

    return {
        "tau_star": tau_star,
        "Dchi_at_tau_star": Dchi_star,
        "D0_min_on_[0,T]": D0_min, "t0_argmin": t0_min,
        "Dchi_min_on_[0,T]": Dchi_min, "tchi_argmin": tchi_min,
        "ts": ts, "Dchi": Dchi, "D0": D0, "T": T,
    }


# ---------------------------------------------------------------------------
# 1.  Cross-constant signing for general n on a structured host.
#
# We build position cells (cells = i mod q) on a circulant/banded host so the
# partition is genuinely equitable, then optimize a small (q x q) cross-constant
# phase tau to minimize the uniform-mixing time of the host.  The optimization is
# over a low-dimensional U(1) connection (q*(q-1)/2 angles), exactly the
# "relative-position band" structure of the CPCA claim.
# ---------------------------------------------------------------------------

def optimize_cross_constant(H0, cells, q, T_max, eps, rng, n_restarts=12,
                            n_iter=400):
    """Random-search / coordinate-descent over the (q x q) antisymmetric angle
    matrix theta to minimize the *uniform-mixing time* of H_chi = sigma * H0.
    Objective: minimize the smallest-eps-achieving time; we use the area-style
    proxy = (min uniform distance on a coarse grid) primarily, then the crossing
    time.  Returns (best_theta, best_sigma, best_metric)."""
    n = H0.shape[0]
    ts = np.linspace(1e-6, T_max, 240)

    def metric(theta):
        sigma = L.cross_constant_signing(cells, L.hermitize_phase(theta))
        H = L.apply_signing(H0, sigma)
        D = L.uniform_distance_curve(H, ts)
        below = np.where(D <= eps)[0]
        if len(below):
            # achieves eps: reward by (negative) crossing time, smaller is better
            return -1.0 + ts[below[0]] / T_max  # in [-1, 0)
        else:
            return float(np.min(D))             # >= eps, smaller is better

    best_theta = None
    best_m = np.inf
    for r in range(n_restarts):
        theta = rng.uniform(-np.pi, np.pi, size=(q, q))
        m = metric(theta)
        # coordinate-descent perturbations
        step = 0.8
        for it in range(n_iter):
            i, j = rng.integers(0, q), rng.integers(0, q)
            if i == j:
                continue
            old = theta[i, j]
            theta[i, j] = old + rng.normal(0, step)
            mm = metric(theta)
            if mm < m:
                m = mm
            else:
                theta[i, j] = old
            if it % 120 == 119:
                step *= 0.6
        if m < best_m:
            best_m = m
            best_theta = theta.copy()
    sigma = L.cross_constant_signing(cells, L.hermitize_phase(best_theta))
    return best_theta, sigma, best_m


def best_free_signing(H0, T_max, eps, rng, n_samples=24):
    """Best-of-n_samples free per-pair signing, scored by the same metric used
    for cross-constant (min uniform distance / crossing time)."""
    n = H0.shape[0]
    ts = np.linspace(1e-6, T_max, 240)

    def metric_of(sigma):
        H = L.apply_signing(H0, sigma)
        D = L.uniform_distance_curve(H, ts)
        below = np.where(D <= eps)[0]
        if len(below):
            return -1.0 + ts[below[0]] / T_max
        return float(np.min(D))

    best_sigma = None
    best_m = np.inf
    for _ in range(n_samples):
        sigma = L.free_phase_signing(n, rng)
        m = metric_of(sigma)
        if m < best_m:
            best_m = m
            best_sigma = sigma
    return best_sigma, best_m


# ---------------------------------------------------------------------------
# 2.  Run one (family, n) configuration: build the 3 hosts, measure tau_mix.
# ---------------------------------------------------------------------------

def run_config(family, n, q, eps, T_max, seed=0, bandwidth=None):
    rng = np.random.default_rng(seed)

    if family == "complete":
        H0 = L.host_complete(n)
    elif family == "band":
        if bandwidth is None:
            bandwidth = max(1, n // 8)
        H0 = L.host_band(n, bandwidth)
    else:
        raise ValueError(family)

    cells = np.arange(n) % q   # position cells (relative-position bands)

    # H_chi: optimized cross-constant signing
    theta, sigma_cc, m_cc = optimize_cross_constant(
        H0, cells, q, T_max, eps, rng)
    H_chi = L.apply_signing(H0, sigma_cc)

    # H_free: best free per-pair signing
    sigma_free, m_free = best_free_signing(H0, T_max, eps, rng)
    H_free = L.apply_signing(H0, sigma_free)

    # measure tau_mix for each
    tau0, D0min = L.tau_mix(H0, eps, T_max)
    tauchi, Dchimin = L.tau_mix(H_chi, eps, T_max)
    taufree, Dfreemin = L.tau_mix(H_free, eps, T_max)

    # equitable-quotient check: cross-constant must descend, free generically not
    ok_cc, viol_cc = L.is_equitable(H_chi, cells)
    ok_0, viol_0 = L.is_equitable(H0, cells)
    ok_free, viol_free = L.is_equitable(H_free, cells)

    return {
        "family": family, "n": n, "q": q, "eps": eps, "T_max": T_max,
        "bandwidth": bandwidth,
        "tau0": tau0, "tauchi": tauchi, "taufree": taufree,
        "D0min": D0min, "Dchimin": Dchimin, "Dfreemin": Dfreemin,
        "equitable_H0": (ok_0, viol_0),
        "equitable_Hchi": (ok_cc, viol_cc),
        "equitable_Hfree": (ok_free, viol_free),
        # keep hosts for plotting in caller
        "_H0": H0, "_Hchi": H_chi, "_Hfree": H_free,
    }


# ---------------------------------------------------------------------------
# 3.  Figures
# ---------------------------------------------------------------------------

def plot_k4(ref):
    fig, ax = plt.subplots(figsize=(7, 4.2))
    ax.plot(ref["ts"], ref["D0"], label="H_0  (unsigned K_4)", color="C0")
    ax.plot(ref["ts"], ref["Dchi"], label="H_chi (Levine signing)", color="C3")
    ax.axvline(ref["tau_star"], ls="--", color="k", lw=1,
               label=r"$\tau^*=\pi/(3\sqrt{3})\approx%.4f$" % ref["tau_star"])
    ax.set_xlabel("time $t$")
    ax.set_ylabel(r"uniform-mixing distance $D(t)=\max_{uv}|M(t)_{uv}-1/n|$")
    ax.set_title("K_4 reference: chiral hits exact uniform mixing; unsigned does not")
    ax.legend()
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig("figures/k4_reference.png", dpi=130)
    plt.close(fig)


def plot_curves(cfg, family, eps):
    ts = np.linspace(1e-6, cfg["T_max"], 1500)
    D0 = L.uniform_distance_curve(cfg["_H0"], ts)
    Dchi = L.uniform_distance_curve(cfg["_Hchi"], ts)
    Dfree = L.uniform_distance_curve(cfg["_Hfree"], ts)
    fig, ax = plt.subplots(figsize=(7.5, 4.5))
    ax.plot(ts, D0, label="H_0 unsigned", color="C0")
    ax.plot(ts, Dchi, label="H_chi cross-constant", color="C3")
    ax.plot(ts, Dfree, label="H_free per-pair", color="C2", alpha=0.8)
    ax.axhline(eps, ls=":", color="k", lw=1, label=f"eps={eps}")
    for tau, c, lab in [(cfg["tau0"], "C0", "tau_0"),
                        (cfg["tauchi"], "C3", "tau_chi"),
                        (cfg["taufree"], "C2", "tau_free")]:
        if tau is not None:
            ax.axvline(tau, ls="--", color=c, lw=1)
    ax.set_xlabel("time $t$")
    ax.set_ylabel(r"$D(t)$")
    ax.set_title(f"CPCA-MIX  family={family}  n={cfg['n']}  q={cfg['q']}")
    ax.legend(fontsize=8)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(f"figures/mixing_curves_{family}_n{cfg['n']}.png", dpi=130)
    plt.close(fig)


def plot_ratio(records, fname="figures/tau_ratio_vs_n.png"):
    fig, ax = plt.subplots(figsize=(7.5, 4.5))
    fams = sorted(set(r["family"] for r in records))
    for fam in fams:
        rs = [r for r in records if r["family"] == fam]
        ns = [r["n"] for r in rs]
        ratios = []
        for r in rs:
            if r["tauchi"] and r["tau0"]:
                ratios.append(r["tau0"] / r["tauchi"])
            elif r["tauchi"] and not r["tau0"]:
                ratios.append(np.nan)  # unsigned never mixed -> infinite speedup
            else:
                ratios.append(np.nan)
        ax.plot(ns, ratios, "o-", label=f"{fam}: tau_0/tau_chi")
    ax.axhline(1.0, ls=":", color="k", lw=1, label="ratio = 1 (no speedup)")
    ax.set_xlabel("n (tokens)")
    ax.set_ylabel(r"speedup ratio $\tau_0/\tau_\chi$")
    ax.set_title("Chiral uniform-mixing speedup vs n")
    ax.legend()
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig(fname, dpi=130)
    plt.close(fig)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    eps = 0.02
    records = []

    # 0. K_4 reference
    ref = k4_reference()
    plot_k4(ref)
    print("K_4 reference:")
    print(f"  tau* = {ref['tau_star']:.6f}")
    print(f"  D_chi(tau*) = {ref['Dchi_at_tau_star']:.3e}  (exact uniform mixing)")
    print(f"  unsigned K_4 best D on [0,{ref['T']}] = {ref['D0_min_on_[0,T]']:.4f}"
          f" at t={ref['t0_argmin']:.3f}  (does NOT reach uniform)")

    # 1. scans.  complete graph K_n and banded host.
    scans = [
        ("complete", [4, 6, 8, 10, 12], 2),  # cells = parity (q=2) for K_n
        ("band",     [16, 24, 32, 48],  4),  # banded relative-position host, q=4 cells
    ]
    Tmap = {"complete": 4.0, "band": 12.0}

    for family, ns, q in scans:
        for n in ns:
            qq = q if n % q == 0 else q
            T_max = Tmap[family]
            print(f"\n=== family={family} n={n} q={qq} eps={eps} ===")
            cfg = run_config(family, n, qq, eps, T_max, seed=12345 + n)
            print(f"  tau0   = {cfg['tau0']}   (Dmin={cfg['D0min']:.4f})")
            print(f"  tauchi = {cfg['tauchi']}   (Dmin={cfg['Dchimin']:.4f})")
            print(f"  taufree= {cfg['taufree']}   (Dmin={cfg['Dfreemin']:.4f})")
            print(f"  equitable: H0={cfg['equitable_H0']}  "
                  f"Hchi={cfg['equitable_Hchi']}  Hfree={cfg['equitable_Hfree']}")
            plot_curves(cfg, family, eps)
            # strip hosts before storing
            rec = {k: v for k, v in cfg.items() if not k.startswith("_")}
            records.append(rec)

    plot_ratio(records)

    # serialize
    out = {
        "eps": eps,
        "k4_reference": {
            "tau_star": ref["tau_star"],
            "Dchi_at_tau_star": ref["Dchi_at_tau_star"],
            "D0_min": ref["D0_min_on_[0,T]"], "t0_argmin": ref["t0_argmin"],
            "Dchi_min": ref["Dchi_min_on_[0,T]"], "tchi_argmin": ref["tchi_argmin"],
        },
        "records": records,
    }
    with open("results.json", "w") as f:
        json.dump(out, f, indent=2, default=lambda o: (
            list(o) if isinstance(o, tuple) else float(o)))
    print("\nWrote results.json and figures/.")


if __name__ == "__main__":
    main()
