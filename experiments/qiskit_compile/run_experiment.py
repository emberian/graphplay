"""
run_experiment.py
=================

Run the CompileML associative-recall experiment on the Qiskit Aer simulator and
validate it against the Lean prediction
    P_key(t) = sin^2(t*q),   q = 2*sqrt(N-1),   peak = 1  at  t = pi/(2q).

Three parts (mirroring the task):

  1. Noiseless validation: at the compiled time t* = pi/(2q) the measured
     flag/key population should be ~1 (perfect associative recall = PST).
  2. Noise -> deficit: add a depolarizing/dephasing noise model; the measured
     population at t* drops below 1.  The DEFICIT grows with the noise rate,
     qualitatively matching the Lean "deficit proportional to BreakingScore".
  3. PST curve scan: sweep t, plot P_key(t) vs the analytic sin^2(t*q),
     noiseless + noisy, and mark the predicted peak.  Saves a figure.

Everything routes through `host_to_circuit.get_backend(...)`, the single seam
to swap in a real IBM backend (see README + real_backend_stub()).
"""

from __future__ import annotations

import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from qiskit import transpile

from host_to_circuit import (
    data_flag_coupling, compiled_time, predicted_key_population,
    quotient_circuit, get_backend, honey_vertex_count, host_to_circuit,
    graph_circuit_exact,
)


SHOTS = 20000


# --------------------------------------------------------------------------- #
#  Noise models                                                               #
# --------------------------------------------------------------------------- #

def make_noise_model(p1: float = 0.0, p_dephase: float = 0.0):
    """A simple 1-qubit noise model: depolarizing error of rate `p1` and pure
    dephasing (phase-damping-like) of rate `p_dephase` after each gate.

    In the Lean picture, generic (non-block-diagonal) noise on the role cells
    has POSITIVE BreakingScore and so is *predicted* to produce a deficit; a
    partition-respecting (block-diagonal) channel has BreakingScore 0 and leaves
    the recall intact.  Depolarizing/dephasing on the quotient qubit mixes the
    data<->flag cells and so plays the role of positive-breaking-score noise.
    """
    from qiskit_aer.noise import (NoiseModel, depolarizing_error,
                                   phase_damping_error)

    nm = NoiseModel()
    if p1 > 0:
        err = depolarizing_error(p1, 1)
        nm.add_all_qubit_quantum_error(err, ["rx", "x", "u", "u3", "r", "sx", "rz"])
    if p_dephase > 0:
        err = phase_damping_error(p_dephase)
        nm.add_all_qubit_quantum_error(err, ["rx", "x", "u", "u3", "r", "sx", "rz"])
    return nm if (p1 > 0 or p_dephase > 0) else None


# --------------------------------------------------------------------------- #
#  Core measurement: key-cell population from shot counts                      #
# --------------------------------------------------------------------------- #

def measure_key_population(q: float, t: float, backend, shots: int = SHOTS,
                           trotter_steps: int | None = None) -> float:
    """Run the 1-qubit quotient recall circuit at time t and return the measured
    flag/key-cell population  P(|1>).  Optionally many Trotter steps if you want
    to exercise the general path (the quotient is exact in 1 step)."""
    qc = quotient_circuit(q, t, measure=True)
    tqc = transpile(qc, backend)
    result = backend.run(tqc, shots=shots).result()
    counts = result.get_counts()
    ones = counts.get("1", 0)
    return ones / shots


# --------------------------------------------------------------------------- #
#  Part 1+2: validation at the compiled time, noiseless and noisy             #
# --------------------------------------------------------------------------- #

def validate_at_compiled_time(n: int = 7, m: int = 19):
    q = data_flag_coupling(n, m)
    t_star = compiled_time(n, m)
    N = honey_vertex_count(n, m)

    print("=" * 70)
    print(f"CompileML recall experiment on Qiskit Aer  (IBM Heron n={n} m={m})")
    print(f"  N = 2nm = {N},   q = 2*sqrt(N-1) = {q:.4f}")
    print(f"  compiled transfer time t* = pi/(2q) = {t_star:.6f}")
    print(f"  Lean prediction P_key(t*) = sin^2(t* q) = "
          f"{predicted_key_population(q, t_star):.6f}")
    print("=" * 70)

    # noiseless
    bk = get_backend()
    p_noiseless = measure_key_population(q, t_star, bk)
    print(f"[noiseless sim]  measured P_key(t*) = {p_noiseless:.5f}   "
          f"(predicted 1.0)   deficit = {1 - p_noiseless:.5f}")

    # noisy, increasing rates -> growing deficit
    print("\n[noise -> deficit]  depolarizing rate p  vs  measured deficit:")
    rows = []
    for p in [0.0, 0.01, 0.02, 0.05, 0.1, 0.2]:
        nm = make_noise_model(p1=p)
        bk_n = get_backend(noise_model=nm)
        pk = measure_key_population(q, t_star, bk_n)
        deficit = 1 - pk
        rows.append((p, pk, deficit))
        print(f"    p = {p:5.3f}   P_key = {pk:.5f}   deficit = {deficit:.5f}")

    # monotone-deficit check
    deficits = [d for (_, _, d) in rows]
    mono = all(deficits[i] <= deficits[i + 1] + 0.01 for i in range(len(deficits) - 1))
    print(f"\n  deficit increases with noise rate: {mono}")
    return q, t_star, p_noiseless, rows


# --------------------------------------------------------------------------- #
#  Part 3: the PST curve scan                                                 #
# --------------------------------------------------------------------------- #

def scan_pst_curve(n: int = 7, m: int = 19, npts: int = 60,
                   noise_p: float = 0.05, shots: int = 8000,
                   outpath: str = "figures/pst_curve.png"):
    q = data_flag_coupling(n, m)
    t_star = compiled_time(n, m)

    ts = np.linspace(0.0, 2.0 * t_star, npts)  # one + a bit periods of sin^2
    analytic = np.array([predicted_key_population(q, t) for t in ts])

    bk_clean = get_backend()
    nm = make_noise_model(p1=noise_p)
    bk_noisy = get_backend(noise_model=nm)

    clean = np.array([measure_key_population(q, t, bk_clean, shots=shots) for t in ts])
    noisy = np.array([measure_key_population(q, t, bk_noisy, shots=shots) for t in ts])

    # fit quality
    rms_clean = float(np.sqrt(np.mean((clean - analytic) ** 2)))
    peak_idx = int(np.argmax(clean))
    print("\n[PST scan]")
    print(f"  analytic peak at t* = {t_star:.6f}")
    print(f"  measured (clean) peak at t = {ts[peak_idx]:.6f}, "
          f"P_key = {clean[peak_idx]:.4f}")
    print(f"  RMS(clean sim vs analytic sin^2) = {rms_clean:.4f}")
    print(f"  measured (noisy p={noise_p}) peak P_key = {noisy.max():.4f} "
          f"(deficit {1 - noisy.max():.4f})")

    plt.figure(figsize=(8.5, 5.2))
    plt.plot(ts, analytic, "-", color="black", lw=2,
             label=r"Lean prediction  $\sin^2(tq)$")
    plt.plot(ts, clean, "o", color="tab:blue", ms=5,
             label=f"Aer sim (noiseless, {shots} shots)")
    plt.plot(ts, noisy, "s", color="tab:red", ms=4, alpha=0.8,
             label=f"Aer sim (depol p={noise_p})")
    plt.axvline(t_star, color="tab:green", ls="--", lw=1.5,
                label=r"compiled $t^*=\pi/(2q)$")
    plt.scatter([t_star], [1.0], color="tab:green", zorder=5, s=60,
                marker="*", label="ideal recall (=1)")
    plt.xlabel("evolution time  t")
    plt.ylabel(r"flag/key-cell population  $P_\mathrm{key}(t)$")
    plt.title(f"CompileML PST recall curve  (IBM Heron quotient, q={q:.2f})\n"
              "Qiskit Aer sim vs Lean-predicted $\\sin^2(tq)$")
    plt.ylim(-0.03, 1.05)
    plt.legend(loc="upper right", fontsize=9)
    plt.grid(alpha=0.3)
    plt.tight_layout()
    import os
    os.makedirs(os.path.dirname(outpath), exist_ok=True)
    plt.savefig(outpath, dpi=140)
    print(f"  figure saved -> {outpath}")
    return ts, analytic, clean, noisy, rms_clean


# --------------------------------------------------------------------------- #
#  Bonus: host-JSON template sanity (the general N-vertex path)               #
# --------------------------------------------------------------------------- #

def demo_host_json(path: str):
    """Show host_to_circuit on an actual Graphplay host-JSON (template graph),
    and confirm the exact-CTQW circuit's measured distribution matches the
    matrix-exponential ground truth."""
    from scipy.linalg import expm
    hc = host_to_circuit(path, t=0.5, exact=True, measure=True)
    print(f"\n[host-JSON demo] {path}")
    print(f"  name: {hc.name!r}   template adjacency {hc.adjacency.shape}  "
          f"-> {hc.n_qubits} qubits   start vertex {hc.marked_index}")
    bk = get_backend()
    tqc = transpile(hc.circuit, bk)
    counts = bk.run(tqc, shots=20000).result().get_counts()
    N = hc.adjacency.shape[0]
    U = expm(-1j * 0.5 * hc.adjacency)
    psi0 = np.zeros(N, dtype=complex); psi0[hc.marked_index] = 1.0
    probs = np.abs(U @ psi0) ** 2
    print("  vertex   sim P     exact P")
    for v in range(N):
        key = format(v, f"0{hc.n_qubits}b")
        simp = counts.get(key, 0) / 20000
        print(f"    {v:3d}    {simp:.4f}   {probs[v]:.4f}")


# --------------------------------------------------------------------------- #

def main():
    q, t_star, p_noiseless, rows = validate_at_compiled_time(7, 19)
    scan_pst_curve(7, 19)
    # host-JSON template demos (small graphs, exact CTQW)
    import os
    examples = os.path.join(os.path.dirname(__file__), "..", "..", "examples")
    for fn in ["c5_equal_fiber.json", "hypercube_q3_equal_fiber.json"]:
        p = os.path.join(examples, fn)
        if os.path.exists(p):
            demo_host_json(p)
    print("\nDone.")


if __name__ == "__main__":
    main()
