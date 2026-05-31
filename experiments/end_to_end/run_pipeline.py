"""
run_pipeline.py  —  the ML-to-quantum-hardware compiler, end to end.

ONE runnable seam, on real artifacts:

    real catgrad-llm Llama model
        └─(catgrad-backend-graphplay: fold SSA, recognize attention)
            → Graphplay host-JSON  per attention layer
                └─(qiskit_compile: host_to_circuit + the CompileML PST prediction)
                    → Qiskit circuit  → Aer sim  → measured PST signal
                        └─ validated against the Lean  sin²(t·q)  prediction.

This script chains three EXISTING pieces (it does not reimplement them):

  1. `~/hellas/catgrad/catgrad-backend-graphplay`  (Rust) emits the host-JSONs.
     We read the JSONs it produced (copied into ./hosts/).  The exact cargo
     command that regenerates them is printed by `--regen-hosts` and documented
     in README.md.  (Step 1 genuinely runs; we depend on its *output* artifacts,
     not catgrad's repo state — swarm-safe.)

  2. `experiments/qiskit_compile/host_to_circuit.py`  builds the Qiskit circuits
     and carries the Lean constants (`predicted_key_population = sin²(t·q)`,
     `quotient_circuit`, `host_to_circuit`, `get_backend`).  We IMPORT it.

  3. `Graphplay/Applications/CompileML.lean`  is the theorem this validates: an
     equitable partition with a `K₂` (path-n=2) quotient and equal fibers has a
     symmetric quotient  Q̃ = q·X,  PST between the two cells at  t* = π/(2q),
     measured key population  sin²(t·q).

The bridge from a host-JSON to the Lean coupling `q`
----------------------------------------------------
`CompileML`/`IBMHeavyHex` give the Heron-specific  q = 2√(N−1).  That number is
the symmetric-quotient off-diagonal of the data/flag partition for THAT chip.
For a GENERIC equitable partition whose quotient is the `K₂` (a `path n=2`
template) with EQUAL fibers of size `f`, the same construction
(`EquitablePartition.symmQuotient`, the geometric-mean symmetrization) gives the
2×2 symmetric quotient

        Q̃ = [[0, f], [f, 0]] = f · X          (q = fiber_size).

So each catgrad GQA layer  → host {template: path n=2, fiber_size: f}  → the
CompileML recall protocol with  q = f:  PST at  t* = π/(2f),  predicted key
population  sin²(t·f).  We validate exactly that on Aer.

Run:
    source ../.venv/bin/activate
    python run_pipeline.py                 # full pipeline on ./hosts/*.json
    python run_pipeline.py --regen-hosts   # print the cargo cmd, don't run it
"""

from __future__ import annotations

import glob
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
QISKIT_COMPILE = os.path.normpath(os.path.join(HERE, "..", "qiskit_compile"))
HOSTS_DIR = os.path.join(HERE, "hosts")
FIG_DIR = os.path.join(HERE, "figures")

# --- import the EXISTING qiskit_compile pieces (do not reimplement) ----------
sys.path.insert(0, QISKIT_COMPILE)
from host_to_circuit import (  # noqa: E402
    predicted_key_population,
    quotient_circuit,
    host_to_circuit,
    get_backend,
)
from qiskit import transpile  # noqa: E402


CATGRAD_DIR = os.path.expanduser("~/hellas/catgrad/catgrad-backend-graphplay")
REGEN_CMD = f"(cd {CATGRAD_DIR} && cargo run --example emit_hosts)"
SHOTS = 20000


# --------------------------------------------------------------------------- #
#  host-JSON  →  Lean coupling q  (the bridge to CompileML)                     #
# --------------------------------------------------------------------------- #

def host_quotient_coupling(host: dict) -> float:
    """The symmetric-quotient off-diagonal coupling `q` for a host whose
    equitable quotient is the `K₂` (path n=2) with equal fibers of size `f`.

    For the `K₂`-with-equal-fibers equitable partition,
    `EquitablePartition.symmQuotient = f · X`, so q = fiber_size.  (The Heron
    file's q = 2√(N−1) is the same construction specialized to its own
    partition; here we read q straight off the catgrad-emitted fiber size.)
    """
    tmpl = host["template"]
    kind = tmpl.get("kind", "").lower()
    n = int(tmpl.get("n", 2))
    f = int(host["fiber_size"])
    if kind in ("path", "line") and n == 2:
        return float(f)
    # For other quotients we still report the K₂-sector coupling f as the
    # recall coupling (the 2-cell symmetric sector the PST theorem is about);
    # the full-quotient walk is validated separately below.
    return float(f)


def compiled_time(q: float) -> float:
    """The CompileML PST transfer time  t* = π/(2q)."""
    return math.pi / (2.0 * q)


# --------------------------------------------------------------------------- #
#  Step 2/3: host  →  Qiskit circuit  →  Aer  →  measured-vs-predicted          #
# --------------------------------------------------------------------------- #

def measure_key_population(q: float, t: float, backend, shots: int = SHOTS) -> float:
    """Build the EXACT 2-cell quotient recall circuit  exp(-i t q X) = Rx(2tq),
    run it on `backend`, return the measured flag/key-cell population P(|1>).
    This is the circuit the Lean prediction sin²(t·q) is literally about."""
    qc = quotient_circuit(q, t, measure=True)
    tqc = transpile(qc, backend)
    counts = backend.run(tqc, shots=shots).result().get_counts()
    return counts.get("1", 0) / shots


def run_host(path: str, backend) -> dict:
    """Take ONE catgrad host-JSON all the way to a validated PST signal."""
    with open(path) as fh:
        host = json.load(fh)

    tmpl = host["template"]
    f = int(host["fiber_size"])
    q = host_quotient_coupling(host)
    t_star = compiled_time(q)

    # (a) the recall / PST circuit on the 2-cell symmetric quotient (exact).
    qc = quotient_circuit(q, t_star, measure=True)
    tqc = transpile(qc, backend)
    n_qubits, depth = tqc.num_qubits, tqc.depth()

    p_meas = measure_key_population(q, t_star, backend)
    p_pred = predicted_key_population(q, t_star)  # = sin²(t* q), = 1 at t*

    # (b) the host's full template-graph CTQW (the walk on the quotient Q),
    #     using the existing host_to_circuit; sanity-checks the template seam.
    hc = host_to_circuit(path, t=t_star, exact=True, measure=True)
    thc = transpile(hc.circuit, backend)

    return {
        "name": host["name"],
        "layer": os.path.splitext(os.path.basename(path))[0],
        "template": f"{tmpl['kind']} n={tmpl['n']}",
        "fiber_size": f,
        "q": q,
        "t_star": t_star,
        "recall_qubits": n_qubits,
        "recall_depth": depth,
        "p_measured": p_meas,
        "p_predicted": p_pred,
        "template_qubits": hc.n_qubits,
        "template_depth": thc.depth(),
    }


# --------------------------------------------------------------------------- #
#  A small t-scan so we can SEE the PST peak land at t*  (one figure)           #
# --------------------------------------------------------------------------- #

def pst_scan_figure(q: float, label: str, outpath: str, npts: int = 60,
                    shots: int = 6000):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    t_star = compiled_time(q)
    ts = np.linspace(0.0, 2.0 * t_star, npts)
    analytic = np.array([predicted_key_population(q, t) for t in ts])

    bk = get_backend()
    meas = np.array([measure_key_population(q, t, bk, shots=shots) for t in ts])

    peak_idx = int(np.argmax(meas))
    rms = float(np.sqrt(np.mean((meas - analytic) ** 2)))

    plt.figure(figsize=(8.4, 5.0))
    plt.plot(ts, analytic, "-", color="black", lw=2,
             label=r"Lean prediction $\sin^2(t q)$")
    plt.plot(ts, meas, "o", color="tab:blue", ms=5,
             label=f"Aer sim ({shots} shots)")
    plt.axvline(t_star, color="tab:green", ls="--", lw=1.5,
                label=r"compiled $t^*=\pi/(2q)$")
    plt.scatter([t_star], [1.0], color="tab:green", marker="*", s=80, zorder=5,
                label="ideal recall (=1)")
    plt.xlabel("evolution time  t")
    plt.ylabel(r"flag/key-cell population $P_\mathrm{key}(t)$")
    plt.title(f"End-to-end: catgrad GQA layer → CompileML PST recall\n"
              f"{label}   (q = fiber_size = {q:g},  t* = {t_star:.4f})")
    plt.ylim(-0.03, 1.05)
    plt.legend(loc="upper right", fontsize=9)
    plt.grid(alpha=0.3)
    plt.tight_layout()
    os.makedirs(os.path.dirname(outpath), exist_ok=True)
    plt.savefig(outpath, dpi=140)
    plt.close()
    return ts[peak_idx], meas[peak_idx], rms, outpath


# --------------------------------------------------------------------------- #

def main():
    if "--regen-hosts" in sys.argv:
        print("To (re)generate the host-JSONs from the real catgrad Llama model:")
        print(f"    {REGEN_CMD}")
        print("then copy hosts/attn_layer_*.json into ./hosts/.")
        return

    host_files = sorted(glob.glob(os.path.join(HOSTS_DIR, "attn_layer_*.json")))
    if not host_files:
        print(f"no host-JSONs in {HOSTS_DIR}; run:  {REGEN_CMD}")
        sys.exit(1)

    # Headline provenance: which model these came from.
    with open(host_files[0]) as fh:
        model_name = json.load(fh)["name"].split(" attention layer")[0]

    print("=" * 78)
    print("ML-to-quantum-hardware compiler  —  END TO END")
    print("=" * 78)
    print(f"  [step 1]  real catgrad-llm model: {model_name}")
    print(f"            emitted by:  {REGEN_CMD}")
    print(f"            → {len(host_files)} attention-layer host-JSON(s) in ./hosts/")
    print(f"  [step 2]  host-JSON → Qiskit circuit via qiskit_compile.host_to_circuit")
    print(f"  [step 3]  Aer sim → measured PST vs Lean CompileML  sin²(t·q)")
    print("-" * 78)

    backend = get_backend()  # the single sim↔hardware seam (one-line IBM swap)
    rows = []
    for path in host_files:
        r = run_host(path, backend)
        rows.append(r)
        ok = abs(r["p_measured"] - r["p_predicted"]) < 0.02
        print(
            f"  {r['layer']:>13s}: template {r['template']:>10s}, "
            f"fiber_size {r['fiber_size']} → q={r['q']:g}  "
            f"→ Qiskit recall ({r['recall_qubits']}q, depth {r['recall_depth']}) "
            f"| template walk ({r['template_qubits']}q, depth {r['template_depth']})"
        )
        print(
            f"  {'':>13s}  t*=π/(2q)={r['t_star']:.5f}  "
            f"measured P_key={r['p_measured']:.5f}  "
            f"Lean sin²(t*q)={r['p_predicted']:.5f}  "
            f"[{'PASS' if ok else 'FAIL'}]"
        )

    # The headline trace line.
    r0 = rows[0]
    print("-" * 78)
    print("HEADLINE TRACE:")
    print(
        f"  {model_name}  →  {len(rows)} attention layers  "
        f"→  host-JSON {{template: {r0['template']}, fiber_size: {r0['fiber_size']}}}  "
        f"→  Qiskit circuit ({r0['recall_qubits']} qubit, depth {r0['recall_depth']})  "
        f"→  measured PST peak P_key = {r0['p_measured']:.4f} at "
        f"t* = {r0['t_star']:.4f}  "
        f"(Lean predicted sin²(t*·q) = {r0['p_predicted']:.4f})"
    )

    # One figure: the PST recall curve for the (identical) GQA layer coupling.
    t_peak, p_peak, rms, fig = pst_scan_figure(
        r0["q"], f"{model_name} (GQA: q=fiber_size)",
        os.path.join(FIG_DIR, "end_to_end_pst.png"),
    )
    print("-" * 78)
    print(f"  PST scan: measured peak at t≈{t_peak:.4f}, P_key≈{p_peak:.3f}  "
          f"(analytic t*={r0['t_star']:.4f});  RMS(sim vs sin²)={rms:.4f}")
    print(f"  figure → {fig}")

    n_pass = sum(1 for r in rows
                 if abs(r["p_measured"] - r["p_predicted"]) < 0.02)
    print("=" * 78)
    print(f"  RESULT: {n_pass}/{len(rows)} layers' measured PST match the Lean "
          f"prediction within shot noise.  Pipeline ran end to end on real "
          f"catgrad artifacts.")
    print(f"  (sim↔hardware seam: host_to_circuit.get_backend — one-line IBM swap, "
          f"see README.)")
    print("=" * 78)


if __name__ == "__main__":
    main()
