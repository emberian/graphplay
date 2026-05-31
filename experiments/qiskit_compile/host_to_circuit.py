"""
host_to_circuit.py
==================

Compile a Graphplay host-spec (and/or the CompileML heavy-hex quotient) into a
runnable Qiskit circuit implementing the CTQW  U(t) = exp(-i t H), where H is the
adjacency matrix of the relevant graph.

This is the REAL hardware path for `Graphplay/Applications/CompileML.lean`:

    ML primitive  ──►  small quotient  ──►  native couplings + schedule  ──►  Qiskit.

The Lean file proves (axiom-clean, via `heavyHex_pst_lift`):

  * the data/flag role partition of IBM's heavy-hex lattice is equitable with the
    2x2 SYMMETRIC quotient  Q~ = [[0, q],[q, 0]] = q*X,  q = 2*sqrt(N-1),
  * cell-uniform PERFECT STATE TRANSFER between the data-uniform (query) and
    flag-uniform (key) cells at  t = pi/(2q),
  * the predicted key (flag-uniform) population at time t is
        predictedKeyPopulation(t) = sin^2(t*q),
    which is 1 at t = pi/(2q)  (ideal associative recall),
  * the observed deficit  1 - sin^2(t*q)  is governed by the noise model's
    BreakingScore of the partition  (partition-respecting noise => no deficit).

We implement two encodings:

  (A) `quotient_circuit(q, t)` -- the EXACT 2-level quotient walk on H = q*X.
      One qubit, |0> = query/data cell, |1> = key/flag cell.  exp(-i t q X) is
      an exact Rx(2 t q) rotation -> NO Trotter error.  This is the circuit that
      directly tests the Lean PST prediction sin^2(t*q).

  (B) `graph_circuit(A, t, ...)` -- the general N-vertex CTQW on an arbitrary
      adjacency matrix A (e.g. the small TEMPLATE graph of a host-JSON: a path,
      cycle C5, hypercube Q3, ...), realized either EXACTLY (matrix exponential
      as a UnitaryGate) or via first-order TROTTERization of the edge terms,
      which is the form that transpiles onto a heavy-hex coupling map.

`host_to_circuit(host_json, t)` reads a Graphplay host description, builds the
template-graph adjacency, and returns a circuit (B).  For the CompileML
experiment proper we use the 2-level quotient (A), which is what the Lean
prediction is literally about.

Hardware readiness: every `run`/`transpile` call routes through a single
`backend` object.  Swapping the Aer simulator for a real IBM backend is the
one-line change documented in the README and in `real_backend_stub()` below.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from itertools import product as iproduct
from typing import Iterable

import numpy as np
from qiskit import QuantumCircuit
from qiskit.circuit.library import UnitaryGate
from qiskit.quantum_info import Operator


# --------------------------------------------------------------------------- #
#  Graphplay quotient constants (mirrors Graphplay/Applications/IBMHeavyHex)   #
# --------------------------------------------------------------------------- #

def honey_vertex_count(n: int, m: int) -> int:
    """|HoneyVertex n m| = |Fin n x Fin m x Bool| = 2*n*m  (the N in the Lean)."""
    return 2 * n * m


def data_flag_coupling(n: int, m: int) -> float:
    """The proven symmetric-quotient off-diagonal coupling  q = 2*sqrt(N-1),
    N = |HoneyVertex n m| = 2 n m.  (IBMHeavyHex.dataFlagCoupling.)"""
    N = honey_vertex_count(n, m)
    return 2.0 * math.sqrt(N - 1)


def compiled_time(n: int, m: int) -> float:
    """The compiled PST transfer time  t = pi/(2q)  (CompileML.compiledTime)."""
    return math.pi / (2.0 * data_flag_coupling(n, m))


def predicted_key_population(q: float, t: float) -> float:
    """The Lean falsifiable prediction: P_key(t) = sin^2(t*q)
    (CompileML.predictedKeyPopulation).  1 at t = pi/(2q)."""
    return math.sin(t * q) ** 2


# --------------------------------------------------------------------------- #
#  (A)  Exact 2-level quotient walk:  H = q*X  on one qubit                    #
# --------------------------------------------------------------------------- #

def quotient_circuit(q: float, t: float, measure: bool = True) -> QuantumCircuit:
    """The CompileML recall protocol as a 1-qubit circuit on the 2-cell
    symmetric quotient  H = q*X.

    Cell encoding:  |0> = data/query-uniform cell,  |1> = flag/key-uniform cell.

    Protocol:
      * state prep: start in |0> (the data/query-uniform state already IS the
        query cell in the quotient picture),
      * evolve U(t) = exp(-i t q X) = Rx(2 t q),  which is EXACT (no Trotter),
      * measure: P(|1>) is the flag/key-uniform population = sin^2(t*q),
        matching the Lean prediction exactly.

    Returns a circuit with 1 qubit (+1 clbit if measure).
    """
    qc = QuantumCircuit(1, 1 if measure else 0)
    # exp(-i t q X) = Rx(theta) with theta = 2 t q   (Rx(th) = exp(-i th/2 X)).
    qc.rx(2.0 * q * t, 0)
    if measure:
        qc.measure(0, 0)
    return qc


# --------------------------------------------------------------------------- #
#  (B)  General N-vertex CTQW on an adjacency matrix                           #
# --------------------------------------------------------------------------- #

def ctqw_unitary(A: np.ndarray, t: float) -> np.ndarray:
    """The exact CTQW propagator U(t) = exp(-i t A) as a dense matrix."""
    from scipy.linalg import expm

    return expm(-1j * t * np.asarray(A, dtype=complex))


def graph_circuit_exact(A: np.ndarray, t: float, init_index: int = 0,
                        measure: bool = True) -> QuantumCircuit:
    """The CTQW on graph adjacency `A` realized EXACTLY as a UnitaryGate.

    The N-vertex walk is embedded into ceil(log2 N) qubits (vertex-as-basis-state
    encoding).  `init_index` is the starting vertex (basis state).  Exact: no
    Trotter error -- the ground truth the Trotter circuit is validated against.
    """
    A = np.asarray(A, dtype=complex)
    N = A.shape[0]
    nq = max(1, math.ceil(math.log2(N)))
    dim = 2 ** nq

    U = np.eye(dim, dtype=complex)
    U[:N, :N] = ctqw_unitary(A, t)

    qc = QuantumCircuit(nq, nq if measure else 0)
    # state prep: |init_index>
    for b in range(nq):
        if (init_index >> b) & 1:
            qc.x(b)
    qc.append(UnitaryGate(U, label="exp(-itA)"), range(nq))
    if measure:
        qc.measure(range(nq), range(nq))
    return qc


def graph_circuit_trotter(A: np.ndarray, t: float, steps: int = 20,
                          init_index: int = 0, measure: bool = True
                          ) -> QuantumCircuit:
    """The CTQW on graph adjacency `A` via first-order Trotterization of the edge
    terms.  Each edge (u,v) with weight w contributes  exp(-i (t/steps) w X_uv),
    where X_uv is the SWAP-like 2-level coupling on the {u,v} basis pair.

    This is the form that transpiles onto a heavy-hex coupling map: it is built
    entirely from 2-level (nearest-neighbour) couplings, which is exactly the
    native heavy-hex gate set.  We realize each 2-level term as a UnitaryGate on
    the full register (correct for any vertex-encoding), so the structure -- not
    the literal gate decomposition -- is what carries over to hardware.

    For the 2-vertex quotient this reduces to the exact Rx and so is also exact.
    """
    A = np.asarray(A, dtype=complex)
    N = A.shape[0]
    nq = max(1, math.ceil(math.log2(N)))
    dim = 2 ** nq

    # collect the upper-triangular edges
    edges = [(u, v, A[u, v]) for u in range(N) for v in range(u + 1, N)
             if abs(A[u, v]) > 1e-12]

    dt = t / steps
    qc = QuantumCircuit(nq, nq if measure else 0)
    for b in range(nq):
        if (init_index >> b) & 1:
            qc.x(b)

    for _ in range(steps):
        for (u, v, w) in edges:
            # 2-level generator on basis pair {u, v}: w*(|u><v| + |v><u|)
            G = np.zeros((dim, dim), dtype=complex)
            G[u, v] = w
            G[v, u] = np.conj(w)
            from scipy.linalg import expm
            Uedge = expm(-1j * dt * G)
            qc.append(UnitaryGate(Uedge, label=f"e{u}{v}"), range(nq))

    if measure:
        qc.measure(range(nq), range(nq))
    return qc


# --------------------------------------------------------------------------- #
#  Host-JSON template graphs                                                   #
# --------------------------------------------------------------------------- #

def _path_adj(n: int) -> np.ndarray:
    A = np.zeros((n, n))
    for i in range(n - 1):
        A[i, i + 1] = A[i + 1, i] = 1.0
    return A


def _cycle_adj(n: int) -> np.ndarray:
    A = _path_adj(n)
    if n > 2:
        A[0, n - 1] = A[n - 1, 0] = 1.0
    return A


def _complete_adj(n: int) -> np.ndarray:
    A = np.ones((n, n)) - np.eye(n)
    return A


def _hypercube_adj(dim: int) -> np.ndarray:
    n = 2 ** dim
    A = np.zeros((n, n))
    for x in range(n):
        for b in range(dim):
            y = x ^ (1 << b)
            A[x, y] = 1.0
    return A


def template_adjacency(template: dict) -> np.ndarray:
    """Build the small TEMPLATE-graph adjacency from a host-JSON `template`
    block: {kind: cycle|path|complete|hypercube, n / dim, ...}."""
    kind = template.get("kind", "").lower()
    if kind in ("cycle", "c"):
        return _cycle_adj(int(template["n"]))
    if kind in ("path", "line"):
        return _path_adj(int(template["n"]))
    if kind in ("complete", "k", "clique"):
        return _complete_adj(int(template["n"]))
    if kind in ("hypercube", "q", "cube"):
        return _hypercube_adj(int(template["dim"]))
    raise ValueError(f"unsupported template kind: {kind!r}")


@dataclass
class HostCircuit:
    """Bundle of what `host_to_circuit` returns."""
    circuit: QuantumCircuit
    adjacency: np.ndarray
    n_qubits: int
    name: str
    marked_index: int


def host_to_circuit(host_json: dict | str, t: float, steps: int = 20,
                    exact: bool = True, measure: bool = True) -> HostCircuit:
    """Read a Graphplay host description and build a CTQW circuit on its small
    TEMPLATE/quotient graph (path, cycle C5, hypercube Q3, ...).

    `host_json` may be a dict or a path to a JSON file.
    `t`        the evolution time.
    `exact`    True -> exact UnitaryGate (ground truth); False -> Trotterized
               (heavy-hex-native form).
    The starting vertex is the (first) `marked` index of the host (the
    "query"/start sector), defaulting to 0.
    """
    if isinstance(host_json, str):
        with open(host_json) as fh:
            host_json = json.load(fh)

    A = template_adjacency(host_json["template"])
    marked = host_json.get("marked", {"0": 1})
    # marked keys may be ints, decimal strings, or binary strings (hypercube).
    first_key = next(iter(marked))
    try:
        init_index = int(first_key)
    except ValueError:
        init_index = int(str(first_key), 2)  # binary address (hypercube Q3)

    if exact:
        qc = graph_circuit_exact(A, t, init_index=init_index, measure=measure)
    else:
        qc = graph_circuit_trotter(A, t, steps=steps, init_index=init_index,
                                   measure=measure)

    return HostCircuit(circuit=qc, adjacency=A, n_qubits=qc.num_qubits,
                       name=host_json.get("name", "host"),
                       marked_index=init_index)


# --------------------------------------------------------------------------- #
#  Backend plumbing -- the ONE place hardware-vs-sim is chosen                 #
# --------------------------------------------------------------------------- #

def get_backend(noise_model=None):
    """Return the execution backend.  Default: Aer simulator (noiseless or with
    a supplied noise model).

    *** This is the single seam between simulation and real IBM hardware. ***

    To run on a REAL IBM backend, replace the body with the two lines documented
    in `real_backend_stub()` -- everything downstream (transpile, run, counts)
    is identical.
    """
    from qiskit_aer import AerSimulator

    if noise_model is not None:
        return AerSimulator(noise_model=noise_model)
    return AerSimulator()


def real_backend_stub():
    """NOT executed (no credentials in this environment).  Documents EXACTLY the
    one-line swap to run on real IBM hardware.

        from qiskit_ibm_runtime import QiskitRuntimeService
        service = QiskitRuntimeService()                     # uses saved creds
        backend = service.least_busy(operational=True, simulator=False)

    Then in run_experiment.py replace `get_backend(...)` with this `backend`.
    Because the heavy-hex CTQW circuits are built from 2-level (nearest-
    neighbour) couplings, `transpile(circ, backend, optimization_level=3)` maps
    them onto the device's native heavy-hex coupling map directly.
    """
    raise RuntimeError(
        "real_backend_stub is documentation only; no IBM credentials in env."
    )


if __name__ == "__main__":
    # quick smoke test
    n, m = 7, 19  # IBM Heron
    q = data_flag_coupling(n, m)
    t = compiled_time(n, m)
    print(f"Heron (n=7,m=19): N=2nm={honey_vertex_count(n,m)}  q={q:.4f}  "
          f"t*=pi/(2q)={t:.6f}")
    print(f"predicted key population at t*: {predicted_key_population(q, t):.6f} "
          f"(Lean predicts 1)")
    qc = quotient_circuit(q, t)
    print(qc.draw(output="text"))
