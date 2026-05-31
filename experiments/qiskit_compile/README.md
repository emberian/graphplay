# qiskit_compile — the REAL hardware path for `CompileML`

Compile a Graphplay host-spec into a runnable **Qiskit** circuit and validate it
on the simulator, making *"compiling walks to IBM's quantum hardware"* concrete:
sim-first, ready to point at a real backend with a one-line change.

This is the executable companion to `Graphplay/Applications/CompileML.lean` and
`Graphplay/Applications/IBMHeavyHex.lean`.

```
ML primitive  ──►  small 2-cell quotient  ──►  native heavy-hex couplings + schedule  ──►  Qiskit circuit  ──►  Aer sim (▶ ready for real IBM backend)
```

## What Lean proves (and what we test here)

`CompileML` proves, axiom-clean (via `heavyHex_pst_lift`):

- IBM's heavy-hex lattice has an **equitable** data/flag role partition whose
  `2×2` **symmetric quotient** is `Q̃ = [[0,q],[q,0]] = q·X`, with
  `q = 2√(N−1)`, `N = |HoneyVertex| = 2nm` (for Heron `(n,m)=(7,19)`, `N=266`,
  `q ≈ 32.56`).
- **Cell-uniform perfect state transfer** (associative recall) between the
  data/query-uniform cell and the flag/key-uniform cell at the compiled time
  `t* = π/(2q)`.
- The falsifiable prediction: the measured flag/key-uniform population is
  `predictedKeyPopulation(t) = sin²(t·q)`, equal to `1` at `t*` (ideal recall),
  with the observed **deficit `1 − sin²(t·q)` governed by the noise model's
  `BreakingScore`** of the partition (partition-respecting noise ⇒ no deficit;
  generic noise that mixes the two cells ⇒ positive deficit).

## Files

| file | what it does |
|---|---|
| `host_to_circuit.py` | `host_to_circuit(host_json, t)` builds a CTQW circuit `exp(-i t H)` from a Graphplay host-spec (template graph). `quotient_circuit(q,t)` is the exact 2-level recall circuit `exp(-i t q X) = Rx(2tq)`. `graph_circuit_exact/trotter` for the general N-vertex walk. `get_backend(...)` is the **single sim↔hardware seam**. |
| `run_experiment.py` | the recall experiment: noiseless validation at `t*`, noise→deficit sweep, the PST-curve scan + figure, and host-JSON template demos. |
| `figures/pst_curve.png` | the PST recall curve: Aer sim vs the Lean-predicted `sin²(tq)`, noiseless + noisy, peak marked at `t* = π/(2q)`. |

## Run it

```bash
source ../.venv/bin/activate           # qiskit, qiskit-aer, scipy, matplotlib
python run_experiment.py               # validation + sweep + figure + host demos
python host_to_circuit.py              # smoke test (prints q, t*, the circuit)
```

## (a) The sim reproduces the Lean-predicted PST signal ✅ (validated)

Measured on Aer (noiseless, Heron quotient `q ≈ 32.56`, `t* = π/(2q) ≈ 0.04825`,
20 000 shots):

```
[noiseless sim]  measured P_key(t*) = 1.00000   (Lean predicts 1.0)   deficit = 0.00000
[PST scan]  measured (clean) peak at t ≈ 0.0474, P_key ≈ 0.999
            RMS(clean sim vs analytic sin²) = 0.0042   (pure shot noise)
```

The blue Aer points lie on the black `sin²(tq)` curve; the peak sits at the
predicted compiled time. The 2-level quotient walk is realized **exactly** as
`Rx(2tq)` — no Trotter error — so this is a direct test of the Lean closed form.
The general N-vertex Trotter path converges to the exact CTQW as steps grow
(`max|sim−exact|`: 0.11 @ 1 step → 0.002 @ 40 steps), and the host-JSON template
walks (C5, hypercube Q3) match the matrix-exponential ground truth to shot noise.

## (b) Noise → deficit ✅ (validated, qualitative)

A depolarizing noise model on the quotient qubit mixes the data↔flag cells —
i.e. it plays the role of **positive-`BreakingScore`** noise — and the measured
deficit grows monotonically with the noise rate:

```
 p = 0.000   deficit = 0.00000
 p = 0.010   deficit = 0.00380
 p = 0.020   deficit = 0.01095
 p = 0.050   deficit = 0.02505
 p = 0.100   deficit = 0.05010
 p = 0.200   deficit = 0.10300
```

This is the qualitative "deficit ∝ BreakingScore" behaviour: a clean partition
gives ideal recall, residual cell-mixing noise eats into it. (The Lean theorem
is the *structural* governance statement — zero breaking score ⇒ no deficit; the
exact quantitative open-system bound is the one `sorry` flagged upstream. We
reproduce the qualitative trend, not a calibrated constant.)

## (c) One-line swap to a REAL IBM backend ✅ (ready, not executed — no creds)

Every run routes through `get_backend(...)` in `host_to_circuit.py`. To execute
on real IBM hardware, replace its body / pass in a real `backend`:

```python
from qiskit_ibm_runtime import QiskitRuntimeService
service = QiskitRuntimeService()                         # uses your saved creds
backend = service.least_busy(operational=True, simulator=False)
```

then in `run_experiment.py` use that `backend` instead of `get_backend()`.
Everything downstream is identical:

```python
from qiskit import transpile
tqc = transpile(qc, backend, optimization_level=3)       # maps onto heavy-hex coupling map
job = backend.run(tqc, shots=20000)
counts = job.result().get_counts()
```

**What ember would run on real IBM hardware**

1. Pick a heavy-hex device (`ibm_*`, e.g. a Heron `r2`); `QiskitRuntimeService`
   reads saved credentials (`QiskitRuntimeService.save_account(...)` once).
2. Build the recall circuit (`quotient_circuit(q, t*)` for the 2-cell signal,
   or `host_to_circuit(..., exact=False)` for the full template walk).
3. `transpile(qc, backend, optimization_level=3)` — the circuits are built from
   2-level (nearest-neighbour) couplings, so they map onto the device's native
   heavy-hex coupling map directly.
4. **Qubit count / shots:** the 2-cell quotient recall needs **1 logical qubit**
   (plus routing), `~20k shots` for ≲1% population error. The full N-vertex
   template walk needs `⌈log₂N⌉` qubits in the basis-state encoding (a cell-
   uniform *physical* heavy-hex realization across all 133 Heron qubits is the
   `CompileML` schedule proper; the 1-qubit quotient is its symmetric-sector
   reduction).
5. Read `P_key = P(|1⟩)`; compare to `sin²(t·q)`. A deviation beyond the
   breaking-score-predicted deficit **falsifies** the chip's data/flag partition
   symmetry or its noise symmetry (exactly the `compiled_experiment_prediction`
   falsifier).

`host_to_circuit.real_backend_stub()` documents this in-code (it intentionally
raises — there are no IBM credentials in this environment).

## Honest scope: validated vs not

- ✅ **Validated (sim):** Aer reproduces the Lean `sin²(tq)` PST signal with peak
  `≈1` at `t* = π/(2q)`; noise produces a monotone deficit; Trotter→exact
  convergence; host-JSON template walks match the matrix exponential.
- ▶ **Ready, not run:** real IBM execution — gated on credentials only; the code
  path is a one-line backend swap and standard `transpile`.
- ⚠️ **Not claimed:** a calibrated quantitative `deficit = c · BreakingScore`
  constant (the Lean quantitative open-system bound is an upstream `sorry`); and
  a full 133-qubit *physical* heavy-hex CTQW (we run the proven 2-cell symmetric
  quotient, which is what the Lean prediction is literally about, plus small
  template walks). The 1-qubit reduction is faithful to the quotient theorem,
  not a substitute for the full-chip schedule.
```
