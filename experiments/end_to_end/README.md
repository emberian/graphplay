# end_to_end — the ML-to-quantum-hardware compiler, in one command

Chains the three existing pieces into ONE runnable pipeline: a **real catgrad-llm
Llama model** → **Graphplay host description** → **Qiskit circuit** → **validated
PST signal** (measured-vs-Lean-predicted). This is the tangible
"ML-to-quantum-hardware compiler" demo — the seam works end to end on real
artifacts.

```
 real catgrad-llm Llama model  (LlamaForCausalLM, 8 query heads / 2 KV groups)
        │
        │  catgrad-backend-graphplay  (Rust):  build model graph → fold SSA →
        │  recognize attention layers (q/k/v/o + matmul→softmax→matmul) →
        │  GQA head grouping = equitable partition
        ▼
 Graphplay host-JSON  per attention layer        ── ./hosts/attn_layer_*.json
   { template: path n=2 (K₂),  fiber_size: 4,  marked: {0:1} }
        │
        │  qiskit_compile.host_to_circuit  (Python):  host → CTQW circuit.
        │  bridge: K₂-with-equal-fibers equitable partition ⇒ symmetric quotient
        │  Q̃ = f·X,  so the CompileML coupling  q = fiber_size = 4.
        ▼
 Qiskit circuit   exp(-i t* q X) = Rx(2 t* q)   (1 qubit, depth 2)
        │
        │  Aer simulator  (get_backend — the single sim↔hardware seam)
        ▼
 measured PST signal   P_key(t*) = 1.000   at   t* = π/(2q) = 0.3927
        │
        └──  validated against  Graphplay/Applications/CompileML.lean :
             predictedKeyPopulation = sin²(t·q),  = 1 at t* = π/(2q).
```

## Run it

```bash
source ../.venv/bin/activate        # qiskit, qiskit-aer, scipy, matplotlib, numpy
python run_pipeline.py              # full pipeline on ./hosts/*.json (+ figure)
# or
./run.sh                           # thin wrapper that sources the venv for you
```

Output (this is what genuinely ran):

```
small-llama (LlamaForCausalLM, 8 heads / 2 KV groups)
  → 4 attention layers
  → host-JSON {template: path n=2, fiber_size: 4}
  → Qiskit circuit (1 qubit, depth 2)
  → measured PST peak P_key = 1.0000 at t* = 0.3927
    (Lean predicted sin²(t*·q) = 1.0000)
RESULT: 4/4 layers' measured PST match the Lean prediction within shot noise.
PST scan: measured peak t≈0.399, P_key≈0.999; RMS(sim vs sin²) = 0.0045
figure → figures/end_to_end_pst.png
```

## Step 1: regenerate the host-JSONs from the real model (the catgrad step)

The host-JSONs in `./hosts/` were emitted by the catgrad backend from a *real*
`catgrad-llm-models` Llama graph (8 query heads, 2 KV groups → GQA → equitable
quotient `K₂` with equal fibers of 4 heads). To regenerate them:

```bash
(cd ~/hellas/catgrad/catgrad-backend-graphplay && cargo run --example emit_hosts)
cp ~/hellas/catgrad/catgrad-backend-graphplay/hosts/attn_layer_*.json hosts/
```

The example's own trace (no network — config in, hypergraph out):

```
built model graph: llama
  config: 4 layers, 8 query heads, 2 KV groups, head_dim 32
  SSA fold saw: 37 matmuls, 8 softmax-exp, 13 softmax-sum, 33 adds;
                4 attention layer(s) with full q/k/v/o projections
  emitted hosts/attn_layer_{0,1,2,3}.json  (template=path n=2, fiber_size=4)
```

`python run_pipeline.py --regen-hosts` prints this exact command.
We copy the JSONs into `./hosts/` and the pipeline depends only on those
artifacts (swarm-safe: nothing in `~/hellas` is committed or mutated by the run).

## The bridge: host-JSON → Lean coupling `q`

`CompileML`/`IBMHeavyHex` prove the Heron-specific coupling `q = 2√(N−1)`, the
off-diagonal of the **symmetric quotient** of the data/flag equitable partition.
For a *generic* equitable partition whose quotient is the `K₂` (a `path n=2`
template) with **equal fibers of size `f`**, the identical construction
(`EquitablePartition.symmQuotient`, the geometric-mean symmetrization) gives

    Q̃ = [[0, f], [f, 0]] = f · X        ⇒   q = fiber_size.

A catgrad GQA layer emits exactly `{template: path n=2, fiber_size: f}`, so we
read `q = f` straight off the JSON and run the CompileML recall protocol:

* prepare the data/query-uniform cell `|0⟩`,
* evolve `U(t) = exp(-i t q X) = Rx(2 t q)` (exact, no Trotter error),
* measure `P_key = P(|1⟩)` = the flag/key-uniform population.

The Lean prediction `predictedKeyPopulation = sin²(t·q)` then says: peak `= 1` at
`t* = π/(2q)` (ideal associative recall). For `f = 4`: `t* = π/8 ≈ 0.3927`,
`P_key(t*) = 1`. The Aer simulator reproduces it to shot noise.

## What runs vs what's stubbed (honest scope)

| stage | status |
|---|---|
| **catgrad model → SSA → host-JSON** (Rust `emit_hosts`) | ✅ **runs** — real `catgrad-llm-models` Llama graph, SSA fold recognizes 4 complete attention layers, emits 4 valid host-JSONs |
| **host-JSON → Qiskit circuit** (`host_to_circuit`) | ✅ **runs** — both the exact 2-cell recall circuit `Rx(2t*q)` and the host's template-graph CTQW |
| **circuit → Aer sim → measured P_key** | ✅ **runs** — 20 000 shots, `P_key(t*) = 1.000` for all 4 layers |
| **measured vs Lean `sin²(t·q)`** | ✅ **validated** — 4/4 match within shot noise; PST scan RMS 0.0045; peak at t* |
| **real IBM hardware execution** | ▶ **ready, not run** — gated on credentials only; one-line backend swap (below) |

What is *honestly* small / not claimed:

* The demonstrated model is a small structurally-real Llama (8/2 GQA). The point
  is the **seam**, not scale — and GQA's equitable `K₂` quotient is the exact
  domain of the theorem.
* All 4 layers have the same head structure, so they emit the same host and the
  same `q = 4`; the per-layer PASS lines are 4 genuine independent Aer runs, not
  4 copies of one number.
* We run the proven **2-cell symmetric-quotient** recall (1 logical qubit) — the
  object the Lean `sin²(t·q)` prediction is literally about — plus the host's
  template-graph CTQW as a seam sanity check. A full physical multi-qubit
  heavy-hex CTQW is the `CompileML` schedule proper, not run here.
* The Lean quantitative noisy-deficit bound is an upstream `sorry`; we don't
  fabricate a calibrated `deficit = c·BreakingScore` constant. (The qualitative
  noise→deficit trend lives in the sibling `../qiskit_compile/run_experiment.py`.)

## One-line swap to a real IBM backend

Everything routes through `host_to_circuit.get_backend(...)` (the single seam).
To execute on real heavy-hex hardware, replace it with:

```python
from qiskit_ibm_runtime import QiskitRuntimeService
service = QiskitRuntimeService()                          # saved creds
backend = service.least_busy(operational=True, simulator=False)
# then in run_pipeline.py pass this `backend` instead of get_backend()
tqc = transpile(qc, backend, optimization_level=3)        # maps onto heavy-hex
```

The recall circuit is a single `Rx` on 1 logical qubit (+ routing), so it
transpiles onto any heavy-hex device directly; read `P_key = P(|1⟩)` and compare
to `sin²(t·q)`. A deviation beyond the breaking-score-predicted deficit
**falsifies** the chip's data/flag partition symmetry — the
`compiled_experiment_prediction` falsifier.

## Files

| file | what it is |
|---|---|
| `run_pipeline.py` | the end-to-end chain: host-JSON → Qiskit → Aer → measured-vs-`sin²(t·q)`; imports `qiskit_compile.host_to_circuit`; writes the figure |
| `run.sh` | thin wrapper (sources `../.venv`, runs `run_pipeline.py`) |
| `hosts/attn_layer_{0..3}.json` | the catgrad-emitted host-JSONs (copied from `~/hellas/catgrad/catgrad-backend-graphplay/hosts/`) |
| `figures/end_to_end_pst.png` | the PST recall curve: Aer sim vs Lean `sin²(t·q)`, peak marked at `t* = π/(2q)` |

## Provenance / related

* upstream Rust backend: `~/hellas/catgrad/catgrad-backend-graphplay`
  (`examples/emit_hosts.rs`, `src/lower.rs`, `src/host.rs`)
* qiskit compile pieces: `../qiskit_compile/` (`host_to_circuit.py`,
  `run_experiment.py`)
* the theorem: `Graphplay/Applications/CompileML.lean`,
  `Graphplay/Applications/IBMHeavyHex.lean`
* host-JSON schema: `examples/c5_equal_fiber.json`,
  `paper/catgrad_integration.md`
```
