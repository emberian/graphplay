# Graphplay ⇄ catgrad: a categorical DL frontend for the quantum-walk backend

*Design note. Status: scoping + runnable-demo plan. Author: Graphplay crew.*

## 0. One-sentence thesis

`catgrad` and Graphplay are the same idea pointed at two ends of one pipe:
**a model is a morphism in a (symmetric-monoidal / hypergraph) category, and
compilation is a functor out of it.** `catgrad` already does the hard frontend
work — parse a model, typecheck it, and (functorially, source-to-source)
produce its forward *and* backward passes as open hypergraphs. Graphplay
supplies a *backend*: a structure-preserving map from that categorical IR into
weighted-graph / CTQW **host Hamiltonians**, which then run on our simulator
and compile onto real chips via `CompileML`. The verified shadow of that
backend functor is already in the repo as
`Graphplay/Integrations/TransformerDSL.lean` (`compile_denote_commutes`).

So: **catgrad is the frontend, Graphplay is the quantum-walk backend, and the
seam between them is small and well-typed.**

## 1. What catgrad gives us (the IR we consume)

- A model is an `OpenHypergraph<O, A>` (the `open-hypergraphs` crate): a typed
  string diagram. `O` = wire/object labels (tensor shape + dtype); `A` =
  operation labels (the hyperedges).
- catgrad lowers it to **SSA** (`catgrad/src/ssa/mod.rs`):

  ```rust
  pub struct SSA<O, A> {
      pub op: A,                          // the operation label
      pub sources: Vec<(NodeId, O)>,      // typed input wires
      pub targets: Vec<(NodeId, O)>,      // typed output wires
  }
  ```

  i.e. a layered (parallel, topologically-ordered) list of
  `targets = op(sources)` assignments over tensor-typed wires.
- Autodiff is **syntactic**: the backward pass is *another open hypergraph*,
  produced by a functor, with no runtime tape. "A backend is an NdArray
  implementation" — equivalently, *a fold over the SSA that interprets each op
  label `A`*. The candle interpreter (`catgrad/src/interpreter/`) is one such
  fold; **our backend is another.**
- `catgrad-llm` / `catgrad-llm-models` already define real transformer models
  as open hypergraphs (`catgrad-llm-models/src/models`, with a `dump_model.rs`
  example). These are our test inputs.

The key consequence of syntactic autodiff: **we get the backward pass for
free, in the same IR as the forward pass.** Our
`training_step_linear_under_equitable` (the O(n·r) training-step cost under an
equitable partition) is therefore a statement about *the exact same hypergraph*
catgrad already hands us — the two autodiff stories compose rather than collide.

## 2. What Graphplay consumes (our host-JSON)

Our toolkit executables (`graphplay-toolkit`, `graphplay-sim`; lake exes
`ToolkitMain`, `SimMain`) read a compact host description. From
`examples/c5_equal_fiber.json`:

```jsonc
{
  "name": "...",
  "problem": { "domain": "...", "task": "...", "encoding": "...",
               "compiler_goal": "...", "proof_route": "..." },
  "template":   { "kind": "cycle", "n": 5, "prefix": "" },   // the QUOTIENT graph
  "fiber_size": 20,                                          // equitable cell size
  "marked":     { "0": 1 },                                  // marked cell(s)
  "scan":       { "steps": 2400, "t_max_factor": 5.0 }       // CTQW time sweep
}
```

The semantics map *exactly* onto the spine: `template` is the **quotient graph**
`Q`, `fiber_size` is the per-cell vertex count of the **equitable partition**,
`marked` selects the target cell, and `scan` is the CTQW evolution
`exp(-iτ Q̃)` time grid. `graphplay-sim` evolves it; `graphplay-toolkit` emits a
search-compiler report; `Graphplay/Applications/CompileML.lean` turns the same
quotient into an IBM-Heron schedule + the falsifiable
`compiled_experiment_prediction`.

## 3. The seam: SSA attention-op → host-JSON

A **Graphplay backend for catgrad** is a fold over the SSA that recognizes the
attention/linear blocks and, for each, emits a host description:

| catgrad SSA op (label `A`)          | Graphplay reading                                   | host-JSON it emits |
|-------------------------------------|-----------------------------------------------------|--------------------|
| `matmul`/`linear` producing an `n×n` score wire | a Hermitian-symmetrized score graph `A_ij` | `template` = its symmetry quotient |
| `softmax`(row) over a score wire    | row-stochastic normalization (mixing readout)       | folds into `scan` readout |
| attention head (Q·Kᵀ → scores → ·V) | a weighted-graph CTQW Hamiltonian on the token set  | `template` + `fiber_size` from the orbit/cell structure |
| `add` (residual)                    | graph sum (`addGraph` in `TransformerDSL`)          | quotient-of-sum = sum-of-quotients |
| multi-head (parallel heads)         | `pooled` head sum (`MultiHeadAttention`)            | `multiHead_restrict_eq_symmQuotient` |

Concretely, for each attention op the backend: (1) extracts the score matrix
(symbolically or from dumped weights); (2) computes its equitable partition
(orbits of the automorphism, or the block-equitable cells if the model carries
structured/grouped attention); (3) writes `template` = the quotient `Q`,
`fiber_size` = the cell sizes, `marked` = a chosen query token; (4) hands it to
`graphplay-sim` / `CompileML`.

This is a **fold over catgrad's existing SSA**, the exact extension point the
candle interpreter already uses — no changes to catgrad's core, just a new
backend crate.

## 4. The runnable demo: model-into-hellas, graphplay-out

```
 catgrad-llm-models                  catgrad-backend-graphplay              Graphplay (this repo)
 ┌────────────────┐  open hypergraph ┌──────────────────────┐  host-JSON   ┌──────────────────────┐
 │  a real model  │ ───────────────▶ │ fold SSA → find attn  │ ───────────▶ │ graphplay-sim:        │
 │ (dump_model.rs)│   + backward     │ ops → emit quotient   │  per layer   │  evolve exp(-iτ Q̃),   │
 └────────────────┘   (syntactic AD) │ template + fibers     │              │  watch the CTQW       │
                                     └──────────────────────┘              ├──────────────────────┤
                                                                           │ CompileML → IBM-Heron │
                                                                           │ schedule + falsifiable │
                                                                           │ prediction (sin²·tq)   │
                                                                           └──────────────────────┘
```

Steps, all on existing artifacts:

1. `catgrad-llm-models` dumps a small transformer to an open hypergraph (its
   `dump_model.rs` path).
2. **New crate `catgrad-backend-graphplay`** (Rust, in the catgrad workspace):
   folds the SSA, finds attention ops, emits one `examples/*.json` host per
   attention layer (§3).
3. Pipe each host JSON → `graphplay-sim` → *watch the attention computation run
   as a continuous-time quantum walk* on the quotient.
4. `graphplay-toolkit` + `CompileML` → emit the IBM-Heron schedule and the
   `compiled_experiment_prediction` (predicted key-population `sin²(tq)`,
   deficit ∝ `BreakingScore`) for that layer.

Deliverable demo: *a real model file in, a quantum-walk animation + a chip
experiment proposal out.*

## 5. The verified bridge (Rust ⇄ Lean)

Two coupling strengths, pick per appetite:

- **Loose (ship first):** the seam is the host-JSON. catgrad's Rust backend
  writes JSON; Graphplay's Lean toolkit reads it. Zero FFI, immediately
  runnable. This is the demo above.
- **Tight (the certificate):** formalize catgrad's open-hypergraph category and
  the backend functor in Lean — `TransformerDSL.lean` is the seed (its
  `denote`/`compile`/`compile_denote_commutes` already model exactly
  "morphism → host, meaning-preserving"). Then a thin **Rust↔Lean FFI** (the
  Lean core exposes the lowering; catgrad calls it) makes the *running* backend
  and the *verified* backend the same artifact. Rust↔Lean FFI is cheap
  (Lean's C ABI + `@[export]`); the math content is the functoriality proof,
  not the plumbing.

The honest target: prove the backend functor preserves semantics *on the
block-equitable sublanguage* (where `compile_denote_commutes` already bites),
and treat general learned attention as the ε-equitable frontier (below).

## 6. Honest caveats

- **Exact vs. learned equitability.** A clean `template` (cycle / K₄ / hypercube
  quotient) exists only when the attention layer is *structured* (grouped
  heads, tied positions, symmetric masks). General *learned* attention has no
  exact automorphism, so its equitable partition is trivial and the O(n·r)
  collapse does not apply verbatim. This is the **ε-equitable frontier** we
  already flag as open.
- **catgrad makes the frontier measurable.** Precisely *because* it hands us
  real models, the backend can *measure the equitability defect* of each
  trained attention matrix (distance from its nearest equitable partition) —
  turning "how close is real attention to compressible?" into a concrete
  experiment on actual weights. That measurement is itself a paper-grade
  result, independent of the quantum claim.
- **We compile structure, not magic.** The win is on the layers that carry
  symmetry; the contribution is the *exact, verified* accounting of that win,
  plus the hardware target — not a blanket speedup of arbitrary attention.

## 7. Concrete next steps

1. **`catgrad-backend-graphplay`** (Rust crate, catgrad workspace): SSA fold →
   host-JSON emitter for attention/linear/residual ops (§3 table). Smallest
   useful unit: handle one attention op end-to-end into `graphplay-sim`.
2. **Equitability-defect probe**: for a dumped model, report per-layer distance
   to the nearest equitable partition (the ε-frontier measurement).
3. **Lean functor** (optional, the certificate): extend `TransformerDSL.lean`
   with an `OpenHypergraph → WGraphP` interpretation and prove
   `compile_denote_commutes` covers the lowering; expose via `@[export]` for
   the tight FFI coupling.
4. **Paper hook**: §3/§5 of the main paper reference this as the *practical
   frontend*; the demo (real model → CTQW + chip schedule) is the executable
   counterpart to the verified compiler.

---

*Why this is worth it:* it converts "the functor stack is a transformer
compiler" from a Lean theorem into a pipeline you can run on a real model, and
it gives the falsifiable on-Heron experiment a genuine front door — a model,
not a toy. catgrad does the parsing/typecheck/autodiff; Graphplay does the
quantum-walk lowering and the hardware target; the seam is one JSON schema (to
ship) or one functoriality proof (to certify).*
