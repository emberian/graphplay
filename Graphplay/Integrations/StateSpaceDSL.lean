/-
# Graphplay.Integrations.StateSpaceDSL

**A compositional combinator language for *sequence models* — transformers AND
state-space models — under one equitable-quotient reduction.**

`TransformerDSL` already compiles a transformer to a *static* token-graph
Hamiltonian and lowers it through the equitable quotient.  A state-space model
(S4 / Mamba / a linear RNN) is not static — it is a *temporal recurrence*
`hₜ = A hₜ₋₁ + B xₜ`, `yₜ = C hₜ + D xₜ`.  But the unifying observation is that
**both an attention graph and an SSM transition `A` are linear endomorphisms of a
state space**, and the *same* equitable partition reduces both:

* string-diagram **wiring** (the "open-hypergraph" view): a model is a morphism in
  a symmetric monoidal category, built from generators (`ssm`, `attn`) by the
  combinators `seqCompose` (∘, series) and `tensor` (⊗, parallel);
* differentiable **semantics** (the "catgrad" view): each generator denotes to a
  linear operator (its Markov parameters / impulse response), and composition is
  functorial;
* **equivariant embeddings** (the graphplay view): an embedding `B` is equivariant
  for the state-graph symmetry exactly when it factors through the *quotient* —
  `B` lands in the cell-uniform subspace — and then the whole `n`-dimensional
  model collapses onto its `r`-dimensional quotient.

The headline is `LinearSSM.freeEvolve_reduces`: the `n`-dimensional free state
trajectory of a *cell-uniform* (equitable) transition is the lift of the
`r`-dimensional **quotient** trajectory — the SSM analogue of the attention
`O(n²) → O(n·r)` collapse, in the *state* dimension.  It is proved by iterating
the spine identity `EquitablePartition.restrict_eq_symmQuotient`.
-/

import Graphplay.Equitable
import Graphplay.Integrations.TransformerDSL

open scoped BigOperators Matrix

namespace Graphplay

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-! ## 1. The cell-uniform lift of a quotient-side coefficient vector

`liftVec P w` is the state vector with cell-coordinate `w i` on cell `i`:
`liftVec P w = ∑ i, w i • (cellUniformVec i)`.  It is the canonical isometric
image of the `r`-dimensional coefficient vector `w : I → ℂ` inside the full
`n`-dimensional state space `V → ℂ`. -/
noncomputable def EquitablePartition.liftVec (P : EquitablePartition G I) (w : I → ℂ) :
    V → ℂ := fun v => ∑ i, w i * P.cellUniformVec i v

/-- One step of a cell-uniform transition **is** one step of the symmetric
quotient: `A · (lift w) = lift (Q̃ · w)`.  This is exactly the spine identity
`restrict_eq_symmQuotient`, packaged in the `liftVec` notation. -/
theorem EquitablePartition.adj_mulVec_liftVec (P : EquitablePartition G I) (w : I → ℂ) :
    G.adj.mulVec (P.liftVec w) = P.liftVec (P.symmQuotient.mulVec w) :=
  P.restrict_eq_symmQuotient w

/-- `Aᵏ` keeps the cell-uniform (symmetry-invariant) subspace invariant — the
iterate of `cellUniformSubspace_invariant`. -/
theorem EquitablePartition.adjPow_mem_cellUniformSubspace (P : EquitablePartition G I)
    (k : ℕ) {v : V → ℂ} (hv : v ∈ P.cellUniformSubspace) :
    (G.adj ^ k).mulVec v ∈ P.cellUniformSubspace := by
  induction k with
  | zero => simpa [pow_zero, Matrix.one_mulVec] using hv
  | succ k ih =>
    rw [pow_succ' G.adj k, ← Matrix.mulVec_mulVec]
    exact P.cellUniformSubspace_invariant _ ih

/-! ## 2. The state-space block (a generator of the DSL)

A `LinearSSM` carries its state-transition operator as a **weighted graph**
`trans` (so the entire equitable-partition machinery applies verbatim), together
with the input map `B = inMap`, output map `C = outMap`, and feedthrough
`D = feed`.  The one-step recurrence is `hₜ = trans.adj · hₜ₋₁ + B · xₜ`,
`yₜ = C · hₜ + D · xₜ`. -/
structure LinearSSM (S : Type u) [Fintype S] [DecidableEq S]
    (In Out : Type v) [Fintype In] [Fintype Out] where
  /-- State-transition operator `A`, carried as a weighted graph on the state space. -/
  trans : WeightedGraph S
  /-- Input map `B : ℂ^In → ℂ^S`. -/
  inMap : Matrix S In ℂ
  /-- Output map `C : ℂ^S → ℂ^Out`. -/
  outMap : Matrix Out S ℂ
  /-- Feedthrough `D : ℂ^In → ℂ^Out`. -/
  feed : Matrix Out In ℂ

namespace LinearSSM

variable {S : Type u} [Fintype S] [DecidableEq S] {In Out : Type v} [Fintype In] [Fintype Out]

/-- The **Markov parameters** (impulse response) of the block: `g₀ = D` and
`g_{k+1} = C · Aᵏ · B`, so that `yₜ = ∑_{k≥0} g_k · x_{t-k}`. -/
noncomputable def markovParam (M : LinearSSM S In Out) : ℕ → Matrix Out In ℂ
  | 0 => M.feed
  | (k + 1) => M.outMap * (M.trans.adj ^ k) * M.inMap

/-! ## 3. The headline: free-state reduction onto the quotient

For an equitable partition `P` of the state-transition graph, the `k`-step free
evolution `Aᵏ` of a **cell-uniform** initial state `lift w` is the lift of the
`r`-dimensional quotient evolution `Q̃ᵏ w`.  The full `n`-dimensional trajectory
is carried by the `r × r` symmetric quotient — the state-dimension analogue of the
attention `O(n²) → O(n·r)` collapse. -/
theorem freeEvolve_reduces (M : LinearSSM S In Out)
    (P : EquitablePartition M.trans I) (w : I → ℂ) (k : ℕ) :
    (M.trans.adj ^ k).mulVec (P.liftVec w)
      = P.liftVec ((P.symmQuotient ^ k).mulVec w) := by
  induction k with
  | zero => simp [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ' M.trans.adj k, ← Matrix.mulVec_mulVec, ih,
        P.adj_mulVec_liftVec, pow_succ' P.symmQuotient k, ← Matrix.mulVec_mulVec]

/-! ## 4. Equivariant embeddings — the model is secretly `r`-dimensional

An **equivariant embedding** is an input map `B` whose every column lands in the
cell-uniform (symmetry-invariant) subspace — i.e. the embedding respects the
state-graph symmetry, factoring through the `r`-cell quotient.  The payoff: under
an equivariant embedding *every reachable state* of the `n`-dimensional model
stays in the `r`-dimensional cell-uniform subspace and evolves by the quotient
(`freeEvolve_reduces`).  The model has `r` effective degrees of freedom, not `n`. -/
def IsEquivariantEmbedding (M : LinearSSM S In Out)
    (P : EquitablePartition M.trans I) : Prop :=
  ∀ x : In, (fun s => M.inMap s x) ∈ P.cellUniformSubspace

/-- **Equivariant embedding ⟹ the reachable state space collapses to the
quotient.**  Every state reachable in `k` steps from an equivariant embedding lies
in the `r`-dimensional cell-uniform subspace (and there evolves by the quotient,
`freeEvolve_reduces`). -/
theorem equivariant_reachable_cellUniform (M : LinearSSM S In Out)
    (P : EquitablePartition M.trans I) (hB : M.IsEquivariantEmbedding P)
    (x : In) (k : ℕ) :
    (M.trans.adj ^ k).mulVec (fun s => M.inMap s x) ∈ P.cellUniformSubspace :=
  P.adjPow_mem_cellUniformSubspace k (hB x)

/-! ## 5. Generators & the transformer bridge

`ofGraph` packages any Hermitian state-coupling graph (a transformer's
symmetrized attention graph, or an S4/Mamba transition) as a `LinearSSM`
generator.  A `TransformerProgram` therefore embeds into the SSM DSL by denoting
to its token graph and reading it as a transition operator — transformers and
state-space models share one transition semantics and one equitable reduction.
(Series `∘` and feedback composition produce *non-Hermitian* couplings, so they
live one level up, at the impulse-response/`markovParam` semantics where
composition is convolution; that monoidal layer is the next increment.) -/
def ofGraph (W : WeightedGraph S) (B : Matrix S In ℂ) (C : Matrix Out S ℂ)
    (D : Matrix Out In ℂ) : LinearSSM S In Out :=
  ⟨W, B, C, D⟩

@[simp] theorem ofGraph_trans (W : WeightedGraph S) (B : Matrix S In ℂ)
    (C : Matrix Out S ℂ) (D : Matrix Out In ℂ) :
    (ofGraph W B C D : LinearSSM S In Out).trans = W := rfl

/-- **A transformer program *is* an SSM transition.**  Reading a
`TransformerProgram`'s token-graph denotation as a `LinearSSM` transition exhibits
transformers as a sub-language of the state-space DSL — one transition semantics,
one equitable reduction.  In particular, a transformer with block-equitable
attention has an equivariant token embedding and reduces by `freeEvolve_reduces`
exactly as an S4/Mamba block with cell-uniform `A` does. -/
noncomputable def transformerAsSSM {W : Type u} [Fintype W] [DecidableEq W]
    (p : TransformerDSL.TransformerProgram W) (B : Matrix W In ℂ)
    (C : Matrix Out W ℂ) (D : Matrix Out In ℂ) : LinearSSM W In Out :=
  ofGraph p.denote B C D

@[simp] theorem transformerAsSSM_trans {W : Type u} [Fintype W] [DecidableEq W]
    (p : TransformerDSL.TransformerProgram W) (B : Matrix W In ℂ)
    (C : Matrix Out W ℂ) (D : Matrix Out In ℂ) :
    (transformerAsSSM p B C D).trans = p.denote := rfl

end LinearSSM

end Graphplay
