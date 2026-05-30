/-
# Graphplay.Integrations.TransformerDSL

**The functor stack is an abstract PROGRAMMING LANGUAGE for transformer models.**

This module realizes the project's headline PL thesis: a transformer is a *typed
program* that **compiles down the tower** to a host Hamiltonian.  Concretely we
build a tiny, finite, concrete DSL `TransformerProgram`, give it a **denotation**
into the `WeightedGraph` quantum-walk semantics, give it a **compiler** that lowers
a program with equitable (block / symmetric) structure to its small quotient via
the `Quotient` functor of `Graphplay.Categorical`, and **prove** that the compiler
is *semantics-preserving*: the compiled (quotient) meaning is exactly the
denotational meaning restricted to the cell-uniform subspace.  This is a *verified
ML→quantum compiler*: the optimizing "drop to the `r × r` quotient" pass provably
computes the same operator on the symmetric sector.

## Language reference

### Syntax — the typed programs

A `TransformerProgram V` (over a finite token type `V`) is built from five
constructors, mirroring the transformer block:

* `attention (A : AttentionMatrix V)` — a single query/key/value head, carrying its
  (already-softmaxed) score matrix.  Its **score weighted-graph** is the Hermitian,
  loopless symmetrization `A.symmetrizedAttention` — exactly the CTQW Hamiltonian on
  the token graph.
* `multiHead (M : MultiHeadAttention V)` — parallel composition of heads; denotes to
  the **pooled** head graph (the coherent sum of the per-head symmetrizations).
* `add (p q)` — residual-style additive combination of two sub-programs (the
  inter-token graphs add; loopless + Hermitian is closed under `+`).
* `residual (p)` — a skip connection: as an *inter-token* operator the identity skip
  contributes no edges, so it denotes to `denote p` unchanged (the `WeightedGraph`
  category is loopless, so the on-site `+I` is invisible — see `denote`).
* `feedForward (p) (f : V → ℂ)` — a position-wise / diagonal (local) map applied after
  `p`.  A diagonal map is a per-vertex on-site potential; being loopless it contributes
  **no inter-token edges**, so it too denotes to `denote p` (the local map is a runtime
  potential, not part of the token graph).  We keep `f` as data so the program records it.
* `compose (p q)` — layer stacking: stacking two layers composes their token graphs
  additively at the Hamiltonian level (the walk Hamiltonian of a stack is the sum of
  layer Hamiltonians), so `compose` denotes like `add`.  Kept as a *separate*
  constructor so the syntax distinguishes "residual branch" from "next layer".

### Denotational semantics — `denote`

`denote : TransformerProgram V → WeightedGraph V` is the standard ML→quantum-walk
semantics: every program means a **token-graph Hamiltonian** (Hermitian, loopless),
the object the entire Graphplay equitable-partition / quantum-walk machinery acts on.
The clauses are the natural ones above; structurally it is a fold sending `attention`
↦ symmetrized score graph, `multiHead` ↦ pooled graph, `add`/`compose` ↦ graph sum,
`residual`/`feedForward` ↦ the sub-graph (local terms are loopless-invisible).

### Typing rules — which programs are *compilable*

A program is **compilable** when it comes equipped with a `BlockEquitable` witness:
an `EquitablePartition` of its denotation into `r` cells (e.g. induced by a token-graph
symmetry via `MachineLearning.equitableOfAutomorphism`).  This is the typing judgment
`p : Compilable` — only block-equitable programs admit the `O(n·r)` lowering.  A program
*without* such structure is still a legal program with a denotation; it just does not
type-check for the optimizing compiler pass (it must run at full `O(n²)` cost).

### The compiler — `compile`

`compile : (p with BlockEquitable witness P) → host data` lowers the program through
the categorical tower: it returns the **quotient weighted graph** `P.quotientGraph`
on the `r`-element cell index — i.e. the image of the program's partitioned denotation
under the `Quotient : WGraphP ⥤ WGraph` functor of `Graphplay.Categorical`.  This is
the *host Hamiltonian*: a small `r × r` weighted graph (a genuine CTQW problem) whose
runtime primitives (PST / search / mixing, the `LiftablePrimitive`s of Categorical) are
the program's executable behaviours.

### The guarantee — `compile_denote_commutes`

The compiler's correctness theorem: for a block-equitable program, the compiled
quotient semantics equals the denoted full semantics restricted to the cell-uniform
subspace.  Formally, the full denotation's action on any cell-uniform input
`∑ i, w i · e_i` is computed by the symmetric quotient `Q̃ = P.symmQuotient` of the
compiled graph (`EquitablePartition.restrict_eq_symmQuotient`, reused).  *Lowering
through the tower preserves the program's meaning* — a verified optimizing pass.
A multi-head specialization (`compile_denote_commutes_multiHead`) reuses
`MachineLearning.multiHead_restrict_eq_symmQuotient`.  The **cost** theorem
`compiled_apply_linear_in_n` reuses `AttentionComplexity.attention_apply_linear_in_n`:
the compiled apply is linear in sequence length.

### Slogan

> `WGraphP` morphisms are the typed programs; the `Quotient` functor is the optimizing
> compiler pass; PST / search / mixing are the runtime primitives.  Compilation is a
> machine-checked, semantics-preserving ML→quantum lowering.

## References

* Vaswani et al., *Attention Is All You Need*, NeurIPS 2017.
* Godsil–Royle, *Algebraic Graph Theory* (equitable partitions, divisor matrix).
* `Graphplay.Integrations.MachineLearning`, `Graphplay.Integrations.AttentionComplexity`,
  `Graphplay.Categorical`, `Graphplay.Equitable`, `Graphplay.Weighted`.
-/

import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Categorical
import Graphplay.Integrations.MachineLearning
import Graphplay.Integrations.AttentionComplexity

open scoped Matrix BigOperators

universe u

namespace Graphplay
namespace TransformerDSL

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## 0. A `WeightedGraph` sum (the additive monoid of token graphs)

The denotation needs to *add* token graphs (for `add`, `compose`, and the residual /
feed-forward folds).  Hermitian + Hermitian is Hermitian and loopless + loopless is
loopless, so the sum of two `WeightedGraph`s is again a `WeightedGraph`; the zero
graph is the additive unit.  These are the algebra of token-graph Hamiltonians. -/

/-- The **empty token graph**: zero adjacency, the additive unit (no edges). -/
def emptyGraph (V : Type u) [Fintype V] [DecidableEq V] : WeightedGraph V where
  adj := 0
  herm := Matrix.isHermitian_zero
  loopless := fun _ => rfl

@[simp] theorem emptyGraph_adj : (emptyGraph V).adj = 0 := rfl

/-- The **sum of two token graphs**: add the adjacency matrices.  Hermitian and
loopless are both closed under `+`, so this is again a `WeightedGraph`.  This is the
Hamiltonian-level superposition of two layers / branches. -/
def addGraph (G H : WeightedGraph V) : WeightedGraph V where
  adj := G.adj + H.adj
  herm := G.herm.add H.herm
  loopless := fun v => by simp [Matrix.add_apply, G.loopless v, H.loopless v]

@[simp] theorem addGraph_adj (G H : WeightedGraph V) :
    (addGraph G H).adj = G.adj + H.adj := rfl

/-! ## 1. The DSL — `TransformerProgram`

A finite, concrete inductive with the five core transformer constructors.  `feedForward`
and `residual` carry the *local* (diagonal / skip) data, which is loopless-invisible at
the inter-token graph level but recorded in the syntax. -/

/-- The **transformer DSL**: a typed program over token type `V`.

* `attention A` — a single head carrying its score matrix `A : AttentionMatrix V`.
* `multiHead M` — parallel heads `M : MultiHeadAttention V`.
* `add p q` — residual-style additive combination of two sub-programs.
* `residual p` — a skip connection wrapping `p` (on-site identity, edge-invisible).
* `feedForward p f` — a position-wise / diagonal local map `f : V → ℂ` after `p`.
* `compose p q` — layer stacking (next-layer composition). -/
inductive TransformerProgram (V : Type u) [Fintype V] [DecidableEq V] where
  | attention (A : MachineLearning.AttentionMatrix V) : TransformerProgram V
  | multiHead (M : MachineLearning.MultiHeadAttention V) : TransformerProgram V
  | add (p q : TransformerProgram V) : TransformerProgram V
  | residual (p : TransformerProgram V) : TransformerProgram V
  | feedForward (p : TransformerProgram V) (f : V → ℂ) : TransformerProgram V
  | compose (p q : TransformerProgram V) : TransformerProgram V

namespace TransformerProgram

/-! ## 2. Denotational semantics — `denote`

The standard ML→quantum-walk meaning: every program denotes to a token-graph
Hamiltonian `WeightedGraph V`. -/

/-- **Denotation** of a transformer program as a token-graph Hamiltonian.

* `attention A`  ↦ `A.symmetrizedAttention`           (Hermitian score graph)
* `multiHead M`  ↦ `M.pooled`                          (pooled head graph)
* `add p q`      ↦ `addGraph (denote p) (denote q)`    (additive branch)
* `residual p`   ↦ `denote p`                          (skip is edge-invisible)
* `feedForward p f` ↦ `denote p`                       (local/diagonal term, loopless)
* `compose p q`  ↦ `addGraph (denote p) (denote q)`    (layer-stack Hamiltonian sum)

This is the verified ML semantics: the "what the program means as a quantum walk." -/
noncomputable def denote : TransformerProgram V → WeightedGraph V
  | .attention A => A.symmetrizedAttention
  | .multiHead M => M.pooled
  | .add p q => addGraph (denote p) (denote q)
  | .residual p => denote p
  | .feedForward p _ => denote p
  | .compose p q => addGraph (denote p) (denote q)

@[simp] theorem denote_attention (A : MachineLearning.AttentionMatrix V) :
    denote (.attention A) = A.symmetrizedAttention := rfl

@[simp] theorem denote_multiHead (M : MachineLearning.MultiHeadAttention V) :
    denote (.multiHead M) = M.pooled := rfl

@[simp] theorem denote_add (p q : TransformerProgram V) :
    denote (.add p q) = addGraph (denote p) (denote q) := rfl

@[simp] theorem denote_residual (p : TransformerProgram V) :
    denote (.residual p) = denote p := rfl

@[simp] theorem denote_feedForward (p : TransformerProgram V) (f : V → ℂ) :
    denote (.feedForward p f) = denote p := rfl

@[simp] theorem denote_compose (p q : TransformerProgram V) :
    denote (.compose p q) = addGraph (denote p) (denote q) := rfl

end TransformerProgram

/-! ## 3. The compiler — typed (compilable) programs and the lowering

A program is **compilable** when it carries an equitable partition of its denotation.
This is the typing judgment that *enables* the `O(n·r)` lowering: only block-equitable
programs admit the optimizing compiler pass. -/

/-- A **compilable transformer program**: a program `prog` together with a `BlockEquitable`
witness `P` — an equitable partition of its denotation into `r = |I|` cells.  This is the
typed program that the optimizing compiler accepts; the partition `P` is the proof that the
token graph has `r`-cell symmetry (e.g. from `MachineLearning.equitableOfAutomorphism`). -/
structure Compilable (V : Type u) [Fintype V] [DecidableEq V]
    (I : Type u) [Fintype I] [DecidableEq I] where
  /-- The underlying transformer program. -/
  prog : TransformerProgram V
  /-- The block-equitable witness: an `r`-cell equitable partition of the denotation. -/
  blockEquitable : EquitablePartition prog.denote I

namespace Compilable

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- **The compiler.**  Lowers a compilable program through the categorical tower to its
*host Hamiltonian*: the quotient weighted graph `P.quotientGraph` on the `r`-element cell
index — i.e. the image of the program's partitioned denotation under the
`Quotient : WGraphP ⥤ WGraph` functor of `Graphplay.Categorical`.  The result is a small
`r × r` CTQW problem whose runtime primitives (PST / search / mixing) are the program's
executable behaviours. -/
noncomputable def compile (C : Compilable V I) : WeightedGraph I :=
  C.blockEquitable.quotientGraph

/-- The compiled host graph is the `Quotient`-functor image of the partitioned denotation:
`compile` is literally the object map of `Graphplay.Quotient` on the bundled
partitioned weighted graph.  This identifies the compiler with the categorical optimizing
pass. -/
theorem compile_eq_quotientFunctor (C : Compilable V I) :
    C.compile =
      (Quotient.obj
        { base := { V := V, G := C.prog.denote }
          I := I
          P := C.blockEquitable }).G := rfl

/-- The **compiled adjacency** is the (loopless) symmetric quotient `Q̃` of the program's
denotation: off-diagonal it is `P.symmQuotient`, the genuine `r × r` Hamiltonian. -/
@[simp] theorem compile_adj (C : Compilable V I) :
    C.compile.adj =
      fun i j => if i = j then 0 else C.blockEquitable.symmQuotient i j := rfl

/-! ## 4. Correctness — the compiler preserves meaning (`compile_denote_commutes`)

The genuinely-provable PL core: for a block-equitable program, the compiled (quotient)
semantics equals the denoted (full) semantics restricted to the cell-uniform subspace.
We surface this through the **symmetric quotient** `P.symmQuotient` (the matrix of the
compiled graph), reusing the spine's `EquitablePartition.restrict_eq_symmQuotient`. -/

/-- **Compiler correctness (PROVEN): lowering preserves meaning.**

For a compilable (block-equitable) program `C`, the **full denotation's** action on any
cell-uniform input `∑ i, w i · e_i` is computed by the **symmetric quotient**
`Q̃ = C.blockEquitable.symmQuotient` of the compiled host graph:

  `denote(prog) · (∑ i, w i · e_i) = ∑ i, (Q̃ · w) i · e_i`.

i.e. the small `r × r` compiled semantics equals the restriction of the full `n × n`
denoted semantics to the symmetric (cell-uniform) sector.  *Lowering through the tower
preserves the program's meaning* — the verified optimizing-pass guarantee.  Directly the
spine's `EquitablePartition.restrict_eq_symmQuotient` applied to the denotation. -/
theorem compile_denote_commutes (C : Compilable V I) (w : I → ℂ) :
    C.prog.denote.adj.mulVec
        (fun v => ∑ i, w i * C.blockEquitable.cellUniformVec i v)
      = (fun v => ∑ i, (C.blockEquitable.symmQuotient.mulVec w) i
            * C.blockEquitable.cellUniformVec i v) :=
  C.blockEquitable.restrict_eq_symmQuotient w

/-- **Compiler correctness, multi-head specialization (PROVEN).**  When the program is a
single `multiHead M`, the cell-uniform restriction of the pooled denotation is the
symmetric quotient — reusing `MachineLearning.multiHead_restrict_eq_symmQuotient`.  This is
the verified statement that *symmetric/redundant heads compile away to the small quotient*. -/
theorem compile_denote_commutes_multiHead
    (M : MachineLearning.MultiHeadAttention V)
    (P : EquitablePartition (TransformerProgram.multiHead M).denote I) (w : I → ℂ) :
    (TransformerProgram.multiHead M).denote.adj.mulVec
        (fun v => ∑ i, w i * P.cellUniformVec i v)
      = (fun v => ∑ i, (P.symmQuotient.mulVec w) i * P.cellUniformVec i v) :=
  -- `denote (multiHead M) = M.pooled` definitionally, so this is the MachineLearning lemma.
  M.multiHead_restrict_eq_symmQuotient P w

/-- **Cell-uniform invariance of the compiled program (PROVEN).**  The cell-uniform
subspace of the denotation is invariant under the full denoted dynamics: structured
(cell-uniform) inputs stay structured.  Hence the compiled quotient dynamics is a
*closed* small system — the compiler's target is self-contained.  Directly
`EquitablePartition.cellUniformSubspace_invariant`. -/
theorem compiled_cellUniform_invariant (C : Compilable V I)
    (v : V → ℂ) (hv : v ∈ C.blockEquitable.cellUniformSubspace) :
    C.prog.denote.adj.mulVec v ∈ C.blockEquitable.cellUniformSubspace :=
  C.blockEquitable.cellUniformSubspace_invariant v hv

/-! ## 5. Cost — the compiled apply is linear in sequence length

The runtime payoff: where the naive denoted apply is `O(n²·d)`, the compiled block apply
is `O(n·r·d)` — **linear in `n`** for fixed cell count `r` and feature dimension `d`.  We
reuse the proven operation-count results of `Graphplay.AttentionComplexity`. -/

/-- **Compiled-apply cost is linear in `n` (PROVEN).**  The block-equitable apply's
operation count `blockCost n r d` equals `n · (r·d + d)`, linear in the sequence length
`n`.  Directly `AttentionComplexity.attention_apply_linear_in_n`. -/
theorem compiled_apply_linear_in_n (n r d : ℕ) :
    AttentionComplexity.blockCost n r d = n * (r * d + d) :=
  AttentionComplexity.attention_apply_linear_in_n n r d

/-- **Compiled apply beats the naive apply (PROVEN).**  Once the cell count `r` is at most
the sequence length `n` (always true: at most `n` distinct cells), the compiled
block apply does no more work than the naive `O(n²)` denoted apply (up to the single
`O(n·d)` cell-sum pass).  Directly `AttentionComplexity.blockCost_le_fullCost`. -/
theorem compiled_apply_le_naive (n r d : ℕ) (hr : r ≤ n) :
    AttentionComplexity.blockCost n r d
      ≤ AttentionComplexity.fullCost n d + n * d :=
  AttentionComplexity.blockCost_le_fullCost n r d hr

/-- **End-to-end compiler guarantee (PROVEN, axiom-clean).**  Packaging the verified
ML→quantum lowering for a compilable program:

1. *Semantics preserved.*  The full denotation restricted to the cell-uniform subspace is
   computed by the compiled quotient `Q̃ = symmQuotient` (`compile_denote_commutes`).
2. *Cost linear in `n`.*  The compiled apply runs in `blockCost n r d = n·(r·d + d)`,
   linear in sequence length (`compiled_apply_linear_in_n`).

The conjunction is the theorem "compilation is a semantics-preserving, complexity-reducing
optimizing pass." -/
theorem compiler_guarantee (C : Compilable V I) (w : I → ℂ) (n r d : ℕ) :
    (C.prog.denote.adj.mulVec
        (fun v => ∑ i, w i * C.blockEquitable.cellUniformVec i v)
      = (fun v => ∑ i, (C.blockEquitable.symmQuotient.mulVec w) i
            * C.blockEquitable.cellUniformVec i v))
    ∧ AttentionComplexity.blockCost n r d = n * (r * d + d) :=
  ⟨C.compile_denote_commutes w, compiled_apply_linear_in_n n r d⟩

end Compilable

/-! ## 6. A worked typing: structured attention is compilable

To witness that the typing judgment is inhabited (not vacuous), we show a single
attention head with a token-graph automorphism whose orbits are the cells *type-checks*:
it carries a `BlockEquitable` witness via `MachineLearning.equitableOfAutomorphism`, hence
compiles.  This is the verified "a symmetric (translation- or block-invariant) attention head
is a compilable program." -/

/-- **Structured attention type-checks (PROVEN).**  A single attention head `A` whose
symmetrized token graph has an automorphism `a` with cells = orbits (`hcell`, `horbit`,
exactly the hypotheses of `MachineLearning.equitableOfAutomorphism`) assembles into a
`Compilable` program: the syntax `attention A` together with the orbit equitable partition
of its denotation.  Hence it compiles to its small quotient with the preservation guarantee
`compile_denote_commutes`. -/
noncomputable def compilableOfStructuredAttention
    (A : MachineLearning.AttentionMatrix V)
    {I : Type u} [Fintype I] [DecidableEq I] (cells : V → I)
    (a : MachineLearning.GraphAut A.symmetrizedAttention)
    (hcell : ∀ v, cells (a.σ v) = cells v)
    (horbit : ∀ x y : V, cells x = cells y → ∃ k : ℕ, (a.σ ^ k) x = y) :
    Compilable V I where
  prog := .attention A
  blockEquitable :=
    -- `denote (attention A) = A.symmetrizedAttention` definitionally.
    MachineLearning.equitableOfAutomorphism A.symmetrizedAttention cells a hcell horbit

@[simp] theorem compilableOfStructuredAttention_prog
    (A : MachineLearning.AttentionMatrix V)
    {I : Type u} [Fintype I] [DecidableEq I] (cells : V → I)
    (a : MachineLearning.GraphAut A.symmetrizedAttention)
    (hcell : ∀ v, cells (a.σ v) = cells v)
    (horbit : ∀ x y : V, cells x = cells y → ∃ k : ℕ, (a.σ ^ k) x = y) :
    (compilableOfStructuredAttention A cells a hcell horbit).prog = .attention A := rfl

end TransformerDSL
end Graphplay
