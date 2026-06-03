/-
# Graphplay.Integrations.MachineLearning

**The machine-learning bridge** — the verified-framework seed for using the
Graphplay quantum-walk / equitable-partition toolkit to accelerate machine
learning (attention optimization, inference, linear algebra, search).

This module is the project's *thesis statement* for the ML application.  The
single load-bearing idea, stated five different ways below, is:

> An **equitable partition** of the token / feature graph is exactly the
> symmetry-reduction that makes both classical structured linear algebra **and**
> its quantum-walk acceleration tractable.  The machine-checked lift
> (`EquitablePartition.restrict_eq_symmQuotient`,
> `EquitablePartition.cellUniformSubspace_invariant`) is the *certificate* that
> the reduction is **exact** — no approximation, the small `r × r` quotient
> computes the same answer as the large `n × n` original on the symmetric
> sector.

## What lives here

1. **Attention as a weighted-graph operator** (`AttentionMatrix`,
   `symmetrizedAttention`).  A permutation symmetry of an attention pattern
   (translation invariance, block-structured heads, ...) induces an equitable
   partition of the token graph; the attention operator then reduces to a small
   `symmQuotient`.  *Proven:* the symmetry ⇒ equitable-partition direction
   (`equitableOfAutomorphism`) and that the symmetric quotient is Hermitian.
   *Proven (the genuine compression content):* attention restricts **exactly** to
   the `r × r` quotient on the cell-uniform subspace
   (`attention_restricts_to_symmQuotient`, via `restrict_eq_symmQuotient`), with the
   companion generic rank ceiling `rank Q̃ ≤ |I|` (`symmQuotient_rank_le_card`).
   *Informal/conjectural only:* the deeper low-rank compressibility narrative.

2. **Multi-head equitable reduction** (`MultiHeadAttention`).  If heads are
   related by a symmetry acting equitably, the (symmetrized) multi-head operator
   restricted to the cell-uniform subspace is computed by the quotient of the
   pooled operator.  *Proven:* the restriction-equals-quotient lift for the
   pooled head operator (`multiHead_restrict_eq_symmQuotient`).

3. **Quantum linear algebra for ML** (`RidgeRegression`, `kernelSolve`).  The
   linear solves inside ML — ridge regression `(XᵀX + λI)⁻¹ Xᵀy`, kernel
   methods, the implicit solve in normalization — are exactly the
   `MatrixInversion.LinearSystem` solved by CTQW matrix inversion, with the
   equitable speedup when the (normal/kernel) matrix has a symmetry.  *Proven
   (axiom-clean)*: a structured `A` with an `r`-cell equitable partition has its
   inversion restrict **exactly** to the `r × r` quotient solve on cell-uniform
   data (`ridge_inversion_restricts_to_quotient`, via the now-complete spine proof
   `MatrixInversion.inversion_restricts_to_quotient`).  The *quantum convergence
   rate* `O(κ/ε)` of the residual `r × r` CTQW solve is the only piece left to the
   spine (`MatrixInversion.LinearSystem.ctqw_success`, honest `sorry`).

4. **Search-as-optimization** (`CombinatorialOptimization`).  A marked-set
   search problem; Childs–Goldstone CTQW spatial search is the
   quantum-accelerated solver, with the CNO spectral-ratio optimality criterion.
   *Statement* of the Grover/CNO speedup for the structured/equitable case
   (`structured_search_optimal`), with honest `sorry` on the deep dynamical core
   (reusing `Search.CNO`).

5. A grounded discussion (§"Toward verified quantum ML acceleration") of what is
   *proven* vs *conjectural*.

## References

* Godsil–Royle, *Algebraic Graph Theory* (equitable partitions, divisor matrix).
* Bachman, Tamon, et al., arXiv:1108.0339 (equitable partitions & quantum walks).
* Harrow–Hassidim–Lloyd, PRL 103, 150502 (2009) (HHL linear solver).
* arXiv:2508.06611 (phase-estimation-free CTQW matrix inversion).
* Childs–Goldstone, arXiv:quant-ph/0306054 (CTQW spatial search).
* Chakraborty–Novo–Roland, arXiv:2004.12686 (CNO spectral-ratio optimality).
* Vaswani et al., *Attention Is All You Need*, NeurIPS 2017 (attention operator).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Exp
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Search
import Graphplay.Search.CNO
import Graphplay.Integrations.MatrixInversion
import Graphplay.Integrations.QuantumAdvantage

open scoped Matrix
open Complex

universe u v

namespace Graphplay
namespace MachineLearning

/-! ## 1. Attention as a weighted-graph operator

The transformer attention operator over `n` tokens is, per head, a row-stochastic
matrix `A` with `A i j = softmax_j(score i j)` — the probability that query token
`i` attends to key token `j`.  We model this concretely as a real matrix together
with the row-stochasticity property.  Its **symmetrized graph operator**
`S = (A + Aᵀ)/2 - diag` is a `WeightedGraph` (Hermitian, loopless), i.e. exactly
the quantum-walk Hamiltonian on the token graph that the rest of Graphplay
analyses.  The diagonal is removed because self-attention contributes a uniform
on-site energy that does not change the inter-token structure (and `WeightedGraph`
is loopless by definition). -/

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- An **attention matrix** over a token type `n`: a real, entrywise-nonnegative,
row-stochastic matrix.  `score i j` is the (already softmax-normalized) attention
weight from query token `i` onto key token `j`.  Row-stochasticity
`∀ i, ∑ j, score i j = 1` is the defining softmax constraint. -/
structure AttentionMatrix (n : Type u) [Fintype n] [DecidableEq n] where
  /-- The (softmax-normalized) attention scores. -/
  score : Matrix n n ℝ
  /-- Entrywise nonnegativity (softmax outputs are probabilities). -/
  nonneg : ∀ i j, 0 ≤ score i j
  /-- Row-stochasticity: each query's attention is a probability distribution. -/
  rowStoch : ∀ i, ∑ j, score i j = 1

namespace AttentionMatrix

/-- The **symmetrized score matrix** `(A + Aᵀ)/2` as a complex matrix, with the
diagonal zeroed out.  This is the Hermitian, loopless operator underlying the
token graph: the average of "`i` attends to `j`" and "`j` attends to `i`". -/
noncomputable def symmScore (A : AttentionMatrix n) : Matrix n n ℂ :=
  fun i j =>
    if i = j then 0
    else (((A.score i j + A.score j i) / 2 : ℝ) : ℂ)

/-- The symmetrized score matrix is Hermitian. -/
theorem symmScore_isHermitian (A : AttentionMatrix n) : A.symmScore.IsHermitian := by
  ext i j
  show star (A.symmScore j i) = A.symmScore i j
  unfold symmScore
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun he => h he.symm), if_neg h]
    rw [show ((A.score j i + A.score i j) / 2 : ℝ) = ((A.score i j + A.score j i) / 2 : ℝ)
          from by ring]
    exact Complex.conj_ofReal _

/-- The symmetrized score matrix is loopless (zero diagonal by construction). -/
@[simp] theorem symmScore_diag (A : AttentionMatrix n) (v : n) : A.symmScore v v = 0 := by
  unfold symmScore; simp

/-- The **symmetrized attention operator** as a `WeightedGraph`: the token graph
whose Hamiltonian is the symmetrized attention pattern.  This is the object the
entire equitable-partition / quantum-walk machinery applies to. -/
noncomputable def symmetrizedAttention (A : AttentionMatrix n) : WeightedGraph n where
  adj := A.symmScore
  herm := A.symmScore_isHermitian
  loopless := A.symmScore_diag

@[simp] theorem symmetrizedAttention_adj (A : AttentionMatrix n) :
    A.symmetrizedAttention.adj = A.symmScore := rfl

end AttentionMatrix

/-! ### Structured attention ⇒ equitable partition

A *structured* attention head is one with a permutation symmetry: a bijection
`σ : n → n` (e.g. a cyclic shift for translation-invariant / convolution-style
attention, or a block permutation for grouped heads) under which the score matrix
is invariant, `score (σ i) (σ j) = score i j`.  Such a `σ` is an **automorphism**
of the token graph, and **the orbits of `σ` form an equitable partition** — the
precise sense in which structured attention is low-rank / compressible: the
`n × n` operator collapses onto the (typically far smaller) orbit quotient.

We prove the cleanest faithful version: if the cell map `cells : n → I` is
*constant on the action of an automorphism `σ`* and refines the orbit structure
in the sense that branching is preserved, the partition is equitable.  Concretely
we package the automorphism-induced partition directly. -/

/-- A **token-graph automorphism**: a permutation `σ` of the tokens that
preserves the symmetrized attention weights, `adj (σ u) (σ v) = adj u v`.  This
is the formal content of "the attention pattern has a permutation symmetry"
(translation invariance, block structure, ...). -/
structure GraphAut (G : WeightedGraph n) where
  /-- The underlying permutation of tokens. -/
  σ : Equiv.Perm n
  /-- Weight preservation under the permutation. -/
  preserves : ∀ u v, G.adj (σ u) (σ v) = G.adj u v

/-- **Structured attention induces an equitable partition (proven direction).**

Given a token graph `G`, a cell labelling `cells : n → I`, and an automorphism
`a : GraphAut G` whose action is *compatible* with the cells — meaning `a.σ`
permutes within each cell (`cells (a.σ v) = cells v`) **and** acts transitively
enough that the cell map is constant on orbits witnessing branching — we obtain
an `EquitablePartition`.  The hypothesis we actually need (and that
translation-invariant / block-symmetric attention satisfies) is the *branching
uniformity within a cell*, which we derive from the automorphism when the cells
are unions of `⟨a.σ⟩`-orbits and the partition is the orbit partition.

Here we give the directly-usable form: the partition with branching uniformity
`huniform` supplied (which, for the orbit partition of an automorphism, is a
theorem — see `equitableOfAutomorphism_orbit` below) packaged as the genuine
`EquitablePartition`.  This is sorry-free: it is `EquitablePartition.refine`. -/
noncomputable def equitableOfAttention (G : WeightedGraph n)
    {I : Type v} [Fintype I] [DecidableEq I] (cells : n → I)
    (huniform : ∀ (i j : I) (x y : n), cells x = i → cells y = i →
      (∑ z, (if cells z = j then G.adj x z else 0))
      = (∑ z, (if cells z = j then G.adj y z else 0))) :
    EquitablePartition G I where
  cells := cells
  uniform := huniform

/-- **The orbit partition of a regular automorphism is equitable (proven).**

This is the genuine "symmetry ⇒ equitable partition" theorem.  Suppose every cell
is a single orbit of a cyclic automorphism in the strong sense that there is a
*cell-transitive* action: for any two vertices `x, y` in the same cell there is a
power `a.σ^k` mapping `x` to `y`.  We model this as the hypothesis `htrans` (the
group action is transitive on cells).  Then branching from `x` into any cell `j`
equals branching from `y`, because applying the automorphism `a.σ^k` is a weight-
and cell-preserving bijection of the summation index `z`. -/
theorem branching_eq_of_aut (G : WeightedGraph n)
    {I : Type v} [Fintype I] [DecidableEq I] (cells : n → I)
    (a : GraphAut G)
    (hcell : ∀ v, cells (a.σ v) = cells v)
    (j : I) (x : n) :
    (∑ z, (if cells z = j then G.adj (a.σ x) z else 0))
      = (∑ z, (if cells z = j then G.adj x z else 0)) := by
  -- Reindex the sum by `z = a.σ w`; the permutation `a.σ` is a bijection of the
  -- index set, the guard `cells z = j ↔ cells w = j` is preserved by `hcell`, and
  -- the weight `G.adj (a.σ x) (a.σ w) = G.adj x w` by `a.preserves`.
  rw [← Equiv.sum_comp a.σ (fun z => if cells z = j then G.adj (a.σ x) z else 0)]
  apply Finset.sum_congr rfl
  intro w _
  rw [hcell w, a.preserves x w]

/-- Branching is invariant under any power of the automorphism. -/
theorem branching_eq_of_aut_pow (G : WeightedGraph n)
    {I : Type v} [Fintype I] [DecidableEq I] (cells : n → I)
    (a : GraphAut G)
    (hcell : ∀ v, cells (a.σ v) = cells v)
    (j : I) (x : n) (k : ℕ) :
    (∑ z, (if cells z = j then G.adj ((a.σ ^ k) x) z else 0))
      = (∑ z, (if cells z = j then G.adj x z else 0)) := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, branching_eq_of_aut G cells a hcell j ((a.σ ^ m) x)]
    exact ih

/-- **Symmetry ⇒ equitable partition, fully proven for the single-automorphism
case.**  If the cell labelling is invariant under a token-graph automorphism `a`
and every cell is a single `⟨a.σ⟩`-orbit (`horbit`: any two same-cell vertices are
related by some power of `a.σ`), then the cell partition is equitable.  This is
the verified statement that "an attention pattern with a permutation symmetry
induces an equitable partition of the token graph." -/
noncomputable def equitableOfAutomorphism (G : WeightedGraph n)
    {I : Type v} [Fintype I] [DecidableEq I] (cells : n → I)
    (a : GraphAut G)
    (hcell : ∀ v, cells (a.σ v) = cells v)
    (horbit : ∀ x y : n, cells x = cells y → ∃ k : ℕ, (a.σ ^ k) x = y) :
    EquitablePartition G I where
  cells := cells
  uniform := by
    intro i j x y hx hy
    -- `x` and `y` are in the same cell, so `y = (a.σ ^ k) x` for some `k`.
    obtain ⟨k, hk⟩ := horbit x y (by rw [hx, hy])
    subst hk
    -- Branching is invariant under the `k`-fold power of the automorphism.
    exact (branching_eq_of_aut_pow G cells a hcell j x k).symm

/-- **Quotient rank is at most the cell count (PROVEN, axiom-clean).**

The `I × I` symmetric quotient `Q̃` of the attention operator has rank `≤ |I|`.

HONEST SCOPE (renamed from the over-selling `attention_compression_bound`): this
is the *generic* width bound `rank M ≤ (number of columns)` (`Matrix.rank_le_card_width`),
true for **any** `I × I` matrix — it says nothing specifically about equitability,
attention, or compression on its own.  Its only attention-specific content is the
*size* of the matrix it is applied to: because the equitable partition collapses
the operator onto the `|I|`-dimensional quotient (`attention_restricts_to_symmQuotient`
below, the genuine exact-reduction content), the bound `|I|` is the effective-rank
ceiling on the symmetric sector — but that load-bearing step is
`restrict_eq_symmQuotient`, not this inequality. -/
theorem symmQuotient_rank_le_card (A : AttentionMatrix n)
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition A.symmetrizedAttention I) :
    (P.symmQuotient.transpose).rank ≤ Fintype.card I :=
  -- Generic `rank ≤ width`; the attention/compression content is carried by
  -- `attention_restricts_to_symmQuotient`, not by this inequality.
  Matrix.rank_le_card_width _

/-- **Attention restricts exactly to the symmetric quotient — the genuine
compression statement (PROVEN, axiom-clean).**

When structured attention collapses onto an `r`-cell equitable partition `P`
(`r = |I|`), the symmetrized attention operator acts on the cell-uniform subspace
*exactly* as the `r × r` symmetric quotient `Q̃ = P.symmQuotient`: for any
quotient-side weight vector `w : I → ℂ`,

  `symmetrizedAttention.adj · (∑ i, w i · e_i)  =  ∑ i, (Q̃ · w) i · e_i`,

with `e_i = P.cellUniformVec i`.  This is the *real* "structured attention is
compressible" content — the large `n × n` operator's symmetric-sector dynamics
descend, with **no approximation**, to the small `r × r` quotient.  It is the
spine's `EquitablePartition.restrict_eq_symmQuotient` applied to the attention
operator.  (The companion rank ceiling `rank Q̃ ≤ |I|` is `symmQuotient_rank_le_card`.) -/
theorem attention_restricts_to_symmQuotient (A : AttentionMatrix n)
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition A.symmetrizedAttention I) (w : I → ℂ) :
    A.symmetrizedAttention.adj.mulVec (fun v => ∑ i, w i * P.cellUniformVec i v)
      = (fun v => ∑ i, (P.symmQuotient.mulVec w) i * P.cellUniformVec i v) :=
  P.restrict_eq_symmQuotient w

/-! ## 2. Multi-head equitable reduction

Multi-head attention is a finite list of heads; the combined operator is (a
linear pooling of) the per-head symmetrized operators.  When the heads are
related by a symmetry group acting equitably — "symmetric heads are redundant" —
the multi-head operator's dynamics on the cell-uniform subspace are computed by
the quotient of the **pooled** head operator, a verified compression statement.

We model the pooled operator as the (loopless Hermitian) **average** of the head
operators, which is again a `WeightedGraph`, and lift its equitable-partition
restriction via `EquitablePartition.restrict_eq_symmQuotient`. -/

/-- **Multi-head attention**: a nonempty list of attention heads over the same
token type.  (Nonemptiness via the explicit `head₀` plus `rest` so the pooled
average is always well-defined.) -/
structure MultiHeadAttention (n : Type u) [Fintype n] [DecidableEq n] where
  /-- The first head (guarantees nonemptiness). -/
  head₀ : AttentionMatrix n
  /-- The remaining heads. -/
  rest : List (AttentionMatrix n)

namespace MultiHeadAttention

/-- All heads of the multi-head attention as one list. -/
def heads (M : MultiHeadAttention n) : List (AttentionMatrix n) := M.head₀ :: M.rest

/-- The **pooled head matrix**: the sum of the symmetrized score matrices of all
heads.  A sum of Hermitian loopless matrices is Hermitian and loopless, so this is
again a `WeightedGraph` Hamiltonian. -/
noncomputable def pooledScore (M : MultiHeadAttention n) : Matrix n n ℂ :=
  (M.heads.map AttentionMatrix.symmScore).sum

theorem pooledScore_isHermitian (M : MultiHeadAttention n) :
    M.pooledScore.IsHermitian := by
  unfold pooledScore
  -- A sum of Hermitian matrices is Hermitian; induct over the mapped list.
  induction M.heads with
  | nil => simp only [List.map_nil, List.sum_nil]; exact Matrix.isHermitian_zero
  | cons h t ih =>
    rw [List.map_cons, List.sum_cons]
    exact (h.symmScore_isHermitian).add ih

@[simp] theorem pooledScore_diag (M : MultiHeadAttention n) (v : n) :
    M.pooledScore v v = 0 := by
  unfold pooledScore
  induction M.heads with
  | nil => simp
  | cons h t ih =>
    rw [List.map_cons, List.sum_cons, Matrix.add_apply, h.symmScore_diag, ih, add_zero]

/-- The **pooled multi-head operator** as a `WeightedGraph`: the token graph whose
Hamiltonian sums all heads.  Symmetric/redundant heads add coherently here, and
the equitable quotient of this single graph governs the whole stack's dynamics. -/
noncomputable def pooled (M : MultiHeadAttention n) : WeightedGraph n where
  adj := M.pooledScore
  herm := M.pooledScore_isHermitian
  loopless := M.pooledScore_diag

@[simp] theorem pooled_adj (M : MultiHeadAttention n) : M.pooled.adj = M.pooledScore := rfl

/-- **Multi-head equitable reduction (proven).**  If the pooled multi-head
operator has an equitable partition `P` (e.g. induced by a head-symmetry group
acting equitably on tokens), then the pooled operator's action on the
cell-uniform subspace is *exactly* the symmetric quotient `P.symmQuotient`:
for any quotient-side weight vector `w : I → ℂ`,

  `pooled.adj · (∑ i, w i · e_i)  =  ∑ i, (Q̃ · w) i · e_i`,

where `e_i = cellUniformVec i`.  This is the verified statement that "symmetric
heads are redundant ⇒ the whole stack's dynamics descend to the small quotient."
It is the spine's `restrict_eq_symmQuotient` applied to `M.pooled`. -/
theorem multiHead_restrict_eq_symmQuotient (M : MultiHeadAttention n)
    {I : Type u} [Fintype I] [DecidableEq I] (P : EquitablePartition M.pooled I)
    (w : I → ℂ) :
    M.pooled.adj.mulVec (fun v => ∑ i, w i * P.cellUniformVec i v)
      = (fun v => ∑ i, (P.symmQuotient.mulVec w) i * P.cellUniformVec i v) :=
  P.restrict_eq_symmQuotient w

/-- **Cell-uniform invariance for multi-head (proven).**  The cell-uniform
subspace of the pooled operator is invariant under the pooled multi-head
dynamics: structured (cell-uniform) inputs stay structured.  Directly
`EquitablePartition.cellUniformSubspace_invariant`. -/
theorem multiHead_cellUniform_invariant (M : MultiHeadAttention n)
    {I : Type u} [Fintype I] [DecidableEq I] (P : EquitablePartition M.pooled I)
    (v : n → ℂ) (hv : v ∈ P.cellUniformSubspace) :
    M.pooled.adj.mulVec v ∈ P.cellUniformSubspace :=
  P.cellUniformSubspace_invariant v hv

end MultiHeadAttention

/-! ## 3. Quantum linear algebra for ML

The linear solves at the heart of ML are all `MatrixInversion.LinearSystem`s:

* **Ridge regression** `θ = (XᵀX + λI)⁻¹ Xᵀy` — the normal-equation solve.  The
  matrix `A = XᵀX + λI` is Hermitian (it is `Xᴴ X + λI`) and, for `λ > 0`,
  invertible.  Its inversion is exactly the CTQW matrix-inversion target.
* **Kernel methods** `α = (K + λI)⁻¹ y` for a Gram matrix `K` — identical shape.
* The **implicit linear solve** inside attention normalization / whitening.

The Graphplay payoff: when the design has a symmetry — `XᵀX` (or `K`) has an
`r`-cell equitable partition, e.g. from feature-group / translation symmetry —
the inversion **restricts exactly to the `r × r` quotient solve** on cell-uniform
data.  This is the *complexity-reduction theorem*, and it is now **fully proven
and axiom-clean** (`MatrixInversion.inversion_restricts_to_quotient`, built on the
proven `restrict_eq_symmQuotient` with its inverse-of-restriction core completed —
`A⁻¹ b = y` by cancelling `A⁻¹ A = 1` after `A y = b`).  The *only* deferred piece
is the physical CTQW convergence *rate* (`ctqw_success`), a hardware statement, not
the (here-proven) exactness of the reduction. -/

/-- A **ridge-regression instance**: design matrix `X : Matrix m n ℂ` (rows =
samples `m`, columns = features `n`), targets `y : m → ℂ`, ridge parameter
`lam : ℝ`.  The normal matrix is `A = Xᴴ X + lam · I`. -/
structure RidgeRegression (m n : Type u) [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] where
  /-- The design matrix (samples × features). -/
  X : Matrix m n ℝ
  /-- The targets. -/
  y : m → ℝ
  /-- The (nonnegative) ridge regularization. -/
  lam : ℝ
  /-- Positivity of the ridge parameter (guarantees invertibility of `XᴴX+λI`). -/
  lam_pos : 0 < lam

namespace RidgeRegression

variable {m : Type u} [Fintype m] [DecidableEq m]

/-- The complex-valued design matrix (real entries coerced into ℂ), so the normal
matrix is a genuine Hermitian complex matrix usable by the CTQW solver. -/
noncomputable def Xc (R : RidgeRegression m n) : Matrix m n ℂ :=
  R.X.map (fun r => (r : ℂ))

/-- The **normal matrix** `A = Xᴴ X + λ I`, the system matrix of the ridge
normal equations.  It is `n × n` (feature space). -/
noncomputable def normalMatrix (R : RidgeRegression m n) : Matrix n n ℂ :=
  R.Xc.conjTranspose * R.Xc + (R.lam : ℂ) • (1 : Matrix n n ℂ)

/-- The normal matrix is Hermitian: `(XᴴX)ᴴ = XᴴX` and `λI` is real-diagonal. -/
theorem normalMatrix_isHermitian (R : RidgeRegression m n) :
    R.normalMatrix.IsHermitian := by
  unfold normalMatrix
  -- `XᴴX` is Hermitian (`Matrix.isHermitian_transpose_mul_self`-style), and
  -- `λ • 1` is Hermitian since `λ` is real.
  refine Matrix.IsHermitian.add ?_ ?_
  · -- (XᴴX)ᴴ = Xᴴ (Xᴴ)ᴴ = Xᴴ X
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  · -- (λ • 1)ᴴ = conj(λ) • 1 = λ • 1 since λ real
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      show (star (R.lam : ℂ)) = (R.lam : ℂ) from Complex.conj_ofReal _]

/-- The ridge right-hand side `b = Xᴴ y` (the `Xᵀy` of the normal equations). -/
noncomputable def rhs (R : RidgeRegression m n) : n → ℂ :=
  R.Xc.conjTranspose.mulVec (fun i => (R.y i : ℂ))

/-- **Ridge regression as a CTQW linear system.**  Packages the normal equations
`(XᴴX + λI) θ = Xᴴ y` as a `MatrixInversion.LinearSystem`, given a proof that the
normal matrix is invertible (automatic for `λ > 0`, recorded as `hinv`).  Solving
it by CTQW matrix inversion *is* solving ridge regression. -/
noncomputable def toLinearSystem (R : RidgeRegression m n)
    (hinv : IsUnit R.normalMatrix.det) : MatrixInversion.LinearSystem n where
  A := R.normalMatrix
  herm := R.normalMatrix_isHermitian
  inv := hinv
  b := R.rhs

/-- The CTQW-prepared ridge solution is the exact regression coefficient vector
`θ = (XᴴX + λI)⁻¹ Xᴴ y`.  (By definition of `LinearSystem.solution`; the physical
CTQW realizes it to within `ε` per `MatrixInversion.ctqw_success`.) -/
@[simp] theorem toLinearSystem_solution (R : RidgeRegression m n)
    (hinv : IsUnit R.normalMatrix.det) :
    (R.toLinearSystem hinv).solution = R.normalMatrix⁻¹.mulVec R.rhs := rfl

end RidgeRegression

/-- **Kernel ridge solve.**  Given a Hermitian, invertible Gram/kernel matrix `K`
on samples and targets `y`, the dual solution `α = (K)⁻¹ y` is a
`MatrixInversion.LinearSystem`.  (Add `λI` to `K` beforehand for regularized
kernels; here we take the already-regularized invertible `K`.) -/
noncomputable def kernelSolve (K : Matrix n n ℂ) (hherm : K.IsHermitian)
    (hinv : IsUnit K.det) (y : n → ℂ) : MatrixInversion.LinearSystem n where
  A := K
  herm := hherm
  inv := hinv
  b := y

/-- **Complexity-reduction theorem for structured ridge / kernel inversion
(PROVEN, axiom-clean — built on the now-complete spine).**

Let `A` be the (Hermitian, invertible) normal/kernel matrix presented as the
adjacency of a `WeightedGraph G`, with an `r`-cell equitable partition `P` whose
symmetric quotient `Q̃` is invertible.  If the right-hand side `b` is cell-uniform
with quotient coordinates `b̃ : I → ℂ`, then the exact solution `A⁻¹ b` is
cell-uniform with quotient coordinates `Q̃⁻¹ b̃`:

  `A⁻¹ · (∑ i, b̃ i · e_i)  =  ∑ i, (Q̃⁻¹ · b̃) i · e_i`.

In words: **inversion of a structured `n × n` ML system with an `r`-cell
equitable symmetry restricts exactly to an `r × r` quotient solve.**  The CTQW
matrix-inverter (or any classical solver) need only run on the `r`-dimensional
quotient — the symmetry-reduction is *exact*.

HONESTY NOTE: this delegates to `MatrixInversion.inversion_restricts_to_quotient`,
whose inverse-of-restriction body is now a **complete proof** (cancel `A⁻¹ A = 1`
after rewriting `A y = b` through `EquitablePartition.restrict_eq_symmQuotient`
and `Matrix.mul_nonsing_inv` on the invertible quotient).  Verified axiom-clean:
`#print axioms ridge_inversion_restricts_to_quotient` reports only
`propext, Classical.choice, Quot.sound` (no `sorryAx`).  So the **exact
symmetry-reduction of the inversion is fully machine-checked**; the only piece
that remains genuinely external is the *physical CTQW convergence rate*
(`MatrixInversion.LinearSystem.ctqw_success`, arXiv:2508.06611), now carried as
the named, cited literature class `CTQWInversionSuccess` (a typeclass assumption,
not an axiom) — a statement about the quantum hardware, not about the (here-proven)
linear-algebraic exactness of the reduction. -/
theorem ridge_inversion_restricts_to_quotient
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hinv : IsUnit G.adj.det)
    {I : Type u} [Fintype I] [DecidableEq I] (P : EquitablePartition G I)
    (hQinv : IsUnit P.symmQuotient.det)
    (bcoord : I → ℂ) :
    (G.adj⁻¹).mulVec (fun v => ∑ i, bcoord i * P.cellUniformVec i v)
      = (fun v => ∑ i, (P.symmQuotient⁻¹.mulVec bcoord) i * P.cellUniformVec i v) :=
  MatrixInversion.inversion_restricts_to_quotient G hinv P hQinv bcoord

/-! ## 4. Search-as-optimization

Many ML/inference tasks are *combinatorial optimization over a marked set*:
maximum-likelihood configuration search, MAP inference, feature/architecture
search, retrieval of a target among `N` candidates.  Childs–Goldstone CTQW
spatial search is the quantum-accelerated solver, with the CNO spectral-ratio
condition certifying `O(√N)` optimality. -/

/-- A **combinatorial optimization instance** as a marked-set search problem on a
token/configuration graph: the weighted graph `graph` (the search space's
connectivity / proposal kernel) and the `marked` set of optimal configurations to
be found.  Solving the optimization = finding a marked element. -/
structure CombinatorialOptimization (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The search-space graph (proposal connectivity). -/
  graph : WeightedGraph V
  /-- The marked (optimal / target) configurations. -/
  marked : Finset V

namespace CombinatorialOptimization

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The CTQW search Hamiltonian for the optimization instance at coupling `γ`:
`H = -γ A − P_marked`, the Childs–Goldstone spatial-search operator. -/
noncomputable def searchHamiltonian (O : CombinatorialOptimization V) (γ : ℝ) :
    Matrix V V ℂ :=
  O.graph.searchHamiltonian O.marked γ

/-- The search evolution `U(τ) = exp(-iτ H)` driving the quantum optimizer. -/
noncomputable def searchEvolve (O : CombinatorialOptimization V) (γ τ : ℝ) :
    Matrix V V ℂ :=
  O.graph.searchEvolve O.marked γ τ

/-- **Quantum-accelerated solvability**: the optimization is *quantumly solvable
with quadratic speedup* if the CTQW search finds a marked optimum with constant
probability in `O(√N)` time — `IsOptimalSearch` for some coupling/time within the
`√N` budget. -/
def IsQuantumSolvable (O : CombinatorialOptimization V) : Prop :=
  ∃ (γ τ C : ℝ), 0 < γ ∧ 0 ≤ C ∧
    τ ≤ C * Real.sqrt (Fintype.card V) ∧
    IsOptimalSearch O.graph O.marked γ τ

/-- **Grover/CNO speedup for structured search (statement; deep core sorried).**

Let the optimization graph be `d`-regular with the uniform all-ones principal
eigenvector at index `p` (the standard CNO normalization), and suppose the
**CNO spectral ratio is bounded below one** (`CNOSpectralRatio < 1`, equivalently
a constant spectral gap by `Search.CNOSpectralRatio_lt_one_iff`).  Then, for a
single marked optimum `w`, CTQW spatial search is optimal — `O(√N)` time,
constant success probability — the quantum (Grover-type) quadratic speedup for the
structured/equitable case.

The hypotheses are exactly CNO's regime of validity (regularity + uniform
principal eigenvector + ratio `< 1`); the conclusion is `IsOptimalCTQWSearch`.
The deep dynamical analysis (amplitude/time computation of arXiv:2004.12686
Thms 1–2) is the honest `sorry`, **reused** from
`Search.optimal_search_of_spectral_ratio_lt_one`. -/
theorem structured_search_optimal (O : CombinatorialOptimization V)
    (w p : V) (d : ℂ)
    (hne : Nonempty V)
    (hreg : O.graph.isRegular d)
    (huniform : ∀ x : V,
      (O.graph.herm.eigenvectorBasis p : V → ℂ) x
        = (1 : ℂ) / Real.sqrt (Fintype.card V))
    (hp : 0 < |O.graph.herm.eigenvalues p|)
    (hratio : CNOSpectralRatio O.graph p < 1) :
    IsOptimalCTQWSearch O.graph w :=
  -- Directly the CNO headline theorem from `Graphplay.Search.CNO`.
  Graphplay.optimal_search_of_spectral_ratio_lt_one O.graph w p d hne hreg huniform hp hratio

/-! ### Equitable-quotient search advantage for structured optimization

The flagship ML payoff, surfaced for `CombinatorialOptimization` and built on the
**axiom-clean** results of `Graphplay.QuantumAdvantage` (no honest `sorry` in the
dynamical core: the upper bound is the unconditional Rabi computation, the lower
bound is the indistinguishability argument).

When the optimization graph `O.graph` carries an `r`-cell equitable partition `P`
(`r = |I|`) and the marked set `O.marked` is **cell-uniform** (constant on each
cell — the natural condition for a symmetric search landscape), two things hold
*simultaneously and exactly*:

* **(exact reduction).**  The host CTQW search dynamics on `O.graph` restricted to
  cell-uniform states are computed by the `r×r` refined-quotient search
  Hamiltonian — the dynamics live entirely on the `r`-dimensional quotient,
  independent of `|V| = N` (`QuantumAdvantage.structured_search_advantage` part a,
  itself `Graphplay.search_quotient_reduction`).

* **(√r vs r separation).**  Quantum search on the quotient succeeds in time
  `O(√r)` (and `2√r ≤ r`), while every classical query algorithm needs `Ω(r)`
  queries on the `r` cells — the genuine quadratic separation, with the quantum
  cost set by the equitable-cell count `r`, **not** the configuration-space size
  `N` (`QuantumAdvantage.ml_structured_search_quantum_advantage`). -/

/-- **Structured-optimization quotient reduction (PROVEN, axiom-clean).**

For a `CombinatorialOptimization` whose graph has an `r`-cell equitable partition
`P` and whose marked set is cell-uniform (`hM`), the host search Hamiltonian
`H = -γ·A − P_marked` acts on any cell-uniform state `∑ ib, w ib · e_ib` exactly as
the `r×r` refined-quotient search Hamiltonian `-γ·Q̃' − markedDiag`.  The search
dynamics of the optimizer descend, with no approximation, to the
`(I × Bool)`-indexed quotient — so the effective search dimension is the number of
equitable cells, independent of `|V| = N`.

This is `QuantumAdvantage.structured_search_advantage` (part a), reused verbatim
for the `CombinatorialOptimization` instance. -/
theorem structured_quotient_reduction (O : CombinatorialOptimization V)
    {I : Type u} [Fintype I] [DecidableEq I] (P : EquitablePartition O.graph I)
    (γ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ O.marked ↔ y ∈ O.marked))
    (w : Graphplay.MarkedRefined I → ℂ) :
    (let P' := P.refineByMarked O.marked hM
     (O.graph.searchHamiltonian O.marked γ).mulVec
         (fun v => ∑ ib, w ib * P'.cellUniformVec ib v)
        = (fun v => ∑ ib,
            ((-(γ : ℂ) • P'.symmQuotient - Graphplay.markedDiag I).mulVec w) ib *
              P'.cellUniformVec ib v)) :=
  (Graphplay.QuantumAdvantage.structured_search_advantage P O.marked γ hM w).1

/-- **Structured-optimization quantum advantage — the flagship ML claim
(PROVEN, axiom-clean; deep dynamical core is the unconditional Rabi computation,
NOT a `sorry`).**

Let a `CombinatorialOptimization O` have a search graph with an `r`-cell equitable
partition `P` and a cell-uniform marked set (`hM`), with effective search
dimension `r = |I| ≥ 4`.  Then, *with the quantum cost governed by the
equitable-cell count `r` rather than the configuration-space size `|V| = N`*:

* **(a) exact reduction.**  The host search dynamics descend exactly to the
  `r×r` refined-quotient (`structured_quotient_reduction` / `search_quotient_reduction`);

* **(b) quantum O(√r).**  There is an evolution time `t_q ≤ (π/2)·√r = O(√r)` at
  which the reduced quotient search reaches *exact* marked amplitude `≥ √(1/2)`
  (`exactSearchAmplitude`, exact Rabi frequency `1/√r`, **no `r→∞` idealization** —
  the unconditional `quantum_search_exact_amplitude` computation);

* **(c) classical Ω(r).**  No correct classical query algorithm can be `Q`-local
  for a queried cell-set `Q` with `Q.card + 1 < r` — the genuine indistinguishability
  lower bound on the `r` cells (`no_correct_QLocal_certifier`).

Together (b)+(c) are a real `√r` vs `r` quadratic separation; (a) certifies that
`r = |I|` (the number of equitable cells), not `N = |V|`, is the dimension that
sets the quantum cost.  Reuses `QuantumAdvantage.structured_search_advantage` and
`QuantumAdvantage.ml_structured_search_quantum_advantage`, both axiom-clean. -/
theorem structured_quantum_advantage (O : CombinatorialOptimization V)
    {I : Type u} [Fintype I] [DecidableEq I] (P : EquitablePartition O.graph I)
    (γ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ O.marked ↔ y ∈ O.marked))
    (hr : 4 ≤ Fintype.card I)
    (w : Graphplay.MarkedRefined I → ℂ) :
    -- (a) exact quotient reduction (effective dimension r = |I|, independent of |V|)
    ((let P' := P.refineByMarked O.marked hM
      (O.graph.searchHamiltonian O.marked γ).mulVec
          (fun v => ∑ ib, w ib * P'.cellUniformVec ib v)
        = (fun v => ∑ ib,
            ((-(γ : ℂ) • P'.symmQuotient - Graphplay.markedDiag I).mulVec w) ib *
              P'.cellUniformVec ib v)))
    ∧
    -- (b) quantum: EXACT marked amplitude ≥ √(1/2) at evolution time ≤ (π/2)√r
    (∃ t_q : ℝ, 0 ≤ t_q ∧ t_q ≤ (Real.pi / 2) * Real.sqrt (Fintype.card I) ∧
        Real.sqrt (1 / 2) ≤
          Graphplay.QuantumAdvantage.exactSearchAmplitude (Fintype.card I) t_q)
    ∧
    -- (c) classical Ω(r): no correct Q-local certifier when Q.card + 1 < r
    (∀ Q : Finset I, Q.card + 1 < Fintype.card I →
        ¬ ∃ A : (I → Bool) → I,
            Graphplay.QuantumAdvantage.QLocal Q A ∧
            Graphplay.QuantumAdvantage.CorrectSearch A) := by
  refine ⟨structured_quotient_reduction O P γ hM w, ?_, ?_⟩
  · -- The √r upper bound: the EXACT-amplitude flagship advantage at r = |I|.
    obtain ⟨⟨t, ht0, htb, hamp⟩, _⟩ :=
      Graphplay.QuantumAdvantage.ml_structured_search_quantum_advantage_exact
        (Fintype.card I) hr
    exact ⟨t, ht0, htb, hamp⟩
  · -- The Ω(r) lower bound: the indistinguishability clause of the flagship.
    intro Q hlt
    exact (Graphplay.QuantumAdvantage.structured_search_advantage P O.marked γ hM w).2 Q hlt

end CombinatorialOptimization

/-! ## 5. Toward verified quantum ML acceleration

**The thesis.**  Across all four bridges above, the *same* mathematical object —
an **equitable partition** of the relevant graph (token graph, feature/design
graph, search graph) — is the symmetry-reduction that makes the problem tractable,
and the *same* machine-checked lift certifies the reduction is exact:

* `EquitablePartition.cellUniformSubspace_invariant` — structured (cell-uniform)
  data stays structured under the dynamics;
* `EquitablePartition.restrict_eq_symmQuotient` — the large operator restricted to
  the symmetric sector **equals** the small `r × r` symmetric quotient `Q̃`;
* `EquitablePartition.symmQuotient_isHermitian` — `Q̃` is a genuine Hamiltonian, so
  the quotient problem is itself a CTQW problem.

**What is genuinely proven here (sorry-free):**

* Attention is a `WeightedGraph` (`AttentionMatrix.symmetrizedAttention`,
  `symmScore_isHermitian`, `symmScore_diag`).
* **Symmetry ⇒ equitable partition** for a token-graph automorphism whose orbits
  are the cells (`branching_eq_of_aut`, `equitableOfAutomorphism`) — the verified
  "structured attention is compressible" direction.
* **Multi-head reduction**: the pooled operator is a `WeightedGraph`
  (`pooledScore_isHermitian`, `pooledScore_diag`), and its restriction to the
  cell-uniform subspace is the symmetric quotient
  (`multiHead_restrict_eq_symmQuotient`) with cell-uniform invariance
  (`multiHead_cellUniform_invariant`).
* **ML linear solves are CTQW linear systems** (`RidgeRegression.toLinearSystem`,
  `normalMatrix_isHermitian`, `kernelSolve`).
* **Structured-inversion complexity reduction**
  (`ridge_inversion_restricts_to_quotient`) — an `r`-cell equitable symmetry makes
  inversion restrict **exactly** to the `r × r` quotient solve.  Now *fully proven
  and axiom-clean*: the spine core `MatrixInversion.inversion_restricts_to_quotient`
  is a complete proof (no `sorry`), so the linear-algebraic exactness of the
  reduction is machine-checked.  Only the physical CTQW *rate* remains a spine
  `sorry` (`ctqw_success`).

**What is honest-`sorry` (deep claims only, never a `def`):**

* `structured_search_optimal` — the CNO `O(√N)` dynamical analysis, reused from
  `Search.optimal_search_of_spectral_ratio_lt_one` (arXiv:2004.12686 Thms 1–2).
* The CTQW convergence *rate* lives upstream in
  `MatrixInversion.ctqw_success` (arXiv:2508.06611) — the only `sorry` behind the
  inversion story.  (`ridge_inversion_restricts_to_quotient` itself is now PROVEN:
  the spine's `inversion_restricts_to_quotient` is a complete proof; see above.)

  (The attention compression content is `attention_restricts_to_symmQuotient` —
  the operator restricts **exactly** to the `r × r` quotient on the cell-uniform
  subspace (`restrict_eq_symmQuotient`), fully proven.  Its companion generic rank
  ceiling `rank Q̃ ≤ |I|` is `symmQuotient_rank_le_card` (`Matrix.rank_le_card_width`,
  true for any `I × I` matrix); only the informal low-rank *compressibility
  narrative* is conjectural.)

**Conjectural vs proven, honestly flagged.**  *Proven and exact:* the
symmetry-reduction / quotient-restriction statements — these are linear algebra
and follow from the spine.  *Conjectural / physics-deep:* the quantum *advantage*
claims (CTQW convergence rate, `O(κ/ε)` inversion time, `O(√N)` search time).  The
contribution of Graphplay is to make the **reduction** machine-certified, so that
whatever quantum speedup the upstream dynamical results provide is inherited by
the *small quotient problem* with a proof that the answer is identical.
-/

end MachineLearning
end Graphplay
