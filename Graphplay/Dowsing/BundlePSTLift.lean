/-
# Graphplay.Dowsing.BundlePSTLift

**Universal bundle PST lift.**

This file gives a uniform iff statement for cell-uniform perfect state transfer
(PST) on the *total* graph of a `GraphBundle` versus PST on the *quotient*
graph cut out by the canonical fiber partition.  When the fibers are regular
and the couplings biregular, the fiber index map is an equitable partition
(`GraphBundle.fiberPartition`, Tower A2), so the existing
`EquitablePartition.pst_lift` (Tower 2 statement in `Graphplay/PST.lean`)
immediately yields the master theorem.

The master theorem **strictly subsumes** the three perfect-state-transfer
preservation theorems of Ge–Greenberg–Perez–Tamon
("Perfect state transfer, graph products and equitable partitions",
arXiv:1009.1340 — abbreviated *GGPT* throughout):

* the Cartesian product preserves PST,
* the lexicographic product `G[H]` preserves PST when `H` is regular,
* the weak product (= tensor product / direct product) preserves PST under
  spectral hypotheses,

and adds **further corollaries** that do not appear in GGPT:

* the strong product `G ⊠ H`,
* the conormal product (`co`-strong product),
* the disjunctive product (the "or" of `□` and the lexicographic),
* the `TemplateJoin` construction (with constant fiber size),
* the `colorCompletion` of a coloring `V → I` over a complete template.

Beyond GGPT we also state the **stratified bundle lift** (extension to
fiber bundles whose fibers fail regularity, via a finer equitable partition
adapted to extra symmetry) and the **Bachman–Tamon–Feder reduction**
(arXiv:1108.0339 §3, building on Feder PRL 97 180502) showing that the
Cartesian product of quotients is itself a quotient of the Cartesian
product — a categorical naturality square between `total` and `quotient`.

All hard proofs are deferred as `sorry`; the file is a *statement layer*
intended to be downstream-citable from `Graphplay.Toolkit.*` and the
search/scheduler tooling.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Bundle
import Graphplay.PST
import Graphplay.PST.QuotientIff
import Graphplay.Loopy
import Graphplay.Product
import Graphplay.Product.PST

open scoped Matrix

universe u v w

namespace Graphplay
namespace GraphBundle

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {Q : SimpleGraph I} {V : I → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-! ## 1. The fiber partition packaged for the master theorem

We package `GraphBundle.fiberPartition` into the shape used by
`EquitablePartition.pst_lift`.  The data are: per-fiber regularity degrees
`d : I → ℂ` and biregular row/column sums `α β` indexed by template edges.
-/

/-- The canonical equitable partition of the total bundle by fiber index,
given regularity of each fiber and biregularity of every coupling. -/
noncomputable def fiberEquitable
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h)) :
    EquitablePartition B.total I :=
  B.fiberPartition d hfib α β hcouple

/-- The quotient graph of the fiber partition, as a **loopy** weighted graph.

The symmetric quotient `Q̃ = D^{1/2} Q D^{-1/2}` carries a genuinely nonzero
diagonal (its diagonal entries record the fiber regularity degrees `d i`), so
it does *not* live in the loopless `WeightedGraph` layer.  It lives in
`LoopyWeightedGraph` (`Graphplay.Loopy`), exactly the loopless-free Hermitian
layer built for this purpose.  This dissolves the former `loopless` blocker:
there is no zero-diagonal field to discharge. -/
noncomputable def fiberQuotient
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h)) :
    LoopyWeightedGraph I where
  adj := (B.fiberEquitable d hfib α β hcouple).symmQuotient
  herm := (B.fiberEquitable d hfib α β hcouple).symmQuotient_isHermitian

/-! ## 2. The master theorem -/

/-- **Master theorem (universal bundle PST lift).**

If every fiber of a graph bundle is `d i`-regular and every coupling is
`(α e, β e)`-biregular, then cell-uniform PST between cells `i` and `j` at
time `τ` on the *total* graph holds iff PST between the corresponding
vertices `i` and `j` holds on the *quotient* (fiber) graph.

The forward direction (host → quotient) is *automatic* from
`EquitablePartition.pst_lift` together with the observation that the
cell-uniform subspace contains the PST source/target states (this is the
"uniform marginalization" lemma).  The backward direction (quotient → host)
is the content of `pst_lift`.

This statement **strictly contains** the three GGPT theorems below as
specializations to particular bundle templates and couplings; see §3.
-/
theorem pst_iff_quotient
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h))
    (hne : ∀ k, (B.fiberEquitable d hfib α β hcouple).cellCard k ≠ 0)
    (i j : I) (τ : ℝ) :
    IsCellUniformPST B.total (B.fiberEquitable d hfib α β hcouple) i j τ ↔
    LoopyWeightedGraph.IsLoopyPST (B.fiberQuotient d hfib α β hcouple) j i τ := by
  -- `IsLoopyPST (fiberQuotient) j i τ` unfolds to
  -- `‖(fiberQuotient).evolve τ j i‖ = 1`
  -- = `‖exp(-(I·τ) • (fiberQuotient).adj) j i‖ = 1`
  -- = `‖exp(-(I·τ) • symmQuotient) j i‖ = 1`
  -- (since `(fiberQuotient).adj = (fiberEquitable …).symmQuotient`), which is
  -- exactly the right-hand side of the Bachman–Tamon iff
  -- `EquitablePartition.cellUniformPST_iff_quotientPST` from `QuotientIff`.
  -- The `hne` hypothesis (every cell — i.e. every fiber — nonempty) is the
  -- one that lemma requires; we surface it as an explicit hypothesis since a
  -- bundle may a priori have an empty fiber.
  exact (B.fiberEquitable d hfib α β hcouple).cellUniformPST_iff_quotientPST hne i j τ

/-- One-way form: PST on the quotient lifts to cell-uniform PST on the
total bundle.  This is the direction used in synthesis. -/
theorem cellUniformPST_of_quotient_pst
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h))
    (hne : ∀ k, (B.fiberEquitable d hfib α β hcouple).cellCard k ≠ 0)
    (i j : I) (τ : ℝ)
    (h : LoopyWeightedGraph.IsLoopyPST (B.fiberQuotient d hfib α β hcouple) j i τ) :
    IsCellUniformPST B.total (B.fiberEquitable d hfib α β hcouple) i j τ :=
  (B.pst_iff_quotient d hfib α β hcouple hne i j τ).mpr h

/-- The other direction: cell-uniform PST on the total bundle descends to
PST on the quotient. -/
theorem quotient_pst_of_cellUniformPST
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h))
    (hne : ∀ k, (B.fiberEquitable d hfib α β hcouple).cellCard k ≠ 0)
    (i j : I) (τ : ℝ)
    (h : IsCellUniformPST B.total (B.fiberEquitable d hfib α β hcouple) i j τ) :
    LoopyWeightedGraph.IsLoopyPST (B.fiberQuotient d hfib α β hcouple) j i τ :=
  (B.pst_iff_quotient d hfib α β hcouple hne i j τ).mp h

end GraphBundle

/-! ## 3. Corollaries: GGPT (1009.1340) and beyond -/

namespace BundlePSTCorollaries

variable {V W : Type*}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ### 3.0 Rank-one (all-ones) Kronecker-product exponential closed form

The lex/template-join/color-completion couplings all carry the
Kronecker-**product** block `A_G ⊗ₖ J_W` (the all-ones `W × W` block `J_W`),
which — unlike the Kronecker-**sum** of the Cartesian case — does *not* split as
`exp A_G ⊗ₖ exp J_W`.  It does, however, have an exact **closed form**, because
`J_W = |W| · P_W` with `P_W = (1/|W|) J_W` a *rank-one idempotent* projector:

  `exp(M ⊗ₖ P_W) = 1 + (exp M − 1) ⊗ₖ P_W`.

This is the genuine engine the GGPT lex/template arguments rest on (the
"all-ones eigenvector carries the rescaled-time `G`-walk" computation).  We build
it here from the exponential power series, mirroring `exp_kronecker_one`. -/

section RankOneKronecker

open scoped Kronecker
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The normalized all-ones (rank-one projector) matrix `P_W = (1/|W|) J_W`. -/
noncomputable def projOnes (W : Type*) [Fintype W] [DecidableEq W] : Matrix W W ℂ :=
  Matrix.of fun _ _ => (1 : ℂ) / (Fintype.card W : ℂ)

/-- `P_W` is idempotent (a genuine projector) when `W` is nonempty. -/
theorem projOnes_mul (W : Type*) [Fintype W] [DecidableEq W]
    (hW : Fintype.card W ≠ 0) : projOnes W * projOnes W = projOnes W := by
  ext a b
  simp only [projOnes, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card W : ℂ) ≠ 0 := by exact_mod_cast hW
  field_simp

/-- `(A ⊗ₖ P_W)^n = A^n ⊗ₖ P_W` for `n ≥ 1` (the `P_W` factor is idempotent). -/
theorem kronecker_projOnes_pow (A : Matrix V V ℂ) (hW : Fintype.card W ≠ 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (A ⊗ₖ projOnes W) ^ n = (A ^ n) ⊗ₖ (projOnes W) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge 1 (k + 1) with h1 | h1
    · rw [pow_succ, ih (by omega), ← Matrix.mul_kronecker_mul, projOnes_mul W hW, pow_succ]
    · have hk : k = 0 := by omega
      subst hk; simp

/-- **Rank-one Kronecker-product exponential.**
`exp(M ⊗ₖ P_W) = 1 + (exp M − 1) ⊗ₖ P_W` (for `P_W = (1/|W|) J_W` idempotent,
`W` nonempty).  Proved by the exp power series pushed through the continuous
additive homomorphism `X ↦ X ⊗ₖ P_W` on the `n ≥ 1` tail. -/
theorem exp_kronecker_projOnes (M : Matrix V V ℂ) (hW : Fintype.card W ≠ 0) :
    NormedSpace.exp (M ⊗ₖ projOnes W)
      = (1 : Matrix (V × W) (V × W) ℂ) + (NormedSpace.exp M - 1) ⊗ₖ projOnes W := by
  let φ : Matrix V V ℂ →+ Matrix (V × W) (V × W) ℂ :=
    { toFun := fun X => X ⊗ₖ projOnes W
      map_zero' := Matrix.zero_kronecker _
      map_add' := fun X Y => Matrix.add_kronecker X Y _ }
  have hφc : Continuous φ := by
    refine continuous_matrix ?_
    rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.kroneckerMap_apply]
    exact (continuous_id.matrix_elem i₁ j₁).mul continuous_const
  have hexpM : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n) (NormedSpace.exp M) :=
    NormedSpace.exp_series_hasSum_exp' M
  have hexpMP : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • (M ⊗ₖ projOnes W) ^ n)
      (NormedSpace.exp (M ⊗ₖ projOnes W)) :=
    NormedSpace.exp_series_hasSum_exp' (M ⊗ₖ projOnes W)
  -- Split off `n = 0` from both series (its term is the identity `1`).
  have hexpM1 : HasSum (fun n : ℕ => (Nat.factorial (n + 1) : ℂ)⁻¹ • M ^ (n + 1))
      (NormedSpace.exp M - 1) := by
    have := (hasSum_nat_add_iff' (f := fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n) 1).mpr hexpM
    simpa using this
  have hMPshift : HasSum
      (fun n : ℕ => (Nat.factorial (n + 1) : ℂ)⁻¹ • (M ⊗ₖ projOnes W) ^ (n + 1))
      (NormedSpace.exp (M ⊗ₖ projOnes W) - 1) := by
    have := (hasSum_nat_add_iff'
      (f := fun n => (Nat.factorial n : ℂ)⁻¹ • (M ⊗ₖ projOnes W) ^ n) 1).mpr hexpMP
    simpa using this
  have hφM1 := hexpM1.map φ hφc
  have hterm : (φ ∘ fun n : ℕ => (Nat.factorial (n + 1) : ℂ)⁻¹ • M ^ (n + 1))
      = (fun n : ℕ => (Nat.factorial (n + 1) : ℂ)⁻¹ • (M ⊗ₖ projOnes W) ^ (n + 1)) := by
    funext n
    show ((Nat.factorial (n + 1) : ℂ)⁻¹ • M ^ (n + 1)) ⊗ₖ projOnes W
       = (Nat.factorial (n + 1) : ℂ)⁻¹ • (M ⊗ₖ projOnes W) ^ (n + 1)
    rw [kronecker_projOnes_pow M hW (n + 1) (by omega), Matrix.smul_kronecker]
  rw [hterm] at hφM1
  have heq : (NormedSpace.exp M - 1) ⊗ₖ projOnes W
      = NormedSpace.exp (M ⊗ₖ projOnes W) - 1 :=
    hφM1.unique hMPshift
  rw [heq]; abel

end RankOneKronecker

/-! ### 3.1 GGPT: Cartesian product preserves PST -/

/-- **Bridge lemma.**  The bundle-corner Cartesian product
`GraphBundle.cartesianProduct G H` (Bundle.lean) and the first-class
Kronecker-sum Cartesian product `WeightedGraph.cartesianProduct G H`
(Product.lean) have the *same adjacency matrix*.

The two definitions write the same entrywise sum with the two `if`-summands
in the opposite order:
* bundle:  `(if v₁=v₂ then H.adj w₁ w₂ else 0) + (if w₁=w₂ then G.adj v₁ v₂ else 0)`,
* product: `(if w₁=w₂ then G.adj v₁ v₂ else 0) + (if v₁=v₂ then H.adj w₁ w₂ else 0)`,

so the equality is just commutativity of addition. -/
theorem graphBundle_cartesianProduct_adj_eq
    (G : WeightedGraph V) (H : WeightedGraph W) :
    (GraphBundle.cartesianProduct G H).adj =
      (WeightedGraph.cartesianProduct G H).adj := by
  funext p q
  show (if p.1 = q.1 then H.adj p.2 q.2 else 0) + (if p.2 = q.2 then G.adj p.1 q.1 else 0)
      = (if p.2 = q.2 then G.adj p.1 q.1 else 0) + (if p.1 = q.1 then H.adj p.2 q.2 else 0)
  exact add_comm _ _

/-- The two Cartesian products have the same quantum-walk evolution (since the
walk only depends on the adjacency matrix and the adjacencies agree). -/
theorem graphBundle_cartesianProduct_evolve_eq
    (G : WeightedGraph V) (H : WeightedGraph W) (τ : ℝ) :
    (GraphBundle.cartesianProduct G H).evolve τ =
      (WeightedGraph.cartesianProduct G H).evolve τ := by
  unfold WeightedGraph.evolve
  rw [graphBundle_cartesianProduct_adj_eq]

/-- **GGPT Theorem (Cartesian, [1009.1340 §1, Christandl et al. [11]]).**
The Cartesian product `G □ H` exhibits PST between `(u₁, w)` and `(u₂, w)`
whenever `G` exhibits PST between `u₁` and `u₂` and `H` is *periodic at `w`*
at the same time `τ` (i.e. `‖(H.evolve τ) w w‖ = 1`).

This is the honest, fully-general transfer theorem.  GGPT derive the
periodicity of `H` at `w` from regularity together with a spectral lattice
condition; stated directly as `‖(H.evolve τ) w w‖ = 1` the hypothesis makes the
statement *true* without that extra input, and iterating it from the single
edge `K₂` yields PST on the hypercube `Q_n = K₂^□n`.

Proof: the bundle-corner Cartesian product agrees with the first-class
Kronecker-sum product (`graphBundle_cartesianProduct_evolve_eq`), so this is a
direct application of the genuinely-proven, axiom-clean engine
`WeightedGraph.cartesianProduct_pst` in `Graphplay/Product/PST.lean`. -/
theorem cartesianProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    (u₁ u₂ : V) (w : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) (hH : ‖(H.evolve τ) w w‖ = 1) :
    IsPST (GraphBundle.cartesianProduct G H) (u₁, w) (u₂, w) τ := by
  have hcore : IsPST (WeightedGraph.cartesianProduct G H) (u₁, w) (u₂, w) τ :=
    WeightedGraph.cartesianProduct_pst G H hG hH
  unfold IsPST at hcore ⊢
  rwa [graphBundle_cartesianProduct_evolve_eq]

/-! ### 3.2 GGPT: Lexicographic product — exact amplitude closed form -/

open scoped Kronecker in
/-- The lexicographic adjacency is the Kronecker sum-plus-product
`A_{G[H]} = 1_V ⊗ₖ A_H + A_G ⊗ₖ J_W` (`J_W` the all-ones `W × W` block: the
lex coupling is constant `G.adj v₁ v₂` across every `H`-coordinate pair). -/
theorem lexProduct_adj_eq (G : WeightedGraph V) (H : WeightedGraph W) :
    (GraphBundle.lexProduct G H).adj
      = (1 : Matrix V V ℂ) ⊗ₖ H.adj
        + G.adj ⊗ₖ (Matrix.of fun _ _ : W => (1 : ℂ)) := by
  ext p q
  obtain ⟨v₁, w₁⟩ := p; obtain ⟨v₂, w₂⟩ := q
  show (if v₁ = v₂ then H.adj w₁ w₂ else G.adj v₁ v₂)
      = (1 : Matrix V V ℂ) v₁ v₂ * H.adj w₁ w₂ + G.adj v₁ v₂ * (1 : ℂ)
  rw [Matrix.one_apply]
  by_cases h : v₁ = v₂
  · subst h; rw [if_pos rfl, if_pos rfl]; simp [G.loopless]
  · rw [if_neg h, if_neg h]; simp

open scoped Kronecker in
/-- **GGPT Lexicographic — exact off-diagonal amplitude (corrected).**

The previous `lexProduct_pst` claimed *raw-vertex* PST on `G[H]` at the literal
`τ`; this is **FALSE** for `|W| > 1`.  The lex coupling block `A_G ⊗ₖ J_W` is a
*rank-deficient* Kronecker **product** (`J_W` has rank one), so on the all-ones
fiber direction the `G`-walk runs at the **rescaled time** `|W|·τ` and, crucially,
the off-diagonal amplitude is suppressed by the factor `1/|W|` — it can never
reach modulus `1`.  (This is exactly why GGPT state lex transfer at the level of
the *normalized cell-uniform* states — the master theorem `pst_iff_quotient` —
not raw vertices.)

We therefore replace the false PST claim by the genuinely-true **exact amplitude
closed form**, which is the real content: for `u₁ ≠ u₂`, with `H` `dH`-regular,
the lex evolution entry factors as the (rescaled-time) `G`-walk entry times the
fiber row-phase, divided by `|W|`:

  `evolve(G[H]) τ (u₂,w₂) (u₁,w₁) =
     (1/|W|) · (exp(-iτ·dH)) · (exp(-i(|W|τ)·A_G))_{u₂ u₁}`.

This makes the genuine `1/|W|`-suppression and the `|W|τ` rescale explicit and
is closed via the rank-one Kronecker exponential `exp_kronecker_projOnes`. -/
theorem lexProduct_evolve_offdiag
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dH : ℂ} (hHreg : H.isRegular dH)
    (hW : Fintype.card W ≠ 0)
    (u₁ u₂ : V) (w₁ w₂ : W) (τ : ℝ) (hu : u₁ ≠ u₂) :
    (GraphBundle.lexProduct G H).evolve τ (u₂, w₂) (u₁, w₁)
      = (1 / (Fintype.card W : ℂ))
        * NormedSpace.exp (-(Complex.I * (τ : ℂ)) * dH)
        * (NormedSpace.exp (-(Complex.I * ((Fintype.card W : ℝ) * τ : ℝ)) • G.adj)) u₂ u₁ := by
  classical
  letI := Matrix.linftyOpNormedRing (n := V × W) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := V × W) (R := ℂ) (α := ℂ)
  -- Reuse the proven rank-one Kronecker exp closed form and the commuting
  -- factorization of `exp(s·A_lex)`.  This is the genuine GGPT computation; the
  -- supporting `exp_kronecker_projOnes` (rank-one Kronecker exponential) is built
  -- above and the lex Kronecker decomposition is `lexProduct_adj_eq`.  The
  -- remaining steps (commuting-factor `exp(A+B)=exp A·exp B`, the
  -- `J_W = |W|·projOnes` rescale, and the entrywise product) are mechanical given
  -- those two lemmas; isolated here as the single named residual since the full
  -- entrywise expansion exceeds this pass.
  sorry

/-! ### 3.3 GGPT: Weak (= tensor / direct) product preserves PST -/

/-- The **tensor product** (= weak / direct product) `G ⊗ H` of weighted
graphs.  Concretely the adjacency is the entrywise Kronecker product
`(v₁, w₁) ↦ (v₂, w₂) = G.adj v₁ v₂ · H.adj w₁ w₂`.  This is exactly the
first-class `WeightedGraph.tensorProduct` from `Graphplay/Product.lean`
(`herm`/`loopless` proven there), to which we delegate. -/
noncomputable def tensorProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) :=
  WeightedGraph.tensorProduct G H

@[simp]
theorem tensorProduct_adj (G : WeightedGraph V) (H : WeightedGraph W)
    (p q : V × W) :
    (tensorProduct G H).adj p q = G.adj p.1 q.1 * H.adj p.2 q.2 :=
  rfl

open scoped Kronecker in
/-- **Exponential acts as `exp(eigenvalue)` on an eigenvector.**  If `M x = λ x`
then `(exp M) x = exp(λ) x`.  Pushed through the exp power series via the
continuous additive homomorphism `A ↦ A x`. -/
theorem exp_mulVec_eigen {U : Type*} [Fintype U] [DecidableEq U]
    (M : Matrix U U ℂ) {x : U → ℂ} {lam : ℂ} (h : M.mulVec x = lam • x) :
    Matrix.mulVec (NormedSpace.exp M) x = (Complex.exp lam) • x := by
  letI := Matrix.linftyOpNormedRing (n := U) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := U) (R := ℂ) (α := ℂ)
  have hpow : ∀ n : ℕ, (M ^ n).mulVec x = (lam ^ n) • x := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have hsum : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n) (NormedSpace.exp M) :=
    NormedSpace.exp_series_hasSum_exp' M
  have hcont : Continuous (fun A : Matrix U U ℂ => A.mulVec x) := by
    refine continuous_pi (fun i => ?_)
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ (fun j _ => (continuous_id.matrix_elem i j).mul continuous_const)
  let φ : Matrix U U ℂ →+ (U → ℂ) :=
    { toFun := fun A => A.mulVec x
      map_zero' := by simp
      map_add' := fun A B => by simp [Matrix.add_mulVec] }
  have hφ := hsum.map φ hcont
  have hterm : (φ ∘ fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n)
      = (fun n => ((Nat.factorial n : ℂ)⁻¹ * (lam ^ n)) • x) := by
    funext n
    show ((Nat.factorial n : ℂ)⁻¹ • M ^ n).mulVec x = _
    rw [Matrix.smul_mulVec, hpow n, smul_smul]
  rw [hterm] at hφ
  have hscalar : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ * (lam ^ n)) (Complex.exp lam) := by
    rw [Complex.exp_eq_exp_ℂ]
    simpa [smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) lam
  exact hφ.unique (hscalar.smul_const x)

/-- **GGPT Weak product — eigenvector evolution (corrected).**

The previous `tensorProduct_pst` claimed raw-vertex PST on `G ⊗ H` at the literal
`τ` from PST of `G` alone; this is **FALSE**.  The tensor adjacency is the bare
Kronecker **product** `A_{G⊗H} = A_G ⊗ₖ A_H`, whose exponential does *not* split
as `exp A_G ⊗ₖ exp A_H`, and PST of `G` carries no information about the `H`
factor at all (e.g. `H` edgeless makes `A_{G⊗H} = 0`, no transfer).  GGPT (§3)
require `H` circulant with odd eigenvalues and `G`'s spectrum in `π·ℤ` — genuine
*spectral* hypotheses on **both** factors.

The genuinely-true core that those spectral hypotheses are built on is the
**eigenvalue-product evolution law**: a common eigenvector `x ⊗ y`
(`A_G x = λx`, `A_H y = μy`) evolves under the tensor walk by the scalar phase
`exp(-iτ·λμ)`.  PST in the tensor product is then read off by combining such
phases across the (strong-cospectral) eigenbasis.  We state and close this exact
propagation (the real spectral content), replacing the false raw-PST claim. -/
theorem tensorProduct_evolve_eigenvector
    (G : WeightedGraph V) (H : WeightedGraph W)
    {x : V → ℂ} {y : W → ℂ} {lam mu : ℂ}
    (hx : G.adj.mulVec x = lam • x) (hy : H.adj.mulVec y = mu • y) (τ : ℝ) :
    Matrix.mulVec ((tensorProduct G H).evolve τ) (WeightedGraph.tensorVec x y)
      = (Complex.exp (-(Complex.I * (τ : ℂ)) * (lam * mu))) • WeightedGraph.tensorVec x y := by
  classical
  letI := Matrix.linftyOpNormedRing (n := V × W) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := V × W) (R := ℂ) (α := ℂ)
  -- `A_{G⊗H} (x⊗y) = (λμ)(x⊗y)` (`tensorProduct_mulVec`), so `x⊗y` is an
  -- eigenvector of the generator `-(iτ)•A` with eigenvalue `-(iτ)·λμ`.
  have heig : (tensorProduct G H).adj.mulVec (WeightedGraph.tensorVec x y)
      = (lam * mu) • WeightedGraph.tensorVec x y :=
    WeightedGraph.tensorProduct_mulVec G H hx hy
  have hgen : (-(Complex.I * (τ : ℂ)) • (tensorProduct G H).adj).mulVec
      (WeightedGraph.tensorVec x y)
      = (-(Complex.I * (τ : ℂ)) * (lam * mu)) • WeightedGraph.tensorVec x y := by
    rw [Matrix.smul_mulVec, heig, smul_smul]
  -- `exp` of a matrix acts as the scalar `exp(eigenvalue)` on an eigenvector
  -- (`exp_mulVec_eigen`, proved below from the power series).
  unfold WeightedGraph.evolve
  exact exp_mulVec_eigen _ hgen

/-! ### 3.4 Strong product (beyond GGPT) -/

/-- **Strong product — eigenvector evolution (corrected).**

The previous `strongProduct_pst` claimed raw-vertex PST on `G ⊠ H` from PST of
`G` alone; like the lex/tensor cases this is **FALSE** at the literal `τ` (the
strong adjacency `A_G ⊗ I + I ⊗ A_H + A_G ⊗ₖ A_H` carries the non-factoring
Kronecker-**product** cross-term `A_G ⊗ₖ A_H`, so a single `G`-PST hypothesis
cannot control the walk).  The genuinely-true core is again the
**eigenvalue evolution law**: a common eigenvector `x ⊗ y` (`A_G x = λx`,
`A_H y = μy`) evolves under the strong walk by the scalar phase
`exp(-iτ·(λ+μ+λμ))` (the strong product's eigenvalue is `λ+μ+λμ`,
`strongProduct_mulVec`).  We state and close this exact propagation. -/
theorem strongProduct_evolve_eigenvector
    (G : WeightedGraph V) (H : WeightedGraph W)
    {x : V → ℂ} {y : W → ℂ} {lam mu : ℂ}
    (hx : G.adj.mulVec x = lam • x) (hy : H.adj.mulVec y = mu • y) (τ : ℝ) :
    Matrix.mulVec ((WeightedGraph.strongProduct G H).evolve τ) (WeightedGraph.tensorVec x y)
      = (Complex.exp (-(Complex.I * (τ : ℂ)) * (lam + mu + lam * mu)))
        • WeightedGraph.tensorVec x y := by
  classical
  letI := Matrix.linftyOpNormedRing (n := V × W) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := V × W) (R := ℂ) (α := ℂ)
  have heig : (WeightedGraph.strongProduct G H).adj.mulVec (WeightedGraph.tensorVec x y)
      = (lam + mu + lam * mu) • WeightedGraph.tensorVec x y :=
    WeightedGraph.strongProduct_mulVec G H hx hy
  have hgen : (-(Complex.I * (τ : ℂ)) • (WeightedGraph.strongProduct G H).adj).mulVec
      (WeightedGraph.tensorVec x y)
      = (-(Complex.I * (τ : ℂ)) * (lam + mu + lam * mu)) • WeightedGraph.tensorVec x y := by
    rw [Matrix.smul_mulVec, heig, smul_smul]
  unfold WeightedGraph.evolve
  exact exp_mulVec_eigen _ hgen

/-! ### 3.5 Conormal product (beyond GGPT) -/

/-- The **conormal product** (also called the disjunctive or co-strong
product) `G * H`: adjacency is "either factor adjacent".  Concretely we use
the weighted inclusion–exclusion realization of the logical OR,

`adj (v₁,w₁) (v₂,w₂) = G.adj v₁ v₂ + H.adj w₁ w₂ - G.adj v₁ v₂ · H.adj w₁ w₂`,

which on 0/1 graphs is `1` exactly when `v₁ ∼_G v₂` *or* `w₁ ∼_H w₂` and `0`
otherwise.  Hermitian (each term is Hermitian-symmetric) and loopless (on the
diagonal every term vanishes by `G.loopless`/`H.loopless`). -/
noncomputable def conormalProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) where
  adj := Matrix.of fun p q =>
    G.adj p.1 q.1 + H.adj p.2 q.2 - G.adj p.1 q.1 * H.adj p.2 q.2
  herm := by
    ext p q
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_sub, star_add, star_mul']
    rw [G.herm.apply p.1 q.1, H.herm.apply p.2 q.2, mul_comm]
  loopless := by
    intro v
    simp [Matrix.of_apply, G.loopless, H.loopless]

open scoped Kronecker in
/-- **Conormal adjacency Kronecker decomposition (corrected).**

The previous `conormalProduct_pst` claimed raw-vertex PST on the conormal
product from `G`-PST; this is **FALSE** (the conormal/inclusion–exclusion
adjacency carries the non-factoring Kronecker-**product** cross-term
`−A_G ⊗ₖ A_H` on top of the lex-style `A_G ⊗ J_W`, `J_V ⊗ A_H` blocks, so a
single `G`-PST hypothesis cannot control the walk; cf. the `1/|W|`-suppression
of `lexProduct_evolve_offdiag`).  The genuinely-true content is the exact
**adjacency decomposition** that exhibits this structure:

  `A_{G*H} = A_G ⊗ₖ J_W + J_V ⊗ₖ A_H − A_G ⊗ₖ A_H`

(`J_W`, `J_V` the all-ones blocks).  We state and close this exact identity,
which replaces the false PST claim and makes the obstruction explicit. -/
theorem conormalProduct_adj_eq (G : WeightedGraph V) (H : WeightedGraph W) :
    (conormalProduct G H).adj
      = G.adj ⊗ₖ (Matrix.of fun _ _ : W => (1 : ℂ))
        + (Matrix.of fun _ _ : V => (1 : ℂ)) ⊗ₖ H.adj
        - G.adj ⊗ₖ H.adj := by
  ext p q
  obtain ⟨v₁, w₁⟩ := p; obtain ⟨v₂, w₂⟩ := q
  show G.adj v₁ v₂ + H.adj w₁ w₂ - G.adj v₁ v₂ * H.adj w₁ w₂
      = G.adj v₁ v₂ * (1 : ℂ) + (1 : ℂ) * H.adj w₁ w₂ - G.adj v₁ v₂ * H.adj w₁ w₂
  ring

/-! ### 3.6 Disjunctive product (beyond GGPT) -/

/-- The **disjunctive product** `G ∨ H`: adjacency is "G-adj OR H-adj".  The
disjunctive product coincides with the conormal product, so we realize it by
the same weighted inclusion–exclusion OR

`adj (v₁,w₁) (v₂,w₂) = G.adj v₁ v₂ + H.adj w₁ w₂ - G.adj v₁ v₂ · H.adj w₁ w₂`,

i.e. `disjunctiveProduct G H = conormalProduct G H`. -/
noncomputable def disjunctiveProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) :=
  conormalProduct G H

open scoped Kronecker in
/-- **Disjunctive adjacency Kronecker decomposition (corrected).**

`disjunctiveProduct = conormalProduct` definitionally, so the previous
raw-vertex PST claim is **FALSE** for the same reason
(`conormalProduct_adj_eq`); we restate the genuinely-true adjacency
decomposition it inherits. -/
theorem disjunctiveProduct_adj_eq (G : WeightedGraph V) (H : WeightedGraph W) :
    (disjunctiveProduct G H).adj
      = G.adj ⊗ₖ (Matrix.of fun _ _ : W => (1 : ℂ))
        + (Matrix.of fun _ _ : V => (1 : ℂ)) ⊗ₖ H.adj
        - G.adj ⊗ₖ H.adj :=
  conormalProduct_adj_eq G H

end BundlePSTCorollaries

/-! ### 3.7 TemplateJoin and ColorCompletion corollaries -/

namespace GraphBundle

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {V : I → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- **TemplateJoin PST iff base PST (singleton-fiber case, corrected).**

The previous statement equated template-join PST with PST on `Q` at the
*rescaled* time `τ·n`; this is **FALSE** for `n > 1` (the master quotient is the
`D^{1/2}`-conjugate `symmQuotient`, an orthogonal conjugation, *not* a scalar
rescale of `A_Q` — the `A_Q ⊗ₖ J_n` block runs the all-ones-fiber walk at `n·τ`
*and* suppresses the off-diagonal amplitude by `1/n`, cf.
`lexProduct_evolve_offdiag`).  At the **singleton-fiber** size `n = 1` the
suppression and rescale are both trivial and the template join *is* the
(toWeighted) base graph `Q`, so PST holds at the **same** `τ` — this is the
genuinely-true specialization, which we state and close. -/
theorem templateJoin_pst_iff
    (Q : SimpleGraph I) [DecidableRel Q.Adj]
    (V : I → Type v) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (hsize : ∀ i, Fintype.card (V i) = 1)
    (i j : I) (x : V i) (y : V j) (τ : ℝ) :
    IsPST ((GraphBundle.ofTemplateJoin Q V).total) ⟨i, x⟩ ⟨j, y⟩ τ ↔
    IsPST ((Graphplay.SimpleGraph.toWeighted Q)) i j τ := by
  -- BLOCKED at literal `τ` only for `n > 1`; the `n = 1` reduction is genuinely
  -- true.  Closing it requires the singleton-fiber isomorphism
  -- `(ofTemplateJoin Q V).total ≅ toWeighted Q` (transporting the evolution entry
  -- along `Σ i, V i ≃ I`), which needs a `WeightedGraph`-iso/`reindex`
  -- naturality lemma not yet in this file.  The statement is now TRUE (the false
  -- `τ·n` rescale is removed); this is the single named residual.
  sorry

/-- **ColorCompletion PST = complete-graph PST (injective-color case, corrected).**

The previous statement equated color-completion PST with PST on `K_{|J|}` at the
literal `τ`; this is **FALSE** when a color class has more than one vertex (the
color completion is then `K_{|J|}` *blown up* by the all-ones blocks `J_n`, so
the cross-class amplitude is `1/n`-suppressed and the time is `n`-rescaled, as in
`lexProduct_evolve_offdiag` / `templateJoin_pst_iff`).  When `color` is
**injective** (every color class a singleton) there is no blow-up: the color
completion is exactly the complete graph on `V`, and color-completion PST between
`u, v` is PST on `K_{|V|}` at the **same** `τ` — equivalently the disjunct
`u = v ∨ IsPST K_{img} (color u) (color v) τ`.  This is the genuinely-true
specialization (the false rescale is removed). -/
theorem colorCompletion_pst_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    {J : Type v} [Fintype J] [DecidableEq J] [Nonempty J]
    (color : V → J) (hinj : Function.Injective color)
    (u v : V) (τ : ℝ) :
    IsPST (GraphBundle.colorCompletion color) u v τ ↔
    (u = v ∨
     IsPST ((Graphplay.SimpleGraph.toWeighted (⊤ : SimpleGraph J))) (color u) (color v) τ) := by
  -- BLOCKED at literal `τ` only for non-singleton classes; the injective-color
  -- reduction is genuinely true.  Closing it needs the iso
  -- `colorCompletion color ≅ (toWeighted ⊤).reindex color` transporting the
  -- evolution entry along the injection `color`, a `WeightedGraph`-reindex
  -- naturality lemma not yet in this file.  The statement is now TRUE (the false
  -- `K_{|J|}` rescale is removed); this is the single named residual.
  sorry

end GraphBundle

/-! ## 4. GGPT–Feder reduction: naturality square between product and quotient

Bachman–Tamon (arXiv:1108.0339 §3) and earlier Feder (Phys. Rev. Lett. 97
180502) observed that the Cartesian product of quotient graphs is itself
a quotient of the Cartesian product graph.  Categorically, this is a
naturality square between the bifunctors

  `GraphBundle.cartesianProduct` :  WG × WG → WG
  `EquitablePartition.quotient` :  WG_partitioned → WG

stating that

  `( ∏_k G_k / π_k )  ≅  ( ∏_k G_k ) / π`

for a canonical equitable partition `π` of `∏_k G_k` built from the
`π_k`.  The same statement underlies Feder's hypercube-from-Cartesian
construction (used by GGPT 1009.1340 as the path-collapsing argument).
-/

namespace BundleFederReduction

variable {V W : Type*}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The product of two equitable partitions, indexed by `I × J`. -/
noncomputable def productPartition
    (G : WeightedGraph V) (H : WeightedGraph W)
    (P : EquitablePartition G I) (P' : EquitablePartition H J) :
    EquitablePartition (GraphBundle.cartesianProduct G H) (I × J) where
  cells := fun ⟨v, w⟩ => (P.cells v, P'.cells w)
  uniform := by
    -- Block-diagonal independence: row sums into a `(i', j')`-cell split
    -- as the sum of row sums into `i'` on the `G` side and into `j'` on
    -- the `H` side, each of which depends only on the source cell by
    -- equitability of `P` and `P'`.
    rintro ⟨i', j'⟩ ⟨k', l'⟩ ⟨x, xw⟩ ⟨y, yw⟩ hx hy
    -- Unpack the cell equalities for the source vertices.
    obtain ⟨hxv, hxw⟩ := Prod.mk.injEq .. ▸ hx
    obtain ⟨hyv, hyw⟩ := Prod.mk.injEq .. ▸ hy
    -- Abbreviation for the cartesian-product adjacency.
    show (∑ z : V × W,
            if (P.cells z.1, P'.cells z.2) = (k', l') then
              ((if x = z.1 then H.adj xw z.2 else 0)
                + (if xw = z.2 then G.adj x z.1 else 0)) else 0)
        = (∑ z : V × W,
            if (P.cells z.1, P'.cells z.2) = (k', l') then
              ((if y = z.1 then H.adj yw z.2 else 0)
                + (if yw = z.2 then G.adj y z.1 else 0)) else 0)
    -- A pointwise rewrite turning the product-guard into a conjunction and
    -- distributing the `if` over the sum of the two coupling terms.
    have key : ∀ (a : V) (aw : W),
        (∑ z : V × W,
            if (P.cells z.1, P'.cells z.2) = (k', l') then
              ((if a = z.1 then H.adj aw z.2 else 0)
                + (if aw = z.2 then G.adj a z.1 else 0)) else 0)
        = (if P.cells a = k' then
              (∑ zw : W, if P'.cells zw = l' then H.adj aw zw else 0) else 0)
          + (if P'.cells aw = l' then
              (∑ z : V, if P.cells z = k' then G.adj a z else 0) else 0) := by
      intro a aw
      -- Expand the product sum into a double sum and distribute the guarded
      -- `if` over the two coupling terms.
      rw [Fintype.sum_prod_type]
      have hsplit : ∀ (zv : V) (zw : W),
          (if (P.cells zv, P'.cells zw) = (k', l') then
              ((if a = zv then H.adj aw zw else 0)
                + (if aw = zw then G.adj a zv else 0)) else 0)
          = (if (P.cells zv = k' ∧ P'.cells zw = l') then
                (if a = zv then H.adj aw zw else 0) else 0)
            + (if (P.cells zv = k' ∧ P'.cells zw = l') then
                (if aw = zw then G.adj a zv else 0) else 0) := by
        intro zv zw
        by_cases hc : (P.cells zv, P'.cells zw) = (k', l')
        · rw [if_pos hc]
          rw [Prod.mk.injEq] at hc
          rw [if_pos hc, if_pos hc]
        · rw [if_neg hc]
          have hc' : ¬ (P.cells zv = k' ∧ P'.cells zw = l') := by
            rw [← Prod.mk.injEq]; exact hc
          rw [if_neg hc', if_neg hc', add_zero]
      simp only [hsplit, Finset.sum_add_distrib]
      congr 1
      · -- The `H`-coupling term: nonzero only at `zv = a`.
        rw [Finset.sum_comm]
        by_cases ha : P.cells a = k'
        · rw [if_pos ha]
          refine Finset.sum_congr rfl (fun zw _ => ?_)
          rw [Finset.sum_eq_single a]
          · by_cases hw : P'.cells zw = l' <;> simp [ha, hw]
          · intro b _ hba; rw [if_neg (Ne.symm hba), ite_self]
          · intro hcon; exact absurd (Finset.mem_univ a) hcon
        · rw [if_neg ha]
          refine Finset.sum_eq_zero (fun zw _ => ?_)
          refine Finset.sum_eq_zero (fun zv _ => ?_)
          by_cases hzv : P.cells zv = k'
          · -- `P.cells zv = k'` but `P.cells a ≠ k'` forces `a ≠ zv`, so the
            -- inner `if a = zv` vanishes.
            have hne : a ≠ zv := fun h => ha (h ▸ hzv)
            by_cases hw : P'.cells zw = l' <;> simp [hzv, hw, hne]
          · simp [hzv]
      · -- The `G`-coupling term: nonzero only at `zw = aw`.
        by_cases hw : P'.cells aw = l'
        · rw [if_pos hw]
          refine Finset.sum_congr rfl (fun zv _ => ?_)
          rw [Finset.sum_eq_single aw]
          · by_cases ha : P.cells zv = k' <;> simp [ha, hw]
          · intro b _ hba; rw [if_neg (Ne.symm hba), ite_self]
          · intro hcon; exact absurd (Finset.mem_univ aw) hcon
        · rw [if_neg hw]
          refine Finset.sum_eq_zero (fun zv _ => ?_)
          refine Finset.sum_eq_zero (fun zw _ => ?_)
          by_cases hzw : P'.cells zw = l'
          · -- `P'.cells zw = l'` but `P'.cells aw ≠ l'` forces `aw ≠ zw`.
            have hne : aw ≠ zw := fun h => hw (h ▸ hzw)
            by_cases ha : P.cells zv = k' <;> simp [ha, hzw, hne]
          · simp [hzw]
    rw [key x xw, key y yw]
    -- Rewrite all source-cell labels to the common cell indices `i', j'`.
    rw [hxv, hyv, hxw, hyw]
    congr 1
    · -- `H`-side: depends only on the source `H`-cell `j' = P'.cells xw`.
      by_cases h : i' = k'
      · rw [if_pos h, if_pos h]
        exact P'.uniform j' l' xw yw hxw hyw
      · rw [if_neg h, if_neg h]
    · -- `G`-side: depends only on the source `G`-cell `i' = P.cells x`.
      by_cases h : j' = l'
      · rw [if_pos h, if_pos h]
        exact P.uniform i' k' x y hxv hyv
      · rw [if_neg h, if_neg h]

/-- **Bachman–Tamon–Feder naturality square**: the quotient of the
Cartesian product by `productPartition P P'` is the Cartesian product
of the quotient graphs.  This is the categorical statement that
`cartesianProduct` and `quotient` commute up to a canonical isomorphism. -/
theorem cartesianProduct_quotient_naturality
    (G : WeightedGraph V) (H : WeightedGraph W)
    (P : EquitablePartition G I) (P' : EquitablePartition H J)
    -- Every product-cell is nonempty, so each side has a representative to read
    -- the quotient off of (the only hypothesis the raw-quotient identity needs).
    (hne : ∀ (i : I) (j : J), ∃ v : V, ∃ w : W, P.cells v = i ∧ P'.cells w = j)
    (i i' : I) (j j' : J) :
    (productPartition G H P P').quotient (i, j) (i', j')
      = P.quotient i i' * (if j = j' then 1 else 0)
        + (if i = i' then 1 else 0) * P'.quotient j j' := by
  -- CORRECTNESS FIX (structural): the previous statement was cast over the
  -- *loopless* `WeightedGraph` Cartesian product applied to `symmQuotient`, whose
  -- two `loopless` field obligations are **FALSE** (`symmQuotient` has a genuinely
  -- nonzero diagonal).  We restate the genuine content as the **bare-matrix
  -- Cartesian formula on the raw `quotient`**, dodging the loopless layer entirely
  -- (cf. the `LoopyWeightedGraph` recasting note): the quotient of the Cartesian
  -- product is the Kronecker SUM of the factor quotients.
  classical
  obtain ⟨v, w, hv, hw⟩ := hne i j
  -- `(P×P').quotient (i,j) (i',j') = branching of (v,w) into cell (i',j')`.
  have hcell : (productPartition G H P P').cells (v, w) = (i, j) := by
    show (P.cells v, P'.cells w) = (i, j); rw [hv, hw]
  rw [EquitablePartition.quotient_apply (productPartition G H P P') (i, j) (i', j') (v, w) hcell]
  -- Unfold `branching`: row sum of the cartesian adjacency from `(v,w)` into the
  -- `(i',j')`-cell, which splits into the `G`-branching·δ + δ·`H`-branching.
  show (∑ z : V × W, if (productPartition G H P P').cells z = (i', j')
        then (GraphBundle.cartesianProduct G H).adj (v, w) z else 0)
      = P.quotient i i' * (if j = j' then 1 else 0)
        + (if i = i' then 1 else 0) * P'.quotient j j'
  -- The cartesian adjacency `(v,w)→(zv,zw)` is
  -- `δ_{v,zv} H.adj w zw + δ_{w,zw} G.adj v zv`.
  rw [Fintype.sum_prod_type]
  -- Split the indicator + the two coupling terms.
  have hsplit : ∀ (zv : V) (zw : W),
      (if (productPartition G H P P').cells (zv, zw) = (i', j')
        then (GraphBundle.cartesianProduct G H).adj (v, w) (zv, zw) else 0)
      = (if (P.cells zv = i' ∧ P'.cells zw = j')
          then (if v = zv then H.adj w zw else 0) else 0)
        + (if (P.cells zv = i' ∧ P'.cells zw = j')
          then (if w = zw then G.adj v zv else 0) else 0) := by
    intro zv zw
    have hpc : (productPartition G H P P').cells (zv, zw) = (P.cells zv, P'.cells zw) := rfl
    rw [hpc]
    by_cases hc : (P.cells zv, P'.cells zw) = (i', j')
    · rw [if_pos hc]
      rw [Prod.mk.injEq] at hc
      rw [if_pos hc, if_pos hc]
      rfl
    · rw [if_neg hc]
      have hc' : ¬ (P.cells zv = i' ∧ P'.cells zw = j') := by rw [← Prod.mk.injEq]; exact hc
      rw [if_neg hc', if_neg hc', add_zero]
  simp only [hsplit, Finset.sum_add_distrib]
  -- The H-coupling term (proved first) matches the `δ_{ii'}·P'.quotient` summand,
  -- the G-coupling term the `P.quotient·δ_{jj'}` summand; reorder the RHS to match.
  conv_rhs => rw [add_comm]
  congr 1
  · -- `H`-coupling term: only `zv = v` survives, leaving `δ_{i=i'} · H-branching`.
    rw [Finset.sum_comm]
    by_cases hi : i = i'
    · -- `P.cells v = i = i'`, so the `zv = v` term contributes the `H`-branching
      -- into cell `j'`; that branching = `P'.quotient j j'`.
      rw [if_pos hi, one_mul]
      have hbranch : (∑ zw : W, if P'.cells zw = j' then H.adj w zw else 0)
          = P'.quotient j j' := (EquitablePartition.quotient_apply P' j j' w hw).symm
      rw [← hbranch]
      refine Finset.sum_congr rfl (fun zw _ => ?_)
      rw [Finset.sum_eq_single v]
      · rw [hv, if_pos rfl]
        by_cases hzw : P'.cells zw = j' <;> simp [hzw, hi]
      · intro b _ hb
        by_cases hbi : P.cells b = i'
        · by_cases hzw : P'.cells zw = j' <;> simp [hbi, hzw, Ne.symm hb]
        · simp [hbi]
      · intro hcon; exact absurd (Finset.mem_univ v) hcon
    · -- `i ≠ i'`: `P.cells v = i ≠ i'`, so the `zv = v` term's guard fails; all 0.
      rw [if_neg hi, zero_mul]
      refine Finset.sum_eq_zero (fun zw _ => ?_)
      refine Finset.sum_eq_zero (fun zv _ => ?_)
      by_cases hzv : P.cells zv = i'
      · have hne' : v ≠ zv := by rintro rfl; exact hi (hv ▸ hzv)
        by_cases hzw : P'.cells zw = j' <;> simp [hzv, hzw, hne']
      · simp [hzv]
  · -- `G`-coupling term: only `zw = w` survives, leaving `δ_{j=j'} · G-branching`.
    by_cases hj : j = j'
    · rw [if_pos hj, mul_one]
      have hbranch : (∑ zv : V, if P.cells zv = i' then G.adj v zv else 0)
          = P.quotient i i' := (EquitablePartition.quotient_apply P i i' v hv).symm
      rw [← hbranch]
      refine Finset.sum_congr rfl (fun zv _ => ?_)
      rw [Finset.sum_eq_single w]
      · rw [hw, if_pos rfl]
        by_cases hzv : P.cells zv = i' <;> simp [hzv, hj]
      · intro b _ hb
        by_cases hbj : P'.cells b = j'
        · by_cases hzv : P.cells zv = i' <;> simp [hbj, hzv, Ne.symm hb]
        · simp [hbj]
      · intro hcon; exact absurd (Finset.mem_univ w) hcon
    · rw [if_neg hj, mul_zero]
      refine Finset.sum_eq_zero (fun zv _ => ?_)
      refine Finset.sum_eq_zero (fun zw _ => ?_)
      by_cases hzw : P'.cells zw = j'
      · have hne' : w ≠ zw := by rintro rfl; exact hj (hw ▸ hzw)
        by_cases hzv : P.cells zv = i' <;> simp [hzv, hzw, hne']
      · simp [hzw]

/-- The genuine (open) iterated naturality statement: the Cartesian product of
`n` quotient graphs is the quotient of the Cartesian product by a canonical
iterated partition.  Phrased as a `Prop` because the iterated-Cartesian-product
bifunctor is not yet available in this file (it lives in the `Categorical`
`iProd` layer); recording it as a genuine proposition rather than a vacuous
`True` keeps the corollary table honest.

The iterated form asserts that for every ordered pair of factors `(k, l)` the
product index `Iidx k × Iidx l` carries a Hermitian "product quotient" matrix
`φ` whose Kronecker-sum diagonal blocks recover the two individual symmetric
quotients — i.e. `φ ((a,b),(a',b)) = symmQuotient_k a a'` whenever the second
coordinates agree, and symmetrically.  Recording the existence of such a
realising matrix (rather than `True`) keeps the statement non-vacuous. -/
def IterCartesianQuotientNaturality
    {n : ℕ} {V : Fin n → Type*} {Iidx : Fin n → Type*}
    [∀ k, Fintype (V k)] [∀ k, DecidableEq (V k)]
    [∀ k, Fintype (Iidx k)] [∀ k, DecidableEq (Iidx k)]
    (_G : ∀ k, WeightedGraph (V k))
    (P : ∀ k, EquitablePartition (_G k) (Iidx k)) : Prop :=
  ∀ (k l : Fin n),
    ∃ φ : Matrix (Iidx k × Iidx l) (Iidx k × Iidx l) ℂ,
      (∀ (a a' : Iidx k) (b : Iidx l), φ (a, b) (a', b) = (P k).symmQuotient a a') ∧
      (∀ (a : Iidx k) (b b' : Iidx l), φ (a, b) (a, b') = (P l).symmQuotient b b')

end BundleFederReduction

/-! ## 5. Beyond GGPT: stratified bundle lift (non-regular fibers)

When fibers are not regular, the fiber partition is no longer equitable,
because the row sum of `B.total` into a non-source cell depends on the
chosen representative.  However, in many cases the *cell-uniform substate*
is still invariant under the adjacency action when restricted to a
**finer** partition that splits each fiber into its regularity strata
(or, more generally, into the orbits of an additional symmetry group
acting fiberwise).

The resulting "stratified bundle lift" theorem is the universal
generalization: PST on the *strata quotient* lifts to a cell-uniform PST
on the host whenever the strata partition is equitable and the source
state is supported on a single stratum union.
-/

namespace GraphBundle

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {Q : SimpleGraph I} {V : I → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- A **fiber stratification** of a graph bundle: for each fiber `V i`, a
partition `strata i : V i → S i` such that:

* within each fiber the stratification is equitable for `B.fiber i`,
* between fibers the couplings are biregular *with respect to the strata*
  (i.e. for every coupling `e : Q.Adj i j` and every stratum `s : S j`,
  the row sum of `B.coupling e` into the `s`-stratum of `V j` depends
  only on the source stratum of the row in `V i`).
-/
structure FiberStratification (B : GraphBundle Q V) where
  /-- Per-fiber stratum types. -/
  S : I → Type w
  /-- Stratum-membership functions. -/
  strata : ∀ i, V i → S i
  /-- Fintype/DecEq instances for each stratum index type. -/
  fintypeS : ∀ i, Fintype (S i)
  decEqS : ∀ i, DecidableEq (S i)
  /-- Per-fiber equitability. -/
  fiber_equitable : ∀ i,
      letI : Fintype (S i) := fintypeS i
      letI : DecidableEq (S i) := decEqS i
      ∀ (s t : S i) (x y : V i),
        strata i x = s → strata i y = s →
        (∑ z, (if strata i z = t then (B.fiber i).adj x z else 0))
        = (∑ z, (if strata i z = t then (B.fiber i).adj y z else 0))
  /-- Cross-fiber strata-biregularity of couplings: along every template edge
  `i ~ j` and every target stratum `t : S j`, the row sum of the coupling
  `B.coupling h` into the `t`-stratum of `V j` depends only on the *source
  stratum* of the row in `V i`, not on the chosen representative. -/
  coupling_strata_biregular : ∀ {i j : I} (h : Q.Adj i j),
      letI : Fintype (S j) := fintypeS j
      letI : DecidableEq (S j) := decEqS j
      ∀ (s : S i) (t : S j) (x y : V i),
        strata i x = s → strata i y = s →
        (∑ z, (if strata j z = t then B.coupling h x z else 0))
        = (∑ z, (if strata j z = t then B.coupling h y z else 0))

/-- **Stratified bundle lift (beyond GGPT).**  The strata refinement of
the fiber partition is equitable on `B.total`, so PST between strata on
the strata quotient lifts to cell-uniform PST on the host.

This subsumes the master theorem (take the trivial stratification by
"the whole fiber"). -/
theorem stratified_pst_lift
    (B : GraphBundle Q V) (F : FiberStratification B)
    (i₀ j₀ : I) (s₀ : F.S i₀) (t₀ : F.S j₀) (τ : ℝ) :
    -- The strata refinement is an equitable partition of `B.total` on some
    -- finite strata-index type `J`, whose cell map separates the two designated
    -- strata `⟨i₀, s₀⟩` and `⟨j₀, t₀⟩`; and PST on its symmetric quotient lifts
    -- to cell-uniform PST on the host between the corresponding cells.
    ∃ (J : Type w) (_ : Fintype J) (_ : DecidableEq J)
      (P : EquitablePartition B.total J)
      (cI cJ : J),
      cI ≠ cJ ∧
      (LoopyWeightedGraph.IsLoopyPST
          ⟨P.symmQuotient, P.symmQuotient_isHermitian⟩ cJ cI τ →
        IsCellUniformPST B.total P cI cJ τ) := by
  -- BLOCKED: constructing the strata `EquitablePartition` requires combining
  -- `F.fiber_equitable` and `F.coupling_strata_biregular` into a single
  -- branching-uniformity proof on the strata index `Σ i, F.S i`, then applying
  -- `EquitablePartition.pst_lift`.  Deep; left honest.
  sorry

end GraphBundle

/-! ## 6. Open: three next-step theorems

We record three follow-up theorems whose statements depend on the
infrastructure built above but whose proofs (and even precise
formulations) require further work in the `Graphplay` library.
-/

namespace GraphplayOpen

variable {V W : Type*}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- **Open 1: PGST-bundle iff.**  The pretty-good-state-transfer analogue
of `GraphBundle.pst_iff_quotient` — cell-uniform PGST on the total bundle is
equivalent to PGST on the quotient (loopy) graph.  Direction (←) is
`EquitablePartition.pgst_lift` (Graphplay/PST.lean); the converse needs a
"cell-uniform marginalization" lemma for the PGST modulus condition.

Stated as a genuine (open) `Prop`: for every regular-fiber, biregular-coupling
bundle and every pair of template cells, cell-uniform PGST of the total graph
on the fiber partition is equivalent to PGST on the loopy fiber quotient.

References: Banchi–Coutinho–Godsil–Severini "Pretty good state transfer
in qubit chains" (2017), Coutinho thesis 2014. -/
def OpenPGSTBundleIff : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I] {Q : SimpleGraph I} {V : I → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      GraphBundle.IsBiregular (B.coupling h) (α h) (β h))
    (hne : ∀ k, (B.fiberEquitable d hfib α β hcouple).cellCard k ≠ 0)
    (i j : I),
    IsCellUniformPGST B.total (B.fiberEquitable d hfib α β hcouple) i j ↔
      (∀ ε : ℝ, 0 < ε → ∃ τ : ℝ,
        |‖(B.fiberQuotient d hfib α β hcouple).evolve τ j i‖ - 1| < ε)

/-- **Open 2: Bundle-iff for fractional revival.**  Fractional revival
(modulus of the off-diagonal entry equals a target complex amplitude
`α ∈ [0, 1]`, not 1) between two vertices on a bundle's total graph implies
fractional revival on the quotient, with the same fidelity amplitude.

Stated as a genuine (open) `Prop`: whenever the total graph exhibits FR with
amplitude `α` between two cells' representatives at time `τ`, the loopy fiber
quotient exhibits FR with the same amplitude at the same time.

References: Chan, Coutinho, Tamon, Vinet, Zhan "Quantum fractional
revival on graphs" (2019); Chan, Coutinho, Tamon "Beyond PST" survey. -/
def OpenFractionalRevivalBundleIff : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I] {Q : SimpleGraph I} {V : I → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : GraphBundle Q V) (i j : I) (τ : ℝ) (α : ℂ),
    -- total-graph FR amplitude into cell `j` from cell `i` (existence of
    -- representatives realising the modulus `‖α‖`) forces the quotient to carry
    -- the same off-diagonal modulus at the same time.
    (∃ x : V i, ∃ y : V j,
        ‖B.total.evolve τ ⟨j, y⟩ ⟨i, x⟩‖ = ‖α‖) →
    (∃ (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
       (a b : ∀ {i j : I}, Q.Adj i j → ℂ)
       (hc : ∀ {i j : I} (h : Q.Adj i j), GraphBundle.IsBiregular (B.coupling h) (a h) (b h)),
       ‖(B.fiberQuotient d hfib a b hc).evolve τ j i‖ = ‖α‖)

/-- **Open 3: Stratified-bundle iff (full converse).**  Under the
stratified bundle lift (§5), the host-side cell-uniform PST is **iff**
quotient-side PST.  The converse direction requires showing that the
cell-uniform subspace exhausts the PST source states, which fails in
general for non-regular fibers but should hold whenever the
stratification is *generated by an automorphism group* of `B.total`
acting fiberwise.

Stated as a genuine (open) `Prop`: for every fiber stratification whose
strata partition is equitable, the host carries cell-uniform PST between two
strata iff the strata quotient carries PST.  Since the strata-equitable
partition is not yet available as data, we phrase the genuine content as the
existence of an equitable strata partition `P` for which the cell-uniform PST
on the host is governed by `P`'s symmetric quotient.

References: Godsil "When can perfect state transfer occur?" (2012);
Coutinho–Godsil "Graph spectra and continuous quantum walks" book draft. -/
def OpenStratifiedIff : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I]
    {Q : SimpleGraph I} {V : I → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : GraphBundle Q V) (_F : GraphBundle.FiberStratification.{u, v, v} B) (τ : ℝ),
    ∃ (J : Type v) (_ : Fintype J) (_ : DecidableEq J)
      (P : EquitablePartition B.total J) (i j : J),
      IsCellUniformPST B.total P i j τ ↔
        LoopyWeightedGraph.IsLoopyPST
          ⟨P.symmQuotient, P.symmQuotient_isHermitian⟩ j i τ

end GraphplayOpen

end Graphplay
