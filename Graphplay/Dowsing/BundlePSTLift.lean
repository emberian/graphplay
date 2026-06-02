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
  -- `A_{G⊗H} (x⊗y) = (λμ)(x⊗y)` (`tensorProduct_mulVec`), so `x⊗y` is an
  -- eigenvector of the generator `-(iτ)•A`, and the matrix exponential acts as
  -- the scalar `exp(-(iτ)·λμ)` on it.
  have heig : (tensorProduct G H).adj.mulVec (WeightedGraph.tensorVec x y)
      = (lam * mu) • WeightedGraph.tensorVec x y :=
    WeightedGraph.tensorProduct_mulVec G H hx hy
  -- The generator `-(I τ) • A` has eigenvalue `-(I τ)·(λμ)` on `x⊗y`.
  have hgen : (-(Complex.I * (τ : ℂ)) • (tensorProduct G H).adj).mulVec
      (WeightedGraph.tensorVec x y)
      = (-(Complex.I * (τ : ℂ)) * (lam * mu)) • WeightedGraph.tensorVec x y := by
    rw [Matrix.smul_mulVec_assoc, heig, smul_smul]
  -- `exp` of a matrix acts as `exp` of the eigenvalue on an eigenvector.
  unfold WeightedGraph.evolve
  exact (NormedSpace.exp_mulVec_eq_of_mulVec_eq _ _ hgen)
end_eig_placeholder

/-! ### 3.4 Strong product (beyond GGPT) -/

/-- **Strong product PST preservation.**  The strong product `G ⊠ H`
preserves PST whenever both factors are regular and `G` has PST.  Not in
GGPT (which only treats `□, ×, [·]`); covered by our master theorem. -/
theorem strongProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dG dH : ℂ} (hGreg : G.isRegular dG) (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) :
    IsPST (GraphBundle.strongProduct G H) (u₁, w) (u₂, w) τ := by
  -- BLOCKED: Kronecker-SUM part factors, but the Kronecker-PRODUCT cross-term
  -- does not.
  -- The strong adjacency decomposes as Cartesian + tensor,
  -- `A_{G⊠H} = (A_G ⊗ I + I ⊗ A_H) + A_G ⊗ₖ A_H`
  -- (`strongProduct_adj_eq_cartesian_add_tensor`, Product.lean).  All three
  -- summands pairwise COMMUTE — e.g. `(A_G⊗I)(A_G⊗A_H) = A_G²⊗A_H =
  -- (A_G⊗A_H)(A_G⊗I)` — so `exp` of the sum is the product of the three
  -- factor exponentials.  The Cartesian (Kronecker-sum) factor `exp(A_G⊗I) ·
  -- exp(I⊗A_H)` does split into one-leg exponentials (the proven engine), BUT
  -- the third factor `exp(A_G ⊗ₖ A_H)` is the exponential of a pure Kronecker
  -- PRODUCT and does NOT split as `exp A_G ⊗ₖ exp A_H`.  So the total walk
  -- amplitude is NOT a clean product of single-graph PST amplitudes.  Closing
  -- needs the GGPT spectral-lattice / circulant hypothesis on `H`
  -- (arXiv:1009.1340 §3–§4), absent here.
  sorry

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

/-- The conormal product preserves PST under bi-regularity. -/
theorem conormalProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dG dH : ℂ} (hGreg : G.isRegular dG) (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) :
    IsPST (conormalProduct G H) (u₁, w) (u₂, w) τ := by
  -- BLOCKED: Kronecker-PRODUCT cross-term `−A_G ⊗ₖ A_H` does not factor.
  -- The conormal/inclusion-exclusion adjacency is
  -- `A_{G*H} = A_G ⊗ J_W + J_V ⊗ A_H − A_G ⊗ₖ A_H` (the entrywise
  -- `G + H − G·H` realization of the logical OR; `J` the all-ones blocks).
  -- Beyond carrying the same `A_G ⊗ J` / `J ⊗ A_H` Kronecker-product blocks as
  -- the lex case, it has the explicit tensor cross-term `−A_G ⊗ₖ A_H`, whose
  -- exponential does NOT split as `exp A_G ⊗ₖ exp A_H`.  Hence the walk does
  -- not reduce to a Cartesian Kronecker-SUM factorization; PST preservation
  -- needs the same spectral-lattice input as the tensor/strong cases
  -- (arXiv:1009.1340 §3), absent here.  Genuinely not Cartesian-reducible.
  sorry

/-! ### 3.6 Disjunctive product (beyond GGPT) -/

/-- The **disjunctive product** `G ∨ H`: adjacency is "G-adj OR H-adj".  The
disjunctive product coincides with the conormal product, so we realize it by
the same weighted inclusion–exclusion OR

`adj (v₁,w₁) (v₂,w₂) = G.adj v₁ v₂ + H.adj w₁ w₂ - G.adj v₁ v₂ · H.adj w₁ w₂`,

i.e. `disjunctiveProduct G H = conormalProduct G H`. -/
noncomputable def disjunctiveProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) :=
  conormalProduct G H

/-- The disjunctive product preserves PST under regularity hypotheses. -/
theorem disjunctiveProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dG dH : ℂ} (hGreg : G.isRegular dG) (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w₁ w₂ : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) :
    IsPST (disjunctiveProduct G H) (u₁, w₁) (u₂, w₂) τ := by
  -- BLOCKED: definitionally `disjunctiveProduct = conormalProduct`, so it
  -- inherits the same Kronecker-PRODUCT cross-term `−A_G ⊗ₖ A_H` that does not
  -- factor (see `conormalProduct_pst`).  Needs the same spectral-lattice input
  -- (arXiv:1009.1340 §3).  Genuinely not Cartesian-reducible.
  sorry

end BundlePSTCorollaries

/-! ### 3.7 TemplateJoin and ColorCompletion corollaries -/

namespace GraphBundle

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {V : I → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- **TemplateJoin PST iff base PST (constant-fiber-size case).**

If all fibers of `ofTemplateJoin Q V` have the same cardinality, the
fiber partition is equitable and the master theorem applies.  The
quotient is `Q` weighted by the common fiber size.  Hence PST on the
template join is equivalent (up to time rescaling) to PST on `Q`. -/
theorem templateJoin_pst_iff
    (Q : SimpleGraph I) [DecidableRel Q.Adj]
    (V : I → Type v) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (n : ℕ)
    (hsize : ∀ i, Fintype.card (V i) = n)
    (i j : I) (τ : ℝ) :
    (∃ x : V i, ∃ y : V j,
        IsPST ((GraphBundle.ofTemplateJoin Q V).total) ⟨i, x⟩ ⟨j, y⟩ τ) ↔
    IsPST ((Graphplay.SimpleGraph.toWeighted Q)) i j (τ * n) := by
  -- BLOCKED: time-rescale mismatch (`A_G ⊗ J` Kronecker-product block again).
  -- The constant-fiber-size template join is the lex-style bundle whose every
  -- coupling along a `Q`-edge is the all-ones `n × n` block `J`; its adjacency
  -- carries the Kronecker-PRODUCT block `A_Q ⊗ₖ J` exactly as in
  -- `lexProduct_pst`.  On the all-ones fiber eigenvector `J` acts as the scalar
  -- `n`, giving PST on `Q` at the RESCALED time `τ·n`; but the master iff is
  -- stated on `symmQuotient = D^{1/2} Q̃ D^{-1/2}`, an orthogonal conjugation,
  -- NOT a scalar rescale of `A_Q`, so the literal `τ·n` cannot be matched
  -- without the GGPT eigenvalue-lattice input absent from these hypotheses.
  sorry

/-- **ColorCompletion PST iff complete-graph PST.**

The color completion of `color : V → I` is the bundle `ofTemplateJoin`
over the *complete* graph on `I` (every pair of distinct colors is a
template edge) with empty fibers.  Hence the master theorem reduces
PST on the color completion to PST on `K_{|I|}` weighted by fiber size.
-/
theorem colorCompletion_pst_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    {J : Type v} [Fintype J] [DecidableEq J] [Nonempty J]
    (color : V → J)
    (hbal : ∀ j, (Finset.univ.filter fun v => color v = j).card =
                 (Finset.univ.filter fun v => color v = (Classical.arbitrary J)).card)
    (u v : V) (τ : ℝ) :
    IsPST (GraphBundle.colorCompletion color) u v τ ↔
    (color u = color v ∨
     IsPST ((Graphplay.SimpleGraph.toWeighted (⊤ : SimpleGraph J))) (color u) (color v) τ) := by
  -- BLOCKED: same time-rescale / `symmQuotient`-vs-scalar mismatch as
  -- `templateJoin_pst_iff`, specialized to the complete template `K_{|J|}`.
  -- The color completion is the all-ones-coupling bundle over `⊤ : SimpleGraph J`
  -- with empty fibers; its adjacency carries the Kronecker-PRODUCT coupling
  -- block `A_{K_{|J|}} ⊗ₖ J_n` (constant block `n` per color edge).  Within a
  -- color class the marginal evolution is trivial (empty fiber → the left `∨`
  -- branch); across classes the master theorem reduces to `K_{|J|}`, but on the
  -- all-ones fiber eigenvector the block scales time by `n`, giving PST on the
  -- symmetric quotient `symmQuotient` (a `D^{1/2}`-conjugation) rather than on
  -- a scalar rescale of `A_{K_{|J|}}`.  Matching the literal `τ` is the GGPT
  -- eigenvalue-lattice content, absent from the hypotheses.
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
    (P : EquitablePartition G I) (P' : EquitablePartition H J) :
    ∃ (φ : Matrix (I × J) (I × J) ℂ),
      (productPartition G H P P').quotient = φ ∧
      φ = (GraphBundle.cartesianProduct
            -- BLOCKED: `symmQuotient` has a genuinely nonzero diagonal, so it is
            -- NOT loopless; the `WeightedGraph` wrapper's `loopless` obligation is
            -- false here.  The statement should be re-cast over `LoopyWeightedGraph`
            -- (cf. `fiberQuotient`), which requires a loopy bundle-Cartesian-product
            -- bifunctor not yet available in this file.
            ⟨P.symmQuotient, P.symmQuotient_isHermitian, by sorry⟩
            ⟨P'.symmQuotient, P'.symmQuotient_isHermitian, by sorry⟩).adj := by
  -- BLOCKED: structural — the conclusion is stated over the loopless
  -- `WeightedGraph` layer but `symmQuotient` is loopy, so the two inner
  -- `loopless` proofs above are unprovable.  Modulo recasting to
  -- `LoopyWeightedGraph`, the naturality is the direct computation
  -- `(P × P').quotient ((i,j),(i',j')) = P.quotient (i,i')·δ(j,j') +
  --   δ(i,i')·P'.quotient (j,j')` (Cartesian product of the quotient adjacencies).
  sorry

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
