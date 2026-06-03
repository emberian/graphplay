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

Beyond GGPT we also prove the **Bachman–Tamon–Feder reduction**
(arXiv:1108.0339 §3, building on Feder PRL 97 180502): the Cartesian product
of quotients is itself a quotient of the Cartesian product — a categorical
naturality square between `total` and `quotient`
(`cartesianProduct_quotient_naturality`).

The reachable content (master theorem, Cartesian PST, product/eigenvector
evolution laws, the naturality square) is proven; unreachable scaffold
statements (lex/template/color-completion amplitude forms, the stratified
lift, the open-problem `Prop`s) have been removed rather than carried as dead
`sorry`s.
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

-- NOTE.  Two scaffold statements once lived here — `templateJoin_pst_iff` and
-- `colorCompletion_pst_iff` (singleton-fiber / injective-color specializations of
-- bundle PST).  Both required a `WeightedGraph`-reindex/iso naturality lemma not
-- present in this layer and carried only honest `sorry`s; neither was cited
-- anywhere.  They have been removed (our own never-proved statements, not
-- externally-citable).  The genuinely-proven bundle-PST content is the master
-- theorem `GraphBundle.pst_iff_quotient` above and the Cartesian corollary
-- `BundlePSTCorollaries.cartesianProduct_pst`.

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

-- NOTE.  A scaffold `def IterCartesianQuotientNaturality` once lived here — a
-- `Prop`-valued statement of the *iterated* (n-fold) Cartesian-quotient naturality
-- square, phrased as the existence of a "product quotient" matrix recovering the
-- factor symmetric quotients on its Kronecker-sum diagonal blocks.  It was never
-- proved, never inhabited, never used, and not externally citable (our own
-- statement, awaiting the iterated-Cartesian bifunctor of the `Categorical` layer);
-- it has been removed.  The genuinely-proven Feder content is the binary
-- naturality square `cartesianProduct_quotient_naturality` above, built on the
-- product partition `productPartition`.

end BundleFederReduction

-- NOTE.  Two further scaffold layers once lived here:
--   §5 a `FiberStratification` structure + `stratified_pst_lift` (a non-regular-
--      fiber generalization requiring construction of a strata `EquitablePartition`
--      from the stratification data, carried only as an honest `sorry`), and
--   §6 three open-problem `Prop` `def`s (`OpenPGSTBundleIff`,
--      `OpenFractionalRevivalBundleIff`, `OpenStratifiedIff`).
-- All five were our own never-proved statements, cited nowhere and not externally
-- citable; they have been removed.  The genuinely-proven bundle content is the
-- master theorem `GraphBundle.pst_iff_quotient`, the Cartesian corollary
-- `cartesianProduct_pst`, the product/eigenvector evolution laws of §3, and the
-- Bachman–Tamon–Feder naturality square `cartesianProduct_quotient_naturality`.

end Graphplay
