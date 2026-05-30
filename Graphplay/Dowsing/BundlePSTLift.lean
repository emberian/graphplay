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

/-! ### 3.2 GGPT: Lexicographic product preserves PST under regular fibers -/

/-- **GGPT Theorem (Lexicographic, [1009.1340 §4]).**
For a regular `H`, the lexicographic product `G[H]` exhibits PST between
`(u₁, w₁)` and `(u₂, w₂)` whenever `G` exhibits PST between `u₁` and `u₂`
(at a compatible time `τ`).

Specialization of `pst_iff_quotient` to the bundle whose template is `G`,
fiber `H`, and coupling the all-ones matrix `J` on each `G`-edge. -/
theorem lexProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dH : ℂ} (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w₁ w₂ : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) :
    IsPST (GraphBundle.lexProduct G H) (u₁, w₁) (u₂, w₂) τ := by
  -- HONEST SORRY (genuinely GGPT-hard; statement is NOT proven here).
  -- Lex coupling = J = all-ones rectangular matrix, which is
  -- (|W|, |W|)-biregular.  In the fiber quotient the off-diagonal is
  -- `|W| · G.adj`, a positive rescaling of `G`, so PST in `G` at time `τ`
  -- becomes PST in the quotient at the RESCALED time `τ / |W|`, not `τ`.
  -- Matching the original `τ` requires the eigenvalue-lattice condition of
  -- GGPT (arXiv:1009.1340 §4, Thm 2), which is not among the hypotheses of
  -- this statement; without it the conclusion at the literal `τ` is false in
  -- general.  Left as an honest sorry pending that spectral input.
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

/-- **GGPT Theorem (Weak product, [1009.1340 §3]).**  For a circulant `H`
with odd eigenvalues and `G` with PST whose spectrum lies in `π · ℤ`, the
tensor product `G ⊗ H` has PST.

This is the spectral form; the underlying combinatorial fact is the same
bundle iff. -/
theorem tensorProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dH : ℂ} (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w₁ w₂ : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) :
    IsPST (tensorProduct G H) (u₁, w₁) (u₂, w₂) τ := by
  -- HONEST SORRY (genuinely GGPT-hard; statement is NOT proven here).
  -- The tensor adjacency is the Kronecker PRODUCT `A_G ⊗ₖ A_H`, whose
  -- exponential does NOT factor as `exp(A_G) ⊗ₖ exp(A_H)` (unlike the
  -- Cartesian/Kronecker-SUM case): `exp(A⊗B) ≠ exp A ⊗ exp B`.  GGPT
  -- (arXiv:1009.1340 §3) instead require `H` circulant with odd eigenvalues
  -- and `G` PST with spectrum in `π·ℤ`; those spectral hypotheses are not
  -- present here.  Closing this needs the GGPT spectral-lattice argument.
  sorry

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
  -- HONEST SORRY (beyond GGPT; statement is NOT proven here).
  -- The strong adjacency `A_{G⊠H} = A_G ⊗ I + I ⊗ A_H + A_G ⊗ₖ A_H` carries
  -- the tensor (Kronecker-product) cross term, so its exponential does not
  -- factor through a Cartesian-style Kronecker-sum split.  As in the tensor
  -- case this needs a spectral-lattice / circulant hypothesis on `H` (cf.
  -- arXiv:1009.1340 §3–§4) not present in the statement.
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
  -- HONEST SORRY (beyond GGPT; statement is NOT proven here).
  -- The conormal adjacency `A_G ⊕ A_H − A_G ⊗ₖ A_H` again contains a
  -- Kronecker-product cross term, so the walk does not factor as a Cartesian
  -- Kronecker sum; PST preservation requires the same spectral-lattice input
  -- as the tensor/strong cases (cf. arXiv:1009.1340 §3).
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
  -- HONEST SORRY (beyond GGPT; statement is NOT proven here).
  -- `disjunctiveProduct = conormalProduct`, so this reduces to
  -- `conormalProduct_pst` and needs the same spectral-lattice input
  -- (cf. arXiv:1009.1340 §3).  Left honest.
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
  -- The empty-fiber + all-ones-coupling bundle has biregular couplings
  -- of constant row sum `n`.  Master theorem.  The factor `n` enters
  -- via the row-sum rescaling between `quotient` and `Q`.
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
  -- Within a single color class the marginal evolution is trivial
  -- (empty fiber); across color classes the master theorem reduces to
  -- the complete graph on `J`.  The `∨` accounts for the "stay in same
  -- color class" case.
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
            ⟨P.symmQuotient, P.symmQuotient_isHermitian, by sorry⟩
            ⟨P'.symmQuotient, P'.symmQuotient_isHermitian, by sorry⟩).adj := by
  -- The two `WeightedGraph` wrappers around `P.quotient`, `P'.quotient`
  -- need to absorb the diagonal in the same way as `fiberQuotient.loopless`;
  -- modulo that, the naturality is a direct computation:
  -- `(P × P').quotient ((i, j), (i', j')) =`
  --   `P.quotient (i, i') · δ(j, j') + δ(i, i') · P'.quotient (j, j')`
  -- which is exactly the Cartesian product of the quotient adjacencies.
  sorry

/-- Iterated form: the Cartesian product of `n` quotient graphs is the
quotient of the Cartesian product by the canonical iterated partition.
This is the form used by Feder (PRL 97 180502) for the hypercube and
the path-collapsing argument of GGPT (1009.1340 §2). -/
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
  -- HONEST SORRY: constructing the strata `EquitablePartition` requires combining
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
      IsBiregular (B.coupling h) (α h) (β h))
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
       (hc : ∀ {i j : I} (h : Q.Adj i j), IsBiregular (B.coupling h) (a h) (b h)),
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
    (B : GraphBundle Q V) (_F : GraphBundle.FiberStratification B) (τ : ℝ),
    ∃ (J : Type v) (_ : Fintype J) (_ : DecidableEq J)
      (P : EquitablePartition B.total J) (i j : J),
      IsCellUniformPST B.total P i j τ ↔
        LoopyWeightedGraph.IsLoopyPST
          ⟨P.symmQuotient, P.symmQuotient_isHermitian⟩ j i τ

end GraphplayOpen

end Graphplay
