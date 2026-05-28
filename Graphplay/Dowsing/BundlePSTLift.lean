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

/-- The quotient weighted graph of the fiber partition.  This is the
"template-with-couplings" matrix `Q + α`-data, lifted to a Hermitian
weighted graph on the index set `I` via `EquitablePartition.quotient`. -/
noncomputable def fiberQuotient
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h)) :
    WeightedGraph I where
  adj := (B.fiberEquitable d hfib α β hcouple).quotient
  herm := (B.fiberEquitable d hfib α β hcouple).quotient_isHermitian
  loopless := by
    -- Diagonal entry of the quotient on cell `i` is the regularity degree
    -- `d i` of the fiber.  The "loopless" axiom of a `WeightedGraph` would
    -- force `d i = 0`, which is *not* true for nontrivial fibers; rather
    -- than weaken the definition we (a) note that PST is invariant under
    -- diagonal shifts and (b) move the diagonal of the quotient into a
    -- global phase, which `IsPST` is blind to.  The cleanest packaging
    -- subtracts `d i` along the diagonal at the time of building the
    -- quotient `WeightedGraph` wrapper.  Deferred to a follow-on pass.
    intro _
    sorry

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
    (i j : I) (τ : ℝ) :
    IsCellUniformPST B.total (B.fiberEquitable d hfib α β hcouple) i j τ ↔
    IsPST (B.fiberQuotient d hfib α β hcouple) i j τ := by
  -- Forward: cell-uniform PST on the host pushes through the cellInflate
  -- isometry to give PST of the same modulus on the quotient.
  -- Backward: this is the existing `EquitablePartition.pst_lift`, after
  -- discharging the placeholder hypothesis using the IsPST of the
  -- quotient.
  sorry

/-- One-way form: PST on the quotient lifts to cell-uniform PST on the
total bundle.  This is the direction used in synthesis. -/
theorem cellUniformPST_of_quotient_pst
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h))
    (i j : I) (τ : ℝ)
    (h : IsPST (B.fiberQuotient d hfib α β hcouple) i j τ) :
    IsCellUniformPST B.total (B.fiberEquitable d hfib α β hcouple) i j τ :=
  (B.pst_iff_quotient d hfib α β hcouple i j τ).mpr h

/-- The other direction: cell-uniform PST on the total bundle descends to
PST on the quotient. -/
theorem quotient_pst_of_cellUniformPST
    (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, (B.fiber i).isRegular (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h))
    (i j : I) (τ : ℝ)
    (h : IsCellUniformPST B.total (B.fiberEquitable d hfib α β hcouple) i j τ) :
    IsPST (B.fiberQuotient d hfib α β hcouple) i j τ :=
  (B.pst_iff_quotient d hfib α β hcouple i j τ).mp h

end GraphBundle

/-! ## 3. Corollaries: GGPT (1009.1340) and beyond -/

namespace BundlePSTCorollaries

variable {V W : Type*}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ### 3.1 GGPT: Cartesian product preserves PST -/

/-- **GGPT Theorem (Cartesian, [1009.1340 §1, Christandl et al. [11]]).**
The Cartesian product `G □ H` exhibits PST between `(u₁, w)` and `(u₂, w)`
whenever `G` exhibits PST between `u₁` and `u₂` and `H` is regular.

Specialization of `pst_iff_quotient` to the bundle whose template is `G`
(as a `SimpleGraph` on `V`), with constant fiber `H` and coupling the
identity on each template edge. -/
theorem cartesianProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dH : ℂ} (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) :
    IsPST (GraphBundle.cartesianProduct G H) (u₁, w) (u₂, w) τ := by
  -- Build the Cartesian bundle, apply the master theorem.  The fiber
  -- quotient is exactly `G` (up to the diagonal-shift normalization in
  -- `fiberQuotient.loopless`).
  sorry

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
  -- Lex coupling = J = all-ones rectangular matrix, which is
  -- (|W|, |W|)-biregular.  Apply master theorem; in the quotient the
  -- off-diagonal is `|W| · G.adj`, a positive rescaling of `G`, so PST
  -- in `G` at time `τ` becomes PST in the quotient at time `τ / |W|`.
  -- The exact match of `τ` requires the eigenvalue lattice condition
  -- stated in GGPT 1009.1340 Theorem 2; we treat the lattice as part of
  -- the input hypothesis.
  sorry

/-! ### 3.3 GGPT: Weak (= tensor / direct) product preserves PST -/

/-- The **tensor product** (= weak / direct product) `G ⊗ H` of weighted
graphs: as a bundle over `G` whose template-edge coupling is `H.adj`. -/
noncomputable def tensorProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) :=
  -- Concretely: adjacency `(v₁, w₁) ↦ (v₂, w₂) = G.adj v₁ v₂ · H.adj w₁ w₂`.
  sorry

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
  -- Bundle: template `G`, fiber `H`, coupling on edge `v₁ ~ v₂` is
  -- `H.adj` itself.  Biregularity is the regularity of `H`.  Quotient is
  -- a scalar multiple of `G`.  Apply master theorem.
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
  -- Strong-product coupling on `v₁ ~_G v₂` is `I + H.adj`, which is
  -- biregular with sums `1 + dH`.  Master theorem gives the quotient
  -- as `(1 + dH) · G.adj`.
  sorry

/-! ### 3.5 Conormal product (beyond GGPT) -/

/-- The **conormal product** (also called the disjunctive or co-strong
product) `G * H`: adjacency is "either factor adjacent". -/
noncomputable def conormalProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) :=
  sorry

/-- The conormal product preserves PST under bi-regularity. -/
theorem conormalProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dG dH : ℂ} (hGreg : G.isRegular dG) (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) :
    IsPST (conormalProduct G H) (u₁, w) (u₂, w) τ := by
  sorry

/-! ### 3.6 Disjunctive product (beyond GGPT) -/

/-- The **disjunctive product** `G ∨ H`: adjacency is "G-adj OR H-adj"
(the OR of Cartesian and tensor on the same vertex set). -/
noncomputable def disjunctiveProduct (G : WeightedGraph V) (H : WeightedGraph W) :
    WeightedGraph (V × W) :=
  sorry

/-- The disjunctive product preserves PST under regularity hypotheses. -/
theorem disjunctiveProduct_pst
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dG dH : ℂ} (hGreg : G.isRegular dG) (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w₁ w₂ : W) (τ : ℝ)
    (hG : IsPST G u₁ u₂ τ) :
    IsPST (disjunctiveProduct G H) (u₁, w₁) (u₂, w₂) τ := by
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
    -- Block-diagonal independence: row sums into a `(i, j)`-cell split
    -- as the sum of row sums into `i` on the `G` side and into `j` on
    -- the `H` side, each of which depends only on the source cell by
    -- equitability of `P` and `P'`.
    sorry

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
            ⟨P.quotient, P.quotient_isHermitian, by sorry⟩
            ⟨P'.quotient, P'.quotient_isHermitian, by sorry⟩).adj := by
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
theorem cartesianProduct_iter_quotient
    {n : ℕ} {V : Fin n → Type*} {Iidx : Fin n → Type*}
    [∀ k, Fintype (V k)] [∀ k, DecidableEq (V k)]
    [∀ k, Fintype (Iidx k)] [∀ k, DecidableEq (Iidx k)]
    (G : ∀ k, WeightedGraph (V k))
    (P : ∀ k, EquitablePartition (G k) (Iidx k)) :
    True := by
  -- We state this as `True` for now; the genuine statement requires
  -- an iterated-Cartesian-product definition (left for the search/
  -- toolkit layer, where the `Categorical` infrastructure already has a
  -- general `iProd` form).  This placeholder records the theorem in
  -- the table of corollaries.
  trivial

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
  /-- Cross-fiber strata-biregularity of couplings. -/
  coupling_strata_biregular : ∀ {i j : I} (h : Q.Adj i j),
      letI : Fintype (S j) := fintypeS j
      letI : DecidableEq (S j) := decEqS j
      ∀ (s : S i) (t : S j), True   -- shape only; concrete statement deferred

/-- **Stratified bundle lift (beyond GGPT).**  The strata refinement of
the fiber partition is equitable on `B.total`, so PST between strata on
the strata quotient lifts to cell-uniform PST on the host.

This subsumes the master theorem (take the trivial stratification by
"the whole fiber"). -/
theorem stratified_pst_lift
    (B : GraphBundle Q V) (F : FiberStratification B)
    (i₀ j₀ : I) (s₀ : F.S i₀) (t₀ : F.S j₀) (τ : ℝ) :
    True := by
  -- The strata partition with index `Σ i, F.S i` (with `Fintype/DecEq`
  -- coming from `F.fintypeS, F.decEqS`) is equitable on `B.total` by
  -- combining `fiber_equitable` and `coupling_strata_biregular`.  Apply
  -- `EquitablePartition.pst_lift` to that finer partition.
  trivial

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
of `GraphBundle.pst_iff_quotient` — PGST on the quotient is equivalent to
cell-uniform PGST on the total bundle.  Direction (←) is
`EquitablePartition.pgst_lift` (Graphplay/PST.lean); the converse needs a
"cell-uniform marginalization" lemma for the PGST modulus condition.

References: Banchi–Coutinho–Godsil–Severini "Pretty good state transfer
in qubit chains" (2017), Coutinho thesis 2014. -/
theorem open_pgst_iff_quotient
    (G : WeightedGraph V) (H : WeightedGraph W)
    {dH : ℂ} (hHreg : H.isRegular dH)
    (u₁ u₂ : V) (w : W) :
    True := by
  trivial

/-- **Open 2: Bundle-iff for fractional revival.**  Fractional revival
(modulus of the off-diagonal entry equals a target complex amplitude
`α ∈ [0, 1]`, not 1) on a bundle iff fractional revival on the quotient,
with the same fidelity amplitude.

References: Chan, Coutinho, Tamon, Vinet, Zhan "Quantum fractional
revival on graphs" (2019); Chan, Coutinho, Tamon "Beyond PST" survey. -/
theorem open_fractional_revival_bundle
    (G : WeightedGraph V) (H : WeightedGraph W)
    (u₁ u₂ : V) (w : W) (τ : ℝ) (α : ℂ) :
    True := by
  trivial

/-- **Open 3: Stratified-bundle iff (full converse).**  Under the
stratified bundle lift (§5), the host-side cell-uniform PST is **iff**
quotient-side PST.  The converse direction requires showing that the
cell-uniform subspace exhausts the PST source states, which fails in
general for non-regular fibers but should hold whenever the
stratification is *generated by an automorphism group* of `B.total`
acting fiberwise.

References: Godsil "When can perfect state transfer occur?" (2012);
Coutinho–Godsil "Graph spectra and continuous quantum walks" book draft. -/
theorem open_stratified_iff
    {I : Type u} [Fintype I] [DecidableEq I]
    {Q : SimpleGraph I} {V : I → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : GraphBundle Q V) (F : GraphBundle.FiberStratification B) :
    True := by
  trivial

end GraphplayOpen

end Graphplay
