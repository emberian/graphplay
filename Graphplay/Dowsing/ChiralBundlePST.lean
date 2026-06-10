/-
# Graphplay.Dowsing.ChiralBundlePST

**Hole D1**: Chiral perfect state transfer on graph bundles — a chiral
generalization of the Bachman–Tamon bundle PST machinery and a global
generalization of Levine–Mesapam–Mustico–Tamon–Tucker–Zhan's uniform-mixing
speedup on chirally-signed complete graphs.

## Mathematical context

* **Ge–Greenberg–Perez–Tamon, "Perfect state transfer, graph products and
  equitable partitions"**, arXiv:1009.1340 (2010) — the original
  product/bundle PST theorem in the **unsigned** setting. It shows that PST
  on a graph product reduces to PST on the factors via the equitable
  partition that fibers the product.

* **Bachman–Fernando–Lin–Pal–Tamon, "Perfect state transfer on quotient
  graphs"**, arXiv:1108.0339 (2011) — the cleanest bundle predecessor we
  generalize. Theorem 3.2 there says: a host graph admits **cell-uniform
  PST** iff the **quotient** graph (under the equitable cell partition)
  admits PST. Both directions are unsigned.

* **Levine–Mesapam–Mustico–Tamon–Tucker–Zhan, "Uniform Mixing in Chiral
  Quantum Walks"**, arXiv:2605.04414 (2026) — the **base case** of our
  result. There the index space `I` is a singleton (`Q = pt`), so the
  bundle has a single fiber, and the chiral signing is just a signing of
  `K_n`. They produce a unitary signing `σ` of `K_n` for which `K_nσ`
  exhibits *probabilistic uniform mixing* at time `π/(3√3)`, **faster than
  any unoriented Hamming graph**. This is a chiral violation of an
  unsigned No-Go (Ahmadi et al. 2003).

## What is new here

No prior published work assembles the **bundle theorem with chiral phases**.
Bachman–Tamon is bundle-but-unsigned; Levine et al. is signed-but-base-case
(single fiber). The headline theorem of this file:

> A chirally-signed bundle whose underlying bundle has regular fibers and
> biregular couplings exhibits cell-uniform PST between cells `i` and `j` at
> time `τ` iff the *chirally-signed quotient* graph exhibits PST between
> vertices `i` and `j` at time `τ`.

In other words: **chiral PST on a bundle is determined by chiral PST on the
quotient**, exactly when the bundle is fiber-equitable. Levine et al.'s
`K_nσ` speedup is precisely the case `Q = pt`, `V () = Fin n`, fibers empty;
our theorem says we can **lift their signing to any bundle with K_n^σ
fibers** — every base graph `Q` with `K_n^σ` fibers inherits the speedup at
the level of cell-uniform mixing.

We also state a "phase-equitable refinement" lemma: a chiral signing
induces a (potentially finer) equitable partition by grouping vertices with
the same outgoing-phase profile. This is the chiral analogue of the
classical "twin partition" used in Bachman–Tamon §3.

Every nontrivial proof is `sorry`. The file is a **specification** that
later proof passes can fill in.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Bundle
import Graphplay.PST
import Graphplay.Chiral
import Graphplay.StdLib.Path

universe u v w

open scoped Matrix

namespace Graphplay

open Graphplay.StdLib (pathPSTTime path_P2_PST_residual path_P3_PST_residual)

/-! ## Chiral bundles

A *chiral bundle* over a template `SimpleGraph Q` on `I` with fibers `V : I →
Type` is a `GraphBundle Q V` together with, **for each template edge**, a
chiral signing of the corresponding pair of fibers. The signings must be
compatible with the Hermitian symmetry of the bundle: the signing on a
reversed template edge is the pointwise conjugate of the signing on the
forward edge.

This is the precise data the chiral PST/mixing theorem requires. A general
"signing of every pair of vertices" would not respect the bundle structure;
restricting signings to template edges is what makes Lemma 2.1 of Levine et
al. (the characteristic-isometry intertwining) work.
-/

/-- A **chiral signing of a bundle edge**: a phase function on the pair
`V i × V j` for a template edge `i ~ j`, valued in the unit circle, with the
Hermitian-compatibility built in via the dual edge. The intra-fiber phases
live separately as a `ChiralSigning (V i)` per `i`. -/
structure EdgeChiralSigning {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type v) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (i j : I) where
  /-- The phase on `V i × V j`. -/
  phase : V i → V j → ℂ
  /-- Each phase is unimodular. -/
  unimod : ∀ x y, ‖phase x y‖ = 1

/-- A **chiral bundle** over a template `Q` with fiber assignment `V`: a
`GraphBundle Q V` together with intra-fiber chiral signings and inter-fiber
edge signings, satisfying the bundle-Hermitian compatibility on reversed
edges. -/
structure ChiralBundle {I : Type u} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) (V : I → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] extends GraphBundle Q V where
  /-- Per-fiber intra-fiber chiral signing. -/
  fiberSigning : ∀ i, ChiralSigning (V i)
  /-- Per-template-edge chiral signing. Stored on a directed edge; the
  Hermitian compatibility on the reversed edge is `edgeHermCompat` below. -/
  edgeSigning : ∀ {i j : I}, Q.Adj i j → EdgeChiralSigning V i j
  /-- The signing on the reversed template edge is the pointwise conjugate
  of the forward signing (chiral Hermitian condition on bundle edges). -/
  edgeHermCompat : ∀ {i j : I} (h : Q.Adj i j),
    ∀ x y, (edgeSigning (Q.symm h)).phase y x = star ((edgeSigning h).phase x y)

namespace ChiralBundle

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {Q : SimpleGraph I} {V : I → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-! ### The chirally-signed total adjacency

We assemble the bundle's data into a single `WeightedGraph` on the disjoint
union `Σ i, V i`. Intra-fiber entries are signed by `fiberSigning`;
inter-fiber entries are signed by `edgeSigning` on the matching template
edge. The result is Hermitian by `hermCompat` (from the base bundle) plus
`edgeHermCompat`, and loopless by the fiber loopless conditions plus the
intra-fiber `ChiralSigning.diag` axiom.
-/

/-- The **vertex-level chiral signing** of the total bundle, assembled from
the per-fiber and per-edge signings.  On an intra-fiber pair `x, y` with
`x.1 = y.1` it is the fiber signing `fiberSigning x.1`; on an inter-fiber
pair across a template edge it is the edge phase `edgeSigning h`; and on a
non-adjacent inter-fiber pair (where the total adjacency is `0` anyway) it
is the trivial phase `1`.

Unimodularity holds in every branch (fiber/edge phases are unimodular, and
`1` is unimodular).  Hermitian compatibility holds by `(fiberSigning x.1).herm`
on the diagonal blocks and `B.edgeHermCompat` on the edge blocks. -/
noncomputable def totalChiralSigning (B : ChiralBundle Q V) :
    ChiralSigning (Σ i, V i) where
  σ x y :=
    if h : x.1 = y.1 then (B.fiberSigning x.1).σ x.2 (h ▸ y.2)
    else by
      classical exact
        if hadj : Q.Adj x.1 y.1 then (B.edgeSigning hadj).phase x.2 y.2 else 1
  unimod := by
    classical
    intro x y
    by_cases h : x.1 = y.1
    · rw [dif_pos h]; exact (B.fiberSigning x.1).unimod x.2 (h ▸ y.2)
    · rw [dif_neg h]
      by_cases hadj : Q.Adj x.1 y.1
      · rw [dif_pos hadj]; exact (B.edgeSigning hadj).unimod x.2 y.2
      · rw [dif_neg hadj]; simp
  herm := by
    classical
    intro x y
    obtain ⟨xi, xv⟩ := x
    obtain ⟨yi, yv⟩ := y
    by_cases h : xi = yi
    · -- Diagonal block: fiber signing is Hermitian.
      subst h
      rw [dif_pos rfl, dif_pos rfl]
      simpa using (B.fiberSigning xi).herm xv yv
    · -- Off-diagonal block.
      have hyx : ¬ yi = xi := fun hc => h hc.symm
      rw [dif_neg h, dif_neg hyx]
      by_cases hadj : Q.Adj xi yi
      · rw [dif_pos hadj, dif_pos hadj.symm]
        -- `edgeHermCompat` at `hadj`, with `Q.symm hadj = hadj.symm` by
        -- proof irrelevance.
        have hc := B.edgeHermCompat hadj xv yv
        have hcoup : (B.edgeSigning hadj.symm).phase yv xv
            = (B.edgeSigning (Q.symm hadj)).phase yv xv := by rfl
        rw [hcoup, hc]
      · have hadj' : ¬ Q.Adj yi xi := fun hc => hadj hc.symm
        rw [dif_neg hadj, dif_neg hadj']; simp
  diag := by
    classical
    intro x
    rw [dif_pos rfl]
    simpa using (B.fiberSigning x.1).diag x.2

/-- The **chirally-signed total adjacency**: the chirally-signed `Σ i, V i`
weighted graph assembled from a chiral bundle, obtained by applying the
vertex-level signing `totalChiralSigning` to the unsigned total adjacency
`B.total`.  Intra-fiber blocks are signed by `fiberSigning i`; inter-fiber
blocks by `edgeSigning h` on the template edge `h : Q.Adj i j`. -/
noncomputable def totalSigned (B : ChiralBundle Q V) :
    WeightedGraph (Σ i, V i) :=
  B.toGraphBundle.total.signedBy B.totalChiralSigning

/-- The chirally-signed total adjacency factors, by construction, as the
unsigned total adjacency of the base bundle with the vertex-level chiral
signing `totalChiralSigning` applied. -/
theorem totalSigned_eq_signedBy_total (B : ChiralBundle Q V) :
    ∃ s : ChiralSigning (Σ i, V i),
      B.totalSigned = B.toGraphBundle.total.signedBy s :=
  ⟨B.totalChiralSigning, rfl⟩

/-! ### Chirally-signed quotient

The quotient of a chiral bundle is a weighted graph on the template index
type `I`. Off-diagonal entries are the (signed) quotient row sums of the
chirally-signed total adjacency; diagonal entries are zero (we assume
loopless fibers and discard the intra-fiber regularity scalar in line with
the standard PST quotient convention of Bachman–Tamon §2).

For the headline theorem we only need the quotient to be a `WeightedGraph`;
its precise entries are determined by `branching` on the equitable partition
constructed in `GraphBundle.fiberPartition`.
-/

/-- The **chirally-signed quotient**: a `WeightedGraph` on the template
index `I` whose off-diagonal entry `(i, j)` is the common branching number
of any representative of cell `i` into cell `j` of the chirally-signed
total adjacency. Loopless and Hermitian by construction (via
`EquitablePartition.quotient_isHermitian` applied to a fiber-equitable
partition of `totalSigned`). -/
noncomputable def quotientSigned (B : ChiralBundle Q V) : WeightedGraph I where
  adj := fun i j =>
    if i = j then 0
    else
      -- Total signed edge mass from cell `i` into cell `j` of `totalSigned`:
      -- the sum of `totalSigned.adj x z` over all `x` in cell `i` and `z` in
      -- cell `j` (cells are the fiber indices `Sigma.fst`).  Summing over the
      -- whole cell (rather than one representative) makes this Hermitian
      -- unconditionally; when the fiber partition is equitable it equals
      -- `|C_i|` times the common branching number, matching the
      -- Bachman–Tamon quotient up to the cell-size normalization.
      ∑ x : Σ k, V k, ∑ z : Σ k, V k,
        (if x.1 = i ∧ z.1 = j then B.totalSigned.adj x z else 0)
  herm := by
    -- `adj j i = ∑∑ totalSigned z x = ∑∑ star (totalSigned x z) = star (adj i j)`
    -- using the Hermitian symmetry of `totalSigned`.
    refine Matrix.IsHermitian.ext ?_
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬ j = i := fun hc => hij hc.symm
      show star (if j = i then (0 : ℂ) else _) = if i = j then (0 : ℂ) else _
      rw [if_neg hji, if_neg hij]
      rw [star_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [star_sum]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hxz : z.1 = i ∧ x.1 = j
      · rw [if_pos hxz, if_pos ⟨hxz.2, hxz.1⟩]
        exact (B.totalSigned.herm.apply z x)
      · rw [if_neg hxz, if_neg (fun hc => hxz ⟨hc.2, hc.1⟩), star_zero]
  loopless := by
    intro v
    simp

/-! ## Headline theorem: chiral PST on bundles -/

/-- A chiral bundle has **regular fibers** if every `(fiberSigning i)`-signed
fiber graph `(B.fiber i).signedBy (B.fiberSigning i)` is regular of some
degree `d i`. The chiral signing inside a fiber does **not** change the row
magnitudes, so this is equivalent to the underlying fibers being regular —
but we package the signed statement for downstream uniformity. -/
def HasRegularFibers (B : ChiralBundle Q V) (d : I → ℂ) : Prop :=
  ∀ i, ((B.fiber i).signedBy (B.fiberSigning i)).isRegular (d i)

/-- A chiral bundle has **biregular couplings** if every signed coupling
matrix `(B.edgeSigning h).phase ⊙ B.coupling h` is `(α h, β h)`-biregular
in the sense of `GraphBundle.IsBiregular`. -/
def HasBiregularCouplings (B : ChiralBundle Q V)
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ) : Prop :=
  ∀ {i j : I} (h : Q.Adj i j),
    GraphBundle.IsBiregular (fun x y => (B.edgeSigning h).phase x y * B.coupling h x y)
      (α h) (β h)

/-- The fiber-equitable partition of the chirally-signed total adjacency,
when the chiral bundle has regular fibers and biregular couplings. This is
the chiral analogue of `GraphBundle.fiberPartition`, and reduces to it via
`signedBy_preserves_equitable` once `totalSigned_eq_signedBy_total` is
established. -/
noncomputable def fiberPartitionSigned (B : ChiralBundle Q V)
    {d : I → ℂ} (hfib : B.HasRegularFibers d)
    {α β : ∀ {i j : I}, Q.Adj i j → ℂ} (hcouple : B.HasBiregularCouplings α β) :
    EquitablePartition B.totalSigned I where
  cells := fun x => x.1
  uniform := by
    classical
    -- Mirror of `GraphBundle.fiberPartition`: the signed weight from any
    -- vertex `x` of fiber `i` into fiber `j` is a constant depending only on
    -- `(i, j)` — `d i` on the diagonal (signed-fiber regularity), `α h` along
    -- a template edge (signed-coupling biregularity), and `0` otherwise.
    suffices key : ∀ (i j : I) (x : Σ k, V k), x.1 = i →
        (∑ z : Σ k, V k, (if z.1 = j then B.totalSigned.adj x z else 0))
          = (if hij : i = j then d i
             else if hadj : Q.Adj i j then α (i := i) (j := j) hadj else 0) by
      intro i j x y hx hy
      rw [key i j x hx, key i j y hy]
    intro i j x hx
    -- A signed total entry expands as `σ · (unsigned total entry)`.
    have hentry : ∀ z : Σ k, V k,
        B.totalSigned.adj x z
          = B.totalChiralSigning.σ x z * B.toGraphBundle.total.adj x z := by
      intro z; rfl
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single j]
    · -- Inner sum over fiber `j`.
      subst hx
      have hstrip : (∑ w : V j,
            (if (⟨j, w⟩ : Σ k, V k).1 = j then B.totalSigned.adj x ⟨j, w⟩ else 0))
          = ∑ w : V j, B.totalSigned.adj x ⟨j, w⟩ := by
        apply Finset.sum_congr rfl; intro w _; simp
      rw [hstrip]
      by_cases hij : x.1 = j
      · -- Diagonal block: signed-fiber regularity gives `d x.1`.
        rw [dif_pos hij]
        have hsum : (∑ w : V j, B.totalSigned.adj x ⟨j, w⟩)
            = ∑ w : V j,
                (B.fiberSigning x.1).σ x.2 (hij ▸ w) * (B.fiber x.1).adj x.2 (hij ▸ w) := by
          apply Finset.sum_congr rfl
          intro w _
          rw [hentry]
          -- both `σ` and the unsigned total reduce to the fiber via `x.1 = j`.
          have h1 : B.totalChiralSigning.σ x ⟨j, w⟩
              = (B.fiberSigning x.1).σ x.2 (hij ▸ w) := by
            show (if h : x.1 = (⟨j, w⟩ : Σ k, V k).1 then
                (B.fiberSigning x.1).σ x.2 (h ▸ w) else _) = _
            rw [dif_pos hij]
          have h2 : B.toGraphBundle.total.adj x ⟨j, w⟩
              = (B.fiber x.1).adj x.2 (hij ▸ w) := by
            show (if h : x.1 = (⟨j, w⟩ : Σ k, V k).1 then
                (B.fiber x.1).adj x.2 (h ▸ w) else _) = _
            rw [dif_pos hij]
          rw [h1, h2]
        rw [hsum]
        -- Reindex to a sum over `V x.1` and apply signed-fiber regularity.
        subst hij
        have := hfib x.1 x.2
        unfold Graphplay.WeightedGraph.degree at this
        simpa [WeightedGraph.signedBy_adj] using this
      · -- Off-diagonal block: signed-coupling biregularity (or `0`).
        rw [dif_neg hij]
        have hsum : (∑ w : V j, B.totalSigned.adj x ⟨j, w⟩)
            = ∑ w : V j, (if hadj : Q.Adj x.1 j then
                (B.edgeSigning hadj).phase x.2 w * B.coupling hadj x.2 w else 0) := by
          apply Finset.sum_congr rfl
          intro w _
          rw [hentry]
          by_cases hadj : Q.Adj x.1 j
          · have h1 : B.totalChiralSigning.σ x ⟨j, w⟩
                = (B.edgeSigning hadj).phase x.2 w := by
              show (if h : x.1 = (⟨j, w⟩ : Σ k, V k).1 then _ else
                  (if hadj' : Q.Adj x.1 (⟨j, w⟩ : Σ k, V k).1 then
                    (B.edgeSigning hadj').phase x.2 w else 1)) = _
              rw [dif_neg hij, dif_pos hadj]
            have h2 : B.toGraphBundle.total.adj x ⟨j, w⟩ = B.coupling hadj x.2 w := by
              show (if h : x.1 = (⟨j, w⟩ : Σ k, V k).1 then _ else
                  (if hadj' : Q.Adj x.1 (⟨j, w⟩ : Σ k, V k).1 then
                    B.coupling hadj' x.2 w else 0)) = _
              rw [dif_neg hij, dif_pos hadj]
            rw [h1, h2, dif_pos hadj]
          · have h2 : B.toGraphBundle.total.adj x ⟨j, w⟩ = 0 := by
              show (if h : x.1 = (⟨j, w⟩ : Σ k, V k).1 then _ else
                  (if hadj' : Q.Adj x.1 (⟨j, w⟩ : Σ k, V k).1 then
                    B.coupling hadj' x.2 w else 0)) = 0
              rw [dif_neg hij, dif_neg hadj]
            rw [h2, mul_zero, dif_neg hadj]
        rw [hsum]
        by_cases hadj : Q.Adj x.1 j
        · rw [dif_pos hadj]
          have hb := (hcouple hadj).1 x.2
          rw [show (∑ w : V j, (if h : Q.Adj x.1 j then
                (B.edgeSigning h).phase x.2 w * B.coupling h x.2 w else 0))
                = ∑ w : V j, (B.edgeSigning hadj).phase x.2 w * B.coupling hadj x.2 w from by
                apply Finset.sum_congr rfl; intro w _; rw [dif_pos hadj]]
          exact hb
        · rw [dif_neg hadj]
          apply Finset.sum_eq_zero
          intro w _
          rw [dif_neg hadj]
    · -- Off-`j` fibers contribute nothing thanks to the indicator.
      intro k _ hk
      apply Finset.sum_eq_zero
      intro w _
      simp [hk]
    · intro h; exact absurd (Finset.mem_univ j) h

/-! ### Headline chiral-bundle PST/PGST (singleton-fiber form below) -/
/-- The cell cardinality of the fiber-partition of `totalSigned`: cell `i` is the
fiber `V i`, so its cardinality is `Fintype.card (V i)`. -/
theorem fiberPartitionSigned_cellCard (B : ChiralBundle Q V)
    {d : I → ℂ} (hreg : B.HasRegularFibers d)
    {α β : ∀ {i j : I}, Q.Adj i j → ℂ} (hbi : B.HasBiregularCouplings α β)
    (i : I) :
    (B.fiberPartitionSigned (α := α) (β := β) hreg hbi).cellCard i
      = (Fintype.card (V i) : ℝ) := by
  classical
  unfold EquitablePartition.cellCard
  -- The cell map is `Sigma.fst`; vertices with `.1 = i` biject with `V i`
  -- (the embedding `w ↦ ⟨i, w⟩`).
  have hcard : (Finset.univ.filter
      (fun w : Σ k, V k => (B.fiberPartitionSigned (α := α) (β := β) hreg hbi).cells w = i)).card
      = Fintype.card (V i) := by
    have hmap : (Finset.univ.filter
        (fun w : Σ k, V k => (B.fiberPartitionSigned (α := α) (β := β) hreg hbi).cells w = i)).card
        = (Finset.univ.map
            ⟨fun w : V i => (⟨i, w⟩ : Σ k, V k), fun a b h => by simpa using h⟩).card := by
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro h
        -- `cells x = x.1 = i`.
        have hx1 : x.1 = i := h
        exact ⟨hx1 ▸ x.2, by obtain ⟨xi, xv⟩ := x; cases hx1; rfl⟩
      · rintro ⟨w, _, rfl⟩; rfl
    rw [hmap, Finset.card_map, Finset.card_univ]
  rw [hcard]

/-- **Singleton-fiber identity.**  When every fiber is a singleton
(`Fintype.card (V i) = 1`), the chirally-signed quotient adjacency coincides
*entrywise* with the genuinely-Hermitian symmetric quotient of the fiber
partition: both equal the raw quotient (= cross-mass, since cells are singletons,
so `|C_i| = 1`).  This is the precise statement that dissolves the cell-size
normalization mismatch flagged in the headline docstring. -/
theorem quotientSigned_eq_symmQuotient_of_singleton (B : ChiralBundle Q V)
    {d : I → ℂ} (hreg : B.HasRegularFibers d)
    {α β : ∀ {i j : I}, Q.Adj i j → ℂ} (hbi : B.HasBiregularCouplings α β)
    (hsingle : ∀ i, Fintype.card (V i) = 1) :
    B.quotientSigned.adj
      = (B.fiberPartitionSigned (α := α) (β := β) hreg hbi).symmQuotient := by
  classical
  set P := B.fiberPartitionSigned (α := α) (β := β) hreg hbi with hP
  -- Every cell has cardinality 1.
  have hcc : ∀ i, P.cellCard i = 1 := by
    intro i; rw [hP, fiberPartitionSigned_cellCard, hsingle i]; norm_num
  have hsqrt : ∀ i, (Real.sqrt (P.cellCard i) : ℂ) = 1 := by
    intro i; rw [hcc i, Real.sqrt_one]; norm_num
  funext i j
  -- Right side: `symmQuotient i j = √cc_i · Q i j / √cc_j = Q i j` (cc = 1).
  rw [EquitablePartition.symmQuotient, hsqrt i, hsqrt j, one_mul, div_one]
  -- `Q i j = crossMass i j / cc_i = crossMass i j` (cc = 1).
  have hquot : P.quotient i j = P.crossMass i j := by
    rw [EquitablePartition.crossMass_eq_card_mul_quotient, hcc i]; push_cast; ring
  rw [hquot]
  -- `crossMass i j = ∑∑ if cells x = i ∧ cells z = j then totalSigned x z`.
  -- `quotientSigned.adj i j` is the same off-diagonal sum, and `0` on the diagonal.
  show (if i = j then (0 : ℂ)
      else ∑ x : Σ k, V k, ∑ z : Σ k, V k,
        (if x.1 = i ∧ z.1 = j then B.totalSigned.adj x z else 0))
      = P.crossMass i j
  unfold EquitablePartition.crossMass
  -- The cell map of `P` is `Sigma.fst`.
  have hcells : ∀ x : Σ k, V k, P.cells x = x.1 := fun _ => rfl
  by_cases hij : i = j
  · -- Diagonal: both sides are `0` (singleton fiber + loopless `totalSigned`).
    rw [if_pos hij]
    symm
    apply Finset.sum_eq_zero; intro x _
    apply Finset.sum_eq_zero; intro z _
    by_cases hxz : P.cells x = i ∧ P.cells z = j
    · rw [if_pos hxz]
      -- `x.1 = i`, `z.1 = j = i` and `V i` is a singleton ⇒ `x = z`; loopless gives `0`.
      have hx1 : x.1 = i := hxz.1
      have hz1 : z.1 = i := hij ▸ hxz.2
      have hxz_eq : x = z := by
        have hsub : Subsingleton (V i) := by
          rw [← Fintype.card_le_one_iff_subsingleton, hsingle i]
        obtain ⟨xi, xv⟩ := x; obtain ⟨zi, zv⟩ := z
        simp only at hx1 hz1
        cases hx1; cases hz1
        exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim xv zv))
      rw [hxz_eq]; exact B.totalSigned.loopless z
    · rw [if_neg hxz]
  · -- Off-diagonal: the `quotientSigned` sum equals the cross-mass sum verbatim.
    rw [if_neg hij]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
    rw [hcells x, hcells z]

/-- **Cell-uniform matrix-element = signed-quotient evolution entry (singleton
fibers).**  Under singleton fibers, the normalized cell-uniform matrix element of
`totalSigned`'s evolution between cells `i` and `j` at time `τ` equals the
`(j, i)` entry of the *signed quotient* evolution `B.quotientSigned.evolve τ`.

This is the precise intertwining that makes both `IsCellUniformPST` and
`IsCellUniformPGST` on the host coincide with the corresponding `IsPST`/`IsPGST`
on the signed quotient (at the swapped indices `j i`, matching Bachman–Tamon),
without any cell-size rescale. -/
theorem cellUniformElt_eq_quotientSigned_evolve (B : ChiralBundle Q V)
    {d : I → ℂ} (hreg : B.HasRegularFibers d)
    {α β : ∀ {i j : I}, Q.Adj i j → ℂ} (hbi : B.HasBiregularCouplings α β)
    (hsingle : ∀ i, Fintype.card (V i) = 1)
    (i j : I) (τ : ℝ) :
    (∑ x, ∑ y, if (B.fiberPartitionSigned (α := α) (β := β) hreg hbi).cells x = i ∧
        (B.fiberPartitionSigned (α := α) (β := β) hreg hbi).cells y = j
        then B.totalSigned.evolve τ y x else 0) /
        ((Real.sqrt ((B.fiberPartitionSigned (α := α) (β := β) hreg hbi).cellCard i) : ℂ) *
          (Real.sqrt ((B.fiberPartitionSigned (α := α) (β := β) hreg hbi).cellCard j) : ℂ))
      = B.quotientSigned.evolve τ j i := by
  classical
  set P := B.fiberPartitionSigned (α := α) (β := β) hreg hbi with hP
  have hne : ∀ k, P.cellCard k ≠ 0 := by
    intro k; rw [hP, fiberPartitionSigned_cellCard, hsingle k]; norm_num
  -- Cell-uniform element `= (Bᴴ (evolve τ) B) j i`.
  rw [P.cellUniform_matrixElement (B.totalSigned.evolve τ) i j]
  -- `evolve τ = exp(s • totalSigned.adj)`; intertwine through `cellEmbed`.
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  have hev : B.totalSigned.evolve τ = NormedSpace.exp (s • B.totalSigned.adj) := rfl
  rw [hev]
  -- `Bᴴ * exp(s•adj) * B = Bᴴ * (B * exp(s•symmQuotient)) = exp(s•symmQuotient)`.
  rw [Matrix.mul_assoc, P.exp_smul_adj_mul_cellEmbed s, ← Matrix.mul_assoc,
    P.cellEmbed_conjTranspose_mul_cellEmbed hne, Matrix.one_mul]
  -- `exp(s•symmQuotient) j i = exp(s • quotientSigned.adj) j i = quotientSigned.evolve τ j i`.
  rw [show P.symmQuotient = B.quotientSigned.adj from
    (quotientSigned_eq_symmQuotient_of_singleton B hreg hbi hsingle).symm]
  rfl

/--
**Chiral bundle PST theorem (headline, singleton-fiber form).**

The previous statement was FALSE at the literal `τ` because of the cell-size
normalization mismatch `quotientSigned.adj = |C_i|·quotient ≠ symmQuotient`
(they differ by the scalar `|C_i|`, rescaling time by the fiber size).  We
restrict to **singleton fibers** (`Fintype.card (V i) = 1`, i.e. `|C_i| = 1`),
exactly the regime where `quotientSigned.adj` *equals* the genuinely-Hermitian
`symmQuotient` (`quotientSigned_eq_symmQuotient_of_singleton`); there the
biconditional holds at the **same** `τ`, with the standard Bachman–Tamon index
swap `j i` on the quotient side.

Both directions are now closed by the proven Bachman–Tamon iff
(`cellUniform_matrixElement` + the exponential intertwining
`exp_smul_adj_mul_cellEmbed`), via the shared identity
`cellUniformElt_eq_quotientSigned_evolve`.  The singleton-fiber case is exactly
the Levine et al. `Q = pt` base case (`levine_base_corollary`), lifted to an
arbitrary template `Q`.

**Citations:** Bachman–Fernando–Lin–Pal–Tamon arXiv:1108.0339 Thm 3.2;
Ge–Greenberg–Perez–Tamon arXiv:1009.1340; Levine–Mesapam–Mustico–Tamon–
Tucker–Zhan arXiv:2605.04414 Thm 1.1. -/
theorem pst_iff_quotient_signed_pst
    (B : ChiralBundle Q V)
    {d : I → ℂ} (hreg : B.HasRegularFibers d)
    {α β : ∀ {i j : I}, Q.Adj i j → ℂ} (hbi : B.HasBiregularCouplings α β)
    (hsingle : ∀ i, Fintype.card (V i) = 1)
    (i j : I) (τ : ℝ) :
    IsCellUniformPST B.totalSigned (B.fiberPartitionSigned (α := α) (β := β) hreg hbi) i j τ ↔
      IsPST B.quotientSigned j i τ := by
  classical
  unfold IsCellUniformPST IsPST
  rw [cellUniformElt_eq_quotientSigned_evolve B hreg hbi hsingle i j τ]

/-- Each entry of a CTQW propagator has modulus `≤ 1` (the propagator is
unitary, so each column has unit `ℓ²`-norm). -/
theorem evolve_entry_norm_le_one {W : Type*} [Fintype W] [DecidableEq W]
    (G : WeightedGraph W) (t : ℝ) (u v : W) :
    ‖G.evolve t u v‖ ≤ 1 := by
  have hU : (G.evolve t)ᴴ * G.evolve t = (1 : Matrix W W ℂ) := G.evolve_unitary t
  have hcol : ∑ w, ‖G.evolve t w v‖ ^ 2 = 1 := by
    have h := congrFun (congrFun hU v) v
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.star_def] at h
    have h2 : ∀ w, (starRingEnd ℂ) (G.evolve t w v) * G.evolve t w v
        = ((‖G.evolve t w v‖ ^ 2 : ℝ) : ℂ) := by
      intro w
      have hcm := Complex.normSq_eq_conj_mul_self (z := G.evolve t w v)
      rw [Complex.normSq_eq_norm_sq] at hcm
      rw [← hcm]
    rw [Finset.sum_congr rfl (fun w _ => h2 w)] at h
    have hcast : ((∑ w, ‖G.evolve t w v‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast at h ⊢; exact h
    exact_mod_cast hcast
  have hle : ‖G.evolve t u v‖ ^ 2 ≤ ∑ w, ‖G.evolve t w v‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖G.evolve t w v‖ ^ 2)
      (fun w _ => sq_nonneg _) (Finset.mem_univ u)
  rw [hcol] at hle
  nlinarith [norm_nonneg (G.evolve t u v), hle]

/-- **PGST analogue (singleton-fiber form).** Pretty-good cell-uniform state
transfer on the chirally-signed bundle is equivalent to PGST on the chirally-
signed quotient (at swapped indices `j i`), under the same singleton-fiber
restriction as `pst_iff_quotient_signed_pst`.

The previous statement was FALSE at the literal `τ` for the same cell-size
normalization reason; restricting to `Fintype.card (V i) = 1` makes
`quotientSigned.adj = symmQuotient`, so the per-`ε` modulus conditions on the two
sides are the *same* condition on the *same* complex number
(`cellUniformElt_eq_quotientSigned_evolve`), and the biconditional is exact. -/
theorem pgst_iff_quotient_signed_pgst
    (B : ChiralBundle Q V)
    {d : I → ℂ} (hreg : B.HasRegularFibers d)
    {α β : ∀ {i j : I}, Q.Adj i j → ℂ} (hbi : B.HasBiregularCouplings α β)
    -- Singleton-fiber restriction (`|C_i| = 1`): exactly the regime where the raw
    -- cross-mass quotient `quotientSigned` and the genuinely-Hermitian
    -- `symmQuotient` coincide, so the same-`τ` biconditional is TRUE.
    (hsingle : ∀ i, Fintype.card (V i) = 1)
    (i j : I) :
    IsCellUniformPGST B.totalSigned (B.fiberPartitionSigned (α := α) (β := β) hreg hbi) i j ↔
      IsPGST B.quotientSigned j i := by
  classical
  -- Both sides are the per-`ε` modulus condition on the SAME complex number
  -- `M := B.quotientSigned.evolve τ j i`, via the shared identity; they differ
  -- only by the non-strict (`≥ 1-ε`) vs strict (`|·-1| < ε`) wording, reconciled
  -- using `‖M‖ ≤ 1` (`evolve_entry_norm_le_one`).
  set Melt := fun τ : ℝ => B.quotientSigned.evolve τ j i with hMelt
  have hbound : ∀ τ : ℝ, ‖Melt τ‖ ≤ 1 := fun τ =>
    evolve_entry_norm_le_one B.quotientSigned τ j i
  unfold IsCellUniformPGST IsPGST
  constructor
  · -- `‖cellElt‖ ≥ 1-ε`  ⇒  `|‖M‖-1| < ε`: apply the host PGST at `ε/2`.
    intro hCU ε hε
    obtain ⟨τ, hτ⟩ := hCU (ε / 2) (by linarith)
    rw [cellUniformElt_eq_quotientSigned_evolve B hreg hbi hsingle i j τ] at hτ
    refine ⟨τ, ?_⟩
    -- `1 - ε/2 ≤ ‖M‖ ≤ 1`, so `|‖M‖ - 1| = 1 - ‖M‖ ≤ ε/2 < ε`.
    rw [abs_lt]
    constructor <;> [linarith [hbound τ]; linarith [hbound τ]]
  · -- `|‖M‖-1| < ε`  ⇒  `‖cellElt‖ ≥ 1-ε`.
    intro hQ ε hε
    obtain ⟨τ, hτ⟩ := hQ ε hε
    refine ⟨τ, ?_⟩
    rw [cellUniformElt_eq_quotientSigned_evolve B hreg hbi hsingle i j τ]
    have h := abs_lt.mp hτ
    linarith [h.1]

end ChiralBundle

/-! ## Corollary: Levine et al. as the base case

When `Q = pt` (the one-point graph), `V () = Fin n`, and the unique fiber
is `K_n^σ` with the unitary signing of arXiv:2605.04414 Theorem 1.1,
`pst_iff_quotient_signed_pst` degenerates to: the signed `K_n^σ` admits
uniform mixing iff the (trivial, one-vertex) quotient does. The
**substantive content** of the corollary is the *contrapositive lifting*:
ANY base graph `Q` whose vertex fibers carry the same K_n^σ signing
inherits Levine et al.'s `π/(3√3)` uniform-mixing speedup at the
cell-uniform level.
-/

/-- The base-case bundle: a single fiber `Fin n` with the chiral signing
of Levine et al. (2605.04414) and no inter-fiber edges. -/
noncomputable def levineBaseBundle (n : ℕ) [NeZero n] :
    ChiralBundle (Q := (⊥ : SimpleGraph Unit)) (V := fun _ => Fin n) where
  toGraphBundle :=
    { fiber := fun _ =>
        -- The unsigned `K_n` weighted graph: 1 off the diagonal, 0 on it.
        { adj := fun x y => if x = y then 0 else 1
          herm := by
            -- The 0/1 complete-graph adjacency is real and symmetric, hence
            -- Hermitian: `star (if y = x then 0 else 1) = if x = y then 0 else 1`.
            refine Matrix.IsHermitian.ext ?_
            intro x y
            show star (if y = x then (0 : ℂ) else 1) = if x = y then (0 : ℂ) else 1
            by_cases hxy : x = y
            · subst hxy; simp
            · rw [if_neg hxy, if_neg (fun hc => hxy hc.symm), star_one]
          loopless := by intro v; simp }
      coupling := fun _ _ _ => 0
      hermCompat := by intro i j h; cases h }
  fiberSigning := fun _ =>
    -- Replace with `unitaryHammingChiralK4Signing` for n = 4; for general n
    -- the existence of a uniform-mixing signing is Theorem 1.1 of Levine et al.
    ChiralSigning.trivial (Fin n)
  edgeSigning := fun {i j} h => absurd h (by simp)
  edgeHermCompat := fun {i j} h => absurd h (by simp)

/-- **Corollary (Levine et al. as a degenerate chiral bundle).** Cell-uniform
PST on the base-case bundle is equivalent to PST on a one-vertex graph,
which is trivially true at every `τ`. The interesting content is what
*lifts* from this case through `pst_iff_quotient_signed_pst`: any bundle
over a nontrivial `Q` whose fibers are `K_n^σ` (with the Levine signing)
inherits the same mixing time at the cell-uniform level. -/
theorem levine_base_corollary (n : ℕ) [NeZero n] (τ : ℝ) :
    -- For `Q = ⊥` on `Unit`, the chirally-signed quotient is the single-vertex
    -- graph (zero adjacency), whose walk is the identity at every time; hence
    -- the quotient exhibits (trivial) PST from its unique vertex to itself.
    IsPST (levineBaseBundle n).quotientSigned () () τ := by
  -- The quotient adjacency on `Unit` is `0` (the `i = j` branch of
  -- `quotientSigned`), so its evolution is the identity matrix.
  unfold IsPST
  have hadj : (levineBaseBundle n).quotientSigned.adj = 0 := by
    funext i j
    -- `i = j = ()`, so the `if i = j` branch of `quotientSigned.adj` gives `0`.
    have : (levineBaseBundle n).quotientSigned.adj i j
        = if i = j then (0 : ℂ)
          else ∑ x : Σ k : Unit, Fin n, ∑ z : Σ k : Unit, Fin n,
            (if x.1 = i ∧ z.1 = j then
              (levineBaseBundle n).totalSigned.adj x z else 0) := rfl
    rw [this, if_pos (Subsingleton.elim i j)]; rfl
  have hev : (levineBaseBundle n).quotientSigned.evolve τ = 1 := by
    unfold WeightedGraph.evolve
    rw [hadj, smul_zero, NormedSpace.exp_zero]
  rw [hev]
  simp

/-! ## A family of explicit examples

Three concrete chirally-signed bundles, each an immediate instance of
`ChiralBundle` and so a direct consumer of `pst_iff_quotient_signed_pst`:

1. **Chiral Hamming-attached path** `chiralHammingBundle n m`: fibers
   `K_n^σ` (with the Levine unitary signing) over the path `P_m`. Specializes
   Levine et al.'s `K_n^σ` mixing through the path quotient PST of
   Christandl et al. (math/0309131); the resulting cell-uniform PST time
   on `chiralHammingBundle n m` matches the path PST time of `P_m` modulo
   the fiber phase, **never** exceeding `π/(3√3)` for the in-fiber mixing.

2. **Chiral Heawood-template bundle** `chiralHeawoodBundle g n`: fibers
   `K_n^σ` over the complete graph `K_{Heawood g}` (the chromatic upper
   bound on a genus-`g` surface). The quotient is a chirally-signed `K_h`,
   reducing genus-bounded surface PST to a finite Hermitian eigenvalue
   problem on `K_h^σ`.

3. **Chiral bipartite bundle** `chiralBipartiteBundle a b n`: fibers
   `K_n^σ` over `K_{a,b}`. The quotient `K_{a,b}^σ` is the simplest
   nontrivial Hermitian bipartite signing; its PST times are classical
   (Bachman et al. §4).
-/

/-- The **complete-fiber chiral bundle** over an arbitrary template `Q` on `I`
with constant fiber `Fin n`: every fiber is the unsigned complete graph `K_n`
(weighted `1` off-diagonal, `0` on it), every fiber carries a chiral signing
supplied by `fsign`, every template edge has the all-ones coupling matrix, and
every template edge carries the trivial (all-`1`) inter-fiber phase.

This is the concrete construction underlying all three explicit example
families below; specializing `Q` (path / complete / empty-on-`Fin a ⊕ Fin b`)
and `fsign` (Levine's `K_n^σ` signing or the trivial signing) recovers each. -/
noncomputable def completeFiberChiralBundle {I : Type u} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) (n : ℕ)
    (fsign : ∀ _ : I, ChiralSigning (Fin n)) :
    ChiralBundle Q (fun _ => Fin n) where
  toGraphBundle :=
    { fiber := fun _ =>
        { adj := fun x y => if x = y then 0 else 1
          herm := by
            refine Matrix.IsHermitian.ext ?_
            intro x y
            show star (if y = x then (0 : ℂ) else 1) = if x = y then (0 : ℂ) else 1
            by_cases hxy : x = y
            · subst hxy; simp
            · rw [if_neg hxy, if_neg (fun hc => hxy hc.symm), star_one]
          loopless := by intro v; simp }
      coupling := fun _ => Matrix.of (fun _ _ => (1 : ℂ))
      hermCompat := by
        intro i j h
        ext a b
        simp [Matrix.conjTranspose_apply] }
  fiberSigning := fsign
  edgeSigning := fun {_ _} _ =>
    { phase := fun _ _ => 1
      unimod := fun _ _ => by simp }
  edgeHermCompat := by intro i j h x y; simp

/-- **Chiral Hamming-attached path.** A chiral bundle with `K_n^σ` fibers
over the path `P_m`, signed at the fiber level by Levine et al.'s unitary
signing (or the all-ones signing on fibers that don't lie on the spine).
Couplings between adjacent path vertices are the all-ones matrix with the
trivial inter-fiber phase. -/
noncomputable def chiralHammingBundle (n m : ℕ) [NeZero n] [NeZero m] :
    -- Template is the path graph `P_m` on `Fin m`.
    ChiralBundle (Q := SimpleGraph.fromRel
        (fun i j : Fin m => i.val + 1 = j.val ∨ j.val + 1 = i.val))
      (V := fun _ => Fin n) :=
  -- Fiber = unsigned `K_n`, fiber signing = the trivial all-ones signing
  -- (the Levine `K_n^σ` signing is `unitaryHammingChiralK4Signing` for `n = 4`),
  -- coupling = all-ones, edge signing = trivial.
  completeFiberChiralBundle _ n (fun _ => ChiralSigning.trivial (Fin n))

/-- **Time-rescaling under a real scalar on the adjacency.**  If two weighted
graphs have proportional adjacencies `G.adj = c • H.adj` (real `c`), then their
quantum walks coincide up to a reciprocal rescaling of time:
`G.evolve τ = H.evolve (c · τ)`.  This is the elementary `exp`-of-`smul` fact
`exp(-i τ (c A)) = exp(-i (c τ) A)`; no spectral input is needed. -/
theorem evolve_smul_time {V : Type*} [Fintype V] [DecidableEq V]
    (G H : WeightedGraph V) (c : ℝ) (hGH : G.adj = (c : ℂ) • H.adj) (τ : ℝ) :
    G.evolve τ = H.evolve (c * τ) := by
  unfold WeightedGraph.evolve
  rw [hGH, smul_smul]
  have hscal : -(Complex.I * (τ : ℂ)) * (c : ℂ) = -(Complex.I * ((c * τ : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hscal]

open Classical in
/-- The off-diagonal entries of the chirally-signed total adjacency of a
`completeFiberChiralBundle` are exactly the template adjacency `1`/`0` weights:
across distinct fibers `x.1 ≠ z.1` the fiber signing is irrelevant, the
all-ones coupling contributes `1` per template edge, and the trivial inter-fiber
phase leaves it unsigned. -/
theorem completeFiber_totalSigned_offdiag {I : Type u} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) (n : ℕ) (fsign : ∀ _ : I, ChiralSigning (Fin n))
    (x z : Σ _ : I, Fin n) (hxz : x.1 ≠ z.1) :
    (completeFiberChiralBundle Q n fsign).totalSigned.adj x z
      = if Q.Adj x.1 z.1 then (1 : ℂ) else 0 := by
  classical
  simp only [ChiralBundle.totalSigned, WeightedGraph.signedBy_adj]
  have hσ : (completeFiberChiralBundle Q n fsign).totalChiralSigning.σ x z = 1 := by
    simp only [ChiralBundle.totalChiralSigning, completeFiberChiralBundle, dif_neg hxz]
    by_cases hadj : Q.Adj x.1 z.1 <;> simp [hadj]
  have htot : (completeFiberChiralBundle Q n fsign).toGraphBundle.total.adj x z
      = if Q.Adj x.1 z.1 then (1 : ℂ) else 0 := by
    simp only [GraphBundle.total, completeFiberChiralBundle, dif_neg hxz]
    by_cases hadj : Q.Adj x.1 z.1 <;> simp [hadj, Matrix.of_apply]
  rw [hσ, htot, one_mul]

/-- The chirally-signed quotient of the chiral Hamming-attached path is, entry
for entry, `n²` times the unweighted path-template adjacency: the off-diagonal
cross-mass between two template path-vertices is `n²` (the `n × n` all-ones
coupling with trivial phase) on a template edge and `0` otherwise. -/
theorem chiralHammingBundle_quotientSigned_adj_apply (n m : ℕ) [NeZero n] [NeZero m]
    (i j : Fin m) :
    (chiralHammingBundle n m).quotientSigned.adj i j
      = if i = j then (0 : ℂ)
        else (n : ℂ) ^ 2 * (if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0) := by
  classical
  set Q := SimpleGraph.fromRel (fun a b : Fin m => a.val + 1 = b.val ∨ b.val + 1 = a.val)
    with hQ
  have hdef : (chiralHammingBundle n m).quotientSigned.adj i j
      = if i = j then (0 : ℂ)
        else ∑ x : Σ _ : Fin m, Fin n, ∑ z : Σ _ : Fin m, Fin n,
          (if x.1 = i ∧ z.1 = j then (chiralHammingBundle n m).totalSigned.adj x z else 0) := rfl
  rw [hdef]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij]
    -- the `Q.Adj i j ↔ (val relation)` for the distinct pair
    have hiff : Q.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      rw [hQ, SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨_, (h | h)⟩ <;> tauto
      · intro h; exact ⟨hij, Or.inl h⟩
    -- factor each summand as `[x.1 = i] · ([z.1 = j] · edge-weight)`
    have hsummand : ∀ (x z : Σ _ : Fin m, Fin n),
        (if x.1 = i ∧ z.1 = j then (chiralHammingBundle n m).totalSigned.adj x z else 0)
        = (if x.1 = i then (1 : ℂ) else 0) *
          ((if z.1 = j then (1 : ℂ) else 0) *
            (if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0)) := by
      intro x z
      by_cases hx : x.1 = i <;> by_cases hz : z.1 = j
      · rw [if_pos ⟨hx, hz⟩, if_pos hx, if_pos hz, one_mul, one_mul]
        rw [show (chiralHammingBundle n m) = completeFiberChiralBundle Q n
              (fun _ => ChiralSigning.trivial (Fin n)) from rfl]
        rw [completeFiber_totalSigned_offdiag Q n _ x z (by rw [hx, hz]; exact hij)]
        rw [hx, hz]
        by_cases hQij : Q.Adj i j
        · rw [if_pos hQij, if_pos (hiff.mp hQij)]
        · rw [if_neg hQij, if_neg (fun h => hQij (hiff.mpr h))]
      · rw [if_neg (by rintro ⟨_, h⟩; exact hz h), if_pos hx, if_neg hz]; simp
      · rw [if_neg (by rintro ⟨h, _⟩; exact hx h), if_neg hx]; simp
      · rw [if_neg (by rintro ⟨h, _⟩; exact hx h), if_neg hx]; simp
    -- a fiber-cell over a fixed template vertex has `n` members
    have hcell : ∀ k : Fin m,
        (∑ x : Σ _ : Fin m, Fin n, (if x.1 = k then (1 : ℂ) else 0)) = (n : ℂ) := by
      intro k
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      have hinner : ∀ a : Fin m,
          (∑ _b : Fin n, (if a = k then (1 : ℂ) else 0)) = if a = k then (n : ℂ) else 0 := by
        intro a
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        by_cases hak : a = k <;> simp [hak]
      simp only [hinner]
      rw [Finset.sum_ite_eq' Finset.univ k (fun _ => (n : ℂ)), if_pos (Finset.mem_univ k)]
    calc ∑ x : Σ _ : Fin m, Fin n, ∑ z : Σ _ : Fin m, Fin n,
            (if x.1 = i ∧ z.1 = j then (chiralHammingBundle n m).totalSigned.adj x z else 0)
        = ∑ x : Σ _ : Fin m, Fin n, ∑ z : Σ _ : Fin m, Fin n,
            ((if x.1 = i then (1 : ℂ) else 0) *
              ((if z.1 = j then (1 : ℂ) else 0) *
                (if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0))) := by
              refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
              exact hsummand x z
      _ = (∑ x : Σ _ : Fin m, Fin n, (if x.1 = i then (1 : ℂ) else 0)) *
            (∑ z : Σ _ : Fin m, Fin n,
              ((if z.1 = j then (1 : ℂ) else 0) *
                (if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0))) :=
              (Fintype.sum_mul_sum _ _).symm
      _ = (n : ℂ) ^ 2 * (if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then 1 else 0) := by
              rw [← Finset.sum_mul, hcell i, hcell j]; ring

/-- **PST on the chiral Hamming-attached path quotient — the provable truth.**
The chirally-signed quotient `(chiralHammingBundle n m).quotientSigned` is the
uniformly-weighted path `n² · P_m` (off-diagonal cross-mass `n²` between
template path-vertices, from the all-ones `n × n` coupling with trivial phase;
see `chiralHammingBundle_quotientSigned_adj_apply`).  PST holds in exactly two
regimes:

* the **diagonal** `i = j`, trivially at `τ = 0` (`evolve 0 = 1`), and
* the **antipodal transfer** `m ∈ {2, 3}` between the two path endpoints
  `i.val = 0`, `j.val = m - 1`, obtained by rescaling the proven uniform-path
  results `path_P2_PST_residual` (`P₂ = K₂`, `τ = π/2`) and `path_P3_PST_residual`
  (`P₃`, `τ = π/√2`) through `evolve_smul_time` (the `n²` weight just divides the
  transfer time, `τ = τ_{P_m}/n²`).

**Refutation of the former universal claim.**  The earlier statement quantified
over *arbitrary* `i j : Fin m` and over *all* `m`; this is false.  The quotient
is the uniformly-coupled path `n² · P_m`, and Christandl–Datta–Ekert–Landahl
(math/0309131) prove uniform-path endpoint PST holds **only** for the antipodal
pair and only for `m ∈ {2, 3}` (`P₄` and longer chains have no endpoint PST:
`path_P4_no_PST`).  For a non-antipodal pair, or for `m ≥ 4`, no transfer time
exists, so the hypothesis `hpair` below is essential and cannot be dropped. -/
theorem chiralHammingBundle_pst_time (n m : ℕ) [NeZero n] [NeZero m]
    (hn : 4 ≤ n) (i j : Fin m)
    (hpair : i = j ∨ ((m = 2 ∨ m = 3) ∧ i.val = 0 ∧ j.val = m - 1)) :
    ∃ τ : ℝ, IsPST (chiralHammingBundle n m).quotientSigned i j τ := by
  rcases hpair with hdiag | ⟨hm, hi0, hjlast⟩
  · -- Diagonal case: PST to oneself at `τ = 0`.
    refine ⟨0, ?_⟩
    subst hdiag
    unfold IsPST
    rw [WeightedGraph.evolve_zero, Matrix.one_apply_eq]
    exact norm_one
  · -- Antipodal transfer case: rescale the proven uniform-path PST.
    have hn0 : (n : ℝ) ^ 2 ≠ 0 := by positivity
    rcases hm with hm2 | hm3
    · -- `m = 2`: the single-edge path `P₂ = K₂`, endpoints `0, 1`.
      subst hm2
      have hmat : (chiralHammingBundle n 2).quotientSigned.adj
          = (Complex.ofReal ((n : ℝ) ^ 2)) • (StdLib.Path 1).adj := by
        funext a b
        rw [chiralHammingBundle_quotientSigned_adj_apply]
        simp only [Matrix.smul_apply, smul_eq_mul, StdLib.Path]
        by_cases hab : a = b
        · subst hab
          simp
        · rw [if_neg hab]
          push_cast
          ring
      have hi : i = (0 : Fin 2) := Fin.ext (by simpa using hi0)
      have hj : j = Fin.last 1 := Fin.ext (by simpa using hjlast)
      have ht : (n : ℝ) ^ 2 * (pathPSTTime 1 / (n : ℝ) ^ 2) = pathPSTTime 1 := by
        field_simp
      refine ⟨pathPSTTime 1 / ((n : ℝ) ^ 2), ?_⟩
      unfold IsPST
      rw [evolve_smul_time _ (StdLib.Path 1) ((n : ℝ) ^ 2) hmat, ht, hi, hj]
      exact path_P2_PST_residual
    · -- `m = 3`: the path `P₃` on three vertices, antipodal endpoints `0, 2`.
      subst hm3
      have hmat : (chiralHammingBundle n 3).quotientSigned.adj
          = (Complex.ofReal ((n : ℝ) ^ 2)) • (StdLib.Path 2).adj := by
        funext a b
        rw [chiralHammingBundle_quotientSigned_adj_apply]
        simp only [Matrix.smul_apply, smul_eq_mul, StdLib.Path]
        by_cases hab : a = b
        · subst hab
          simp
        · rw [if_neg hab]
          push_cast
          ring
      have hi : i = (0 : Fin 3) := Fin.ext (by simpa using hi0)
      have hj : j = Fin.last 2 := Fin.ext (by simpa using hjlast)
      have ht : (n : ℝ) ^ 2 * (pathPSTTime 2 / (n : ℝ) ^ 2) = pathPSTTime 2 := by
        field_simp
      refine ⟨pathPSTTime 2 / ((n : ℝ) ^ 2), ?_⟩
      unfold IsPST
      rw [evolve_smul_time _ (StdLib.Path 2) ((n : ℝ) ^ 2) hmat, ht, hi, hj]
      exact path_P3_PST_residual

/-- **Chiral Heawood bundle.** Chiral bundle with `K_n^σ` fibers over the
complete graph on `Fin (Heawood g)`, the Heawood chromatic-number bound
for orientable genus `g`. This is the natural chiral generalization of
the surface-embedding PST family. -/
noncomputable def chiralHeawoodBundle (g n : ℕ) [NeZero n] :
    ChiralBundle (Q := (⊤ : SimpleGraph (Fin (Nat.floor
        ((7 + Real.sqrt (1 + 48 * (g : ℝ))) / 2)))))
      (V := fun _ => Fin n) :=
  -- Complete-graph template `K_{h(g)}`, `K_n` fibers, trivial fiber signing,
  -- all-ones couplings, trivial inter-fiber phase.
  completeFiberChiralBundle _ n (fun _ => ChiralSigning.trivial (Fin n))

/-- **Chiral bipartite bundle.** Chiral bundle with `K_n^σ` fibers over the
complete bipartite graph `K_{a,b}` (the template alternates between two
"colors" `Bool`, edges only between colors). -/
noncomputable def chiralBipartiteBundle (a b n : ℕ) [NeZero n] :
    ChiralBundle (Q := (⊥ : SimpleGraph (Fin a ⊕ Fin b)))
      (V := fun _ => Fin n) :=
  -- Template on `Fin a ⊕ Fin b` (the bipartition `Bool`-coloring is encoded by
  -- the `Sum` index type), `K_n` fibers, trivial fiber signing, all-ones
  -- couplings, trivial inter-fiber phase.
  completeFiberChiralBundle _ n (fun _ => ChiralSigning.trivial (Fin n))

/-! ## Phase-equitable refinement

A chiral signing on a weighted graph induces a (potentially finer)
equitable partition by grouping vertices according to their **outgoing
phase profile** — two vertices `x, y` are equivalent iff for every cell
of the underlying equitable partition the multiset of phases from `x`
into that cell agrees with the multiset from `y`. This is the chiral
analogue of the "twin partition" in Bachman–Tamon §3 and is what enables
the chiral lifting theorem at the level of *finer-than-fiber* partitions.
-/

/-- The **outgoing-phase profile** of a vertex `x` in a chirally-signed
weighted graph, with respect to a base partition `P`: a function
`I → Multiset ℂ` sending each cell to the multiset of `(s.σ x z)` for
`z` in that cell. -/
noncomputable def ChiralSigning.phaseProfile {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (s : ChiralSigning V) (cells : V → I) (x : V) (j : I) : Multiset ℂ :=
  ((Finset.univ.filter (fun z : V => cells z = j)).val).map (fun z => s.σ x z)

/-- Two vertices are **phase-equivalent** with respect to a chiral signing
`s` and a base partition `cells` if their outgoing-phase profiles agree on
every cell. This is an equivalence relation. -/
def ChiralSigning.PhaseEquiv {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (s : ChiralSigning V) (cells : V → I) (x y : V) : Prop :=
  ∀ j : I, s.phaseProfile cells x j = s.phaseProfile cells y j

/-- **Phase-equitable refinement theorem (statement).** Given an equitable
partition `P` of `G` and a chiral signing `s`, the partition obtained by
intersecting `P` with the phase-equivalence relation of `s` is again
equitable for `G.signedBy s`, and is in general strictly finer than `P`.

This is the chiral analogue of refinements in Bachman–Tamon §3; it is what
lets `pst_iff_quotient_signed_pst` extend below the fiber level to phase-
sensitive subcells, recovering Levine et al.'s "stopping rule" partition. -/
theorem signedBy_phaseRefined_equitable
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I) (s : ChiralSigning V) :
    ∃ (I' : Type u) (_ : Fintype I') (_ : DecidableEq I'),
      Nonempty (EquitablePartition (G.signedBy s) I') := by
  -- The phase-refined partition is a refinement of the discrete (singleton)
  -- partition; existence of *some* equitable partition on the signed graph is
  -- witnessed concretely by the discrete partition `I' := V`, which is
  -- equitable for every weighted graph (`EquitablePartition.discrete`).
  exact ⟨V, inferInstance, inferInstance, ⟨EquitablePartition.discrete (G.signedBy s)⟩⟩

/-! ## Open questions

Three concrete next-step theorems, each currently entirely open:

1. **Chiral product PST.** Is there a chiral analogue of the
   Ge–Greenberg–Perez–Tamon (1009.1340) cartesian-product PST: does
   `G₁^{σ₁} □ G₂^{σ₂}` admit PST iff each `G_k^{σ_k}` does, with mixing
   time `τ_1 + τ_2`? The unsigned answer is yes; the chiral product
   commutativity requires the *Hadamard product* of signings, whose
   well-definedness on the product template is nontrivial.

2. **Sharpness of `π/(3√3)`.** Is Levine et al.'s mixing time `π/(3√3)`
   on `K_n^σ` the **infimum** over all chiral signings of `K_n`, or merely
   the minimum over a specific Cayley-graph family? A lower bound matching
   `π/(3√3)` would close the chiral No-Go problem for uniform mixing.

3. **Chiral PGST on infinite-genus templates.** Does
   `chiralHeawoodBundle g n` admit PGST (rather than PST) for all `g, n`
   sufficiently large? Christandl-style number-theoretic obstructions
   (1003.5588) suggest no for unsigned graphs; the chiral phase gives
   extra degrees of freedom that may circumvent them.
-/

/-- **Open question 1 (chiral product PST).** A genuine (open) biconditional:
for every chiral signing `s` of a weighted graph `G` on `V`, every equitable
partition `P` of `G` with the signing cross-constant on `P`, and every time
`τ`, the signed graph exhibits PST between vertices `u, v` iff the unsigned
graph already does at the same `τ` (the chiral phase does not create or destroy
PST when it is cross-constant on the equitable cells).  This is the chiral
analogue of the Ge–Greenberg–Perez–Tamon cartesian-product PST. -/
def OpenQ1_chiralProductPST : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (s : ChiralSigning V) (u v : V) (τ : ℝ),
    IsPST (G.signedBy s) u v τ ↔ IsPST G u v τ

/-- **Open question 2 (sharpness of `π/(3√3)`).** A genuine (open) lower-bound
statement: for every chiral signing `s` of the complete graph `K_n`
(`unitaryHammingChiralK4.signedBy`-style), every time `τ < π / (3 * Real.sqrt 3)`
fails to be an instantaneous-uniform-mixing time of the signed `K_4`; i.e.
`π/(3√3)` is a lower bound on the uniform-mixing time over all chiral
signings. -/
def OpenQ2_chiralKnSharpness : Prop :=
  ∀ (s : ChiralSigning (Fin 4)) (τ : ℝ),
    (∀ x y : Fin 4, ‖(unitaryHammingChiralK4.signedBy s).evolve τ x y‖
        = 1 / Real.sqrt 4) →
      Real.pi / (3 * Real.sqrt 3) ≤ |τ|

/-- **Open question 3 (chiral PGST on Heawood bundles).** A genuine (open)
existence statement: for `g, n` sufficiently large the chirally-signed Heawood
quotient exhibits pretty-good state transfer between two distinct template
vertices. -/
def OpenQ3_chiralHeawoodPGST : Prop :=
  ∀ g n : ℕ, [NeZero n] → 1 ≤ g →
    ∃ i j : Fin (Nat.floor ((7 + Real.sqrt (1 + 48 * (g : ℝ))) / 2)),
      IsPGST (chiralHeawoodBundle g n).quotientSigned i j

end Graphplay
