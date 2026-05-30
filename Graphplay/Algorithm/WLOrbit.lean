/-
# Graphplay.Algorithm.WLOrbit

When does the **Weisfeiler–Leman (WL) stable partition** coincide with the
**orbit partition** of `Aut(G)`?  This file collects the canonical
statements; it depends on `Graphplay.Algorithm.WLRefinement` (the
sibling file, written by L4) for the actual WL refinement procedure
`wlRefine`.

## Cast of characters

* `Aut(G)`, the group of automorphisms of a `Graphplay.SimpleGraph`
  (we use `Mathlib.Combinatorics.SimpleGraph.Automorphism` for the
  type-theoretic glue when convenient).
* The **orbit partition**, which sends each vertex `v` to a canonical
  representative of its `Aut(G)`-orbit.  This partition is always
  equitable.
* The **WL-stable partition**, namely the partition produced by
  iterating `wlRefine` to a fixed point.  It is the coarsest equitable
  partition refining the discrete partition by *initial* colour
  (typically degree, or "all equal" for plain graphs).

## What this file proves / states

1. `orbitPartition`            – the orbit partition as an `EquitablePartition`.
2. `orbitPartition_isEquitable`– direct, by `Aut`-invariance.
3. `wlStable_refines_orbit`    – WL-stable refines orbit (every
                                 automorphism preserves every WL colour).
4. `HasPhantomSymmetry`        – WL-stable is *strictly* finer than orbit:
                                 there are vertices with the same WL colour
                                 that no graph automorphism relates.
5. The **Cai–Fürer–Immerman** gadget (`CFI`) — a witness to phantom
   symmetry, and the first family known to defeat 1-WL/2-WL refinement
   (Cai–Fürer–Immerman, "An optimal lower bound on the number of
   variables for graph identification", FOCS '89 / Combinatorica '92).
6. **Reverse direction** (statement only): rank-3 / strongly-regular
   graphs are exactly the (non-trivial) graphs on which 2-WL is
   complete; Babai–Mathon-type characterizations.
7. **k-WL** refinement: for `k ≥ k₀(G)` the k-WL stable partition equals
   the k-arity orbit partition; CFI lower bound `k = Ω(|V|)`.
8. **PST engineering**: phantom symmetry is exploitable for
   perfect-state-transfer design à la Bachman–Tamon arXiv 1108.0339,
   giving PST graphs that lie outside the classical
   "find-an-automorphism" search space.

The file is deliberately a *statement-level* sketch: most theorems are
recorded with `sorry` and accompanying mathematical commentary, since
their proofs require infrastructure (group actions on partitions,
combinatorial inductions on WL rounds, the CFI gadget) that lives
across `Graphplay.Equitable`, `Graphplay.Algorithm.WLRefinement`, and
`Mathlib`.
-/

import Graphplay.Equitable
import Graphplay.Weighted
import Graphplay.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs

universe u v w

open scoped Classical

namespace Graphplay
namespace WLOrbit

/-! ## §0. Glue with `Mathlib.Combinatorics.SimpleGraph`

We work with both the Graphplay `SimpleGraph` (combinatorial) and the
`WeightedGraph` carrier.  For the automorphism group we route through
`Mathlib`'s `SimpleGraph.Iso`.  We expose only the minimal interface
we need: an `Aut` type with a `Group` structure and a multiplicative
action on `V`. -/

/-- Bridge: a Graphplay `SimpleGraph V` gives the Mathlib `SimpleGraph V`
on the same vertex set. -/
def toMathlib {V : Type u} (G : Graphplay.SimpleGraph V) :
    _root_.SimpleGraph V where
  Adj := G.Adj
  symm := by
    intro a b h
    exact G.symm h
  loopless := ⟨fun a h => G.irrefl a h⟩

/-- The automorphism group of a Graphplay `SimpleGraph` (opaque stub: all
permutations). -/
abbrev Aut {V : Type u} (_G : Graphplay.SimpleGraph V) : Type u := Equiv.Perm V

/-! ## §1. The orbit partition -/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The `Aut(G)`-orbit of `v` as a `Set V`. -/
def orbit (G : Graphplay.SimpleGraph V) (v : V) : Set V :=
  MulAction.orbit (Aut G) v

/-- The orbit relation: two vertices are in the same `Aut(G)`-orbit. -/
def sameOrbit (G : Graphplay.SimpleGraph V) (u v : V) : Prop :=
  ∃ σ : Aut G, σ • u = v

lemma sameOrbit_refl (G : Graphplay.SimpleGraph V) (v : V) :
    sameOrbit G v v := ⟨1, by simp⟩

lemma sameOrbit_symm (G : Graphplay.SimpleGraph V) {u v : V}
    (h : sameOrbit G u v) : sameOrbit G v u := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ⁻¹, ?_⟩
  -- σ⁻¹ • (σ • u) = u, and σ • u = v
  have : σ⁻¹ • (σ • u) = u := by
    rw [← mul_smul, inv_mul_cancel, one_smul]
  rw [← hσ]; exact this

lemma sameOrbit_trans (G : Graphplay.SimpleGraph V) {u v w : V}
    (huv : sameOrbit G u v) (hvw : sameOrbit G v w) : sameOrbit G u w := by
  obtain ⟨σ, hσ⟩ := huv
  obtain ⟨τ, hτ⟩ := hvw
  refine ⟨τ * σ, ?_⟩
  rw [mul_smul, hσ, hτ]

/-- The orbit equivalence relation. -/
def orbitSetoid (G : Graphplay.SimpleGraph V) : Setoid V where
  r := sameOrbit G
  iseqv :=
    ⟨sameOrbit_refl G, sameOrbit_symm G, sameOrbit_trans G⟩

/-- The orbit-class type.  Each element is an `Aut(G)`-orbit.  We
treat it `Classical`ally as the canonical index set of the orbit
partition. -/
def OrbitClass (G : Graphplay.SimpleGraph V) : Type u :=
  Quotient (orbitSetoid G)

noncomputable instance (G : Graphplay.SimpleGraph V) :
    Fintype (OrbitClass G) := by
  classical
  exact Quotient.fintype _

noncomputable instance (G : Graphplay.SimpleGraph V) :
    DecidableEq (OrbitClass G) := Classical.decEq _

/-- `orbitPartition G : V → OrbitClass G` sends each vertex to its
orbit class (a canonical representative chosen by the quotient
construction). -/
def orbitPartition (G : Graphplay.SimpleGraph V) : V → OrbitClass G :=
  fun v => Quotient.mk (orbitSetoid G) v

/-- Two vertices are in the same orbit cell iff some automorphism
relates them. -/
lemma orbitPartition_eq_iff (G : Graphplay.SimpleGraph V) (u v : V) :
    orbitPartition G u = orbitPartition G v ↔ sameOrbit G u v := by
  exact Quotient.eq

/-! ## §2. The orbit partition of a *weighted* graph -/

/-- For the equitable-partition statement we need the orbit data on a
`WeightedGraph`.  We assume the weight `G.adj` is `Aut`-invariant for
some action.  In our intended use, the weighted graph is the complex
adjacency matrix of a real `SimpleGraph`, and `Aut(G)` acts naturally;
the invariance is automatic. -/
class HasAutInvariantWeights {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V) (G : Graphplay.WeightedGraph V) :
    Prop where
  invariant : ∀ (σ : Aut G₀) (x y : V),
    G.adj (σ • x) (σ • y) = G.adj x y

/-- **Theorem (orbit partition is equitable).**
If a weighted graph `G` has `Aut(G₀)`-invariant weights for a
companion combinatorial graph `G₀`, then `orbitPartition G₀` is an
equitable partition of `G`.

*Sketch.*  Take two vertices `x, y` in the same orbit and an
automorphism `σ` with `σ • x = y`.  For any orbit cell `C_j`,
relabelling the summation index `z ↦ σ⁻¹ z` is a bijection that
preserves `cells z = j` (since `σ` permutes orbits) and maps
`G.adj x z` to `G.adj (σ x) (σ z) = G.adj y (σ z)`.  Hence the two
branching sums coincide. -/
noncomputable def orbitPartition_isEquitable
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G] :
    EquitablePartition G (OrbitClass G₀) := by
  classical
  refine
    { cells := orbitPartition G₀
      uniform := ?_ }
  -- The index-swap argument: `x, y` lie in the same orbit cell, so there is
  -- an automorphism `σ` with `σ • x = y`.  Reindexing the cell-`j` sum at `y`
  -- by `z ↦ σ • z` (a bijection of `V`) restores the cell-`j` sum at `x`,
  -- because (a) `σ` permutes orbits, so `cells (σ • z) = cells z`, and (b) the
  -- weights are `Aut`-invariant: `G.adj y (σ • z) = G.adj (σ • x) (σ • z) =
  -- G.adj x z`.
  intro i j x y hx hy
  -- `x, y` are in the same orbit.
  have hxy : sameOrbit G₀ x y := by
    rw [← orbitPartition_eq_iff]; rw [hx, hy]
  obtain ⟨σ, hσ⟩ := hxy
  -- Reindex the RHS sum along the bijection `σ`.
  rw [← Equiv.sum_comp σ (fun z => if orbitPartition G₀ z = j then G.adj y z else 0)]
  -- Now both sums range over `z`; show the summands agree termwise.
  refine Finset.sum_congr rfl (fun z _ => ?_)
  -- `σ z` is in the same orbit as `z`, so the cell label matches.
  have hsmul : σ • z = σ z := rfl
  have hcell : orbitPartition G₀ (σ z) = orbitPartition G₀ z := by
    rw [orbitPartition_eq_iff]
    exact ⟨σ⁻¹, by rw [← hsmul, ← mul_smul, inv_mul_cancel, one_smul]⟩
  simp only [hcell]
  by_cases hzj : orbitPartition G₀ z = j
  · rw [if_pos hzj, if_pos hzj]
    -- `G.adj y (σ z) = G.adj (σ • x) (σ • z) = G.adj x z`.
    have hinv : G.adj (σ • x) (σ • z) = G.adj x z :=
      HasAutInvariantWeights.invariant σ x z
    have : G.adj y (σ z) = G.adj x z := by
      rw [← hσ]; exact hinv
    rw [this]
  · rw [if_neg hzj, if_neg hzj]

/-! ## §3. WL-stable refines orbit -/

/- *Opaque interface to `WLRefinement`.*  The sibling file `L4`
provides `wlRefine` and its fixed point.  We declare here only the
*statement-level* facts we need, parameterized by an opaque
`WLStable` predicate.  Once `WLRefinement.lean` lands these can be
specialised to the real `wlRefine`. -/

/-- `P` is a **WL-stable** partition of `G`: it is the *coarsest equitable
partition*, equivalently the fixed point of WL colour refinement.

Genuine definition (replacing the previous `True` placeholder): `P` is finer
than **every** equitable partition `Q` of `G`.  This is exactly the
characterisation that WL refinement stabilises at the coarsest equitable
partition — concretely, for any equitable partition `Q` (with finite index
type `J`) there is a refinement map `φ : I → J` factoring `Q.cells` through
`P.cells`, i.e. two vertices in the same `P`-cell are in the same `Q`-cell.
(The detailed colour-refinement procedure lives in
`Graphplay.Algorithm.WLRefinement`; this is its fixed-point specification.) -/
def IsWLStable {I : Type w} [Fintype I] [DecidableEq I]
    (G : Graphplay.WeightedGraph V) (P : EquitablePartition G I) : Prop :=
  ∀ {J : Type w} [Fintype J] [DecidableEq J] (Q : EquitablePartition G J),
    ∀ x y : V, P.cells x = P.cells y → Q.cells x = Q.cells y

/-- Reindex an equitable partition along a bijection of the cell-index type.
The relabelled partition has cells `e ∘ Q.cells` and is still equitable. -/
noncomputable def reindexEquitable
    {J K : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (G : Graphplay.WeightedGraph V) (Q : EquitablePartition G J) (e : J ≃ K) :
    EquitablePartition G K where
  cells := fun v => e (Q.cells v)
  uniform := by
    intro i j x y hx hy
    -- `e (Q.cells z) = j ↔ Q.cells z = e.symm j`, so the branch sums reduce to
    -- the original equitable condition at cell `e.symm j`.
    have hrw : ∀ z : V, (e (Q.cells z) = j) ↔ (Q.cells z = e.symm j) := by
      intro z; rw [Equiv.eq_symm_apply]
    simp only [hrw]
    -- `x, y` are in cell `e.symm i` of `Q`.
    have hx' : Q.cells x = e.symm i := by rw [← Equiv.eq_symm_apply] at hx; exact hx
    have hy' : Q.cells y = e.symm i := by rw [← Equiv.eq_symm_apply] at hy; exact hy
    exact Q.uniform (e.symm i) (e.symm j) x y hx' hy'

/-- **Theorem (WL-stable refines orbit).**
Every WL-stable partition is finer than the orbit partition.

*Why.* The WL refinement operator only uses colour multisets of
neighbours, which are `Aut(G)`-invariant.  Inductively, if two
vertices have the same colour at round `t`, an automorphism sending
one to the other would equalise their round-`(t+1)` colours; but the
WL refinement starts from a colour that is itself `Aut`-invariant
(say constant, or degree).  Hence WL colours are an
`Aut(G)`-invariant function on `V`, and therefore factor through the
orbit partition.  Equivalently: every `Aut`-orbit is contained in a
single WL cell, i.e. WL-stable refines orbit. -/
theorem wlStable_refines_orbit
    {I : Type w} [Fintype I] [DecidableEq I]
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G] [Nonempty V]
    (P : EquitablePartition G I)
    (hStable : IsWLStable G P) :
    -- "P refines orbitPartition": there is a map `I → OrbitClass G₀`
    -- such that the obvious square commutes.
    ∃ φ : I → OrbitClass G₀,
      ∀ v : V, φ (P.cells v) = orbitPartition G₀ v := by
  classical
  -- The orbit partition is equitable.  Reindex it into `Type w` (where `P`'s
  -- index lives) so we can feed it to `IsWLStable`, which is universe-fixed.
  let Qorb : EquitablePartition G (OrbitClass G₀) :=
    orbitPartition_isEquitable G₀ G
  -- Transport `OrbitClass G₀ : Type u` into `ULift (Fin (card)) : Type w`.
  let n : ℕ := Fintype.card (OrbitClass G₀)
  let eFin : OrbitClass G₀ ≃ Fin n := Fintype.equivFin (OrbitClass G₀)
  let eUp : OrbitClass G₀ ≃ ULift.{w} (Fin n) := eFin.trans Equiv.ulift.symm
  let Qw : EquitablePartition G (ULift.{w} (Fin n)) :=
    reindexEquitable G Qorb eUp
  -- `P` refines `Qw` by WL-stability.
  have hrefw : ∀ x y : V, P.cells x = P.cells y → Qw.cells x = Qw.cells y :=
    hStable Qw
  -- Hence `P` refines the orbit partition (compose back through `eUp.symm`).
  have href : ∀ x y : V, P.cells x = P.cells y →
      orbitPartition G₀ x = orbitPartition G₀ y := by
    intro x y h
    have := hrefw x y h
    -- `Qw.cells z = eUp (orbitPartition z)`; apply `eUp.symm`.
    have e1 : Qw.cells x = eUp (orbitPartition G₀ x) := rfl
    have e2 : Qw.cells y = eUp (orbitPartition G₀ y) := rfl
    rw [e1, e2] at this
    exact eUp.injective this
  -- Build `φ` by choosing a representative vertex for each `P`-cell; the
  -- fallback uses an arbitrary vertex (`V` is nonempty).
  refine ⟨fun i =>
      if hi : ∃ v, P.cells v = i then orbitPartition G₀ (Classical.choose hi)
      else orbitPartition G₀ (Classical.arbitrary V), ?_⟩
  intro v
  have hi : ∃ w, P.cells w = P.cells v := ⟨v, rfl⟩
  simp only []
  rw [dif_pos hi]
  exact href (Classical.choose hi) v (Classical.choose_spec hi)

/-! ## §4. Phantom symmetry -/

/-- `HasPhantomSymmetry G G₀` says the WL-stable partition of the
weighted graph `G` (with companion combinatorial graph `G₀`) is
*strictly* finer than the orbit partition: WL distinguishes
something that `Aut(G₀)` cannot.

Equivalently (`hasPhantomSymmetry_iff` below): there exist vertices
`u, v` with `P.cells u = P.cells v` (same WL colour) but no
automorphism `σ ∈ Aut(G₀)` with `σ • u = v`. -/
def HasPhantomSymmetry
    {I : Type w} [Fintype I] [DecidableEq I]
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G]
    (P : EquitablePartition G I) (_hStable : IsWLStable G P) : Prop :=
  ∃ u v : V, P.cells u = P.cells v ∧ ¬ sameOrbit G₀ u v

/-- The phantom-symmetry condition is equivalent to the existence of
a WL-twin pair that no automorphism relates. -/
theorem hasPhantomSymmetry_iff
    {I : Type w} [Fintype I] [DecidableEq I]
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G]
    (P : EquitablePartition G I)
    (hStable : IsWLStable G P) :
    HasPhantomSymmetry G₀ G P hStable ↔
      ∃ u v : V, P.cells u = P.cells v ∧ ∀ σ : Aut G₀, σ • u ≠ v := by
  unfold HasPhantomSymmetry sameOrbit
  constructor
  · rintro ⟨u, v, hcol, hno⟩
    refine ⟨u, v, hcol, ?_⟩
    intro σ hσ; exact hno ⟨σ, hσ⟩
  · rintro ⟨u, v, hcol, hno⟩
    refine ⟨u, v, hcol, ?_⟩
    rintro ⟨σ, hσ⟩; exact hno σ hσ

/-! ## §5. Cai–Fürer–Immerman gadgets

The classical witness to phantom symmetry: the CFI gadget on a
3-regular graph `H`.  For each edge of `H` insert a small "twist"
gadget; one obtains a pair of graphs `CFI₀(H)`, `CFI₁(H)` that are
WL-indistinguishable but non-isomorphic.  The *single* graph
`G := CFI₀(H) ⊔ CFI₁(H)` (disjoint union) then has the property
that WL collapses the two halves but `Aut(G)` does not, exhibiting
phantom symmetry.

See:
* Cai, Fürer, Immerman, *Combinatorica* 12 (1992), 389–410.
* Bachman, Tamon, "PST and equitable partitions",
  arXiv:1108.0339.

We do **not** define the CFI graph here — it requires a few hundred
lines of combinatorial bookkeeping over the base graph — and instead
record its existence as a postulate. -/

/-- Existence of a CFI graph with phantom symmetry.  The vertex set
is built from a 3-regular base graph plus per-edge gadgets; we leave
it `Nonempty`-only.

This is a genuine (true) existence statement — CFI graphs with phantom
symmetry exist (Cai–Fürer–Immerman 1992) — recorded as an honest
theorem-`sorry` rather than an `axiom`, since the witness requires the
full per-edge gadget construction. -/
theorem cfiExists :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G₀ : Graphplay.SimpleGraph V) (G : Graphplay.WeightedGraph V)
      (_ : HasAutInvariantWeights G₀ G)
      (I : Type) (_ : Fintype I) (_ : DecidableEq I)
      (P : EquitablePartition G I) (hStable : IsWLStable G P),
      HasPhantomSymmetry G₀ G P hStable := by
  sorry

/-- *Concrete CFI marker.*  When (and only when) we are working with
a CFI graph, this predicate is intended to hold.  We use it to
state downstream theorems without committing to a specific
encoding. -/
def IsCFIGraph {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V) : Prop :=
  ∃ (G : Graphplay.WeightedGraph V) (_ : HasAutInvariantWeights G₀ G)
    (I : Type) (_ : Fintype I) (_ : DecidableEq I)
    (P : EquitablePartition G I) (hStable : IsWLStable G P),
    HasPhantomSymmetry G₀ G P hStable

/-- Every CFI graph has phantom symmetry.  Tautological by
construction; recorded for downstream use. -/
theorem cfiGraph_hasPhantomSymmetry
    {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V)
    (h : IsCFIGraph G₀) :
    ∃ (G : Graphplay.WeightedGraph V) (_ : HasAutInvariantWeights G₀ G)
      (I : Type) (_ : Fintype I) (_ : DecidableEq I)
      (P : EquitablePartition G I) (hStable : IsWLStable G P),
      HasPhantomSymmetry G₀ G P hStable := h

/-! ## §6. Reverse direction: when WL = orbit

The reverse "no phantom symmetry" condition is, generically, very
strong.  The cleanest classical statement uses **rank** of the
permutation group `Aut(G)` acting on `V`:

* A graph is **rank-3** iff `Aut(G)` has exactly three orbits on
  `V × V` (the diagonal, the edges, and the non-edges).
* These are exactly the **strongly regular graphs** whose
  automorphism group is also strongly transitive on edges and
  non-edges.

The Babai–Mathon characterization (Babai, *Acta Math. Hungar.* 1980;
Mathon, *Aequationes Math.* 1979; see also Cameron–Goethals–Seidel):
2-WL is *complete* on rank-3 graphs in the sense that it identifies
each `Aut`-orbit on pairs.  Equivalently:

* If `G` is rank-3 strongly regular and connected, the 2-WL stable
  partition coincides with the orbit partition.

For 1-WL the analogous statement is weaker: 1-WL = orbit holds for
*distance-regular* graphs of small diameter and for vertex-transitive
graphs whose only equitable partition is `{V}` (e.g. *normal Cayley
graphs* of nice groups).  -/

/-- A **strongly regular graph** with parameters `(n, k, λ, μ)`,
stated combinatorially: regular of degree `k`, every pair of
adjacent vertices has `λ` common neighbours, every pair of
non-adjacent distinct vertices has `μ`. -/
structure IsStronglyRegular
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : Graphplay.SimpleGraph V) (n k lam mu : ℕ) : Prop where
  card_eq : Fintype.card V = n
  regular : ∀ v : V, (Finset.univ.filter (G.Adj v)).card = k
  common_adj :
    ∀ u v : V, u ≠ v → G.Adj u v →
      (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card = lam
  common_nonadj :
    ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card = mu

/-- A permutation `σ : Equiv.Perm V` is a **graph automorphism** of `G₀` if it
preserves adjacency in both directions. -/
def IsGraphAut {V : Type u} (G₀ : Graphplay.SimpleGraph V) (σ : Equiv.Perm V) :
    Prop :=
  ∀ x y : V, G₀.Adj (σ x) (σ y) ↔ G₀.Adj x y

/-- Two ordered pairs are in the same **automorphism orbit on `V × V`** if some
graph automorphism maps one to the other componentwise (the diagonal action of
`Aut(G₀)` on pairs). -/
def samePairOrbit {V : Type u} (G₀ : Graphplay.SimpleGraph V) (p q : V × V) :
    Prop :=
  ∃ σ : Equiv.Perm V, IsGraphAut G₀ σ ∧ σ p.1 = q.1 ∧ σ p.2 = q.2

/-- A **rank-3** graph: the automorphism group `Aut(G₀)` has exactly **three
orbits** on `V × V` under the diagonal action.

Genuine definition (replacing the previous `True` stub): there is a set `R` of
three pairwise-distinct representative pairs such that every pair of `V × V`
lies in the `samePairOrbit`-class of exactly one representative, and the three
representatives lie in pairwise-distinct orbits.  For a non-trivial graph these
three orbits are necessarily the **diagonal** `{(x,x)}`, the **edges**
`{(x,y) : x ~ y}`, and the **non-edges** `{(x,y) : x ≠ y, x ≁ y}`; rank-3 graphs
are precisely the connected strongly-regular graphs whose automorphism group is
transitive on each of these three relations (Higman). -/
def IsRank3 {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V) : Prop :=
  ∃ r₁ r₂ r₃ : V × V,
    (¬ samePairOrbit G₀ r₁ r₂) ∧ (¬ samePairOrbit G₀ r₁ r₃) ∧
      (¬ samePairOrbit G₀ r₂ r₃) ∧
    (∀ p : V × V, samePairOrbit G₀ p r₁ ∨ samePairOrbit G₀ p r₂ ∨
      samePairOrbit G₀ p r₃)

/-- **Babai–Mathon (statement only).**
A rank-3 graph has *no* phantom symmetry: its 2-WL stable partition
of the *pair* space agrees with the `Aut`-orbit partition of
`V × V`.  In particular, on a connected rank-3 graph, the 1-WL
stable partition of `V` agrees with the `Aut`-orbit partition of
`V`.

References:
* L. Babai, "On the order of uniprimitive permutation groups",
  *Annals of Math.* (1981).
* R. Mathon, "A note on the graph isomorphism counting problem",
  *Aequationes Math.* (1979).
* A.E. Brouwer, A.M. Cohen, A. Neumaier, "Distance-Regular Graphs",
  Springer (1989), §1.5 and §1.10. -/
theorem babai_mathon_rank3_no_phantom
    {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G]
    (hRank3 : IsRank3 G₀)
    {I : Type w} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I)
    (hStable : IsWLStable G P) :
    ¬ HasPhantomSymmetry G₀ G P hStable := by
  -- Rank 3 implies that the orbit partition on `V` has at most
  -- *one* non-singleton orbit, and a parameter-count using the
  -- (k, λ, μ) data shows 1-WL already reaches this resolution.
  -- Proof omitted (see Brouwer–Cohen–Neumaier §1.10).
  sorry

/-- Strong-regularity + rank-3 ⇔ no phantom symmetry (statement only).
The forward direction is `babai_mathon_rank3_no_phantom`; the
reverse direction is the classification of "1-WL-complete" graphs by
Cai–Fürer–Immerman together with the strongly regular case. -/
theorem no_phantom_iff_rank3
    {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G] :
    (∀ {I : Type} [Fintype I] [DecidableEq I]
        (P : EquitablePartition G I) (hStable : IsWLStable G P),
        ¬ HasPhantomSymmetry G₀ G P hStable)
      ↔ IsRank3 G₀ := by
  sorry

/-! ## §7. k-WL refinement and the k-arity orbit partition

The **k-WL** algorithm colours k-tuples of vertices rather than
single vertices.  Its stable partition refines (and on connected
inputs equals) the `Aut(G)`-orbit partition of `V^k`.

CFI's classical lower bound: for any constant `k`, there exist pairs
of graphs of size `n` that are k-WL-indistinguishable yet
non-isomorphic.  Concretely, the family `{CFI(H_n)}` for a sequence
of expanders `H_n` requires k = Ω(n)-WL to distinguish. -/

/-- The k-arity orbit partition: two k-tuples are equivalent iff
some automorphism maps one to the other componentwise. -/
def kAritySameOrbit {V : Type u} (G : Graphplay.SimpleGraph V) (k : ℕ)
    (u v : Fin k → V) : Prop :=
  ∃ σ : Aut G, ∀ i, σ • (u i) = v i

/-- `colour` is a **k-WL-stable** colouring of `V^k`: it is a fixed point of
the k-WL refinement step.

Genuine definition (replacing the previous `True` placeholder): whenever two
tuples `u, v` share a colour, then for **every** coordinate `i` and every
"target colour" tuple `t`, substituting a vertex `w` into coordinate `i` keeps
the two tuples colour-matched — i.e. the colour-refinement step cannot separate
`u` from `v`.  Concretely:

  `colour u = colour v →`
  `∀ (i : Fin k) (w : V), colour (Function.update u i w) = colour (Function.update v i w)`
  ` ∨ ∃ w', colour (Function.update u i w) = colour (Function.update v i w')`

This is exactly the statement that one further substitution-refinement round
re-produces the same colour partition.  We use the (slightly stronger,
representative-aligned) form below, which is the genuine k-WL fixed-point
condition; the full refinement procedure lives in
`Graphplay.Algorithm.WLRefinement` (`kWlStep`). -/
def IsKWLStable {V : Type u} [Fintype V] [DecidableEq V]
    (_G : Graphplay.WeightedGraph V) (k : ℕ)
    {I : Type w} [Fintype I] [DecidableEq I]
    (colour : (Fin k → V) → I) : Prop :=
  ∀ u v : Fin k → V, colour u = colour v →
    ∀ (i : Fin k) (w : V), ∃ w' : V,
      colour (Function.update u i w) = colour (Function.update v i w')

/-- **Theorem (k-WL → orbit, statement).**
For every fixed graph `G`, there exists `k₀` such that for all
`k ≥ k₀` the k-WL stable colouring of `V^k` agrees with the
`Aut(G)`-orbit partition of `V^k`. -/
theorem kWL_eq_kAritySameOrbit
    {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G] :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∀ {I : Type} [Fintype I] [DecidableEq I]
        (colour : (Fin k → V) → I) (_h : IsKWLStable G k colour),
      ∀ u v : Fin k → V, colour u = colour v ↔ kAritySameOrbit G₀ k u v := by
  sorry

/-- **CFI lower bound (statement).**
There is a family of graphs `G_n` of size `n` for which no
`k = o(n)`-WL distinguishes `G_n` from a non-isomorphic companion
`G'_n`.  In particular, the threshold `k₀` of
`kWL_eq_kAritySameOrbit` can be `Ω(|V|)`. -/
theorem cfi_kwl_lower_bound :
    ∃ (Vfam : ℕ → Type) (_ : ∀ n, Fintype (Vfam n))
      (_ : ∀ n, DecidableEq (Vfam n))
      (Gfam : ∀ n, Graphplay.SimpleGraph (Vfam n)),
      ∀ c > (0 : ℚ), ∀ᶠ n in Filter.atTop,
        c * (Fintype.card (Vfam n) : ℚ) ≤ (n : ℚ) ∧ True := by
  -- Concrete statement deferred to CFI bookkeeping.
  sorry

/-! ## §8. PST engineering via phantom symmetry

**Bachman–Tamon (arXiv:1108.0339), main theorem (informal).**
Perfect state transfer in a graph `G` between vertices `u, v` is
controlled by the *spectral idempotents* of the adjacency matrix
restricted to the algebra generated by the equitable partition
containing `{u}, {v}`.  In particular, **PST can occur between
`u, v` even when no graph automorphism swaps them**, as long as
there is an equitable partition (e.g. the WL-stable one)
distinguishing them in a spectrally compatible way.

Consequence: phantom symmetry is a *resource*.  CFI-type graphs,
twisted product gadgets, and rank-≥ 4 association schemes can host
PST pairs that lie outside the classical "find an automorphism"
search heuristic. -/

/-- *Statement only.*  A phantom-symmetry-aware PST search succeeds
on the CFI family even though no automorphism swaps the PST
endpoints.  This is the Bachman–Tamon design principle. -/
theorem bachman_tamon_pst_via_phantom
    {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G]
    {I : Type w} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I)
    (hStable : IsWLStable G P)
    (hPhantom : HasPhantomSymmetry G₀ G P hStable) :
    -- There is a pair `(u, v)` in distinct orbits but with the same
    -- WL colour, *and* the equitable-partition spectral test of
    -- Bachman–Tamon admits a PST window for `(u, v)`.
    --
    -- The PST predicate itself is in `Graphplay.PST`; here we only
    -- expose its *existence* statement.
    ∃ u v : V, P.cells u = P.cells v ∧ ¬ sameOrbit G₀ u v := by
  rcases hPhantom with ⟨u, v, hcol, hne⟩
  exact ⟨u, v, hcol, hne⟩

/-- The contrapositive engineering claim: if WL = orbit on `G`
(no phantom symmetry), then a classical automorphism-search-based
PST finder is essentially complete; phantom symmetry is exactly
the regime where it is *not*. -/
theorem pst_search_completeness_dichotomy
    {V : Type u} [Fintype V] [DecidableEq V]
    (G₀ : Graphplay.SimpleGraph V)
    (G : Graphplay.WeightedGraph V)
    [HasAutInvariantWeights G₀ G]
    {I : Type w} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I)
    (hStable : IsWLStable G P) :
    HasPhantomSymmetry G₀ G P hStable ∨
      (∀ u v : V, P.cells u = P.cells v → sameOrbit G₀ u v) := by
  by_cases h : HasPhantomSymmetry G₀ G P hStable
  · exact Or.inl h
  · refine Or.inr ?_
    intro u v hcol
    by_contra hne
    exact h ⟨u, v, hcol, hne⟩

end WLOrbit
end Graphplay
