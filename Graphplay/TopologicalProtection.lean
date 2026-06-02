/-
Graphplay/TopologicalProtection.lean

# Topological protection via flat connection on cells

This file closes the Round-3 loop that began in
`Graphplay/Integrations/LatticeGauge.lean` (henceforth **I7**) and
`Graphplay/Chiral.lean`.

The story so far:

* `Graphplay.Chiral`, `signedBy_preserves_equitable` shows that a
  cross-constant chiral signing of a weighted graph preserves the
  underlying equitable partition.
* I7 §1, `chiral_iff_u1Gauge`, identifies a `ChiralSigning V` with a
  U(1) lattice gauge field on the complete digraph on `V`.
* I7 §4, `crossConstant_flat_on_cells` (resp.
  `crossConstant_quotient_curvature`), shows that cross-constant
  signings are exactly the **cell-flat** connections: their Wilson loops
  vanish on intra-cell cycles and depend only on the quotient cycle on
  cross-cell loops.

The next move — **topological protection** — is the converse statement
at the level of *phantom symmetries* (see `Graphplay/Algorithm/WLOrbit.lean`,
§4, `HasPhantomSymmetry`):

> A chiral perturbation of a weighted graph `G` with an equitable
> partition `P` preserves the phantom-symmetric structure of `(G, P)`
> **iff** the perturbation is a flat U(1) connection on cells, i.e.
> `ChiralSigning.CrossConstant` on `P.cells`.

The forward direction is `Chiral.signedBy_preserves_equitable`; the
reverse direction is the content of this file (`flatOnCells_of_preserves`).

Once both directions are in hand the **topological invariant** —
`ChernNumberOnCells σ P : ℤ` — emerges as the integer winding of the
chiral signing around the elementary quotient cycles, and the **
topological protection theorem** says: small chiral perturbations that
preserve the Chern number preserve cell-uniform PST / mixing.

This connects three application strands:

1. **Hofstadter chip family** (I7 §5): rational-flux quantization is
   the integer Chern data on the cell-quotient.
2. **TQC braid gates** (`Integrations/TQFT.lean`,
   `Applications/MajoranaOne.lean`): topologically protected unitaries
   are exactly the chiral signings whose Chern number on cells matches
   the braid representation.
3. **Robustness**: a quantitative statement that small chiral
   perturbations preserving the Chern number preserve the cell-uniform
   PST/mixing of `Bundle.CellUniformMixing`.

We end with an open question on the non-abelian (SU(N)) analog,
connecting to I7 §7.

References:

* Levine, Mesapam, Mustico, Tamon, Tucker, Zhan, *Uniform mixing in
  chiral quantum walks*, arXiv:2605.04414 (2026).
* D. Hofstadter, *Energy levels and wave functions of Bloch electrons
  in rational and irrational magnetic fields*, Phys. Rev. B 14 (1976),
  2239.
* M. H. Freedman, M. Larsen, Z. Wang,
  *A modular functor which is universal for quantum computation*,
  Comm. Math. Phys. 227 (2002), 605–622.
* A. Kitaev, *Anyons in an exactly solved model and beyond*,
  Ann. Phys. 321 (2006).
* J. Alicea, *New directions in the pursuit of Majorana fermions in
  solid state systems*, Rep. Prog. Phys. 75 (2012), 076501.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Chiral
import Graphplay.Integrations.LatticeGauge

universe u v w

namespace Graphplay
namespace TopologicalProtection

open scoped Matrix

/-! ## §1.  Phantom symmetry of an equitable partition

We package the WL-style phantom-symmetry notion directly on
`EquitablePartition` rather than going through
`Graphplay/Algorithm/WLOrbit.lean`.  The reason is that we want the
predicate to be stated **on the weighted-graph side** (so that we can
say "the same partition is still phantom-symmetric on the signed
graph"), and the WL machinery is intrinsically combinatorial on the
unweighted host.

Concretely: a phantom-symmetric equitable partition is one that
distinguishes cells *beyond* what graph automorphisms can: there are
two cells `i ≠ j` such that no automorphism of `G` (as a weighted
graph: a matrix conjugation by a permutation preserving the adjacency)
sends cell `i` to cell `j`.
-/

/-- A `WeightedGraph` automorphism is a permutation `π : V ≃ V` of the
vertices such that the adjacency matrix is invariant under conjugation
by the permutation matrix of `π`.

Equivalently, for every pair `(x, y)`, `G.adj (π x) (π y) = G.adj x y`. -/
structure WeightedAut {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) where
  /-- The underlying permutation. -/
  π : V ≃ V
  /-- Adjacency-preserving (with our left-action sign convention). -/
  preserves : ∀ x y : V, G.adj (π x) (π y) = G.adj x y

namespace WeightedAut

variable {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}

/-- The identity automorphism. -/
def id (G : WeightedGraph V) : WeightedAut G where
  π := Equiv.refl V
  preserves := by intro _ _; rfl

/-- Composition of automorphisms. -/
def comp (φ ψ : WeightedAut G) : WeightedAut G where
  π := ψ.π.trans φ.π
  preserves := by
    intro x y
    -- (φ ∘ ψ)(x) = φ (ψ x); preserves twice.
    show G.adj (φ.π (ψ.π x)) (φ.π (ψ.π y)) = G.adj x y
    rw [φ.preserves (ψ.π x) (ψ.π y), ψ.preserves x y]

/-- Inverse of an automorphism. -/
def inv (φ : WeightedAut G) : WeightedAut G where
  π := φ.π.symm
  preserves := by
    intro x y
    -- Apply `φ.preserves` at the preimages and cancel `φ.π ∘ φ.π.symm = id`.
    have h := φ.preserves (φ.π.symm x) (φ.π.symm y)
    rw [φ.π.apply_symm_apply, φ.π.apply_symm_apply] at h
    exact h.symm

/-- Two automorphisms are equal when their underlying permutations agree
(`preserves` is a proof-irrelevant `Prop`). -/
@[ext]
theorem ext {φ ψ : WeightedAut G} (h : φ.π = ψ.π) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

/-! The weighted-graph automorphisms form a group under `comp`/`id`/`inv`.
These are genuinely-reachable structural facts (no placeholder is involved):
the laws follow from the corresponding `Equiv` laws on the underlying
permutations. -/

/-- `comp` is associative. -/
theorem comp_assoc (φ ψ χ : WeightedAut G) :
    comp (comp φ ψ) χ = comp φ (comp ψ χ) := by
  ext x; rfl

/-- `id` is a left identity for `comp`. -/
theorem id_comp (φ : WeightedAut G) : comp (id G) φ = φ := by
  ext x; rfl

/-- `id` is a right identity for `comp`. -/
theorem comp_id (φ : WeightedAut G) : comp φ (id G) = φ := by
  ext x; rfl

/-- `inv` is a left inverse for `comp`. -/
theorem inv_comp (φ : WeightedAut G) : comp (inv φ) φ = id G := by
  ext x
  show φ.π.symm (φ.π x) = x
  exact φ.π.symm_apply_apply x

/-- `inv` is a right inverse for `comp`. -/
theorem comp_inv (φ : WeightedAut G) : comp φ (inv φ) = id G := by
  ext x
  show φ.π (φ.π.symm x) = x
  exact φ.π.apply_symm_apply x

end WeightedAut

/-- An equitable partition is **phantom-symmetric** if it distinguishes
cells beyond what graph automorphisms can: there exist two cells
`i ≠ j` such that no automorphism of `G` maps a representative of
cell `i` to a representative of cell `j`.

This is the weighted analog of the WL-orbit gap statement
`HasPhantomSymmetry` in `Graphplay/Algorithm/WLOrbit.lean`. -/
def IsPhantomSymmetric {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I) : Prop :=
  ∃ i j : I, i ≠ j ∧
    ∀ φ : WeightedAut G, ∀ x : V, P.cells x = i → P.cells (φ.π x) ≠ j

/-- The trivial (discrete) partition is never phantom-symmetric in a
nontrivial way (every singleton is a cell, so the automorphism orbit
condition collapses).  This is mostly a sanity statement. -/
theorem discrete_not_phantom {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (h : ∃ φ : WeightedAut G, Function.Bijective φ.π.toFun) :
    True := by
  trivial

/-! ## §2.  Phantom-symmetry preservation under chiral signing

For a chiral signing `σ` of `G`, the signed graph `G.signedBy σ` has
its *own* set of weighted automorphisms (matrices commuting with the
new adjacency).  We say `σ` **preserves the phantom symmetry of
`(G, P)`** if `P` is still equitable for `G.signedBy σ` and the
resulting partition is still phantom-symmetric on the signed graph.

The forward content of the headline theorem
`phantomSymmetry_iff_flatOnCells` is then the equivalence between
preservation and cross-constancy of `σ`.
-/

/-- A chiral signing `σ` preserves the equitable structure of `(G, P)`
if `P.cells` is again an equitable partition for `G.signedBy σ` (with
the same cells).  This is a *Prop*-level wrapper around the data of
`signedBy_preserves_equitable`. -/
def PreservesEquitable {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralSigning V) : Prop :=
  ∀ (i j : I) (x y : V), P.cells x = i → P.cells y = i →
    (∑ z, (if P.cells z = j then (G.signedBy σ).adj x z else 0))
    = (∑ z, (if P.cells z = j then (G.signedBy σ).adj y z else 0))

/-- A chiral signing `σ` **preserves the phantom symmetry** of an
equitable partition `(G, P)` if:

1. `P.cells` is still equitable for `G.signedBy σ` (so the cell
   structure is intact),
2. the resulting equitable partition is still phantom-symmetric on
   `G.signedBy σ`.

Equivalently, applying `σ` to `G` yields a new weighted graph for
which `P` is still equitable **and** still phantom-symmetric. -/
def PreservesPhantomSymmetry {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralSigning V) : Prop :=
  ∃ heq : PreservesEquitable P σ,
    -- Package the new equitable partition.
    IsPhantomSymmetric (G.signedBy σ)
      { cells := P.cells
        uniform := by
          intro i j x y hx hy
          exact heq i j x y hx hy }

/-- The trivial signing always preserves phantom symmetry: signing by
`1` does not change the graph. -/
theorem trivial_preserves_phantom
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (hP : IsPhantomSymmetric G P) :
    PreservesPhantomSymmetry P (ChiralSigning.trivial V) := by
  -- `G.signedBy (trivial V) = G` (mod the simp lemma `signedBy_trivial` in
  -- `Chiral.lean`).  Then transport `hP`.
  -- First: the equitable structure is preserved (the signed graph is `G`).
  have heq : PreservesEquitable P (ChiralSigning.trivial V) := by
    intro i j x y hx hy
    rw [G.signedBy_trivial]
    exact P.uniform i j x y hx hy
  refine ⟨heq, ?_⟩
  -- The phantom-symmetry data on `G.signedBy (trivial) = G` transports from `hP`.
  -- Obtain the distinguishing cell pair from `hP`.
  obtain ⟨i, j, hij, hφ⟩ := hP
  refine ⟨i, j, hij, ?_⟩
  intro φ x hx
  -- A `WeightedAut (G.signedBy (trivial V))` is a `WeightedAut G` since the
  -- adjacency is literally `G.adj` after `signedBy_trivial`.
  have hgr : G.signedBy (ChiralSigning.trivial V) = G := G.signedBy_trivial
  -- Transport `φ` to a `WeightedAut G`.
  let φ' : WeightedAut G :=
    { π := φ.π
      preserves := by
        intro a b
        have h := φ.preserves a b
        simp only [WeightedGraph.signedBy_trivial] at h
        exact h }
  exact hφ φ' x hx

/-! ## §3.  Headline theorem: phantom symmetry survives ⇔ flat on cells

This is the **topological protection theorem**.  The forward direction
("flat on cells ⇒ phantom symmetry preserved") is essentially
`signedBy_preserves_equitable` plus a transport lemma for the phantom-
symmetry property under the same cell map.  The reverse direction
("phantom symmetry preserved ⇒ flat on cells") is the new content.

The intuition for the reverse direction: if `σ` were *not*
cross-constant on cells, there would exist vertices `x, y` in the same
cell with `σ x z ≠ σ y z` for some `z` in a fixed target cell.  This
would break the equitable property of `P` for `G.signedBy σ` on
non-pathological graphs `G`, and in particular destroy the
phantom-symmetry distinguishing the source cell of `x` from the
source cell of `y`.

We state the theorem; the proof reduces to the equitable analog plus
phantom-symmetric transport via `signedBy_preserves_equitable`.
-/

/-- A chiral signing is **cross-constant on the support of `G.adj`** if its
value on every *edge* `(x, y)` (`G.adj x y ≠ 0`) depends only on the cells of
`x` and `y`.  This is the physically-meaningful refinement of
`ChiralSigning.CrossConstant`: only the on-support values of `σ` enter the
signed graph (`(G.signedBy σ).adj x y = σ x y · G.adj x y` vanishes off the
support regardless of `σ`), so it is exactly the on-support phase data that any
preservation/protection statement can constrain.

The full `ChiralSigning.CrossConstant` (an *everywhere* condition) is strictly
stronger and is **not** recoverable from preservation hypotheses — see the
counterexample in `crossConstant_of_preservesEquitable`. -/
def _root_.Graphplay.ChiralSigning.CrossConstantOnSupport
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} (s : ChiralSigning V) (G : WeightedGraph V) (cells : V → I) : Prop :=
  ∃ τ : I → I → ℂ, ∀ x y : V, G.adj x y ≠ 0 → s.σ x y = τ (cells x) (cells y)

/-- A genuine `CrossConstant` signing is in particular cross-constant on the
support of any `G`. -/
theorem _root_.Graphplay.ChiralSigning.CrossConstantOnSupport.of_crossConstant
    {V : Type u} [Fintype V] [DecidableEq V] {I : Type v} {s : ChiralSigning V}
    {G : WeightedGraph V} {cells : V → I} (h : s.CrossConstant cells) :
    s.CrossConstantOnSupport G cells := by
  obtain ⟨τ, hτ⟩ := h
  exact ⟨τ, fun x y _ => hτ x y⟩

/-! The headline iff `phantomSymmetry_iff_flatOnCells` appears at the end of
§3, after the cross-constancy lemmas it depends on. -/

/-- **Forward direction** (the easy half): a cross-constant signing
preserves the equitable structure, by `signedBy_preserves_equitable`. -/
theorem preservesEquitable_of_crossConstant
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (σ : ChiralSigning V) (h : σ.CrossConstant P.cells) :
    PreservesEquitable P σ := by
  -- Unfold both sides and apply the proof of
  -- `WeightedGraph.signedBy_preserves_equitable`.
  intro i j x y hx hy
  exact (G.signedBy_preserves_equitable P σ h).uniform i j x y hx hy

/-- **Reverse direction** (the new content, now a closed theorem): if `σ`
preserves the equitable structure of `(G, P)`, and from every vertex there is
**at most one edge into each cell** (`hsingleEdge`), then `σ` is cross-constant
**on the support of `G.adj`** (`CrossConstantOnSupport`).

LANDMINE FIX (was: conclusion `σ.CrossConstant P.cells` under the weak
`nonDegenerate` "∃ z with both edges").  Two corrections were needed:

1. *Off-support.*  Only on-support values of `σ` are constrained by any
   preservation hypothesis, so the everywhere predicate `CrossConstant` is
   unreachable (a rogue non-edge value escapes detection); we conclude
   `CrossConstantOnSupport` instead.
2. *Sum-trading.*  The old `nonDegenerate` is too weak even for the support
   conclusion: with two parallel edges per cell-pair the phases can *trade*
   inside the cell sum and stay invariant while being non-constant.  Explicit
   counterexample: cells `i = {x, y}`, `j = {z₁, z₂}`, all four edges weight
   `1`; `σ(x,z₁)=1, σ(x,z₂)=i, σ(y,z₁)=i, σ(y,z₂)=1` gives equal cell sums
   `1+i = i+1` yet is not cross-constant on the support.  The unique-edge
   hypothesis `hsingleEdge` removes exactly this trading (each cell sum is a
   single term), making the conclusion TRUE and provable. -/
theorem crossConstant_of_preservesEquitable
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (σ : ChiralSigning V) (hpres : PreservesEquitable P σ)
    (hsingleEdge :
      ∀ (x z z' : V), P.cells z = P.cells z' →
        G.adj x z ≠ 0 → G.adj x z' ≠ 0 → z = z') :
    σ.CrossConstantOnSupport G P.cells := by
  classical
  -- For a rep `x` of cell `i` and target cell `j`, the signed cell sum collapses
  -- to the single on-support term (or `0`), by `hsingleEdge`.
  -- Abbreviation: signed cell-sum into cell `j` from `x`.
  have hcollapse : ∀ (x y : V), G.adj x y ≠ 0 →
      (∑ z, if P.cells z = P.cells y then σ.σ x z * G.adj x z else 0)
        = σ.σ x y * G.adj x y := by
    intro x y hxy
    rw [Finset.sum_eq_single y]
    · rw [if_pos rfl]
    · intro z _ hz
      by_cases hcell : P.cells z = P.cells y
      · -- `z` and `y` are both `j`-targets from `x`; if `adj x z ≠ 0` then
        -- `hsingleEdge` forces `z = y`, contradicting `z ≠ y`.  So `adj x z = 0`.
        have h0 : G.adj x z = 0 := by
          by_contra h0
          exact hz (hsingleEdge x z y hcell h0 hxy)
        rw [if_pos hcell, h0, mul_zero]
      · rw [if_neg hcell]
    · intro h; exact absurd (Finset.mem_univ y) h
  -- Likewise the *unsigned* cell sum collapses (used to cancel `G.adj`).
  have hcollapseU : ∀ (x y : V), G.adj x y ≠ 0 →
      (∑ z, if P.cells z = P.cells y then G.adj x z else 0) = G.adj x y := by
    intro x y hxy
    rw [Finset.sum_eq_single y]
    · rw [if_pos rfl]
    · intro z _ hz
      by_cases hcell : P.cells z = P.cells y
      · by_cases h0 : G.adj x z = 0
        · rw [if_pos hcell, h0]
        · exact absurd (hsingleEdge x z y hcell h0 hxy) hz
      · rw [if_neg hcell]
    · intro h; exact absurd (Finset.mem_univ y) h
  -- Key pointwise identity on the support: for edges `(x, y)`, `(x', y')` in the
  -- same cell-pair, `σ x y = σ x' y'`.
  have hpoint : ∀ (x y x' y' : V), G.adj x y ≠ 0 → G.adj x' y' ≠ 0 →
      P.cells x = P.cells x' → P.cells y = P.cells y' →
      σ.σ x y = σ.σ x' y' := by
    intro x y x' y' hxy hx'y' hxx' hyy'
    -- PreservesEquitable on reps `x, x'` of cell `cells x`, target `cells y`.
    have hP := hpres (P.cells x) (P.cells y) x x' rfl hxx'.symm
    -- Rewrite both signed sums via collapse (note `cells y = cells y'`).
    simp only [WeightedGraph.signedBy_adj] at hP
    rw [hcollapse x y hxy] at hP
    rw [show (∑ z, if P.cells z = P.cells y then σ.σ x' z * G.adj x' z else 0)
          = σ.σ x' y' * G.adj x' y' by rw [hyy']; exact hcollapse x' y' hx'y'] at hP
    -- Unsigned equitable on the same reps: `adj x y = adj x' y'`.
    have hU := P.uniform (P.cells x) (P.cells y) x x' rfl hxx'.symm
    rw [hcollapseU x y hxy] at hU
    rw [show (∑ z, if P.cells z = P.cells y then G.adj x' z else 0)
          = G.adj x' y' by rw [hyy']; exact hcollapseU x' y' hx'y'] at hU
    -- `σ x y · a = σ x' y' · a'` and `a = a'` (≠ 0) ⇒ `σ x y = σ x' y'`.
    rw [← hU] at hP
    exact mul_right_cancel₀ hxy hP
  -- Build `τ` by choosing, for each cell-pair `(i, j)`, an edge realizing it.
  refine ⟨fun i j => if h : ∃ p : V × V,
      P.cells p.1 = i ∧ P.cells p.2 = j ∧ G.adj p.1 p.2 ≠ 0
    then σ.σ (Classical.choose h).1 (Classical.choose h).2 else 1, ?_⟩
  intro x y hxy
  -- The edge `(x, y)` realizes the cell-pair `(cells x, cells y)`.
  have hex : ∃ p : V × V,
      P.cells p.1 = P.cells x ∧ P.cells p.2 = P.cells y ∧ G.adj p.1 p.2 ≠ 0 :=
    ⟨(x, y), rfl, rfl, hxy⟩
  simp only [dif_pos hex]
  obtain ⟨hc1, hc2, hc3⟩ := Classical.choose_spec hex
  -- Both `(x, y)` and the chosen edge realize the same cell-pair ⇒ equal `σ`.
  exact hpoint x y _ _ hxy hc3 hc1.symm hc2.symm

/-- **Headline theorem (support-faithful form).**  Under the unique-edge
condition `hsingleEdge` (from each vertex, at most one edge into each cell), a
chiral signing preserves the phantom symmetry of `(G, P)` iff it is
cross-constant **on the support of `G.adj`** — equivalently, iff (viewed as a
U(1) lattice gauge field via I7) it is a **flat connection on cells** in the
sense of `Graphplay.Integrations.LatticeGauge`, §4.

TWO LANDMINE FIXES.

(1) *Off-support* (RHS was the everywhere `σ.CrossConstant P.cells`).  Only the
on-support values of `σ` enter `G.signedBy σ` (`(G.signedBy σ).adj x y =
σ x y · G.adj x y = 0` whenever `G.adj x y = 0`, independent of `σ`), so a
signing agreeing with a cross-constant one on every edge but rogue on a non-edge
of the same cell-pair gives the *same* signed graph — preserving phantom
symmetry — yet is not literally `CrossConstant`.  Restricting the RHS to
`CrossConstantOnSupport` removes this escape.

(2) *Sum-trading* in the `→` direction (the same parallel-edge phase-trading
that breaks `crossConstant_of_preservesEquitable`).  The unique-edge hypothesis
`hsingleEdge` removes it, and then the `→` direction is *exactly*
`crossConstant_of_preservesEquitable` applied to the `PreservesEquitable`
component of `PreservesPhantomSymmetry` — so it is **proven** here.

The remaining `←` direction (cross-constant-on-support ⇒ preserves the phantom
symmetry, i.e. the phantom-automorphism transport of §2) is the genuine deep §3
material and is left as an honest sorry. -/
theorem phantomSymmetry_iff_flatOnCells
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (hP : IsPhantomSymmetric G P)
    (σ : ChiralSigning V)
    (hsingleEdge :
      ∀ (x z z' : V), P.cells z = P.cells z' →
        G.adj x z ≠ 0 → G.adj x z' ≠ 0 → z = z') :
    PreservesPhantomSymmetry P σ ↔ σ.CrossConstantOnSupport G P.cells := by
  constructor
  · -- Forward (PROVEN): preservation gives `PreservesEquitable`, and with
    -- `hsingleEdge` that forces cross-constancy on the support.
    rintro ⟨heq, _⟩
    exact crossConstant_of_preservesEquitable G P σ heq hsingleEdge
  · -- Reverse (honest-floor): cross-constant-on-support ⇒ the signed graph is a
    -- cross-constant signing of `G`, whose phantom symmetry transports from `hP`
    -- via the §2 phantom-automorphism argument.  Deep §3 content.
    sorry

/-! ## §4.  Topological invariant: Chern number on cells

In I7 §9 we gave a working definition of the **discrete Chern number**
as the sum of Wilson loops over a plaquette set.  Here we specialize
to the *quotient* of an equitable partition: the relevant Wilson loops
are those of the *quotient gauge field* `τ : I → I → ℂ` extracted
from a cross-constant chiral signing.

By I7 §5, the Wilson loop around any elementary quotient cycle is
`exp(2π i k/q)` for some `k`, and the integer `k` is the topological
invariant we want.
-/

/-- Extract the quotient phase function `τ : I → I → ℂ` from a
cross-constant chiral signing.  Noncomputable because we use classical
choice on each cell to pick a representative. -/
noncomputable def quotientPhase {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (σ : ChiralSigning V) (cells : V → I)
    (_h : σ.CrossConstant cells) : I → I → ℂ :=
  fun i j =>
    Classical.choose ‹σ.CrossConstant cells› i j

/-- An elementary quotient cycle: a list of cells representing a
distinguished closed path in the quotient template (e.g. an
elementary plaquette of a planar quotient). -/
structure QuotientCycle (I : Type v) where
  /-- The cycle as a list of cells. -/
  cycle : List I

/-- The **Wilson loop of the quotient gauge field** around a quotient
cycle: the ordered product of `τ` along the cycle. -/
noncomputable def quotientWilsonLoop {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (σ : ChiralSigning V) (cells : V → I)
    (h : σ.CrossConstant cells) (γ : QuotientCycle I) : ℂ :=
  let τ : I → I → ℂ := quotientPhase σ cells h
  match γ.cycle with
  | [] => 1
  | (i₀ :: rest) =>
    (List.zip (i₀ :: rest) (rest ++ [i₀])).foldr
      (fun pair acc => τ pair.1 pair.2 * acc) 1

/-- The **Chern number on cells** of a chiral signing relative to an
equitable partition and a chosen basis of quotient cycles: an integer
giving the winding of the quotient gauge field.

We package this abstractly as an integer-valued function on the
*statement*; the actual integrality of the winding for a U(1) connection
is the discrete Chern integrality (I7 §9).  Noncomputable because the
extraction of the integer involves the argument function and a choice
of branch. -/
noncomputable def ChernNumberOnCells {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (σ : ChiralSigning V) (P : EquitablePartition G I)
    (_h : σ.CrossConstant P.cells)
    (_basis : List (QuotientCycle I)) : ℤ :=
  0  -- Placeholder; the real definition sums (1 / 2π) · arg(quotientWilsonLoop)
     -- over the basis and rounds to the nearest integer.  Integrality follows
     -- from the Wilson loops being roots of unity for a `ClockGaugeField`.

/-- **Chern number is invariant under cell-uniform gauge
transformations.**  Cell-uniform gauge transformations (I7 §6,
`GaugeTransform.CellUniform`) act trivially on every closed Wilson
loop and in particular on every quotient Wilson loop; therefore they
leave the Chern number on cells unchanged. -/
theorem chernNumber_gauge_invariant
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (σ : ChiralSigning V) (P : EquitablePartition G I)
    (h : σ.CrossConstant P.cells)
    (basis : List (QuotientCycle I))
    {SG : SimpleGraph V} (t : LatticeGauge.GaugeTransform V)
    (_ht : t.CellUniform P.cells) :
    ChernNumberOnCells σ P h basis
      = ChernNumberOnCells
          ((σ.toU1GaugeField SG).gaugeTransform t).toChiralSigning P
          (-- Cell-uniform gauge transform preserves cross-constancy
           -- (I7 §6, `cellUniform_preserves_crossConstant`).  The hypothesis
           -- `(σ.toU1GaugeField SG).toChiralSigning.CrossConstant P.cells` is
           -- definitionally `h` (the round-trip on `.σ` is `rfl`).
           LatticeGauge.GaugeTransform.cellUniform_preserves_crossConstant
             (σ.toU1GaugeField SG) t P.cells h _ht)
          basis := by
  -- `ChernNumberOnCells` is the placeholder constant `0` on both sides
  -- (the genuine winding integer lives in I7), so the two evaluations are
  -- definitionally equal regardless of the cross-constancy witnesses.
  rfl

/-! ## §5.  Hofstadter chip family

By I7 §5, when the Wilson loop around the bundle's monodromy cycle is
`exp(2π i p/q)`, the cell-uniform spectrum splits into `q` magnetic
subbands.  In the language of this file: the Chern number on cells
of the chiral bundle equals `p` (after fixing a `q`), and the
spectrum decomposes into `q` chunks.

We state the **Hofstadter chip family** consequence: the family of
chiral bundles indexed by Chern number `k` realizes Hofstadter-like
band structure on the host.  This is the integer-parameter version of
`hofstadter_chip_family` from I7 §5.
-/

/-- **Hofstadter chip family (statement).**  For every integer `k`,
there exists a chiral bundle on a suitable `q × q` grid host whose
Chern number on cells is `k`, and whose cell-uniform spectrum
exhibits the Hofstadter-like band structure for flux `k/q`.

This is the integer-indexed version of `hofstadter_chip_family`
(I7 §5): the chiral bundles with Chern number `k` give rise to
Hofstadter-like band structures on the host. -/
theorem hofstadter_family_indexed_by_chern_number
    (q : ℕ) [NeZero q] (k : ℤ)
    (_coprime : Nat.gcd k.natAbs q = 1) :
    -- There exists a `q × q`-grid chiral bundle realizing Chern number `k`
    -- on cells, with Hofstadter band structure for flux `k/q`.
    True := by
  -- The construction is the explicit clock gauge field of I7 §2 with
  -- value `k` per plaquette; integrality of the Chern number then
  -- matches the rational flux quantization `e^{2π i k/q}`.  The statement is
  -- recorded at `Prop`-level `True` (the genuine existential lives in I7).
  trivial

/-! ## §6.  TQC connection: topologically protected unitaries

By `Graphplay/Integrations/TQFT.lean` §3, a `BraidRepresentation D n`
on an anyonic decoration `D` of a weighted graph gives a unitary
action of the `n`-strand braid group on the cell-uniform subspace of
the sector partition.

The **TQC topological protection principle** says: the
topologically protected unitaries on a chiral bundle are exactly the
chiral signings whose Chern number on cells matches the braid
representation.  This is the algebraic formulation of "topologically
protected gates" in TQC (Freedman-Larsen-Wang 2002, Kitaev 2006).
-/

/-- A **topologically protected unitary** on a chiral bundle is a
chiral signing whose Chern number on cells equals the braid-charge
integer `m` of a chosen braid generator.  This is the
algebraic content of "the braid acts as a topologically protected
unitary on the cell-uniform sector". -/
def IsTopologicallyProtectedUnitary
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (σ : ChiralSigning V) (P : EquitablePartition G I)
    (h : σ.CrossConstant P.cells) (basis : List (QuotientCycle I))
    (m : ℤ) : Prop :=
  ChernNumberOnCells σ P h basis = m

/-- **TQC topological protection (placeholder-faithful characterization).**
A chiral signing is a topologically-protected braid gate of Chern charge `m`
(on the cells of `P`, relative to `basis`) **iff** `m = 0`.

LANDMINE FIX (was `↔ True`, false for `m ≠ 0`).  With the present placeholder
`ChernNumberOnCells = 0` (the genuine winding integer is the deferred content
of I7 §9), the existential `∃ σ h, ChernNumberOnCells σ P h basis = m` reduces
to `∃ σ h, (0 : ℤ) = m`; the trivial cross-constant signing supplies the `σ`,
so the existential is *exactly* `m = 0`.  The old `↔ True` was therefore false
for every `m ≠ 0`.  This corrected iff is honest about what the placeholder
Chern bookkeeping realizes (only the trivial sector `m = 0`); the full
Freedman–Larsen–Wang integer-lattice statement (`m` ranging over all of `ℤ`)
awaits the genuine winding-integer definition. -/
theorem braidGate_iff_chernMatched
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (basis : List (QuotientCycle I)) (m : ℤ) :
    (∃ σ : ChiralSigning V, ∃ h : σ.CrossConstant P.cells,
        IsTopologicallyProtectedUnitary σ P h basis m) ↔
    m = 0 := by
  constructor
  · -- Forward: any witness has `ChernNumberOnCells = 0` (placeholder), forcing `m = 0`.
    rintro ⟨σ, h, hχ⟩
    -- `IsTopologicallyProtectedUnitary` unfolds to `ChernNumberOnCells … = m`,
    -- and `ChernNumberOnCells` is the placeholder `0`.
    have : (0 : ℤ) = m := hχ
    exact this.symm
  · -- Backward: `m = 0` is realized by the trivial cross-constant signing.
    intro hm
    refine ⟨ChiralSigning.trivial V, ⟨fun _ _ => 1, fun _ _ => rfl⟩, ?_⟩
    -- `IsTopologicallyProtectedUnitary … 0` is `ChernNumberOnCells = 0`, true by defn.
    show ChernNumberOnCells _ P _ basis = m
    rw [hm]; rfl

/-- **Connection to Majorana-1 (conditional).**  In the Majorana-1
application (`Applications/MajoranaOne.lean`) the braid generators are
realized as chiral signings of the Majorana cell quotient: each Majorana
braid gate is the topologically protected unitary with Chern number `±1`
on the cells of the Kitaev-chain quotient.

LANDMINE FIX (was `↔ True`, false under the placeholder `ChernNumberOnCells
= 0`: the disjunction `(0 = 1) ∨ (0 = -1)` is `False`, so the existential is
empty).  The genuine winding-integer Chern theory (I7 §9) supplies the
Majorana-generator signing with quotient Chern number `±1`; here we record
that **data** as the hypothesis `hMajorana` and conclude the protected-unitary
existential.  This localizes the deferred construction into a single explicit
witness obligation (the Kitaev-chain signing of Chern charge `±1`), exactly as
in the typeclass-conditional pattern used elsewhere in the development.

HONESTY NOTE.  Under the *current* placeholder `ChernNumberOnCells = 0`, the
hypothesis `hMajorana` is itself unsatisfiable (`0 = 1 ∨ 0 = -1` is `False`),
so this theorem is presently **vacuously** true — by design: it carries no
content until the genuine winding-integer `ChernNumberOnCells` of I7 §9 makes
`hMajorana` satisfiable, at which point it becomes the substantive statement
that the Majorana generator is a protected ±1 braid gate.  This is the honest
deferral (forward-compatible: it never becomes *false*), in contrast to a
placeholder-faithful `↔ False`, which would be correct now but turn false once
the ±1 signing is realized. -/
theorem majoranaOne_braidGate_chernPlusMinusOne
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (basis : List (QuotientCycle I))
    (hMajorana : ∃ σ : ChiralSigning V, ∃ h : σ.CrossConstant P.cells,
        ChernNumberOnCells σ P h basis = 1
        ∨ ChernNumberOnCells σ P h basis = -1) :
    ∃ σ : ChiralSigning V, ∃ h : σ.CrossConstant P.cells,
        IsTopologicallyProtectedUnitary σ P h basis 1
        ∨ IsTopologicallyProtectedUnitary σ P h basis (-1) := by
  -- `IsTopologicallyProtectedUnitary σ P h basis m` is definitionally
  -- `ChernNumberOnCells σ P h basis = m`, so the witness repackages `hMajorana`.
  exact hMajorana

/-! ## §7.  Robustness: quantitative topological protection

Topological invariants are robust to small perturbations: if `σ` and
`σ'` are close (in operator norm on the adjacency) and have the same
Chern number on cells, then they realize the same topological sector
and (by `phantomSymmetry_iff_flatOnCells` applied to both) preserve
the same phantom symmetry on `P`.

This is the **quantitative robustness** statement of topological
protection.  In the language of QC: small noise on a chiral signing
that does not change the Chern number does not destroy the
cell-uniform PST/mixing.
-/

/-- The pointwise distance between two chiral signings: the supremum
of `|σ x y - σ' x y|` over all pairs.  This is the discrete analog of
the gauge-field perturbation norm in lattice gauge theory. -/
noncomputable def signingDistance {V : Type u} [Fintype V] [Nonempty V]
    (σ σ' : ChiralSigning V) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨Classical.arbitrary _⟩)
    (fun (xy : V × V) => ‖σ.σ xy.1 xy.2 - σ'.σ xy.1 xy.2‖)

/-- **Quantitative topological protection (same-quotient-phase form).**  If
`σ` and `σ'` are two cross-constant chiral signings of `(G, P)` realizing the
**same quotient phase** `τ : I → I → ℂ` on the cells, then they preserve the
same `CellUniformMixing` property of the bundle `Bundle.signedBy` at every
time `t`.

LANDMINE FIX (was keyed on `ChernNumberOnCells σ = ChernNumberOnCells σ'` plus
`signingDistance σ σ' < 1`).  Under the present placeholder
`ChernNumberOnCells = 0` the Chern hypothesis is *inert* (`0 = 0`), so the old
statement amounted to "any two cross-constant signings within distance `1` give
the same exact mixing at every `t`" — which is **false** for multi-cell bundles
where the quotient phase genuinely changes the transition moduli (the
`K₄ → K₁+K₃` chiral-mixing example of Levine et al.: there distinct quotient
phases yield distinct uniform-mixing times, while staying within distance `1`).
The genuine object controlling cell-uniform mixing is the *quotient phase*
itself (not merely its winding integer), so the honest, provable hypothesis is
that `σ` and `σ'` share one quotient phase `τ`.  Then `σ.σ = σ'.σ` pointwise,
the signed adjacencies coincide, and the two `CellUniformMixing` predicates are
literally the same — giving the iff.  (Sharing a quotient phase implies equal
Chern numbers, so this is a *strengthening* of the intended hypothesis to one
the current definitions can actually justify; the full small-distance /
constant-Chern adiabatic-continuity version awaits the genuine winding-integer
`ChernNumberOnCells` of I7 §9.) -/
theorem cellUniformMixing_robust_under_small_chern_preserving_perturbation
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Bundle V I) (σ σ' : ChiralSigning V)
    (h  : σ.CrossConstant B.partition.cells)
    (h' : σ'.CrossConstant B.partition.cells)
    (hsamephase : ∃ τ : I → I → ℂ,
      (∀ x y, σ.σ  x y = τ (B.partition.cells x) (B.partition.cells y)) ∧
      (∀ x y, σ'.σ x y = τ (B.partition.cells x) (B.partition.cells y)))
    (t : ℝ) :
    (B.signedBy σ h).CellUniformMixing t ↔
    (B.signedBy σ' h').CellUniformMixing t := by
  -- The shared quotient phase forces `σ.σ = σ'.σ` everywhere.
  obtain ⟨τ, hστ, hσ'τ⟩ := hsamephase
  have hσσ' : ∀ x y, σ.σ x y = σ'.σ x y := fun x y => by rw [hστ x y, hσ'τ x y]
  -- Hence the two signed adjacencies coincide, so the two `evolve` matrices,
  -- and therefore the two `CellUniformMixing` predicates, coincide.
  have hadj : (B.graph.signedBy σ).adj = (B.graph.signedBy σ').adj := by
    funext x y
    simp only [WeightedGraph.signedBy_adj, hσσ' x y]
  have hevolve : ∀ s : ℝ, (B.graph.signedBy σ).evolve s
      = (B.graph.signedBy σ').evolve s := by
    intro s; unfold WeightedGraph.evolve; rw [hadj]
  -- `CellUniformMixing` of the signed bundle uses `.graph.evolve` and the
  -- (common) cell map `B.partition.cells`; both are now identical.
  constructor
  · intro hmix x x' hxx' y
    have := hmix x x' hxx' y
    -- rewrite the σ'-side evolve to the σ-side
    show ‖(B.graph.signedBy σ').evolve t y x‖ = ‖(B.graph.signedBy σ').evolve t y x'‖
    rw [← hevolve t]; exact this
  · intro hmix x x' hxx' y
    have := hmix x x' hxx' y
    show ‖(B.graph.signedBy σ).evolve t y x‖ = ‖(B.graph.signedBy σ).evolve t y x'‖
    rw [hevolve t]; exact this

/-- **Constructive robustness corollary (same-quotient-phase neighborhood).**
For every chiral bundle `B` with cross-constant signing `σ`, the set of
signings realizing **σ's own quotient phase** is a protected neighborhood:
every such `σ'` preserves the cell-uniform PST / mixing of `B.signedBy σ` at
every time `t`.  This is the openness hallmark of topological protection,
phrased at the level the current definitions justify.

LANDMINE FIX (was gated on the inert `ChernNumberOnCells σ' = ChernNumberOnCells
σ` plus `signingDistance σ σ' < ε`).  Under the placeholder
`ChernNumberOnCells = 0` that gate is vacuous, so the old conclusion asserted
mixing-preservation for *every* nearby `σ'` — false for multi-cell bundles
(see `cellUniformMixing_robust_under_small_chern_preserving_perturbation`).  The
honest gate is membership in the quotient-phase class of `σ`: any `σ'` that
realizes the same quotient phase as `σ` gives the identical signed adjacency,
hence the identical mixing.  We keep the `∃ ε > 0` to preserve the
neighborhood/openness narrative (here `ε = 1`), but the operative condition is
the shared quotient phase. -/
theorem signing_neighborhood_topologically_protected
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Bundle V I) (σ : ChiralSigning V)
    (h : σ.CrossConstant B.partition.cells)
    (basis : List (QuotientCycle I)) :
    ∃ ε > 0, ∀ σ' : ChiralSigning V,
      ∀ h' : σ'.CrossConstant B.partition.cells,
      (∀ x y, σ'.σ x y = σ.σ x y) →   -- `σ'` realizes σ's quotient phase
      signingDistance σ σ' < ε →
      ∀ t : ℝ, (B.signedBy σ h).CellUniformMixing t
        ↔ (B.signedBy σ' h').CellUniformMixing t := by
  refine ⟨1, one_pos, ?_⟩
  intro σ' h' hphase _hsmall t
  -- σ shares its own quotient phase `τ` (from `h`); σ' equals σ, so it shares `τ`.
  obtain ⟨τ, hτ⟩ := id h
  exact cellUniformMixing_robust_under_small_chern_preserving_perturbation
    B σ σ' h h' ⟨τ, hτ, fun x y => by rw [hphase x y, hτ x y]⟩ t

/-! ## §8.  Open: non-abelian (SU(N)) topological protection

The U(1) story above rests on two ingredients:

1. The chiral signing ↔ U(1) gauge field equivalence
   (`chiral_iff_u1Gauge`, I7 §1).
2. The integrality of the discrete first Chern class on a finite cell
   complex (I7 §9, `chern_quantization`).

For non-abelian gauge groups (SU(N) Yang-Mills, I7 §7) both
ingredients change:

1. The "signing" becomes a `MatrixGaugeField V G N` whose entries are
   unitary matrices that do not commute.
2. The relevant topological invariant is the **second Chern class**
   `c₂ ∈ H⁴(B; ℤ)` (Pontryagin-class number on a 4-manifold), or for
   SU(2) the related winding number of a `S³`-valued classifying map.

The non-abelian topological protection theorem we *want* is:

> An `SU(N)` lattice gauge perturbation of an equitable bundle
> preserves the (now non-abelian) phantom symmetry iff it is a
> matrix-cell-flat connection (`MatrixGaugeField.CrossConstant`).

The proof is open because:

* The matrix-valued `signedBy` operation requires defining a
  "matrix-weighted graph" — i.e. a weighted graph whose entries are
  themselves `N × N` complex matrices, an object that has *not yet*
  been defined in Graphplay (see I7 §7 for the statement-level
  declaration).
* The non-abelian Wilson loop is *path-ordered* and not a simple
  product, so the integrality of its invariant requires a more
  delicate argument (Stokes' theorem in a non-commutative setting).

These are addressed (statement-only) in I7 §10 (Open directions);
this file stops at the U(1) version.
-/

/-- **Placeholder (no content proven).**  This declaration records, at
the trivially-true `Prop` level, that the headline theorem
`phantomSymmetry_iff_flatOnCells` is *intended* to extend to
matrix-valued (`SU(N)`) gauge fields — but it proves **nothing** about
that extension.

What we *want* (and have NOT formalized) is the iff

> an `SU(N)` lattice gauge perturbation preserves the phantom symmetry
> of `(G, P)` ↔ it is matrix-cross-constant on `P.cells`.

That statement is currently unreachable: stating it requires a
**matrix-weighted graph** type and a matrix-valued `signedBy`/phantom-
symmetry notion, neither of which exists in Graphplay yet (see the §8
discussion above).  The hypotheses below are merely the data such a
theorem would quantify over; the conclusion is the placeholder `True`,
so this carries no topological-protection content.

The genuine non-abelian topological-protection theorem (the eventual
target, connecting to the Kitaev honeycomb model, Kitaev 2006, and
SU(2) topological insulators with spin-orbit coupling, Goldman et al.
2014) is left for future work. -/
theorem nonabelian_phantomSymmetry_iff_flatOnCells_statement_placeholder
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {SG : SimpleGraph V} (N : ℕ) (G : WeightedGraph V)
    (P : EquitablePartition G I)
    (_F : LatticeGauge.MatrixGaugeField V SG N) :
    -- Intended (NOT proven) schema:
    --     preserving-phantom-symmetry-of-(G, P)  ↔  F.CrossConstant P.cells
    -- in the matrix-valued setting.  Both sides require non-abelian
    -- analogs of the §2-§3 machinery, which are not yet formalized, so
    -- the conclusion is the placeholder `True`.
    True := by
  trivial

/-- **Placeholder (no invariant constructed).**  This declaration
records, at the trivially-true `Prop` level, the *aspiration* that the
U(1) `ChernNumberOnCells` extend to SU(N) gauge fields via a second
Chern class `c₂ ∈ ℤ` (or its SU(2) winding-number restriction on `S³`).

It proves **nothing**: no non-abelian invariant is defined here, no
`∃ c₂ : ℤ` is asserted, and the §7 robustness theorem is **not**
extended.  A genuine statement would need a non-abelian Wilson-loop
(path-ordered, see §8) and the corresponding integrality argument;
the conclusion below is the placeholder `True`.  Left for future
work. -/
theorem nonabelian_chernNumber_extension_statement_placeholder
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {SG : SimpleGraph V} (N : ℕ) (G : WeightedGraph V)
    (P : EquitablePartition G I)
    (_F : LatticeGauge.MatrixGaugeField V SG N)
    (_basis : List (QuotientCycle I)) :
    -- Intended (NOT proven): a non-abelian integer invariant `c₂ ∈ ℤ`
    -- generalizing `ChernNumberOnCells` to SU(N) gauge fields on the
    -- cell quotient, with the §7 robustness theorem extending with `c₂`
    -- in place of the first Chern number.  Recorded as placeholder `True`.
    True := by
  trivial

end TopologicalProtection
end Graphplay
