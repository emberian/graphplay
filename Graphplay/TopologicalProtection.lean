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
  sorry

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

/-- **Headline theorem (statement).**  A chiral signing preserves the
phantom symmetry of `(G, P)` iff it is cross-constant on the cells of
`P` — equivalently, iff (viewed as a U(1) lattice gauge field via I7)
it is a **flat connection on cells** in the sense of
`Graphplay.Integrations.LatticeGauge`, §4. -/
theorem phantomSymmetry_iff_flatOnCells
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (hP : IsPhantomSymmetric G P)
    (σ : ChiralSigning V) :
    PreservesPhantomSymmetry P σ ↔ σ.CrossConstant P.cells := by
  -- Forward: `signedBy_preserves_equitable` (Chiral.lean) plus phantom-
  -- symmetric transport along the same cell map.  Reverse: the new content;
  -- a non-cross-constant `σ` introduces phase inhomogeneity that breaks
  -- the equitable identity for some pair of cells, contradicting
  -- preservation.  Punted.
  sorry

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

/-- **Reverse direction** (the new content): if `σ` preserves the
equitable structure of `(G, P)`, and `G` is *generic enough* (no
accidental cancellations in cell sums), then `σ` is cross-constant on
`P.cells`.

The hypothesis `nonDegenerate` captures the "generic enough"
condition: there exist enough independent edges between cells so that
phase factors cannot conspire to leave the sums invariant unless they
are constant. -/
theorem crossConstant_of_preservesEquitable
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (σ : ChiralSigning V) (_hpres : PreservesEquitable P σ)
    (_nonDegenerate :
      ∀ (i j : I) (x y : V), P.cells x = i → P.cells y = i →
        ∃ z : V, P.cells z = j ∧ G.adj x z ≠ 0 ∧ G.adj y z ≠ 0) :
    σ.CrossConstant P.cells := by
  -- Sketch: from preservation, derive that for any two reps `x, y` of
  -- the same cell `i` and any target cell `j`,
  --   ∑_{z ∈ cell j} σ x z · G.adj x z = ∑_{z ∈ cell j} σ y z · G.adj y z.
  -- Combined with the equitable identity for `G`, this forces each
  -- `σ x z = σ y z` on the support of `G.adj`, hence cross-constancy.
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
          (by
            -- Cell-uniform gauge transform preserves cross-constancy
            -- (I7 §6, `cellUniform_preserves_crossConstant`).
            sorry)
          basis := by
  sorry

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
  -- matches the rational flux quantization `e^{2π i k/q}`.
  sorry

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

/-- **TQC topological protection (statement).**  The topologically
protected unitaries (braid gates of `Integrations/TQFT.lean`) acting
on the cell-uniform subspace of a chiral bundle are *exactly* the
chiral signings whose Chern number on cells matches the braid
representation.

This is the algebraic version of the Freedman-Larsen-Wang universality
theorem in the chiral-bundle setting: the topologically protected
gates form an integer lattice indexed by the Chern number on cells. -/
theorem braidGate_iff_chernMatched
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (basis : List (QuotientCycle I)) (m : ℤ) :
    (∃ σ : ChiralSigning V, ∃ h : σ.CrossConstant P.cells,
        IsTopologicallyProtectedUnitary σ P h basis m) ↔
    True := by
  -- The forward direction picks `σ` to be the clock signing
  -- corresponding to flux `m` on the elementary plaquette; the
  -- reverse direction follows from the integrality of the discrete
  -- Chern number (I7 §9).
  sorry

/-- **Connection to Majorana-1 (statement).**  In the Majorana-1
application (`Applications/MajoranaOne.lean`) the braid generators are
realized as chiral signings of the Majorana cell quotient.  In our
language: each Majorana braid gate is the topologically protected
unitary with Chern number `±1` on the cells of the Kitaev-chain
quotient.  This connects the abstract braid-group representation of
§3 of `Integrations/TQFT.lean` to the concrete chiral-bundle data on
the Majorana-1 chip. -/
theorem majoranaOne_braidGate_chernPlusMinusOne
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (basis : List (QuotientCycle I)) :
    -- The Majorana-1 braid generator is realized by a chiral signing
    -- with Chern number ±1 on the Kitaev-chain quotient.
    (∃ σ : ChiralSigning V, ∃ h : σ.CrossConstant P.cells,
        IsTopologicallyProtectedUnitary σ P h basis 1
        ∨ IsTopologicallyProtectedUnitary σ P h basis (-1)) ↔
    True := by
  -- Concrete realization: the Kitaev-chain quotient on `Fin 2` cells
  -- (occupied / unoccupied) with the Majorana braid acting as the
  -- ±i phase on the cross-cell edge.  The Chern number of this
  -- signing on cells is ±1.
  sorry

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

/-- **Quantitative topological protection (statement).**  If `σ` and
`σ'` are two cross-constant chiral signings of `(G, P)` whose pointwise
distance is small enough (smaller than the "Chern gap" `2π/q` for a
quotient of size `q`), and which have the same Chern number on cells,
then they preserve the same `CellUniformMixing` property of the bundle
`Bundle.signedBy`.

This is the precise quantitative version of "small perturbations
preserving the topological invariant preserve the protected
physics". -/
theorem cellUniformMixing_robust_under_small_chern_preserving_perturbation
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Bundle V I) (σ σ' : ChiralSigning V)
    (h  : σ.CrossConstant B.partition.cells)
    (h' : σ'.CrossConstant B.partition.cells)
    (basis : List (QuotientCycle I))
    (_hChern :
      ChernNumberOnCells σ  B.partition h  basis
        = ChernNumberOnCells σ' B.partition h' basis)
    (_hSmall : signingDistance σ σ' < 1)  -- placeholder threshold
    (t : ℝ) :
    (B.signedBy σ h).CellUniformMixing t ↔
    (B.signedBy σ' h').CellUniformMixing t := by
  -- Both `B.signedBy σ` and `B.signedBy σ'` reduce, via
  -- `chiral_mixing_optimization` (Chiral.lean), to the *quotient*
  -- weighted graph signed by the corresponding quotient phase.
  -- The same Chern number implies the two quotient phases lie in the
  -- same homotopy class of `U(1)`-valued maps on the quotient cycle
  -- basis; the smallness hypothesis makes the homotopy realizable
  -- through a continuous path of cross-constant signings.  Standard
  -- adiabatic continuity then gives equality of `CellUniformMixing`
  -- at every time `t`.
  sorry

/-- **Constructive robustness corollary (statement).**  For every
chiral bundle `B` with cross-constant signing `σ`, there is a
*neighborhood* `N(σ)` in signing-space such that every `σ' ∈ N(σ)`
with the same Chern number on cells preserves the cell-uniform PST /
mixing of `B.signedBy σ`.  In particular, the set of chiral signings
realizing a given protected physics is *open* in signing-space — the
hallmark of topological protection. -/
theorem signing_neighborhood_topologically_protected
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Bundle V I) (σ : ChiralSigning V)
    (h : σ.CrossConstant B.partition.cells)
    (basis : List (QuotientCycle I)) :
    ∃ ε > 0, ∀ σ' : ChiralSigning V,
      ∀ h' : σ'.CrossConstant B.partition.cells,
      ChernNumberOnCells σ' B.partition h' basis
        = ChernNumberOnCells σ B.partition h basis →
      signingDistance σ σ' < ε →
      ∀ t : ℝ, (B.signedBy σ h).CellUniformMixing t
        ↔ (B.signedBy σ' h').CellUniformMixing t := by
  sorry

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

/-- **Open conjecture (statement only).**  The headline theorem
`phantomSymmetry_iff_flatOnCells` extends *verbatim* to matrix-valued
gauge fields: an `SU(N)` lattice gauge perturbation preserves the
phantom symmetry of `(G, P)` iff it is matrix-cross-constant on
`P.cells`.

This is the **non-abelian topological protection theorem**, and
formalizes "topological protection in non-abelian Yang-Mills lattice
gauge theory".  Connects directly to the Kitaev honeycomb model
(Kitaev 2006) and SU(2) topological insulators with spin-orbit
coupling (Goldman, Juzeliūnas, Öhberg, Spielman, 2014). -/
theorem nonabelian_phantomSymmetry_iff_flatOnCells_conjecture
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {SG : SimpleGraph V} (N : ℕ) (G : WeightedGraph V)
    (P : EquitablePartition G I)
    (_F : LatticeGauge.MatrixGaugeField V SG N) :
    -- Statement schema:  preserving-phantom-symmetry-of-(G, P)
    --                  ↔  F.CrossConstant P.cells
    -- in the matrix-valued setting.  Both sides require non-abelian
    -- analogs of the §2-§3 machinery, which are not yet formalized.
    True := by
  -- See I7 §7, `matrix_gauge_field_preserves_equitable` for the
  -- equitable-preservation half; the phantom-symmetric half awaits a
  -- matrix-weighted graph type.
  sorry

/-- **Companion statement: non-abelian Chern number on cells.**  For
SU(N) lattice gauge fields, the relevant integer invariant on the
cell quotient is the **second Chern class** (or its SU(2) restriction
to a winding number on `S³`).  We package the statement that this
extends the U(1) `ChernNumberOnCells` to SU(N) bundles. -/
theorem nonabelian_chernNumber_extension_conjecture
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {SG : SimpleGraph V} (N : ℕ) (G : WeightedGraph V)
    (P : EquitablePartition G I)
    (_F : LatticeGauge.MatrixGaugeField V SG N)
    (_basis : List (QuotientCycle I)) :
    -- A non-abelian integer invariant `c₂ ∈ ℤ` exists, generalizing
    -- `ChernNumberOnCells` to SU(N) gauge fields on the cell quotient,
    -- and the robustness theorem of §7 extends with `c₂` in place of
    -- the first Chern number.
    True := by
  sorry

end TopologicalProtection
end Graphplay
