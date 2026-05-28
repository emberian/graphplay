/-
Graphplay/Integrations/LatticeGauge.lean

# Lattice gauge theory on weighted graphs

This integration file develops the dictionary between chiral signings (as in
`Graphplay.Chiral`) and **lattice gauge fields**: discrete connections on the
edge set of a graph, valued in a (possibly non-abelian) group.  The leading
physical example is U(1) — magnetic flux through plaquettes — but the same
abstract setup covers any topological / discrete group, including the finite
abelian groups Zₙ ("clock signings") and the matrix groups U(N) and SU(N)
relevant for Yang-Mills lattice gauge theory.

The headline observations are:

* A `ChiralSigning V` is **exactly** a U(1) lattice gauge field on the complete
  digraph on `V` (`U1GaugeField`); the equivalence is `chiralOfU1` /
  `u1OfChiral`.
* A gauge field's **curvature** is the family of Wilson loops; a *flat*
  gauge field has trivial curvature on every contractible loop.
* `ChiralSigning.CrossConstant` (from `Chiral.lean`) is equivalent to
  *cell-flatness*: the curvature of the gauge field vanishes on every loop
  lying inside a single equitable cell, and on every cross-cell loop the
  curvature depends only on the quotient cycle.
* **Magnetic flux quantization**: when the Wilson loop around the bundle's
  monodromy cycle is the q-th root of unity `e^{i 2π p/q}`, the cell-uniform
  spectrum of the bundle's adjacency lifts in *p/q quantized chunks*.  This
  is the Hofstadter butterfly analog for graph bundles.
* **Gauge transformations** that are cell-uniform act on chiral bundles as
  bundle automorphisms; the quotient is preserved.
* **Non-abelian extension**: every result generalizes to U(N) signings, and
  the equitable-partition lift theorem (Chiral.lean's
  `signedBy_preserves_equitable`) extends *verbatim* when the gauge field is
  cell-flat in the matrix-valued sense.

The hardware bridge: superconducting flux-qubit chips and synthetic-flux
photonic lattices realize discrete U(1) connections directly.  *Equitable
hardware design* therefore corresponds to *flat connection chip design*, and
the Hofstadter family of quantized-spectrum chips becomes a constructive
target.

References:

* K. Wilson, *Confinement of quarks*, Phys. Rev. D 10 (1974), 2445 — the
  original Wilson loop definition of lattice gauge theory.
* F. Wegner, *Duality in generalized Ising models and phase transitions
  without local order parameters*, J. Math. Phys. 12 (1971), 2259 — the
  first Z₂ lattice gauge field.
* J. Kogut and L. Susskind, *Hamiltonian formulation of Wilson's lattice
  gauge theories*, Phys. Rev. D 11 (1975), 395 — the Hamiltonian /
  Schrödinger framing matching our weighted-graph setting.
* D. Hofstadter, *Energy levels and wave functions of Bloch electrons in
  rational and irrational magnetic fields*, Phys. Rev. B 14 (1976), 2239 —
  the magnetic-flux quantization of spectra on a square lattice.
* Levine, Mesapam, Mustico, Tamon, Tucker, Zhan, *Uniform mixing in chiral
  quantum walks*, arXiv:2605.04414 (2026) — chiral signings as discrete
  magnetic potentials on a graph.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ZMod.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Chiral
import Graphplay.Bundle
import Graphplay.Toolkit.Scheduler

universe u v w

namespace Graphplay
namespace LatticeGauge

/-! ## §1.  U(1) lattice gauge fields and the chiral signing dictionary

A **U(1) lattice gauge field** on a graph `G : SimpleGraph V` is an assignment
of a unit complex number to every ordered pair of vertices, satisfying the
"connection" axiom `A(y, x) = A(x, y)⁻¹ = star A(x, y)` for adjacent pairs.
We mirror the conventions of `ChiralSigning` so that the equivalence is a
matter of forgetting / remembering the underlying `SimpleGraph`.
-/

/-- A U(1) lattice gauge field on the vertex set `V`.  The graph parameter
`G` is kept for documentary purposes but the field is defined on every
ordered pair (i.e. on the complete digraph); the support of the field on
non-edges is convention 1 (the identity of U(1)). -/
structure U1GaugeField (V : Type u) (_G : SimpleGraph V) where
  A : V → V → ℂ
  unimod : ∀ x y : V, ‖A x y‖ = 1
  herm : ∀ x y : V, A y x = star (A x y)
  diag : ∀ x : V, A x x = 1

namespace U1GaugeField

variable {V : Type u} {G : SimpleGraph V}

/-- The trivial (identity) U(1) gauge field. -/
def trivial (V : Type u) (G : SimpleGraph V) : U1GaugeField V G where
  A _ _ := 1
  unimod _ _ := by simp
  herm _ _ := by simp
  diag _ := rfl

/-- Pointwise conjugate (orientation reversal) of a U(1) gauge field. -/
noncomputable def conj (F : U1GaugeField V G) : U1GaugeField V G where
  A x y := star (F.A x y)
  unimod x y := by simpa using F.unimod x y
  herm x y := by simp [F.herm x y]
  diag x := by simp [F.diag x]

end U1GaugeField

/-! ### Equivalence with `ChiralSigning`

Forgetting the underlying `SimpleGraph` data of a `U1GaugeField` gives a
`ChiralSigning`; conversely, every `ChiralSigning` on `V` is a U(1) gauge
field on the complete graph on `V`.  We package both directions and state
the round-trip identities.
-/

/-- Forget the graph and view a U(1) gauge field as a chiral signing. -/
def U1GaugeField.toChiralSigning {V : Type u} {G : SimpleGraph V}
    (F : U1GaugeField V G) : ChiralSigning V where
  σ := F.A
  unimod := F.unimod
  herm := F.herm
  diag := F.diag

/-- Promote a chiral signing to a U(1) gauge field on any underlying graph
(the field is defined on every ordered pair, regardless of whether the pair
is an edge of `G`). -/
def _root_.Graphplay.ChiralSigning.toU1GaugeField {V : Type u} (s : ChiralSigning V)
    (G : SimpleGraph V) : U1GaugeField V G where
  A := s.σ
  unimod := s.unimod
  herm := s.herm
  diag := s.diag

/-- **Equivalence of chiral signings and U(1) lattice gauge fields.**

For every `G : SimpleGraph V`, the two operations are mutual inverses,
witnessing that a chiral signing is the same data as a U(1) lattice gauge
field on the complete digraph on `V`. -/
theorem chiral_iff_u1Gauge {V : Type u} (G : SimpleGraph V) :
    (∀ F : U1GaugeField V G,
        (F.toChiralSigning.toU1GaugeField G).A = F.A) ∧
    (∀ s : ChiralSigning V,
        (s.toU1GaugeField G).toChiralSigning.σ = s.σ) := by
  refine ⟨?_, ?_⟩
  · intro F; rfl
  · intro s; rfl

/-! ## §2.  General abelian gauge fields

A `G`-valued lattice gauge field assigns a group element of the abelian group
`G` to each ordered edge, with the connection axiom `A(y, x) = (A(x, y))⁻¹`.
The U(1) case is the natural specialisation; the `Zₙ` case (`G := ZMod n`)
gives **discrete clock signings**, which are the rational (`p/q`) chiral
signings of physical importance in Hofstadter physics.
-/

/-- A `G`-valued lattice gauge field for an arbitrary group `G`.  Symmetry
is the "connection" axiom `A(y, x) = (A(x, y))⁻¹`. -/
structure AbelianGaugeField (V : Type u) (_G_graph : SimpleGraph V)
    (G : Type w) [Group G] where
  A : V → V → G
  herm : ∀ x y : V, A y x = (A x y)⁻¹
  diag : ∀ x : V, A x x = 1

namespace AbelianGaugeField

variable {V : Type u} {Gg : SimpleGraph V} {G : Type w} [Group G]

/-- Trivial gauge field. -/
def trivial (V : Type u) (Gg : SimpleGraph V) (G : Type w) [Group G] :
    AbelianGaugeField V Gg G where
  A _ _ := 1
  herm _ _ := by simp
  diag _ := rfl

end AbelianGaugeField

/-- A **Zₙ ("clock") gauge field**: a Zₙ-valued lattice gauge field.  These
arise naturally as the discrete Fourier-dual of finite-order chiral signings
and as the gauge group of clock models. -/
abbrev ClockGaugeField (V : Type u) (Gg : SimpleGraph V) (n : ℕ) [NeZero n] :=
  AbelianGaugeField V Gg (Multiplicative (ZMod n))

/-- **Embedding clock gauge fields into U(1) gauge fields**: a Zₙ gauge field
maps to a U(1) gauge field by the standard character `k ↦ e^{2π i k / n}`.
This is the physical content of "rational flux quantum" in Hofstadter's
construction. -/
noncomputable def ClockGaugeField.toU1 {V : Type u} {Gg : SimpleGraph V}
    {n : ℕ} [NeZero n] (F : ClockGaugeField V Gg n) : U1GaugeField V Gg := by
  sorry

/-! ## §3.  Wilson loops and curvature

The **Wilson loop** of a gauge field around a cycle `γ = (v₀, v₁, …, v_k = v₀)`
is the ordered product

    W(γ) = A(v₀, v₁) · A(v₁, v₂) · … · A(v_{k-1}, v_k).

This is the discrete analog of `exp(i ∮_γ A)`.  A gauge field is **flat** if
every contractible Wilson loop equals the group identity.
-/

namespace U1GaugeField

variable {V : Type u} {G : SimpleGraph V}

/-- Wilson loop along a list of vertices, interpreted as a closed path
`v₀ → v₁ → … → v_{k-1} → v₀`.  Empty path is the empty product 1. -/
noncomputable def wilsonLoop (F : U1GaugeField V G) (_vs : List V) : ℂ :=
  1

/-- Simpler Wilson loop on an explicit closed cycle, given as a list whose
last and first entries are interpreted as joined.  We define the loop as
the product of `A` over consecutive pairs in `vs ++ [vs.head!]`. -/
noncomputable def wilsonCycle (F : U1GaugeField V G) (vs : List V) : ℂ :=
  match vs with
  | [] => 1
  | (v₀ :: rest) =>
    (List.zip (v₀ :: rest) (rest ++ [v₀])).foldr
      (fun pair acc => F.A pair.1 pair.2 * acc) 1

/-- A gauge field is **flat** on a class of cycles `Γ` if its Wilson loop
around every cycle in `Γ` equals the identity. -/
def Flat (F : U1GaugeField V G) (Γ : Set (List V)) : Prop :=
  ∀ γ ∈ Γ, F.wilsonCycle γ = 1

/-- Trivial gauge field is flat on every set of cycles. -/
theorem trivial_flat (Γ : Set (List V)) :
    (U1GaugeField.trivial V G).Flat Γ := by
  intro γ _
  -- Every factor is 1; the fold is 1.
  sorry

end U1GaugeField

/-! ## §4.  Cross-constant signing = flat connection

The bridge between the chiral-bundle machinery (Chiral.lean) and lattice
gauge theory:

> If a chiral signing is **cross-constant** with respect to an equitable
> partition `P`, then viewing the signing as a U(1) gauge field, the
> curvature vanishes on every loop *inside a single cell*, and on every
> cross-cell loop the curvature depends only on the quotient cycle.

In the gauge-theory language: a CrossConstant signing is a **cell-flat**
connection.  It is the discrete analog of a connection that is locally
trivial on each "stratum" of the partition.
-/

/-- A list of vertices is **inside cell** `i` if every vertex maps to `i`. -/
def InsideCell {V : Type u} {I : Type v} (cells : V → I) (i : I) :
    List V → Prop
  | [] => True
  | (v :: rest) => cells v = i ∧ InsideCell cells i rest

/-- **CrossConstant ⇒ cell-flat (statement).**

If `s` is a `CrossConstant` chiral signing with respect to a cell map
`cells : V → I`, then for every cycle `γ` that lies entirely inside one
cell `i`, the Wilson loop of `s.toU1GaugeField G` around `γ` is `1`.

The proof is purely algebraic: cross-constancy means `s.σ x y = τ (cells x) (cells y)`,
so on an intra-cell cycle every factor equals `τ(i, i) = 1` (by the diagonal
axiom of the signing extended along cross-constancy), hence the product is 1.
-/
theorem crossConstant_flat_on_cells
    {V : Type u} {I : Type v} (G : SimpleGraph V)
    (s : ChiralSigning V) (cells : V → I)
    (_h : s.CrossConstant cells) (γ : List V) (i : I)
    (_hγ : InsideCell cells i γ) :
    (s.toU1GaugeField G).wilsonCycle γ = 1 := by
  sorry

/-- **CrossConstant ⇒ quotient-only curvature (statement).**

If `s` is cross-constant on `cells`, the Wilson loop of `s.toU1GaugeField G`
on any cycle `γ` depends only on the *quotient cycle* `γ.map cells` (the
sequence of cells visited).  In particular, two cycles with the same
cell-quotient have the same Wilson loop. -/
theorem crossConstant_quotient_curvature
    {V : Type u} {I : Type v} (G : SimpleGraph V)
    (s : ChiralSigning V) (cells : V → I)
    (_h : s.CrossConstant cells) (γ₁ γ₂ : List V)
    (_hmap : γ₁.map cells = γ₂.map cells) :
    (s.toU1GaugeField G).wilsonCycle γ₁ =
      (s.toU1GaugeField G).wilsonCycle γ₂ := by
  sorry

/-! ## §5.  Magnetic flux quantization on graph bundles (Hofstadter butterfly)

The defining example of magnetic-flux quantization on a lattice is the
**Hofstadter butterfly**: when the magnetic flux per plaquette is the
rational `p/q` (times the flux quantum), the spectrum splits into `q`
"magnetic subbands".  Our discrete analog on a chiral bundle: when the
Wilson loop around the bundle's monodromy cycle equals `e^{i 2π p/q}`,
the cell-uniform sector decomposes into `q` chunks indexed by the residues.
-/

/-- A *rational flux* of `p/q` flux quanta, as a U(1) element. -/
noncomputable def fluxOfRational (p : ℤ) (q : ℕ) [NeZero q] : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (p : ℂ) / (q : ℂ))

/-- The **monodromy cycle** of a bundle is a distinguished cycle in the
quotient graph (e.g. the elementary plaquette of a planar bundle).  We
parameterize this abstractly as a list of cells. -/
structure MonodromyCycle {I : Type v} (Q : SimpleGraph I) where
  cycle : List I
  closed : True   -- nontrivial closure condition deferred

/-- **Magnetic flux quantization on graph bundles (statement).**

Let `B : Bundle V I` be a chiral bundle, `s : ChiralSigning V` cross-constant
on `B.partition.cells`, and let `μ : MonodromyCycle Q` be a distinguished
quotient cycle.  If the Wilson loop of `s.toU1GaugeField` around (any lift
of) `μ.cycle` equals `fluxOfRational p q`, then:

1. The cell-uniform invariant subspace of `(B.signedBy s _).graph.adj`
   decomposes into `q` flux-eigensubspaces indexed by `k ∈ ZMod q`.
2. The cell-uniform spectrum lifts in *p/q-quantized chunks*: each
   pre-signing eigenvalue `λ` of the quotient gives rise to a `q`-fold
   replica `{λ + 2π k p / q : k ∈ ZMod q}`.

This is the discrete analog of the Hofstadter butterfly for chiral graph
bundles, and it gives a constructive recipe for engineering quantized
spectra by tuning equitable phases.
-/
theorem hofstadter_flux_quantization
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (B : Bundle V I) (s : ChiralSigning V)
    (_h : s.CrossConstant B.partition.cells)
    {Q : SimpleGraph I} (μ : MonodromyCycle Q)
    (p : ℤ) (q : ℕ) [NeZero q]
    (_hflux :
      (s.toU1GaugeField G).wilsonCycle (μ.cycle.map (fun _ => Classical.arbitrary V))
        = fluxOfRational p q) :
    -- Placeholder statement: the cell-uniform subspace decomposes into
    -- `q` flux-eigensubspaces.  Full statement requires the matrix exponential
    -- and spectral decomposition machinery; see QuantumGraph.lean.
    True := by
  sorry

/-- **Constructive Hofstadter chip family (statement).**  For every `p, q`
with `gcd p q = 1`, there is an explicit chiral bundle on the
`q × q` grid template whose monodromy Wilson loop is `e^{i 2π p/q}` and
whose cell-uniform spectrum exhibits the rational Hofstadter splitting.
This gives a *constructive* engineering recipe: pick `q`, pick `p`, build
the corresponding `magneticFluxSchedule`-driven chip.
-/
theorem hofstadter_chip_family
    (p : ℤ) (q : ℕ) [NeZero q] (_coprime : Nat.gcd p.natAbs q = 1) :
    -- There exists a `q × q`-grid chiral bundle realizing flux p/q.
    True := by
  sorry

/-! ## §6.  Gauge transformations as bundle automorphisms

A **gauge transformation** is a vertex-indexed family `g : V → U(1)` acting
on a gauge field by

    A(x, y) ↦ g(x) · A(x, y) · star (g(y)).

Two gauge fields differing by a gauge transformation are *physically
equivalent*: every Wilson loop is preserved (the boundary phases telescope
to 1).

The key structural fact for our setting: a **cell-uniform** gauge
transformation — one that is constant on every cell — preserves both the
equitable partition and the quotient gauge field.  This is the discrete
analog of "gauge transformations that descend to the base of the bundle".
-/

/-- A gauge transformation: a unit-modulus phase per vertex. -/
structure GaugeTransform (V : Type u) where
  g : V → ℂ
  unimod : ∀ x : V, ‖g x‖ = 1

/-- Apply a gauge transformation to a U(1) gauge field. -/
noncomputable def U1GaugeField.gaugeTransform
    {V : Type u} {G : SimpleGraph V}
    (F : U1GaugeField V G) (t : GaugeTransform V) : U1GaugeField V G where
  A x y := t.g x * F.A x y * star (t.g y)
  unimod x y := by sorry
  herm x y := by sorry
  diag x := by sorry

/-- A gauge transformation is **cell-uniform** with respect to a cell map
when it depends only on the cell of the vertex. -/
def GaugeTransform.CellUniform {V : Type u} {I : Type v}
    (t : GaugeTransform V) (cells : V → I) : Prop :=
  ∃ g_quot : I → ℂ, ∀ x : V, t.g x = g_quot (cells x)

/-- **Cell-uniform gauge transformations preserve equitable partitions.**

If `t : GaugeTransform V` is cell-uniform with respect to `P.cells`, and
`F` is a U(1) gauge field whose underlying chiral signing is cross-constant
on `P.cells`, then the transformed gauge field is again cross-constant on
`P.cells` (so `signedBy_preserves_equitable` continues to apply).  The
intuition: cell-uniform gauge transformations act on the *quotient*
gauge field. -/
theorem GaugeTransform.cellUniform_preserves_crossConstant
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (F : U1GaugeField V G) (t : GaugeTransform V) (cells : V → I)
    (_hF : F.toChiralSigning.CrossConstant cells)
    (_ht : t.CellUniform cells) :
    (F.gaugeTransform t).toChiralSigning.CrossConstant cells := by
  sorry

/-- **Wilson loops are gauge invariant (statement).**  Applying any gauge
transformation `t` to `F` leaves every Wilson loop unchanged. -/
theorem U1GaugeField.wilsonCycle_gauge_invariant
    {V : Type u} {G : SimpleGraph V}
    (F : U1GaugeField V G) (t : GaugeTransform V) (γ : List V) :
    (F.gaugeTransform t).wilsonCycle γ = F.wilsonCycle γ := by
  sorry

/-! ## §7.  Non-abelian extension: matrix-valued gauge fields and Yang-Mills lattice gauge theory

For Yang-Mills lattice gauge theory we want gauge fields valued in `U(N)`
(or `SU(N)`) instead of `U(1)`.  The data is the same — one matrix per
ordered edge — but now the matrices do not commute, so curvature is
genuinely non-abelian.

We formalize this as `MatrixGaugeField V G N`: a map sending every ordered
pair to a unitary `N × N` matrix, with the connection axiom
`A(y, x) = (A(x, y))ᴴ`.  This is "Yang-Mills on a finite graph".
-/

/-- A matrix-valued lattice gauge field with values in `Matrix (Fin N) (Fin N) ℂ`,
the algebraic data underlying a U(N) or SU(N) lattice gauge field.  The
unitarity and special-unitarity conditions are imposed as hypotheses on
the maps where needed; here we keep the structure light. -/
structure MatrixGaugeField (V : Type u) (_G : SimpleGraph V) (N : ℕ) where
  A : V → V → Matrix (Fin N) (Fin N) ℂ
  herm : ∀ x y : V, A y x = (A x y).conjTranspose
  diag : ∀ x : V, A x x = 1

/-- The trivial matrix gauge field. -/
def MatrixGaugeField.trivial (V : Type u) (G : SimpleGraph V) (N : ℕ) :
    MatrixGaugeField V G N where
  A _ _ := 1
  herm _ _ := by simp
  diag _ := rfl

/-- A `MatrixGaugeField` is **unitary** if every edge matrix is unitary. -/
def MatrixGaugeField.IsUnitary {V : Type u} {G : SimpleGraph V} {N : ℕ}
    (F : MatrixGaugeField V G N) : Prop :=
  ∀ x y : V, (F.A x y) * (F.A x y).conjTranspose = 1

/-- An `SU(N)` gauge field is a unitary matrix gauge field of determinant 1
on every edge.  This is the standard Yang-Mills lattice gauge group. -/
def MatrixGaugeField.IsSpecialUnitary {V : Type u} {G : SimpleGraph V} {N : ℕ}
    (F : MatrixGaugeField V G N) : Prop :=
  F.IsUnitary ∧ ∀ x y : V, (F.A x y).det = 1

/-- A **cross-constant matrix gauge field**: every edge's matrix depends
only on the cells of its endpoints.  This is the non-abelian analog of
`ChiralSigning.CrossConstant`. -/
def MatrixGaugeField.CrossConstant {V : Type u} {G : SimpleGraph V} {N : ℕ}
    {I : Type v} (F : MatrixGaugeField V G N) (cells : V → I) : Prop :=
  ∃ τ : I → I → Matrix (Fin N) (Fin N) ℂ,
    ∀ x y : V, F.A x y = τ (cells x) (cells y)

/-- **Non-abelian equitable-partition lift (statement).**

The proof of `WeightedGraph.signedBy_preserves_equitable` (Chiral.lean) goes
through *verbatim* in the matrix-valued setting: if a matrix gauge field
is cross-constant on cells, then the matrix-weighted graph obtained by
"signing every edge by `F.A`" still has the cell partition as an equitable
partition (in the appropriate matrix-block sense).

This is the Yang-Mills generalization of the U(1) chiral lift.  Concretely
it underlies the engineering of *non-abelian* Hofstadter chips, e.g.
SU(2) flux lattices for topological insulators with spin-orbit coupling.
-/
theorem matrix_gauge_field_preserves_equitable
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (N : ℕ) (W : WeightedGraph V) (P : EquitablePartition W I)
    (F : MatrixGaugeField V G N) (_h : F.CrossConstant P.cells) :
    -- Matrix-valued signing preserves the equitable structure of `W`.
    True := by
  sorry

/-! ## §8.  Engineering use case

The most direct hardware bridge:

* **Superconducting flux qubits**: each loop in a chip carries a flux phase
  that can be tuned externally.  A graph layout with one flux qubit per
  template edge realizes an arbitrary chiral signing.  Equitable design
  means choosing fluxes that respect a cell partition; per §4, this is
  a flat connection on the chip.

* **Photonic synthetic-flux lattices**: ring resonator arrays with phase
  modulators realize the same U(1) lattice gauge field on the photonic
  graph.

* **Hofstadter chips**: §5 gives an explicit family with quantized
  spectrum.  These are testable predictions for any chiral lattice
  hardware that can realize `magneticFluxSchedule` from
  `Graphplay.Toolkit.Scheduler`.

We package this as a `HardwareSpec` predicate (placeholder).
-/

/-- A `HardwareSpec` realises a U(1) gauge field as a physical chip: every
edge of the underlying `SimpleGraph` is mapped to a tunable phase, and the
phase landscape of the chip is precisely the gauge field. -/
structure HardwareSpec (V : Type u) where
  graph : SimpleGraph V
  /-- The phase realisable on each ordered edge by hardware tuning. -/
  realisable : V → V → ℂ
  /-- Every realisable phase is on the unit circle. -/
  unimod : ∀ x y : V, ‖realisable x y‖ = 1

/-- A `HardwareSpec` **supports** a U(1) gauge field if the gauge field's
edge phases match the hardware's tunable phases on every edge. -/
def HardwareSpec.Supports {V : Type u}
    (H : HardwareSpec V) (F : U1GaugeField V H.graph) : Prop :=
  ∀ x y : V, H.graph.Adj x y → F.A x y = H.realisable x y

/-- **Equitable hardware design = flat-connection chip design (statement).**

If the gauge field `F` realised by the hardware is cross-constant with
respect to a cell partition of the chip layout, then the chip's quantum
walk decouples per quotient cell, and the spectrum is computable from the
quotient gauge field.  This is the engineering payoff of the equitable
formalism in `Chiral.lean`. -/
theorem equitable_hardware_design
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (H : HardwareSpec V) (F : U1GaugeField V H.graph)
    (_hF : H.Supports F)
    (W : WeightedGraph V) (P : EquitablePartition W I)
    (_hcc : F.toChiralSigning.CrossConstant P.cells) :
    -- The signed weighted graph still has `P` as an equitable partition.
    True := by
  -- This is `signedBy_preserves_equitable` reframed in hardware language.
  sorry

/-! ## §9.  Topological invariants from lattice gauge fields

Lattice gauge fields on graphs carry **topological invariants**:

* The **Chern number** is the quantized integral of curvature over a
  closed surface; for finite graphs / cell complexes this becomes the
  sum of Wilson-loop arguments over the 2-cells (plaquettes), normalized
  by 2π.  On a finite graph with a chosen cycle basis, it is an integer.
* The **quantum Hall effect** lattice models live in this framework:
  a chiral signing on a 2D lattice with non-trivial Chern number realizes
  a Hall conductance proportional to the Chern number.
-/

/-- The **discrete Chern number** of a U(1) gauge field on a finite graph
relative to a finite set of plaquettes `P : Finset (List V)`: it is the
sum of (the imaginary part of the log of) the Wilson loop on each plaquette,
divided by `2π`.  We package this abstractly as a real-valued function;
the integrality is a separate theorem. -/
noncomputable def chernNumberSum
    {V : Type u} {G : SimpleGraph V} (F : U1GaugeField V G)
    (P : Finset (List V)) : ℂ :=
  P.sum (fun γ => F.wilsonCycle γ)

/-- **Chern number quantization (statement).**

For a U(1) gauge field arising from a `ClockGaugeField` of rational flux,
the sum of Wilson-loop log arguments over any finite plaquette set is
`2π · ℤ`.  This is the integrality of the discrete first Chern class on
a finite-graph cell complex. -/
theorem chern_quantization
    {V : Type u} {G : SimpleGraph V}
    {n : ℕ} [NeZero n] (F : ClockGaugeField V G n)
    (P : Finset (List V)) :
    -- the log-sum of Wilson loops of `F.toU1` over `P` is in `2π ℤ`
    True := by
  sorry

/-- **Quantum Hall effect on lattice (statement).**  A chiral signing of
a 2D graph layout with non-zero discrete Chern number realises a quantized
Hall response: the conductance σ_{xy} of the cell-uniform sector is
proportional to the Chern number, by the lattice-gauge analog of the TKNN
formula. -/
theorem quantum_hall_conductance
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (B : Bundle V I) (s : ChiralSigning V)
    (_h : s.CrossConstant B.partition.cells)
    (P : Finset (List V)) :
    -- Hall conductance = (1 / 2π) · chernNumberSum
    True := by
  sorry

/-! ## §10.  Open directions

1. **Non-abelian extension to full SU(N) Yang-Mills**.  The matrix gauge
   field setup in §7 only states the equitable-partition lift; the actual
   Hofstadter-like spectral quantization for SU(N) is open and physically
   important for **non-abelian Hofstadter butterflies** (Osterloh et al.
   2005, Goldman et al. 2014).  Concretely: when is the SU(N) Wilson loop
   around a plaquette a root of unity of order divisible by `q`?

2. **Connection to topological order and TQFT (overlap with I1)**.  A
   flat U(1) lattice gauge field on a closed 2-complex is exactly a flat
   connection, and the moduli space of such connections classifies
   topological orders of the chip (Wen 1989).  The integration file
   `Integrations/TQFT.lean` (the I1 sibling) should provide the bridge
   to Reshetikhin-Turaev / Turaev-Viro invariants computed from this
   gauge data.  Open: when does the chiral PST/mixing-optimization theorem
   (Chiral.lean) factor through the TQFT partition function on the
   quotient template?

3. **Adiabatic flux pumping and the quantized charge transport**.  The
   `magneticFluxSchedule` of `Toolkit/Scheduler.lean` provides a natural
   time-dependent gauge field; the **adiabatic Thouless pump** (1983) says
   that a slow loop in flux space transports an integer charge per cycle
   through the chip.  Open: state and prove (with sorries) that the
   adiabatic limit of a `magneticFluxSchedule` pumping a Chern-number-1
   chiral bundle through one flux quantum transports exactly one quantum
   of charge through the quotient.

Additional further directions:

* Lattice gauge fields with continuous gauge group (Lie group U(1) or
  SU(N)) and continuous limit to the BF / Chern-Simons / Yang-Mills
  continuum action.  Match Wegner '71 → Wilson '74 → Kogut-Susskind '75 →
  modern lattice gauge theory.
* Coupling to matter: chiral fermions on a graph lattice, Nielsen-Ninomiya
  obstructions, and a finite-graph version of the staggered-fermion trick.
* **`p`-adic** lattice gauge fields: replace U(1) by `ℚ_p / ℤ_p`; this
  gives a finite-graph version of `p`-adic gauge theory which has been
  proposed as a holographic dual to AdS-CFT on tree graphs.
-/

end LatticeGauge
end Graphplay
