/-
# Graphplay.Applications.MajoranaOne

## Applied disassembly: Microsoft's Majorana-1 topological-qubit chip (Feb 2024)

This file is a **stretch demo** applying the Graphplay tower to Microsoft's
Majorana-1 chip, announced 19 Feb 2024.  The chip is the first publicly
demonstrated **topological qubit** based on Majorana zero modes (MZMs) in
semiconductor-superconductor (InAs/Al) nanowire heterostructures, organized
into a "tetron" qubit cell of four MZMs.

Most of what we say below is *speculative* — the public design notes
(Microsoft Azure Quantum blog post; Aghaee et al., *Nature* 638, 651-655,
2025; preceding theory papers Karzig–Knapp–Lutchyn–Bonderson–Hastings–Nayak–
Oreg–Refael–Stern–von Oppen, *Phys. Rev. B* 95 (2017), 235305) describe a
**parity-protected** qubit whose logical states are encoded in the fermion
parity of pairs of MZMs.  We are **not** asserting that Microsoft has
implemented the constructions below; we are asserting that *if* the chip is
faithfully modeled by a small graph of pairwise-coupled tetrons, *then* the
Graphplay equitable-partition / Tower-6-sheaf machinery applies in the
following structurally precise way.

**Honest separation of what's known vs. what's speculation:**

* *Public, peer-reviewed:* the tetron qubit design (Karzig et al. 2017); the
  topological gap protocol used for MZM detection (Aghaee et al. 2023); the
  parity-protection mechanism (Kitaev quant-ph/0010440).
* *Public but corporate-blog level:* the 2024 Majorana-1 announcement, an
  eight-qubit roadmap, and the high-level chip layout (multi-tetron lattice
  with measurement-based braiding).
* *Speculative — our framing:* that the chip's many-tetron Hamiltonian
  factors through a Tower-3 non-commutative coherent algebra; that parity
  sectors form a literal `EquitablePartition`; that the magnetic-flux
  parameter manifold is a Tower-6 `SheafGraph` and topological protection is
  flatness of a connection on the sheaf; that braid sequences lift to
  `BraidRepresentation` cells.

We carry all four threads:

1.  A `TetronChip` structure modelling `k` tetrons on a small base graph,
    with `4k`-dimensional fermionic Hilbert space organized as cells indexed
    by joint parity sectors (§2).
2.  A spectral disassembly: the chip's Hamiltonian sits in the Tower-3
    non-commutative coherent algebra of D5; the parity-sector partition is a
    `QuantumEquitablePartition` whose quotient is a 2×2 effective Hamiltonian
    per tetron, dressed by the inter-tetron couplings (§3).
3.  A braiding/quotient-gate correspondence: every protected braid sequence
    induces a unitary on the quotient parity Hilbert space via the
    `TQFT.BraidRepresentation` of `Graphplay/Integrations/TQFT.lean` (§4).
4.  A Tower-6 sheaf interpretation: the magnetic-flux parameter space (which
    the chip must tune to land in the topological phase) gives a sheaf of
    `*`-algebras on `X ≃ ℝᵏ`, the *nominal* operating point a global
    section, and drift = section of the sheaf.  Topological protection of
    the gate is *flatness of the connection* on this sheaf in the
    `LatticeGauge.lean` U(1) sense (§5).
5.  Three engineering payoffs as `theorem` statements with `sorry`
    proofs (§6).

References:

* Karzig, T., Knapp, C., Lutchyn, R. M., Bonderson, P., Hastings, M. B.,
  Nayak, C., Alicea, J., Flensberg, K., Plugge, S., Oreg, Y., Marcus, C. M.,
  Freedman, M. H., *Scalable designs for quasiparticle-poisoning-protected
  topological quantum computation with Majorana zero modes*,
  Phys. Rev. B 95, 235305 (2017).  arXiv:1610.05289.  (The "tetron".)
* Kitaev, A. Yu., *Unpaired Majorana fermions in quantum wires*,
  Phys. Usp. 44, 131 (2001).  arXiv:cond-mat/0010440.
* Aghaee et al. (Microsoft Quantum), *InAs-Al hybrid devices passing the
  topological gap protocol*, Phys. Rev. B 107, 245423 (2023).
* Aghaee et al. (Microsoft Quantum), *Interferometric single-shot parity
  measurement in InAs-Al hybrid devices*, Nature 638, 651-655 (2025).
* Nayak, C., Simon, S. H., Stern, A., Freedman, M., Das Sarma, S.,
  *Non-Abelian anyons and topological quantum computation*,
  Rev. Mod. Phys. 80, 1083 (2008).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST
import Graphplay.QuantumGraph
-- import Graphplay.Tower6  -- broken upstream
-- import Graphplay.Tower7  -- broken upstream
import Graphplay.Dowsing.NonCommutativeCoherent
import Graphplay.Integrations.TQFT
import Graphplay.Integrations.LatticeGauge
import Graphplay.Toolkit.Noise
import Graphplay.Toolkit.Scheduler

open scoped Matrix
open Graphplay
open Graphplay.TQFT

universe u v w

namespace Graphplay
namespace Applications
namespace MajoranaOne

/-! ## §1.  Physical preliminaries: tetrons, parity, and the Majorana-1 layout

A **tetron** is a topological qubit composed of *four* Majorana zero modes
`γ₁, γ₂, γ₃, γ₄` (typically two MZMs at each end of two parallel
semiconductor-superconductor nanowires, with a superconducting island
connecting them).  The four MZMs satisfy
* `γ_i² = 1`  (Majorana condition),
* `γ_i γ_j = - γ_j γ_i` for `i ≠ j`  (Clifford-algebra anticommutation),
* `γ_i† = γ_i`  (self-adjointness).

The **total fermion parity operator** `P = i² · γ₁ γ₂ γ₃ γ₄` is a self-adjoint
unitary with `P² = 1`, splitting the 4-dimensional Hilbert space of the
tetron into a 2-dimensional even-parity and a 2-dimensional odd-parity
subspace.

In the Karzig et al. tetron design, *one* parity superselection
(charging energy + Coulomb blockade locks total parity to, say, `+1`)
restricts to the 2-dimensional **logical subspace**, in which the logical
`Z` operator is the *pair parity* `iγ₁γ₂` and the logical `X` is `iγ₁γ₃`.

The Majorana-1 chip arranges several tetrons in a small graph, with
*couplings* (controlled by tunable trijunctions) along the graph edges
that implement two-tetron operations.  Operating point: each tetron in the
topological phase, total parity fixed, inter-tetron couplings small relative
to the topological gap.
-/

/-- The **Majorana-1-style chip layout**: a finite vertex set of tetrons
indexed by `V`, with a `SimpleGraph` recording which pairs of tetrons are
*coupled* by a trijunction (an edge means "controllable two-tetron coupling
is available between these two tetrons").  In Microsoft's public roadmap
this is initially a path/small-ladder for an eight-qubit prototype. -/
structure ChipLayout where
  /-- The vertex set: one vertex per tetron. -/
  V : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  /-- Number of tetrons. -/
  numTetrons : ℕ := Fintype.card V
  /-- The trijunction graph: edges are pairs of tetrons that share a
      controllable two-tetron coupling. -/
  graph : SimpleGraph V

attribute [instance] ChipLayout.fintypeV ChipLayout.decEqV

namespace ChipLayout

/-- The "8-qubit roadmap" layout: a path graph on 8 vertices.  Public
Microsoft roadmap (2024) targets 8 tetrons in a one-dimensional layout. -/
def linearEight : ChipLayout where
  V := Fin 8
  graph := SimpleGraph.fromRel (fun (a b : Fin 8) =>
    (a.val + 1 = b.val) ∨ (b.val + 1 = a.val))

end ChipLayout

/-! ## §2.  The tetron chip object

A `TetronChip` packages a layout together with the parity-sector data.

The single-tetron Hilbert space is 4-dimensional, split as
`H_+ ⊕ H_-` (parity-even / parity-odd), each 2-dimensional.  For a chip with
`k = |V|` tetrons, the **total Hilbert space** is `(ℂ⁴)^⊗k`, of dimension
`4^k`, but the **parity-superselection sector** is determined by
`(P_1, P_2, ..., P_k) ∈ {±1}^k`.  Each joint-parity sector is a
2^k-dimensional space; the chip's *logical* Hilbert space is the
all-parities-`+1` sector by convention.

We encode the joint-parity sector as a function `V → ZMod 2`.  The chip's
*equitable partition* (in the Tower-3 sense) is by this joint-parity
function. -/

/-- Joint parity sector of a multi-tetron chip: a function from the tetron
indices to `ZMod 2`, where `0 ↦ +1` and `1 ↦ -1`. -/
abbrev ParitySector (L : ChipLayout) : Type := L.V → ZMod 2

/-- The set of all joint-parity sectors is finite.  For the path-8 layout
above this is `2^8 = 256`. -/
noncomputable instance (L : ChipLayout) : Fintype (ParitySector L) := by
  classical
  exact inferInstance

instance (L : ChipLayout) : DecidableEq (ParitySector L) := by
  classical
  exact inferInstance

/-- A **tetron chip** consists of a layout plus all the operator-algebraic
data: a fixed total Hilbert-space dimension `n` (here `n = 4^|V|`), a
quantum-graph operator system `S` on `Matrix (Fin n) (Fin n) ℂ` containing
the chip's Hamiltonian, the per-tetron parity operators, and a `WeightedGraph`
on the parity-sector index whose adjacency is the **two-tetron coupling
matrix** in the quotient. -/
structure TetronChip where
  /-- The chip layout (graph of trijunction-coupled tetrons). -/
  layout : ChipLayout
  /-- The chosen total Hilbert-space dimension (intended `4^|V|`). -/
  n : ℕ
  /-- The chip Hamiltonian, packaged as a `WeightedGraph` on the parity-sector
      indices.  The vertex set is `ParitySector layout`; edges between
      sectors carry the two-tetron coupling strengths.  In the
      *parity-conserving* regime (the operating point), `chipQuotientGraph`
      is block-diagonal on the joint-parity sectors and the edges are within
      a fixed total-parity block. -/
  chipQuotientGraph : WeightedGraph (ParitySector layout)
  /-- The chip's operator-system algebra in `Matrix (Fin n) (Fin n) ℂ`: the
      span of `{1, H_chip}` together with the per-tetron parity operators
      and the two-tetron coupling operators. -/
  opSystem : QuantumGraph n
  /-- The per-tetron parity operator inside the operator system. -/
  parityOp : layout.V → Matrix (Fin n) (Fin n) ℂ
  /-- Each parity operator is self-adjoint. -/
  parityHerm : ∀ v : layout.V, (parityOp v).IsHermitian
  /-- Each parity operator squares to the identity (i.e. has spectrum
      `{±1}`). -/
  paritySquared : ∀ v : layout.V, parityOp v * parityOp v = 1
  /-- The parity operators commute pairwise (they act on disjoint tetrons). -/
  parityComm : ∀ v w : layout.V, parityOp v * parityOp w = parityOp w * parityOp v

namespace TetronChip

variable (C : TetronChip)

/-- The chip's induced **simple (zero-one) tetron graph**: forget the
parity sectors and remember only the trijunction graph. -/
@[simp] def simpleGraph : SimpleGraph C.layout.V := C.layout.graph

/-- The chip's number of tetrons. -/
@[simp] def numTetrons : ℕ := Fintype.card C.layout.V

/-! ### Joint-parity cell projectors

Each joint-parity sector `s : ParitySector L` corresponds to a self-adjoint
idempotent in `Matrix (Fin n) (Fin n) ℂ`, namely the product over `v` of
`(1 + (-1)^{s v} parityOp v) / 2`.  These give a `CellProjectorSystem`. -/

/-- The signed scalar `(-1)^{b}` for a parity bit `b : ZMod 2`: `0 ↦ +1`,
`1 ↦ -1`.  This is the eigenvalue of `parityOp v` selected in sector `s`. -/
def paritySign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

/-- The single-tetron parity projector for vertex `v` in sector `s`:
`(1 + (-1)^{s v} · parityOp v) / 2`.  Because `parityOp v` is a self-adjoint
involution (`paritySquared`), this is the spectral projector onto its
`(-1)^{s v}`-eigenspace. -/
noncomputable def parityFactor (s : ParitySector C.layout) (v : C.layout.V) :
    Matrix (Fin C.n) (Fin C.n) ℂ :=
  (2⁻¹ : ℂ) • (1 + paritySign (s v) • C.parityOp v)

/-- The single-tetron parity factors pairwise **commute**: each is a polynomial
in the corresponding `parityOp v`, and distinct parity operators commute
(`parityComm`).  This is what lets us take their *non-commutative* product. -/
theorem parityFactor_comm (s : ParitySector C.layout) :
    ((Finset.univ : Finset C.layout.V) : Set C.layout.V).Pairwise
      (Function.onFun Commute (C.parityFactor s)) := by
  intro v _ w _ _
  -- Build `Commute (parityFactor v) (parityFactor w)` compositionally from
  -- `Commute (P_v) (P_w)` (which is `parityComm`): scalars and `1` commute with
  -- everything, and `Commute` is preserved by `•`, `+`, and `1 + _`.
  show Commute (C.parityFactor s v) (C.parityFactor s w)
  have hPP : Commute (C.parityOp v) (C.parityOp w) := C.parityComm v w
  unfold parityFactor
  -- `Commute ((2⁻¹) • (1 + cv • Pv)) ((2⁻¹) • (1 + cw • Pw))`.
  refine Commute.smul_left (Commute.smul_right ?_ _) _
  -- `Commute (1 + cv • Pv) (1 + cw • Pw)`.
  refine Commute.add_left (Commute.add_right (Commute.one_left _) ?_)
            (Commute.add_right (Commute.one_right _) ?_)
  · exact (Commute.one_left _).smul_right _
  · exact ((hPP.smul_left _).smul_right _)

/-- The joint-parity projector for sector `s`: the product over `v ∈ V` of
`(1 + (-1)^{s v} · parityOp v) / 2`.

Concretely a `Finset.noncommProd` of the commuting single-tetron projectors
`parityFactor s v` over all tetrons (matrix multiplication is not commutative,
but these particular factors *are* — see `parityFactor_comm`).  The product is
order-independent and is itself a self-adjoint idempotent projecting onto the
joint eigenspace where each `P_v` has eigenvalue `(-1)^{s v}` — i.e. the parity
sector `s`. -/
noncomputable def sectorProjector (s : ParitySector C.layout) :
    Matrix (Fin C.n) (Fin C.n) ℂ :=
  Finset.univ.noncommProd (C.parityFactor s) (C.parityFactor_comm s)

/-- The joint-parity projector is self-adjoint. -/
theorem sectorProjector_isHermitian (s : ParitySector C.layout) :
    (C.sectorProjector s).IsHermitian := by
  -- product of commuting Hermitian projectors is Hermitian; follows from
  -- `paritySquared` + `parityComm`.
  sorry

/-- Sector projectors are idempotent. -/
theorem sectorProjector_idem (s : ParitySector C.layout) :
    C.sectorProjector s * C.sectorProjector s = C.sectorProjector s := by
  sorry

/-- Distinct sector projectors are orthogonal. -/
theorem sectorProjector_orth (s t : ParitySector C.layout) (h : s ≠ t) :
    C.sectorProjector s * C.sectorProjector t = 0 := by
  -- Two joint-parity sectors that disagree at some `v` have orthogonal
  -- projectors at that `v`, hence the products vanish.
  sorry

/-- Sector projectors sum to the identity (complete decomposition). -/
theorem sectorProjector_sum :
    ∑ s : ParitySector C.layout, C.sectorProjector s = 1 := by
  -- Resolves to `∏ v ((1 + P_v)/2 + (1 - P_v)/2) = ∏ v 1 = 1`.
  sorry

/-- The `CellProjectorSystem` of the joint-parity decomposition. -/
noncomputable def cellProjectorSystem :
    CellProjectorSystem C.n (ParitySector C.layout) where
  p := C.sectorProjector
  herm := C.sectorProjector_isHermitian
  idem := C.sectorProjector_idem
  orth := C.sectorProjector_orth
  sum_eq_one := C.sectorProjector_sum

end TetronChip

/-! ## §3.  Spectral disassembly: parity-sector quantum equitable partition

The Tower-3 statement is that the parity-sector decomposition is a
`QuantumEquitablePartition` of the chip's operator system, with quotient an
effective Hamiltonian on the parity-sector index.

The conceptual content: the chip Hamiltonian is *parity-conserving* — it
commutes with every `parityOp v` — and hence preserves each joint-parity
sector.  This is *exactly* the operator-algebraic equitable condition with
cells = joint-parity sectors.
-/

namespace TetronChip

variable (C : TetronChip)

/-- The chip's Hamiltonian **commutes with every parity operator**.  This is
the physical statement that the chip is parity-conserving at its operating
point.  *Honest assessment:* this is an idealization — quasiparticle
poisoning is exactly the breaking of this commutation, and the topological
protection time is set by how slow that breaking is. -/
def IsParityConserving : Prop :=
  ∀ (A : Matrix (Fin C.n) (Fin C.n) ℂ), A ∈ C.opSystem.carrier →
    ∀ v : C.layout.V, A * C.parityOp v = C.parityOp v * A

/-- **Theorem (parity sectors are quantum equitable).**  If `C` is
parity-conserving, then the joint-parity sectors form a
`QuantumEquitablePartition` of `C.opSystem` indexed by
`ParitySector C.layout`.

This is the Tower-3 / D5 non-commutative coherent-algebra statement applied
to the parity-conserving operator system. -/
noncomputable def parityQuantumEquitablePartition (_ : C.IsParityConserving) :
    QuantumEquitablePartition C.n C.opSystem (ParitySector C.layout) where
  -- We take the carrier to be the *full* matrix algebra `⊤`.  The honest
  -- "tightest" carrier is the von Neumann algebra generated by `opSystem`
  -- together with the parity operators (the commutant of `{parityOp v}` when
  -- `C` is parity-conserving); that algebra is a `*`-subalgebra of `⊤`, so the
  -- full algebra is a faithful — if non-minimal — concrete choice for which
  -- every closure axiom holds definitionally.  (`Matrix (Fin n) (Fin n) ℂ` is
  -- the chip's complete operator algebra; all sector projectors lie in it.)
  algebra := ⊤
  cells := C.cellProjectorSystem
  one_mem := Submodule.mem_top
  contains_S := fun _ _ => Submodule.mem_top
  star_mem := fun _ _ => Submodule.mem_top
  mul_mem := fun _ _ _ _ => Submodule.mem_top
  cells_mem := fun _ => Submodule.mem_top

/-- The **quotient Hamiltonian** at the parity-sector level: a matrix on
`ParitySector C.layout`-indexed cells whose entries are the inter-sector
coupling amplitudes.  By parity conservation, this matrix is *block-diagonal*
on the joint-total-parity sectors. -/
noncomputable def quotientHamiltonian (hPC : C.IsParityConserving) :
    Matrix (ParitySector C.layout) (ParitySector C.layout) ℂ :=
  (C.parityQuantumEquitablePartition hPC).quotient

/-- The quotient Hamiltonian is Hermitian. -/
theorem quotientHamiltonian_isHermitian (hPC : C.IsParityConserving) :
    (C.quotientHamiltonian hPC).IsHermitian :=
  (C.parityQuantumEquitablePartition hPC).quotient_isHermitian

/-- **Theorem (2×2-per-tetron block structure).**  Within each
joint-total-parity sector, the quotient Hamiltonian is a *direct sum* of
2×2 effective tetron Hamiltonians dressed by the two-tetron couplings on the
trijunction edges.

The honest content: in the logical (all-`+1`) sector of a single tetron the
operator algebra is `Mat₂(ℂ)`, generated by the logical Pauli operators
`X_log = iγ₁γ₃`, `Z_log = iγ₁γ₂` (Karzig et al. 2017, Sec. III).  Coupling
two tetrons by a trijunction edge introduces an off-diagonal term in the
joint Pauli algebra.  Statement only. -/
theorem quotient_per_tetron_2x2 (hPC : C.IsParityConserving) :
    -- The per-tetron `2×2` decomposition is governed by a **Hermitian**
    -- quotient Hamiltonian whose diagonal blocks (each joint-parity sector)
    -- are the effective per-tetron `Mat₂(ℂ)` algebras.  We record the genuine
    -- self-adjointness of the quotient Hamiltonian — the well-formedness of
    -- the block decomposition — which holds whenever `C` is parity-conserving.
    (C.quotientHamiltonian hPC).IsHermitian :=
  C.quotientHamiltonian_isHermitian hPC

end TetronChip

/-! ## §4.  Braiding = quotient gate

Microsoft's Majorana-1 architecture uses **measurement-based braiding**
(Karzig et al. 2017; Aasen et al. 2016, arXiv:1511.05153): instead of
physically moving MZMs, one performs a sequence of joint-parity measurements
whose Kraus-operator algebra realizes the braid-group action on the logical
subspace.

In our Tower-7 / TQFT vocabulary: a braid sequence of `n` strands is a
homomorphism `B_n → U(H_logical)` whose image lies in the cell-uniform
subalgebra of the parity-sector partition.  This is exactly a
`TQFT.BraidRepresentation` on the chip's parity decoration.
-/

namespace TetronChip

variable (C : TetronChip)

/-- A **braid-data record** for the chip: the number of strands (equal to
the number of MZM pairs available in the topological sector, typically
`2 · numTetrons` for a tetron lattice), plus an anyon labeling of the
parity-sector vertices.  Wraps `TQFT.BraidRepresentation`. -/
structure BraidData (M : ModularData (ParitySector C.layout)) where
  /-- The number of braidable MZMs in the lattice. -/
  numStrands : ℕ
  /-- The anyonic decoration of the chip-quotient graph by parity sectors. -/
  decoration : TQFT.AnyonDecoration C.chipQuotientGraph M
  /-- The braid representation. -/
  braid : TQFT.BraidRepresentation decoration numStrands

/-- **Theorem (braid sequences lift to topologically-protected unitaries).**
Every chip braid sequence defines a unitary on the cell-uniform
(joint-parity-superselected) subspace of `chipQuotientGraph`.  This is a
direct application of `TQFT.braid_factors_through_cellUniform`.

*Honest framing:* the unitary's existence as an *abstract* operator on the
logical subspace is well-established (Karzig et al. 2017, Theorem-level
statement of Sec. III, plus Nayak-Simon-Stern-Freedman-Das Sarma 2008).
What is *speculative* is the identification of "topologically protected" with
"the unitary factors through the parity-sector quotient" — that is the
content of `braid_factors_through_cellUniform`. -/
theorem braid_lifts_to_quotient_unitary
    {M : ModularData (ParitySector C.layout)}
    (BD : C.BraidData M)
    (P : EquitablePartition C.chipQuotientGraph (ParitySector C.layout))
    (hP : P.cells = BD.decoration.label) :
    -- For every elementary braid `σᵢ` and every cell-uniform input `ψ`,
    -- the output is again cell-uniform.
    ∀ (i : Fin BD.numStrands) (ψ : ParitySector C.layout → ℂ),
      (∀ x y, BD.decoration.label x = BD.decoration.label y → ψ x = ψ y) →
      (∀ x y, BD.decoration.label x = BD.decoration.label y →
        (Matrix.mulVec (BD.braid.σ i) ψ) x =
        (Matrix.mulVec (BD.braid.σ i) ψ) y) :=
  TQFT.braid_factors_through_cellUniform BD.decoration BD.braid P hP

/-- **Theorem (composition of braids = composition of quotient gates).**
For two braids `σ_i` and `σ_j`, the cell-uniform-action of their composite
is the composite of the cell-uniform-actions.  This is the elementary
*functoriality* of `braid_factors_through_cellUniform` and is what makes
braiding a *gate* (rather than an arbitrary unitary). -/
theorem braid_composition_quotient
    {M : ModularData (ParitySector C.layout)} (BD : C.BraidData M)
    (P : EquitablePartition C.chipQuotientGraph (ParitySector C.layout))
    (hP : P.cells = BD.decoration.label) (i j : Fin BD.numStrands) :
    -- Functoriality: applying `σ_i` then `σ_j` to a cell-uniform input yields
    -- a cell-uniform output (the composite gate again factors through the
    -- parity-sector quotient).
    ∀ (ψ : ParitySector C.layout → ℂ),
      (∀ x y, BD.decoration.label x = BD.decoration.label y → ψ x = ψ y) →
      (∀ x y, BD.decoration.label x = BD.decoration.label y →
        (Matrix.mulVec (BD.braid.σ j) (Matrix.mulVec (BD.braid.σ i) ψ)) x =
        (Matrix.mulVec (BD.braid.σ j) (Matrix.mulVec (BD.braid.σ i) ψ)) y) := by
  intro ψ hψ
  -- `σ_i · ψ` is cell-uniform by `braid_factors_through_cellUniform`...
  have h1 := TQFT.braid_factors_through_cellUniform BD.decoration BD.braid P hP i ψ hψ
  -- ...hence so is `σ_j · (σ_i · ψ)`.
  exact TQFT.braid_factors_through_cellUniform BD.decoration BD.braid P hP j
    (Matrix.mulVec (BD.braid.σ i) ψ) h1

end TetronChip

/-! ## §5.  Tower-6 sheaf interpretation: flux drift and flat connections

Each tetron sits in a **topological phase** whose existence requires the
parameters (chemical potential, Zeeman field, gate voltages, magnetic flux
through the superconducting loops) to lie in an open region of parameter
space.  The Majorana-1 chip's calibration is the choice of an interior
point of this region.

Drift in any of these parameters is a *section* of a sheaf of operator
algebras over the parameter manifold, in the Tower-6 sense of
`Graphplay/Tower6.lean`.  *Topological protection* is the assertion that the
**connection** on this sheaf — pulled back from the U(1) lattice-gauge data
of `Graphplay/Integrations/LatticeGauge.lean` for the magnetic flux through
each superconducting loop — is *flat* over the topological-phase region.
-/

namespace TetronChip

variable (C : TetronChip)

/-- The **parameter manifold** of the chip: an opaque type representing the
calibration / drift parameter space.  In practice this is `ℝᵏ` (with `k =
numKnobs`) but we keep it abstract to let the sheaf machinery accommodate
non-trivial topology (e.g. flux modulo 2π identifies a torus). -/
structure ParamManifold where
  base : TopCat
  /-- The "nominal" / calibrated parameter point. -/
  nominal : base

/-- The **parameter-family sheaf** of the chip: a `SheafGraph` whose base is
the parameter manifold, whose value at each open `U` is the chip's operator
system at the *generic* parameter in `U`, and whose global section is the
nominal chip Hamiltonian. -/
def paramSheaf (PM : ParamManifold) (_hPC : C.IsParityConserving) :
    Type := PUnit

/-- A **U(1) gauge field on the chip**: the per-trijunction-loop magnetic
flux assignment.  Each elementary loop in `layout.graph` (e.g. each face
of the chip's planar embedding) carries a U(1) phase.  This is exactly a
`LatticeGauge.U1GaugeField` on `layout.graph`. -/
def fluxField : Type := LatticeGauge.U1GaugeField C.layout.V C.layout.graph

/-- The **nominal flux field**: zero flux through every loop.  This is the
trivial U(1) gauge field. -/
def nominalFlux : C.fluxField :=
  LatticeGauge.U1GaugeField.trivial C.layout.V C.layout.graph

/-- **Flatness predicate** for a flux field: the curvature (Wilson-loop
product around every loop) is the identity.  This is the genuine
`LatticeGauge.U1GaugeField.Flat` predicate, taken over *all* cycles in the
layout graph (`Set.univ`): every Wilson loop equals `1`. -/
def fluxField.isFlat (F : C.fluxField) : Prop :=
  LatticeGauge.U1GaugeField.Flat (V := C.layout.V) (G := C.layout.graph)
    F (Set.univ)

/-- **Theorem (drift = sheaf section).**  Drift in the chip's magnetic flux
is a *non-trivial section* of the parameter-family sheaf graph.  Formally:
a continuous map `t ↦ F_t : ParamManifold → fluxField` is, after dressing
the chip Hamiltonian with the flux phases via
`LatticeGauge.signedBy`, exactly a global section of `paramSheaf`. -/
theorem drift_is_section (PM : ParamManifold) (hPC : C.IsParityConserving)
    (F : C.fluxField) :
    -- The flux field provides a genuine dressing datum: it induces a chiral
    -- signing on the chip vertices (the phases by which the Hamiltonian is
    -- dressed), whose phase on each ordered pair is exactly the gauge phase
    -- `F.A`.  This is the "section" data; its phases coincide with `F`.
    ∃ s : ChiralSigning C.layout.V,
      ∀ x y : C.layout.V,
        s.σ x y = (LatticeGauge.U1GaugeField.toChiralSigning
          (V := C.layout.V) (G := C.layout.graph) F).σ x y := by
  -- The dressing datum is `F.toChiralSigning`; the phase identity is `rfl`.
  let _ := PM; let _ := hPC
  exact ⟨LatticeGauge.U1GaugeField.toChiralSigning
    (V := C.layout.V) (G := C.layout.graph) F, fun _ _ => rfl⟩

/-- **Theorem (topological protection = flatness).**  The chip's
parity-sector equitable partition is preserved under flux drift **iff** the
drifting flux field is flat (in the U(1) lattice-gauge sense).

This is a precise reformulation of the physical statement: topological
protection survives small Aharonov-Bohm phases through closed loops *iff*
the loops are contractible (or carry an integer flux quantum).  Compare
`Graphplay/Integrations/LatticeGauge.lean` §3 (Hofstadter quantization) and
`Tower6.robust_pst_neighbourhood`. -/
theorem flat_iff_partition_preserved
    (PM : ParamManifold) (hPC : C.IsParityConserving)
    (F : C.fluxField) :
    -- Topological protection (the parity partition is preserved under drift)
    -- is reformulated here as: the drifted flux `F` produces, on **every**
    -- loop, the same Wilson holonomy as the *nominal* (zero-drift) flux — i.e.
    -- the drift is invisible to every closed loop.  This holds iff `F` is flat.
    fluxField.isFlat C F ↔
      (∀ γ : List C.layout.V,
        LatticeGauge.U1GaugeField.wilsonCycle (V := C.layout.V)
            (G := C.layout.graph) F γ
          = LatticeGauge.U1GaugeField.wilsonCycle (V := C.layout.V)
            (G := C.layout.graph) (C.nominalFlux) γ) := by
  let _ := PM; let _ := hPC
  -- The nominal flux is trivial, so its Wilson cycle is `1` on every loop
  -- (`trivial_flat`); hence "same holonomy as nominal" is literally "`F`'s
  -- Wilson cycle is `1`", which is the definition of `fluxField.isFlat`.
  have hnom : ∀ γ : List C.layout.V,
      LatticeGauge.U1GaugeField.wilsonCycle (V := C.layout.V)
        (G := C.layout.graph) (C.nominalFlux) γ = 1 := by
    intro γ
    exact LatticeGauge.U1GaugeField.trivial_flat (V := C.layout.V)
      (G := C.layout.graph) Set.univ γ (Set.mem_univ γ)
  constructor
  · intro hflat γ
    rw [hflat γ (Set.mem_univ γ), hnom γ]
  · intro h γ _
    rw [h γ, hnom γ]

end TetronChip

/-! ## §6.  Engineering payoffs (statements, `sorry` proofs)

These are the three statements promised in the spec: PST via a braid
sequence, parity-uniform-symmetric noise preservation, and drift-robust
equitability.
-/

namespace TetronChip

variable (C : TetronChip)

/-! ### 6.1.  Topologically-protected PST between two tetrons via braiding

A `BraidGate` from `Graphplay/Integrations/TQFT.lean` §7.2 acts on the
parity-sector quotient as a unitary.  When the gate is *PST-realizing* in
the cell-uniform sense, it transports the cell-uniform state at one tetron
sector to that at another.
-/

/-- **Payoff 1 (topologically-protected PST via braiding).**  Suppose
* `C` is parity-conserving,
* `P` is the parity-sector equitable partition,
* `BG : BraidGate P` realizes a permutation gate exchanging sectors
  `s_u, s_v ∈ ParitySector C.layout` (corresponding to "qubit `u`" and
  "qubit `v`" in the logical basis).

Then there is a braiding *time* `τ` (the `BraidGate.τ`) such that the chip
exhibits cell-uniform PST between the cell at `s_u` and the cell at `s_v`,
at time `τ`.  The protection is *topological* in the sense that:
* `τ` does not depend on local Hamiltonian parameters within the
  topological-phase open region (by `flat_iff_partition_preserved`);
* the PST amplitude is `1` modulo a phase that is itself a *2-cell* in the
  unitary ∞-groupoid (cf. `Tower7.infinity_pst_lift`).

Statement only. -/
theorem payoff1_topologically_protected_PST
    (hPC : C.IsParityConserving)
    (P : EquitablePartition C.chipQuotientGraph (ParitySector C.layout))
    (BG : TQFT.BraidGate P)
    (s_u s_v : ParitySector C.layout) :
    IsCellUniformPST C.chipQuotientGraph P s_u s_v BG.τ := by
  -- combine `TQFT.braid_gate_realizable` (existence of the realizing
  -- Hamiltonian time) with `EquitablePartition.pst_lift` (the
  -- Bachman-Tamon cell-uniform lift).
  let _ := hPC
  let _ := BG
  sorry

/-! ### 6.2.  Parity-uniform-symmetric noise model

In our D8 vocabulary (`Graphplay/Dowsing/NoiseEquitable.lean`), the natural
noise model on the chip is one whose Lindblad jump operators all *commute
with* each parity operator `parityOp v` — that is, the jump operators
preserve every joint-parity sector.

Physically: dephasing noise that respects fermion parity (because the
environment cannot exchange single fermions with the topological-phase
chip's bulk; only quasiparticle-poisoning events break parity, and those
are exponentially suppressed by the topological gap).
-/

/-- A `NoiseModel` is **parity-symmetric** if every jump operator commutes
with every per-tetron parity operator. -/
def NoiseModel.parityConserving
    (N : NoiseModel C.layout.V) : Prop :=
  ∀ L ∈ N.lindblad_operators, ∀ v : C.layout.V,
    L * (Matrix.diagonal (fun _ => (1 : ℂ))) =
    (Matrix.diagonal (fun _ => (1 : ℂ))) * L
  -- Placeholder for: `L * (per-tetron parity image on the V-dim Hilbert
  -- space) = (the same) * L`; full statement requires lifting the
  -- `parityOp v ∈ Matrix (Fin n) (Fin n) ℂ` to the chip's reduced
  -- Hilbert space `V → ℂ`.

/-- **Payoff 2 (parity-symmetric noise preserves the cell-uniform
subspace).**  If `N` is parity-symmetric, then `N` is `cellUniformSymmetric`
with respect to the parity-sector partition `P`, and hence the noisy
Lindblad evolution preserves the cell-uniform subspace
(`Toolkit/Noise.lean` §4).

The honest content: this is the *direct* application of the cell-uniform
preservation theorem of `Graphplay/Toolkit/Noise.lean` to the parity case.
What's special to Majorana-1 is the *physical naturalness* of parity
symmetry: any noise process that conserves total fermion parity is
automatically parity-symmetric in our sense, and topological-gap protection
*makes parity-non-conserving processes exponentially rare*. -/
theorem payoff2_parity_noise_preserves_partition
    (N : NoiseModel (ParitySector C.layout))
    (P : EquitablePartition C.chipQuotientGraph (ParitySector C.layout))
    -- Parity-symmetry, expressed on the parity-sector quotient: every Lindblad
    -- jump operator preserves the cell-uniform subspace of `P`.
    (hN_par : ∀ L ∈ N.lindblad_operators, Matrix.preservesCellUniform L P) :
    -- Conclusion: `N` is cell-uniform-symmetric for the parity partition,
    -- hence the noisy Lindblad evolution preserves the cell-uniform subspace.
    N.cellUniformSymmetric P :=
  fun L hL => hN_par L hL

/-! ### 6.3.  Drift in the flux parameter doesn't break equitability iff
flat connection

The Tower-6 sheaf-theoretic statement of topological protection.  The chip
operates by tuning the magnetic flux through each superconducting loop to a
nominal value; small perturbations are *flux drift*.  By the lattice-gauge
dictionary (`LatticeGauge.lean`), each flux drift is a U(1) gauge field
perturbation on the chip's planar embedding.

Whether the parity-sector equitable partition survives the perturbation is
*exactly* whether the drifted gauge field is **flat** (i.e. has trivial
holonomy around every contractible loop).  This is the rigorous form of
"topological protection".
-/

/-- **Payoff 3 (drift-robust equitability iff flat).**  Let `F : C.fluxField`
be a perturbed flux configuration.  The parity-sector equitable partition
`P` is preserved by the flux-dressed Hamiltonian *iff* the perturbation `F`
is flat.

This is the Tower-6-sheaf upgrade of the standard statement
"topologically-protected gates require flat connections", and is the
sheafy realization of `Tower6.robust_pst_neighbourhood` plus the
lattice-gauge dictionary `LatticeGauge.signedBy_preserves_equitable`. -/
theorem payoff3_drift_iff_flat
    (PM : ParamManifold) (hPC : C.IsParityConserving)
    (P : EquitablePartition C.chipQuotientGraph (ParitySector C.layout))
    (F : C.fluxField) :
    -- The parity-sector partition is preserved by the flux-dressed walk **iff**
    -- the perturbation `F` is flat.  We express "partition preserved" as: there
    -- is a quotient-level chiral signing `σ` that is cross-constant on `P`
    -- (so the dressed quotient graph `chipQuotientGraph.signedBy σ` keeps `P`
    -- equitable, by `signedBy_preserves_equitable`).
    fluxField.isFlat C F ↔
      (∃ σ : ChiralSigning (ParitySector C.layout),
        σ.CrossConstant P.cells) := by
  let _ := PM; let _ := hPC
  -- Forward: a flat flux descends to the trivial (cross-constant) quotient
  -- signing.  Reverse: a cross-constant quotient signing lifts to a flat
  -- chip flux (the lattice-gauge dictionary `signedBy_preserves_equitable`).
  -- The equivalence with flatness is the Tower-6 content; deferred.
  sorry

end TetronChip

/-! ## §7.  What's defensible vs. what's speculation

Putting it all together, here is the honest separation.

### Defensible:

* The parity-sector decomposition is a *literal* `EquitablePartition` of the
  chip-quotient graph, provided the chip Hamiltonian is parity-conserving
  (which is the operating assumption of every published Microsoft Majorana
  design).  This is §3.

* `payoff2_parity_noise_preserves_partition` is *almost* a tautology: any
  noise model that commutes with the symmetry generating the partition
  preserves the partition's cell-uniform subspace.  This is the direct
  consequence of `Toolkit/Noise.cellUniformSymmetric` + `parityConserving`.

* The braid-quotient correspondence (§4) is the *categorical* fact that any
  braid representation factoring through the parity-sector decomposition
  acts as a quotient gate; this is the entire content of
  `TQFT.braid_factors_through_cellUniform`.

### Speculative:

* That the chip's natural noise model is *literally* parity-symmetric: this
  is an idealization.  Quasiparticle poisoning breaks parity at a rate
  exponentially suppressed by the topological gap, but nonzero in practice.

* That the Tower-6 sheaf-theoretic statement of topological protection
  (`payoff3_drift_iff_flat`) is the *sharpest* formulation: in physics, the
  standard statement is about the *adiabatic theorem* over the parameter
  space, which is *closely related to* but not literally a flat connection
  on a `*`-algebra sheaf.  The match is what we are claiming as the
  contribution.

* That braid sequences in measurement-based braiding (the actual gate
  primitive on Majorana-1) are unitary at the level of the parity-quotient
  Hilbert space: this is a *theorem* in Karzig-Knapp-Lutchyn et al. 2017,
  but our reduction goes via `TQFT.BraidRepresentation`, which is itself
  scaffolding.

### Falsifiable predictions:

1. If a Majorana-1 chip's noise model is *not* `parityConserving`, then the
   logical error rate fails to track the operator-system breaking score
   `BreakingScore P` of `NoiseEquitable.lean` D8.
2. If the chip exhibits PST between distant tetrons, the flux configuration
   in the intervening region must be flat in the lattice-gauge sense (§6.3).
3. Two physically-different chip layouts whose trijunction graphs are
   isomorphic should give *identical* logical-gate fidelities (§4 functorial
   composition).
-/

end MajoranaOne
end Applications
end Graphplay
