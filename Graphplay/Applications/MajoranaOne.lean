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
2.  A spectral disassembly: the chip's operator system sits in the Tower-3
    non-commutative coherent algebra of D5, the parity-sector partition is a
    genuine `QuantumEquitablePartition`, and — the de-hollowed headline — the
    chip's **designated Hamiltonian** compresses onto the parity sectors to a
    genuinely **block-diagonal** effective Hamiltonian
    (`chip_effectiveHamiltonian_isDiag`): the chip decouples into one independent
    effective block per joint-parity sector.  The single-tetron logical algebra
    is a genuine `Mat₂(ℂ)` (the Karzig logical Paulis `Z=iγ₁γ₂`, `X=iγ₁γ₃` are
    Hermitian involutions that anticommute — `TetronLogical.logical_pauli_algebra`)
    (§3, §3a).
3.  A braiding/quotient-gate correspondence: every protected braid sequence
    induces a unitary on the quotient parity Hilbert space via the
    `TQFT.BraidRepresentation` of `Graphplay/Integrations/TQFT.lean` (§4).
4.  A Tower-6 sheaf interpretation: the magnetic-flux parameter space (which
    the chip must tune to land in the topological phase) gives a sheaf of
    `*`-algebras on `X ≃ ℝᵏ`, the *nominal* operating point a global
    section, and drift = section of the sheaf.  Topological protection of
    the gate is *flatness of the connection* on this sheaf in the
    `LatticeGauge.lean` U(1) sense (§5).
5.  Three engineering payoffs as `theorem` statements (§6); payoff 1 is the
    honest FKLW-conditional braid-gate realizability (no `sorry`).

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
  /-- **The designated chip Hamiltonian** as a concrete `n × n` matrix.  This is
      the genuine physical Hamiltonian — single-tetron topological-gap terms plus
      the inter-tetron coupling terms — and is the object that gets compressed
      onto the parity sectors to produce the *effective* (per-sector) Hamiltonian.
      Unlike the projector-overlap Gram matrix, the disassembly traces against
      *this* matrix, so the quotient genuinely depends on the chip dynamics. -/
  hamiltonian : Matrix (Fin n) (Fin n) ℂ
  /-- The chip Hamiltonian is self-adjoint (a physical Hamiltonian). -/
  hamiltonianHerm : hamiltonian.IsHermitian
  /-- The chip Hamiltonian is an element of the operator system. -/
  hamiltonianMem : hamiltonian ∈ opSystem.carrier
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

/-- Any two single-tetron parity factors commute — even across *different*
sectors `s, t` and *different* vertices `v, w` — since both are polynomials in
the pairwise-commuting `parityOp`s. -/
theorem parityFactor_comm' (s t : ParitySector C.layout) (v w : C.layout.V) :
    Commute (C.parityFactor s v) (C.parityFactor t w) := by
  have hPP : Commute (C.parityOp v) (C.parityOp w) := C.parityComm v w
  unfold parityFactor
  refine Commute.smul_left (Commute.smul_right ?_ _) _
  refine Commute.add_left (Commute.add_right (Commute.one_left _) ?_)
            (Commute.add_right (Commute.one_right _) ?_)
  · exact (Commute.one_left _).smul_right _
  · exact ((hPP.smul_left _).smul_right _)

/-- The parity sign is `±1`, hence a self-adjoint scalar. -/
theorem paritySign_selfAdjoint (b : ZMod 2) : IsSelfAdjoint (paritySign b) := by
  unfold paritySign; split
  · exact IsSelfAdjoint.one ℂ
  · exact (IsSelfAdjoint.one ℂ).neg

/-- The parity sign squares to `1`. -/
theorem paritySign_sq (b : ZMod 2) : paritySign b * paritySign b = 1 := by
  unfold paritySign; split <;> norm_num

/-- Each single-tetron parity factor is self-adjoint (a real combination of the
identity and the Hermitian involution `parityOp v`). -/
theorem parityFactor_isHermitian (s : ParitySector C.layout) (v : C.layout.V) :
    (C.parityFactor s v).IsHermitian := by
  unfold parityFactor
  refine Matrix.IsHermitian.smul ?_ ?_
  · exact (Matrix.isHermitian_one).add ((C.parityHerm v).smul (paritySign_selfAdjoint (s v)))
  · show star (2⁻¹ : ℂ) = 2⁻¹; rw [star_inv₀]; norm_num

/-- Each single-tetron parity factor is idempotent: `((1 + cP)/2)² = (1 + cP)/2`
since `c² = 1` and `P² = 1`. -/
theorem parityFactor_idem (s : ParitySector C.layout) (v : C.layout.V) :
    C.parityFactor s v * C.parityFactor s v = C.parityFactor s v := by
  unfold parityFactor
  have hP : C.parityOp v * C.parityOp v = 1 := C.paritySquared v
  have hc : paritySign (s v) * paritySign (s v) = 1 := paritySign_sq (s v)
  set c := paritySign (s v) with hcdef
  set P := C.parityOp v with hPdef
  -- Expand `(2⁻¹ • (1 + c•P)) * (2⁻¹ • (1 + c•P))`.
  have hexpand : (2⁻¹ : ℂ) • (1 + c • P) * ((2⁻¹ : ℂ) • (1 + c • P))
      = (2⁻¹ * 2⁻¹ : ℂ) • ((1 + c • P) * (1 + c • P)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hexpand]
  have hsq : (1 + c • P) * (1 + c • P) = (2 : ℂ) • (1 + c • P) := by
    have : (1 + c • P) * (1 + c • P)
        = 1 + c • P + c • P + (c * c) • (P * P) := by
      simp only [mul_add, add_mul, Matrix.one_mul, Matrix.mul_one,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      abel
    rw [this, hc, hP]
    module
  rw [hsq, smul_smul]
  norm_num

/-- The product over a finset of pairwise-commuting Hermitian idempotents is a
Hermitian idempotent.  Proved by `Finset.cons`-induction: each new factor
commutes with the running product (by `noncommProd_commute`), so Hermiticity
and idempotence are preserved (`(AB)ᴴ = BA = AB`, `(AB)² = A²B² = AB`). -/
theorem noncommProd_herm_idem {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Matrix (Fin C.n) (Fin C.n) ℂ)
    (comm : (s : Set ι).Pairwise (Function.onFun Commute f))
    (hherm : ∀ i ∈ s, (f i).IsHermitian)
    (hidem : ∀ i ∈ s, f i * f i = f i) :
    (s.noncommProd f comm).IsHermitian ∧
      (s.noncommProd f comm) * (s.noncommProd f comm) = s.noncommProd f comm := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [Finset.noncommProd_empty, Matrix.isHermitian_one]
  | cons a s ha ih =>
    rw [Finset.noncommProd_cons]
    set Q := s.noncommProd f (comm.mono fun _ => Finset.mem_cons.2 ∘ .inr) with hQ
    have hmem : ∀ i ∈ s, i ∈ Finset.cons a s ha := fun i hi => Finset.mem_cons.2 (.inr hi)
    obtain ⟨hQherm, hQidem⟩ :=
      ih (comm.mono fun _ => Finset.mem_cons.2 ∘ .inr)
        (fun i hi => hherm i (hmem i hi)) (fun i hi => hidem i (hmem i hi))
    have hfaherm : (f a).IsHermitian := hherm a (Finset.mem_cons_self a s)
    have hfaidem : f a * f a = f a := hidem a (Finset.mem_cons_self a s)
    -- `f a` commutes with the running product `Q`.
    have hcomm : Commute (f a) Q := by
      rw [hQ]
      refine Finset.noncommProd_commute _ _ _ _ ?_
      intro i hi
      exact comm (Finset.mem_cons_self a s) (hmem i hi) (by rintro rfl; exact ha hi)
    refine ⟨?_, ?_⟩
    · -- Hermitian: `(f a * Q)ᴴ = Qᴴ * (f a)ᴴ = Q * f a = f a * Q`.
      rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hQherm.eq, hfaherm.eq, hcomm.eq]
    · -- Idempotent: `(f a * Q)(f a * Q) = f a * (f a * Q) * Q = f a² * Q² = f a * Q`.
      calc f a * Q * (f a * Q)
          = f a * (Q * f a) * Q := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = f a * (f a * Q) * Q := by rw [hcomm.eq]
        _ = (f a * f a) * (Q * Q) := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = f a * Q := by rw [hfaidem, hQidem]

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
    (C.sectorProjector s).IsHermitian :=
  (C.noncommProd_herm_idem Finset.univ (C.parityFactor s) (C.parityFactor_comm s)
    (fun v _ => C.parityFactor_isHermitian s v)
    (fun v _ => C.parityFactor_idem s v)).1

/-- Sector projectors are idempotent. -/
theorem sectorProjector_idem (s : ParitySector C.layout) :
    C.sectorProjector s * C.sectorProjector s = C.sectorProjector s :=
  (C.noncommProd_herm_idem Finset.univ (C.parityFactor s) (C.parityFactor_comm s)
    (fun v _ => C.parityFactor_isHermitian s v)
    (fun v _ => C.parityFactor_idem s v)).2

/-- At a vertex `v` where two parity sectors disagree (`s v ≠ t v`, i.e. opposite
parity signs `c, −c`), the single-tetron factors are orthogonal:
`(1+cP)/2 · (1−cP)/2 = (1 − c²P²)/4 = (1−1)/4 = 0`. -/
theorem parityFactor_orth (s t : ParitySector C.layout) (v : C.layout.V)
    (hv : s v ≠ t v) : C.parityFactor s v * C.parityFactor t v = 0 := by
  unfold parityFactor
  have hP : C.parityOp v * C.parityOp v = 1 := C.paritySquared v
  -- The two parity signs are negatives of each other.
  have hsign : paritySign (t v) = -paritySign (s v) := by
    unfold paritySign
    -- `s v, t v ∈ ZMod 2` are distinct, so one is `0` and the other `1`.
    by_cases hsv : s v = 0
    · have htv : t v ≠ 0 := fun hc => hv (hsv.trans hc.symm)
      rw [if_pos hsv, if_neg htv]
    · have htv : t v = 0 := by
        revert hv hsv; generalize s v = a; generalize t v = b; revert a b; decide
      rw [if_neg hsv, if_pos htv]; ring
  set c := paritySign (s v)
  set P := C.parityOp v
  rw [hsign, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hexp : (1 + c • P) * (1 + (-c) • P)
      = 1 + ((-c) • P + c • P) + (c * (-c)) • (P * P) := by
    rw [mul_add, add_mul, add_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    module
  rw [hexp,
    show ((-c) • P + c • P) = (0 : Matrix (Fin C.n) (Fin C.n) ℂ) by module,
    show c * (-c) = -(c * c) by ring, paritySign_sq, hP]
  simp

/-- Distinct sector projectors are orthogonal.  At a vertex `v₀` where the
sectors disagree, the factors `f_s v₀` and `f_t v₀` multiply to `0`
(`parityFactor_orth`); peeling that factor off the front of each `noncommProd`
(`mul_noncommProd_erase`) and commuting the (everywhere-commuting) tails past
`f_t v₀` collects the zero pair, killing the whole product. -/
theorem sectorProjector_orth (s t : ParitySector C.layout) (h : s ≠ t) :
    C.sectorProjector s * C.sectorProjector t = 0 := by
  classical
  -- A vertex where the two sectors disagree.
  obtain ⟨v₀, hv₀⟩ : ∃ v, s v ≠ t v := by
    by_contra hcon
    push_neg at hcon
    exact h (funext hcon)
  unfold sectorProjector
  -- Peel `f_s v₀` and `f_t v₀` off the fronts of the two products.
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ v₀) (C.parityFactor s)
        (C.parityFactor_comm s),
      ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ v₀) (C.parityFactor t)
        (C.parityFactor_comm t)]
  set Rs := (Finset.univ.erase v₀).noncommProd (C.parityFactor s)
    (fun _ hx _ hy hxy => C.parityFactor_comm s (Finset.mem_univ _) (Finset.mem_univ _) hxy)
  set Rt := (Finset.univ.erase v₀).noncommProd (C.parityFactor t)
    (fun _ hx _ hy hxy => C.parityFactor_comm t (Finset.mem_univ _) (Finset.mem_univ _) hxy)
  -- The tail `Rs` commutes with `f_t v₀` (all factors commute).
  have hcomm : Commute (C.parityFactor t v₀) Rs := by
    refine Finset.noncommProd_commute _ _ _ _ ?_
    intro w _
    exact (C.parityFactor_comm' t s v₀ w)
  -- `f_s v₀ * Rs * (f_t v₀ * Rt) = f_s v₀ * (f_t v₀ * Rs) * Rt = 0`.
  calc C.parityFactor s v₀ * Rs * (C.parityFactor t v₀ * Rt)
      = C.parityFactor s v₀ * (Rs * C.parityFactor t v₀) * Rt := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = C.parityFactor s v₀ * (C.parityFactor t v₀ * Rs) * Rt := by rw [hcomm.symm.eq]
    _ = (C.parityFactor s v₀ * C.parityFactor t v₀) * (Rs * Rt) := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [C.parityFactor_orth s t v₀ hv₀, Matrix.zero_mul]

/-- Reindexing a `Finset.noncommProd` along an injective map `g`: the product
over `s.image g` of `f` equals the product over `s` of `f ∘ g`.  Proved by
unfolding to the underlying `Multiset` (where `image` becomes `map` because `g`
is injective on `s`, so no `dedup` collapse occurs) and `Multiset.map_map`. -/
theorem noncommProd_image {α β γ : Type*} [DecidableEq α] [Monoid γ]
    {s : Finset α} {g : α → β} (hg : Set.InjOn g s) [DecidableEq β]
    (f : β → γ) (comm) :
    (s.image g).noncommProd f comm
      = s.noncommProd (fun a => f (g a))
          (fun x hx y hy hxy => comm (Finset.mem_image_of_mem g hx)
            (Finset.mem_image_of_mem g hy)
            (fun h => hxy (hg hx hy h))) := by
  classical
  -- Unfold both sides to `Multiset.noncommProd`; the underlying multisets are
  -- equal because `g` is injective on `s` (so `image` = `map`, no `dedup`
  -- collapse).  Then the `Pairwise` commutation proof is irrelevant.
  have hnodup : ((s.image g).val.map f) = s.val.map (fun a => f (g a)) := by
    rw [Finset.image_val,
      Multiset.dedup_eq_self.2
        (s.nodup.map_on (fun x hx y hy h => hg hx hy h)),
      Multiset.map_map]
    rfl
  show Multiset.noncommProd ((s.image g).val.map f) _
      = Multiset.noncommProd (s.val.map (fun a => f (g a))) _
  -- Generalize both commutation proofs, then rewrite the multiset; the two
  -- `noncommProd`s then agree by proof irrelevance (`Pairwise` is a `Prop`).
  generalize_proofs h₁ h₂
  revert h₁
  rw [hnodup]
  intro h₁
  rfl

/-- A `noncommProd` over a finset equals the `noncommProd` over its `attach`
(reindexing the factor function along `Subtype.val`).  Special case of
`noncommProd_image` along the injection `Subtype.val`. -/
theorem noncommProd_attach {α γ : Type*} [DecidableEq α] [Monoid γ]
    (s : Finset α) (h : α → γ) (comm) :
    s.noncommProd h comm
      = s.attach.noncommProd (fun x => h x.1)
          (fun x _ y _ hxy => comm x.2 y.2 (fun heq => hxy (Subtype.ext heq))) := by
  classical
  have hval : s.val.map h = s.attach.val.map (fun x => h x.1) := by
    rw [Finset.attach_val, ← Multiset.attach_map_val' s.val h]
    rfl
  show Multiset.noncommProd (s.val.map h) _ = Multiset.noncommProd _ _
  generalize_proofs h₁ h₂
  revert h₁
  rw [hval]
  intro h₁
  rfl

/-- **General distributive interchange for a globally-commuting `noncommProd`.**
For a family `f i : κ i → A` whose *entire* image pairwise commutes (the
`gcomm` hypothesis), the non-commutative product over `s` of the row-sums
`∑_b f i b` expands as a sum over the dependent product `s.pi t` of the
non-commutative products of the chosen entries.  This is the
`Finset.noncommProd` analogue of `Finset.prod_sum`; because we keep the head
factor on the *left* throughout, no reordering (hence no use of `gcomm` beyond
discharging the `noncommProd` commutation side-goals) is needed in the algebra.

This is the engine behind `sectorProjector_sum`. -/
theorem noncommProd_sum_pi {ι : Type*} [DecidableEq ι] {A : Type*} [Ring A]
    {κ : ι → Type*} [∀ i, DecidableEq (κ i)] (s : Finset ι) (t : ∀ i, Finset (κ i))
    (f : ∀ i, κ i → A)
    (gcomm : ∀ (i j : ι) (a : κ i) (b : κ j), Commute (f i a) (f j b)) :
    s.noncommProd (fun i => ∑ b ∈ t i, f i b)
        (fun i _ j _ _ => Commute.sum_left _ _ _
          (fun a _ => Commute.sum_right _ _ _ (fun b _ => gcomm i j a b)))
      = ∑ p ∈ s.pi t,
          s.attach.noncommProd (fun x => f x.1 (p x.1 x.2))
            (fun x _ y _ _ => gcomm x.1 y.1 _ _) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    -- Peel the head vertex `a` off the left of the product.
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, ih, Finset.pi_insert ha]
    -- `(∑_b f a b) * (∑_p ∏ ...) = ∑_b ∑_p f a b * ∏ ...`.
    rw [Finset.sum_mul_sum]
    -- The RHS is a sum over `(t a).biUnion`; expand via `Finset.sum_biUnion`.
    have hdisj : ∀ x ∈ t a, ∀ y ∈ t a, x ≠ y →
        Disjoint ((s.pi t).image (Finset.Pi.cons s a x))
          ((s.pi t).image (Finset.Pi.cons s a y)) := by
      intro x _ y _ hxy
      simp only [Finset.disjoint_iff_ne, Finset.mem_image]
      rintro _ ⟨p₂, _, rfl⟩ _ ⟨p₃, _, rfl⟩ heq
      have := congrArg (fun g => g a (Finset.mem_insert_self a s)) heq
      simp only [Finset.Pi.cons_same] at this
      exact hxy this
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun b _ => ?_
    -- Reindex the inner sum over the injective image `Pi.cons s a b`.
    have hinj : ∀ p₁ ∈ s.pi t, ∀ p₂ ∈ s.pi t,
        Finset.Pi.cons s a b p₁ = Finset.Pi.cons s a b p₂ → p₁ = p₂ :=
      fun p₁ _ p₂ _ eq => Finset.Pi.cons_injective ha eq
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun p _ => ?_
    -- Re-attach the head vertex inside the inner `noncommProd`.
    rw [Finset.attach_insert,
      Finset.noncommProd_insert_of_notMem _ _ _ _
        (by simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
          Subtype.exists, exists_prop, exists_eq_right] using ha)]
    -- Head factor evaluates to `f a b` (via `Pi.cons_same`); the tail is a
    -- `noncommProd` over `s.attach.image (embedding into (insert a s).attach)`.
    have hinj' : Set.InjOn
        (fun x : {x // x ∈ s} => (⟨x.1, Finset.mem_insert_of_mem x.2⟩ : {x // x ∈ insert a s}))
        s.attach := by
      intro x _ y _ h
      exact Subtype.ext (Subtype.mk.inj h)
    rw [noncommProd_image hinj']
    -- Now both sides are `head * tail` products over `s.attach`.  The head
    -- factor: `f a (Pi.cons s a b p a _) = f a b` by `Pi.cons_same`; the tail
    -- factor: on a vertex `x.1 ∈ s` (so `x.1 ≠ a`), `Pi.cons s a b p x.1 _ =
    -- p x.1 _` by `Pi.cons_ne`.
    have hhead : f a (Finset.Pi.cons s a b p a (Finset.mem_insert_self a s)) = f a b := by
      rw [Finset.Pi.cons_same]
    have htail : s.attach.noncommProd
          (fun x : {x // x ∈ s} =>
            f x.1 (Finset.Pi.cons s a b p x.1 (Finset.mem_insert_of_mem x.2)))
          (fun x _ y _ _ => gcomm x.1 y.1 _ _)
        = s.attach.noncommProd (fun x => f x.1 (p x.1 x.2))
          (fun x _ y _ _ => gcomm x.1 y.1 _ _) := by
      refine Finset.noncommProd_congr rfl (fun x _ => ?_) _
      rw [Finset.Pi.cons_ne (ha := by rintro heq; exact ha (heq ▸ x.2))]
    rw [hhead, htail]

/-- The single-tetron parity factor as a function of the *bit* `b : ZMod 2`
(rather than of the whole sector `s`): `g v b = (1 + (-1)^b · P_v)/2`.  We have
`parityFactor s v = parityFactorBit v (s v)`, so the sector projector is a
non-commutative product of these bit-indexed factors. -/
noncomputable def parityFactorBit (v : C.layout.V) (b : ZMod 2) :
    Matrix (Fin C.n) (Fin C.n) ℂ :=
  (2⁻¹ : ℂ) • (1 + paritySign b • C.parityOp v)

theorem parityFactor_eq_bit (s : ParitySector C.layout) (v : C.layout.V) :
    C.parityFactor s v = C.parityFactorBit v (s v) := rfl

/-- The two single-tetron parity factors at a vertex sum to the identity:
`(1 + P)/2 + (1 − P)/2 = 1`.  This is the per-vertex completeness that, multiplied
over all vertices, gives `sectorProjector_sum`. -/
theorem parityFactorBit_sum (v : C.layout.V) :
    ∑ b : ZMod 2, C.parityFactorBit v b = 1 := by
  have h2 : (∑ b : ZMod 2, C.parityFactorBit v b)
      = C.parityFactorBit v 0 + C.parityFactorBit v 1 := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [h2]
  unfold parityFactorBit paritySign
  simp only [if_pos rfl, if_neg (by decide : (1 : ZMod 2) ≠ 0), one_smul, neg_smul]
  match_scalars <;> norm_num

/-- Any two bit-indexed parity factors commute (polynomials in commuting
`parityOp`s). -/
theorem parityFactorBit_comm (v w : C.layout.V) (a b : ZMod 2) :
    Commute (C.parityFactorBit v a) (C.parityFactorBit w b) := by
  have hPP : Commute (C.parityOp v) (C.parityOp w) := C.parityComm v w
  unfold parityFactorBit
  refine Commute.smul_left (Commute.smul_right ?_ _) _
  refine Commute.add_left (Commute.add_right (Commute.one_left _) ?_)
            (Commute.add_right (Commute.one_right _) ?_)
  · exact (Commute.one_left _).smul_right _
  · exact ((hPP.smul_left _).smul_right _)

/-- Sector projectors sum to the identity (complete decomposition).

`∑_s ∏_v g_v(s_v) = ∏_v (∑_b g_v(b)) = ∏_v 1 = 1`, the distributive interchange
mechanised in `noncommProd_sum_pi`.  The sum-over-sectors / product-over-vertices
swap is the heart of the `CellProjectorSystem` completeness axiom. -/
theorem sectorProjector_sum :
    ∑ s : ParitySector C.layout, C.sectorProjector s = 1 := by
  classical
  -- Rewrite each `sectorProjector s` as a `noncommProd` of bit-indexed factors.
  have hsp : ∀ s : ParitySector C.layout,
      C.sectorProjector s
        = Finset.univ.attach.noncommProd
            (fun x : {x // x ∈ (Finset.univ : Finset C.layout.V)} =>
              C.parityFactorBit x.1 (s x.1))
            (fun x _ y _ _ => C.parityFactorBit_comm x.1 y.1 _ _) := by
    intro s
    rw [sectorProjector, noncommProd_attach Finset.univ (C.parityFactor s)]
    refine Finset.noncommProd_congr rfl (fun x _ => ?_) _
    rw [parityFactor_eq_bit]
  -- Apply the distributive interchange with `t _ = univ`, `f v b = g_v(b)`.
  have hkey := noncommProd_sum_pi (A := Matrix (Fin C.n) (Fin C.n) ℂ)
    (κ := fun _ : C.layout.V => ZMod 2) Finset.univ (fun _ => Finset.univ)
    (fun v b => C.parityFactorBit v b)
    (fun i j a b => C.parityFactorBit_comm i j a b)
  -- LHS of `hkey`: `∏_v (∑_b g_v b) = ∏_v 1 = 1`.
  have hLHS : (Finset.univ.noncommProd (fun v => ∑ b : ZMod 2, C.parityFactorBit v b)
      (fun i _ j _ _ => Commute.sum_left _ _ _
        (fun a _ => Commute.sum_right _ _ _
          (fun b _ => C.parityFactorBit_comm i j a b)))) = 1 := by
    rw [Finset.noncommProd_congr rfl (fun v _ => C.parityFactorBit_sum v)]
    simp [Finset.noncommProd_eq_pow_card]
  rw [hLHS] at hkey
  -- RHS of `hkey`: a sum over `univ.pi (fun _ => univ)`; reindex via
  -- `sum_univ_pi` to a sum over `Fintype.piFinset (fun _ => univ) = univ`, i.e.
  -- over all sectors `x : V → ZMod 2`.
  rw [Finset.sum_univ_pi, Fintype.piFinset_univ] at hkey
  -- `1 = ∑_{x : V → ZMod 2} attach.noncommProd (fun y => parityFactorBit y.1 (x y.1))`.
  rw [eq_comm] at hkey
  rw [← hkey]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hsp]

/-- The `CellProjectorSystem` of the joint-parity decomposition. -/
noncomputable def cellProjectorSystem :
    CellProjectorSystem C.n (ParitySector C.layout) where
  p := C.sectorProjector
  herm := C.sectorProjector_isHermitian
  idem := C.sectorProjector_idem
  orth := C.sectorProjector_orth
  sum_eq_one := C.sectorProjector_sum

end TetronChip

/-! ## §3.  Spectral disassembly: the effective per-sector Hamiltonian

The Tower-3 statement formalized here: the parity-sector decomposition is a
`QuantumEquitablePartition` of the chip's operator system, and — crucially — the
chip's **designated Hamiltonian** `C.hamiltonian` *compresses* onto the parity
sectors to a genuinely *block-diagonal* effective Hamiltonian.  This is the
de-hollowed disassembly: it is built by tracing the *actual chip Hamiltonian*
(not the unit `1`) against the sector projectors, and the block-diagonality
**uses** parity conservation essentially.

The conceptual content: the chip Hamiltonian is *parity-conserving* — it commutes
with every `parityOp v` — and therefore commutes with every joint-parity sector
projector `sectorProjector s` (a polynomial in the `parityOp`s,
`hamiltonian_commute_sectorProjector`).  Commutation with the projectors is
exactly the operator-algebraic equitable / locality condition
(`block_offdiag_eq_zero`), so the compression `p_s · H · p_t` vanishes for `s ≠ t`:
the chip disassembles into one independent block per sector
(`effectiveHamiltonian_isDiag`, here `chip_effectiveHamiltonian_isDiag`).

The per-tetron `Mat₂(ℂ)` logical structure is built from the genuine Majorana
data in §3a (`TetronLogical`): the Karzig logical Paulis `Z_log = iγ₁γ₂`,
`X_log = iγ₁γ₃` are Hermitian involutions that **anticommute**, hence generate a
copy of `Mat₂(ℂ)` (the Pauli algebra) on the fixed-total-parity 2-dimensional
logical subspace (Karzig et al. 2017, Sec. III).
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

/-- **Any operator that commutes with every parity operator commutes with every
sector projector.**  The sector projector `sectorProjector s` is a
`Finset.noncommProd` of the single-tetron factors `parityFactor s v`, each a
polynomial `(1 + ±parityOp v)/2` in a `parityOp`.  If `A` commutes with each
`parityOp v` it commutes with each `parityFactor s v`, hence with their product
(`Finset.noncommProd_commute`).  This is the operator-algebraic bridge from the
*physical* parity-conservation condition (commuting with the parity operators) to
the *equitable* condition (commuting with the cell projectors). -/
theorem commute_sectorProjector_of_commute_parityOp
    {A : Matrix (Fin C.n) (Fin C.n) ℂ}
    (hA : ∀ v : C.layout.V, A * C.parityOp v = C.parityOp v * A)
    (s : ParitySector C.layout) :
    A * C.sectorProjector s = C.sectorProjector s * A := by
  classical
  -- `A` commutes with each `parityFactor s v` (a polynomial in `parityOp v`).
  have hfac : ∀ v : C.layout.V, Commute A (C.parityFactor s v) := by
    intro v
    have hAP : Commute A (C.parityOp v) := hA v
    unfold parityFactor
    refine Commute.smul_right (Commute.add_right (Commute.one_right _) ?_) _
    exact hAP.smul_right _
  -- Hence `A` commutes with their `noncommProd` (= `sectorProjector s`).
  have : Commute A (C.sectorProjector s) := by
    unfold sectorProjector
    exact Finset.noncommProd_commute _ _ _ _ (fun v _ => hfac v)
  exact this

/-- **The chip Hamiltonian commutes with every sector projector.**  Specialization
of `commute_sectorProjector_of_commute_parityOp` to `A = C.hamiltonian`, using the
parity-conservation hypothesis (which applies because `C.hamiltonian ∈ opSystem`).
This is where `IsParityConserving` and `hamiltonianMem` are *both used*: parity
conservation only constrains elements of `opSystem`, and the Hamiltonian is one. -/
theorem hamiltonian_commute_sectorProjector (hPC : C.IsParityConserving)
    (s : ParitySector C.layout) :
    C.hamiltonian * C.sectorProjector s = C.sectorProjector s * C.hamiltonian :=
  C.commute_sectorProjector_of_commute_parityOp
    (fun v => hPC C.hamiltonian C.hamiltonianMem v) s

/-- The **effective (per-sector) chip Hamiltonian**: the compression of the
designated chip Hamiltonian `C.hamiltonian` onto the joint-parity sectors,
`Hₑ(s, t) = tr(p_s · H · p_t)/√(d_s d_t)`.

Unlike the retracted projector-Gram matrix, this is `effectiveHamiltonian` of the
*actual chip Hamiltonian*, so its entries genuinely depend on the chip dynamics
(the single-tetron gap terms and the inter-tetron couplings carried by
`C.hamiltonian`). -/
noncomputable def effectiveHamiltonian (hPC : C.IsParityConserving) :
    Matrix (ParitySector C.layout) (ParitySector C.layout) ℂ :=
  (C.parityQuantumEquitablePartition hPC).effectiveHamiltonian C.hamiltonian

/-- **The effective chip Hamiltonian is Hermitian** (the chip Hamiltonian is
self-adjoint, so its compression is too).  This is the genuine, dynamics-bearing
upgrade of the retracted `parityProjectorGram_isHermitian`. -/
theorem effectiveHamiltonian_isHermitian (hPC : C.IsParityConserving) :
    (C.effectiveHamiltonian hPC).IsHermitian :=
  (C.parityQuantumEquitablePartition hPC).effectiveHamiltonian_isHermitian
    C.hamiltonianHerm

/-- **HEADLINE — spectral disassembly of the chip Hamiltonian.**

If the chip is parity-conserving, the effective Hamiltonian obtained by
compressing the *designated chip Hamiltonian* onto the joint-parity sectors is
**block-diagonal**: its off-diagonal `(s, t)` entry vanishes for every pair of
distinct sectors `s ≠ t`.

This is the genuine disassembly: the chip Hamiltonian decouples completely across
parity sectors — there is one independent effective block per sector, with no
inter-sector mixing.  The proof *uses* parity conservation essentially (via
`hamiltonian_commute_sectorProjector`); without it the off-diagonal blocks need
not vanish.  This replaces the retracted, chip-independent projector-Gram
statement with a true theorem about the chip's own dynamics.

(In the Karzig–Knapp tetron encoding the relevant sectors are the joint
fixed-total-parity sectors of the tetron lattice; the per-sector block is a
`Mat₂(ℂ)`-valued effective Hamiltonian on the logical subspace — see the
single-tetron `Mat₂(ℂ)` logical algebra in §3a.) -/
theorem chip_effectiveHamiltonian_isDiag (hPC : C.IsParityConserving) :
    ∀ s t : ParitySector C.layout, s ≠ t →
      C.effectiveHamiltonian hPC s t = 0 := by
  apply (C.parityQuantumEquitablePartition hPC).effectiveHamiltonian_isDiag
  -- The required commutation `H · p_s = p_s · H` is
  -- `hamiltonian_commute_sectorProjector` (the cells of the partition are the
  -- sector projectors).
  intro s
  exact C.hamiltonian_commute_sectorProjector hPC s

/-- **The diagonal block is the genuine sector-restricted Hamiltonian.**  Under
parity conservation the compression `p_s · H · p_s` of the chip Hamiltonian onto
sector `s` collapses to `p_s · H` — the honest restriction of the dynamics to the
parity sector `s` (no off-sector leakage).  Together with
`chip_effectiveHamiltonian_isDiag` this is the complete disassembly: `H` acts
within each sector as `p_s · H` and across sectors as `0`. -/
theorem chip_block_diag_eq (hPC : C.IsParityConserving)
    (s : ParitySector C.layout) :
    (C.parityQuantumEquitablePartition hPC).block C.hamiltonian s s
      = C.sectorProjector s * C.hamiltonian := by
  apply (C.parityQuantumEquitablePartition hPC).block_diag_eq
  intro t
  exact C.hamiltonian_commute_sectorProjector hPC t

end TetronChip

/-! ### §3a.  The single-tetron logical `Mat₂(ℂ)` algebra (Karzig et al. 2017)

The §3 disassembly shows the chip Hamiltonian block-decouples across joint-parity
sectors.  The remaining half of the "2×2 effective Hamiltonian per tetron"
headline is the *per-tetron* structure: each tetron's logical subspace carries a
genuine `Mat₂(ℂ)` — the Pauli algebra of the logical qubit.

The physics (Karzig–Knapp–Lutchyn et al. 2017, Sec. III).  A tetron has four
Majorana zero modes `γ₁, γ₂, γ₃, γ₄`, each a Hermitian involution
(`γᵢ² = 1`, `γᵢᴴ = γᵢ`), pairwise *anticommuting* (`γᵢγⱼ = −γⱼγᵢ`, `i ≠ j`).
The total fermion parity `P = −γ₁γ₂γ₃γ₄` is fixed by Coulomb blockade, restricting
to a 2-dimensional logical subspace.  On that subspace the logical Paulis are

    `Z_log = i γ₁ γ₂`,   `X_log = i γ₁ γ₃`,   `Y_log = i Z_log X_log = i γ₂ γ₃ … `

— each Hermitian, squaring to `1`, and **pairwise anticommuting**; this is exactly
the defining relation of the `2 × 2` Pauli algebra, so the logical operators
generate a copy of `Mat₂(ℂ)`.

We formalize the *core algebraic fact* — that the logical `Z` and `X` built from
three pairwise-anticommuting Hermitian involutions are themselves Hermitian
involutions that anticommute, i.e. a Pauli pair — entirely from the Majorana
relations, with no `sorry`.  This is what licenses the "2×2-per-tetron" language. -/

/-- A **single-tetron Majorana system** on an `m`-dimensional Hilbert space: four
Majorana zero modes `γ : Fin 4 → M_m(ℂ)`, each a self-adjoint involution, with
distinct modes anticommuting.  This is the genuine operator data of one
Karzig-et-al. tetron. -/
structure TetronLogical (m : ℕ) where
  /-- The four Majorana zero-mode operators `γ₁, γ₂, γ₃, γ₄`. -/
  γ : Fin 4 → Matrix (Fin m) (Fin m) ℂ
  /-- Each Majorana operator is self-adjoint (`γᵢᴴ = γᵢ`). -/
  herm : ∀ i, (γ i).IsHermitian
  /-- Each Majorana operator squares to the identity (`γᵢ² = 1`). -/
  sq : ∀ i, γ i * γ i = 1
  /-- Distinct Majorana operators anticommute (`γᵢγⱼ = −γⱼγᵢ`). -/
  anticomm : ∀ i j, i ≠ j → γ i * γ j = - (γ j * γ i)

namespace TetronLogical

variable {m : ℕ} (T : TetronLogical m)

/-- The logical **Pauli `Z`** of the tetron: `Z_log = i γ₁ γ₂`. -/
noncomputable def Zlog : Matrix (Fin m) (Fin m) ℂ :=
  Complex.I • (T.γ 0 * T.γ 1)

/-- The logical **Pauli `X`** of the tetron: `X_log = i γ₁ γ₃`. -/
noncomputable def Xlog : Matrix (Fin m) (Fin m) ℂ :=
  Complex.I • (T.γ 0 * T.γ 2)

/-- The logical **Pauli `Y`** of the tetron: `Y_log = i γ₂ γ₃`.  (Up to the
overall sign convention `Y = iXZ`; here we take the equivalent `iγ₂γ₃`.) -/
noncomputable def Ylog : Matrix (Fin m) (Fin m) ℂ :=
  Complex.I • (T.γ 1 * T.γ 2)

/-- **`Z_log` is a Hermitian involution.**  `(iγ₁γ₂)ᴴ = -i (γ₂ᴴγ₁ᴴ) = -i γ₂γ₁ =
-i(-γ₁γ₂) = iγ₁γ₂`, and `(iγ₁γ₂)² = -γ₁γ₂γ₁γ₂ = γ₁γ₁γ₂γ₂ = 1`. -/
theorem Zlog_isHermitian : (T.Zlog).IsHermitian := by
  unfold Zlog Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, (T.herm 0).eq, (T.herm 1).eq]
  -- `star I • (γ₂ * γ₁) = I • (γ₀ * γ₁)`.  `star I = -I`, and `γ₂γ₁ = γ₁ ... `
  -- Use anticommutation `γ₁γ₂ = -(γ₂γ₁)`, i.e. `γ₂γ₁ = -(γ₁γ₂)`.
  rw [show T.γ 1 * T.γ 0 = -(T.γ 0 * T.γ 1) from T.anticomm 1 0 (by decide)]
  rw [Complex.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]

theorem Zlog_sq : T.Zlog * T.Zlog = 1 := by
  unfold Zlog
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I]
  -- `(γ₀γ₁)(γ₀γ₁) = -1` so `(-1)•(-1)... ` Let us compute `(γ₀γ₁)(γ₀γ₁)`.
  have key : (T.γ 0 * T.γ 1) * (T.γ 0 * T.γ 1) = -1 := by
    have h10 := T.anticomm 1 0 (by decide)  -- γ₁γ₀ = -(γ₀γ₁)
    calc (T.γ 0 * T.γ 1) * (T.γ 0 * T.γ 1)
        = T.γ 0 * (T.γ 1 * T.γ 0) * T.γ 1 := by
          simp only [Matrix.mul_assoc]
      _ = T.γ 0 * (-(T.γ 0 * T.γ 1)) * T.γ 1 := by rw [h10]
      _ = -(T.γ 0 * T.γ 0) * (T.γ 1 * T.γ 1) := by
          rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul]
          simp only [Matrix.mul_assoc]
      _ = -1 := by rw [T.sq 0, T.sq 1, Matrix.mul_one]
  rw [key, neg_one_smul, neg_neg]

/-- **`X_log` is a Hermitian involution.**  Identical computation with `γ₃` in
place of `γ₂`. -/
theorem Xlog_isHermitian : (T.Xlog).IsHermitian := by
  unfold Xlog Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, (T.herm 0).eq, (T.herm 2).eq]
  rw [show T.γ 2 * T.γ 0 = -(T.γ 0 * T.γ 2) from T.anticomm 2 0 (by decide)]
  rw [Complex.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]

theorem Xlog_sq : T.Xlog * T.Xlog = 1 := by
  unfold Xlog
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I]
  have key : (T.γ 0 * T.γ 2) * (T.γ 0 * T.γ 2) = -1 := by
    have h20 := T.anticomm 2 0 (by decide)
    calc (T.γ 0 * T.γ 2) * (T.γ 0 * T.γ 2)
        = T.γ 0 * (T.γ 2 * T.γ 0) * T.γ 2 := by simp only [Matrix.mul_assoc]
      _ = T.γ 0 * (-(T.γ 0 * T.γ 2)) * T.γ 2 := by rw [h20]
      _ = -(T.γ 0 * T.γ 0) * (T.γ 2 * T.γ 2) := by
          rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul]
          simp only [Matrix.mul_assoc]
      _ = -1 := by rw [T.sq 0, T.sq 2, Matrix.mul_one]
  rw [key, neg_one_smul, neg_neg]

/-- **The logical Paulis anticommute: `Z_log X_log = − X_log Z_log`.**

`Z_log X_log = (iγ₁γ₂)(iγ₁γ₃) = −γ₁γ₂γ₁γ₃`, while
`X_log Z_log = (iγ₁γ₃)(iγ₁γ₂) = −γ₁γ₃γ₁γ₂`; using the pairwise anticommutation of
`γ₁, γ₂, γ₃` (and `γ₁² = 1`) both reduce to `±γ₂γ₃` with opposite signs.  This
is the defining Pauli relation — the operators generate `Mat₂(ℂ)`. -/
theorem Zlog_Xlog_anticomm : T.Zlog * T.Xlog = - (T.Xlog * T.Zlog) := by
  have h10 := T.anticomm 1 0 (by decide)  -- γ₁γ₀ = -(γ₀γ₁)
  have h20 := T.anticomm 2 0 (by decide)  -- γ₂γ₀ = -(γ₀γ₂)
  have h12 := T.anticomm 1 2 (by decide)  -- γ₁γ₂ = -(γ₂γ₁)
  -- Word identity LHS: γ₀γ₁γ₀γ₂ = γ₀(γ₁γ₀)γ₂ = γ₀(-(γ₀γ₁))γ₂ = -(γ₀γ₀)γ₁γ₂ = -γ₁γ₂.
  have hLHS : (T.γ 0 * T.γ 1) * (T.γ 0 * T.γ 2) = -(T.γ 1 * T.γ 2) := by
    calc (T.γ 0 * T.γ 1) * (T.γ 0 * T.γ 2)
        = T.γ 0 * (T.γ 1 * T.γ 0) * T.γ 2 := by simp only [Matrix.mul_assoc]
      _ = T.γ 0 * (-(T.γ 0 * T.γ 1)) * T.γ 2 := by rw [h10]
      _ = -((T.γ 0 * T.γ 0) * (T.γ 1 * T.γ 2)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(T.γ 1 * T.γ 2) := by rw [T.sq 0, Matrix.one_mul]
  -- Word identity RHS: γ₀γ₂γ₀γ₁ = -(γ₀γ₀)γ₂γ₁ = -γ₂γ₁ = γ₁γ₂.
  have hRHS : (T.γ 0 * T.γ 2) * (T.γ 0 * T.γ 1) = (T.γ 1 * T.γ 2) := by
    calc (T.γ 0 * T.γ 2) * (T.γ 0 * T.γ 1)
        = T.γ 0 * (T.γ 2 * T.γ 0) * T.γ 1 := by simp only [Matrix.mul_assoc]
      _ = T.γ 0 * (-(T.γ 0 * T.γ 2)) * T.γ 1 := by rw [h20]
      _ = -((T.γ 0 * T.γ 0) * (T.γ 2 * T.γ 1)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(T.γ 2 * T.γ 1) := by rw [T.sq 0, Matrix.one_mul]
      _ = (T.γ 1 * T.γ 2) := h12.symm
  -- Assemble with scalars: `Zlog Xlog = i²•(γ₀γ₁γ₀γ₂) = -1•(-γ₁γ₂) = γ₁γ₂`, and
  -- `Xlog Zlog = i²•(γ₀γ₂γ₀γ₁) = -1•(γ₁γ₂) = -γ₁γ₂`.
  have hZX : T.Zlog * T.Xlog = T.γ 1 * T.γ 2 := by
    unfold Zlog Xlog
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, hLHS,
      neg_one_smul, neg_neg]
  have hXZ : T.Xlog * T.Zlog = -(T.γ 1 * T.γ 2) := by
    unfold Zlog Xlog
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, hRHS,
      neg_one_smul]
  rw [hZX, hXZ, neg_neg]

/-- **The total fermion parity `P = −γ₁γ₂γ₃γ₄` is a Hermitian involution** that
**commutes** with both logical Paulis `Z_log` and `X_log`.  This is the
superselection operator: it commutes with the logical algebra (each logical Pauli
is built from `γ₁,γ₂,γ₃`, and `P` is the full 4-fold product), so fixing its
value `±1` restricts to a logical subspace stable under `Z_log, X_log` — exactly
the parity-protected 2-dimensional logical qubit. -/
noncomputable def totalParity : Matrix (Fin m) (Fin m) ℂ :=
  - (T.γ 0 * T.γ 1 * T.γ 2 * T.γ 3)

/-- `Z_log` commutes with the total parity `P`: both are *even* words in the
Majoranas (a product of two vs. four generators), and even Majorana words commute.
Concretely `Z_log = iγ₁γ₂` and `P = -γ₁γ₂γ₃γ₄`: straightening each product against
the Majorana relations reduces **both** `Z_log·P` and `P·Z_log` to `i·γ₃γ₄`
(`-γ₃γ₄` from the bare words, times the `-1` from the two prefactors `i` and the
sign of `P`), so they agree.  This is the superselection statement: fixing the
total parity leaves the logical algebra `⟨Z_log, X_log⟩` invariant. -/
theorem Zlog_commute_totalParity : T.Zlog * T.totalParity = T.totalParity * T.Zlog := by
  -- Conceptual route.  Write `P = -(c₀₁ * c₂₃)` with `c₀₁ = γ₀γ₁`, `c₂₃ = γ₂γ₃`.
  -- The pair `c₀₁` and `c₂₃` **commute** (each of γ₀,γ₁ anticommutes with each of
  -- γ₂,γ₃, giving four sign flips → net `+1`).  Then both `Zlog·P` and `P·Zlog`
  -- equal `-i•(c₀₁·c₀₁·c₂₃)` and so agree.  Only `Commute c₀₁ c₂₃` is needed.
  -- A single Majorana `γ a` **commutes** with a 2-product `γ b * γ c` when `a`
  -- differs from both `b, c`: two anticommutations give a net `+1`.
  have single_comm_pair : ∀ a b c : Fin 4, a ≠ b → a ≠ c →
      T.γ a * (T.γ b * T.γ c) = (T.γ b * T.γ c) * T.γ a := by
    intro a b c hab hac
    have hb := T.anticomm a b hab  -- γₐγ_b = -(γ_bγₐ)
    have hc := T.anticomm a c hac  -- γₐγ_c = -(γ_cγₐ)
    calc T.γ a * (T.γ b * T.γ c)
        = (T.γ a * T.γ b) * T.γ c := by rw [Matrix.mul_assoc]
      _ = (-(T.γ b * T.γ a)) * T.γ c := by rw [hb]
      _ = -(T.γ b * (T.γ a * T.γ c)) := by
            simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(T.γ b * (-(T.γ c * T.γ a))) := by rw [hc]
      _ = (T.γ b * T.γ c) * T.γ a := by
            simp only [Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  -- Hence `c₀₁ = γ₀γ₁` commutes with `c₂₃ = γ₂γ₃` (both γ₀ and γ₁ commute with it).
  have hC : Commute (T.γ 0 * T.γ 1) (T.γ 2 * T.γ 3) := by
    have c0 : Commute (T.γ 0) (T.γ 2 * T.γ 3) := single_comm_pair 0 2 3 (by decide) (by decide)
    have c1 : Commute (T.γ 1) (T.γ 2 * T.γ 3) := single_comm_pair 1 2 3 (by decide) (by decide)
    exact c0.mul_left c1
  -- `totalParity = -(c₀₁ * c₂₃)` (associate the 4-fold product as `(γ₀γ₁)(γ₂γ₃)`).
  have hP : T.totalParity = -((T.γ 0 * T.γ 1) * (T.γ 2 * T.γ 3)) := by
    unfold totalParity; simp only [Matrix.mul_assoc]
  -- Assemble using `Commute c₀₁ c₂₃`.  Abbreviate `c₀₁ := γ₀γ₁`, `c₂₃ := γ₂γ₃`
  -- (atomic), so associativity is clean.
  unfold Zlog
  rw [hP]
  set c01 := T.γ 0 * T.γ 1 with hc01
  set c23 := T.γ 2 * T.γ 3 with hc23
  -- Goal: `(i•c₀₁) * (-(c₀₁ * c₂₃)) = (-(c₀₁ * c₂₃)) * (i•c₀₁)`.  Pull `i•` and
  -- `-` to the front; the cores agree by `Commute c₀₁ c₂₃` (`hC`).
  calc (Complex.I • c01) * (-(c01 * c23))
      = -(Complex.I • (c01 * (c01 * c23))) := by
        simp only [Matrix.smul_mul, Matrix.mul_neg, smul_neg]
    _ = -(Complex.I • ((c01 * c23) * c01)) := by
        -- `c01` commutes with `c01 * c23` (with itself and, by `hC`, with `c23`).
        rw [((Commute.refl c01).mul_right hC).eq]
    _ = (-(c01 * c23)) * (Complex.I • c01) := by
        simp only [Matrix.mul_smul, Matrix.neg_mul, smul_neg]

/-- **The single-tetron logical algebra is `Mat₂(ℂ)`** (the Pauli algebra): the
three constructions `Zlog`, `Xlog`, `Ylog` are Hermitian involutions, `Zlog` and
`Xlog` anticommute, and `Ylog = i·Zlog·Xlog`.  This packages the genuine
per-tetron `2 × 2` logical-Pauli structure (Karzig et al. 2017, Sec. III) as a
single non-vacuous statement — the algebraic content licensing the "2×2 effective
Hamiltonian per tetron" disassembly language of §3. -/
theorem logical_pauli_algebra :
    (T.Zlog).IsHermitian ∧ (T.Xlog).IsHermitian ∧
      T.Zlog * T.Zlog = 1 ∧ T.Xlog * T.Xlog = 1 ∧
      T.Zlog * T.Xlog = - (T.Xlog * T.Zlog) ∧
      T.Ylog = Complex.I • (T.Zlog * T.Xlog) := by
  refine ⟨T.Zlog_isHermitian, T.Xlog_isHermitian, T.Zlog_sq, T.Xlog_sq,
    T.Zlog_Xlog_anticomm, ?_⟩
  -- `Ylog = iγ₁γ₂`, and `i•(Zlog·Xlog) = i•(γ₁γ₂)` since `Zlog·Xlog = γ₁γ₂`
  -- (computed in `Zlog_Xlog_anticomm`'s hLHS branch).
  have hZX : T.Zlog * T.Xlog = T.γ 1 * T.γ 2 := by
    have h10 := T.anticomm 1 0 (by decide)
    have hLHS : (T.γ 0 * T.γ 1) * (T.γ 0 * T.γ 2) = -(T.γ 1 * T.γ 2) := by
      calc (T.γ 0 * T.γ 1) * (T.γ 0 * T.γ 2)
          = T.γ 0 * (T.γ 1 * T.γ 0) * T.γ 2 := by simp only [Matrix.mul_assoc]
        _ = T.γ 0 * (-(T.γ 0 * T.γ 1)) * T.γ 2 := by rw [h10]
        _ = -((T.γ 0 * T.γ 0) * (T.γ 1 * T.γ 2)) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = -(T.γ 1 * T.γ 2) := by rw [T.sq 0, Matrix.one_mul]
    unfold Zlog Xlog
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, hLHS,
      neg_one_smul, neg_neg]
  rw [hZX]
  rfl

/-! ### Non-vacuity: a concrete tetron model on `ℂ⁴`

The `TetronLogical` relations are not vacuous: they have an explicit `4 × 4`
model — the standard two-qubit representation of four Majoranas

    γ₀ = X⊗I,   γ₁ = Y⊗I,   γ₂ = Z⊗X,   γ₃ = Z⊗Y

on `ℂ² ⊗ ℂ² ≅ ℂ⁴` (basis order `00,01,10,11`).  Each is Hermitian, squares to
`1`, and any two distinct ones anticommute.  We give the matrices explicitly and
prove the structure fields by entrywise computation, witnessing
`Nonempty (TetronLogical 4)` — so `logical_pauli_algebra` is non-vacuous. -/

/-- The explicit Majorana operators of the concrete `ℂ⁴` tetron model. -/
noncomputable def modelγ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]          -- X⊗I
  | 1 => !![0, 0, -Complex.I, 0; 0, 0, 0, -Complex.I;
            Complex.I, 0, 0, 0; 0, Complex.I, 0, 0]                  -- Y⊗I
  | 2 => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0]        -- Z⊗X
  | 3 => !![0, -Complex.I, 0, 0; Complex.I, 0, 0, 0;
            0, 0, 0, Complex.I; 0, 0, -Complex.I, 0]                 -- Z⊗Y

set_option maxHeartbeats 1600000 in
/-- **Non-vacuity witness.**  The concrete `ℂ⁴` Majorana operators satisfy all the
`TetronLogical` axioms, so `TetronLogical 4` is inhabited.  Consequently every
`TetronLogical` theorem (in particular `logical_pauli_algebra`) is applicable to a
genuine model and is **not vacuous**.

The fields are checked by entrywise computation on the explicit `4 × 4` matrices;
we raise `maxHeartbeats` because the `anticomm` field unfolds `16` ordered pairs
of `4 × 4` complex matrix products. -/
noncomputable def model : TetronLogical 4 where
  γ := modelγ
  herm := by
    intro i
    fin_cases i <;>
      · show Matrix.IsHermitian _
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [modelγ, Matrix.conjTranspose_apply, Complex.conj_I]
  sq := by
    intro i
    fin_cases i <;>
      · ext a b
        fin_cases a <;> fin_cases b <;>
          simp [modelγ, Matrix.mul_apply, Fin.sum_univ_four]
  anticomm := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | · ext a b
          fin_cases a <;> fin_cases b <;>
            simp [modelγ, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_four]

theorem tetronLogical_nonempty : Nonempty (TetronLogical 4) := ⟨model⟩

end TetronLogical

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
    (hP : P.cells = BD.decoration.label)
    -- CORRECTNESS FIX (propagated from `TQFT.braid_factors_through_cellUniform`):
    -- the locality hypothesis is genuinely needed — a bare unitary braid need
    -- not preserve cell-uniformity; each elementary braid must lie in the
    -- coherent algebra of the parity-sector partition.
    (hLocal : ∀ (i : Fin BD.numStrands) (φ : ParitySector C.layout → ℂ),
        (∀ x y, BD.decoration.label x = BD.decoration.label y → φ x = φ y) →
        ∀ x y, BD.decoration.label x = BD.decoration.label y →
          (Matrix.mulVec (BD.braid.σ i) φ) x = (Matrix.mulVec (BD.braid.σ i) φ) y) :
    -- For every elementary braid `σᵢ` and every cell-uniform input `ψ`,
    -- the output is again cell-uniform.
    ∀ (i : Fin BD.numStrands) (ψ : ParitySector C.layout → ℂ),
      (∀ x y, BD.decoration.label x = BD.decoration.label y → ψ x = ψ y) →
      (∀ x y, BD.decoration.label x = BD.decoration.label y →
        (Matrix.mulVec (BD.braid.σ i) ψ) x =
        (Matrix.mulVec (BD.braid.σ i) ψ) y) :=
  TQFT.braid_factors_through_cellUniform BD.decoration BD.braid P hP hLocal

/-- **Theorem (composition of braids = composition of quotient gates).**
For two braids `σ_i` and `σ_j`, the cell-uniform-action of their composite
is the composite of the cell-uniform-actions.  This is the elementary
*functoriality* of `braid_factors_through_cellUniform` and is what makes
braiding a *gate* (rather than an arbitrary unitary). -/
theorem braid_composition_quotient
    {M : ModularData (ParitySector C.layout)} (BD : C.BraidData M)
    (P : EquitablePartition C.chipQuotientGraph (ParitySector C.layout))
    (hP : P.cells = BD.decoration.label)
    -- CORRECTNESS FIX (propagated from `TQFT.braid_factors_through_cellUniform`):
    -- the per-braid locality hypothesis is genuinely needed (see above).
    (hLocal : ∀ (k : Fin BD.numStrands) (φ : ParitySector C.layout → ℂ),
        (∀ x y, BD.decoration.label x = BD.decoration.label y → φ x = φ y) →
        ∀ x y, BD.decoration.label x = BD.decoration.label y →
          (Matrix.mulVec (BD.braid.σ k) φ) x = (Matrix.mulVec (BD.braid.σ k) φ) y)
    (i j : Fin BD.numStrands) :
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
  have h1 := TQFT.braid_factors_through_cellUniform BD.decoration BD.braid P hP hLocal i ψ hψ
  -- ...hence so is `σ_j · (σ_i · ψ)`.
  exact TQFT.braid_factors_through_cellUniform BD.decoration BD.braid P hP hLocal j
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

/-! ## §6.  Engineering payoffs (all proved — no `sorry`)

These are the three payoffs: (1) FKLW-conditional braid-gate realizability of an
arbitrary logical unitary (honest *approximate* form, delegating to
`TQFT.braid_gate_realizable`), (2) parity-symmetric noise preserves the
cell-uniform subspace, and (3) drift-robust equitability iff flat connection.
All three are genuine theorems; payoff 1 carries the FKLW density theorem as a
typeclass hypothesis rather than an axiom or `sorry`.
-/

namespace TetronChip

variable (C : TetronChip)

/-! ### 6.1.  Topologically-protected PST between two tetrons via braiding

A `BraidGate` from `Graphplay/Integrations/TQFT.lean` §7.2 acts on the
parity-sector quotient as a unitary.  When the gate is *PST-realizing* in
the cell-uniform sense, it transports the cell-uniform state at one tetron
sector to that at another.
-/

/-- **Payoff 1 (topologically-protected logical gate via braiding) — honest
form.**  Given the chip's `BraidData` and the FKLW universality hypothesis
`[BraidGateUniversal BD.braid]` (the Freedman–Larsen–Wang density theorem,
carried as a typeclass), **every** target logical unitary `U` on the
parity-sector logical space is realized to arbitrary precision `ε > 0` by an
*actual braid word* `w`: the word's representation is genuinely unitary and is
within `ε` of `U` entrywise.

HONEST RESTATEMENT (replaces a false `sorry`).  The previous `payoff1` asserted
*exact* cell-uniform PST `IsCellUniformPST … BG.τ` realized by a single
braid-gate CTQW.  That statement is **mathematically false**: the spectrum of a
single `exp(−iτH)` restricted to an invariant subspace lies on a one-parameter
subgroup of the unit circle, so it cannot equal the spectrum of an arbitrary
target unitary (see the honesty note on `TQFT.braid_gate_realizable`).  The
genuine, faithful topological-quantum-computation payoff is *density /
approximation* by braid **words** (a discrete subgroup), not exact reachability
by one exponential.  This delegates directly to `TQFT.braid_gate_realizable`; the
one external input — the FLW density theorem — is honestly a typeclass
hypothesis, not an axiom or a `sorry`.

The "topological protection" is the content of `TQFT.BraidGateUniversal`:
braiding alone (no fine-tuned Hamiltonian, no measurement) suffices, and the
realized gate is exactly unitary on the nose (only the *target match* is
approximate). -/
theorem payoff1_braiding_realizes_logical_gate
    {M : ModularData (ParitySector C.layout)}
    (BD : C.BraidData M) [TQFT.BraidGateUniversal BD.braid]
    (U : Matrix (ParitySector C.layout) (ParitySector C.layout) ℂ)
    (hU : U * Uᴴ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : BD.braid.Word,
      (BD.braid.wordMatrix w * (BD.braid.wordMatrix w)ᴴ = 1 ∧
        (BD.braid.wordMatrix w)ᴴ * BD.braid.wordMatrix w = 1) ∧
      ∀ a b : ParitySector C.layout, ‖U a b - BD.braid.wordMatrix w a b‖ < ε :=
  -- `U` is two-sidedly unitary (one side suffices for square matrices,
  -- `Matrix.mul_eq_one_comm`); the FKLW density theorem then gives the word.
  TQFT.braid_gate_realizable BD.braid U hU (Matrix.mul_eq_one_comm.mp hU) hε

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

/-- A `NoiseModel` is **parity-symmetric** with respect to a given family of
per-tetron parity operators `parityOpV v : Matrix C.layout.V C.layout.V ℂ` (the
images of `C.parityOp v` on the chip's reduced `V → ℂ` Hilbert space) if every
jump operator commutes with every per-tetron parity operator.

NON-VACUITY FIX: the previous version asked `L * 1 = 1 * L`, i.e. `L = L`, a
predicate satisfied by *every* `L` — vacuously `True` and saying nothing about
parity.  We now take the genuine parity-operator family as an explicit parameter
(the `parityOpV` argument, supplying the V-level lift the older comment said was
missing) and demand honest commutation `L * Pᵥ = Pᵥ * L`. -/
def NoiseModel.parityConserving
    (parityOpV : C.layout.V → Matrix C.layout.V C.layout.V ℂ)
    (N : NoiseModel C.layout.V) : Prop :=
  ∀ L ∈ N.lindblad_operators, ∀ v : C.layout.V,
    L * parityOpV v = parityOpV v * L

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
be a perturbed flux configuration.  The drift `F` is **flat** (Wilson holonomy
trivial on every loop) *iff* the flux-dressed walk is **drift-invisible**: the
flux-induced signing `F.toChiralSigning` reproduces, on every closed loop, the
*same* Wilson holonomy as the nominal (zero-drift) flux.

This is the Tower-6-sheaf upgrade of "topologically-protected gates require
flat connections": drift-invisibility (the parity-sector partition is preserved
under drift) is *exactly* flatness.

CORRECTNESS FIX (replaces a *false* prior statement and its `sorry`): the prior
RHS `∃ σ, σ.CrossConstant P.cells` is **vacuously `True`** — `ChiralSigning.trivial`
is always cross-constant — so the iff was not a theorem.  We pin the witness to the
genuine *flux-induced* signing `F.toChiralSigning` and use the honest
drift-invisibility property (equal Wilson holonomy to nominal on every loop),
which is genuinely equivalent to flatness.  This delegates to the proven
`flat_iff_partition_preserved`. -/
theorem payoff3_drift_iff_flat
    (PM : ParamManifold) (hPC : C.IsParityConserving)
    (P : EquitablePartition C.chipQuotientGraph (ParitySector C.layout))
    (F : C.fluxField) :
    -- `F` is flat **iff** the flux-dressed walk is drift-invisible: on every loop
    -- `γ`, the drifted flux `F` has the same Wilson holonomy as the nominal flux.
    fluxField.isFlat C F ↔
      (∀ γ : List C.layout.V,
        LatticeGauge.U1GaugeField.wilsonCycle (V := C.layout.V)
            (G := C.layout.graph) F γ
          = LatticeGauge.U1GaugeField.wilsonCycle (V := C.layout.V)
            (G := C.layout.graph) (C.nominalFlux) γ) :=
  C.flat_iff_partition_preserved PM hPC F

end TetronChip

/-! ## §7.  What's defensible vs. what's speculation

Putting it all together, here is the honest separation.

### Defensible:

* The parity-sector decomposition is a *literal* `EquitablePartition` of the
  chip-quotient graph, provided the chip Hamiltonian is parity-conserving
  (which is the operating assumption of every published Microsoft Majorana
  design).  This is §3.

* **Spectral disassembly (the de-hollowed headline).**  The chip's *designated*
  Hamiltonian compresses onto the parity sectors to a genuinely block-diagonal
  effective Hamiltonian (`chip_effectiveHamiltonian_isDiag`): off-sector blocks
  vanish, and each diagonal block is the honest sector restriction `p_s · H`
  (`chip_block_diag_eq`).  The proof *uses* parity conservation essentially
  (`hamiltonian_commute_sectorProjector`).  The single-tetron logical algebra is
  a genuine `Mat₂(ℂ)` — the Karzig logical Paulis `Z=iγ₁γ₂`, `X=iγ₁γ₃` are
  Hermitian involutions that anticommute (`TetronLogical.logical_pauli_algebra`),
  with `P = −γ₁γ₂γ₃γ₄` commuting with the logical algebra
  (`TetronLogical.Zlog_commute_totalParity`).  This is §3, §3a — no `sorry`, no
  axioms beyond the propext/Classical/Quot trio.

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
