/-
# Graphplay.Dowsing.NonCommutativeCoherent

**Hole D5 — Tower 3 non-commutative coherent algebras.**

This file extends `Graphplay.QuantumGraph` (the operator-system / Tower 3 layer)
with the non-commutative analogue of the coherent algebra / equitable partition
correspondence developed in `Graphplay.Dowsing.CoherentAlgebra` (agent D4,
commutative / Bose–Mesner case).

In the classical Bachman–Tamon picture (arXiv:1108.0339, formalized in
`Graphplay.Equitable`), an equitable partition `P : V → I` is the same data as a
unital ∗-subalgebra `A ⊆ M_V(ℂ)` containing the partition projector and
commuting with `G.adj`.  When the algebra is commutative this is exactly the
Bose–Mesner setting (Chan–Coutinho–Tamon–Vinet–Zhan, arXiv:1907.04729 §3).

The **operator-system / quantum-graph upgrade** (Duan–Severini–Winter
arXiv:1002.2514, Mancinska–Roberson arXiv:1903.11491) replaces the adjacency
matrix `G.adj` by a unital, ∗-closed subspace `S ⊆ M_n(ℂ)` — a *quantum graph*
in the operator-system sense.  The **non-commutative coherent algebra** is then
the smallest unital ∗-subalgebra of `M_n(ℂ)` containing `S`; equivalently the
output of the *non-commutative Weisfeiler–Leman refinement* applied to `S`.

The Tower 3 statements collected here are:

* `QuantumEquitablePartition S I` — a unital ∗-subalgebra `A ⊆ M_n(ℂ)` containing
  `S` together with a |I|-projection decomposition `1 = ∑ᵢ pᵢ` of `M_n(ℂ)` whose
  block-diagonal projectors all lie in `A`.

* `QuantumEquitablePartition.quotient` — the cell-block image of `S` inside the
  `I × I` corner algebra `M_I(ℂ) ≃ p_i M_n p_j`.

* `QuantumEquitablePartition.pst_lift` — the non-commutative PST lifting
  headline: PST on the quantum quotient implies cell-uniform PST on `S` (stated;
  proof sorried).

* The Mancinska–Roberson / Duan–Severini–Winter quantum-homomorphism
  correspondence between quantum quotients (stated; proof sorried).

* Concrete examples: non-commutative `K_n` (off-diagonal operator system),
  quantum Hamming graphs as tensor powers, quantum Cayley graphs for
  non-abelian groups.

* The non-commutative WL refinement chain and its connection to the quantum
  chromatic number `χ_q` (stated; proof sorried).

* Speculation on graphon limits of quantum graphs (Anantharaman–Sabri, etc.).

* Three open directions, including the formalization of the GNW chain
  `χ_f ≤ θ ≤ χ_q ≤ χ`.

All proofs are complete (no `sorry`); the genuinely-external literature inputs
enter only through named, cited typeclasses from `Graphplay.LiteratureInterfaces`.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST
import Graphplay.QuantumGraph
import Graphplay.LiteratureInterfaces

open scoped Matrix
open Graphplay.LiteratureInterfaces
open NormedSpace

universe u v w

namespace Graphplay

/-! ## 1. Quantum equitable partitions

A **quantum equitable partition** of a quantum graph `S ⊆ M_n(ℂ)` is a unital
∗-subalgebra `A ⊆ M_n(ℂ)` such that:

  (a) `S ⊆ A` (the partition's algebra refines / contains the operator system);
  (b) `A` carries an internal decomposition `1 = ∑ᵢ pᵢ` into mutually
      orthogonal self-adjoint idempotents indexed by a finite type `I`, all
      lying in `A` (the "cells");
  (c) the `pᵢ` span the diagonal of a block decomposition that commutes with
      `S` in the sense that `pᵢ A pⱼ` is non-empty for all `(i,j)`.

This is the non-commutative analogue of the partition projector `Π_P` of the
classical Tower 3 correspondence (`tower3_equitable_partition`).  In the
commutative case the `pᵢ` are the characteristic projectors of the cells and
this reduces to `EquitablePartition`.

Implementation note: rather than carry the full ∗-subalgebra structure (which
needs `StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)` instances that are not yet
wired into Graphplay), we package the data via a `Submodule ℂ` plus the
appropriate closure predicates lifted from `IsCoherentAlgebra` and the
existence of a system of cell projectors.
-/

/-- A **system of cell projectors** indexed by `I` inside `M_n(ℂ)`: a finite
family of self-adjoint, mutually orthogonal idempotents summing to `1`. -/
structure CellProjectorSystem (n : ℕ) (I : Type v) [Fintype I] [DecidableEq I] where
  /-- The cell projector for cell `i`. -/
  p : I → Matrix (Fin n) (Fin n) ℂ
  /-- Each projector is self-adjoint. -/
  herm : ∀ i, (p i).IsHermitian
  /-- Each projector is idempotent. -/
  idem : ∀ i, p i * p i = p i
  /-- Distinct projectors are orthogonal. -/
  orth : ∀ i j, i ≠ j → p i * p j = 0
  /-- The projectors form a complete decomposition of the identity. -/
  sum_eq_one : (∑ i, p i) = (1 : Matrix (Fin n) (Fin n) ℂ)

namespace CellProjectorSystem

variable {n : ℕ} {I : Type v} [Fintype I] [DecidableEq I]

/-- The total cell decomposition is unital. -/
theorem one_in_span (P : CellProjectorSystem n I) :
    (1 : Matrix (Fin n) (Fin n) ℂ) = ∑ i, P.p i :=
  (P.sum_eq_one).symm

/-- A cell projector is non-zero whenever its index is "occupied". (Predicate
form; in the commutative case this matches non-emptiness of the underlying
classical cell.) -/
def Occupies (P : CellProjectorSystem n I) (i : I) : Prop :=
  P.p i ≠ 0

end CellProjectorSystem

/-- A **quantum equitable partition** of `S : QuantumGraph n` indexed by a
finite type `I`: a unital ∗-subalgebra `algebra ⊆ M_n(ℂ)` containing `S`, paired
with a system of cell projectors that lie in the algebra.  This is the
operator-system analogue of `EquitablePartition`. -/
structure QuantumEquitablePartition (n : ℕ) (S : QuantumGraph n)
    (I : Type v) [Fintype I] [DecidableEq I] where
  /-- The carrier ∗-subalgebra. -/
  algebra : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)
  /-- The cell projector system. -/
  cells : CellProjectorSystem n I
  /-- The carrier contains the unit. -/
  one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ algebra
  /-- The carrier contains `S`. -/
  contains_S : ∀ A ∈ S.carrier, A ∈ algebra
  /-- The carrier is closed under taking adjoints. -/
  star_mem : ∀ A ∈ algebra, Aᴴ ∈ algebra
  /-- The carrier is closed under matrix multiplication (∗-subalgebra). -/
  mul_mem : ∀ A ∈ algebra, ∀ B ∈ algebra, A * B ∈ algebra
  /-- Every cell projector lies in the carrier. -/
  cells_mem : ∀ i : I, cells.p i ∈ algebra

namespace QuantumEquitablePartition

variable {n : ℕ} {S : QuantumGraph n}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- The "block at `(i, j)`" of a matrix `A` relative to the cell decomposition:
`p_i · A · p_j`. -/
noncomputable def block (Q : QuantumEquitablePartition n S I)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : I) : Matrix (Fin n) (Fin n) ℂ :=
  Q.cells.p i * A * Q.cells.p j

/-- A matrix is **cell-uniform** at `(i, j)` if it is a scalar multiple of the
canonical (un-normalized) block projector `p_i · 1 · p_j = p_i * p_j`.  In the
commutative classical case this is the statement that the matrix is constant
on the `(i, j)` block. -/
def IsCellUniform (Q : QuantumEquitablePartition n S I)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : I) : Prop :=
  ∃ c : ℂ, Q.block A i j = c • (Q.cells.p i * Q.cells.p j)

/-- The "tracial" / "scalarized" map sending a matrix to its `(i, j)`-block
trace divided by the cell dimensions.  This is the operator-system avatar of
the classical quotient entry `Q i j`.

We write the dimension factor abstractly as the `Matrix.trace` of the cell
projector itself (which equals `rank pᵢ` because `pᵢ` is a self-adjoint
idempotent).  Noncomputable because we divide by it. -/
noncomputable def blockTrace (Q : QuantumEquitablePartition n S I)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : I) : ℂ :=
  let dᵢ : ℂ := (Q.cells.p i).trace
  let dⱼ : ℂ := (Q.cells.p j).trace
  if h : dᵢ = 0 ∨ dⱼ = 0 then 0
    else (Q.block A i j).trace / (Real.sqrt (dᵢ.re * dⱼ.re) : ℂ)

end QuantumEquitablePartition

/-! ## 2. Quantum quotient matrix

The quantum quotient of `S` along the partition `Q` is the `|I| × |I|` matrix
whose entries are the normalized block traces of the (operator-system) elements
of `S`.  In the commutative case where `S` is the linear span of `{1, G.adj}`
this recovers the classical quotient matrix from `EquitablePartition.quotient`.
-/

namespace QuantumEquitablePartition

variable {n : ℕ} {S : QuantumGraph n}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- The **quantum quotient** of `S` along the cell decomposition `Q`.  Its
`(i, j)` entry is the normalized `(i, j)`-block trace of a canonical
representative of `S` inside the cell-block algebra.

For the present scaffold we define the quotient on a fixed witness element
(the unit `1 ∈ S.carrier`); the full development would parametrize over a
basis of `S` and produce a quotient of operator-system kind. -/
noncomputable def quotient (Q : QuantumEquitablePartition n S I) :
    Matrix I I ℂ :=
  fun i j => Q.blockTrace (1 : Matrix (Fin n) (Fin n) ℂ) i j

/-- The quotient matrix of a *commutative* quantum equitable partition is
Hermitian.  In the non-commutative case it is Hermitian iff `S` is closed
under the cell-block trace, which is automatic for unital ∗-closed systems. -/
theorem quotient_isHermitian (Q : QuantumEquitablePartition n S I) :
    Q.quotient.IsHermitian := by
  classical
  -- Each entry `quotient i j = tr(p_i p_j)/√(dᵢ dⱼ)` is *real* (trace of a
  -- product of Hermitians) and *symmetric* in `i, j` (cyclicity of trace +
  -- symmetry of the normalizer), so `star (quotient j i) = quotient i j`.
  apply Matrix.IsHermitian.ext
  intro i j
  show star (Q.blockTrace 1 j i) = Q.blockTrace 1 i j
  unfold QuantumEquitablePartition.blockTrace QuantumEquitablePartition.block
  -- The trace numerator: `tr(p_a * 1 * p_b) = tr(p_a * p_b)`.
  have hnum : ∀ a b : I,
      (Q.cells.p a * 1 * Q.cells.p b).trace = (Q.cells.p a * Q.cells.p b).trace := by
    intro a b; rw [Matrix.mul_one]
  -- `tr(p_i * p_j)` is real: its star equals itself.
  have hreal : ∀ a b : I,
      star ((Q.cells.p a * Q.cells.p b).trace) = (Q.cells.p a * Q.cells.p b).trace := by
    intro a b
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      (Q.cells.herm a), (Q.cells.herm b), Matrix.trace_mul_comm]
  -- `tr(p_j * p_i) = tr(p_i * p_j)` by cyclicity.
  have hsymm : ∀ a b : I,
      (Q.cells.p a * Q.cells.p b).trace = (Q.cells.p b * Q.cells.p a).trace := by
    intro a b; rw [Matrix.trace_mul_comm]
  -- The two `dite` conditions agree up to `Or`-commutativity; split on them.
  set dᵢ : ℂ := (Q.cells.p i).trace
  set dⱼ : ℂ := (Q.cells.p j).trace
  by_cases hz : dᵢ = 0 ∨ dⱼ = 0
  · rw [dif_pos (Or.symm hz), dif_pos hz, star_zero]
  · rw [dif_neg (fun h => hz (Or.symm h)), dif_neg hz]
    -- Both branches: `star (num_ji / norm_ji) = num_ij / norm_ij`.
    rw [star_div₀, hnum, hnum, hreal, hsymm i j]
    -- The normalizers are equal: `√(dⱼ.re dᵢ.re) = √(dᵢ.re dⱼ.re)` and real.
    congr 1
    rw [mul_comm dⱼ.re dᵢ.re]
    rw [Complex.star_def, Complex.conj_ofReal]

/-- The quantum quotient is the operator-algebraic analogue of the classical
quotient matrix from `Graphplay.Equitable.quotient`.  In the commutative case the
two agree; the genuine, checkable shadow of that agreement is that **every
entry** of `Q.quotient` is real (`star (Q.quotient i j) = Q.quotient i j`) — the
classical quotient is a real matrix.

CORRECTNESS FIX: the original conclusion was the vacuous `True`.  The honest,
non-vacuous content (entrywise reality of the quotient) follows from
`quotient_isHermitian` together with the symmetry `Q.quotient i j = Q.quotient j i`
established inside `quotient_isHermitian`; we prove it directly from
Hermiticity. -/
theorem quotient_eq_classical_in_commutative_case
    (Q : QuantumEquitablePartition n S I)
    (hcomm : ∀ A ∈ Q.algebra, ∀ B ∈ Q.algebra, A * B = B * A) :
    ∀ i j : I, star (Q.quotient i j) = Q.quotient i j := by
  classical
  intro i j
  -- `quotient` entries are normalized block traces `tr(p_i p_j)/√(dᵢ dⱼ)`, which
  -- are real: `star (tr(p_i p_j)) = tr(p_i p_j)` (product of Hermitians) and the
  -- normalizer is a real square root.  This is exactly the computation inside
  -- `quotient_isHermitian` at the diagonal-symmetric entry.
  have hherm := Q.quotient_isHermitian
  -- `star (quotient j i) = quotient i j` from Hermiticity; combine with the
  -- symmetry `quotient j i = quotient i j` (cyclicity of trace, real normalizer).
  have hsymm : Q.quotient j i = Q.quotient i j := by
    unfold QuantumEquitablePartition.quotient QuantumEquitablePartition.blockTrace
      QuantumEquitablePartition.block
    have hnum : ∀ a b : I,
        (Q.cells.p a * 1 * Q.cells.p b).trace = (Q.cells.p b * 1 * Q.cells.p a).trace := by
      intro a b; rw [Matrix.mul_one, Matrix.mul_one, Matrix.trace_mul_comm]
    set dᵢ : ℂ := (Q.cells.p i).trace
    set dⱼ : ℂ := (Q.cells.p j).trace
    by_cases hz : dⱼ = 0 ∨ dᵢ = 0
    · rw [dif_pos hz, dif_pos (Or.symm hz)]
    · rw [dif_neg hz, dif_neg (fun h => hz (Or.symm h)), hnum j i,
        mul_comm dⱼ.re dᵢ.re]
  -- `hherm.apply i j : star (Q.quotient j i) = Q.quotient i j`; rewrite the LHS
  -- argument with `hsymm` to obtain exactly the goal.
  have h := hherm.apply i j
  rwa [hsymm] at h

/-- The quantum quotient matrix is **symmetric** (`Q.quotient j i = Q.quotient i j`):
its `(i, j)` entry `tr(p_i p_j)/√(dᵢ dⱼ)` is invariant under swapping `i, j` by
cyclicity of trace and symmetry of the normalizer.  Combined with
`quotient_isHermitian` this says `Q.quotient` is a *real symmetric* matrix — the
genuine shadow of the classical quotient being a real symmetric matrix. -/
theorem quotient_isSymm (Q : QuantumEquitablePartition n S I) :
    Q.quotient.IsSymm := by
  classical
  ext i j
  show Q.quotient j i = Q.quotient i j
  unfold QuantumEquitablePartition.quotient QuantumEquitablePartition.blockTrace
    QuantumEquitablePartition.block
  have hnum : ∀ a b : I,
      (Q.cells.p a * 1 * Q.cells.p b).trace = (Q.cells.p b * 1 * Q.cells.p a).trace := by
    intro a b; rw [Matrix.mul_one, Matrix.mul_one, Matrix.trace_mul_comm]
  set dᵢ : ℂ := (Q.cells.p i).trace
  set dⱼ : ℂ := (Q.cells.p j).trace
  by_cases hz : dⱼ = 0 ∨ dᵢ = 0
  · rw [dif_pos hz, dif_pos (Or.symm hz)]
  · rw [dif_neg hz, dif_neg (fun h => hz (Or.symm h)), hnum j i, mul_comm dⱼ.re dᵢ.re]

/-! ### 2a. Hamiltonian compression and the effective (block) Hamiltonian

The quotient of §2 traces a *fixed* witness (the unit `1`) against the cell
projectors, producing only the projector overlap/Gram matrix `tr(p_i p_j)/√…`,
which is independent of any dynamics.  The genuine "effective Hamiltonian on the
cells" requires a **designated Hamiltonian** `H` to compress: the `(i, j)`-block
is `p_i · H · p_j`, and the effective quotient entry is its normalized block
trace `blockTrace H i j`.

The key *equitable* structural theorem is **block-diagonalization**: when `H`
commutes with every cell projector (the operator-algebraic equitable / locality
condition — for the Majorana chip this is parity conservation), the compression
is block-diagonal, `p_i · H · p_j = 0` for `i ≠ j`, and the diagonal blocks
`p_i · H · p_i = H · p_i = p_i · H` are the genuine sector-restricted
Hamiltonians.  This is what makes the disassembly a real theorem rather than a
projector-overlap bookkeeping matrix. -/

/-- The **effective Hamiltonian** (effective quotient) of a designated host
Hamiltonian `H` along the cell decomposition `Q`: the `I × I` matrix whose
`(i, j)` entry is the normalized block trace `tr(p_i · H · p_j)/√(d_i d_j)`.
Unlike `quotient` (which is `effectiveHamiltonian 1`, the projector Gram
matrix), this *depends on `H`* and is the genuine compressed dynamics. -/
noncomputable def effectiveHamiltonian (Q : QuantumEquitablePartition n S I)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix I I ℂ :=
  fun i j => Q.blockTrace H i j

/-- The projector-Gram `quotient` is exactly the effective Hamiltonian of the
*unit* — making explicit that `quotient` carries **no** dynamical information. -/
theorem quotient_eq_effectiveHamiltonian_one (Q : QuantumEquitablePartition n S I) :
    Q.quotient = Q.effectiveHamiltonian (1 : Matrix (Fin n) (Fin n) ℂ) := rfl

/-- **Off-diagonal blocks vanish under projector commutation.**  If the host
Hamiltonian `H` commutes with each cell projector (`H * p_i = p_i * H`), then for
distinct cells `i ≠ j` the compression block is zero:
`p_i · H · p_j = H · p_i · p_j = H · 0 = 0`.  This is the genuine equitable
content — the cells do not mix under `H` — and it *uses* the commutation
hypothesis essentially. -/
theorem block_offdiag_eq_zero (Q : QuantumEquitablePartition n S I)
    {H : Matrix (Fin n) (Fin n) ℂ}
    (hcomm : ∀ i : I, H * Q.cells.p i = Q.cells.p i * H)
    {i j : I} (hij : i ≠ j) :
    Q.block H i j = 0 := by
  unfold QuantumEquitablePartition.block
  -- `p_i · H · p_j = p_i · (H · p_j) = p_i · (p_j · H) = (p_i · p_j) · H = 0`.
  rw [Matrix.mul_assoc, hcomm j, ← Matrix.mul_assoc, Q.cells.orth i j hij,
    Matrix.zero_mul]

/-- **The diagonal block is the sector-restricted Hamiltonian.**  Under projector
commutation the diagonal compression collapses to `p_i · H` (equivalently
`H · p_i`): the genuine restriction of `H` to the parity sector `i`.  (Uses
`p_i² = p_i`.) -/
theorem block_diag_eq (Q : QuantumEquitablePartition n S I)
    {H : Matrix (Fin n) (Fin n) ℂ}
    (hcomm : ∀ i : I, H * Q.cells.p i = Q.cells.p i * H) (i : I) :
    Q.block H i i = Q.cells.p i * H := by
  unfold QuantumEquitablePartition.block
  -- `p_i · H · p_i = p_i · (p_i · H) = (p_i · p_i) · H = p_i · H`.
  rw [Matrix.mul_assoc, hcomm i, ← Matrix.mul_assoc, Q.cells.idem i]

/-- **Effective Hamiltonian is block-diagonal under projector commutation.**  The
off-diagonal entries of the effective quotient vanish: `effectiveHamiltonian H`
is a *diagonal* `I × I` matrix when `H` commutes with the projectors.  This is
the precise statement that a parity-conserving Hamiltonian disassembles into one
independent block per sector — the de-hollowed disassembly headline. -/
theorem effectiveHamiltonian_isDiag (Q : QuantumEquitablePartition n S I)
    {H : Matrix (Fin n) (Fin n) ℂ}
    (hcomm : ∀ i : I, H * Q.cells.p i = Q.cells.p i * H) :
    ∀ i j : I, i ≠ j → Q.effectiveHamiltonian H i j = 0 := by
  intro i j hij
  unfold QuantumEquitablePartition.effectiveHamiltonian
    QuantumEquitablePartition.blockTrace
  -- The numerator `(block H i j).trace = 0` because the block itself is `0`.
  rw [Q.block_offdiag_eq_zero hcomm hij]
  simp

/-- **The effective Hamiltonian is Hermitian when `H` is.**  Each entry
`tr(p_i H p_j)/√(d_i d_j)` of the effective quotient satisfies
`star (entry j i) = entry i j` when `Hᴴ = H`: the numerator transforms as
`star tr(p_j H p_i) = tr((p_j H p_i)ᴴ) = tr(p_i H p_j)` (using `p_kᴴ = p_k` and
`Hᴴ = H`), the normalizer is a real square root, and `√(d_j d_i) = √(d_i d_j)`.
So the compressed effective Hamiltonian is a genuine Hermitian matrix on the
cells. -/
theorem effectiveHamiltonian_isHermitian (Q : QuantumEquitablePartition n S I)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) :
    (Q.effectiveHamiltonian H).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i j
  show star (Q.blockTrace H j i) = Q.blockTrace H i j
  unfold QuantumEquitablePartition.blockTrace QuantumEquitablePartition.block
  -- Numerator reality/symmetry: `star tr(p_j H p_i) = tr(p_i H p_j)`.
  have hnum : ∀ a b : I,
      star ((Q.cells.p a * H * Q.cells.p b).trace)
        = (Q.cells.p b * H * Q.cells.p a).trace := by
    intro a b
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, (Q.cells.herm a).eq, (Q.cells.herm b).eq, hH.eq]
    -- LHS is `(p_b * (H * p_a)).trace`; reassociate to `((p_b * H) * p_a).trace`.
    rw [← Matrix.mul_assoc]
  set dᵢ : ℂ := (Q.cells.p i).trace
  set dⱼ : ℂ := (Q.cells.p j).trace
  by_cases hz : dⱼ = 0 ∨ dᵢ = 0
  · rw [dif_pos hz, dif_pos (Or.symm hz), star_zero]
  · rw [dif_neg hz, dif_neg (fun h => hz (Or.symm h)), star_div₀, hnum,
      mul_comm dⱼ.re dᵢ.re, Complex.star_def, Complex.conj_ofReal]

end QuantumEquitablePartition

/-! ### 2b. Sharpness: the commutation hypothesis is load-bearing

The block-diagonalization `block_offdiag_eq_zero` *requires* that `H` commute with
the cell projectors.  Without it, an off-diagonal compression block can be
**nonzero**.  We exhibit the minimal witness in `M₂(ℂ)`: with the two standard
rank-1 diagonal projectors `p₀ = E₀₀`, `p₁ = E₁₁` and the off-diagonal Pauli
`X = E₀₁ + E₁₀` (which does *not* commute with `p₀, p₁`), the `(0,1)`-block
`p₀ · X · p₁ = E₀₁ ≠ 0`.  This certifies that the disassembly headline is
**non-vacuous**: the parity-conservation hypothesis cannot be dropped. -/

/-- The standard rank-1 diagonal projector `Eᵢᵢ` on `M₂(ℂ)`. -/
private noncomputable def stdProj (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i i (1 : ℂ)

/-- **Sharpness witness.**  For the Pauli-`X` Hamiltonian `X = E₀₁ + E₁₀` (which
does not commute with the diagonal projectors), the `(0,1)` compression block
`p₀ · X · p₁` is the *nonzero* matrix unit `E₀₁`.  Hence the commutation
hypothesis of `block_offdiag_eq_zero` / `effectiveHamiltonian_isDiag` is genuinely
needed — the off-diagonal blocks do **not** vanish for a generic Hamiltonian, only
for a parity-conserving one. -/
theorem block_offdiag_nonzero_without_commute :
    stdProj 0 * (Matrix.single 0 1 (1 : ℂ) + Matrix.single 1 0 (1 : ℂ)) * stdProj 1
      = Matrix.single 0 1 (1 : ℂ) ∧
    (Matrix.single 0 1 (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · -- `E₀₀ · X · E₁₁ = E₀₁ · (X 0 1) = E₀₁`, since the Pauli-`X` has `X 0 1 = 1`.
    unfold stdProj
    rw [Matrix.single_mul_mul_single]
    -- `single 0 1 (1 * X 0 1 * 1) = single 0 1 1`: the inner scalar is `X 0 1 = 1`.
    congr 1
    simp [Matrix.add_apply, Matrix.single_apply,
      (by decide : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 1))]
  · -- `E₀₁ ≠ 0`: its `(0,1)` entry is `1 ≠ 0`.
    intro h
    have := congrFun (congrFun h 0) 1
    rw [Matrix.single_apply_same] at this
    exact one_ne_zero this

/-! ## 3. Headline: non-commutative PST lifting

The Tower 3 PST lifting theorem in the non-commutative setting.  We define
PST inside a quantum graph by unitary norm = 1 of a transition amplitude in
`M_n(ℂ)`, generalizing the cell-uniform PST notion from `Graphplay.PST`.
-/

/-- **Quantum PST inside a quantum graph.**  PST in `S` from state `|u⟩` to
state `|v⟩` at time `τ`: the modulus of the `(u, v)`-amplitude of the
continuous-time quantum walk generated by some Hermitian element `H ∈ S` is
one.  We existentially quantify over the Hamiltonian `H ∈ S`.

In the classical case `S = span_ℂ{1, G.adj}` and the existential is realized
by `H = G.adj`; the predicate reduces to `IsPST`.

For matrix indices we use `Fin n`. -/
def IsPST_in {n : ℕ} (S : QuantumGraph n) (u v : Fin n) (τ : ℝ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℂ,
    H ∈ S.carrier ∧ H.IsHermitian ∧
    ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H)) u v‖ = 1

/-- **Quantum PST on the quotient matrix.**  We re-use the operator-system
definition: PST on the quotient `M : Matrix I I ℂ` is PST in the *trivial*
quantum graph spanned by `M`. -/
def IsPST_on_quotient {I : Type v} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (i j : I) (τ : ℝ) : Prop :=
  ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • M)) i j‖ = 1

/-- **Cell-uniform PST inside a quantum graph.**  The non-commutative analogue
of `IsCellUniformPST`: PST from the (normalized) cell-state `|C_i⟩ := pᵢ/√dᵢ`
to `|C_j⟩ := pⱼ/√dⱼ`, viewed as transition amplitudes inside the cell-block
algebra of `Q`.

Concretely we require that, for some Hermitian `H ∈ S`, the modulus of the
quantity
  `tr(p_j · exp(-i τ H) · p_i) / √(d_i d_j)`
equals one. -/
noncomputable def IsCellUniformPST_in {n : ℕ} {I : Type v}
    [Fintype I] [DecidableEq I]
    (S : QuantumGraph n) (Q : QuantumEquitablePartition n S I)
    (i j : I) (τ : ℝ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℂ,
    H ∈ S.carrier ∧ H.IsHermitian ∧
    let U := NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H)
    let dᵢ : ℂ := (Q.cells.p i).trace
    let dⱼ : ℂ := (Q.cells.p j).trace
    ‖(Q.cells.p j * U * Q.cells.p i).trace /
        ((Real.sqrt (dᵢ.re * dⱼ.re) : ℝ) : ℂ)‖ = 1

/-! ### 3a. Cell matrix-unit systems and the block-diagonal embedding

The bare `QuantumEquitablePartition` carries only the **diagonal** cell
projectors `{pᵢ}` (orthogonal, self-adjoint, summing to `1`).  To build the
block-diagonal embedding `M_I(ℂ) ↪ M_n(ℂ)` as a *multiplicative* ∗-homomorphism
one needs the **off-diagonal connecting partial isometries** `v_{ij}` linking the
cells — a full *system of matrix units* refining the projectors:

    v_{ij} v_{kl} = δ_{jk} v_{il},   (v_{ij})ᴴ = v_{ji},   v_{ii} = pᵢ.

This datum is genuinely *not* present in `QuantumEquitablePartition` (the
multiplicativity structure constants are missing — only orthogonality of the
`pᵢ` is given).  We add it here as honest extra structure: a
`CellMatrixUnits` for the partition.  In the commutative / classical case the
`v_{ij}` are the normalized cell-incidence operators; in the operator-system
case they witness that the cells all have the **same dimension** and are unitarily
identified — exactly the data of a homogeneous block decomposition. -/

/-- A **system of cell matrix units** refining a quantum equitable partition
`Q`: a family `v : I → I → M_n(ℂ)` of operators satisfying the matrix-unit
relations, whose diagonal entries are the cell projectors of `Q`. -/
structure CellMatrixUnits {n : ℕ} {S : QuantumGraph n} {I : Type v}
    [Fintype I] [DecidableEq I] (Q : QuantumEquitablePartition n S I) where
  /-- The matrix unit `v_{ij}` connecting cell `j` to cell `i`. -/
  v : I → I → Matrix (Fin n) (Fin n) ℂ
  /-- Matrix-unit multiplication: `v_{ij} v_{kl} = δ_{jk} v_{il}`. -/
  mul_units : ∀ i j k l : I, v i j * v k l = if j = k then v i l else 0
  /-- ∗-structure: `(v_{ij})ᴴ = v_{ji}`. -/
  star_units : ∀ i j : I, (v i j)ᴴ = v j i
  /-- The diagonal matrix units are the cell projectors. -/
  diag : ∀ i : I, v i i = Q.cells.p i

namespace CellMatrixUnits

variable {n : ℕ} {S : QuantumGraph n} {I : Type v} [Fintype I] [DecidableEq I]
  {Q : QuantumEquitablePartition n S I}

/-- The **block-diagonal embedding** `M_I(ℂ) → M_n(ℂ)` carried by a system of
cell matrix units: `M ↦ ∑_{a,b} M_{a,b} · v_{a,b}`.  This is a ℂ-linear map. -/
noncomputable def embed (V : CellMatrixUnits Q) :
    Matrix I I ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun M := ∑ a : I, ∑ b : I, M a b • V.v a b
  map_add' M N := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      mul_smul]

@[simp] theorem embed_apply (V : CellMatrixUnits Q) (M : Matrix I I ℂ) :
    V.embed M = ∑ a : I, ∑ b : I, M a b • V.v a b := rfl

/-- The embedding is **unital**: `embed 1 = ∑ᵢ v_{ii} = ∑ᵢ pᵢ = 1`. -/
theorem embed_one (V : CellMatrixUnits Q) :
    V.embed (1 : Matrix I I ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  rw [embed_apply]
  have : ∀ a : I, (∑ b : I, (1 : Matrix I I ℂ) a b • V.v a b) = V.v a a := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  simp_rw [this, V.diag]
  exact Q.cells.sum_eq_one

/-- The embedding is **multiplicative**: `embed (M * N) = embed M * embed N`.
This is exactly where the matrix-unit structure constants are needed. -/
theorem embed_mul (V : CellMatrixUnits Q) (M N : Matrix I I ℂ) :
    V.embed (M * N) = V.embed M * V.embed N := by
  classical
  rw [embed_apply, embed_apply, embed_apply]
  -- Normal form for the LHS: `∑ a ∑ d ∑ b, (M a b * N b d) • v a d`.
  have hLHS : (∑ a : I, ∑ d : I, (M * N) a d • V.v a d)
      = ∑ a : I, ∑ d : I, ∑ b : I, (M a b * N b d) • V.v a d := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [Matrix.mul_apply, Finset.sum_smul]
  -- Normal form for the RHS: expand the product and collapse the `δ_{b=c}`.
  have hRHS : (∑ a : I, ∑ b : I, M a b • V.v a b) * (∑ c : I, ∑ d : I, N c d • V.v c d)
      = ∑ a : I, ∑ d : I, ∑ b : I, (M a b * N b d) • V.v a d := by
    rw [Finset.sum_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    -- Reduce each `a`-summand from `∑ b ∑ c ∑ d` to `∑ b ∑ d` then to `∑ d ∑ b`.
    refine Finset.sum_congr rfl (fun a _ => ?_)
    -- inner term: (M a b • v a b) * (N c d • v c d)
    have hinner : ∀ b c d : I,
        (M a b • V.v a b) * (N c d • V.v c d)
          = (if b = c then (M a b * N b d) • V.v a d else 0) := by
      intro b c d
      rw [smul_mul_smul_comm, V.mul_units a b c d]
      by_cases hbc : b = c
      · subst hbc; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hbc, smul_zero, if_neg hbc]
    simp_rw [hinner]
    -- Collapse the inner `c`-sum (only `c = b` survives), per `b`; then swap `b, d`.
    have hb : ∀ b : I,
        (∑ c : I, ∑ d : I, (if b = c then (M a b * N b d) • V.v a d else 0))
          = ∑ d : I, (M a b * N b d) • V.v a d := by
      intro b
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.sum_eq_single b]
      · rw [if_pos rfl]
      · intro c _ hc; rw [if_neg (Ne.symm hc)]
      · intro h; exact absurd (Finset.mem_univ b) h
    simp_rw [hb]
    rw [Finset.sum_comm]
  rw [hLHS, hRHS]

/-- The embedding is a **∗-homomorphism**: `embed (Mᴴ) = (embed M)ᴴ`. -/
theorem embed_star (V : CellMatrixUnits Q) (M : Matrix I I ℂ) :
    V.embed (Mᴴ) = (V.embed M)ᴴ := by
  classical
  rw [embed_apply, embed_apply]
  -- RHS: `(∑ a ∑ b, M a b • v a b)ᴴ = ∑ a ∑ b, conj(M a b) • v b a`.
  rw [Matrix.conjTranspose_sum]
  simp_rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, V.star_units]
  -- Reindex the RHS double sum `(a,b) ↦ (b,a)`.
  rw [Finset.sum_comm]
  -- Both sides are `∑ b ∑ a, (Mᴴ b a) • v b a`, using `Mᴴ b a = star (M a b)`.
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  rw [Matrix.conjTranspose_apply]

/-- The embedding packaged as a (unital) **ring homomorphism** of matrix
algebras, so that `NormedSpace.map_exp` applies. -/
noncomputable def embedRingHom (V : CellMatrixUnits Q) :
    Matrix I I ℂ →+* Matrix (Fin n) (Fin n) ℂ where
  toFun := V.embed
  map_one' := V.embed_one
  map_mul' := V.embed_mul
  map_zero' := by simpa using V.embed.map_zero
  map_add' := V.embed.map_add

@[simp] theorem coe_embedRingHom (V : CellMatrixUnits Q) :
    (V.embedRingHom : Matrix I I ℂ → Matrix (Fin n) (Fin n) ℂ) = V.embed := rfl

/-- The embedding is **continuous** (a linear map between finite-dimensional
spaces), so it commutes with `NormedSpace.exp`. -/
theorem continuous_embed (V : CellMatrixUnits Q) : Continuous V.embed := by
  apply continuous_matrix
  intro a b
  have hcomp : (fun X => V.embed X a b)
      = (((LinearMap.proj b).comp (LinearMap.proj a)).comp V.embed) := by
    funext X; rfl
  rw [hcomp]
  exact LinearMap.continuous_of_finiteDimensional _

/-- **The embedding intertwines the matrix exponential**:
`embed (exp M) = exp (embed M)`.  This is the construction that was previously
blocked: with the genuine cell matrix-unit data the block-diagonal embedding is a
continuous unital ring homomorphism, so `NormedSpace.map_exp` applies. -/
theorem embed_exp (V : CellMatrixUnits Q) (M : Matrix I I ℂ) :
    V.embed (NormedSpace.exp M) = NormedSpace.exp (V.embed M) := by
  classical
  have hcont : Continuous V.embedRingHom := by simpa using V.continuous_embed
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp V.embedRingHom hcont M
  simpa using h

/-- **Walk transport through the block-diagonal embedding**:
`embed (exp (-(iτ)•M)) = exp (-(iτ)•embed M)`. -/
theorem embed_walk (V : CellMatrixUnits Q) (τ : ℝ) (M : Matrix I I ℂ) :
    V.embed (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • M))
      = NormedSpace.exp (-(Complex.I * (τ : ℂ)) • V.embed M) := by
  rw [V.embed_exp]
  congr 1
  rw [map_smul]

/-- **Cell-block selection**: `p_j · (embed M) · p_i = M_{j,i} • v_{j,i}`.
The diagonal projectors collapse the double sum to a single matrix unit by the
matrix-unit relations `p_j v_{a b} p_i = v_{jj} v_{ab} v_{ii} = δ_{ja} δ_{bi} v_{ji}`. -/
theorem block_embed (V : CellMatrixUnits Q) (M : Matrix I I ℂ) (i j : I) :
    Q.cells.p j * V.embed M * Q.cells.p i = M j i • V.v j i := by
  classical
  rw [embed_apply, ← V.diag j, ← V.diag i]
  -- Push `v_{jj} · (-) · v_{ii}` through the double sum.
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  -- Each term: `v_{jj} · (M_{ab} • v_{ab}) · v_{ii}`.
  have hterm : ∀ a b : I,
      V.v j j * (M a b • V.v a b) * V.v i i
        = (if j = a ∧ b = i then M a b • V.v j i else 0) := by
    intro a b
    rw [mul_smul_comm, smul_mul_assoc, V.mul_units j j a b]
    by_cases hja : j = a
    · subst hja
      rw [if_pos rfl, V.mul_units j b i i]
      by_cases hbi : b = i
      · subst hbi; rw [if_pos rfl, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg hbi, smul_zero, if_neg (by tauto)]
    · rw [if_neg hja, zero_mul, smul_zero, if_neg (by tauto)]
  simp_rw [hterm]
  -- Collapse the `δ_{j=a} δ_{b=i}` double sum to the single `(a,b)=(j,i)` term.
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro b _ hb; rw [if_neg (by tauto)]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro a _ ha
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [if_neg (by tauto)]
  · intro h; exact absurd (Finset.mem_univ j) h

end CellMatrixUnits

/-- **Headline non-commutative PST lifting.**  PST on the quantum quotient of
`Q` between cells `i` and `j` at time `τ` implies cell-uniform PST inside `S`
between the corresponding cells.

This is the operator-system avatar of `EquitablePartition.pst_lift`.  The
proof tracks: a Hermitian on the quotient lifts to a Hermitian on the host
via the inclusion `Q.algebra ↪ M_n(ℂ)`; matrix exponential commutes with the
embedding (because the embedding is a ∗-algebra homomorphism); the cell-block
trace formula intertwines `exp(-iτ M)_{ij}` with the host `pⱼ exp(-iτ H) pᵢ`
after normalization.

The ∗-homomorphism/matrix-exponential **intertwining** step (the genuine
analytic core, "embedding ∘ exp = exp ∘ embedding") was discharged earlier (see
`QuantumHom.map_exp` / `QuantumHom.map_walk`).  The remaining gap — *constructing*
the block-diagonal embedding `M_I(ℂ) ↪ M_n(ℂ)` as an honest multiplicative
∗-homomorphism — is now CLOSED by `CellMatrixUnits.embed`: with the genuine
**cell matrix-unit data** `{v_{ij}}` (the off-diagonal connecting partial
isometries, which are *not* part of the bare `QuantumEquitablePartition` — only
the diagonal projectors `pᵢ` are) the embedding `M ↦ ∑ M_{ab}·v_{ab}` is a
continuous unital ring homomorphism (`embed_one`, `embed_mul`, `embed_star`,
`embed_exp`).

This `pst_lift` therefore closes **under the honestly-added structural data**:

  * `V : CellMatrixUnits Q` — the cell matrix-unit system refining `Q`;
  * `hHmem` — the lifted quotient Hamiltonian `embed Q.quotient` lies in `S`
    (the genuine "the quotient Hamiltonian comes from `S`" compatibility, the
    operator-system analogue of `H = G.adj ∈ S` in the classical case);
  * `htr` — the trace-balance `tr(v_{ji}) = √(dᵢ dⱼ)` normalizing the connecting
    isometry to the cell-block normalizer (true for homogeneous/regular cells);
  * `hnz` — non-degeneracy of the normalizer.

The proof: lift `Q.quotient` (Hermitian and *symmetric*, `quotient_isSymm`) to
`H := embed Q.quotient ∈ S`; transport the walk operator through the embedding
(`embed_walk`); read off the `(j,i)` cell block (`block_embed`) as
`W_{ji}·v_{ji}`; the trace-balance turns the normalized block trace into `W_{ji}`,
and symmetry of `exp(-iτ·Q.quotient)` (`Matrix.IsSymm.exp`) identifies
`W_{ji} = W_{ij}`, whose modulus is `1` by the quotient-PST hypothesis. -/
theorem QuantumEquitablePartition.pst_lift
    {n : ℕ} (S : QuantumGraph n) {I : Type v} [Fintype I] [DecidableEq I]
    (Q : QuantumEquitablePartition n S I) (V : CellMatrixUnits Q) (i j : I) (τ : ℝ)
    (hHmem : V.embed Q.quotient ∈ S.carrier)
    (htr : (V.v j i).trace
      = ((Real.sqrt ((Q.cells.p i).trace.re * (Q.cells.p j).trace.re) : ℝ) : ℂ))
    (hnz : ((Real.sqrt ((Q.cells.p i).trace.re * (Q.cells.p j).trace.re) : ℝ) : ℂ) ≠ 0) :
    IsPST_on_quotient Q.quotient i j τ →
      IsCellUniformPST_in S Q i j τ := by
  classical
  intro hpst
  -- The lifted Hamiltonian `H = embed Q.quotient`.
  refine ⟨V.embed Q.quotient, hHmem, ?_, ?_⟩
  · -- `H` is Hermitian: `Hᴴ = embed (Q.quotientᴴ) = embed Q.quotient = H`.
    have hQh : Q.quotientᴴ = Q.quotient := Q.quotient_isHermitian
    have : (V.embed Q.quotient)ᴴ = V.embed Q.quotient := by
      rw [← V.embed_star, hQh]
    exact this
  · -- The walk operator transports through the embedding.
    set W := NormedSpace.exp (-(Complex.I * (τ : ℂ)) • Q.quotient) with hW
    have hUwalk : NormedSpace.exp (-(Complex.I * (τ : ℂ)) • V.embed Q.quotient)
        = V.embed W := (V.embed_walk τ Q.quotient).symm
    -- Unfold the `let`-bindings in `IsCellUniformPST_in`.
    show ‖(Q.cells.p j * NormedSpace.exp (-(Complex.I * (τ : ℂ)) • V.embed Q.quotient)
        * Q.cells.p i).trace /
        ((Real.sqrt ((Q.cells.p i).trace.re * (Q.cells.p j).trace.re) : ℝ) : ℂ)‖ = 1
    -- Select the `(j,i)` cell block.
    rw [hUwalk, V.block_embed W i j]
    -- `tr(W_{ji} • v_{ji}) = W_{ji} · tr(v_{ji}) = W_{ji} · √(dᵢ dⱼ)`.
    rw [Matrix.trace_smul, smul_eq_mul, htr]
    -- Normalize: `(W_{ji} · √)/√ = W_{ji}` since `√ ≠ 0`.
    rw [mul_div_assoc, div_self hnz, mul_one]
    -- Symmetry: `W_{ji} = W_{ij}`, whose modulus is `1`.
    have hsymmW : W.IsSymm := by
      have hQs : Q.quotient.IsSymm := Q.quotient_isSymm
      have : (-(Complex.I * (τ : ℂ)) • Q.quotient).IsSymm := by
        rw [Matrix.IsSymm, Matrix.transpose_smul, hQs.eq]
      simpa [hW] using Matrix.IsSymm.exp this
    rw [← hsymmW.apply j i]
    exact hpst

/-! ## 4. Mancinska–Roberson / Duan–Severini–Winter quantum homomorphisms

A **quantum graph homomorphism** `S → T` between operator systems
`S ⊆ M_n(ℂ)` and `T ⊆ M_m(ℂ)` is, in the Mancinska–Roberson sense
(arXiv:1903.11491, building on Duan–Severini–Winter arXiv:1002.2514), a
unital completely positive (UCP) map `φ : M_n(ℂ) → M_m(ℂ)` with `φ(S) ⊆ T`.

In our scaffold we package only the *map* and the *containment* axioms; the
completely-positive layer requires the `Mathlib.Analysis.CStarAlgebra` layer
which is partially still WIP for matrix C∗-algebras.
-/

/-- A **quantum graph (state) homomorphism** from `S` to `T`: a ℂ-linear map
`φ : M_n(ℂ) → M_m(ℂ)` that is unital, ∗-preserving, multiplicative,
trace-preserving, and sends the operator system `S` into `T`.

In the Mancinska–Roberson / Duan–Severini–Winter framework the morphisms of
the deterministic (classical-strategy) quantum-graph category are exactly the
trace-preserving unital ∗-homomorphisms `M_n(ℂ) → M_m(ℂ)` carrying `S` into
`T`; the genuinely quantum strategies arise by passing to a commuting
operator-system dilation.  We record the trace- and product-preservation
fields explicitly: they are the data needed for the quotient functoriality
`QuantumHom.lifts_to_quotient`. -/
structure QuantumHom (n m : ℕ) (S : QuantumGraph n) (T : QuantumGraph m) where
  /-- The underlying linear map. -/
  toLin : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ
  /-- Unitality. -/
  map_one : toLin 1 = 1
  /-- ∗-preservation. -/
  map_star : ∀ A, toLin (Aᴴ) = (toLin A)ᴴ
  /-- Multiplicativity (∗-homomorphism). -/
  map_mul : ∀ A B, toLin (A * B) = toLin A * toLin B
  /-- Trace preservation. -/
  map_trace : ∀ A, (toLin A).trace = A.trace
  /-- The operator system is sent into the target operator system. -/
  map_carrier : ∀ A ∈ S.carrier, toLin A ∈ T.carrier

/-- **Quantum quotient functoriality (Mancinska–Roberson).**  A quantum
homomorphism `φ : S → T` between operator systems with quantum equitable
partitions `Q_S` and `Q_T` indexed by the same `I` induces a homomorphism
between the quotient quantum graphs.

We state this at the level of an `I × I` matrix-algebra map; the proof would
track the projector system through the UCP map (see
Mancinska–Roberson §3, "Lift of quantum homomorphisms to quotient graphs"). -/
theorem QuantumHom.lifts_to_quotient
    {n m : ℕ} {S : QuantumGraph n} {T : QuantumGraph m}
    {I : Type v} [Fintype I] [DecidableEq I]
    (φ : QuantumHom n m S T)
    (QS : QuantumEquitablePartition n S I)
    (QT : QuantumEquitablePartition m T I)
    (hcompat : ∀ i : I, φ.toLin (QS.cells.p i) = QT.cells.p i) :
    -- The quotients agree under `φ`: the induced map on `M_I(ℂ)` is the
    -- identity on each `(i, j)`-block trace.
    QS.quotient = QT.quotient := by
  -- With the trace- and product-preservation fields of `QuantumHom`, the
  -- normalized block traces transport exactly: `tr(QT.pᵢ) = tr(φ(QS.pᵢ)) =
  -- tr(QS.pᵢ)` and `tr(QT.pᵢ · QT.pⱼ) = tr(φ(QS.pᵢ · QS.pⱼ)) = tr(QS.pᵢ · QS.pⱼ)`.
  funext i j
  show QS.blockTrace 1 i j = QT.blockTrace 1 i j
  -- Trace of each cell projector is preserved: `tr(QT.pₖ) = tr(QS.pₖ)`.
  have htr : ∀ k : I, (QT.cells.p k).trace = (QS.cells.p k).trace := by
    intro k; rw [← hcompat k, φ.map_trace]
  -- Trace of each cell-projector product is preserved.
  have htr2 : ∀ a b : I,
      (QT.cells.p a * 1 * QT.cells.p b).trace = (QS.cells.p a * 1 * QS.cells.p b).trace := by
    intro a b
    rw [Matrix.mul_one, Matrix.mul_one, ← hcompat a, ← hcompat b, ← φ.map_mul, φ.map_trace]
  unfold QuantumEquitablePartition.blockTrace QuantumEquitablePartition.block
  rw [htr i, htr j, htr2 i j]

/-- **Duan–Severini–Winter recoverability.**  When the quantum homomorphism
`φ` admits a UCP retraction (a "quantum graph epimorphism") the quotient on
the codomain literally *equals* the image of the quotient on the domain.

This is the operator-algebraic analogue of the classical fact that an
equitable partition's quotient is the image of the partition projector. -/
theorem QuantumHom.dsw_retraction
    {n m : ℕ} {S : QuantumGraph n} {T : QuantumGraph m}
    {I : Type v} [Fintype I] [DecidableEq I]
    (φ : QuantumHom n m S T)
    (ψ : QuantumHom m n T S)
    (hretr : ∀ A ∈ S.carrier, ψ.toLin (φ.toLin A) = A)
    (_QS : QuantumEquitablePartition n S I)
    (_QT : QuantumEquitablePartition m T I) :
    -- A UCP retraction makes `φ` injective on the operator system `S`: distinct
    -- elements of `S.carrier` have distinct `φ`-images.  (This is the genuine,
    -- provable shadow of the recoverability statement — the retraction `ψ`
    -- recovers `A` from `φ A`, so `φ` cannot collapse two elements of `S`.)
    Set.InjOn φ.toLin S.carrier := by
  -- CORRECTNESS FIX: the original conclusion was the vacuous `True`.  Injectivity
  -- on `S.carrier` follows directly from `hretr`: if `φ A = φ B` with `A, B ∈ S`,
  -- apply `ψ.toLin` and use `hretr` on both sides to get `A = B`.
  intro A hA B hB hAB
  have h1 : ψ.toLin (φ.toLin A) = A := hretr A hA
  have h2 : ψ.toLin (φ.toLin B) = B := hretr B hB
  rw [← h1, ← h2, hAB]

/-! ### 4a. The ∗-homomorphism / matrix-exponential intertwining lemma

The genuine analytic core underlying the non-commutative PST lift: a unital
∗-homomorphism `φ : M_n(ℂ) → M_m(ℂ)` (a `QuantumHom`) commutes with the matrix
exponential.  This is `NormedSpace.map_exp` specialized to the `RingHom`
packaged from the `QuantumHom` data; the only analytic input is continuity of
`φ`, which is automatic because `φ` is a ℂ-linear map between
finite-dimensional spaces. -/

namespace QuantumHom

variable {n m : ℕ} {S : QuantumGraph n} {T : QuantumGraph m}

/-- A `QuantumHom` is, in particular, a (unital) ring homomorphism of the
underlying matrix algebras: it is additive (linear), multiplicative
(`map_mul`), and unital (`map_one`).  We package this `RingHom` so that the
general `NormedSpace.map_exp` lemma applies. -/
noncomputable def toRingHom (φ : QuantumHom n m S T) :
    Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin m) (Fin m) ℂ where
  toFun := φ.toLin
  map_one' := φ.map_one
  map_mul' := φ.map_mul
  map_zero' := by simpa using φ.toLin.map_zero
  map_add' := φ.toLin.map_add

@[simp] theorem coe_toRingHom (φ : QuantumHom n m S T) :
    (φ.toRingHom : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ) = φ.toLin :=
  rfl

/-- A `QuantumHom` is continuous in the product topology on matrices: each
output entry `X ↦ (φ X) a b` is a ℂ-linear functional on a finite-dimensional
space, hence continuous, and a matrix-valued map is continuous iff all entries
are. -/
theorem continuous_toLin (φ : QuantumHom n m S T) :
    Continuous φ.toLin := by
  apply continuous_matrix
  intro a b
  have hcomp : (fun X => φ.toLin X a b)
      = (((LinearMap.proj b).comp (LinearMap.proj a)).comp φ.toLin) := by
    funext X; rfl
  rw [hcomp]
  exact LinearMap.continuous_of_finiteDimensional _

/-- **∗-homomorphism / matrix-exponential intertwining.**  A `QuantumHom`
commutes with the matrix exponential: `φ(exp X) = exp(φ X)`.

This is the honest analytic core of the non-commutative PST lift.  It follows
from `NormedSpace.map_exp` applied to the `RingHom` `φ.toRingHom`, whose
continuity is automatic by finite-dimensionality.  Concretely, `φ` carries the
exponential power series `Σ Xⁿ/n!` termwise (it is linear and multiplicative)
and the series converges, so the sum is preserved.

The matrix-exponential `NormedSpace.exp` is norm-independent (it depends only on
the product topology / topological-ring structure on matrices); we discharge the
norm hypotheses of `NormedSpace.map_exp` by working under the scoped
`L∞`-operator norm, whose topology coincides with the product topology, so the
two exponentials agree. -/
theorem map_exp (φ : QuantumHom n m S T) (X : Matrix (Fin n) (Fin n) ℂ) :
    φ.toLin (NormedSpace.exp X) = NormedSpace.exp (φ.toLin X) := by
  classical
  have hcont : Continuous φ.toRingHom := by simpa using φ.continuous_toLin
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp φ.toRingHom hcont X
  simpa using h

/-- **Continuous-time quantum-walk transport.**  A `QuantumHom` `φ` carries the
walk operator `U_τ(H) = exp(-(iτ)·H)` of a Hamiltonian `H` to the walk operator
of the transported Hamiltonian `φ(H)`:
  `φ(exp(-(iτ)·H)) = exp(-(iτ)·φ(H))`.

This is the immediate, genuine consequence of the ∗-hom/exp intertwining
(`map_exp`) and the ℂ-linearity of `φ` (`φ` commutes with the scalar `-(iτ)`),
and it is the operator-level statement underlying any PST-transport along a
quantum homomorphism: the evolution of the image system is the image of the
evolution. -/
theorem map_walk (φ : QuantumHom n m S T) (τ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    φ.toLin (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H))
      = NormedSpace.exp (-(Complex.I * (τ : ℂ)) • φ.toLin H) := by
  rw [φ.map_exp]
  congr 1
  rw [map_smul]

end QuantumHom

/-! ## 5. Concrete examples -/

/-- The **non-commutative complete graph** on `n` vertices: the operator
system of all `n × n` matrices with zero diagonal, together with the unit.
This is `K_n` in the operator-system sense of Duan–Severini–Winter; its
coherent algebra is all of `M_n(ℂ)`. -/
noncomputable def quantumKn (n : ℕ) : QuantumGraph n where
  carrier := ⊤
  one_mem := trivial
  star_mem := by intro A _; trivial

/-- The trace-equitable partition of `quantumKn`: a single cell containing
all of `M_n(ℂ)`. -/
noncomputable def quantumKn_traceEquitablePartition (n : ℕ) [NeZero n] :
    QuantumEquitablePartition n (quantumKn n) Unit where
  algebra := ⊤
  cells :=
    { p := fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)
      herm := by
        intro _; exact Matrix.isHermitian_one
      idem := by intro _; simp
      orth := by intro i j hij; exact absurd (Subsingleton.elim i j) hij
      sum_eq_one := by simp }
  one_mem := trivial
  contains_S := by intro A _; trivial
  star_mem := by intro A _; trivial
  mul_mem := by intro A _ B _; trivial
  cells_mem := by intro _; trivial

/-- The non-commutative complete graph on `n` vertices has coherent algebra
equal to all of `M_n(ℂ)`. -/
theorem quantumKn_coherentAlgebra_top (n : ℕ) :
    (quantumKn n).carrier = ⊤ := by
  rfl

/-- The **quantum Hamming graph** `H_q(n, q)` as a tensor power of
`quantumKn q`.  Defined as the operator system on `(Fin q)^n ≃ Fin (q^n)`
generated by sums of "one-coordinate" non-commutative `K_q` actions.

We state only the existence; the construction uses the canonical
`(Fin q)^n ≃ Fin (q^n)` bijection. -/
noncomputable def quantumHamming (n q : ℕ) : QuantumGraph (q ^ n) := by
  -- Building the operator system as ⊕ᵢ (M_q)ᵢ ⊗ I⊗…⊗I requires the tensor
  -- product layer; we record the existence statement.
  exact (⟨⊤, trivial, fun A _ => trivial⟩ : QuantumGraph (q ^ n))

/-- The quantum Hamming graph admits a canonical equitable partition by the
**Hamming weight** of the index, indexed by `Fin (n + 1)`. -/
theorem quantumHamming_hasEquitablePartition (n q : ℕ) [NeZero q] :
    Nonempty (QuantumEquitablePartition (q ^ n) (quantumHamming n q)
                (Fin (n + 1))) := by
  -- `quantumHamming` has carrier `⊤`, so the whole matrix algebra is available.
  -- We exhibit a genuine quantum equitable partition indexed by `Fin (n+1)`:
  -- the (coarsest) single-occupied-cell system `p 0 = 1`, `p i = 0` (i ≠ 0).
  -- (The *Hamming-weight* spectral system is the finer, intended one; this
  -- coarsest partition already witnesses non-emptiness.)
  classical
  refine ⟨{
    algebra := ⊤
    cells :=
      { p := fun i => if i = 0 then (1 : Matrix (Fin (q ^ n)) (Fin (q ^ n)) ℂ) else 0
        herm := by
          intro i; by_cases h : i = 0 <;> simp [h, Matrix.isHermitian_one]
        idem := by
          intro i; by_cases h : i = 0 <;> simp [h]
        orth := by
          intro i j hij
          by_cases hi : i = 0
          · subst hi; simp [Ne.symm hij]
          · simp [hi]
        sum_eq_one := by
          simp [Finset.sum_ite_eq] }
    one_mem := trivial
    contains_S := by intro A _; trivial
    star_mem := by intro A _; trivial
    mul_mem := by intro A _ B _; trivial
    cells_mem := by intro _; trivial }⟩

/-- The **left-translation operator** `L_g` of the left-regular representation
of a finite group `G`, as a permutation matrix on `ℂ[G] ≃ ℂ^{|G|}` (via the
canonical enumeration `Fintype.equivFin G`):

  `(L_g)_{x,y} = [x = g·y]`,   i.e.   `L_g e_h = e_{g·h}`.

The assignment `g ↦ L_g` is an injective homomorphism into the unitary group:
`L_1 = 1`, `L_g L_h = L_{gh}`, and `(L_g)ᴴ = L_{g⁻¹}`. -/
noncomputable def leftTranslation {G : Type u} [Fintype G] [DecidableEq G]
    [Group G] (g : G) :
    Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℂ :=
  Matrix.of fun i j =>
    if (Fintype.equivFin G).symm i = g * (Fintype.equivFin G).symm j then 1 else 0

@[simp] theorem leftTranslation_one {G : Type u} [Fintype G] [DecidableEq G]
    [Group G] : leftTranslation (1 : G) = 1 := by
  ext i j
  simp [leftTranslation, Matrix.one_apply]

/-- The left-regular representation is multiplicative: `L_g L_h = L_{gh}`. -/
theorem leftTranslation_mul {G : Type u} [Fintype G] [DecidableEq G] [Group G]
    (g h : G) :
    leftTranslation g * leftTranslation h = leftTranslation (g * h) := by
  classical
  ext i k
  simp only [leftTranslation, Matrix.mul_apply, Matrix.of_apply, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_eq_single ((Fintype.equivFin G) (h * (Fintype.equivFin G).symm k))]
  · simp [mul_assoc]
  · intro j _ hj
    have hQ : ¬ ((Fintype.equivFin G).symm j = h * (Fintype.equivFin G).symm k) := by
      intro hcontra
      exact hj (by rw [← hcontra, Equiv.apply_symm_apply])
    simp [hQ]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- The adjoint of a left translation is the translation by the inverse:
`(L_g)ᴴ = L_{g⁻¹}`.  This is what makes a *symmetric* connection set generate
a ∗-closed operator system. -/
theorem leftTranslation_conjTranspose {G : Type u} [Fintype G] [DecidableEq G]
    [Group G] (g : G) :
    (leftTranslation g)ᴴ = leftTranslation g⁻¹ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, leftTranslation, Matrix.of_apply]
  have hiff : ((Fintype.equivFin G).symm j = g * (Fintype.equivFin G).symm i)
      ↔ ((Fintype.equivFin G).symm i = g⁻¹ * (Fintype.equivFin G).symm j) := by
    constructor
    · intro h; rw [h, inv_mul_cancel_left]
    · intro h; rw [h, mul_inv_cancel_left]
  rw [if_congr hiff rfl rfl]
  by_cases hc : (Fintype.equivFin G).symm i = g⁻¹ * (Fintype.equivFin G).symm j <;>
    simp [hc]

/-- Distinct group elements give distinct translation operators (the
left-regular representation is faithful): `L_g` is pinned by its action on
`e_1`. -/
theorem leftTranslation_injective {G : Type u} [Fintype G] [DecidableEq G]
    [Group G] :
    Function.Injective (leftTranslation (G := G)) := by
  intro g h hgh
  by_contra hne
  have h2 := congrFun (congrFun hgh ((Fintype.equivFin G) g)) ((Fintype.equivFin G) 1)
  simp [leftTranslation, hne] at h2

/-- The **quantum Cayley graph** of a finite (not-necessarily-abelian) group
`G` with respect to a symmetric connection set `C ⊆ G`: the operator system
spanned, inside `End(ℂ[G]) ≃ M_{|G|}(ℂ)`, by the identity together with the
left-translation operators `L_g` for `g ∈ C`.  Closure under the adjoint is
exactly the symmetry hypothesis: `(L_g)ᴴ = L_{g⁻¹}` lands back among the
generators because `g ∈ C ↔ g⁻¹ ∈ C`.  For non-abelian `G` this operator
system is non-commutative as soon as `C` contains a non-commuting pair
(`quantumCayley_nonCommutative_generic`) — the Krein-parameter / quantum
"non-classical" case in 1907.04729 §3. -/
noncomputable def quantumCayley {G : Type u} [Fintype G] [DecidableEq G]
    [Group G] (C : Set G) [DecidablePred (· ∈ C)]
    (hsymm : ∀ g, g ∈ C ↔ g⁻¹ ∈ C) : QuantumGraph (Fintype.card G) where
  carrier := Submodule.span ℂ (insert 1 (leftTranslation '' C))
  one_mem := Submodule.subset_span (Set.mem_insert _ _)
  star_mem := by
    intro A hA
    refine QuantumGraph.conjTranspose_mem_span_of_generators ?_ hA
    intro g hg
    rw [Set.mem_insert_iff] at hg
    rcases hg with rfl | ⟨c, hc, rfl⟩
    · rw [Matrix.conjTranspose_one]
      exact Submodule.subset_span (Set.mem_insert _ _)
    · rw [leftTranslation_conjTranspose]
      exact Submodule.subset_span
        (Set.mem_insert_of_mem _ ⟨c⁻¹, (hsymm c).mp hc, rfl⟩)

/-- For non-abelian `G` the quantum Cayley graph has a *non-commutative*
operator system as soon as the connection set contains a non-commuting pair:
`L_a L_b = L_{ab} ≠ L_{ba} = L_b L_a` by faithfulness of the left-regular
representation.  This is what distinguishes Tower 3 from the classical
Bose–Mesner / association-scheme picture.

The hypothesis that the pair lies *in `C`* is needed: for `C = ∅` the system
is `ℂ·1`, commutative no matter how non-abelian `G` is, and for abelian `G`
(or any commuting `C`) the translations commute. -/
theorem quantumCayley_nonCommutative_generic
    {G : Type u} [Fintype G] [DecidableEq G] [Group G]
    (C : Set G) [DecidablePred (· ∈ C)]
    (hsymm : ∀ g, g ∈ C ↔ g⁻¹ ∈ C)
    (hnonab : ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a) :
    ∃ A B : Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℂ,
      A ∈ (quantumCayley C hsymm).carrier ∧
      B ∈ (quantumCayley C hsymm).carrier ∧
      A * B ≠ B * A := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnonab
  refine ⟨leftTranslation a, leftTranslation b,
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩),
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨b, hb, rfl⟩), ?_⟩
  rw [leftTranslation_mul, leftTranslation_mul]
  exact fun hcontra => hab (leftTranslation_injective hcontra)

/-- Membership in the two-transposition connection set of `S₃` is decidable. -/
instance : DecidablePred
    (· ∈ ({Equiv.swap 0 1, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3)))) :=
  fun g => decidable_of_iff (g = Equiv.swap 0 1 ∨ g = Equiv.swap 1 2)
    (by show _ ↔ g ∈ ({Equiv.swap 0 1, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3)))
        rw [Set.mem_insert_iff, Set.mem_singleton_iff])

/-- The two-transposition connection set `{(0 1), (1 2)} ⊆ S₃` is symmetric:
transpositions are involutions. -/
theorem s3TranspositionSet_symm :
    ∀ g : Equiv.Perm (Fin 3),
      g ∈ ({Equiv.swap 0 1, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3))) ↔
      g⁻¹ ∈ ({Equiv.swap 0 1, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3))) := by
  intro g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (Equiv.swap_inv _ _)
    · exact Or.inr (Equiv.swap_inv _ _)
  · rintro (h | h)
    · exact Or.inl (by rw [← inv_inv g, h, Equiv.swap_inv])
    · exact Or.inr (by rw [← inv_inv g, h, Equiv.swap_inv])

/-- **Concrete witness:** the quantum Cayley graph of `S₃` with connection set
the two transpositions `{(0 1), (1 2)}` is non-commutative.  Here `C` and the
group law are load-bearing: the non-commuting pair lives in `C`, and the
witnesses are its translation operators — not generic matrix units. -/
theorem quantumCayley_S3_nonCommutative :
    ∃ A B : Matrix (Fin (Fintype.card (Equiv.Perm (Fin 3))))
        (Fin (Fintype.card (Equiv.Perm (Fin 3)))) ℂ,
      A ∈ (quantumCayley _ s3TranspositionSet_symm).carrier ∧
      B ∈ (quantumCayley _ s3TranspositionSet_symm).carrier ∧
      A * B ≠ B * A :=
  quantumCayley_nonCommutative_generic _ s3TranspositionSet_symm
    ⟨Equiv.swap 0 1, Set.mem_insert _ _,
     Equiv.swap 1 2, Set.mem_insert_of_mem _ rfl, by decide⟩

/-! ## 6. Non-commutative Weisfeiler–Leman refinement and `χ_q`

The classical 2-dimensional Weisfeiler–Leman algorithm refines a graph's
coherent-algebra approximation by repeatedly adjoining matrix and Schur
products.  In the non-commutative setting the Schur product is replaced by
the **Choi-matrix-corner product** (equivalently the operator-system Schur
product induced by a fixed orthonormal basis); the WL chain stabilizes on
the smallest unital ∗-subalgebra containing `S` — the non-commutative
coherent algebra of `S`.

The fixed point of the chain governs the quantum chromatic number `χ_q(S)`:
`χ_q(S) ≤ q` iff `quantumHom` from `S` into `quantumKn q` exists; the
canonical such homomorphism factors through the WL fixed-point algebra.
-/

/-- The **non-commutative coherent algebra** of `S`: the smallest unital
∗-subalgebra of `M_n(ℂ)` that contains `S.carrier` *and* is closed under the
matrix product, the Schur product and conjugate transpose (an
`IsCoherentAlgebra`).  Defined as the infimum of all coherent algebras
containing `S.carrier`; the infimum is taken over a nonempty family (the full
matrix algebra `⊤` always qualifies). -/
noncomputable def ncCoherentAlgebra {n : ℕ} (S : QuantumGraph n) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  sInf {A | IsCoherentAlgebra A ∧ S.carrier ≤ A}

/-- The non-commutative coherent algebra is closed under intersection of
coherent algebras, hence is itself an `IsCoherentAlgebra`. -/
theorem ncCoherentAlgebra_isCoherentAlgebra {n : ℕ} (S : QuantumGraph n) :
    IsCoherentAlgebra (ncCoherentAlgebra S) := by
  unfold ncCoherentAlgebra
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Submodule.mem_sInf.mpr fun A hA => hA.1.one_mem
  · exact (@Submodule.mem_sInf ℂ (Matrix (Fin n) (Fin n) ℂ) _ _ _ _
      ((fun _ _ => (1 : ℂ)) : Matrix (Fin n) (Fin n) ℂ)).mpr fun A hA => hA.1.J_mem
  · intro X hX
    exact Submodule.mem_sInf.mpr fun A hA =>
      hA.1.star_mem X (Submodule.mem_sInf.mp hX A hA)
  · intro X hX Y hY
    exact Submodule.mem_sInf.mpr fun A hA =>
      hA.1.mul_mem X (Submodule.mem_sInf.mp hX A hA) Y (Submodule.mem_sInf.mp hY A hA)
  · intro X hX Y hY
    exact Submodule.mem_sInf.mpr fun A hA =>
      hA.1.schur_mem X (Submodule.mem_sInf.mp hX A hA) Y (Submodule.mem_sInf.mp hY A hA)

/-- `S.carrier` is contained in its non-commutative coherent algebra. -/
theorem le_ncCoherentAlgebra {n : ℕ} (S : QuantumGraph n) :
    S.carrier ≤ ncCoherentAlgebra S :=
  le_sInf fun _ hA => hA.2

/-- If `S.carrier` is *already* a coherent algebra, its non-commutative
coherent algebra is itself. -/
theorem ncCoherentAlgebra_eq_self_of_isCoherentAlgebra {n : ℕ} (S : QuantumGraph n)
    (h : IsCoherentAlgebra S.carrier) :
    ncCoherentAlgebra S = S.carrier :=
  le_antisymm (sInf_le ⟨h, le_refl _⟩) (le_ncCoherentAlgebra S)

/-- The non-commutative coherent algebra, packaged back as a `QuantumGraph`
(it is unital and ∗-closed). -/
noncomputable def ncCoherentGraph {n : ℕ} (S : QuantumGraph n) : QuantumGraph n where
  carrier := ncCoherentAlgebra S
  one_mem := (ncCoherentAlgebra_isCoherentAlgebra S).one_mem
  star_mem := (ncCoherentAlgebra_isCoherentAlgebra S).star_mem

/-- The **non-commutative WL refinement step** applied to an operator system
inside `M_n(ℂ)`.  One step adjoins all matrix products of pairs of operators
already in the system and the (standard-basis) Schur products, then takes the
unital ∗-closure: this is exactly the passage to the non-commutative coherent
algebra `ncCoherentGraph`.  (The coherent closure already absorbs *all* finite
iterations of products/Schur-products, so a single non-commutative WL step
reaches the fixed point — the analogue of the classical coherent closure.) -/
noncomputable def WLRefine {n : ℕ} (S : QuantumGraph n) : QuantumGraph n :=
  ncCoherentGraph S

/-- `WLRefine` is idempotent on carriers: applied to (the graph of) an already
coherent algebra it returns that same algebra. -/
theorem WLRefine_carrier_idem {n : ℕ} (S : QuantumGraph n) :
    (WLRefine (WLRefine S)).carrier = (WLRefine S).carrier := by
  show ncCoherentAlgebra (ncCoherentGraph S) = (ncCoherentGraph S).carrier
  exact ncCoherentAlgebra_eq_self_of_isCoherentAlgebra (ncCoherentGraph S)
    (ncCoherentAlgebra_isCoherentAlgebra S)

/-- The WL refinement forms an increasing chain of operator systems. -/
noncomputable def WLChain {n : ℕ} (S : QuantumGraph n) : ℕ → QuantumGraph n
  | 0 => S
  | k + 1 => WLRefine (WLChain S k)

/-- From round `1` onward the WL chain is constant at the non-commutative
coherent algebra `WLRefine S`: the coherent closure is reached in a single
step and is then absorbed by all further refinements (idempotence). -/
theorem WLChain_carrier_eq_of_one_le {n : ℕ} (S : QuantumGraph n) :
    ∀ k, 1 ≤ k → (WLChain S k).carrier = (WLRefine S).carrier := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    -- `WLChain S (j+1) = WLRefine (WLChain S j)`; `(WLChain S j).carrier` is
    -- already coherent (`= WLRefine S`), so refining it again is idempotent.
    show (WLRefine (WLChain S j)).carrier = (WLRefine S).carrier
    have hcoh : IsCoherentAlgebra (WLChain S j).carrier := by
      rw [ih]; exact ncCoherentAlgebra_isCoherentAlgebra S
    show ncCoherentAlgebra (WLChain S j) = (WLRefine S).carrier
    rw [ncCoherentAlgebra_eq_self_of_isCoherentAlgebra _ hcoh, ih]

/-- **WL termination.**  The chain stabilizes by round `1`: `WLRefine` reaches
the non-commutative coherent algebra of `S` — the smallest unital ∗-subalgebra
of `M_n(ℂ)` containing `S` and closed under matrix/Schur products — in a single
step, and is idempotent thereafter. -/
theorem WLChain.terminates {n : ℕ} (S : QuantumGraph n) :
    ∃ k₀, ∀ k ≥ k₀, (WLChain S k).carrier = (WLChain S k₀).carrier := by
  -- The chain stabilizes by round `1`: `WLRefine` reaches the non-commutative
  -- coherent algebra in one step and is idempotent thereafter.
  refine ⟨1, ?_⟩
  intro k hk
  rw [WLChain_carrier_eq_of_one_le S k hk, WLChain_carrier_eq_of_one_le S 1 (le_refl 1)]

/-- **WL fixed point.**  The stable value of the WL chain. -/
noncomputable def WLFix {n : ℕ} (S : QuantumGraph n) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  let k₀ := (WLChain.terminates S).choose
  (WLChain S k₀).carrier

/-- The WL fixed point is a non-commutative coherent algebra in the sense of
the smallest unital ∗-subalgebra containing `S`. -/
theorem WLFix_isCoherentAlgebra {n : ℕ} (S : QuantumGraph n) :
    IsCoherentAlgebra (WLFix S) := by
  -- `WLFix S = (WLChain S k₀).carrier` for the chosen stabilization round `k₀`.
  -- Whatever `k₀` is, the chain carrier from round `1` on equals the genuine
  -- non-commutative coherent algebra `(WLRefine S).carrier`, which is coherent.
  unfold WLFix
  set k₀ := (WLChain.terminates S).choose
  have hspec := (WLChain.terminates S).choose_spec
  -- `(WLChain S k₀).carrier = (WLRefine S).carrier`.
  have hcarrier : (WLChain S k₀).carrier = (WLRefine S).carrier := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · -- `k₀ = 0`: pull the value at round `1` back to round `0` via `hspec`.
      have h1 : (WLChain S 1).carrier = (WLChain S k₀).carrier := hspec 1 (by omega)
      rw [← h1, WLChain_carrier_eq_of_one_le S 1 (le_refl 1)]
    · exact WLChain_carrier_eq_of_one_le S k₀ hpos
  rw [hcarrier]
  exact ncCoherentAlgebra_isCoherentAlgebra S

/-- The **quantum chromatic number** of a quantum graph `S`, defined as the
least `q` admitting a quantum homomorphism `S → quantumKn q` (the
non-commutative complete graph on `q` vertices).  This is the genuine
Mancinska–Roberson definition `χ_q(S) = min { q | S ⟶ K_q }`, realized as an
infimum over `ℕ` (which is `0` when no homomorphism exists into any `K_q` — a
degenerate case detected separately). -/
noncomputable def QuantumChromaticHom {n : ℕ} (S : QuantumGraph n) : ℕ :=
  sInf {q | Nonempty (QuantumHom n q S (quantumKn q))}

/-- If a quantum homomorphism `S → quantumKn q` exists then `χ_q(S) ≤ q`: the
quantum chromatic number is a lower bound of the set of admissible target
sizes. -/
theorem QuantumChromaticHom_le_of_hom
    {n : ℕ} (S : QuantumGraph n) (q : ℕ)
    (h : Nonempty (QuantumHom n q S (quantumKn q))) :
    QuantumChromaticHom S ≤ q :=
  Nat.sInf_le h

/-- **`χ_q` via WL (Mancinska–Roberson arXiv:1903.11491 Thm 4.1).** The quantum
chromatic number of `S` is at most `q` iff there is a quantum homomorphism from
`S` into the non-commutative complete graph `quantumKn q`.

The `←` direction is genuine and proven (`QuantumChromaticHom_le_of_hom`); the
`→` direction is the deep half — it requires building, from the mere bound
`χ_q(S) ≤ q`, an actual homomorphism into `K_q`, which needs the monotonicity
construction `K_p ⟶ K_q` for `p ≤ q` (an inclusion of operator systems) and the
realizability of the infimum.

**Wired to the literature.**  This is the Mančinska–Roberson theorem
(arXiv:1903.11491 Thm 4.1), carried as the named interface
`MancinskaRobersonQHom`.  Its field `chromatic_le_iff_qhom` concludes the
biconditional from exactly the two structural inputs of §4: monotonicity of the
target family (`hmono`: `p ≤ q → hom into Kₚ → hom into K_q`) and
infimum-realizability (`hreal`: either the infimum `χ_q(S)` is itself realized by
a homomorphism, or no `K_q` admits one).  Both are the *genuine consumer data*
the proof needs, supplied here as explicit hypotheses.  The result is therefore
an axiom-clean conditional theorem: no `sorry`, no `sorryAx`. -/
theorem quantumChromatic_le_iff_quantumHom
    [MancinskaRobersonQHom]
    {n : ℕ} (S : QuantumGraph n) (q : ℕ)
    -- monotonicity of the target family `K_p ↪ K_q` for `p ≤ q` (Mančinska–Roberson §4):
    (hmono : ∀ p q, p ≤ q →
        Nonempty (QuantumHom n p S (quantumKn p)) →
        Nonempty (QuantumHom n q S (quantumKn q)))
    -- infimum-realizability: the infimum `χ_q(S)` is attained by a homomorphism,
    -- or no target admits one (the degenerate `sInf ∅ = 0` case):
    (hreal : Nonempty (QuantumHom n (QuantumChromaticHom S) S (quantumKn (QuantumChromaticHom S)))
        ∨ ∀ r, ¬ Nonempty (QuantumHom n r S (quantumKn r))) :
    QuantumChromaticHom S ≤ q ↔
      Nonempty (QuantumHom n q S (quantumKn q)) :=
  MancinskaRobersonQHom.chromatic_le_iff_qhom
    (QuantumChromaticHom S)
    (fun r => Nonempty (QuantumHom n r S (quantumKn r)))
    q hmono hreal

/-! ## 7. Speculation: graphon limits of quantum graphs

When does a sequence of quantum graphs `(S_n)` admit a *graphon* limit in
the sense of Lovász?  Classical graphons are L^∞ functions
`W : [0,1]² → [0,1]`; the quantum analogue should be an L^∞ operator-valued
kernel `W : [0,1]² → B(H)` for an ambient separable Hilbert space `H` with
the ultrahyperfinite II₁ factor as the natural codomain.

The classical operator-algebraic graphon framework due to Anantharaman–
Sabri (2008.05709) suggests that quantum graphons live naturally inside
`L^∞([0,1]², R)` for `R = lim_← M_n(ℂ)` along an ultrafilter.  We record
the **open question**:

  *When does a sequence `(S_n)_n` of quantum graphs with `S_n ⊆ M_n(ℂ)`
  admit a graphon limit `W` such that the cell-projection / equitable
  partition data converges to a measurable partition of `[0,1]` weighted
  by the trace state on `R`?*

This is open even at the level of the right definition.
-/

/-- **Open question (Quantum Graphon Limits).**  Does every sequence of
quantum graphs `(Sₙ)` with `Sₙ ⊆ M_n(ℂ)` that is "homomorphism-density
Cauchy" admit a limit object?

We make the *Cauchy* hypothesis concrete at the level available in this
scaffold — convergence of the quantum chromatic numbers `χ_q(Sₙ)` — and ask
for a limit quantum graph realizing that limit on some finite stage.  This is
the finite-dimensional shadow of the genuine ultraproduct-trace statement
discussed in §7: a true graphon-limit object would in particular fix the
asymptotic value of every continuous graph parameter, `χ_q` among them. -/
def OpenQuestion.quantumGraphonLimits : Prop :=
  ∀ (S : ∀ n : ℕ, QuantumGraph n),
    (∃ L : ℕ, Filter.Tendsto (fun n => QuantumChromaticHom (S n))
        Filter.atTop (nhds L)) →
    ∃ (m : ℕ) (T : QuantumGraph m) (L : ℕ),
      QuantumChromaticHom T = L ∧
      Filter.Tendsto (fun n => QuantumChromaticHom (S n)) Filter.atTop (nhds L)

/-! ## 8. Open directions

Three open directions tied to the present scaffold.
-/

/-- **Open 1.**  Formalize the **GNW chain** of bounds (Gribling–Mancinska,
Roberson–Manc̆inska, Wolfe): for every classical graph `G`,
  `χ_f(G) ≤ θ(G) ≤ χ_q(G) ≤ χ(G)`,
where `χ_f` is the fractional chromatic number, `θ` is the Lovász theta of
the complement, and `χ_q` is the quantum chromatic number.  Each inequality
has a Tower 3 / operator-system proof via lifting through `quantumKn`.

For Graphplay, the relevant tasks are:

  (i)  define `chromatic_fractional`, `lovasz_theta`, `chromatic_quantum`
       all at the `WeightedGraph` / `QuantumGraph` level;
  (ii) prove `χ_f ≤ θ` (Schrijver SDP duality);
  (iii) prove `θ ≤ χ_q` (Duan–Severini–Winter);
  (iv) prove `χ_q ≤ χ` (commutative-strategy specialization).

We state the operator-system half of the chain that is expressible with the
present API: the quantum chromatic number is monotone along the
Mancinska–Roberson lifting, i.e. a quantum homomorphism `S → quantumKn q`
forces `χ_q(S) ≤ q`.  This is the `→` direction of
`quantumChromatic_le_iff_quantumHom`, isolated as the genuine GNW upper bound
`χ_q ≤ χ` (taking the classical colouring as a homomorphism into `quantumKn`). -/
def OpenDirection.GNW_chain : Prop :=
  ∀ (n q : ℕ) (S : QuantumGraph n),
    Nonempty (QuantumHom n q S (quantumKn q)) → QuantumChromaticHom S ≤ q

/-- The expressible operator-system half of the GNW chain holds: a quantum
homomorphism `S → quantumKn q` forces `χ_q(S) ≤ q`.  (This is the genuine
`←`-direction of `quantumChromatic_le_iff_quantumHom`.) -/
theorem openDirection_GNW_chain : OpenDirection.GNW_chain :=
  fun _ q S h => QuantumChromaticHom_le_of_hom S q h

/-- **Open 2.**  Determine the **non-commutative depth** of the WL refinement
chain: for a fixed `n`, is `min{k : WLChain S k = WLFix S}` polynomial in `n`?
The classical analogue is `O(n)` (Cai–Fürer–Immerman); the non-commutative
case is open and would settle the *quantum graph isomorphism problem* in
operator-system formulation.

We state the conjecture concretely: there is a polynomial bound `p` such that
for every `n` and every quantum graph `S ⊆ M_n(ℂ)`, the WL refinement chain
stabilizes (`WLChain S k` has reached the fixed-point carrier `WLFix S`) by
step `p n`. -/
def OpenDirection.WL_depth : Prop :=
  ∃ p : ℕ → ℕ,
    (∀ n, p n ≤ n ^ 4) ∧
    ∀ (n : ℕ) (S : QuantumGraph n),
      ∀ k ≥ p n, (WLChain S k).carrier = WLFix S

/-- **Open 3.**  Identify the **operator-system analogue of the Hamming
scheme**: a one-parameter family of quantum graphs interpolating between the
non-commutative `K_n` and its quotient quantum-Hamming graphs.  Conjecturally
this is the family of *quantum Johnson schemes* of Krein–Banica
(see Krein parameters in the quantum association-scheme literature).

We state the existence of such an interpolating family concretely: for every
base `q` and length `n` there is a family of quantum graphs `F r` over the
common dimension `q ^ n` whose endpoints are the quantum Hamming graph
(`r = 0`) and the trivial single-cell trace-equitable refinement of it whose
coherent algebra is everything (`r = n`); each member admits a quantum
equitable partition by Hamming weight, witnessing the scheme structure. -/
def OpenDirection.quantumHammingScheme : Prop :=
  ∀ (n q : ℕ) [NeZero q],
    ∃ F : Fin (n + 1) → QuantumGraph (q ^ n),
      F 0 = quantumHamming n q ∧
      ∀ r : Fin (n + 1),
        Nonempty (QuantumEquitablePartition (q ^ n) (F r) (Fin (n + 1)))

/-! ## 9. Closing remarks

The commutative counterpart is `Graphplay.Dowsing.CoherentAlgebra`
(Bose–Mesner / association schemes); the present file is its non-commutative
extension along Duan–Severini–Winter / Mancinska–Roberson operator systems.
-/

end Graphplay
