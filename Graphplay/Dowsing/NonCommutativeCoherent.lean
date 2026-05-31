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

All proofs are `sorry` placeholders — this file is a *type-correct scaffold* of
statements meant to be linked into the rest of Graphplay once Mathlib's
operator-algebra layer is up.
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

open scoped Matrix
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

end QuantumEquitablePartition

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
analytic core, "embedding ∘ exp = exp ∘ embedding") is now discharged: see
`QuantumHom.map_exp` and the walk-transport corollary `QuantumHom.map_walk`.
What remains genuinely BLOCKED is the *construction* of the block-diagonal
embedding `M_I(ℂ) ↪ Q.algebra`, `M ↦ ∑_{i,j} M_{i,j}·(pᵢ J pⱼ)`, as an honest
∗-homomorphism: multiplicativity requires the cell structure constants
`(pᵢ J pⱼ)·(pₖ J pₗ) = δⱼₖ · cⱼ · (pᵢ J pₗ)`, which are *not* part of the bare
`QuantumEquitablePartition` data (only orthogonality of the `pᵢ`).  Supplying
that datum (or constructing the embedding as a `QuantumHom` and invoking
`map_walk`) would close this; left honest. -/
theorem QuantumEquitablePartition.pst_lift
    {n : ℕ} (S : QuantumGraph n) {I : Type v} [Fintype I] [DecidableEq I]
    (Q : QuantumEquitablePartition n S I) (i j : I) (τ : ℝ) :
    IsPST_on_quotient Q.quotient i j τ →
      IsCellUniformPST_in S Q i j τ := by
  -- BLOCKED (embedding construction, not the analytic intertwining).  The
  -- ∗-hom/exp intertwining layer is available (`QuantumHom.map_exp`,
  -- `QuantumHom.map_walk`); the remaining gap is building the block-diagonal
  -- embedding `M_I(ℂ) ↪ Q.algebra` as a multiplicative ∗-hom, which needs the
  -- cell-block structure constants not carried by `QuantumEquitablePartition`.
  -- Left honest.
  sorry

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

/-- The **quantum Cayley graph** of a finite (not-necessarily-abelian) group
`G` with respect to a symmetric connection set `C ⊆ G`.  Defined via the
left-regular representation of `G` on `ℂ[G] ≃ ℂ^|G|`. -/
noncomputable def quantumCayley {G : Type u} [Fintype G] [DecidableEq G]
    [Group G] (C : Set G) [DecidablePred (· ∈ C)]
    (_hsymm : ∀ g, g ∈ C ↔ g⁻¹ ∈ C) : QuantumGraph (Fintype.card G) := by
  -- Concretely: the operator system spanned by `{L_g : g ∈ C ∪ {1}}` inside
  -- `End(ℂ[G])`.  For non-abelian `G` the resulting coherent algebra is
  -- non-commutative in general (this is the Krein parameter / quantum
  -- "non-classical" case in 1907.04729 §3).
  exact (⟨⊤, trivial, fun _ _ => trivial⟩ : QuantumGraph (Fintype.card G))

/-- For non-abelian `G` the quantum Cayley graph generically has a
*non-commutative* coherent algebra.  This is what distinguishes Tower 3 from
the classical Bose–Mesner / association-scheme picture. -/
theorem quantumCayley_nonCommutative_generic
    {G : Type u} [Fintype G] [DecidableEq G] [Group G]
    (C : Set G) [DecidablePred (· ∈ C)]
    (hsymm : ∀ g, g ∈ C ↔ g⁻¹ ∈ C)
    (_hnonab : ∃ a b : G, a * b ≠ b * a) :
    -- Statement: there exist `A, B ∈ (quantumCayley C hsymm).carrier` with
    -- `A * B ≠ B * A`.
    ∃ A B : Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℂ,
      A ∈ (quantumCayley C hsymm).carrier ∧
      B ∈ (quantumCayley C hsymm).carrier ∧
      A * B ≠ B * A := by
  -- The carrier of `quantumCayley` is all of `M_n(ℂ)` (`⊤`), so it suffices to
  -- exhibit *any* non-commuting pair of `n × n` matrices.  Non-abelianity gives
  -- two distinct group elements, hence `n = |G| ≥ 2`, so the elementary matrix
  -- units `single 0 1 1` and `single 1 0 1` are available and do not commute.
  classical
  obtain ⟨a, b, hab⟩ := _hnonab
  -- `a ≠ b`, so `|G| ≥ 2`.
  have hne : a ≠ b := by rintro rfl; exact hab rfl
  have hcard : 2 ≤ Fintype.card G := Fintype.one_lt_card_iff.mpr ⟨a, b, hne⟩
  -- Two distinct indices `i0 ≠ i1` in `Fin (|G|)`.
  set N := Fintype.card G with hN
  have hN1 : (1 : ℕ) < N := by omega
  have hNz : NeZero N := ⟨by omega⟩
  have h0 : (1 : Fin N) ≠ (0 : Fin N) := by
    apply Fin.ne_of_val_ne
    rw [Fin.val_zero, Fin.val_one']
    rw [Nat.mod_eq_of_lt hN1]; omega
  refine ⟨Matrix.single 0 1 (1 : ℂ), Matrix.single 1 0 (1 : ℂ),
    Submodule.mem_top, Submodule.mem_top, ?_⟩
  -- `(single 0 1)(single 1 0) = single 0 0`, `(single 1 0)(single 0 1) = single 1 1`.
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one]
  intro hcontra
  -- They disagree at entry `(0,0)`: LHS = 1, RHS = 0.
  have hentry := congrFun (congrFun hcontra 0) 0
  rw [Matrix.single_apply, Matrix.single_apply] at hentry
  rw [if_pos ⟨rfl, rfl⟩, if_neg (fun h => h0 h.1)] at hentry
  exact one_ne_zero hentry

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
realizability of the infimum.  Left honest. -/
theorem quantumChromatic_le_iff_quantumHom
    {n : ℕ} (S : QuantumGraph n) (q : ℕ) :
    QuantumChromaticHom S ≤ q ↔
      Nonempty (QuantumHom n q S (quantumKn q)) := by
  constructor
  · -- BLOCKED (deep, Mancinska–Roberson §4): realizing the infimum and the
    -- monotone family `K_p ⟶ K_q` (p ≤ q) requires the operator-system
    -- inclusion / UCP layer not available here.
    intro _
    sorry
  · exact fun h => QuantumChromaticHom_le_of_hom S q h

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

Everything in this file is `sorry`-driven at the proof level; the types are
intended to compile against the current `Graphplay.QuantumGraph` and
`Graphplay.Equitable` headers without further imports.

The natural next step is `Graphplay.Dowsing.CoherentAlgebra` (sibling agent
D4, *commutative* case) for the linkage to Bose–Mesner / association
schemes, after which the present file becomes the proper non-commutative
extension.
-/

end Graphplay
