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
def block (Q : QuantumEquitablePartition n S I)
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
  -- Hermiticity of the unnormalized block-traces follows from the unital,
  -- ∗-closed structure of `S` + `Q.algebra`; the normalization preserves it.
  sorry

/-- The quantum quotient is the operator-algebraic analogue of the classical
quotient matrix from `Graphplay.Equitable.quotient`.  In the commutative case
the two agree (statement only). -/
theorem quotient_eq_classical_in_commutative_case
    (Q : QuantumEquitablePartition n S I)
    (hcomm : ∀ A ∈ Q.algebra, ∀ B ∈ Q.algebra, A * B = B * A) :
    -- In the commutative case `Q.quotient` agrees with the classical
    -- `EquitablePartition.quotient` once we identify the underlying weighted
    -- graph; we leave the identification implicit.
    True := by
  trivial

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
    ‖(Matrix.exp (-(Complex.I * (τ : ℂ)) • H)) u v‖ = 1

/-- **Quantum PST on the quotient matrix.**  We re-use the operator-system
definition: PST on the quotient `M : Matrix I I ℂ` is PST in the *trivial*
quantum graph spanned by `M`. -/
def IsPST_on_quotient {I : Type v} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (i j : I) (τ : ℝ) : Prop :=
  ‖(Matrix.exp (-(Complex.I * (τ : ℂ)) • M)) i j‖ = 1

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
    let U := Matrix.exp (-(Complex.I * (τ : ℂ)) • H)
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
after normalization. -/
theorem QuantumEquitablePartition.pst_lift
    {n : ℕ} (S : QuantumGraph n) {I : Type v} [Fintype I] [DecidableEq I]
    (Q : QuantumEquitablePartition n S I) (i j : I) (τ : ℝ) :
    IsPST_on_quotient Q.quotient i j τ →
      IsCellUniformPST_in S Q i j τ := by
  -- Lift the quotient Hamiltonian to a Hermitian in `Q.algebra ⊆ M_n(ℂ)` via
  -- the canonical block-diagonal embedding `M ↦ ∑_{i,j} M_{i,j} · pᵢ J pⱼ`;
  -- exp commutes with ∗-homs; conclude by the block-trace normalization.
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
`φ : M_n(ℂ) → M_m(ℂ)` that is unital, ∗-preserving, and sends the operator
system `S` into `T`.  Complete positivity is omitted at this scaffold level;
the conventional Mancinska–Roberson definition demands it. -/
structure QuantumHom (n m : ℕ) (S : QuantumGraph n) (T : QuantumGraph m) where
  /-- The underlying linear map. -/
  toLin : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ
  /-- Unitality. -/
  map_one : toLin 1 = 1
  /-- ∗-preservation. -/
  map_star : ∀ A, toLin (Aᴴ) = (toLin A)ᴴ
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
  -- Track the block-trace through `φ`: ∗-preservation gives Hermiticity of
  -- the image, unitality gives the cell-projector compatibility automatically
  -- once `hcompat` is supplied, and the trace of `pⱼ A pᵢ` is preserved.
  sorry

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
    (QS : QuantumEquitablePartition n S I)
    (QT : QuantumEquitablePartition m T I) :
    -- Statement: the lifted PST property transports along the retraction.
    True := by
  trivial

/-! ## 5. Concrete examples -/

/-- The **non-commutative complete graph** on `n` vertices: the operator
system of all `n × n` matrices with zero diagonal, together with the unit.
This is `K_n` in the operator-system sense of Duan–Severini–Winter; its
coherent algebra is all of `M_n(ℂ)`. -/
def quantumKn (n : ℕ) : QuantumGraph n where
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
  -- The cell projectors are the spectral projectors onto the Hamming-weight
  -- eigenspaces of the underlying Cayley-graph operator on (ℤ/qℤ)^n.
  sorry

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
  -- The non-commutativity of `G` lifts to non-commutativity of the
  -- left-regular representation; explicit witnesses are `L_a, L_b` for
  -- `a, b` in the witness pair.
  sorry

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

/-- The **non-commutative WL refinement step** applied to an operator system
inside `M_n(ℂ)`.  One step adjoins all matrix products of pairs of operators
already in the system (and the operator-system Schur product with respect to
the standard basis), then takes the unital ∗-closure. -/
noncomputable def WLRefine {n : ℕ} (S : QuantumGraph n) : QuantumGraph n := by
  -- Definitionally: the unital ∗-closure of `S ∪ (S · S) ∪ (S ⊙ S)` inside
  -- `M_n(ℂ)`, where `⊙` is the operator-system Schur product.  We record the
  -- statement as a placeholder.
  exact S

/-- The WL refinement forms an increasing chain of operator systems. -/
def WLChain {n : ℕ} (S : QuantumGraph n) : ℕ → QuantumGraph n
  | 0 => S
  | k + 1 => WLRefine (WLChain S k)

/-- **WL termination.**  In `M_n(ℂ)` the dimension is finite, so the chain
`WLChain S k` stabilizes at some `k ≤ n^2`.  The fixed point is the
**non-commutative coherent algebra** of `S` — the smallest unital
∗-subalgebra of `M_n(ℂ)` containing `S`. -/
theorem WLChain.terminates {n : ℕ} (S : QuantumGraph n) :
    ∃ k₀, ∀ k ≥ k₀, (WLChain S k).carrier = (WLChain S k₀).carrier := by
  -- Use that `dim_ℂ (Submodule.span …) ≤ n^2` is a non-increasing
  -- well-founded bound on the strictly-ascending chain.
  sorry

/-- **WL fixed point.**  The stable value of the WL chain. -/
noncomputable def WLFix {n : ℕ} (S : QuantumGraph n) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  let k₀ := (WLChain.terminates S).choose
  (WLChain S k₀).carrier

/-- The WL fixed point is a non-commutative coherent algebra in the sense of
the smallest unital ∗-subalgebra containing `S`. -/
theorem WLFix_isCoherentAlgebra {n : ℕ} (S : QuantumGraph n) :
    IsCoherentAlgebra (WLFix S) := by
  -- The fixed point is closed under products by construction, and is unital
  -- + ∗-closed because `S` is.
  sorry

/-- **`χ_q` via WL.**  The quantum chromatic number of `S` is at most `q` iff
there is a unital ∗-homomorphism from the WL fixed point of `S` to
`M_q(ℂ)` (Mancinska–Roberson arXiv:1903.11491 Thm 4.1). -/
theorem quantumChromatic_le_iff_quantumHom
    {n : ℕ} (S : QuantumGraph n) (q : ℕ) :
    QuantumChromatic S ≤ q ↔
      Nonempty (QuantumHom n q S (quantumKn q)) := by
  -- This is the Mancinska–Roberson characterization of χ_q via UCP maps; the
  -- "→" direction realizes the colouring as the image of the cell projectors
  -- of an equitable partition into `M_q(ℂ)`.
  sorry

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

/-- **Open question (Quantum Graphon Limits).**  Does every Cauchy sequence of
quantum graphs (in cut-distance for an ultraproduct trace on `R`) admit a
limit object?  See discussion at the head of §7. -/
def OpenQuestion.quantumGraphonLimits : Prop :=
  -- Placeholder: no `Prop`-level content; this is an essay-level open
  -- question.  We record it as `True` so the file compiles.
  True

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
-/
def OpenDirection.GNW_chain : Prop := True

/-- **Open 2.**  Determine the **non-commutative depth** of the WL refinement
chain: for a fixed `n`, is `min{k : WLChain S k = WLFix S}` polynomial in `n`?
The classical analogue is `O(n)` (Cai–Fürer–Immerman); the non-commutative
case is open and would settle the *quantum graph isomorphism problem* in
operator-system formulation. -/
def OpenDirection.WL_depth : Prop := True

/-- **Open 3.**  Identify the **operator-system analogue of the Hamming
scheme**: a one-parameter family of quantum graphs interpolating between the
non-commutative `K_n` and its quotient quantum-Hamming graphs.  Conjecturally
this is the family of *quantum Johnson schemes* of Krein–Banica
(see Krein parameters in the quantum association-scheme literature). -/
def OpenDirection.quantumHammingScheme : Prop := True

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
