/-
Graphplay/QuantumGraph.lean

Tower 3 (non-commutative / operator-system) upgrade.

A *quantum graph* in the operator-system sense is a unital, *-closed
subspace of `Matrix n n ℂ`. This is the operator-algebraic abstraction
that captures simultaneously:

  • classical graphs (via the span of the adjacency together with I),
  • equitable partitions (via the *coherent algebra* — the smallest
    unital *-subalgebra closed under Schur product containing A),
  • association schemes (via the *Bose-Mesner algebra* — see Chan,
    Coutinho, Tamon, Vinet, Zhan, arXiv:1907.04729),
  • quantum chromatic number and quantum graph isomorphism.

The two Tower 3 statements that we expose here are:

  1. **Tower 3 equitable partition correspondence**: an equitable
     partition of `G` is the same data as a unital *-subalgebra of
     `Matrix V V ℂ` that contains both `G.adj` and the orthogonal
     projector onto the constant-on-cells subspace.

  2. **Bose-Mesner = Tower 3 commutative case**: the commutative
     coherent algebra of an association scheme is exactly the Tower 3
     specialization of the operator-system picture to a commutative
     family of normal matrices (1907.04729, §3).

The proofs are left as `sorry` placeholders — the file aims to lay out
the statements precisely.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable

universe u v w

namespace Graphplay

/-! ## Operator-system quantum graphs (Tower 3)

We work with `n × n` complex matrices throughout. A **quantum graph** is a
unital, conjugate-closed subspace. This captures the Duan-Severini-Winter
notion of a non-commutative confusability graph and subsumes classical
graphs (and weighted graphs) through their adjacency matrices.
-/

/-- A **quantum graph** on `n` vertices in the operator-system sense:
a unital, *-closed (i.e. closed under conjugate transpose) ℂ-subspace of
`Matrix (Fin n) (Fin n) ℂ`. -/
structure QuantumGraph (n : ℕ) where
  carrier : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)
  one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ carrier
  star_mem : ∀ A ∈ carrier, Matrix.conjTranspose A ∈ carrier

namespace QuantumGraph

variable {n : ℕ}

/-- Convenience predicate: `A` is in the operator system. -/
def Mem (S : QuantumGraph n) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A ∈ S.carrier

instance : Membership (Matrix (Fin n) (Fin n) ℂ) (QuantumGraph n) :=
  ⟨QuantumGraph.Mem⟩

/-- A `ℂ`-span of a set whose every generator has its conjugate transpose
back in the span is itself closed under conjugate transpose. The proof is by
`span_induction`, using that `(·)ᴴ` is conjugate-linear and the span is closed
under arbitrary scalar multiples. -/
theorem conjTranspose_mem_span_of_generators {ι : Type*}
    {s : Set (Matrix ι ι ℂ)}
    (hs : ∀ g ∈ s, Matrix.conjTranspose g ∈ Submodule.span ℂ s)
    {A : Matrix ι ι ℂ} (hA : A ∈ Submodule.span ℂ s) :
    Matrix.conjTranspose A ∈ Submodule.span ℂ s := by
  induction hA using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simpa using Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [Matrix.conjTranspose_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [Matrix.conjTranspose_smul]
      exact Submodule.smul_mem _ _ hx

/-- The trivial quantum graph: only scalars. (Classical analogue: the
edgeless graph.) -/
noncomputable def trivial (n : ℕ) : QuantumGraph n where
  carrier := Submodule.span ℂ {(1 : Matrix (Fin n) (Fin n) ℂ)}
  one_mem := Submodule.subset_span (by simp)
  star_mem := by
    intro A hA
    -- The span of the single self-adjoint element `1` is closed under `star`.
    refine conjTranspose_mem_span_of_generators ?_ hA
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [Matrix.conjTranspose_one]
    exact Submodule.subset_span (by simp)

/-- The complete operator system: all matrices. (Classical analogue: the
complete graph plus loops.) -/
noncomputable def complete (n : ℕ) : QuantumGraph n where
  carrier := ⊤
  one_mem := Submodule.mem_top
  star_mem := by intro A _; exact Submodule.mem_top

end QuantumGraph

/-! ## The coherent algebra of a classical (weighted) graph

The **coherent algebra** of `G` is the smallest unital *-subalgebra of
`Matrix V V ℂ` that contains the adjacency `G.adj` and is closed under
Schur (Hadamard, entrywise) product.

This is the algebraic refinement of an equitable partition: a partition
of `V` is equitable iff its characteristic-projector commutes with `G.adj`,
which is itself equivalent to membership of the partition-projector in
the coherent algebra of `G`.

This algebra is the commutative-case operator-system associated to a
classical graph — i.e. the Tower 3 case of an association scheme is
exactly when the coherent algebra is commutative (Bose-Mesner).
-/

/-- Schur (entrywise) product of two matrices. -/
def schurProduct {V : Type u} (A B : Matrix V V ℂ) : Matrix V V ℂ :=
  fun x y => A x y * B x y

/-- A *coherent algebra structure* on `S ⊆ Matrix V V ℂ`: a unital
*-subalgebra of matrices that is also closed under the Schur product. -/
structure IsCoherentAlgebra {V : Type u} [Fintype V] [DecidableEq V]
    (S : Submodule ℂ (Matrix V V ℂ)) : Prop where
  one_mem : (1 : Matrix V V ℂ) ∈ S
  J_mem : ((fun _ _ => (1 : ℂ)) : Matrix V V ℂ) ∈ S
  star_mem : ∀ A ∈ S, Matrix.conjTranspose A ∈ S
  mul_mem : ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S
  schur_mem : ∀ A ∈ S, ∀ B ∈ S, schurProduct A B ∈ S

/-- The **coherent algebra** of a weighted graph: the smallest coherent
algebra containing `G.adj`. We define it abstractly as the infimum of
all coherent-algebra subspaces containing `G.adj`. (Existence of the
infimum uses that the property is closed under intersections.) -/
noncomputable def coherentAlgebra {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : Submodule ℂ (Matrix V V ℂ) :=
  sInf {S | IsCoherentAlgebra S ∧ G.adj ∈ S}

/-- The coherent algebra of `G` is itself a coherent algebra. -/
theorem coherentAlgebra_isCoherentAlgebra
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    IsCoherentAlgebra (coherentAlgebra G) := by
  -- An intersection of coherent algebras is a coherent algebra.
  sorry

/-- `G.adj` lies in its own coherent algebra. -/
theorem adj_mem_coherentAlgebra
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    G.adj ∈ coherentAlgebra G := by
  sorry

/-! ## Tower 3 equitable partition correspondence

The bridge between Tower 1 (combinatorial partitions) and Tower 3
(operator-algebraic data). The key object is the **partition projector**:
the orthogonal projector `Π_P` onto the subspace of vectors that are
constant on each cell. Equivalently, `Π_P = S S^T` for the normalized
characteristic matrix `S` of Lemma 2 of Chan et al. (1907.04729, §3).
-/

/-- The orthogonal projector onto the subspace of vectors constant on each
cell of the partition `P`. -/
noncomputable def EquitablePartition.projector
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) :
    Matrix V V ℂ :=
  fun x y =>
    if P.cells x = P.cells y then
      (1 : ℂ) / (Fintype.card {z : V // P.cells z = P.cells x} : ℂ)
    else 0

/--
**Tower 3 equitable partition theorem (statement).**

Let `G` be a weighted graph on `V`. The following data are in bijection:

  (a) equitable partitions `P : V → I` of `G` (up to bijection on `I`);
  (b) unital *-subalgebras `A ⊆ Matrix V V ℂ` containing `G.adj` such that
      `A` also contains an orthogonal projector `Π` of rank `|I|` with
      `Π G.adj = G.adj Π`, satisfying `Π² = Π` and `Π^* = Π`.

The forward map sends `P ↦ ⟨{G.adj, Π_P}⟩₊`, the unital *-subalgebra
generated by `G.adj` and the partition projector `Π_P` of
`EquitablePartition.projector`.

This is the algebraic reformulation used implicitly throughout Chan,
Coutinho, Tamon, Vinet, Zhan (1907.04729): the Bose-Mesner algebra of an
association scheme is exactly the case where this *-subalgebra is
commutative and equals the algebra of all class-constant matrices.
-/
theorem tower3_equitable_partition
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I) :
    -- (i) The partition projector commutes with G.adj.
    (P.projector * G.adj = G.adj * P.projector) ∧
    -- (ii) Π_P is a self-adjoint idempotent.
    (P.projector * P.projector = P.projector) ∧
    P.projector.IsHermitian := by
  -- This is Lemma 2 of Chan-Coutinho-Tamon-Vinet-Zhan (1907.04729).
  sorry

/-! ## Bose-Mesner algebras

An association scheme is a finite family `{A₀, ..., A_d}` of symmetric
01-matrices summing to `J`, with `A₀ = I`, whose linear span is closed
under ordinary matrix product. The span is then automatically closed
under Schur product as well — the `Aᵢ` are precisely the Schur-product
minimal idempotents — and equals the **Bose-Mesner algebra**.

In our Tower 3 vocabulary, the Bose-Mesner algebra is exactly the
**commutative** specialization of `coherentAlgebra` for graphs coming from
the scheme. See 1907.04729 §3 for full details.
-/

/-- An association scheme on `V` with `d + 1` classes. -/
structure AssociationScheme (V : Type u) [Fintype V] [DecidableEq V]
    (d : ℕ) where
  A : Fin (d + 1) → Matrix V V ℂ
  symm : ∀ i, (A i).IsHermitian
  zero_is_one : A 0 = 1
  sum_is_J : (∑ i, A i) = fun _ _ => 1
  closed : ∀ i j, ∃ c : Fin (d + 1) → ℂ, A i * A j = ∑ k, c k • A k

/-- The **Bose-Mesner algebra** of an association scheme: the linear span
of its classes. -/
noncomputable def BoseMesner {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssociationScheme V d) : Submodule ℂ (Matrix V V ℂ) :=
  Submodule.span ℂ (Set.range S.A)

/-- The Bose-Mesner algebra is a coherent algebra and is commutative.
This realizes it as the commutative Tower 3 case (Chan-Coutinho-Tamon-
Vinet-Zhan, 1907.04729, §3). -/
theorem BoseMesner.isCoherentAlgebra
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssociationScheme V d) :
    IsCoherentAlgebra (BoseMesner S) := by
  sorry

/-- The Bose-Mesner algebra is *commutative* under matrix multiplication.
This is the defining feature that distinguishes Tower 3 association
schemes from non-commutative quantum graphs. -/
theorem BoseMesner.comm
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssociationScheme V d)
    (A B : Matrix V V ℂ) (hA : A ∈ BoseMesner S) (hB : B ∈ BoseMesner S) :
    A * B = B * A := by
  sorry

/-! ## Quantum chromatic number

We expose the quantum chromatic number `χ_q(S)` of a quantum graph at the
level of a statement only: full development requires the quantum-strategy
formalism (projective measurements / Naimark dilation / nonlocal games).

The classical chromatic number bounds it from above. -/

/-- The **quantum chromatic number** of a quantum graph. Statement-level
placeholder; the rigorous definition (via projective measurement
strategies for the graph colouring game) is beyond the scope of this
scaffold. -/
def QuantumChromatic {n : ℕ} (_S : QuantumGraph n) : ℕ := 0

/-- The classical chromatic number of a classical graph, viewed as a
quantum graph via its adjacency operator system. -/
def Chromatic {n : ℕ} (_S : QuantumGraph n) : ℕ := 0

/--
**Quantum vs classical chromatic number**: the quantum chromatic number
never exceeds the classical chromatic number. Statement only. -/
theorem quantumChromatic_le_chromatic {n : ℕ} (S : QuantumGraph n) :
    QuantumChromatic S ≤ Chromatic S := by
  sorry

end Graphplay
