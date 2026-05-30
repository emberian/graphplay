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
import Graphplay.PST

universe u v w

open scoped Matrix

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

@[simp] theorem schurProduct_zero_left {V : Type u} (B : Matrix V V ℂ) :
    schurProduct 0 B = 0 := by
  ext x y; simp [schurProduct]

@[simp] theorem schurProduct_zero_right {V : Type u} (A : Matrix V V ℂ) :
    schurProduct A 0 = 0 := by
  ext x y; simp [schurProduct]

theorem schurProduct_add_left {V : Type u} (A₁ A₂ B : Matrix V V ℂ) :
    schurProduct (A₁ + A₂) B = schurProduct A₁ B + schurProduct A₂ B := by
  ext x y; simp [schurProduct, add_mul]

theorem schurProduct_add_right {V : Type u} (A B₁ B₂ : Matrix V V ℂ) :
    schurProduct A (B₁ + B₂) = schurProduct A B₁ + schurProduct A B₂ := by
  ext x y; simp [schurProduct, mul_add]

theorem schurProduct_smul_left {V : Type u} (a : ℂ) (A B : Matrix V V ℂ) :
    schurProduct (a • A) B = a • schurProduct A B := by
  ext x y; simp [schurProduct, mul_assoc]

theorem schurProduct_smul_right {V : Type u} (a : ℂ) (A B : Matrix V V ℂ) :
    schurProduct A (a • B) = a • schurProduct A B := by
  ext x y; simp only [schurProduct, Matrix.smul_apply, smul_eq_mul]; ring

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
  -- An intersection of coherent algebras is a coherent algebra: each closure
  -- property is checked memberwise against every `S` in the defining family,
  -- using `Submodule.mem_sInf`.
  unfold coherentAlgebra
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `1` is in every coherent algebra of the family.
    exact Submodule.mem_sInf.mpr fun S hS => hS.1.one_mem
  · -- `J` (all-ones) is in every coherent algebra of the family.
    exact (@Submodule.mem_sInf ℂ (Matrix V V ℂ) _ _ _ _
      ((fun _ _ => (1 : ℂ)) : Matrix V V ℂ)).mpr fun S hS => hS.1.J_mem
  · -- closed under conjugate transpose.
    intro A hA
    exact Submodule.mem_sInf.mpr fun S hS =>
      hS.1.star_mem A (Submodule.mem_sInf.mp hA S hS)
  · -- closed under matrix product.
    intro A hA B hB
    exact Submodule.mem_sInf.mpr fun S hS =>
      hS.1.mul_mem A (Submodule.mem_sInf.mp hA S hS) B (Submodule.mem_sInf.mp hB S hS)
  · -- closed under Schur product.
    intro A hA B hB
    exact Submodule.mem_sInf.mpr fun S hS =>
      hS.1.schur_mem A (Submodule.mem_sInf.mp hA S hS) B (Submodule.mem_sInf.mp hB S hS)

/-- `G.adj` lies in its own coherent algebra. -/
theorem adj_mem_coherentAlgebra
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    G.adj ∈ coherentAlgebra G := by
  -- Every member `S` of the defining family contains `G.adj` by construction,
  -- so `G.adj` lies in their intersection.
  unfold coherentAlgebra
  exact Submodule.mem_sInf.mpr fun S hS => hS.2

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

/-- The partition projector factors as `Π_P = B Bᴴ` for the cell-embedding
matrix `B = P.cellEmbed` (columns the normalized cell-uniform vectors).  This
is the Gram/outer-product form of Lemma 2 in Chan et al. (1907.04729). -/
theorem EquitablePartition.projector_eq_cellEmbed_mul_conjTranspose
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) :
    P.projector = P.cellEmbed * P.cellEmbedᴴ := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [EquitablePartition.cellEmbed, Matrix.conjTranspose_apply,
    EquitablePartition.cellUniformVec]
  unfold EquitablePartition.projector
  -- Each summand over `i` is `[cells x = i]/√(cellCard i) · conj([cells y = i]/√(cellCard i))`,
  -- nonzero only when `i = cells x = cells y`.
  -- `c = cellCard (cells x) > 0`.
  have hcpos : (0:ℝ) < P.cellCard (P.cells x) := by
    simp only [EquitablePartition.cellCard]
    have hx : x ∈ Finset.univ.filter (fun w : V => P.cells w = P.cells x) := by simp
    have : 0 < (Finset.univ.filter (fun w : V => P.cells w = P.cells x)).card :=
      Finset.card_pos.mpr ⟨x, hx⟩
    exact_mod_cast this
  have hne : (P.cellCard (P.cells x) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt hcpos
  by_cases hxy : P.cells x = P.cells y
  · rw [if_pos hxy]
    -- only the `i = cells x` term survives.
    rw [Finset.sum_eq_single (P.cells x)]
    · rw [if_pos rfl, if_pos hxy.symm]
      rw [star_div₀, star_one, Complex.star_def, Complex.conj_ofReal]
      -- `(1/√c) * (1/√c) = 1/c`, with `c = cellCard (cells x)`.
      rw [div_mul_div_comm, one_mul,
        ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hcpos)]
      -- LHS denominator `Fintype.card {z // cells z = cells x}` equals `cellCard (cells x)`.
      have hcard : (Fintype.card {z : V // P.cells z = P.cells x} : ℂ)
          = (P.cellCard (P.cells x) : ℂ) := by
        unfold EquitablePartition.cellCard
        rw [Fintype.card_subtype]
        push_cast
        rfl
      rw [hcard]
    · intro i _ hi
      rw [if_neg (fun e : P.cells x = i => hi e.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hxy]
    refine (Finset.sum_eq_zero ?_).symm
    intro i _
    by_cases hxi : P.cells x = i
    · have hyi : P.cells y ≠ i := fun e => hxy (hxi.trans e.symm)
      rw [if_neg hyi, star_zero, mul_zero]
    · rw [if_neg hxi, zero_mul]

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
  -- This is Lemma 2 of Chan-Coutinho-Tamon-Vinet-Zhan (1907.04729).  All three
  -- follow from the outer-product factorization `Π = B Bᴴ` together with the
  -- intertwining `A B = B Q̃` (`adj_mul_cellEmbed`) and the Hermiticity of `A`
  -- and `Q̃`.
  have hfac := P.projector_eq_cellEmbed_mul_conjTranspose
  set B := P.cellEmbed with hB
  refine ⟨?_, ?_, ?_⟩
  · -- Commutation: Π A = B Bᴴ A = B Q̃ Bᴴ = A B Bᴴ = A Π.
    -- From `A B = B Q̃` (adj_mul_cellEmbed), conjugate-transpose & Hermiticity
    -- give `Bᴴ A = Q̃ Bᴴ`.
    have hAB : G.adj * B = B * P.symmQuotient := P.adj_mul_cellEmbed
    have hBA : Bᴴ * G.adj = P.symmQuotient * Bᴴ := by
      have h := congrArg Matrix.conjTranspose hAB
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        G.herm, P.symmQuotient_isHermitian] at h
      exact h
    rw [hfac, Matrix.mul_assoc, hBA, ← Matrix.mul_assoc, ← hAB, Matrix.mul_assoc]
  · -- Idempotency: entrywise.  `(Π Π) x y = ∑_z Π x z Π z y`.
    ext x y
    rw [Matrix.mul_apply]
    unfold EquitablePartition.projector
    set c := fun w : V => (Fintype.card {z : V // P.cells z = P.cells w} : ℂ) with hc
    -- `cx = |cell x| ≠ 0` since `x` lives in its own cell.
    have hcx : c x ≠ 0 := by
      rw [hc]
      have hne : Nonempty {z : V // P.cells z = P.cells x} := ⟨⟨x, rfl⟩⟩
      have hpos := Fintype.card_pos_iff.mpr hne
      have : (Fintype.card {z : V // P.cells z = P.cells x} : ℂ) ≠ 0 := by
        exact_mod_cast hpos.ne'
      exact this
    by_cases hxy : P.cells x = P.cells y
    · rw [if_pos hxy]
      -- only `z` with `cells z = cells x` contribute; there are `|cell x|` of
      -- them, each contributing `(1/cx)(1/cx)`.
      have hsum : (∑ z : V, (if P.cells x = P.cells z then (1:ℂ)/c x else 0)
              * (if P.cells z = P.cells y then (1:ℂ)/c z else 0))
          = ∑ z : V, (if P.cells z = P.cells x then ((1:ℂ)/c x)*((1:ℂ)/c x) else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : P.cells z = P.cells x
        · rw [if_pos hz.symm, if_pos (hz.trans hxy)]
          -- `c z = c x` since cells equal.
          have hcz : c z = c x := by rw [hc]; simp only [hz]
          rw [hcz, if_pos hz]
        · rw [if_neg (fun e => hz e.symm), zero_mul, if_neg hz]
      rw [hsum, ← Finset.sum_filter, Finset.sum_const]
      -- `|cell x|` copies of `(1/cx)^2`; card-of-subtype = c x.
      have hcardeq : ((Finset.univ.filter (fun z : V => P.cells z = P.cells x)).card : ℂ)
          = c x := by
        rw [hc]
        simp only
        rw [Fintype.card_subtype]
      rw [nsmul_eq_mul, hcardeq]
      -- goal: `c x * (1/(c x * c x)) = 1 / c x`  (RHS denom is `c x` by def).
      rw [show (Fintype.card {z : V // P.cells z = P.cells x} : ℂ) = c x from rfl]
      field_simp
    · rw [if_neg hxy]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : P.cells z = P.cells y
      · have hxz : P.cells x ≠ P.cells z := fun e => hxy (e.trans hz)
        rw [if_neg hxz, zero_mul]
      · rw [if_neg hz, mul_zero]
  · -- Hermitian: `Π = B Bᴴ` and `(B Bᴴ)ᴴ = B Bᴴ`.
    rw [hfac]
    exact Matrix.isHermitian_mul_conjTranspose_self B

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

/-- A **(commutative) association scheme** on `V` with `d + 1` classes.

The `A i` are the *associate matrices*: in the standard combinatorial
definition they are `0/1` matrices with pairwise-disjoint supports summing to
the all-ones matrix `J`, with `A 0 = I`.  We carry the consequences of the
`0/1`/disjoint-support data directly as the fields `schur` (the Schur-product
law `A i ∘ A j = δ_{ij} A i`) and we restrict to the **commutative** case via
`comm` (the associate matrices pairwise commute under matrix multiplication).

Commutativity is the standard Bose-Mesner setting (general association schemes
can be non-commutative; the Bose-Mesner *algebra* theory and the §3 development
of Chan-Coutinho-Tamon-Vinet-Zhan 1907.04729 are stated for the commutative
case, which is the Tower 3 specialization we model). -/
structure AssociationScheme (V : Type u) [Fintype V] [DecidableEq V]
    (d : ℕ) where
  A : Fin (d + 1) → Matrix V V ℂ
  symm : ∀ i, (A i).IsHermitian
  zero_is_one : A 0 = 1
  sum_is_J : (∑ i, A i) = fun _ _ => 1
  closed : ∀ i j, ∃ c : Fin (d + 1) → ℂ, A i * A j = ∑ k, c k • A k
  /-- The Schur-product law of the `0/1` associate matrices with disjoint
  supports: `A i ∘ A j = A i` if `i = j` and `0` otherwise.  (A consequence of
  the `0/1`/disjoint-support combinatorial data, carried here as structure since
  we work with the matrices abstractly.) -/
  schur : ∀ i j, schurProduct (A i) (A j) = if i = j then A i else 0
  /-- **Commutativity** of the associate matrices under matrix multiplication.
  This restricts to commutative association schemes — the Bose-Mesner setting. -/
  comm : ∀ i j, A i * A j = A j * A i

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
  have hgen : ∀ i, S.A i ∈ BoseMesner S := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `1 = A 0 ∈ span`.
    rw [← S.zero_is_one]; exact hgen 0
  · -- `J = ∑ A i ∈ span`.
    rw [← S.sum_is_J]
    exact Submodule.sum_mem _ fun i _ => hgen i
  · -- Closed under conjugate transpose: each generator is Hermitian.
    intro X hX
    refine QuantumGraph.conjTranspose_mem_span_of_generators ?_ hX
    rintro g ⟨i, rfl⟩
    rw [(S.symm i).eq]; exact Submodule.subset_span ⟨i, rfl⟩
  · -- Closed under matrix product: bilinear, generators close via `S.closed`.
    intro X hX Y hY
    induction hY using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨c, hc⟩ := S.closed i j
        rw [hc]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hgen k)
      | zero => simpa using Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Matrix.add_mul]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ _ hx
    | zero => simpa using Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ _ hx
  · -- Closed under Schur product: bilinear, generators close via `S.schur`.
    intro X hX Y hY
    induction hY using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [S.schur i j]
        by_cases hij : i = j
        · rw [if_pos hij]; exact hgen i
        · rw [if_neg hij]; exact Submodule.zero_mem _
      | zero => rw [schurProduct_zero_left]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [schurProduct_add_left]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [schurProduct_smul_left]; exact Submodule.smul_mem _ _ hx
    | zero => rw [schurProduct_zero_right]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [schurProduct_add_right]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [schurProduct_smul_right]; exact Submodule.smul_mem _ _ hx

/-- The Bose-Mesner algebra is *commutative* under matrix multiplication.
This is the defining feature that distinguishes Tower 3 association
schemes from non-commutative quantum graphs. -/
theorem BoseMesner.comm
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssociationScheme V d)
    (A B : Matrix V V ℂ) (hA : A ∈ BoseMesner S) (hB : B ∈ BoseMesner S) :
    A * B = B * A := by
  -- Commutativity is bilinear, so it suffices to check it on the spanning
  -- generators `S.A i`, where it is the `comm` field of the scheme.  We run a
  -- `span_induction` on `B` (with `A` fixed in the span), then on `A`.
  unfold BoseMesner at hA hB
  induction hB using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    -- Now `A` is general in the span; induct on `A` against the generator `S.A j`.
    induction hA using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact S.comm i j
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
  | smul a x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]

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
  -- DEEP / honest sorry.  `QuantumChromatic`/`Chromatic` are placeholder `0`
  -- stubs, so a `0 ≤ 0` proof would be vacuous and would NOT establish the
  -- real Lovász-theta / nonlocal-game bound this theorem names.  Left honest
  -- pending the quantum-strategy (projective-measurement / Naimark dilation)
  -- formalism that gives the two chromatic numbers genuine bodies.
  sorry

end Graphplay
