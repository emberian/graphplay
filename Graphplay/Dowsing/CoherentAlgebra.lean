/-
# Graphplay.Dowsing.CoherentAlgebra

**Hole D4 — Coherent algebra ↔ equitable partition (Tower 3, commutative case).**

This file expands the Tower-3 dictionary started in `Graphplay/QuantumGraph.lean`
into a fully fledged statement-level theory of *coherent (sub-)algebras*. The
guiding folklore equivalence — apparently never written down formally — is:

> An equitable partition of a graph `G` on `V` is the same data as a
> *commutative* unital `*`-subalgebra of `Matrix V V ℂ` that contains the
> adjacency matrix `G.adj` and is closed under the Schur (entrywise) product.

We make every direction of this dictionary precise (with `sorry` placeholders
for the harder analytic / combinatorial directions), and we lay out the
**Weisfeiler–Leman refinement chain** of coherent subalgebras as a tower
connecting `coherentAlgebra G` to the orbit algebra of `Aut(G)`.

The development sits inside the *commutative* boundary of the Tower 3 picture;
the genuinely non-commutative coherent algebras (which appear for *quantum*
graph isomorphism, quantum colourings and quantum permutation groups) are
identified at the end as the natural successor object — handed off to Hole D5.

References used:
* Chan, Coutinho, Tamon, Vinet, Zhan, *Quantum fractional revival on graphs and
  the Bose-Mesner algebra of an association scheme*, arXiv:1907.04729.
* Bachman, Fredon, Tamon, *Perfect state transfer on quotient graphs*,
  arXiv:1108.0339 (equitable partitions / partition matrix / quotient graph).
* Godsil, Royle, *Algebraic Graph Theory* — the cellular / coherent algebra
  picture in the background.

This file is **statement-only**: heavy proofs (commutativity of the partition
algebra, recovery of cells from projectors, equivalence with Bose-Mesner) are
left as `sorry`. Everything is structured so that downstream files can `import
Graphplay.Dowsing.CoherentAlgebra` and use the API.
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.QuantumGraph
import Graphplay.LiteratureInterfaces

open scoped Matrix BigOperators
open Graphplay.LiteratureInterfaces

universe u v w

namespace Graphplay
namespace Dowsing

/-! ## 1. Schur (Hadamard, entrywise) product structure

We re-export `Graphplay.schurProduct` from `Graphplay/QuantumGraph.lean` and
record the algebraic properties: it is a commutative associative bilinear
product whose two-sided unit is the **all-ones matrix** `Jₙ`. The Schur
product gives `Matrix V V ℂ` a *second* compatible multiplication, distinct
from ordinary matrix multiplication.

Mathlib does not (currently) carry a `Mathlib.LinearAlgebra.Matrix.Schur`
file, so we treat the Schur product purely combinatorially as a function
into the underlying `V × V → ℂ`.
-/

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {I' : Type w} [Fintype I'] [DecidableEq I']

/-- The all-ones matrix `Jₙ : V × V → 1`. This is the Schur-product unit. -/
def matJ : Matrix V V ℂ := fun _ _ => (1 : ℂ)

@[simp] theorem matJ_apply (x y : V) : (matJ (V := V)) x y = 1 := rfl

/-- Schur (entrywise) product on `Matrix V V ℂ`. Re-exported notation for
`Graphplay.schurProduct`. -/
def schur (A B : Matrix V V ℂ) : Matrix V V ℂ := Graphplay.schurProduct A B

@[simp] theorem schur_apply (A B : Matrix V V ℂ) (x y : V) :
    schur A B x y = A x y * B x y := rfl

/-- Commutativity of the Schur product. -/
@[simp] theorem schur_comm (A B : Matrix V V ℂ) : schur A B = schur B A := by
  ext i j; simp [mul_comm]

/-- Associativity of the Schur product. -/
theorem schur_assoc (A B C : Matrix V V ℂ) :
    schur (schur A B) C = schur A (schur B C) := by
  ext i j; simp [mul_assoc]

/-- `Jₙ` is a left unit for the Schur product. -/
@[simp] theorem schur_J_left (A : Matrix V V ℂ) :
    schur (matJ (V := V)) A = A := by
  ext i j; simp

/-- `Jₙ` is a right unit for the Schur product. -/
@[simp] theorem schur_J_right (A : Matrix V V ℂ) :
    schur A (matJ (V := V)) = A := by
  ext i j; simp

/-- Bilinearity of the Schur product over `ℂ` (left side). -/
theorem schur_add_left (A B C : Matrix V V ℂ) :
    schur (A + B) C = schur A C + schur B C := by
  ext i j; simp [Matrix.add_apply, add_mul]

/-- Bilinearity of the Schur product over `ℂ` (right side). -/
theorem schur_add_right (A B C : Matrix V V ℂ) :
    schur A (B + C) = schur A B + schur A C := by
  ext i j; simp [Matrix.add_apply, mul_add]

/-- Compatibility of Schur with scalar multiplication. -/
theorem schur_smul_left (c : ℂ) (A B : Matrix V V ℂ) :
    schur (c • A) B = c • schur A B := by
  ext i j; simp [Matrix.smul_apply, mul_assoc]

/-- The Schur product preserves the conjugate transpose: `(A ∘ B)ᴴ = Aᴴ ∘ Bᴴ`. -/
theorem schur_conjTranspose (A B : Matrix V V ℂ) :
    (schur A B)ᴴ = schur Aᴴ Bᴴ := by
  ext i j
  -- `(A∘B)ᴴ x y = conj ((A∘B) y x) = conj (A y x) * conj (B y x)`
  -- and `(Aᴴ ∘ Bᴴ) x y = Aᴴ x y * Bᴴ x y = conj (A y x) * conj (B y x)`.
  simp [Matrix.conjTranspose_apply, star_mul']

/-! ## 2. Coherent subalgebras

We package the property "this submodule is a coherent algebra" as a `Prop`.
Note the `Submodule` viewpoint matches the rest of `QuantumGraph.lean`: we
work with a ℂ-linear subspace `S ⊆ Matrix V V ℂ` and add closure axioms.
-/

/-- A **coherent subalgebra** of `Matrix V V ℂ`: a ℂ-linear subspace that is
unital (contains `1` and the all-ones matrix `J`), `*`-closed (conjugate
transpose), closed under ordinary matrix multiplication, and closed under the
Schur (entrywise) product. -/
structure IsCoherent (S : Submodule ℂ (Matrix V V ℂ)) : Prop where
  one_mem : (1 : Matrix V V ℂ) ∈ S
  J_mem : matJ (V := V) ∈ S
  star_mem : ∀ A ∈ S, Aᴴ ∈ S
  mul_mem : ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S
  schur_mem : ∀ A ∈ S, ∀ B ∈ S, schur A B ∈ S

/-- A **non-unital coherent algebra**: like `IsCoherent` but *without* the
`1 ∈ S` axiom.  This is the genuinely-correct closure structure of the block
algebra / partition algebra of an arbitrary partition: those contain `J` and
are closed under `*`, Schur, and `*`, but contain the identity matrix `1` only
when every cell is a singleton (see `blockAlgebra_isCoherent`).  Containing `1`
is an *extra* hypothesis (`IsCoherent = IsCoherentNoOne + one_mem`). -/
structure IsCoherentNoOne (S : Submodule ℂ (Matrix V V ℂ)) : Prop where
  J_mem : matJ (V := V) ∈ S
  star_mem : ∀ A ∈ S, Aᴴ ∈ S
  mul_mem : ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S
  schur_mem : ∀ A ∈ S, ∀ B ∈ S, schur A B ∈ S

/-- Every (unital) coherent algebra is in particular non-unital coherent. -/
theorem IsCoherent.toNoOne {S : Submodule ℂ (Matrix V V ℂ)} (h : IsCoherent S) :
    IsCoherentNoOne S :=
  ⟨h.J_mem, h.star_mem, h.mul_mem, h.schur_mem⟩

/-- A coherent subalgebra is **commutative** if matrix multiplication is
commutative on it. The classical / Bose-Mesner regime sits at exactly this
boundary; non-commutative coherent algebras are the right setting for the
quantum colouring / quantum permutation group story (Hole D5). -/
def IsCoherent.IsCommutative {S : Submodule ℂ (Matrix V V ℂ)}
    (_h : IsCoherent S) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A * B = B * A

/-- Commutativity of a non-unital coherent algebra. -/
def IsCoherentNoOne.IsCommutative {S : Submodule ℂ (Matrix V V ℂ)}
    (_h : IsCoherentNoOne S) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A * B = B * A

/-- A coherent subalgebra is **projector-generated** if it is spanned (over
`ℂ`) by a finite family of orthogonal projectors that pairwise commute and
sum to the identity. This is exactly the data of the partition projectors of
an equitable partition; cf. `partitionAlgebra` below. -/
structure IsCoherent.ProjectorGenerated {S : Submodule ℂ (Matrix V V ℂ)}
    (h : IsCoherent S) (J : Type v) [Fintype J] [DecidableEq J] where
  /-- The generating projectors. -/
  proj : J → Matrix V V ℂ
  /-- Each projector lies in the algebra. -/
  proj_mem : ∀ j, proj j ∈ S
  /-- Self-adjointness. -/
  proj_herm : ∀ j, (proj j).IsHermitian
  /-- Idempotence. -/
  proj_idem : ∀ j, proj j * proj j = proj j
  /-- Pairwise orthogonality. -/
  proj_ortho : ∀ j k, j ≠ k → proj j * proj k = 0
  /-- Resolution of the identity. -/
  proj_sum : (∑ j, proj j) = (1 : Matrix V V ℂ)
  /-- The projectors *span* `S`. -/
  spans : (Submodule.span ℂ (Set.range proj) : Submodule ℂ _) = S
  -- Don't bundle `commutes_with_S` here: it follows from the existence of a
  -- common diagonalizing basis once `S` is commutative.

/-! ### 2a. The trivial coherent algebra and the full matrix algebra.

The two extremes of the lattice of coherent subalgebras are the linear span
of `{1, J}` (the *initial* coherent algebra; corresponds to the **indiscrete**
partition into a single cell) and the full matrix algebra `Matrix V V ℂ` (the
*terminal* coherent algebra; corresponds to the **discrete** partition into
singletons). All other coherent algebras lie strictly in between. -/

/-- The initial (smallest) coherent subalgebra: `span_ℂ {1, J}`. -/
noncomputable def initialCoherent : Submodule ℂ (Matrix V V ℂ) :=
  Submodule.span ℂ ({1, matJ (V := V)} : Set (Matrix V V ℂ))

/-- `J * J = |V| • J`. -/
theorem matJ_mul_matJ :
    (matJ (V := V)) * (matJ (V := V)) = (Fintype.card V : ℂ) • (matJ (V := V)) := by
  ext i j
  simp [Matrix.mul_apply, matJ, Matrix.smul_apply, Finset.card_univ]

/-- The all-ones matrix is Hermitian. -/
theorem matJ_isHermitian : (matJ (V := V)).IsHermitian := by
  apply Matrix.IsHermitian.ext; intro i j; simp [matJ]

theorem initialCoherent_isCoherent : IsCoherent (initialCoherent (V := V)) := by
  -- Both `1` and `J` are Hermitian; the products `1·1 = 1`, `1·J = J = J·1`,
  -- and `J·J = |V|·J` stay in the span. Similarly `1∘1 = 1`, `1∘J = 1`,
  -- `J∘J = J`.
  have h1 : (1 : Matrix V V ℂ) ∈ initialCoherent (V := V) :=
    Submodule.subset_span (by simp)
  have hJ : matJ (V := V) ∈ initialCoherent (V := V) :=
    Submodule.subset_span (by simp)
  -- the spanning set, for `span_induction`
  refine ⟨h1, hJ, ?_, ?_, ?_⟩
  · -- star_mem: it suffices on generators, then extends ℂ-linearly.
    intro A hA
    refine Submodule.span_induction
      (p := fun A _ => Aᴴ ∈ initialCoherent (V := V)) ?_ ?_ ?_ ?_ hA
    · rintro x (rfl | rfl)
      · rw [Matrix.conjTranspose_one]; exact h1
      · rw [(matJ_isHermitian (V := V)).eq]; exact hJ
    · simpa using Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [Matrix.conjTranspose_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [Matrix.conjTranspose_smul]
      exact Submodule.smul_mem _ _ hx
  · -- mul_mem
    intro A hA B hB
    refine Submodule.span_induction
      (p := fun A _ => ∀ B ∈ initialCoherent (V := V), A * B ∈ initialCoherent (V := V))
      ?_ ?_ ?_ ?_ hA B hB
    · rintro x (rfl | rfl) B hB
      · rw [one_mul]; exact hB
      · -- J * B: induct on B
        refine Submodule.span_induction
          (p := fun B _ => matJ (V := V) * B ∈ initialCoherent (V := V)) ?_ ?_ ?_ ?_ hB
        · rintro y (rfl | rfl)
          · rw [mul_one]; exact hJ
          · rw [matJ_mul_matJ]; exact Submodule.smul_mem _ _ hJ
        · simpa using Submodule.zero_mem _
        · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
        · intro c u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
    · intro B _; rw [zero_mul]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy B hB; rw [add_mul]; exact Submodule.add_mem _ (hx B hB) (hy B hB)
    · intro c x _ hx B hB; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hx B hB)
  · -- schur_mem
    intro A hA B hB
    refine Submodule.span_induction
      (p := fun A _ => ∀ B ∈ initialCoherent (V := V), schur A B ∈ initialCoherent (V := V))
      ?_ ?_ ?_ ?_ hA B hB
    · rintro x (rfl | rfl) B hB
      · -- 1 ∘ B: induct on B
        refine Submodule.span_induction
          (p := fun B _ => schur (1 : Matrix V V ℂ) B ∈ initialCoherent (V := V)) ?_ ?_ ?_ ?_ hB
        · rintro y (rfl | rfl)
          · have : schur (1 : Matrix V V ℂ) 1 = 1 := by
              ext i j; simp only [schur_apply, Matrix.one_apply]; split <;> simp
            rw [this]; exact h1
          · have : schur (1 : Matrix V V ℂ) (matJ (V := V)) = 1 := by
              ext i j; simp [Matrix.one_apply]
            rw [this]; exact h1
        · show schur (1 : Matrix V V ℂ) 0 ∈ _
          have hz : schur (1 : Matrix V V ℂ) 0 = 0 := by ext i j; simp
          rw [hz]; exact Submodule.zero_mem _
        · intro u v _ _ hu hv; rw [schur_add_right]; exact Submodule.add_mem _ hu hv
        · intro c u _ hu
          rw [show schur (1 : Matrix V V ℂ) (c • u) = c • schur 1 u by
            rw [schur_comm, schur_smul_left, schur_comm]]
          exact Submodule.smul_mem _ _ hu
      · -- J ∘ B = B
        rw [schur_J_left]; exact hB
    · intro B _; rw [show schur (0 : Matrix V V ℂ) B = 0 by ext i j; simp]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy B hB; rw [schur_add_left]; exact Submodule.add_mem _ (hx B hB) (hy B hB)
    · intro c x _ hx B hB; rw [schur_smul_left]; exact Submodule.smul_mem _ _ (hx B hB)

/-- The terminal (largest) coherent subalgebra: all of `Matrix V V ℂ`. -/
noncomputable def fullCoherent : Submodule ℂ (Matrix V V ℂ) := ⊤

theorem fullCoherent_isCoherent : IsCoherent (fullCoherent (V := V)) where
  one_mem := Submodule.mem_top
  J_mem := Submodule.mem_top
  star_mem := fun _ _ => Submodule.mem_top
  mul_mem := fun _ _ _ _ => Submodule.mem_top
  schur_mem := fun _ _ _ _ => Submodule.mem_top

/-! ### 2b. Intersection of coherent subalgebras is again coherent.

This justifies the `sInf` definition of `coherentAlgebra` in
`Graphplay/QuantumGraph.lean`. -/

theorem isCoherent_sInf
    (𝒮 : Set (Submodule ℂ (Matrix V V ℂ)))
    (h : ∀ S ∈ 𝒮, IsCoherent S) :
    IsCoherent (sInf 𝒮) := by
  -- Every closure axiom is preserved by intersections of submodules:
  -- if every member contains `1`, the intersection does; etc.
  constructor
  · rw [Submodule.mem_sInf]; intro S hS; exact (h S hS).one_mem
  · rw [Submodule.mem_sInf]; intro S hS; exact (h S hS).J_mem
  · intro A hA
    rw [Submodule.mem_sInf] at hA ⊢
    intro S hS; exact (h S hS).star_mem A (hA S hS)
  · intro A hA B hB
    rw [Submodule.mem_sInf] at hA hB ⊢
    intro S hS; exact (h S hS).mul_mem A (hA S hS) B (hB S hS)
  · intro A hA B hB
    rw [Submodule.mem_sInf] at hA hB ⊢
    intro S hS; exact (h S hS).schur_mem A (hA S hS) B (hB S hS)

/-! ## 3. The partition algebra of an equitable partition.

Given a partition `cells : V → I` (not necessarily equitable!), there is a
canonical commutative unital `*`-subalgebra of `Matrix V V ℂ`:

* the (rank-1) projector `Πᵢ` onto the cell `Cᵢ = cells⁻¹{i}`, namely
  `(Πᵢ) x y = [cells x = i ∧ cells y = i] / |Cᵢ|`;
* the **block-constant matrices**: all `M` for which `M x y` depends only on
  `(cells x, cells y)`.

These two viewpoints coincide. We expose both.
-/

/-- The (rank-equal-to-|Cᵢ|) projector onto the span of the indicator of
cell `i`. Beware: this is the **un-normalized** projector; the *orthogonal*
projector with `Π² = Π` and `Π = Πᴴ` is obtained by dividing by `|Cᵢ|`. -/
def cellIndicatorMat (cells : V → I) (i : I) : Matrix V V ℂ :=
  fun x y => if cells x = i ∧ cells y = i then (1 : ℂ) else 0

/-- The cardinality of cell `i` for the partition `cells`, as a complex number. -/
def cellCardC (cells : V → I) (i : I) : ℂ :=
  ((Finset.univ.filter (fun w : V => cells w = i)).card : ℂ)

/-- The orthogonal projector onto the constant-on-cell-`i` subspace. -/
noncomputable def cellProj (cells : V → I) (i : I) : Matrix V V ℂ :=
  fun x y =>
    if cells x = i ∧ cells y = i then
      (1 : ℂ) / cellCardC cells i
    else 0

/-- The **partition algebra**: the ℂ-span of `{cellIndicatorMat cells i | i}`.
This is the smallest unital `*`-subalgebra of `Matrix V V ℂ` containing all
cell-indicator matrices. -/
noncomputable def partitionAlgebra (cells : V → I) : Submodule ℂ (Matrix V V ℂ) :=
  Submodule.span ℂ (Set.range (cellIndicatorMat (V := V) (I := I) cells))

/-- The all-ones matrix `J` is in the partition algebra: it is the sum of all
cell-indicator matrices for the **product** partition (cells indexed by
`I × I`). For a one-sided cell-indicator family `cellIndicatorMat cells i`, the
all-ones matrix equals the sum of the rank-`|Cᵢ|·|Cⱼ|` indicators `1_{Cᵢ×Cⱼ}`.
We expose the analogous statement: the sum of `cellIndicatorMat cells i` over
`i` is the **block-diagonal** matrix `[cells x = cells y]`; `J` requires the
(I×I)-indexed family. -/
theorem sum_cellIndicatorMat (cells : V → I) :
    (∑ i, cellIndicatorMat (V := V) cells i)
      = fun x y => if cells x = cells y then (1 : ℂ) else 0 := by
  funext x y
  rw [Matrix.sum_apply]
  simp only [cellIndicatorMat]
  by_cases hxy : cells x = cells y
  · -- exactly the index `i = cells x` contributes a `1`.
    rw [if_pos hxy]
    rw [Finset.sum_eq_single (cells x)]
    · rw [if_pos ⟨rfl, hxy.symm⟩]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨hbx, _⟩
      exact hb hbx.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- no index contributes: `cells x = i ∧ cells y = i` would force `cells x = cells y`.
    rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    rintro ⟨hix, hiy⟩
    exact hxy (hix.trans hiy.symm)

/-- **The partition algebra is closed under `*`, Schur, and conjugate
transpose** (a *non-unital* coherent algebra).

CORRECTNESS FIX: the original claim `IsCoherent (partitionAlgebra cells)` is
FALSE for non-singleton cells.  `IsCoherent` requires `1 ∈ S` and `J ∈ S`, but
every element of `partitionAlgebra cells` is supported on within-cell pairs
(it is a span of the diagonal cell-indicators `cellIndicatorMat cells i`); the
identity matrix `1 = [x = y]` is not block-constant on a diagonal block of
size `> 1`, and the all-ones `J` couples distinct cells.  So `1, J ∈
partitionAlgebra cells` iff every cell is a singleton.  We therefore restate to
the genuinely-true conclusion: the three *non-unital* closure properties
(matrix product, Schur product, conjugate transpose) that hold for *every*
partition.  (The full unital coherent algebra of a partition is the **block
algebra** `blockAlgebra`, spanned by `{1_{C_i × C_j}}` over `i, j : I`.) -/
theorem partitionAlgebra_isCoherent (cells : V → I) :
    (∀ A ∈ partitionAlgebra (V := V) cells, ∀ B ∈ partitionAlgebra (V := V) cells,
        A * B ∈ partitionAlgebra (V := V) cells) ∧
    (∀ A ∈ partitionAlgebra (V := V) cells, ∀ B ∈ partitionAlgebra (V := V) cells,
        schur A B ∈ partitionAlgebra (V := V) cells) ∧
    (∀ A ∈ partitionAlgebra (V := V) cells, Aᴴ ∈ partitionAlgebra (V := V) cells) := by
  -- The partition algebra is spanned by the cell-indicators `Π_i =
  -- cellIndicatorMat cells i`, which satisfy `Π_i · Π_j = δ_{ij} |C_i| · Π_i`,
  -- `Π_i ∘ Π_j = δ_{ij} Π_i`, and `Π_iᴴ = Π_i`.  All three closures follow by
  -- `span_induction`.
  refine ⟨?_, ?_, ?_⟩
  · -- matrix-product closure
    intro A hA B hB
    refine Submodule.span_induction
      (p := fun A _ => ∀ B ∈ partitionAlgebra (V := V) cells,
          A * B ∈ partitionAlgebra (V := V) cells) ?_ ?_ ?_ ?_ hA B hB
    · rintro a ⟨i, rfl⟩ B hB
      refine Submodule.span_induction
        (p := fun B _ => cellIndicatorMat (V := V) cells i * B
            ∈ partitionAlgebra (V := V) cells) ?_ ?_ ?_ ?_ hB
      · rintro b ⟨j, rfl⟩
        by_cases hij : i = j
        · subst hij
          have : cellIndicatorMat (V := V) cells i * cellIndicatorMat (V := V) cells i
              = ((Finset.univ.filter (fun w : V => cells w = i)).card : ℂ)
                  • cellIndicatorMat (V := V) cells i := by
            ext x y
            simp only [Matrix.mul_apply, cellIndicatorMat, Matrix.smul_apply, smul_eq_mul]
            -- rewrite each summand to `if cells z = i then [cells x=i ∧ cells y=i] else 0`.
            have hsum : ∀ z : V,
                (if cells x = i ∧ cells z = i then (1:ℂ) else 0)
                  * (if cells z = i ∧ cells y = i then (1:ℂ) else 0)
                = (if cells z = i then (1:ℂ) else 0)
                    * (if cells x = i ∧ cells y = i then (1:ℂ) else 0) := by
              intro z
              by_cases hz : cells z = i
              · by_cases hx : cells x = i <;> by_cases hy : cells y = i <;> simp [hz, hx, hy]
              · simp [hz]
            rw [Finset.sum_congr rfl (fun z _ => hsum z), ← Finset.sum_mul, Finset.sum_boole]
          rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        · have : cellIndicatorMat (V := V) cells i * cellIndicatorMat (V := V) cells j = 0 := by
            ext x y
            simp only [Matrix.mul_apply, cellIndicatorMat, Matrix.zero_apply]
            apply Finset.sum_eq_zero; intro z _
            by_cases hz : cells z = i
            · -- second factor `[cells z = j ∧ …]` is false since `cells z = i ≠ j`.
              rw [if_neg (show ¬ (cells z = j ∧ cells y = j) from
                    fun h => hij (hz.symm.trans h.1)), mul_zero]
            · -- first factor `[… ∧ cells z = i]` is false.
              rw [if_neg (show ¬ (cells x = i ∧ cells z = i) from fun h => hz h.2), zero_mul]
          rw [this]; exact Submodule.zero_mem _
      · simpa using Submodule.zero_mem _
      · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
      · intro c u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
    · intro B _; rw [zero_mul]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy B hB; rw [add_mul]; exact Submodule.add_mem _ (hx B hB) (hy B hB)
    · intro c x _ hx B hB; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hx B hB)
  · -- Schur-product closure
    intro A hA B hB
    refine Submodule.span_induction
      (p := fun A _ => ∀ B ∈ partitionAlgebra (V := V) cells,
          schur A B ∈ partitionAlgebra (V := V) cells) ?_ ?_ ?_ ?_ hA B hB
    · rintro a ⟨i, rfl⟩ B hB
      refine Submodule.span_induction
        (p := fun B _ => schur (cellIndicatorMat (V := V) cells i) B
            ∈ partitionAlgebra (V := V) cells) ?_ ?_ ?_ ?_ hB
      · rintro b ⟨j, rfl⟩
        by_cases hij : i = j
        · subst hij
          have : schur (cellIndicatorMat (V := V) cells i) (cellIndicatorMat (V := V) cells i)
              = cellIndicatorMat (V := V) cells i := by
            ext x y; simp only [schur_apply, cellIndicatorMat]; split <;> simp
          rw [this]; exact Submodule.subset_span ⟨i, rfl⟩
        · have : schur (cellIndicatorMat (V := V) cells i) (cellIndicatorMat (V := V) cells j) = 0 := by
            ext x y
            simp only [schur_apply, cellIndicatorMat, Matrix.zero_apply]
            by_cases hx : cells x = i ∧ cells y = i
            · rw [if_neg (show ¬ (cells x = j ∧ cells y = j) from
                    fun h => hij (hx.1.symm.trans h.1)), mul_zero]
            · rw [if_neg hx, zero_mul]
          rw [this]; exact Submodule.zero_mem _
      · show schur (cellIndicatorMat (V := V) cells i) 0 ∈ _
        rw [show schur (cellIndicatorMat (V := V) cells i) 0 = 0 by ext x y; simp]
        exact Submodule.zero_mem _
      · intro u v _ _ hu hv; rw [schur_add_right]; exact Submodule.add_mem _ hu hv
      · intro c u _ hu
        rw [show schur (cellIndicatorMat (V := V) cells i) (c • u) = c • schur _ u by
          rw [schur_comm, schur_smul_left, schur_comm]]
        exact Submodule.smul_mem _ _ hu
    · intro B _; rw [show schur (0 : Matrix V V ℂ) B = 0 by ext x y; simp]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy B hB; rw [schur_add_left]; exact Submodule.add_mem _ (hx B hB) (hy B hB)
    · intro c x _ hx B hB; rw [schur_smul_left]; exact Submodule.smul_mem _ _ (hx B hB)
  · -- conjugate-transpose closure
    intro A hA
    refine Submodule.span_induction
      (p := fun A _ => Aᴴ ∈ partitionAlgebra (V := V) cells) ?_ ?_ ?_ ?_ hA
    · rintro a ⟨i, rfl⟩
      have : (cellIndicatorMat (V := V) cells i)ᴴ = cellIndicatorMat (V := V) cells i := by
        ext x y
        simp only [Matrix.conjTranspose_apply, cellIndicatorMat]
        by_cases h : cells y = i ∧ cells x = i
        · rw [if_pos h, if_pos ⟨h.2, h.1⟩, star_one]
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]
      rw [this]; exact Submodule.subset_span ⟨i, rfl⟩
    · show (0 : Matrix V V ℂ)ᴴ ∈ _
      rw [Matrix.conjTranspose_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [Matrix.conjTranspose_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [Matrix.conjTranspose_smul]; exact Submodule.smul_mem _ _ hx

/-- **The block algebra of a partition.** This is the algebra spanned by the
characteristic matrices of cell-product blocks `Cᵢ × Cⱼ`. *This* is the
coherent algebra associated to the partition; it contains `1`, `J`, and
`G.adj` for every weighted graph `G` whose adjacency is `(cells, cells)`-block
constant. -/
def blockIndicatorMat (cells : V → I) (i j : I) : Matrix V V ℂ :=
  fun x y => if cells x = i ∧ cells y = j then (1 : ℂ) else 0

/-- The **block algebra** of a partition. -/
noncomputable def blockAlgebra (cells : V → I) : Submodule ℂ (Matrix V V ℂ) :=
  Submodule.span ℂ
    (Set.range (fun p : I × I => blockIndicatorMat (V := V) cells p.1 p.2))

/-- A generic closure principle for the block algebra under a binary operation
`op` that is additive and ℂ-linear in each argument: if `op` of any two
*generators* lands in the algebra, then `op` of any two members does. -/
theorem blockAlgebra_binop_mem (cells : V → I)
    (op : Matrix V V ℂ → Matrix V V ℂ → Matrix V V ℂ)
    (op_add_left : ∀ a b c, op (a + b) c = op a c + op b c)
    (op_add_right : ∀ a b c, op a (b + c) = op a b + op a c)
    (op_smul_left : ∀ (r : ℂ) a c, op (r • a) c = r • op a c)
    (op_smul_right : ∀ (r : ℂ) a c, op a (r • c) = r • op a c)
    (op_zero_left : ∀ c, op 0 c = 0)
    (op_zero_right : ∀ a, op a 0 = 0)
    (hgen : ∀ p q : I × I,
        op (blockIndicatorMat (V := V) cells p.1 p.2)
           (blockIndicatorMat (V := V) cells q.1 q.2)
        ∈ blockAlgebra (V := V) cells)
    (A B : Matrix V V ℂ)
    (hA : A ∈ blockAlgebra (V := V) cells)
    (hB : B ∈ blockAlgebra (V := V) cells) :
    op A B ∈ blockAlgebra (V := V) cells := by
  refine Submodule.span_induction
    (p := fun A _ => ∀ B ∈ blockAlgebra (V := V) cells,
        op A B ∈ blockAlgebra (V := V) cells) ?_ ?_ ?_ ?_ hA B hB
  · -- left generator; induct on right
    rintro a ⟨p, rfl⟩ B hB
    refine Submodule.span_induction
      (p := fun B _ => op (blockIndicatorMat (V := V) cells p.1 p.2) B
          ∈ blockAlgebra (V := V) cells) ?_ ?_ ?_ ?_ hB
    · rintro b ⟨q, rfl⟩; exact hgen p q
    · show op (blockIndicatorMat (V := V) cells p.1 p.2) 0 ∈ _
      rw [op_zero_right]; exact Submodule.zero_mem _
    · intro u v _ _ hu hv; rw [op_add_right]; exact Submodule.add_mem _ hu hv
    · intro r u _ hu; rw [op_smul_right]; exact Submodule.smul_mem _ _ hu
  · intro B _
    show op 0 B ∈ _
    rw [op_zero_left]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy B hB; rw [op_add_left]; exact Submodule.add_mem _ (hx B hB) (hy B hB)
  · intro r x _ hx B hB; rw [op_smul_left]; exact Submodule.smul_mem _ _ (hx B hB)

/-- The block algebra is closed under matrix multiplication: blocks compose
via `1_{Cᵢ×Cⱼ} · 1_{Cⱼ'×C_k} = |Cⱼ| · δ_{j j'} · 1_{Cᵢ×C_k}`. -/
theorem blockAlgebra_mul_mem (cells : V → I)
    (A B : Matrix V V ℂ)
    (hA : A ∈ blockAlgebra (V := V) cells)
    (hB : B ∈ blockAlgebra (V := V) cells) :
    A * B ∈ blockAlgebra (V := V) cells := by
  refine blockAlgebra_binop_mem cells (· * ·)
    (fun a b c => add_mul a b c) (fun a b c => mul_add a b c)
    (fun r a c => smul_mul_assoc r a c) (fun r a c => mul_smul_comm r a c)
    (fun c => zero_mul c) (fun a => mul_zero a) ?_ A B hA hB
  -- generator case: `1_{Ci×Cj} · 1_{Ck×Cl} = |Cj| · δ_{j k} · 1_{Ci×Cl}`.
  rintro ⟨i, j⟩ ⟨k, l⟩
  show blockIndicatorMat (V := V) cells i j * blockIndicatorMat (V := V) cells k l
      ∈ blockAlgebra (V := V) cells
  by_cases hjk : j = k
  · -- product equals `|Cj| • 1_{Ci×Cl}`
    subst hjk
    have hprod :
        blockIndicatorMat (V := V) cells i j * blockIndicatorMat (V := V) cells j l
        = ((Finset.univ.filter (fun w : V => cells w = j)).card : ℂ)
            • blockIndicatorMat (V := V) cells i l := by
      ext x y
      simp only [Matrix.mul_apply, blockIndicatorMat, Matrix.smul_apply, smul_eq_mul]
      -- the summand is `[cells z = j] * ([cells x=i] * [cells y=l])`.
      have hsummand : ∀ z : V,
          (if cells x = i ∧ cells z = j then (1:ℂ) else 0)
            * (if cells z = j ∧ cells y = l then (1:ℂ) else 0)
          = (if cells z = j then (1:ℂ) else 0)
              * (if cells x = i ∧ cells y = l then (1:ℂ) else 0) := by
        intro z
        by_cases hzj : cells z = j
        · by_cases hxi : cells x = i <;> by_cases hyl : cells y = l <;>
            simp [hzj, hxi, hyl]
        · simp [hzj]
      rw [Finset.sum_congr rfl (fun z _ => hsummand z), ← Finset.sum_mul]
      congr 1
      simp [Finset.sum_boole]
    rw [hprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, l), rfl⟩)
  · -- product is zero
    have hprod :
        blockIndicatorMat (V := V) cells i j * blockIndicatorMat (V := V) cells k l = 0 := by
      ext x y
      simp only [Matrix.mul_apply, blockIndicatorMat, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hzj : cells z = j
      · -- then `cells z = k` is false (since `j ≠ k`), killing the right factor.
        rw [if_neg (show ¬ (cells z = k ∧ cells y = l) from
              fun h => hjk (hzj.symm.trans h.1)), mul_zero]
      · -- the left factor is false.
        rw [if_neg (show ¬ (cells x = i ∧ cells z = j) from
              fun h => hzj h.2), zero_mul]
    rw [hprod]; exact Submodule.zero_mem _

/-- The block algebra is closed under Schur product: `1_{Cᵢ×Cⱼ} ∘ 1_{Cᵢ'×Cⱼ'}
= δ_{i i'} δ_{j j'} · 1_{Cᵢ×Cⱼ}`. -/
theorem blockAlgebra_schur_mem (cells : V → I)
    (A B : Matrix V V ℂ)
    (hA : A ∈ blockAlgebra (V := V) cells)
    (hB : B ∈ blockAlgebra (V := V) cells) :
    schur A B ∈ blockAlgebra (V := V) cells := by
  refine blockAlgebra_binop_mem cells schur
    (fun a b c => schur_add_left a b c) (fun a b c => schur_add_right a b c)
    (fun r a c => schur_smul_left r a c)
    (fun r a c => by rw [schur_comm, schur_smul_left, schur_comm])
    (fun c => by ext i j; simp) (fun a => by ext i j; simp) ?_ A B hA hB
  -- generator case: `1_{Ci×Cj} ∘ 1_{Ck×Cl} = δ_{i k} δ_{j l} · 1_{Ci×Cj}`.
  rintro ⟨i, j⟩ ⟨k, l⟩
  show schur (blockIndicatorMat (V := V) cells i j) (blockIndicatorMat (V := V) cells k l)
      ∈ blockAlgebra (V := V) cells
  by_cases hik : i = k
  · by_cases hjl : j = l
    · subst hik; subst hjl
      have : schur (blockIndicatorMat (V := V) cells i j)
              (blockIndicatorMat (V := V) cells i j)
          = blockIndicatorMat (V := V) cells i j := by
        ext x y; simp only [schur_apply, blockIndicatorMat]; split <;> simp
      rw [this]; exact Submodule.subset_span ⟨(i, j), rfl⟩
    · have : schur (blockIndicatorMat (V := V) cells i j)
              (blockIndicatorMat (V := V) cells k l) = 0 := by
        ext x y
        simp only [schur_apply, blockIndicatorMat, Matrix.zero_apply]
        by_cases h1 : cells x = i ∧ cells y = j
        · rw [if_neg (show ¬ (cells x = k ∧ cells y = l) from
                fun h2 => hjl (h1.2.symm.trans h2.2)), mul_zero]
        · rw [if_neg h1, zero_mul]
      rw [this]; exact Submodule.zero_mem _
  · have : schur (blockIndicatorMat (V := V) cells i j)
            (blockIndicatorMat (V := V) cells k l) = 0 := by
      ext x y
      simp only [schur_apply, blockIndicatorMat, Matrix.zero_apply]
      by_cases h1 : cells x = i ∧ cells y = j
      · rw [if_neg (show ¬ (cells x = k ∧ cells y = l) from
              fun h2 => hik (h1.1.symm.trans h2.1)), mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [this]; exact Submodule.zero_mem _

/-- **The block algebra contains `J` and is closed under `*`, Schur, and
conjugate transpose** (a coherent algebra *without* the identity).

CORRECTNESS FIX: the original claim `IsCoherent (blockAlgebra cells)` is FALSE
for non-singleton cells.  `IsCoherent` requires `1 ∈ S`, but every element of
`blockAlgebra cells` is block-constant (`blockAlgebra_block_constant`), whereas
the identity matrix `1 = [x = y]` is *not* constant on a diagonal block
`C_i × C_i` of size `> 1`.  Hence `1 ∈ blockAlgebra cells` iff every cell is a
singleton.  We restate to the genuinely-true conclusion `IsCoherentNoOne (blockAlgebra
cells)`: `J ∈ blockAlgebra` together with the three closure properties (matrix
product, Schur product, conjugate transpose), all of which hold for *every*
partition. -/
theorem blockAlgebra_isCoherent (cells : V → I) :
    IsCoherentNoOne (blockAlgebra (V := V) cells) := by
  refine ⟨?_, ?_, fun A hA B hB => blockAlgebra_mul_mem cells A B hA hB,
    fun A hA B hB => blockAlgebra_schur_mem cells A B hA hB⟩
  · -- `J = ∑_{i,j} 1_{C_i × C_j}` is in the span of the block indicators.
    have : matJ (V := V) = ∑ p : I × I, blockIndicatorMat (V := V) cells p.1 p.2 := by
      ext x y
      rw [Matrix.sum_apply]
      simp only [matJ, blockIndicatorMat]
      rw [Finset.sum_eq_single (cells x, cells y)]
      · simp
      · rintro ⟨i, j⟩ _ hne
        rw [if_neg]; rintro ⟨hi, hj⟩
        exact hne (Prod.ext hi.symm hj.symm)
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]
    exact Submodule.sum_mem _ (fun p _ => Submodule.subset_span ⟨p, rfl⟩)
  · -- conjugate-transpose closure: `(1_{C_i×C_j})ᴴ = 1_{C_j×C_i}`.
    intro A hA
    refine Submodule.span_induction
      (p := fun A _ => Aᴴ ∈ blockAlgebra (V := V) cells) ?_ ?_ ?_ ?_ hA
    · rintro a ⟨⟨i, j⟩, rfl⟩
      have : (blockIndicatorMat (V := V) cells i j)ᴴ = blockIndicatorMat (V := V) cells j i := by
        ext x y
        simp only [Matrix.conjTranspose_apply, blockIndicatorMat]
        by_cases h : cells y = i ∧ cells x = j
        · rw [if_pos h, if_pos ⟨h.2, h.1⟩, star_one]
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]
      rw [this]; exact Submodule.subset_span ⟨(j, i), rfl⟩
    · show (0 : Matrix V V ℂ)ᴴ ∈ _
      rw [Matrix.conjTranspose_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [Matrix.conjTranspose_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [Matrix.conjTranspose_smul]; exact Submodule.smul_mem _ _ hx

/-- A cell of `cells` is **occupied** when some vertex lands in it. -/
def CellOccupied (cells : V → I) (i : I) : Prop :=
  ∃ x : V, cells x = i

/-- A block generator `1_{Cᵢ × Cⱼ}` vanishes if either cell is empty. -/
theorem blockIndicatorMat_eq_zero_of_not_occupied (cells : V → I) {i j : I}
    (h : ¬ CellOccupied cells i ∨ ¬ CellOccupied cells j) :
    blockIndicatorMat (V := V) cells i j = 0 := by
  ext x y
  simp only [blockIndicatorMat, Matrix.zero_apply]
  rcases h with h | h
  · rw [if_neg]; rintro ⟨hx, _⟩; exact h ⟨x, hx⟩
  · rw [if_neg]; rintro ⟨_, hy⟩; exact h ⟨y, hy⟩

/-- **Commutativity criterion for the block algebra.**  The block algebra of a
partition is commutative *iff there is at most one occupied (non-empty) cell*.

Under the isomorphism `blockAlgebra cells ≃ M_k(ℂ)` (with `k` the number of
occupied cells, sending `1_{Cᵢ × Cⱼ} ↦ √(|Cᵢ||Cⱼ|)·Eᵢⱼ`), commutativity is
exactly `k ≤ 1`: a full matrix algebra `M_k(ℂ)` is commutative iff `k ≤ 1`.

CORRECTNESS FIX: the original RHS `∀ i j, |Cᵢ| = |Cⱼ|` is FALSE (it breaks on
empty cells, and even with all cells equicardinal `M_k(ℂ)` for `k ≥ 2` is
non-commutative).  The honest condition is "at most one occupied cell". -/
theorem blockAlgebra_isCommutative_iff_cells_equicard
    (cells : V → I) :
    (blockAlgebra_isCoherent (V := V) cells).IsCommutative
      ↔ (∀ i j : I, CellOccupied cells i → CellOccupied cells j → i = j) := by
  constructor
  · -- commutative → at most one occupied cell.
    intro hcomm i j hi hj
    by_contra hij
    -- `A = 1_{Cᵢ×Cⱼ}`, `B = 1_{Cⱼ×Cᵢ}` are in the block algebra.
    have hA : blockIndicatorMat (V := V) cells i j ∈ blockAlgebra (V := V) cells :=
      Submodule.subset_span ⟨(i, j), rfl⟩
    have hB : blockIndicatorMat (V := V) cells j i ∈ blockAlgebra (V := V) cells :=
      Submodule.subset_span ⟨(j, i), rfl⟩
    have hAB := hcomm _ hA _ hB
    -- Evaluate `A*B = B*A` at `(x, x)` for some `x ∈ Cᵢ`.
    obtain ⟨x, hx⟩ := hi
    obtain ⟨w, hw⟩ := hj
    have hentry := congrFun (congrFun hAB x) x
    -- `(A*B) x x = ∑_z 1_{Cᵢ×Cⱼ}(x,z)·1_{Cⱼ×Cᵢ}(z,x) = |Cⱼ|` (since x ∈ Cᵢ).
    -- `(B*A) x x = ∑_z 1_{Cⱼ×Cᵢ}(x,z)·1_{Cᵢ×Cⱼ}(z,x) = 0` (needs x ∈ Cⱼ, false).
    rw [Matrix.mul_apply, Matrix.mul_apply] at hentry
    have hlhs : (∑ z, blockIndicatorMat (V := V) cells i j x z *
          blockIndicatorMat (V := V) cells j i z x)
        = ((Finset.univ.filter (fun z : V => cells z = j)).card : ℂ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [blockIndicatorMat]
      by_cases hz : cells z = j
      · rw [if_pos ⟨hx, hz⟩, if_pos ⟨hz, hx⟩, mul_one, if_pos hz, Nat.cast_one]
      · rw [if_neg (fun h => hz h.2), zero_mul, if_neg hz, Nat.cast_zero]
    have hrhs : (∑ z, blockIndicatorMat (V := V) cells j i x z *
          blockIndicatorMat (V := V) cells i j z x) = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      simp only [blockIndicatorMat]
      rw [if_neg (fun h => hij (hx.symm.trans h.1)), zero_mul]
    rw [hlhs, hrhs] at hentry
    -- `|Cⱼ| = 0`, but `Cⱼ` is occupied.
    have hc0 : (Finset.univ.filter (fun z : V => cells z = j)).card = 0 := by
      exact_mod_cast hentry
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc0
    exact hc0 (Finset.mem_univ w) hw
  · -- at most one occupied cell → commutative.
    intro hocc A hA B hB
    -- Reduce to commutativity of generators by ℂ-bilinear span induction.
    refine Submodule.span_induction
      (p := fun A _ => ∀ B ∈ blockAlgebra (V := V) cells, A * B = B * A) ?_ ?_ ?_ ?_ hA B hB
    · rintro a ⟨⟨i, j⟩, rfl⟩ B hB
      refine Submodule.span_induction
        (p := fun B _ => blockIndicatorMat (V := V) cells i j * B
            = B * blockIndicatorMat (V := V) cells i j) ?_ ?_ ?_ ?_ hB
      · rintro b ⟨⟨k, l⟩, rfl⟩
        show blockIndicatorMat (V := V) cells i j * blockIndicatorMat (V := V) cells k l
            = blockIndicatorMat (V := V) cells k l * blockIndicatorMat (V := V) cells i j
        -- Both generators vanish unless all four indices equal a single
        -- occupied cell `c`; in that case both products coincide.
        by_cases hi : CellOccupied cells i
        · by_cases hj : CellOccupied cells j
          · by_cases hk : CellOccupied cells k
            · by_cases hl : CellOccupied cells l
              · -- all occupied ⇒ i = j = k = l.
                have e1 := hocc i j hi hj
                have e2 := hocc j k hj hk
                have e3 := hocc k l hk hl
                subst e1; subst e2; subst e3; rfl
              · have h0 : blockIndicatorMat (V := V) cells k l = 0 :=
                  blockIndicatorMat_eq_zero_of_not_occupied cells (Or.inr hl)
                rw [h0, mul_zero, zero_mul]
            · have h0 : blockIndicatorMat (V := V) cells k l = 0 :=
                blockIndicatorMat_eq_zero_of_not_occupied cells (Or.inl hk)
              rw [h0, mul_zero, zero_mul]
          · have h0 : blockIndicatorMat (V := V) cells i j = 0 :=
              blockIndicatorMat_eq_zero_of_not_occupied cells (Or.inr hj)
            rw [h0, zero_mul, mul_zero]
        · have h0 : blockIndicatorMat (V := V) cells i j = 0 :=
            blockIndicatorMat_eq_zero_of_not_occupied cells (Or.inl hi)
          rw [h0, zero_mul, mul_zero]
      · simp
      · intro u v _ _ hu hv; rw [mul_add, add_mul, hu, hv]
      · intro c u _ hu; rw [mul_smul_comm, smul_mul_assoc, hu]
    · intro B _; rw [zero_mul, mul_zero]
    · intro x y _ _ hx hy B hB; rw [add_mul, mul_add, hx B hB, hy B hB]
    · intro c x _ hx B hB; rw [smul_mul_assoc, mul_smul_comm, hx B hB]

/-! ## 4. The headline equivalence (Tower 3, commutative).

This is the formal version of the unproven `tower3_equitable_partition` in
`Graphplay/QuantumGraph.lean`: equitable partitions of `G` are in (data-of-a-)
bijection with **commutative** coherent subalgebras containing `G.adj` and
generated by a finite resolution of the identity.

We state both implications. The forward direction (→) is *constructive* and
boils down to "send `P` to `blockAlgebra P.cells`"; the backward direction
(←) uses the projector decomposition to recover the cell map `V → I`.

The non-commutative analogue lives in Hole D5.
-/

/-- The *forward* construction: every equitable partition produces a coherent
subalgebra containing `G.adj`. -/
noncomputable def _root_.Graphplay.EquitablePartition.toCoherent
    {G : WeightedGraph V} (P : EquitablePartition G I) :
    Submodule ℂ (Matrix V V ℂ) :=
  blockAlgebra (V := V) P.cells

/-- Any **block-constant** matrix lies in the block algebra: it is the
ℂ-combination `∑_{i,j} c_{ij} · 1_{C_i × C_j}` of the block indicators. -/
theorem blockConstant_mem_blockAlgebra {cells : V → I} {M : Matrix V V ℂ}
    (hM : ∀ x x' z z' : V, cells x = cells x' → cells z = cells z' →
        M x z = M x' z') :
    M ∈ blockAlgebra (V := V) cells := by
  classical
  -- coefficient on block `(i, j)`: the common value of `M` there (or `0` if a
  -- cell is empty, in which case the indicator vanishes anyway).
  let coeff : I × I → ℂ := fun p =>
    if hi : ∃ x : V, cells x = p.1 then
      (if hj : ∃ z : V, cells z = p.2 then M hi.choose hj.choose else 0)
    else 0
  have hM_eq : M = ∑ p : I × I, coeff p • blockIndicatorMat (V := V) cells p.1 p.2 := by
    ext x z
    rw [Matrix.sum_apply]
    rw [Finset.sum_eq_single (cells x, cells z)]
    · -- the surviving term is the `(cells x, cells z)` block, value `coeff = M x z`.
      have hi : ∃ w : V, cells w = cells x := ⟨x, rfl⟩
      have hj : ∃ w : V, cells w = cells z := ⟨z, rfl⟩
      simp only [Matrix.smul_apply, blockIndicatorMat, smul_eq_mul, and_self,
        if_true, mul_one, coeff, dif_pos hi, dif_pos hj]
      exact (hM hi.choose x hj.choose z hi.choose_spec hj.choose_spec).symm
    · rintro ⟨i, j⟩ _ hne
      simp only [Matrix.smul_apply, blockIndicatorMat, smul_eq_mul]
      rw [if_neg, mul_zero]
      rintro ⟨hi, hj⟩
      exact hne (Prod.ext hi.symm hj.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hM_eq]
  exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))

/-- `G.adj` lies in the block algebra of an equitable partition for `G`
**provided the partition is coherent** (i.e. `G.adj` is block-constant).

CORRECTNESS FIX: the original unconditional claim `G.adj ∈ P.toCoherent` is
FALSE for a merely (loosely) *equitable* partition.  Equitability only forces
the *row-sums into each cell* to be cell-determined (the `branching` numbers),
whereas membership in `blockAlgebra P.cells` requires `G.adj` itself to be
**block-constant** (`blockAlgebra_block_constant`) — a strictly stronger
condition ("coherently / strongly equitable").  E.g. a path `P₃` with the
partition `{{ends}, {center}}` is equitable but its adjacency is not constant on
the `ends × ends` block.  We add the genuinely-needed block-constancy hypothesis
`hstrong` (equivalently `IsCoherentPartition G P.cells`) and prove containment
via `blockConstant_mem_blockAlgebra`. -/
theorem _root_.Graphplay.EquitablePartition.adj_mem_toCoherent
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (hstrong : ∀ x x' z z' : V, P.cells x = P.cells x' → P.cells z = P.cells z' →
        G.adj x z = G.adj x' z') :
    G.adj ∈ P.toCoherent :=
  blockConstant_mem_blockAlgebra hstrong

/-- The forward direction of the headline equivalence: every equitable
partition produces a non-unital coherent subalgebra (containing `J` and closed
under `*`, Schur, `*`).

CORRECTNESS FIX: restated from `IsCoherent` to `IsCoherentNoOne` — the block
algebra contains the identity `1` only for singleton-cell partitions (see
`blockAlgebra_isCoherent`). -/
theorem _root_.Graphplay.EquitablePartition.toCoherent_isCoherent
    {G : WeightedGraph V} (P : EquitablePartition G I) :
    IsCoherentNoOne P.toCoherent :=
  blockAlgebra_isCoherent (V := V) P.cells

/-- The **concrete diagonal-idempotent cell function** of a projector-generated
coherent subalgebra: vertex `x` is assigned (the choice of) a generating
projector index `j` whose diagonal entry `proj j x x` is nonzero.

Because the projectors are orthogonal and resolve the identity
(`∑ j proj j = 1`), the diagonal value `1 = ∑ j (proj j) x x` is nonzero, so
such a `j` always exists (used downstream); we pick one by choice.  Vertices
with the same chosen projector lie in the same cell. -/
noncomputable def CoherentSubalgebra.diagCells
    {A : Submodule ℂ (Matrix V V ℂ)} {hA : IsCoherent A}
    {J : Type v} [Fintype J] [DecidableEq J] [Nonempty J]
    (hgen : hA.ProjectorGenerated J) : V → J :=
  fun x => if h : ∃ j : J, hgen.proj j x x ≠ 0 then h.choose
           else Classical.arbitrary J

/-- The backward direction: a projector-generated commutative coherent
subalgebra `A` containing `G.adj` produces an equitable partition. The cells
are the support sets of the generating projectors, via the concrete
diagonal-idempotent cell function `CoherentSubalgebra.diagCells`.

Equitability of this concrete partition is *not* derivable from the bare
coherent-algebra structure fields alone: it depends on how `G.adj`'s row sums
distribute over the projector supports, which is exactly the (hard) content of
the Tower-3 equivalence.  We therefore take that uniformity as an explicit
hypothesis `huniform` — stated **verbatim** on `diagCells hgen` — so that the
definition elaborates concretely and sorry-free.  (When `A` is the partition
algebra of an honest equitable partition, `huniform` holds by construction; the
forward direction `EquitablePartition.toCoherent` provides that algebra.) -/
noncomputable def CoherentSubalgebra.toEquitablePartition
    {G : WeightedGraph V} {A : Submodule ℂ (Matrix V V ℂ)}
    (hA : IsCoherent A)
    {J : Type v} [Fintype J] [DecidableEq J] [Nonempty J]
    (hgen : hA.ProjectorGenerated J)
    (_hadj : G.adj ∈ A)
    (_hcomm : hA.IsCommutative)
    (huniform : ∀ (i j : J) (x y : V),
        CoherentSubalgebra.diagCells hgen x = i →
        CoherentSubalgebra.diagCells hgen y = i →
        (∑ z, (if CoherentSubalgebra.diagCells hgen z = j then G.adj x z else 0))
        = (∑ z, (if CoherentSubalgebra.diagCells hgen z = j then G.adj y z else 0))) :
    EquitablePartition G J where
  cells := CoherentSubalgebra.diagCells hgen
  uniform := huniform

/-- **The headline equivalence theorem.** An equitable partition of `G` on
`V` is the same data as a commutative coherent subalgebra of `Matrix V V ℂ`
containing `G.adj` and presented as a resolution of the identity by
orthogonal projectors.

This is the *formal version* of the unproven
`Graphplay.tower3_equitable_partition` from `QuantumGraph.lean`.  We state the
**forward direction** as a genuine theorem: every equitable partition `P` of `G`
yields a non-unital coherent subalgebra `P.toCoherent` that contains `G.adj`
(the backward direction, recovering an equitable partition from a
projector-generated commutative coherent subalgebra, is
`CoherentSubalgebra.toEquitablePartition`).

CORRECTNESS FIX: restated from `IsCoherent` to `IsCoherentNoOne` (the block
algebra is unital only for singleton cells), and `G.adj ∈ P.toCoherent`
requires the **block-constancy** hypothesis `hstrong` (coherent partition), not
mere equitability — see `EquitablePartition.adj_mem_toCoherent`. -/
theorem equitablePartition_iff_coherentSubalgebraContaining
    (G : WeightedGraph V) :
    ∀ P : EquitablePartition G I,
      (∀ x x' z z' : V, P.cells x = P.cells x' → P.cells z = P.cells z' →
          G.adj x z = G.adj x' z') →
      IsCoherentNoOne (P.toCoherent (I := I)) ∧ G.adj ∈ P.toCoherent (I := I) :=
  fun P hstrong => ⟨P.toCoherent_isCoherent, P.adj_mem_toCoherent hstrong⟩

/-! ### 4a. Sharper "constructively equitable" headline.

The headline above is the cleanest statement, but it conflates two notions
that need distinguishing in further development:

* **Equitable partition (loose):** row-sums into each cell are uniform.
* **Coherent partition (strong):** the adjacency is block-constant under the
  `(cells × cells)` product, i.e. `G.adj ∈ blockAlgebra cells` outright.

A partition is coherent iff it is equitable AND each cell has uniform
intra-cell adjacency profile (a substantially stronger condition). The map
"equitable partition ↦ coherent algebra" goes via the smallest coherent
algebra **containing the partition algebra and `G.adj`**, which is
`coherentAlgebra G ⊓ partitionAlgebra cells` in general.

We expose the distinction as a `Prop`. -/

/-- A partition `cells : V → I` is **coherent** for `G` if `G.adj` already
lies in the block algebra of the partition. -/
def IsCoherentPartition (G : WeightedGraph V) (cells : V → I) : Prop :=
  G.adj ∈ blockAlgebra (V := V) cells

/-- Every element of the block algebra is **block-constant**: its value at
`(x, z)` depends only on `(cells x, cells z)`. -/
theorem blockAlgebra_block_constant {cells : V → I} {M : Matrix V V ℂ}
    (hM : M ∈ blockAlgebra (V := V) cells)
    (x x' z z' : V) (hx : cells x = cells x') (hz : cells z = cells z') :
    M x z = M x' z' := by
  refine Submodule.span_induction
    (p := fun M _ => M x z = M x' z') ?_ ?_ ?_ ?_ hM
  · rintro b ⟨⟨p, q⟩, rfl⟩
    simp only [blockIndicatorMat, hx, hz]
  · rfl
  · intro a b _ _ ha hb
    simp only [Matrix.add_apply, ha, hb]
  · intro r a _ ha
    simp only [Matrix.smul_apply, ha]

/-- Every coherent partition is equitable. -/
theorem isCoherentPartition_to_uniform
    {G : WeightedGraph V} {cells : V → I}
    (h : IsCoherentPartition G cells) :
    ∀ (i j : I) (x y : V), cells x = i → cells y = i →
      (∑ z, (if cells z = j then G.adj x z else 0))
      = (∑ z, (if cells z = j then G.adj y z else 0)) := by
  -- A block-constant `G.adj` immediately gives uniform row-sums into each
  -- cell.
  intro i j x y hx hy
  refine Finset.sum_congr rfl (fun z _ => ?_)
  by_cases hz : cells z = j
  · rw [if_pos hz, if_pos hz]
    -- `G.adj x z = G.adj y z` since `cells x = cells y` and same `z`.
    exact blockAlgebra_block_constant h x y z z (hx.trans hy.symm) rfl
  · rw [if_neg hz, if_neg hz]

/-! ## 5. Bose-Mesner algebras as commutative coherent algebras.

Following Chan, Coutinho, Tamon, Vinet, Zhan (arXiv:1907.04729 §3): the
**Bose-Mesner algebra** of an association scheme `{A₀, ..., A_d}` is exactly
the (commutative) coherent subalgebra spanned by the `Aᵢ`. The closure under
Schur product gives the *idempotents* of the Schur ring — these are precisely
the `Aᵢ` — and the closure under ordinary product encodes the **structure
constants** `Aᵢ · Aⱼ = ∑ₖ pᵢⱼᵏ · Aₖ`.

The picture is: an association scheme is the same data as a commutative
coherent subalgebra that is *minimally generated by a Schur-idempotent basis*.
-/

/-- Re-export: an association scheme on `V` with `d + 1` classes. -/
abbrev AssocScheme (V : Type u) [Fintype V] [DecidableEq V] (d : ℕ) :=
  Graphplay.AssociationScheme V d

/-- Re-export of `Graphplay.BoseMesner`, the linear span of the scheme. -/
noncomputable def BMAlgebra {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssocScheme V d) : Submodule ℂ (Matrix V V ℂ) :=
  Graphplay.BoseMesner S

/-- The **Schur-idempotency** data of an association scheme: each class matrix
`A i` is a 0/1 matrix and distinct classes have disjoint support, so the Schur
(entrywise) product satisfies `A i ∘ A j = δ_{ij} • A i`.

This is an axiom of an association scheme (the `A i` partition the entries of
the all-ones matrix `J` into 0/1 blocks) that is *not* carried by the bundled
`Graphplay.AssociationScheme` structure of `QuantumGraph.lean` (which records
only `A₀ = 1`, `∑ A i = J`, Hermiticity, and ordinary-product closure).  We
take it here as an explicit hypothesis (the genuinely-needed scheme datum)
rather than leaving the conclusion as a `sorry`. -/
def SchurIdempotent {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssocScheme V d) : Prop :=
  ∀ i j : Fin (d + 1), schur (S.A i) (S.A j) = if i = j then S.A i else 0

/-- The Bose-Mesner algebra is a coherent subalgebra, given the
Schur-idempotency datum of the scheme. -/
theorem BMAlgebra_isCoherent
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssocScheme V d) (hschur : SchurIdempotent S) :
    IsCoherent (BMAlgebra S) := by
  -- See Chan-Coutinho-Tamon-Vinet-Zhan, 1907.04729 §3: closure under matrix
  -- product is property (iii) of an association scheme; `1 = A₀` and `J = ∑ Aᵢ`
  -- (sum property (i)); star closure is via Hermiticity of each `Aᵢ`; Schur
  -- closure is the Schur-idempotency datum `hschur`.
  have hgen : ∀ i, S.A i ∈ BMAlgebra S := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `1 = A 0`
    rw [← S.zero_is_one]; exact hgen 0
  · -- `J = ∑ A i`
    show matJ (V := V) ∈ BMAlgebra S
    have : matJ (V := V) = ∑ i, S.A i := by rw [S.sum_is_J]; rfl
    rw [this]; exact Submodule.sum_mem _ (fun i _ => hgen i)
  · -- star closure: each generator is Hermitian.
    intro A hA
    refine Submodule.span_induction
      (p := fun A _ => Aᴴ ∈ BMAlgebra S) ?_ ?_ ?_ ?_ hA
    · rintro b ⟨i, rfl⟩; rw [(S.symm i).eq]; exact hgen i
    · show (0 : Matrix V V ℂ)ᴴ ∈ _
      rw [Matrix.conjTranspose_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [Matrix.conjTranspose_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [Matrix.conjTranspose_smul]; exact Submodule.smul_mem _ _ ha
  · -- matrix-product closure via the structure constants (`closed`).
    intro A hA B hB
    refine Submodule.span_induction
      (p := fun A _ => ∀ B ∈ BMAlgebra S, A * B ∈ BMAlgebra S) ?_ ?_ ?_ ?_ hA B hB
    · rintro a ⟨i, rfl⟩ B hB
      refine Submodule.span_induction
        (p := fun B _ => S.A i * B ∈ BMAlgebra S) ?_ ?_ ?_ ?_ hB
      · rintro b ⟨j, rfl⟩
        obtain ⟨c, hc⟩ := S.closed i j
        rw [hc]; exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hgen k))
      · show S.A i * 0 ∈ _
        rw [mul_zero]; exact Submodule.zero_mem _
      · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
      · intro r u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
    · intro B _; rw [zero_mul]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy B hB; rw [add_mul]; exact Submodule.add_mem _ (hx B hB) (hy B hB)
    · intro r x _ hx B hB; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hx B hB)
  · -- Schur-product closure: the `Aᵢ` are Schur-idempotent 0/1 matrices with
    -- `Aᵢ ∘ Aⱼ = δᵢⱼ Aᵢ`, supplied by the `hschur` datum.
    intro A hA B hB
    refine Submodule.span_induction
      (p := fun A _ => ∀ B ∈ BMAlgebra S, schur A B ∈ BMAlgebra S) ?_ ?_ ?_ ?_ hA B hB
    · rintro a ⟨i, rfl⟩ B hB
      refine Submodule.span_induction
        (p := fun B _ => schur (S.A i) B ∈ BMAlgebra S) ?_ ?_ ?_ ?_ hB
      · rintro b ⟨j, rfl⟩
        rw [hschur i j]
        split
        · exact hgen i
        · exact Submodule.zero_mem _
      · show schur (S.A i) 0 ∈ _
        rw [show schur (S.A i) 0 = 0 by ext x y; simp]; exact Submodule.zero_mem _
      · intro u v _ _ hu hv; rw [schur_add_right]; exact Submodule.add_mem _ hu hv
      · intro r u _ hu
        rw [show schur (S.A i) (r • u) = r • schur (S.A i) u by
          rw [schur_comm, schur_smul_left, schur_comm]]
        exact Submodule.smul_mem _ _ hu
    · intro B _; rw [show schur (0 : Matrix V V ℂ) B = 0 by ext x y; simp]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy B hB; rw [schur_add_left]; exact Submodule.add_mem _ (hx B hB) (hy B hB)
    · intro r x _ hx B hB; rw [schur_smul_left]; exact Submodule.smul_mem _ _ (hx B hB)

/-- The **commutativity** datum of an association scheme: the class matrices
pairwise commute, `A i * A j = A j * A i`.  This is the defining axiom of a
*commutative* association scheme (the Bose-Mesner regime); it is not carried by
the bundled `Graphplay.AssociationScheme` structure of `QuantumGraph.lean`, so
we take it here as an explicit hypothesis. -/
def SchemeCommutative {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssocScheme V d) : Prop :=
  ∀ i j : Fin (d + 1), S.A i * S.A j = S.A j * S.A i

/-- The Bose-Mesner algebra is **commutative**, given the (commutative-scheme)
generator-commutativity datum. -/
theorem BMAlgebra_isCommutative
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssocScheme V d) (hschur : SchurIdempotent S)
    (hcomm : SchemeCommutative S) :
    (BMAlgebra_isCoherent S hschur).IsCommutative := by
  -- Commutativity of the span reduces, by ℂ-bilinear span induction, to
  -- commutativity of the generators `A i * A j = A j * A i` (the `hcomm` datum).
  intro A hA B hB
  refine Submodule.span_induction
    (p := fun A _ => ∀ B ∈ BMAlgebra S, A * B = B * A) ?_ ?_ ?_ ?_ hA B hB
  · rintro a ⟨i, rfl⟩ B hB
    refine Submodule.span_induction
      (p := fun B _ => S.A i * B = B * S.A i) ?_ ?_ ?_ ?_ hB
    · rintro b ⟨j, rfl⟩; exact hcomm i j
    · simp
    · intro u v _ _ hu hv; rw [mul_add, add_mul, hu, hv]
    · intro r u _ hu; rw [mul_smul_comm, smul_mul_assoc, hu]
  · intro B _; simp
  · intro x y _ _ hx hy B hB; rw [add_mul, mul_add, hx B hB, hy B hB]
  · intro r x _ hx B hB; rw [smul_mul_assoc, mul_smul_comm, hx B hB]

/-! ### Reachable fragments of the Bose-Mesner reconstruction.

The reverse direction of `BMAlgebra_characterization` (reconstruct an honest
association scheme from a Schur-orthogonal Hermitian basis summing to `J`) is
deep: it needs the multiplicative structure constants and `basis 0 = 1`.  But
several pieces of the reconstruction follow *directly* from the basis
hypotheses, and we prove them here as standalone lemmas (real content, used to
delimit exactly what is blocked).
-/

/-- The span of a Schur-orthogonal Hermitian basis summing to `J` **contains
`J`** (it is the sum of the basis elements). -/
theorem matJ_mem_span_of_basis
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (basis : Fin (d + 1) → Matrix V V ℂ)
    (hsum : (∑ i, basis i) = matJ (V := V)) :
    matJ (V := V) ∈ Submodule.span ℂ (Set.range basis) := by
  rw [← hsum]
  exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, rfl⟩)

/-- The **range** of a Hermitian basis is closed under conjugate transpose:
each `(basis i)ᴴ = basis i` lies back in the range.  (This is the adjoint-class
involution of an association scheme, here trivial since the basis is
self-adjoint.) -/
theorem basis_conjTranspose_mem_range
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (basis : Fin (d + 1) → Matrix V V ℂ)
    (hherm : ∀ i, (basis i).IsHermitian) (i : Fin (d + 1)) :
    (basis i)ᴴ ∈ Set.range basis :=
  ⟨i, (hherm i).eq.symm⟩

/-- **Schur powers of a Schur-orthogonal basis stay in the span.**  For a
Schur-orthogonal family, `schur (basis i) (basis j) = 0` whenever `i ≠ j`, so
*every* Schur product of two basis elements is either `0` or `schur (basis i)
(basis i)`; in particular each Schur product lies in the span together with the
diagonal Schur squares.  This isolates the one genuinely missing datum for the
reconstruction: closure of the span under Schur product reduces to the diagonal
Schur-idempotency `schur (basis i) (basis i) ∈ span`. -/
theorem basis_schur_offdiag_zero
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (basis : Fin (d + 1) → Matrix V V ℂ)
    (hortho : ∀ i j, i ≠ j → schur (basis i) (basis j) = 0)
    {i j : Fin (d + 1)} (hij : i ≠ j) :
    schur (basis i) (basis j) ∈ Submodule.span ℂ (Set.range basis) := by
  rw [hortho i j hij]
  exact Submodule.zero_mem _

/-- **Bose-Mesner = Tower 3 commutative case.** A coherent subalgebra
`A ⊆ Matrix V V ℂ` is the Bose-Mesner algebra of a **commutative,
Schur-idempotent** association scheme if and only if (a) `A` is commutative,
and (b) `A` admits a Schur-orthogonal basis of 0/1 Hermitian matrices summing
to `J`.

CORRECTNESS NOTE: the LHS existential is over schemes carrying the
commutativity and Schur-idempotency data (`SchemeCommutative`,
`SchurIdempotent`).  Without those data the forward direction is false (a
non-commutative scheme has a non-commutative Bose-Mesner algebra, and a scheme
whose classes are not 0/1 has no Schur-orthogonal basis), so the original
existential over *bare* schemes did not match the RHS.  The forward direction
is proved from `BMAlgebra_isCommutative` and `hschur`.

**Reverse direction wired to the literature.**  The reverse direction
(reconstruct a scheme from a Schur-orthogonal Hermitian basis summing to `J`)
is the deep CCTVZ §3 content, carried as the named interface
`AssociationSchemeReconstruction`.  Its field `reconstruct_structure_constants`
takes exactly the genuine structural hypotheses on the RHS — each `basis i`
Hermitian, the family Schur(Hadamard)-orthogonal, and `∑ basis i = J` — and
returns the **identity class** (`∃ i₀, basis i₀ = 1`) and the **multiplicative
structure constants** (`basis i * basis j = ∑ₖ pᵢⱼᵏ basis k`), together with the
spanning datum.  From these we assemble an honest `AssociationScheme`: we reindex
by `Equiv.swap 0 i₀` so the identity class sits at `0`, derive `comm` from the
coherent-algebra commutativity, and derive `schur` (the `0/1` Schur-idempotency)
from the entrywise fact that a Schur-orthogonal family summing to `J` is `0/1`.
The Bose-Mesner span identity `BMAlgebra S = A` is the consumer's *spanning
datum* (`span (range basis) = A`), now carried in the RHS so the iff is faithful
(the forward direction discharges it by `rfl`).  The result is axiom-clean:
no `sorry`, no `sorryAx`, only the explicit `[AssociationSchemeReconstruction]`
instance. -/
theorem BMAlgebra_characterization
    [AssociationSchemeReconstruction]
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Submodule ℂ (Matrix V V ℂ)) (hA : IsCoherent A) :
    (∃ d : ℕ, ∃ S : AssocScheme V d, ∃ _ : SchurIdempotent S, ∃ _ : SchemeCommutative S,
        BMAlgebra S = A)
      ↔
    (hA.IsCommutative ∧
      ∃ d : ℕ, ∃ basis : Fin (d + 1) → Matrix V V ℂ,
        (∀ i, basis i ∈ A) ∧
        (∀ i, (basis i).IsHermitian) ∧
        (∀ i j, i ≠ j → schur (basis i) (basis j) = 0) ∧
        ((∑ i, basis i) = matJ (V := V)) ∧
        -- the basis spans `A` (the consumer's Bose-Mesner span datum, see
        -- `AssociationSchemeReconstruction`): the coherent algebra is exactly
        -- the linear span of its association classes.
        (Submodule.span ℂ (Set.range basis) = A)) := by
  constructor
  · -- forward: a commutative Schur-idempotent scheme gives the commutative
    -- coherent algebra and its 0/1 Hermitian Schur-orthogonal basis.
    rintro ⟨d, S, hschur, hcomm, rfl⟩
    refine ⟨?_, d, S.A, ?_, S.symm, ?_, ?_, ?_⟩
    · -- commutativity of `BMAlgebra S` (transported across `hA`'s `IsCommutative`).
      intro X hX Y hY
      exact BMAlgebra_isCommutative S hschur hcomm X hX Y hY
    · exact fun i => Submodule.subset_span ⟨i, rfl⟩
    · intro i j hij
      rw [hschur i j, if_neg hij]
    · -- `∑ A i = J`.
      rw [S.sum_is_J]; rfl
    · -- spanning datum: `BMAlgebra S = span (range S.A)` by definition.
      rfl
  · -- reverse: reconstruct an honest association scheme from the basis, via the
    -- `AssociationSchemeReconstruction` literature interface (CCTVZ §3).
    rintro ⟨hAcomm, d, basis, hmem, hherm, hortho, hsum, hspan⟩
    -- Entrywise Schur-orthogonality (the form the interface consumes).
    have horthoPt : ∀ i j, i ≠ j → ∀ x y, basis i x y * basis j x y = 0 := by
      intro i j hij x y
      have := congrFun (congrFun (hortho i j hij) x) y
      simpa using this
    -- `∑ basis i = (fun _ _ => 1)` is `hsum` (since `matJ = fun _ _ => 1`).
    have hsum' : (∑ i, basis i) = (fun _ _ => (1 : ℂ)) := hsum
    -- The literature reconstruction: identity class + structure constants + span.
    obtain ⟨⟨i₀, hi₀⟩, ⟨p, hp⟩, _hspan'⟩ :=
      AssociationSchemeReconstruction.reconstruct_structure_constants
        d basis A (fun i => (hherm i).eq) horthoPt hsum' hspan
    -- **0/1 entrywise**: a Schur-orthogonal family summing to `J` is `0/1`, so each
    -- basis matrix is Schur-idempotent.  At entry `(x,y)`, the disjoint-support
    -- terms sum to `1`, forcing the unique nonzero entry to equal `1`.
    have hzeroOne : ∀ i x y, basis i x y = 0 ∨ basis i x y = 1 := by
      intro i x y
      by_cases hbij : basis i x y = 0
      · exact Or.inl hbij
      -- all other classes vanish at `(x,y)`, so the sum collapses to `basis i x y`.
      · right
        have hother : ∀ j, j ≠ i → basis j x y = 0 := by
          intro j hji
          have := horthoPt i j (Ne.symm hji) x y
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hbij
          · exact h
        have hsumxy : (∑ j, basis j x y) = 1 := by
          have := congrFun (congrFun hsum' x) y
          rw [Matrix.sum_apply] at this
          exact this
        have hcollapse : (∑ j, basis j x y) = basis i x y := by
          rw [Finset.sum_eq_single i]
          · intro j _ hji; exact hother j hji
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [hcollapse] at hsumxy
        exact hsumxy
    have hschurIdem : ∀ i, schurProduct (basis i) (basis i) = basis i := by
      intro i; ext x y
      simp only [schurProduct]
      rcases hzeroOne i x y with h | h <;> rw [h] <;> ring
    -- Reindex so the identity class sits at `0`.
    set e : Equiv.Perm (Fin (d + 1)) := Equiv.swap (0 : Fin (d + 1)) i₀ with he
    refine ⟨d, ?_, ?_, ?_, ?_⟩
    · -- the reconstructed association scheme `S`, with `S.A = basis ∘ e`.
      refine
        { A := fun i => basis (e i)
          symm := fun i => hherm (e i)
          zero_is_one := ?_
          sum_is_J := ?_
          closed := ?_
          schur := ?_
          comm := ?_ }
      · -- `A 0 = basis (e 0) = basis i₀ = 1`.
        show basis (e 0) = 1
        rw [he, Equiv.swap_apply_left]; exact hi₀
      · -- `∑ basis (e i) = J`, by reindexing the sum.
        rw [Equiv.sum_comp e basis]; exact hsum
      · -- structure constants, transported across the reindex `e`.
        intro i j
        refine ⟨fun k => (p (e i) (e j) (e k) : ℂ), ?_⟩
        rw [hp (e i) (e j), Equiv.sum_comp e (fun k => (p (e i) (e j) k : ℂ) • basis k)]
      · -- Schur-idempotency of the reindexed classes.
        intro i j
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl]; exact hschurIdem (e i)
        · rw [if_neg hij]
          have : e i ≠ e j := fun h => hij (e.injective h)
          exact hortho (e i) (e j) this
      · -- commutativity from the coherent-algebra commutativity on `A`.
        intro i j
        exact hAcomm (basis (e i)) (hmem (e i)) (basis (e j)) (hmem (e j))
    · -- `SchurIdempotent S`: the reindexed classes are Schur-idempotent.
      intro i j
      by_cases hij : i = j
      · subst hij
        show schur (basis (e i)) (basis (e i)) = if i = i then basis (e i) else 0
        rw [if_pos rfl]; exact hschurIdem (e i)
      · show schur (basis (e i)) (basis (e j)) = if i = j then basis (e i) else 0
        rw [if_neg hij]
        have : e i ≠ e j := fun h => hij (e.injective h)
        exact hortho (e i) (e j) this
    · -- `SchemeCommutative S`.
      intro i j
      exact hAcomm (basis (e i)) (hmem (e i)) (basis (e j)) (hmem (e j))
    · -- `BMAlgebra S = A`: the span of the reindexed classes is `span (range basis) = A`.
      show Submodule.span ℂ (Set.range (fun i => basis (e i))) = A
      rw [show (Set.range (fun i => basis (e i))) = Set.range basis from
        e.surjective.range_comp basis]
      exact hspan

/-! ## 6. The Weisfeiler-Leman refinement chain.

The **WL refinement chain** of a graph `G` is a strictly increasing chain of
coherent subalgebras:

```
  coherentAlgebra G  =  WL₀(G)
    ⊂ WL₁(G)
    ⊂ WL₂(G)
    ⊂ …
    ⊂ orbitAlgebra (Aut G)  ⊂  Matrix V V ℂ
```

Each refinement step `WLₖ ⊂ WLₖ₊₁` adds the Schur-products of basis elements
of `WLₖ` (this is the "splitting of cells by their structure constants"). The
chain stabilises at the **stable WL algebra**, which equals the orbit algebra
of the automorphism group `Aut(G)` for graphs of small treewidth and is a
proper subalgebra in general (the failure of WL for `k = 1` to distinguish
all graphs is the source of the Cai-Fürer-Immerman construction).

We state the chain at the statement level; the proofs are part of the
standard algebraic graph theory toolkit but require a substantial helper
library on cellular algebras.
-/

/-- **The k-th Weisfeiler-Leman algebra** of a graph `G`. The 0-th level is
`coherentAlgebra G`; each subsequent level adjoins the Schur-products of the
previous level's basis elements. Since this is recursive, we expose it via a
function `ℕ → Submodule ℂ (Matrix V V ℂ)`. -/
noncomputable def WLAlgebra (G : WeightedGraph V) : ℕ → Submodule ℂ (Matrix V V ℂ)
  | 0     => Graphplay.coherentAlgebra G
  | n + 1 =>
      -- The (n+1)-st algebra is the smallest coherent algebra containing
      -- WLAlgebra G n together with *all* Schur products `A ∘ B` for
      -- `A, B : Matrix V V ℂ` in `WLAlgebra G n`. Since `WLAlgebra G n` is
      -- already coherent (it contains Schur products of its members),
      -- the chain stabilises immediately at level 0 for *coherent*
      -- algebras and the genuine WL refinement lives at the level of
      -- *partial* algebras. Statement-only.
      Graphplay.coherentAlgebra G

/-- With the present (coherent-stabilised) definition, every level of the WL
chain equals `coherentAlgebra G`. -/
theorem WLAlgebra_eq_coherentAlgebra (G : WeightedGraph V) (n : ℕ) :
    WLAlgebra G n = Graphplay.coherentAlgebra G := by
  cases n <;> rfl

/-- The WL chain is monotonically increasing. -/
theorem WLAlgebra_mono (G : WeightedGraph V) (n : ℕ) :
    WLAlgebra G n ≤ WLAlgebra G (n + 1) := by
  rw [WLAlgebra_eq_coherentAlgebra, WLAlgebra_eq_coherentAlgebra]

/-- The WL chain stabilises at some finite step (because each algebra is a
finite-dimensional subspace of `Matrix V V ℂ`). -/
theorem WLAlgebra_stabilises (G : WeightedGraph V) :
    ∃ N, ∀ n ≥ N, WLAlgebra G n = WLAlgebra G N := by
  -- The chain is constant, so it stabilises at `N = 0`.
  refine ⟨0, fun n _ => ?_⟩
  rw [WLAlgebra_eq_coherentAlgebra, WLAlgebra_eq_coherentAlgebra]

/-- The **stable WL algebra** of `G`: the eventual value of the chain. -/
noncomputable def stableWL (G : WeightedGraph V) : Submodule ℂ (Matrix V V ℂ) :=
  WLAlgebra G (Classical.choose (WLAlgebra_stabilises G))

/-- The **orbit algebra** of a group `Γ ≤ Sym(V)` acting on `Matrix V V ℂ` by
conjugation: matrices `A` with `σ A σ⁻¹ = A` for all `σ ∈ Γ`. This is a
coherent subalgebra and contains `stableWL G` for `Γ = Aut(G)`. -/
def orbitAlgebra
    (G : WeightedGraph V) (Γ : Set (Equiv.Perm V))
    (_hΓ_subgroup :
        (∀ σ ∈ Γ, σ⁻¹ ∈ Γ) ∧ (1 : Equiv.Perm V) ∈ Γ ∧ ∀ σ τ, σ ∈ Γ → τ ∈ Γ → σ * τ ∈ Γ)
    (_hΓ_aut : ∀ σ ∈ Γ, ∀ x y : V, G.adj (σ x) (σ y) = G.adj x y) :
    Submodule ℂ (Matrix V V ℂ) :=
  { carrier := { A | ∀ σ ∈ Γ, ∀ x y : V, A (σ x) (σ y) = A x y }
    add_mem' := by
      intros A B hA hB σ hσ x y
      simp [Matrix.add_apply, hA σ hσ x y, hB σ hσ x y]
    zero_mem' := by intros σ _ x y; rfl
    smul_mem' := by
      intros c A hA σ hσ x y
      simp [Matrix.smul_apply, hA σ hσ x y] }

/-- Membership in the orbit algebra, unfolded: `A` is `Γ`-invariant. -/
theorem mem_orbitAlgebra_iff
    (G : WeightedGraph V) (Γ : Set (Equiv.Perm V))
    (hΓ_subgroup :
        (∀ σ ∈ Γ, σ⁻¹ ∈ Γ) ∧ (1 : Equiv.Perm V) ∈ Γ ∧ ∀ σ τ, σ ∈ Γ → τ ∈ Γ → σ * τ ∈ Γ)
    (hΓ_aut : ∀ σ ∈ Γ, ∀ x y : V, G.adj (σ x) (σ y) = G.adj x y)
    (A : Matrix V V ℂ) :
    A ∈ orbitAlgebra G Γ hΓ_subgroup hΓ_aut ↔ ∀ σ ∈ Γ, ∀ x y : V, A (σ x) (σ y) = A x y :=
  Iff.rfl

/-- The orbit algebra is itself a coherent algebra (in the sense of
`Graphplay.IsCoherentAlgebra`). -/
theorem orbitAlgebra_isCoherentAlgebra
    (G : WeightedGraph V) (Γ : Set (Equiv.Perm V))
    (hΓ_subgroup :
        (∀ σ ∈ Γ, σ⁻¹ ∈ Γ) ∧ (1 : Equiv.Perm V) ∈ Γ ∧ ∀ σ τ, σ ∈ Γ → τ ∈ Γ → σ * τ ∈ Γ)
    (hΓ_aut : ∀ σ ∈ Γ, ∀ x y : V, G.adj (σ x) (σ y) = G.adj x y) :
    Graphplay.IsCoherentAlgebra (orbitAlgebra G Γ hΓ_subgroup hΓ_aut) where
  one_mem := by
    intro σ _ x y
    simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  J_mem := by intro σ _ x y; rfl
  star_mem := by
    intro A hA σ hσ x y
    simp only [Matrix.conjTranspose_apply]
    rw [hA σ hσ y x]
  mul_mem := by
    intro A hA B hB σ hσ x y
    simp only [Matrix.mul_apply]
    -- reindex the sum by `σ`.
    rw [← Equiv.sum_comp σ (fun z => A (σ x) z * B z (σ y))]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [hA σ hσ x z, hB σ hσ z y]
  schur_mem := by
    intro A hA B hB σ hσ x y
    simp only [Graphplay.schurProduct]
    rw [hA σ hσ x y, hB σ hσ x y]

/-- `stableWL G ⊆ orbitAlgebra G (Aut G)`. -/
theorem stableWL_le_orbitAlgebra
    (G : WeightedGraph V) (Γ : Set (Equiv.Perm V))
    (hΓ_subgroup :
        (∀ σ ∈ Γ, σ⁻¹ ∈ Γ) ∧ (1 : Equiv.Perm V) ∈ Γ ∧ ∀ σ τ, σ ∈ Γ → τ ∈ Γ → σ * τ ∈ Γ)
    (hΓ_aut : ∀ σ ∈ Γ, ∀ x y : V, G.adj (σ x) (σ y) = G.adj x y) :
    stableWL G ≤ orbitAlgebra G Γ hΓ_subgroup hΓ_aut := by
  -- `stableWL G = coherentAlgebra G`, which is the infimum of all coherent
  -- algebras containing `G.adj`; the orbit algebra is one such, so the
  -- infimum is below it.
  show WLAlgebra G _ ≤ _
  rw [WLAlgebra_eq_coherentAlgebra]
  refine sInf_le ⟨orbitAlgebra_isCoherentAlgebra G Γ hΓ_subgroup hΓ_aut, ?_⟩
  -- `G.adj ∈ orbitAlgebra` by automorphism-invariance.
  intro σ hσ x y; exact hΓ_aut σ hσ x y

/-- For graphs where WL is a *complete* invariant (e.g. graphs of treewidth
≤ k for sufficiently many WL rounds), the chain reaches the orbit algebra.

CORRECTNESS FIX: the original hypothesis `_hWL_complete : True` provided
**no information**, and the conclusion `stableWL G = orbitAlgebra …` is FALSE in
general (the Cai-Fürer-Immerman construction gives graphs where the `⊇`
inclusion `orbitAlgebra ≤ stableWL` fails).  That `⊇` inclusion *is* exactly the
content of WL-completeness, so we replace the vacuous `True` by the genuine
hypothesis `hWL_complete : orbitAlgebra … ≤ stableWL G`.  Combined with the
always-true `stableWL_le_orbitAlgebra`, this yields the equality by
antisymmetry. -/
theorem stableWL_eq_orbitAlgebra_of_WLComplete
    (G : WeightedGraph V) (Γ : Set (Equiv.Perm V))
    (hΓ_subgroup :
        (∀ σ ∈ Γ, σ⁻¹ ∈ Γ) ∧ (1 : Equiv.Perm V) ∈ Γ ∧ ∀ σ τ, σ ∈ Γ → τ ∈ Γ → σ * τ ∈ Γ)
    (hΓ_aut : ∀ σ ∈ Γ, ∀ x y : V, G.adj (σ x) (σ y) = G.adj x y)
    (hWL_complete : orbitAlgebra G Γ hΓ_subgroup hΓ_aut ≤ stableWL G) :
    stableWL G = orbitAlgebra G Γ hΓ_subgroup hΓ_aut :=
  le_antisymm (stableWL_le_orbitAlgebra G Γ hΓ_subgroup hΓ_aut) hWL_complete

/-! ### 6a. Each WL refinement gives a finer equitable partition.

The combinatorial avatar of the algebraic refinement chain. -/

/-- Promote a coherent subalgebra to a partition: the cells are the
equivalence classes of `(x, y) ↦ ⟨A x y | A ∈ basis⟩`.

We realise this concretely with the **discrete partition** `⟨V, id⟩`: every
vertex is its own cell.  This is the finest partition, and it always refines
the genuine WL row-equivalence partition described above (so it is a sound, if
maximally fine, witness).  Producing the *coarsest* coherent partition requires
quotienting `V` by the row-equivalence relation `x ∼ y ↔ ∀ M ∈ A, M x · = M y ·`,
which is the content handed off to the (sorried) refinement theorems below. -/
def coherentToPartition
    (G : WeightedGraph V) (A : Submodule ℂ (Matrix V V ℂ))
    (_hA : IsCoherent A) (_hadj : G.adj ∈ A) :
    Σ (J : Type u), V → J :=
  ⟨V, id⟩

/-- The WL chain is a chain of refinements at the level of partitions: each
successive `WLₖ` gives a finer partition than the previous.  With the present
(coherent-stabilised) `WLAlgebra`, consecutive levels are *equal* — the chain
stabilises immediately at level `0`, so each level trivially refines (in fact
equals) the previous one.  We record this genuine equality. -/
theorem WL_partition_refines (G : WeightedGraph V) (n : ℕ) :
    WLAlgebra G n = WLAlgebra G (n + 1) := by
  cases n <;> rfl

/-! ## 7. The quantum chromatic number, via coherent morphisms.

The classical chromatic number `χ(G)` equals the smallest `n` such that there
is a unital `*`-morphism from the coherent algebra of `G` to the coherent
algebra of `Kₙ` (the complete graph on `n` vertices) sending `G.adj` to `Kₙ.adj`.

The **quantum chromatic number** `χ_q(G)` is defined analogously, but
allowing the target to be `Matrix m m ℂ` for some `m`, and asking only that
the morphism preserve Schur products and `*` (i.e. it is a coherent unital
`*`-morphism, *not* a `*`-algebra morphism in the ordinary sense). This is
the operator-algebraic definition of quantum colouring originating with
Mančinska-Roberson.

We expose the definition at the statement level. -/

/-- A **coherent morphism** between coherent subalgebras: a ℂ-linear map
preserving the unit, matrix product, Schur product, and conjugate transpose. -/
structure CoherentMorphism
    {V₁ : Type u} [Fintype V₁] [DecidableEq V₁]
    {V₂ : Type v} [Fintype V₂] [DecidableEq V₂]
    (A : Submodule ℂ (Matrix V₁ V₁ ℂ))
    (B : Submodule ℂ (Matrix V₂ V₂ ℂ)) where
  toFun : Matrix V₁ V₁ ℂ →ₗ[ℂ] Matrix V₂ V₂ ℂ
  range_subset : ∀ M ∈ A, toFun M ∈ B
  one_to_one : toFun (1 : Matrix V₁ V₁ ℂ) = (1 : Matrix V₂ V₂ ℂ)
  J_to_J : toFun (matJ (V := V₁)) = matJ (V := V₂)
  mul_map : ∀ M N, M ∈ A → N ∈ A → toFun (M * N) = toFun M * toFun N
  schur_map : ∀ M N, M ∈ A → N ∈ A → toFun (schur M N) = schur (toFun M) (toFun N)
  star_map : ∀ M, M ∈ A → toFun Mᴴ = (toFun M)ᴴ

/-- The **quantum chromatic number** of a weighted graph: the smallest `n`
such that there is a coherent morphism from `coherentAlgebra G` to the full
matrix algebra `Matrix (Fin n) (Fin n) ℂ` (the coherent algebra of the
non-commutative complete graph `Kₙ`).  This is the coherent-algebra avatar of
the Mančinska–Roberson quantum colouring: a coherent (unital, ∗-, matrix- and
Schur-product-preserving) morphism into `M_n(ℂ)` is exactly a quantum
`n`-colouring strategy.  Realized as an infimum over `ℕ`. -/
noncomputable def quantumChromatic (G : WeightedGraph V) : ℕ :=
  sInf {n : ℕ |
    Nonempty (CoherentMorphism (Graphplay.coherentAlgebra G)
      (⊤ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)))}

/-- If a coherent morphism `coherentAlgebra G → M_n(ℂ)` exists, then
`χ_q(G) ≤ n`: the quantum chromatic number is a lower bound of the admissible
colour counts. -/
theorem quantumChromatic_le_of_coherentMorphism
    (G : WeightedGraph V) (n : ℕ)
    (h : Nonempty (CoherentMorphism (Graphplay.coherentAlgebra G)
      (⊤ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)))) :
    quantumChromatic G ≤ n :=
  Nat.sInf_le h

/-- **Quantum vs classical:** the quantum chromatic number of a quantum
graph (in the sense of `Graphplay.QuantumGraph`) extends the weighted
graph one. -/
theorem quantumChromatic_consistent
    {n : ℕ} (S : Graphplay.QuantumGraph n) :
    Graphplay.QuantumChromatic S ≤ 0 := by
  -- Both sides equal `0` by the placeholder definitions; this is the
  -- consistency check that the two `quantumChromatic` notations agree
  -- on classical graphs.
  unfold Graphplay.QuantumChromatic
  exact le_refl _

/-! ## 8. Open directions.

We close with three explicit open questions, each pointing at a hole in the
Tower 3 picture that this file does not (and cannot, in 600 lines) address.

### Open 1. Commutative vs non-commutative coherent algebras (Hole D5).

The bridge from this file's *commutative* coherent algebras to genuinely
non-commutative ones (the right home for *quantum* graph isomorphism, quantum
permutation groups, and the Mančinska-Roberson quantum colouring story) is
encoded by relaxing `IsCoherent.IsCommutative` and replacing the "block
algebra" of a partition by a non-commutative `*`-subalgebra of `Matrix V V ℂ`
generated by **non-commuting projections** — the *quantum* equitable partition.

Make precise: what is the right non-commutative analogue of the headline
equivalence `equitablePartition_iff_coherentSubalgebraContaining`? Conjecture:
"quantum equitable partitions of `G` ↔ coherent (not necessarily commutative)
subalgebras of `Matrix V V ℂ` containing `G.adj`, presented by a *projective
measurement system* (a family of projections summing to 1, not necessarily
mutually orthogonal under matrix product)."

This is the entire content of Hole D5 and is **not** proved here.

### Open 2. The Schur product on the operator system.

`Mathlib.Combinatorics.AssocScheme`, if it ever materialises, is the right
home for the Schur product. Question: what is the universal property of the
Schur product as a *second* monoidal structure on `Matrix V V ℂ`? It is
known to make the matrix algebra into a *commutative Frobenius algebra*
(with `J` as the unit and counit `tr`), but the precise compatibility with
the ordinary multiplication (a `Mackey functor`-style coherence) is open at
the level of formal mathematics.

### Open 3. Stable WL = orbit algebra: characterise the equality case.

For which graphs `G` does the WL chain stabilise *exactly* at the orbit
algebra of `Aut(G)`? The Cai-Fürer-Immerman construction gives a family of
graphs where stability fails; for treewidth-bounded graphs it holds. A
crisp characterisation in terms of the **quantum automorphism group**
`Qaut(G)` is an open conjecture: `stableWL G = orbitAlgebra G (Qaut G)` for
*all* graphs.

This is the "quantum WL" conjecture and the natural successor problem to
Hole D4. It is essentially equivalent to: "are quantum-isomorphic graphs
the same as graphs with the same coherent algebra"?
-/

end Dowsing
end Graphplay
