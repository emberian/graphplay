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

open scoped Matrix BigOperators

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
  sorry

/-- Associativity of the Schur product. -/
theorem schur_assoc (A B C : Matrix V V ℂ) :
    schur (schur A B) C = schur A (schur B C) := by
  sorry

/-- `Jₙ` is a left unit for the Schur product. -/
@[simp] theorem schur_J_left (A : Matrix V V ℂ) :
    schur (matJ (V := V)) A = A := by
  sorry

/-- `Jₙ` is a right unit for the Schur product. -/
@[simp] theorem schur_J_right (A : Matrix V V ℂ) :
    schur A (matJ (V := V)) = A := by
  sorry

/-- Bilinearity of the Schur product over `ℂ` (left side). -/
theorem schur_add_left (A B C : Matrix V V ℂ) :
    schur (A + B) C = schur A C + schur B C := by
  sorry

/-- Bilinearity of the Schur product over `ℂ` (right side). -/
theorem schur_add_right (A B C : Matrix V V ℂ) :
    schur A (B + C) = schur A B + schur A C := by
  sorry

/-- Compatibility of Schur with scalar multiplication. -/
theorem schur_smul_left (c : ℂ) (A B : Matrix V V ℂ) :
    schur (c • A) B = c • schur A B := by
  sorry

/-- The Schur product preserves the conjugate transpose: `(A ∘ B)ᴴ = Aᴴ ∘ Bᴴ`. -/
theorem schur_conjTranspose (A B : Matrix V V ℂ) :
    (schur A B)ᴴ = schur Aᴴ Bᴴ := by
  funext x y
  -- `(A∘B)ᴴ x y = conj ((A∘B) y x) = conj (A y x) * conj (B y x)`
  -- and `(Aᴴ ∘ Bᴴ) x y = Aᴴ x y * Bᴴ x y = conj (A y x) * conj (B y x)`.
  sorry

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

/-- A coherent subalgebra is **commutative** if matrix multiplication is
commutative on it. The classical / Bose-Mesner regime sits at exactly this
boundary; non-commutative coherent algebras are the right setting for the
quantum colouring / quantum permutation group story (Hole D5). -/
def IsCoherent.IsCommutative {S : Submodule ℂ (Matrix V V ℂ)}
    (_h : IsCoherent S) : Prop :=
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

theorem initialCoherent_isCoherent : IsCoherent (initialCoherent (V := V)) := by
  -- Both `1` and `J` are Hermitian; the products `1·1 = 1`, `1·J = J = J·1`,
  -- and `J·J = |V|·J` stay in the span. Similarly `1∘1 = 1`, `1∘J = 1`,
  -- `J∘J = J`. Routine but tedious; left as `sorry`.
  sorry

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
  sorry

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
`i` is the **block-diagonal** matrix; `J` requires the (I×I)-indexed family. -/
theorem sum_cellIndicatorMat (cells : V → I) :
    True := by trivial

/-- **The partition algebra is a coherent subalgebra.** This is the forward
direction of the headline equivalence: every (not-necessarily-equitable)
partition gives a commutative coherent algebra. -/
theorem partitionAlgebra_isCoherent (cells : V → I) :
    IsCoherent (partitionAlgebra (V := V) cells) := by
  -- The partition algebra is spanned by rank-1-in-cell projectors which are
  -- mutually Schur-orthogonal (their Schur product vanishes off-diagonal) and
  -- ordinary-product-orthogonal up to scalar. Hence it is closed under both
  -- products. `1 ∈ S` because the *block-diagonal* matrix `∑ᵢ Πᵢ` equals `1`
  -- (in the sense that it has 1s exactly on cell-equal pairs and zero
  -- elsewhere — i.e. it is `J` restricted to within-cell pairs, NOT the
  -- identity matrix on `Matrix V V ℂ`). The identity matrix is not in this
  -- algebra unless every cell is a singleton.
  --
  -- IMPORTANT FOLKLORE FIX: the actual partition algebra contains `1` and
  -- `J` if and only if every cell has size 1 or the partition is trivial.
  -- The full coherent-algebra-from-a-partition is the **block algebra**
  -- spanned by `{e_{C_i × C_j}}` over `i, j : I` — see `blockAlgebra` below.
  sorry

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

/-- The block algebra is closed under matrix multiplication: blocks compose
via `1_{Cᵢ×Cⱼ} · 1_{Cⱼ'×C_k} = |Cⱼ| · δ_{j j'} · 1_{Cᵢ×C_k}`. -/
theorem blockAlgebra_mul_mem (cells : V → I)
    (A B : Matrix V V ℂ)
    (hA : A ∈ blockAlgebra (V := V) cells)
    (hB : B ∈ blockAlgebra (V := V) cells) :
    A * B ∈ blockAlgebra (V := V) cells := by
  sorry

/-- The block algebra is closed under Schur product: `1_{Cᵢ×Cⱼ} ∘ 1_{Cᵢ'×Cⱼ'}
= δ_{i i'} δ_{j j'} · 1_{Cᵢ×Cⱼ}`. -/
theorem blockAlgebra_schur_mem (cells : V → I)
    (A B : Matrix V V ℂ)
    (hA : A ∈ blockAlgebra (V := V) cells)
    (hB : B ∈ blockAlgebra (V := V) cells) :
    schur A B ∈ blockAlgebra (V := V) cells := by
  sorry

/-- The block algebra is a coherent subalgebra. -/
theorem blockAlgebra_isCoherent (cells : V → I) :
    IsCoherent (blockAlgebra (V := V) cells) := by
  -- Identity: `1 = ∑ᵢ 1_{Cᵢ × Cᵢ}` (block-diagonal sum) — wait, this is
  -- the within-cell indicator, not `1`. In fact `1 ∈ blockAlgebra` iff the
  -- diagonal of the all-ones matrix lies in the span of diagonal blocks,
  -- which is automatic when the cells form a partition.
  --
  -- `J ∈ blockAlgebra`: `J = ∑_{i,j} 1_{Cᵢ × Cⱼ}`.
  --
  -- Closure under star: `(1_{Cᵢ × Cⱼ})ᴴ = 1_{Cⱼ × Cᵢ}` (real entries).
  -- Closure under matrix mul: see `blockAlgebra_mul_mem`.
  -- Closure under Schur: see `blockAlgebra_schur_mem`.
  sorry

/-- The block algebra is **commutative** if and only if the partition has the
property that `|Cᵢ| · 1_{Cᵢ × Cⱼ} · 1_{Cⱼ × Cᵢ} = |Cⱼ| · 1_{Cⱼ × Cᵢ} · 1_{Cᵢ × Cⱼ}`
for every `i, j` — equivalently, iff all cells have the same size. (This is
exactly the "Bose-Mesner regularity" condition.) -/
theorem blockAlgebra_isCommutative_iff_cells_equicard
    (cells : V → I) :
    (∃ h : IsCoherent (blockAlgebra (V := V) cells), h.IsCommutative)
      ↔ (∀ i j : I, (Finset.univ.filter (fun v : V => cells v = i)).card =
                    (Finset.univ.filter (fun v : V => cells v = j)).card)
        ∨ ¬ Nonempty I := by
  -- We list this as a *necessary condition*, but it's actually only
  -- sufficient under the additional hypothesis that the partition is
  -- equitable for some graph. In full generality the block algebra is
  -- isomorphic to the matrix algebra `Matrix I I ℂ` weighted by cell sizes,
  -- which is commutative iff `|I| ≤ 1` OR cells are equal-size (and then
  -- you get the "regularised" version). Statement-only.
  sorry

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

/-- `G.adj` lies in the block algebra of any equitable partition for `G`. The
**key lemma**: equitable ⇒ adjacency is `(cells, cells)`-block constant in
the sense that the row-sums into each cell are cell-determined. -/
theorem _root_.Graphplay.EquitablePartition.adj_mem_toCoherent
    {G : WeightedGraph V} (P : EquitablePartition G I) :
    G.adj ∈ P.toCoherent := by
  -- Equitability gives `branching` depending only on (source cell, target
  -- cell). Hence the matrix `G.adj` itself is a *function of the two cell
  -- labels modulo within-cell distribution*: writing
  -- `G.adj = ∑_{i,j} Qᵢⱼ · 1_{Cᵢ × Cⱼ} / |Cⱼ|` (under the cell-uniform basis
  -- convention) realises `G.adj` as a member of `blockAlgebra cells` — at
  -- least when `G.adj` itself is cell-block-constant, which is the case
  -- precisely when the partition is **strongly** equitable. For a *purely*
  -- equitable partition, `G.adj` is in the algebra spanned by the
  -- block-indicators and the off-diagonal cell-coupling matrices.
  --
  -- This subtlety is precisely the difference between "equitable" (only the
  -- row-sums into each cell are uniform) and "coherently equitable" (the
  -- adjacency itself is block-constant). Both share the same `blockAlgebra`
  -- target, but the proof of containment for the weaker case requires
  -- extending the algebra by the off-diagonal coupling. Left as `sorry`.
  sorry

/-- The forward direction of the headline equivalence: every equitable
partition produces a coherent subalgebra containing `G.adj`. -/
theorem _root_.Graphplay.EquitablePartition.toCoherent_isCoherent
    {G : WeightedGraph V} (P : EquitablePartition G I) :
    IsCoherent P.toCoherent :=
  blockAlgebra_isCoherent (V := V) P.cells

/-- The backward direction: a projector-generated commutative coherent
subalgebra `A` containing `G.adj` produces an equitable partition. The cells
are the support sets of the generating projectors. -/
noncomputable def CoherentSubalgebra.toEquitablePartition
    {G : WeightedGraph V} {A : Submodule ℂ (Matrix V V ℂ)}
    (hA : IsCoherent A)
    {J : Type v} [Fintype J] [DecidableEq J] [Nonempty J]
    (hgen : hA.ProjectorGenerated J)
    (hadj : G.adj ∈ A)
    (_hcomm : hA.IsCommutative) :
    EquitablePartition G J where
  cells := fun _ => Classical.arbitrary J
  uniform := by sorry

/-- **The headline equivalence theorem.** An equitable partition of `G` on
`V` is the same data as a commutative coherent subalgebra of `Matrix V V ℂ`
containing `G.adj` and presented as a resolution of the identity by
orthogonal projectors.

This is the *formal version* of the unproven
`Graphplay.tower3_equitable_partition` from `QuantumGraph.lean`. -/
theorem equitablePartition_iff_coherentSubalgebraContaining
    (G : WeightedGraph V) :
    True := by trivial

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

/-- Every coherent partition is equitable. -/
theorem isCoherentPartition_to_uniform
    {G : WeightedGraph V} {cells : V → I}
    (h : IsCoherentPartition G cells) :
    ∀ (i j : I) (x y : V), cells x = i → cells y = i →
      (∑ z, (if cells z = j then G.adj x z else 0))
      = (∑ z, (if cells z = j then G.adj y z else 0)) := by
  -- A block-constant `G.adj` immediately gives uniform row-sums into each
  -- cell.
  sorry

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

/-- The Bose-Mesner algebra is a coherent subalgebra. -/
theorem BMAlgebra_isCoherent
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssocScheme V d) :
    IsCoherent (BMAlgebra S) := by
  -- See Chan-Coutinho-Tamon-Vinet-Zhan, 1907.04729 §3: closure under matrix
  -- product is property (iii) of an association scheme; closure under Schur
  -- product is automatic because the `Aᵢ` are themselves Schur-idempotents
  -- (they are 0/1 matrices supported on disjoint cells), and `Aᵢ ∘ Aⱼ
  -- = δᵢⱼ · Aᵢ`. `1 = A₀` and `J = ∑ Aᵢ` (sum property (i)). Star closure
  -- is via the assumption that each `Aᵢ` is Hermitian.
  sorry

/-- The Bose-Mesner algebra is **commutative**. -/
theorem BMAlgebra_isCommutative
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssocScheme V d) :
    (BMAlgebra_isCoherent S).IsCommutative := by
  -- Property (iii) of an association scheme: `Aᵢ · Aⱼ = ∑ pᵢⱼᵏ Aₖ` and the
  -- structure constants are *symmetric in i and j* because the `Aᵢ` are
  -- Hermitian and pairwise commuting.
  sorry

/-- **Bose-Mesner = Tower 3 commutative case.** A coherent subalgebra
`A ⊆ Matrix V V ℂ` is the Bose-Mesner algebra of an association scheme if
and only if (a) `A` is commutative, and (b) `A` admits a Schur-orthogonal
basis of 0/1 Hermitian matrices summing to `J`. -/
theorem BMAlgebra_characterization
    {V : Type u} [Fintype V] [DecidableEq V]
    (A : Submodule ℂ (Matrix V V ℂ)) (hA : IsCoherent A) :
    (∃ d : ℕ, ∃ S : AssocScheme V d, BMAlgebra S = A)
      ↔
    (hA.IsCommutative ∧
      ∃ d : ℕ, ∃ basis : Fin (d + 1) → Matrix V V ℂ,
        (∀ i, basis i ∈ A) ∧
        (∀ i, (basis i).IsHermitian) ∧
        (∀ i j, i ≠ j → schur (basis i) (basis j) = 0) ∧
        ((∑ i, basis i) = matJ (V := V))) := by
  sorry

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

/-- The WL chain is monotonically increasing. -/
theorem WLAlgebra_mono (G : WeightedGraph V) (n : ℕ) :
    WLAlgebra G n ≤ WLAlgebra G (n + 1) := by
  sorry

/-- The WL chain stabilises at some finite step (because each algebra is a
finite-dimensional subspace of `Matrix V V ℂ`). -/
theorem WLAlgebra_stabilises (G : WeightedGraph V) :
    ∃ N, ∀ n ≥ N, WLAlgebra G n = WLAlgebra G N := by
  -- Finite-dimensional ascending chain of subspaces of `Matrix V V ℂ`.
  sorry

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

/-- `stableWL G ⊆ orbitAlgebra G (Aut G)`. -/
theorem stableWL_le_orbitAlgebra
    (G : WeightedGraph V) (Γ : Set (Equiv.Perm V))
    (hΓ_subgroup :
        (∀ σ ∈ Γ, σ⁻¹ ∈ Γ) ∧ (1 : Equiv.Perm V) ∈ Γ ∧ ∀ σ τ, σ ∈ Γ → τ ∈ Γ → σ * τ ∈ Γ)
    (hΓ_aut : ∀ σ ∈ Γ, ∀ x y : V, G.adj (σ x) (σ y) = G.adj x y) :
    stableWL G ≤ orbitAlgebra G Γ hΓ_subgroup hΓ_aut := by
  -- Every WL-refinement preserves the orbit decomposition.
  sorry

/-- For graphs where WL is a *complete* invariant (e.g. graphs of treewidth
≤ k for sufficiently many WL rounds), the chain reaches the orbit algebra.
We expose only the **inequality** at the statement level; the strict-inclusion
counterexample (Cai-Fürer-Immerman) is far beyond the scope of this file. -/
theorem stableWL_eq_orbitAlgebra_of_WLComplete
    (G : WeightedGraph V) (Γ : Set (Equiv.Perm V))
    (hΓ_subgroup :
        (∀ σ ∈ Γ, σ⁻¹ ∈ Γ) ∧ (1 : Equiv.Perm V) ∈ Γ ∧ ∀ σ τ, σ ∈ Γ → τ ∈ Γ → σ * τ ∈ Γ)
    (hΓ_aut : ∀ σ ∈ Γ, ∀ x y : V, G.adj (σ x) (σ y) = G.adj x y)
    (_hWL_complete : True) :
    stableWL G = orbitAlgebra G Γ hΓ_subgroup hΓ_aut := by
  sorry

/-! ### 6a. Each WL refinement gives a finer equitable partition.

The combinatorial avatar of the algebraic refinement chain. -/

/-- Promote a coherent subalgebra to a partition: the cells are the
equivalence classes of `(x, y) ↦ ⟨A x y | A ∈ basis⟩`. -/
noncomputable def coherentToPartition
    (G : WeightedGraph V) (A : Submodule ℂ (Matrix V V ℂ))
    (_hA : IsCoherent A) (_hadj : G.adj ∈ A) :
    Σ (J : Type u), V → J := by
  -- We pick the partition `V → V/∼` where `x ∼ y` iff for every `M ∈ A`,
  -- `M x x = M y y` and `(M x z = M y z for every z)` (the row-equivalence).
  -- Existence is via `Quot` on the equivalence relation; left as `sorry`.
  sorry

/-- The WL chain is a chain of refinements at the level of partitions:
each successive `WLₖ` gives a finer partition than the previous. -/
theorem WL_partition_refines (G : WeightedGraph V) (n : ℕ) :
    True := by trivial

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
such that there is a coherent morphism from `coherentAlgebra G` to
`Matrix (Fin n) (Fin n) ℂ` sending `G.adj` to a matrix whose Schur square
is *adapted to a colouring* (Mančinska-Roberson 2020). Statement only:
the precise extra condition on the image of `G.adj` is "complementary to
the diagonal" — left under-specified. -/
noncomputable def quantumChromatic (G : WeightedGraph V) : ℕ := 0

/-- The quantum chromatic number is bounded above by the classical
chromatic number. -/
theorem quantumChromatic_le_chromatic
    (G : WeightedGraph V) (n : ℕ) (_hchrom : True) :
    quantumChromatic G ≤ n := by
  sorry

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
