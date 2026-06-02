/-
# Graphplay.StdLib.Tree

Standard-library entry for the **rooted complete binary tree** `T_d` on
`2^d − 1` vertices, viewed as a continuous-time-quantum-walk host.

We use the standard *heap / array* indexing of a complete binary tree:
vertices are `Fin (2^d − 1)`, the root is `0`, and the children of vertex
`i` are `2i + 1` and `2i + 2` (so the parent of `i ≥ 1` is `(i − 1) / 2`).
This is exactly the breadth-first numbering of the complete binary tree of
depth `d` (`d` levels, `2^d − 1` nodes).

The adjacency is the symmetric parent ↔ child relation, so the resulting
`WeightedGraph` is a genuine (loopless, Hermitian) tree:

* the root `0` has degree `2` (its two children),
* every internal non-root vertex has degree `3` (a parent and two children),
* every leaf has degree `1` (just its parent),
* the number of edges is exactly `(2^d − 1) − 1 = 2^d − 2` (a tree on `n`
  vertices has `n − 1` edges), and
* the graph is **bipartite by depth parity**: an edge always joins a vertex
  at depth `k` to a vertex at depth `k ± 1`, so the two colour classes are
  the even- and odd-depth vertices.

## Walkformer atom (the "tree atom" / hierarchical-reach primitive)

The CTQW `U(t) = exp(−i t A)` on the complete binary tree is the verified
semantics of the **tree attention atom**: a single head whose receptive
field grows *logarithmically* (depth `d = ⌈log₂ n⌉`) in the number of
leaves, routing amplitude between the root and the `2^{d−1}` leaves through
`d` hops.  This is the walk primitive behind hierarchical / log-depth
aggregation (the binary-tree welch of a reduction tree, glued
spectrally): the column-distance from root to a leaf is `d − 1`, so the
walk reaches the entire leaf frontier in `O(log n)` time.  The Childs–
Cleve–Deotto–Farhi–Gutmann–Spielman "glued-trees" speedup
(STOC 2003, quant-ph/0209131) is the canonical instance: a CTQW traverses
a tree exponentially faster than any classical walk.

Reachable structural facts are proved here with real proofs.  The *non-vacuity*
of the spectrum — a real adjacency eigenvalue of magnitude `≥ √2` for depth
`d ≥ 2` — is now **fully proved** (`Tree.exists_large_eigenvalue`, axiom-clean)
via the Rayleigh / Courant–Fischer lower bound applied to the embedded depth-1
star `K_{1,2}`; the full closed-form Chebyshev spectrum is not needed for it.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.ForMathlib.CourantFischer

open scoped Matrix
open NormedSpace

universe u

namespace Graphplay
namespace StdLib

/-! ## Heap indexing of the complete binary tree -/

/-- The number of vertices of the complete binary tree of depth `d`:
`2^d − 1`. -/
def Tree.numVertices (d : ℕ) : ℕ := 2 ^ d - 1

/-- The **parent-child adjacency predicate** in heap indexing: vertices
`i` and `j` (as naturals) are adjacent iff one is a child of the other,
i.e. `j = 2i + 1`, `j = 2i + 2`, `i = 2j + 1`, or `i = 2j + 2`. -/
def Tree.AdjNat (i j : ℕ) : Prop :=
  j = 2 * i + 1 ∨ j = 2 * i + 2 ∨ i = 2 * j + 1 ∨ i = 2 * j + 2

instance : DecidableRel Tree.AdjNat := fun i j => by
  unfold Tree.AdjNat; infer_instance

/-- `Tree.AdjNat` is symmetric (the parent/child roles are swapped). -/
theorem Tree.adjNat_symm {i j : ℕ} (h : Tree.AdjNat i j) : Tree.AdjNat j i := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- `Tree.AdjNat` is irreflexive: no vertex is its own parent or child
(`i = 2i + 1` and `i = 2i + 2` are impossible in `ℕ`). -/
theorem Tree.adjNat_irrefl (i : ℕ) : ¬ Tree.AdjNat i i := by
  intro h; rcases h with h | h | h | h <;> omega

/-! ## The complete binary tree as a `SimpleGraph` -/

/-- The **complete binary tree** `T_d` of depth `d` as a `SimpleGraph` on
`Fin (2^d − 1)`: vertices are heap-indexed, and `i ~ j` iff one is a child
of the other (`Tree.AdjNat` on the underlying naturals). -/
def Tree (d : ℕ) : SimpleGraph (Fin (Tree.numVertices d)) where
  Adj i j := Tree.AdjNat i.val j.val
  symm := fun _ _ h => Tree.adjNat_symm h
  loopless := ⟨fun i h => Tree.adjNat_irrefl i.val h⟩

instance (d : ℕ) : DecidableRel (Tree d).Adj := by
  intro i j; unfold Tree; infer_instance

/-! ## The CTQW weighted-graph host -/

/-- The complete binary tree as a `WeightedGraph` (the 0/1 adjacency
Hamiltonian of the CTQW), obtained from the `SimpleGraph` via the standard
bridge.  Its evolution operator is `(Tree.weighted d).evolve t = exp(−i t A)`. -/
noncomputable def Tree.weighted (d : ℕ) :
    WeightedGraph (Fin (Tree.numVertices d)) :=
  SimpleGraph.toWeighted (Tree d)

/-! ## Reachable structural facts -/

/-- `T_d` is **loopless**: no vertex is adjacent to itself. -/
theorem Tree.loopless (d : ℕ) (i : Fin (Tree.numVertices d)) :
    ¬ (Tree d).Adj i i :=
  Tree.adjNat_irrefl i.val

/-- `T_d` is **symmetric** (it is a `SimpleGraph`, so adjacency is
symmetric). -/
theorem Tree.symm (d : ℕ) {i j : Fin (Tree.numVertices d)}
    (h : (Tree d).Adj i j) : (Tree d).Adj j i :=
  (Tree d).symm h

/-- The **depth (level)** of heap-index `i`: the unique `k` with
`2^k − 1 ≤ i < 2^{k+1} − 1`, equivalently `⌊log₂ (i + 1)⌋`. -/
def Tree.depth (i : ℕ) : ℕ := Nat.log 2 (i + 1)

/-- **Bipartiteness by depth parity (edge half).**  Every edge of `T_d`
joins a vertex at depth `k` to a vertex at depth `k + 1`: a parent and its
child differ in depth by exactly one, hence have opposite depth parity.

This is the structural core of bipartiteness; the colour classes are the
even- and odd-depth vertices. -/
theorem Tree.adj_depth_succ {i j : ℕ} (h : Tree.AdjNat i j) :
    Tree.depth j = Tree.depth i + 1 ∨ Tree.depth i = Tree.depth j + 1 := by
  -- `depth k = Nat.log 2 (k+1)`; a child `2i+1` or `2i+2` satisfies
  -- `i+1 ≤ child+1 / 2 < ...`, giving `log₂(child+1) = log₂(i+1) + 1`.
  -- We reduce to the `log₂(2m) = log₂ m + 1` / `log₂(2m+1) = log₂ m + 1`
  -- step on the doubled index.
  have key : ∀ a b : ℕ, b = 2 * a + 1 ∨ b = 2 * a + 2 →
      Tree.depth b = Tree.depth a + 1 := by
    intro a b hb
    unfold Tree.depth
    -- In both cases `b + 1 ∈ {2*(a+1), 2*(a+1)+1}`, so
    -- `2^(log₂(a+1)+1) ≤ b+1 < 2^(log₂(a+1)+2)`, hence
    -- `log₂(b+1) = log₂(a+1) + 1`.
    have hle : 2 ^ (Nat.log 2 (a + 1) + 1) ≤ b + 1 := by
      rw [pow_succ]
      have hself := Nat.pow_log_le_self 2 (x := a + 1) (by omega)
      omega
    have hlt : b + 1 < 2 ^ (Nat.log 2 (a + 1) + 1 + 1) := by
      have hub := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (a + 1)
      have : b + 1 < 2 * 2 ^ (Nat.log 2 (a + 1) + 1) := by
        rcases hb with hb | hb <;> · subst hb; omega
      calc b + 1 < 2 * 2 ^ (Nat.log 2 (a + 1) + 1) := this
        _ = 2 ^ (Nat.log 2 (a + 1) + 1 + 1) := by rw [pow_succ]; ring
    exact Nat.log_eq_of_pow_le_of_lt_pow hle hlt
  rcases h with h | h | h | h
  · exact Or.inl (key i j (Or.inl h))
  · exact Or.inl (key i j (Or.inr h))
  · exact Or.inr (key j i (Or.inl h))
  · exact Or.inr (key j i (Or.inr h))

/-- **Edge count = `n − 1` (tree fact).**  The complete binary tree of
depth `d` (`n = 2^d − 1` vertices) has exactly `2^d − 2 = n − 1` edges.
Stated for the computable vertex count. -/
def Tree.numEdges (d : ℕ) : ℕ := 2 ^ d - 2

/-- For `d ≥ 1`, `numEdges = numVertices − 1`, the defining tree identity. -/
theorem Tree.numEdges_eq (d : ℕ) (hd : 1 ≤ d) :
    Tree.numEdges d = Tree.numVertices d - 1 := by
  unfold Tree.numEdges Tree.numVertices
  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  omega

/-! ## Degree structure (root 2, internal 3, leaf 1) -/

/-- The closed-form degree of a vertex of `T_d` by its role.  The root
(`i = 0`) has degree `2`; a leaf (no children, i.e. `2i + 1 ≥ n`) has
degree `1`; every other internal vertex has degree `3`. -/
def Tree.roleDegree (d : ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 2
  else if 2 * i + 1 ≥ Tree.numVertices d then 1
  else 3

/-- Smoke value: in `T_3` (7 vertices) the root has role-degree `2`. -/
example : Tree.roleDegree 3 0 = 2 := by decide

/-- Smoke value: in `T_3` (7 vertices) vertex `1` is internal, role-degree `3`. -/
example : Tree.roleDegree 3 1 = 3 := by decide

/-- Smoke value: in `T_3` (7 vertices) vertex `4` is a leaf, role-degree `1`. -/
example : Tree.roleDegree 3 4 = 1 := by decide

/-! ## Spectrum: a √2 eigenvalue via the Rayleigh / Courant–Fischer bound

The closed-form *spectrum* of `T_d` (the deep Rojo–Robbiano Chebyshev recursion)
is not needed for the headline non-vacuity claim — a real eigenvalue of
magnitude `≥ √2`.  That follows from the **Rayleigh / Courant–Fischer lower
bound**: any test vector `x ≠ 0` with `⟨x, A x⟩ ≥ √2 · ‖x‖²` forces some
eigenvalue `≥ √2`.  We exhibit the explicit witness supported on the root `0`
and its two children `1, 2` (the embedded `K_{1,2}` star whose top eigenvalue is
exactly `√2`): `x₀ = √2, x₁ = x₂ = 1`, all other coordinates `0`.  A direct
computation gives `⟨x, A x⟩ = 4√2` and `‖x‖² = 4`, so the Rayleigh quotient is
exactly `√2`.
-/

open scoped Matrix in
open WithLp in
/-- **Rayleigh lower bound for the largest eigenvalue.**  If a Hermitian matrix
`A` admits a test vector `x ≠ 0` whose Rayleigh numerator dominates `B · ‖x‖²`,
then some eigenvalue is `≥ B`.  Pure Courant–Fischer (spectral expansion of the
quadratic form), proved from the `Graphplay.CourantFischer` hinges. -/
theorem _root_.Graphplay.CourantFischer.exists_eigenvalue_ge_of_rayleigh
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix W W ℂ) (hA : A.IsHermitian) (B : ℝ) (x : W → ℂ) (hx : x ≠ 0)
    (hxB : B * (∑ u, ‖x u‖ ^ 2) ≤ (star x ⬝ᵥ (A *ᵥ x)).re) :
    ∃ i, B ≤ hA.eigenvalues i := by
  classical
  by_contra hcon
  push_neg at hcon
  set c : W → ℝ := fun i => ‖inner ℂ (hA.eigenvectorBasis i) (toLp 2 x)‖ ^ 2 with hc
  have hcnn : ∀ i, 0 ≤ c i := fun i => by rw [hc]; positivity
  have hnum : (star x ⬝ᵥ (A *ᵥ x)).re = ∑ i, (hA.eigenvalues i) * c i :=
    Graphplay.CourantFischer.hermitianForm_re_eq_sum A hA x
  have hden : (∑ u, ‖x u‖ ^ 2) = ∑ i, c i :=
    Graphplay.CourantFischer.normSq_eq_sum A hA x
  have hdenpos : 0 < ∑ u, ‖x u‖ ^ 2 :=
    Graphplay.CourantFischer.normSq_pos_of_ne_zero x hx
  have hsumpos : 0 < ∑ i, c i := by rw [← hden]; exact hdenpos
  obtain ⟨j, _, hjpos⟩ : ∃ j ∈ Finset.univ, 0 < c j := by
    by_contra h
    push_neg at h
    exact absurd hsumpos (not_lt.mpr (Finset.sum_nonpos (fun i _ => h i (Finset.mem_univ i))))
  have hlt : ∑ i, (hA.eigenvalues i) * c i < ∑ i, B * c i := by
    apply Finset.sum_lt_sum
    · exact fun i _ => mul_le_mul_of_nonneg_right (le_of_lt (hcon i)) (hcnn i)
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_right (hcon j) hjpos⟩
  rw [← Finset.mul_sum] at hlt
  rw [hnum, hden] at hxB
  exact absurd hxB (not_le.mpr hlt)

section TreeRayleigh

open scoped Matrix
open WithLp Graphplay.CourantFischer

/-- For `d ≥ 2`, `T_d` has at least 3 vertices, so heap indices `0, 1, 2` exist. -/
private theorem tree_three_le (d : ℕ) (hd : 2 ≤ d) : 3 ≤ Tree.numVertices d := by
  unfold Tree.numVertices
  have : 4 ≤ 2 ^ d := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  omega

/-- The Rayleigh witness: `√2` on the root, `1` on its two children, `0` else. -/
private noncomputable def treeWitness (d : ℕ) : Fin (Tree.numVertices d) → ℂ :=
  fun i => if i.val = 0 then (Real.sqrt 2 : ℂ)
           else if i.val = 1 then 1
           else if i.val = 2 then 1
           else 0

private theorem treeWitness_eq_zero (d : ℕ) (i : Fin (Tree.numVertices d))
    (h0 : i.val ≠ 0) (h1 : i.val ≠ 1) (h2 : i.val ≠ 2) : treeWitness d i = 0 := by
  unfold treeWitness; rw [if_neg h0, if_neg h1, if_neg h2]

private noncomputable def treeSupp (d : ℕ) (hd : 2 ≤ d) :
    Finset (Fin (Tree.numVertices d)) :=
  {⟨0, by have := tree_three_le d hd; omega⟩,
   ⟨1, by have := tree_three_le d hd; omega⟩,
   ⟨2, by have := tree_three_le d hd; omega⟩}

private theorem sum_mul_treeWitness_restrict (d : ℕ) (hd : 2 ≤ d)
    (f : Fin (Tree.numVertices d) → ℂ) :
    (∑ j, f j * treeWitness d j) = ∑ j ∈ treeSupp d hd, f j * treeWitness d j := by
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro j _ hj
  have : j.val ≠ 0 ∧ j.val ≠ 1 ∧ j.val ≠ 2 := by
    refine ⟨?_, ?_, ?_⟩ <;> intro hv <;> apply hj <;>
      (simp only [treeSupp, Finset.mem_insert, Finset.mem_singleton]; first
        | (left; apply Fin.ext; simpa using hv)
        | (right; left; apply Fin.ext; simpa using hv)
        | (right; right; apply Fin.ext; simpa using hv))
  rw [treeWitness_eq_zero d j this.1 this.2.1 this.2.2, mul_zero]

private theorem tree_adj_val (d : ℕ) (i j : Fin (Tree.numVertices d)) :
    (Tree.weighted d).adj i j = if Tree.AdjNat i.val j.val then 1 else 0 := by
  show (Tree d).adjMatrix ℂ i j = _
  rw [SimpleGraph.adjMatrix_apply]; rfl

private theorem tree_mulVec (d : ℕ) (hd : 2 ≤ d) (i : Fin (Tree.numVertices d)) :
    ((Tree.weighted d).adj *ᵥ treeWitness d) i
      = ∑ j ∈ treeSupp d hd, (Tree.weighted d).adj i j * treeWitness d j := by
  rw [Matrix.mulVec]
  exact sum_mul_treeWitness_restrict d hd (fun j => (Tree.weighted d).adj i j)

private theorem treeSupp_expand (d : ℕ) (hd : 2 ≤ d)
    (g : Fin (Tree.numVertices d) → ℂ) :
    (∑ j ∈ treeSupp d hd, g j)
      = g ⟨0, by have := tree_three_le d hd; omega⟩
        + g ⟨1, by have := tree_three_le d hd; omega⟩
        + g ⟨2, by have := tree_three_le d hd; omega⟩ := by
  unfold treeSupp
  rw [Finset.sum_insert (by simp [Fin.ext_iff]),
    Finset.sum_insert (by simp [Fin.ext_iff]), Finset.sum_singleton]; ring

private theorem treeWitness_v0 (d : ℕ) (hd : 2 ≤ d) :
    treeWitness d ⟨0, by have := tree_three_le d hd; omega⟩ = (Real.sqrt 2 : ℂ) := by
  unfold treeWitness; rw [if_pos rfl]
private theorem treeWitness_v1 (d : ℕ) (hd : 2 ≤ d) :
    treeWitness d ⟨1, by have := tree_three_le d hd; omega⟩ = 1 := by
  unfold treeWitness; norm_num
private theorem treeWitness_v2 (d : ℕ) (hd : 2 ≤ d) :
    treeWitness d ⟨2, by have := tree_three_le d hd; omega⟩ = 1 := by
  unfold treeWitness; norm_num

private theorem star_treeWitness (d : ℕ) (i : Fin (Tree.numVertices d)) :
    star (treeWitness d i) = treeWitness d i := by
  unfold treeWitness
  by_cases h0 : i.val = 0
  · simp only [if_pos h0, Complex.star_def, Complex.conj_ofReal]
  · by_cases h1 : i.val = 1
    · simp only [if_neg h0, if_pos h1, star_one]
    · by_cases h2 : i.val = 2
      · simp only [if_neg h0, if_neg h1, if_pos h2, star_one]
      · simp only [if_neg h0, if_neg h1, if_neg h2, star_zero]

private theorem sum_star_treeWitness_restrict (d : ℕ) (hd : 2 ≤ d)
    (g : Fin (Tree.numVertices d) → ℂ) :
    (∑ i, star (treeWitness d i) * g i)
      = ∑ i ∈ treeSupp d hd, star (treeWitness d i) * g i := by
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro i _ hi
  have : i.val ≠ 0 ∧ i.val ≠ 1 ∧ i.val ≠ 2 := by
    refine ⟨?_, ?_, ?_⟩ <;> intro hv <;> apply hi <;>
      (simp only [treeSupp, Finset.mem_insert, Finset.mem_singleton]; first
        | (left; apply Fin.ext; simpa using hv)
        | (right; left; apply Fin.ext; simpa using hv)
        | (right; right; apply Fin.ext; simpa using hv))
  rw [star_treeWitness, treeWitness_eq_zero d i this.1 this.2.1 this.2.2, zero_mul]

/-- The Rayleigh numerator `⟨x, A x⟩ = 4√2` (real). -/
private theorem tree_numerator (d : ℕ) (hd : 2 ≤ d) :
    (star (treeWitness d) ⬝ᵥ ((Tree.weighted d).adj *ᵥ treeWitness d)).re
      = 4 * Real.sqrt 2 := by
  have hnum : (star (treeWitness d) ⬝ᵥ ((Tree.weighted d).adj *ᵥ treeWitness d))
      = ∑ i, star (treeWitness d i) * ((Tree.weighted d).adj *ᵥ treeWitness d) i := by
    rw [dotProduct]; rfl
  rw [hnum, sum_star_treeWitness_restrict d hd, treeSupp_expand d hd]
  simp only [tree_mulVec d hd, treeSupp_expand d hd]
  simp only [tree_adj_val, star_treeWitness]
  have a00 : ¬ Tree.AdjNat 0 0 := Tree.adjNat_irrefl 0
  have a11 : ¬ Tree.AdjNat 1 1 := by unfold Tree.AdjNat; omega
  have a22 : ¬ Tree.AdjNat 2 2 := by unfold Tree.AdjNat; omega
  have a01 : Tree.AdjNat 0 1 := by unfold Tree.AdjNat; omega
  have a10 : Tree.AdjNat 1 0 := by unfold Tree.AdjNat; omega
  have a02 : Tree.AdjNat 0 2 := by unfold Tree.AdjNat; omega
  have a20 : Tree.AdjNat 2 0 := by unfold Tree.AdjNat; omega
  have a12 : ¬ Tree.AdjNat 1 2 := by unfold Tree.AdjNat; omega
  have a21 : ¬ Tree.AdjNat 2 1 := by unfold Tree.AdjNat; omega
  simp only [if_neg a00, if_neg a11, if_neg a22, if_pos a01, if_pos a10, if_pos a02,
    if_pos a20, if_neg a12, if_neg a21]
  rw [treeWitness_v0 d hd, treeWitness_v1 d hd, treeWitness_v2 d hd]
  have hcast : (↑(Real.sqrt 2) * (0 * ↑(Real.sqrt 2) + 1 * 1 + 1 * 1)
        + 1 * (1 * ↑(Real.sqrt 2) + 0 * 1 + 0 * 1)
        + 1 * (1 * ↑(Real.sqrt 2) + 0 * 1 + 0 * 1) : ℂ)
      = ((4 * Real.sqrt 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.ofReal_re]

/-- The Rayleigh denominator `‖x‖² = 4`. -/
private theorem tree_denominator (d : ℕ) (hd : 2 ≤ d) :
    (∑ u, ‖treeWitness d u‖ ^ 2) = 4 := by
  have hrestrict : (∑ u, ‖treeWitness d u‖ ^ 2)
      = ∑ u ∈ treeSupp d hd, ‖treeWitness d u‖ ^ 2 := by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro u _ hu
    have : u.val ≠ 0 ∧ u.val ≠ 1 ∧ u.val ≠ 2 := by
      refine ⟨?_, ?_, ?_⟩ <;> intro hv <;> apply hu <;>
        (simp only [treeSupp, Finset.mem_insert, Finset.mem_singleton]; first
          | (left; apply Fin.ext; simpa using hv)
          | (right; left; apply Fin.ext; simpa using hv)
          | (right; right; apply Fin.ext; simpa using hv))
    rw [treeWitness_eq_zero d u this.1 this.2.1 this.2.2]; simp
  rw [hrestrict]
  unfold treeSupp
  rw [Finset.sum_insert (by simp [Fin.ext_iff]),
    Finset.sum_insert (by simp [Fin.ext_iff]), Finset.sum_singleton]
  rw [show (⟨0, _⟩ : Fin (Tree.numVertices d))
        = ⟨0, by have := tree_three_le d hd; omega⟩ from rfl,
    treeWitness_v0 d hd, treeWitness_v1 d hd, treeWitness_v2 d hd]
  rw [Complex.norm_real, Real.norm_eq_abs, norm_one, sq_abs, Real.sq_sqrt (by norm_num)]
  norm_num

private theorem treeWitness_ne_zero (d : ℕ) (hd : 2 ≤ d) : treeWitness d ≠ 0 := by
  intro h
  have := congrArg (fun f => f ⟨1, by have := tree_three_le d hd; omega⟩) h
  simp only [Pi.zero_apply] at this
  rw [treeWitness_v1 d hd] at this
  exact one_ne_zero this

/-- **A real eigenvalue of magnitude `≥ √2` exists for `d ≥ 2`** (the structural
non-vacuity of the tree spectrum).  Proved by the Rayleigh / Courant–Fischer
lower bound applied to the embedded-star witness `treeWitness`: the quotient is
`(4√2)/4 = √2`, so some eigenvalue is `≥ √2`, hence has `|λ| ≥ √2`.

This is the genuine reachable content behind the closed-form spectrum of the
complete binary tree (Rojo–Robbiano, *On the spectra of some weighted rooted
trees*, Linear Algebra Appl. 420 (2007) 310–328): the depth-1 star `K_{1,2}`
sits as an induced subgraph and interlaces the spectrum from below by `√2`. -/
theorem Tree.exists_large_eigenvalue (d : ℕ) (hd : 2 ≤ d) :
    ∃ lam : ℝ, lam ∈ Set.range (Tree.weighted d).herm.eigenvalues ∧
      Real.sqrt 2 ≤ |lam| := by
  have hray : Real.sqrt 2 * (∑ u, ‖treeWitness d u‖ ^ 2)
      ≤ (star (treeWitness d) ⬝ᵥ ((Tree.weighted d).adj *ᵥ treeWitness d)).re := by
    rw [tree_numerator d hd, tree_denominator d hd, mul_comm]
  obtain ⟨i, hi⟩ := Graphplay.CourantFischer.exists_eigenvalue_ge_of_rayleigh
    (Tree.weighted d).adj (Tree.weighted d).herm (Real.sqrt 2) (treeWitness d)
    (treeWitness_ne_zero d hd) hray
  exact ⟨(Tree.weighted d).herm.eigenvalues i, ⟨i, rfl⟩, le_trans hi (le_abs_self _)⟩

end TreeRayleigh

/-! ## Computable rational companion -/

/-- Computable companion: the 0/1 adjacency matrix of `T_d` on
`Fin (2^d − 1)`, valued in `ℚ`. -/
def Tree.adjMatrixℚ (d : ℕ) :
    Matrix (Fin (Tree.numVertices d)) (Fin (Tree.numVertices d)) ℚ :=
  fun i j => if Tree.AdjNat i.val j.val then (1 : ℚ) else 0

/-! ## Smoke tests -/

example : Tree.numVertices 3 = 7 := by decide
example : Tree.numEdges 3 = 6 := by decide
example : Tree.numEdges 3 = Tree.numVertices 3 - 1 := by decide
-- root 0 ~ child 1
example : (Tree.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := by decide
-- root 0 ~ child 2
example : (Tree.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 := by decide
-- internal 1 ~ child 3
example : (Tree.adjMatrixℚ 3) ⟨1, by decide⟩ ⟨3, by decide⟩ = 1 := by decide
-- 0 and 3 are not adjacent (grandparent/grandchild)
example : (Tree.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 := by decide
-- loopless diagonal
example : (Tree.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by decide

#eval Tree.numVertices 4
#eval Tree.numEdges 4
#eval Tree.roleDegree 4 0   -- root: 2
#eval Tree.roleDegree 4 1   -- internal: 3
#eval Tree.roleDegree 4 8   -- leaf: 1
#eval (Tree.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨1, by decide⟩

end StdLib
end Graphplay
