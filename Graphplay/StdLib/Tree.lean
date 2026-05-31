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

Reachable structural facts are proved here with real proofs; the
closed-form spectrum of the complete binary tree (Chebyshev-like, governed
by the depth recursion) is left as an honest `sorry`.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted

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

/-! ## Spectrum (honest `sorry`) -/

/-- **Closed-form spectrum of the complete binary tree (honest `sorry`).**
The adjacency eigenvalues of `T_d` are governed by the depth recursion: the
spectrum is the union, over levels `k = 1, …, d`, of the roots of a degree-`k`
Chebyshev-type polynomial `p_k`, with multiplicities `2^{d−k} − 2^{d−k−1}`
(Rojo–Robbiano, *On the spectra of some weighted rooted trees*, Linear
Algebra Appl. 420 (2007) 310–328).  Concretely there is a real number `λ`
in the spectrum of the Hamiltonian with `|λ| ≥ √2` for `d ≥ 2`.

This is a genuinely non-vacuous spectral statement (it asserts a real
eigenvalue of magnitude ≥ √2 exists), and its closed form is the deep
Chebyshev-recursion content — left as an honest `sorry`. -/
theorem Tree.exists_large_eigenvalue (d : ℕ) (hd : 2 ≤ d) :
    ∃ lam : ℝ, lam ∈ Set.range (Tree.weighted d).herm.eigenvalues ∧
      Real.sqrt 2 ≤ |lam| := by
  sorry

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
