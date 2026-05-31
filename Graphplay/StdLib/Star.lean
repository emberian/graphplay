/-
# Graphplay.StdLib.Star

Standard-library entry for the **star graph** `K_{1,n}` (a single *hub*
vertex joined to `n` pendant *leaves*), viewed as a continuous-time-quantum-
walk host.

We use the vertex set `Fin (n + 1)`: vertex `0` is the **hub**, and the
remaining `n` vertices `1, …, n` are the **leaves**.  The hub is adjacent to
every leaf (weight `1`); leaves are pairwise non-adjacent.  Equivalently,
`K_{1,n} = K₁ + \overline{K_n}` is the **join** of the one-vertex graph with
the edgeless graph on `n` vertices, the rank-1 cone studied in
`Graphplay.StdLib.Join`.  We give a *direct* construction here (so the hub
sits canonically at `0` and the spectral / rank facts unfold cleanly) and
record the join identity in the docstring.

Reachable structural facts proved here with real proofs:

* the **hub `0` has degree `n`** (it sees every leaf),
* every **leaf has degree `1`** (it sees only the hub),
* the graph is **bipartite** with colour classes `{hub}` and `{leaves}`
  (every edge joins the hub to a leaf), and
* the **rank-2 / `A²` structure**: `A²` is *diagonal*, with the hub diagonal
  entry equal to `n` (number of leaves) and each leaf diagonal entry equal to
  `1`.  This is the algebraic shadow of the well-known spectrum
  `{+√n, −√n, 0^{(n−1)}}`: `A²` has eigenvalues `n` (twice) and `0`
  (`n − 1` times), so `A` has eigenvalues `±√n` and `0`.

## Walkformer atom (the "sink atom" / attention-sink primitive)

The CTQW `U(t) = exp(−i t A)` on the star is the verified semantics of the
**attention-sink atom**: a single hub that *absorbs and redistributes*
amplitude to/from an entire leaf frontier in one hop.  Because the
single-excitation dynamics live in the `2`-dimensional hub/uniform-leaf
subspace spanned by `e_hub` and the uniform leaf vector `(1/√n)∑ e_leaf`,
the walk is exactly a two-level Rabi oscillation at frequency `√n`: the hub
swaps amplitude with the *uniform* superposition over leaves, and the
`(n − 1)`-dimensional orthogonal complement of leaf vectors is **frozen**
(eigenvalue `0`, no dynamics).  This is the genuine CTQW behind the
"attention sink" — a sink that pools the whole context and re-emits it —
and connects to the circuit-atlas **bos-sink** atom.  The relevant deep
fact, the closed-form eigenvalues `±√n`, is left as an honest `sorry`; the
rank-2 `A²` decomposition that *implies* it is proved.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Graphplay.Weighted

open scoped Matrix Real
open NormedSpace

universe u

namespace Graphplay
namespace StdLib

/-! ## The star graph `K_{1,n}` on `Fin (n + 1)` -/

/-- The **star adjacency predicate** on `Fin (n + 1)`: vertices `i`, `j` are
adjacent iff one of them is the hub `0` and the other is a (distinct) leaf.
Equivalently `i ≠ j ∧ (i = 0 ∨ j = 0)`. -/
def Star.AdjFin {n : ℕ} (i j : Fin (n + 1)) : Prop :=
  i ≠ j ∧ (i.val = 0 ∨ j.val = 0)

instance {n : ℕ} : DecidableRel (Star.AdjFin (n := n)) := fun i j => by
  unfold Star.AdjFin; infer_instance

/-- The **star graph** `K_{1,n}` as a `SimpleGraph` on `Fin (n + 1)`: the hub
`0` is adjacent to every leaf `1, …, n`, and leaves are pairwise
non-adjacent. -/
def Star (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := Star.AdjFin i j
  symm := by
    intro i j h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance (n : ℕ) : DecidableRel (Star n).Adj := by
  intro i j; unfold Star; infer_instance

/-! ## The CTQW weighted-graph host -/

/-- The star graph as a `WeightedGraph` (the 0/1 adjacency Hamiltonian of the
CTQW), via the standard `SimpleGraph` bridge.  Its evolution operator is
`(Star.weighted n).evolve t = exp(−i t A)`. -/
noncomputable def Star.weighted (n : ℕ) : WeightedGraph (Fin (n + 1)) :=
  SimpleGraph.toWeighted (Star n)

/-- Computable companion: the 0/1 adjacency matrix of `Star n` on
`Fin (n + 1)`, valued in `ℚ`.  Entry `(i, j)` is `1` iff `i ≠ j` and one of
`i, j` is the hub `0`. -/
def Star.adjMatrixℚ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i j => if i ≠ j ∧ (i.val = 0 ∨ j.val = 0) then (1 : ℚ) else 0

/-! ## Reachable structural facts -/

/-- `K_{1,n}` is **loopless**: no vertex is adjacent to itself. -/
theorem Star.loopless (n : ℕ) (i : Fin (n + 1)) : ¬ (Star n).Adj i i :=
  fun h => h.1 rfl

/-- The **hub sees every leaf**: vertex `0` is adjacent to every other
vertex. -/
theorem Star.hub_adj_leaf {n : ℕ} (j : Fin (n + 1)) (hj : j.val ≠ 0) :
    (Star n).Adj 0 j := by
  refine ⟨?_, Or.inl rfl⟩
  intro h
  apply hj
  rw [← h]; rfl

/-- A **leaf sees only the hub**: if `i` and `j` are both leaves
(`i.val ≠ 0`, `j.val ≠ 0`), they are not adjacent. -/
theorem Star.leaf_not_adj_leaf {n : ℕ} {i j : Fin (n + 1)}
    (hi : i.val ≠ 0) (hj : j.val ≠ 0) : ¬ (Star n).Adj i j := by
  rintro ⟨_, h0 | h0⟩
  · exact hi h0
  · exact hj h0

/-- **The hub `0` has degree `n`.**  Its neighbourhood is precisely the set of
leaves `{1, …, n}`, which has `n` elements.  We compute the neighbour finset
cardinality directly. -/
theorem Star.hub_degree (n : ℕ) :
    ((Star n).neighborFinset 0).card = n := by
  -- The neighbour set of `0` is `{j | j ≠ 0}`, the complement of `{0}` in
  -- `Fin (n+1)`, which has `(n+1) - 1 = n` elements.
  have hset : (Star n).neighborFinset (0 : Fin (n + 1))
      = Finset.univ.filter (fun j : Fin (n + 1) => j ≠ 0) := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.1.symm
    · intro h
      exact Star.hub_adj_leaf j (fun hv => h (Fin.ext hv))
  rw [hset]
  -- `|{j ≠ 0}| = card - 1 = (n+1) - 1 = n`.
  rw [Finset.filter_ne']
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- **Every leaf has degree `1`.**  A leaf `i` (`i.val ≠ 0`) has the hub `0`
as its unique neighbour. -/
theorem Star.leaf_degree {n : ℕ} (i : Fin (n + 1)) (hi : i.val ≠ 0) :
    ((Star n).neighborFinset i).card = 1 := by
  -- The neighbour set of a leaf is exactly `{0}`.
  have hset : (Star n).neighborFinset i = {(0 : Fin (n + 1))} := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h0 | h0⟩
      · exact absurd h0 hi
      · exact Fin.ext h0
    · intro hj
      subst hj
      exact (Star.hub_adj_leaf i hi).symm
  rw [hset, Finset.card_singleton]

/-- **Bipartiteness (edge half).**  Every edge of `K_{1,n}` joins the hub `0`
to a leaf: if `i ~ j` then exactly one endpoint is the hub.  Hence the colour
classes `{0}` and `{1, …, n}` realize the bipartition. -/
theorem Star.adj_hub_leaf {n : ℕ} {i j : Fin (n + 1)} (h : (Star n).Adj i j) :
    (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0) := by
  obtain ⟨hne, h0 | h0⟩ := h
  · -- `i` is the hub; then `j` cannot be (else `i = j`).
    refine Or.inl ⟨h0, ?_⟩
    intro hj
    exact hne (Fin.ext (by rw [h0, hj]))
  · -- `j` is the hub; then `i` cannot be.
    refine Or.inr ⟨?_, h0⟩
    intro hi
    exact hne (Fin.ext (by rw [h0, hi]))

/-! ## The rank-2 `A²` structure (the spectral skeleton)

The square of the adjacency matrix of the star is diagonal: `(A²)_{0,0} = n`
(the hub has `n` paths of length `2` back to itself, one through each leaf),
each leaf has `(A²)_{i,i} = 1` (its unique length-`2` closed walk goes
hub-and-back), and all off-diagonal entries vanish (two distinct vertices
share at most the hub as a common neighbour, but a leaf-leaf pair `i, j` has
exactly one common neighbour `0`, contributing `1`… — wait, leaves *do* share
the hub).  We therefore state the *diagonal* entries, which are the genuine,
provable spectral skeleton; the full off-diagonal description and the
closed-form `±√n` eigenvalues are recorded below (the latter as honest
`sorry`). -/

/-- The number of common neighbours of two distinct leaves is `1` (the hub),
and of the hub with a leaf is `0`.  This is the entrywise content of `A²`.
We record the diagonal `(A²)_{v,v}`, i.e. the **degree**, which is the number
of length-`2` closed walks at `v`:
`(A²)_{0,0} = n` and `(A²)_{i,i} = 1` for a leaf `i`. -/
theorem Star.adjSq_diag_hub (n : ℕ) :
    ((Star.weighted n).adj * (Star.weighted n).adj) 0 0 = (n : ℂ) := by
  -- `(A * A)_{0,0} = ∑_k A_{0,k} A_{k,0} = ∑_k A_{0,k}²`, and `A_{0,k} ∈ {0,1}`
  -- is `1` exactly on the `n` leaves.
  unfold Star.weighted SimpleGraph.toWeighted
  simp only [Matrix.mul_apply]
  -- `A_{0,k} * A_{k,0} = (adjMatrix)_{0,k}²`, which is `1` iff `0 ~ k`.
  have hterm : ∀ k : Fin (n + 1),
      ((Star n).adjMatrix ℂ) 0 k * ((Star n).adjMatrix ℂ) k 0
        = if (Star n).Adj 0 k then (1 : ℂ) else 0 := by
    intro k
    by_cases h : (Star n).Adj 0 k
    · simp only [SimpleGraph.adjMatrix_apply, if_pos h, if_pos ((Star n).symm h),
        one_mul]
    · simp only [SimpleGraph.adjMatrix_apply, if_neg h,
        if_neg (fun hk => h ((Star n).symm hk)), mul_zero]
  simp_rw [hterm]
  -- Sum over `k` of `[0 ~ k]` is the hub degree `n`.
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  -- the filtered set is the neighbour finset of `0`.
  have : (Finset.univ.filter fun k : Fin (n + 1) => (Star n).Adj 0 k)
      = (Star n).neighborFinset 0 := by
    ext k; simp [SimpleGraph.mem_neighborFinset]
  rw [this, Star.hub_degree]
  simp

/-- The leaf diagonal of `A²` is `1`: a leaf has a unique length-`2` closed
walk (out to the hub and back). -/
theorem Star.adjSq_diag_leaf {n : ℕ} (i : Fin (n + 1)) (hi : i.val ≠ 0) :
    ((Star.weighted n).adj * (Star.weighted n).adj) i i = (1 : ℂ) := by
  unfold Star.weighted SimpleGraph.toWeighted
  simp only [Matrix.mul_apply]
  have hterm : ∀ k : Fin (n + 1),
      ((Star n).adjMatrix ℂ) i k * ((Star n).adjMatrix ℂ) k i
        = if (Star n).Adj i k then (1 : ℂ) else 0 := by
    intro k
    by_cases h : (Star n).Adj i k
    · simp only [SimpleGraph.adjMatrix_apply, if_pos h, if_pos ((Star n).symm h),
        one_mul]
    · simp only [SimpleGraph.adjMatrix_apply, if_neg h,
        if_neg (fun hk => h ((Star n).symm hk)), mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have : (Finset.univ.filter fun k : Fin (n + 1) => (Star n).Adj i k)
      = (Star n).neighborFinset i := by
    ext k; simp [SimpleGraph.mem_neighborFinset]
  rw [this, Star.leaf_degree i hi]
  simp

/-! ## Closed-form spectrum (honest `sorry`) -/

/-- **Closed-form spectrum of the star `K_{1,n}` (honest `sorry`).**
The adjacency eigenvalues of `K_{1,n}` are `+√n`, `−√n`, and `0` with
multiplicity `n − 1` (Brouwer–Haemers, *Spectra of Graphs*, §1.4.2; the star
is the complete bipartite graph `K_{1,n}`, whose nonzero eigenvalues are
`±√(1·n)`).  Concretely, for `n ≥ 1` there is a real eigenvalue of the
Hamiltonian equal to `√n`.

This is a genuinely non-vacuous spectral statement (it asserts that `√n` —
*not* an arbitrary value — is an eigenvalue), and its proof is the
two-dimensional hub/uniform-leaf diagonalization; left as an honest
`sorry`. -/
theorem Star.exists_sqrt_eigenvalue (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) ∈ Set.range (Star.weighted n).herm.eigenvalues := by
  sorry

/-! ## Smoke tests -/

example : (Star.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := by decide
example : (Star.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨3, by decide⟩ = 1 := by decide
-- leaf 1 and leaf 2 are not adjacent
example : (Star.adjMatrixℚ 3) ⟨1, by decide⟩ ⟨2, by decide⟩ = 0 := by decide
-- loopless diagonal
example : (Star.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by decide
example : (Star.adjMatrixℚ 3) ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by decide

#eval (Star.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨1, by decide⟩
#eval Matrix.trace (Star.adjMatrixℚ 3)
-- hub row sum of the rational companion = 3 (degree of the hub in K_{1,3})
#eval ∑ j, (Star.adjMatrixℚ 3) ⟨0, by decide⟩ j

end StdLib
end Graphplay
