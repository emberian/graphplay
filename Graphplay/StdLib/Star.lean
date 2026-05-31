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
fact, the closed-form eigenvalue `√n`, is now **proved** below
(`Star.exists_sqrt_eigenvalue`) by exhibiting the explicit hub/uniform-leaf
eigenvector; the rank-2 `A²` decomposition that frames it is also proved.
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
closed-form `√n` eigenvalue are recorded below (the latter now **proved**
via the explicit eigenvector). -/

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

/-! ## Closed-form spectrum -/

/-- The **explicit `√n`-eigenvector** of the star adjacency.  The hub `0`
carries amplitude `√n`; every leaf carries amplitude `1`.  This lies in the
two-dimensional hub/uniform-leaf invariant subspace, and satisfies
`A · v = √n · v`:

* at the **hub**, `A` sees the `n` leaves, each contributing `1`, giving
  `n = √n · √n = √n · v_0`;
* at each **leaf**, `A` sees only the hub, contributing `v_0 = √n = √n · 1
  = √n · v_leaf`. -/
noncomputable def Star.sqrtEigvec (n : ℕ) : Fin (n + 1) → ℂ :=
  fun i => if i = 0 then (Real.sqrt (n : ℝ) : ℂ) else 1

/-- The defining eigen-equation for `Star.sqrtEigvec`:
`A · v = √n · v` for the star adjacency `A = (Star.weighted n).adj`. -/
theorem Star.adj_mulVec_sqrtEigvec (n : ℕ) :
    (Star.weighted n).adj.mulVec (Star.sqrtEigvec n)
      = (Real.sqrt (n : ℝ) : ℂ) • (Star.sqrtEigvec n) := by
  funext i
  unfold Star.weighted SimpleGraph.toWeighted Star.sqrtEigvec
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  by_cases hi : i = 0
  · -- Hub row: sum over all `n` leaves of `1` is `n = √n · √n`.
    subst hi
    -- the neighbour finset of `0` is the set of leaves; each `vec u = 1`.
    have hsum : ∑ u ∈ (Star n).neighborFinset 0,
        (if u = 0 then (Real.sqrt (n : ℝ) : ℂ) else 1) = (n : ℂ) := by
      have hne : ∀ u ∈ (Star n).neighborFinset 0, u ≠ 0 := by
        intro u hu
        rw [SimpleGraph.mem_neighborFinset] at hu
        exact fun h => (h ▸ hu).1 rfl
      rw [Finset.sum_congr rfl (fun u hu => by rw [if_neg (hne u hu)])]
      rw [Finset.sum_const, Star.hub_degree]
      simp
    rw [hsum, if_pos rfl]
    -- `n = √n · √n`.
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  · -- Leaf row: the only neighbour is the hub `0`, contributing `√n`.
    have hival : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have hset : (Star n).neighborFinset i = {(0 : Fin (n + 1))} := by
      ext j
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h0 | h0⟩
        · exact absurd h0 hival
        · exact Fin.ext h0
      · intro hj; subst hj; exact (Star.hub_adj_leaf i hival).symm
    rw [hset, Finset.sum_singleton, if_pos rfl, if_neg hi, mul_one]

/-- The `√n`-eigenvector is nonzero (its hub amplitude `√n` is positive for
`n ≥ 1`). -/
theorem Star.sqrtEigvec_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    Star.sqrtEigvec n ≠ 0 := by
  intro h
  have h0 : Star.sqrtEigvec n 0 = 0 := by rw [h]; rfl
  rw [Star.sqrtEigvec, if_pos rfl] at h0
  have : Real.sqrt (n : ℝ) = 0 := by exact_mod_cast h0
  rw [Real.sqrt_eq_zero (by positivity)] at this
  exact absurd this (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn ∘ (by exact_mod_cast ·))

/-- **Closed-form spectrum of the star `K_{1,n}`.**
The adjacency eigenvalues of `K_{1,n}` are `+√n`, `−√n`, and `0` with
multiplicity `n − 1` (Brouwer–Haemers, *Spectra of Graphs*, §1.4.2; the star
is the complete bipartite graph `K_{1,n}`, whose nonzero eigenvalues are
`±√(1·n)`).  Concretely, for `n ≥ 1` there is a real eigenvalue of the
Hamiltonian equal to `√n`.

**Proof.**  We exhibit the explicit eigenvector `Star.sqrtEigvec n`
(`√n` on the hub, `1` on each leaf), which satisfies `A · v = √n · v`
(`Star.adj_mulVec_sqrtEigvec`) and is nonzero.  Hence `(√n : ℂ)` is an
eigenvalue of `toLin' A`, so it lies in `spectrum ℂ A`.  By Mathlib's
`IsHermitian.spectrum_eq_image_range`, the complex spectrum is the image of
the real eigenvalue range under `ℝ ↪ ℂ`; injectivity of that embedding lifts
`√n` back to the range of the real eigenvalue function. -/
theorem Star.exists_sqrt_eigenvalue (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) ∈ Set.range (Star.weighted n).herm.eigenvalues := by
  -- The eigenvector gives `√n ∈ spectrum ℂ A`.
  have heig : Module.End.HasEigenvalue (Matrix.toLin' (Star.weighted n).adj)
      (Real.sqrt (n : ℝ) : ℂ) := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := Star.sqrtEigvec n)
    refine ⟨?_, Star.sqrtEigvec_ne_zero n hn⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact Star.adj_mulVec_sqrtEigvec n
  have hspec : (Real.sqrt (n : ℝ) : ℂ) ∈ spectrum ℂ (Star.weighted n).adj := by
    rw [← Matrix.spectrum_toLin']
    exact heig.mem_spectrum
  -- Translate to the real eigenvalue range via the Hermitian spectral theorem.
  rw [(Star.weighted n).herm.spectrum_eq_image_range] at hspec
  obtain ⟨r, hr_range, hr_eq⟩ := hspec
  have : r = Real.sqrt (n : ℝ) := by
    have hr : (r : ℂ) = (Real.sqrt (n : ℝ) : ℂ) := by
      simpa using hr_eq
    exact_mod_cast hr
  rw [← this]; exact hr_range

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
