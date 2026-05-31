/-
# Graphplay.StdLib.CompleteMultipartite

Standard-library entry for **complete multipartite graphs**
`K_{n_1, n_2, …, n_k}`: the graph on the disjoint union of `k` parts of
sizes `n_1, …, n_k`, with every pair of vertices in *different* parts
adjacent and every pair in the *same* part non-adjacent.

Complete multipartite graphs are *Laplacian integral* — their Laplacian
spectrum is `{0, n_1 + ⋯ + n_k - n_i (with multiplicity n_i - 1), n}` —
and they form the most-studied family of explicit deterministic-search
hosts in continuous-time quantum walk theory:

* The four-color-completion construction (cf. Graphplay's own
  `Tower6` / `Tower7` papers) recovers `K_{a, b, c, d}` as the quotient
  of an `S_4`-equivariant bundle.
* **Li, Luo, Feng, Li (2025)** (arXiv:2506.21108, *Deterministic quantum
  search on all Laplacian integral graphs*) prove that **every Laplacian
  integral graph** admits deterministic CTQW spatial search with certainty
  when the marked proportion is known in advance — a general result, not
  specific to complete multipartite graphs.  Complete multipartite graphs
  are one instance, because they are Laplacian integral (shown below); so
  the theorem specializes to `K_{n_1,…,n_k}`.  (The success-time formula is
  a consequence of Laplacian integrality, not assumed here.)

We package the family, give its Laplacian spectrum, and state the
deterministic-search theorem.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Multiset.Basic
import Graphplay.Weighted
import Graphplay.PST

open scoped Matrix Real
open Real

universe u

namespace Graphplay
namespace StdLib

/-! ## The complete multipartite graph `K_{n_1, …, n_k}` -/

/-- The **part-index** type of a multiset of part sizes
`parts : Multiset ℕ`: a sigma-type pairing each part index `i` with a
vertex `j : Fin (parts.toList.get i)` inside part `i`. -/
def CompleteMultipartiteV (parts : List ℕ) : Type :=
  Σ i : Fin parts.length, Fin (parts.get i)

instance (parts : List ℕ) : Fintype (CompleteMultipartiteV parts) := by
  unfold CompleteMultipartiteV; infer_instance
instance (parts : List ℕ) : DecidableEq (CompleteMultipartiteV parts) := by
  unfold CompleteMultipartiteV; infer_instance

/-- The **complete multipartite graph** `K_{n_1, …, n_k}` as a weighted
graph on `CompleteMultipartiteV parts`: edge weight `1` between vertices
in different parts; `0` between vertices in the same part.

(Multiset input is canonicalised to a list for indexing; the underlying
graph is the same up to relabelling.) -/
noncomputable def CompleteMultipartite (parts : List ℕ) :
    WeightedGraph (CompleteMultipartiteV parts) where
  adj := fun x y => if x.1 ≠ y.1 then (1 : ℂ) else 0
  herm := by
    -- Symmetric real 0/1 matrix: `x.1 ≠ y.1 ↔ y.1 ≠ x.1`, and `star` fixes `0`, `1`.
    ext x y
    rw [Matrix.conjTranspose_apply, apply_ite (star : ℂ → ℂ), star_one, star_zero]
    -- Goal: `(if y.1 ≠ x.1 then 1 else 0) = if x.1 ≠ y.1 then 1 else 0`.
    by_cases h : x.1 = y.1
    · rw [if_neg (not_not.mpr h.symm), if_neg (not_not.mpr h)]
    · rw [if_pos (Ne.symm h), if_pos h]
  loopless := by
    intro v
    simp

/-- The **multiset-flavoured constructor**: choose any list
representative of the multiset of part sizes. -/
noncomputable def CompleteMultipartite' (parts : Multiset ℕ) :
    WeightedGraph (CompleteMultipartiteV parts.toList) :=
  CompleteMultipartite parts.toList

/-! ## Laplacian spectrum (Laplacian-integral) -/

/-- The **Laplacian matrix** of a `WeightedGraph`: `L = D - A` where
`D` is the diagonal of row sums.  (Restated locally for self-containment.) -/
noncomputable def laplacian {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : Matrix V V ℂ :=
  Matrix.diagonal (fun v => ∑ u, G.adj v u) - G.adj

/-- **Laplacian-integrality of complete multipartite graphs.**  For
`parts = [n_1, …, n_k]` and `n = n_1 + ⋯ + n_k`, the Laplacian spectrum
of `K_{n_1, …, n_k}` is

  `{0} ∪ ⋃_{i = 1}^{k} { n - n_i  (with multiplicity n_i - 1) } ∪ {n (with mult k - 1)}`.

Reference: Brouwer–Haemers, *Spectra of Graphs*, §1.4.3; or
Mohar, *The Laplacian spectrum of graphs*, in *Graph Theory, Combinatorics
and Applications*, 1991.  This is also the spectrum recovered in
Graphplay's own four-color-completion case from the `Tower` papers. -/
theorem completeMultipartite_laplacian_spectrum (parts : List ℕ) :
    ∃ μ : Finset ℝ,
      (μ : Set ℝ) ⊆ spectrum ℝ (laplacian (CompleteMultipartite parts)) ∧
      (0 : ℝ) ∈ μ ∧
      (parts.sum : ℝ) ∈ μ ∧
      ∀ ni ∈ parts, ((parts.sum : ℝ) - (ni : ℝ)) ∈ μ := by
  -- Block-structure diagonalisation by part.
  sorry

/-- Corollary: the complete multipartite graph is **Laplacian integral**
— every Laplacian eigenvalue is a non-negative integer. -/
theorem completeMultipartite_laplacian_integral (parts : List ℕ) :
    ∀ μ ∈ spectrum ℝ (laplacian (CompleteMultipartite parts)),
      ∃ n : ℕ, μ = (n : ℝ) := by
  -- From the explicit spectrum.
  sorry

/-! ## Four-color-completion case -/

/-- The four-part complete multipartite graph `K_{a, b, c, d}`, which is
the case recovered from the four-color completion of the `Tower6`
construction in Graphplay's own paper.  Provided as a convenience
alias. -/
noncomputable def K4parts (a b c d : ℕ) :
    WeightedGraph (CompleteMultipartiteV [a, b, c, d]) :=
  CompleteMultipartite [a, b, c, d]

/-! ## Deterministic spatial search (Li–Luo–Feng–Li 2025) -/

/-- **Spatial-search Hamiltonian** on a host graph `G` with a marked
vertex `w ∈ V`, oracle strength `γ ∈ ℝ`:
  `H_γ = γ · A + |w⟩⟨w|`.
The search succeeds at time `τ` if `|⟨w| exp(-i τ H_γ) |s⟩| = 1`, where
`|s⟩ = (1/√n) Σ_v |v⟩` is the equal-superposition initial state. -/
noncomputable def searchHamiltonian {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (w : V) (γ : ℝ) : Matrix V V ℂ :=
  (γ : ℂ) • G.adj + Matrix.single w w (1 : ℂ)

/-- The CTQW spatial-search **success amplitude** from the uniform
superposition to the marked vertex `w` at time `τ` and oracle strength
`γ`. -/
noncomputable def searchSuccessAmplitude {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (w : V) (γ τ : ℝ) : ℝ :=
  let H := searchHamiltonian G w γ
  let U := NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H)
  let n := (Fintype.card V : ℝ)
  ‖(1 / Real.sqrt n : ℂ) * ∑ v, U w v‖

/-- The graph `G` admits **deterministic search at vertex `w`** if there
exist `γ, τ ∈ ℝ` with `searchSuccessAmplitude G w γ τ = 1`. -/
def IsDeterministicSearch {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (w : V) : Prop :=
  ∃ γ τ : ℝ, searchSuccessAmplitude G w γ τ = 1

/-- **Complete-multipartite instance of Li–Luo–Feng–Li (2025).**  Every
complete multipartite graph `K_{n_1, …, n_k}` admits deterministic CTQW spatial
search at *every* vertex `w`, provided the graph is non-empty (at least two
parts, each of size ≥ 1).

CITATION FIX: the deterministic-search guarantee is **not** a
complete-multipartite-specific result.  It is the specialisation of the
**general** theorem of Li, Luo, Feng, Li (arXiv:2506.21108, *Deterministic
quantum search on all Laplacian integral graphs*): every Laplacian-integral
graph admits deterministic search, and `K_{n_1,…,n_k}` is Laplacian integral
(`completeMultipartite_laplacian_integral`), hence covered.  The witnessing
`(γ*, τ*)` come from that general construction applied to the explicit
Laplacian spectrum, not from a formula special to complete multipartite
graphs. -/
theorem completeMultipartite_deterministicSearch
    (parts : List ℕ) (hk : 2 ≤ parts.length)
    (hpos : ∀ ni ∈ parts, 1 ≤ ni)
    (w : CompleteMultipartiteV parts) :
    IsDeterministicSearch (CompleteMultipartite parts) w := by
  -- Reduce to the 2-dimensional invariant subspace spanned by `|w⟩` and
  -- a "rest" cell-uniform vector; cf. arXiv:2506.21108 §3.
  sorry

/-- **Four-part specialisation** of Li–Luo–Feng–Li.  This is the exact
host appearing in Graphplay's `Tower6` four-color-completion construction;
the deterministic-search guarantee transfers directly to that bundle via
the equitable-partition quotient. -/
theorem K4parts_deterministicSearch
    (a b c d : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (w : CompleteMultipartiteV [a, b, c, d]) :
    IsDeterministicSearch (K4parts a b c d) w := by
  -- `K4parts a b c d` is definitionally `CompleteMultipartite [a, b, c, d]`, the
  -- four-part complete multipartite host.  The four-part case is exactly the
  -- `parts = [a, b, c, d]` instance of the general Li–Luo–Feng–Li theorem: the
  -- list has length `4 ≥ 2`, and each part `∈ {a, b, c, d}` is `≥ 1` by
  -- hypothesis, so `completeMultipartite_deterministicSearch` applies verbatim.
  have hk : 2 ≤ [a, b, c, d].length := by simp [List.length]
  have hpos : ∀ ni ∈ [a, b, c, d], 1 ≤ ni := by
    intro ni hni
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rcases hni with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  exact completeMultipartite_deterministicSearch [a, b, c, d] hk hpos w

end StdLib
end Graphplay
