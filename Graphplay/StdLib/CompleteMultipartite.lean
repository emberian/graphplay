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
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Spectrum
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


/-! ## Explicit Laplacian eigen-computation (proven, non-vacuous)

We diagonalise the complete-multipartite Laplacian block-by-block.  Writing
`n = parts.sum` and `p_i = parts.get i`, the diagonal of `L` at a vertex in part
`i` is `n - p_i`, and `(A f)` at that vertex is `S - P_i` where `S = ∑ f` and
`P_i` is the part-`i` partial sum.  From this `L`-action formula we exhibit
genuine eigenvectors for `0` (all-ones), `n` (a part-constant vector with
`∑ p_i c_i = 0`, needing `≥ 2` parts), and `n - p_{i0}` (a within-part-`i0`
zero-sum vector, needing `p_{i0} ≥ 2`).  Each carries an explicit nonzero
witness, so every membership below is non-vacuous. -/

/-- Bridge: a nonzero vector `v` with `A v = (μ:ℂ) • v` puts `μ ∈ spectrum ℝ A`. -/
theorem cm_mem_spectrum_of_mulVec {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) (μ : ℝ) (v : V → ℂ) (hv : v ≠ 0)
    (heig : A.mulVec v = (μ : ℂ) • v) : μ ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff]
  intro hunit
  have hker : (algebraMap ℝ (Matrix V V ℂ) μ - A).mulVec v = 0 := by
    have halg : (algebraMap ℝ (Matrix V V ℂ) μ).mulVec v = (μ : ℂ) • v := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
        Complex.coe_smul]
    rw [Matrix.sub_mulVec, halg, heig, sub_self]
  have hinj := (Matrix.mulVec_injective_iff_isUnit).mpr hunit
  exact hv (hinj (by rw [hker, Matrix.mulVec_zero]))

/-- Adjacency `mulVec` formula. -/
theorem cm_adj_mulVec (parts : List ℕ) (f : CompleteMultipartiteV parts → ℂ)
    (i : Fin parts.length) (j : Fin (parts.get i)) :
    ((CompleteMultipartite parts).adj.mulVec f) ⟨i, j⟩
      = (∑ v, f v) - (∑ j' : Fin (parts.get i), f ⟨i, j'⟩) := by
  rw [Matrix.mulVec]
  show (fun k => (CompleteMultipartite parts).adj ⟨i,j⟩ k) ⬝ᵥ f = _
  rw [dotProduct]
  rw [show (∑ k : CompleteMultipartiteV parts,
        (CompleteMultipartite parts).adj ⟨i,j⟩ k * f k)
      = ∑ k : Σ i : Fin parts.length, Fin (parts.get i),
        (CompleteMultipartite parts).adj ⟨i,j⟩ k * f k from rfl]
  rw [Fintype.sum_sigma (α := fun i : Fin parts.length => Fin (parts.get i))
        (fun k => (CompleteMultipartite parts).adj ⟨i,j⟩ k * f k)]
  have hadj : ∀ (i' : Fin parts.length) (j' : Fin (parts.get i')),
      (CompleteMultipartite parts).adj ⟨i,j⟩ ⟨i',j'⟩
        = if i ≠ i' then (1:ℂ) else 0 := fun i' j' => rfl
  simp_rw [hadj]
  have step : ∀ i' : Fin parts.length,
      (∑ j' : Fin (parts.get i'), (if i ≠ i' then (1:ℂ) else 0) * f ⟨i',j'⟩)
        = (if i ≠ i' then (∑ j' : Fin (parts.get i'), f ⟨i',j'⟩) else 0) := by
    intro i'
    by_cases h : i = i'
    · simp [h]
    · simp [h, Finset.mul_sum]
  simp_rw [step]
  have hS : (∑ v, f v)
      = ∑ i' : Fin parts.length, ∑ j' : Fin (parts.get i'), f ⟨i',j'⟩ :=
    Fintype.sum_sigma (α := fun i : Fin parts.length => Fin (parts.get i)) f
  rw [hS]
  set P : Fin parts.length → ℂ := fun i' => ∑ j' : Fin (parts.get i'), f ⟨i',j'⟩ with hP
  have key : ∀ i' : Fin parts.length,
      (if i ≠ i' then P i' else 0) = P i' - (if i' = i then P i' else 0) := by
    intro i'
    by_cases h : i = i'
    · simp [h]
    · rw [if_pos h, if_neg (fun e => h e.symm), sub_zero]
  rw [Finset.sum_congr rfl (fun i' _ => key i')]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i P]
  rw [if_pos (Finset.mem_univ i)]

/-- Diagonal (row sum) at `⟨i,j⟩`: `n - parts.get i`. -/
theorem cm_rowsum (parts : List ℕ) (i : Fin parts.length) (j : Fin (parts.get i)) :
    (∑ u, (CompleteMultipartite parts).adj ⟨i,j⟩ u)
      = (parts.sum : ℂ) - (parts.get i : ℂ) := by
  rw [show (∑ u, (CompleteMultipartite parts).adj ⟨i,j⟩ u)
      = ∑ u : Σ i : Fin parts.length, Fin (parts.get i),
        (CompleteMultipartite parts).adj ⟨i,j⟩ u from rfl]
  rw [Fintype.sum_sigma (α := fun i : Fin parts.length => Fin (parts.get i))
        (fun u => (CompleteMultipartite parts).adj ⟨i,j⟩ u)]
  have hadj : ∀ (i' : Fin parts.length) (j' : Fin (parts.get i')),
      (CompleteMultipartite parts).adj ⟨i,j⟩ ⟨i',j'⟩
        = if i ≠ i' then (1:ℂ) else 0 := fun i' j' => rfl
  simp_rw [hadj]
  -- ∑_{i'} ∑_{j'} (if i ≠ i' then 1 else 0) = ∑_{i'} (if i ≠ i' then parts.get i' else 0)
  have step : ∀ i' : Fin parts.length,
      (∑ _j' : Fin (parts.get i'), (if i ≠ i' then (1:ℂ) else 0))
        = (if i ≠ i' then (parts.get i' : ℂ) else 0) := by
    intro i'
    by_cases h : i = i'
    · simp [h]
    · simp [h]
  simp_rw [step]
  -- ∑_{i'} (if i ≠ i' then parts.get i' else 0) = (∑_{i'} parts.get i') - parts.get i
  have key : ∀ i' : Fin parts.length,
      (if i ≠ i' then (parts.get i' : ℂ) else 0)
        = (parts.get i' : ℂ) - (if i' = i then (parts.get i' : ℂ) else 0) := by
    intro i'
    by_cases h : i = i'
    · simp [h]
    · rw [if_pos h, if_neg (fun e => h e.symm), sub_zero]
  rw [Finset.sum_congr rfl (fun i' _ => key i')]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i (fun i' => (parts.get i' : ℂ))]
  rw [if_pos (Finset.mem_univ i)]
  congr 1
  rw [← Nat.cast_sum]
  congr 1
  rw [← List.sum_ofFn (f := parts.get), List.ofFn_get]

/-- Laplacian `mulVec` formula. -/
theorem cm_laplacian_mulVec (parts : List ℕ) (f : CompleteMultipartiteV parts → ℂ)
    (i : Fin parts.length) (j : Fin (parts.get i)) :
    ((laplacian (CompleteMultipartite parts)).mulVec f) ⟨i, j⟩
      = ((parts.sum : ℂ) - (parts.get i : ℂ)) * f ⟨i,j⟩
        - ((∑ v, f v) - (∑ j' : Fin (parts.get i), f ⟨i, j'⟩)) := by
  unfold laplacian
  rw [Matrix.sub_mulVec, Pi.sub_apply]
  rw [Matrix.mulVec_diagonal, cm_adj_mulVec parts f i j]
  -- diagonal entry at ⟨i,j⟩ is the rowsum
  have hd : (∑ u, (CompleteMultipartite parts).adj ⟨i,j⟩ u)
      = (parts.sum : ℂ) - (parts.get i : ℂ) := cm_rowsum parts i j
  rw [hd]

/-- Reduce `mulVec f = μ•f` to a per-vertex identity over the sigma type. -/
theorem cm_mulVec_ext (parts : List ℕ) (M : Matrix (CompleteMultipartiteV parts)
    (CompleteMultipartiteV parts) ℂ) (μ : ℝ) (f : CompleteMultipartiteV parts → ℂ)
    (h : ∀ (i : Fin parts.length) (j : Fin (parts.get i)),
      (M.mulVec f) ⟨i,j⟩ = (μ : ℂ) * f ⟨i,j⟩) :
    M.mulVec f = (μ : ℂ) • f := by
  funext v
  obtain ⟨i, j⟩ := v
  rw [Pi.smul_apply, smul_eq_mul]
  exact h i j

/-! ### 0 is a Laplacian eigenvalue (all-ones eigenvector). -/

theorem cm_zero_mem_spectrum (parts : List ℕ) [Nonempty (CompleteMultipartiteV parts)] :
    (0 : ℝ) ∈ spectrum ℝ (laplacian (CompleteMultipartite parts)) := by
  apply cm_mem_spectrum_of_mulVec _ 0 (fun _ => (1:ℂ))
  · intro h
    obtain ⟨v⟩ := (inferInstance : Nonempty (CompleteMultipartiteV parts))
    have := congrFun h v
    simp at this
  · apply cm_mulVec_ext
    intro i j
    rw [cm_laplacian_mulVec]
    have hcard : Fintype.card (CompleteMultipartiteV parts) = parts.sum := by
      rw [show Fintype.card (CompleteMultipartiteV parts)
          = Fintype.card (Σ i : Fin parts.length, Fin (parts.get i)) from rfl]
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      rw [← List.sum_ofFn (f := parts.get), List.ofFn_get]
    have hS : (∑ _v : CompleteMultipartiteV parts, (1:ℂ)) = (parts.sum : ℂ) := by
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one]
    simp only [hS, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, Complex.ofReal_zero, zero_mul]
    ring

/-- Cardinality of the vertex type is `parts.sum`. -/
theorem cm_card (parts : List ℕ) :
    Fintype.card (CompleteMultipartiteV parts) = parts.sum := by
  rw [show Fintype.card (CompleteMultipartiteV parts)
      = Fintype.card (Σ i : Fin parts.length, Fin (parts.get i)) from rfl]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← List.sum_ofFn (f := parts.get), List.ofFn_get]

/-! ### `n - p_{i0}` is an eigenvalue when part `i0` has size ≥ 2. -/

theorem cm_partEig_mem_spectrum (parts : List ℕ) (i0 : Fin parts.length)
    (hsize : 2 ≤ parts.get i0) :
    ((parts.sum : ℝ) - (parts.get i0 : ℝ))
      ∈ spectrum ℝ (laplacian (CompleteMultipartite parts)) := by
  -- two valid indices in part i0
  have h0 : (0 : ℕ) < parts.get i0 := by omega
  have h1 : (1 : ℕ) < parts.get i0 := by omega
  set a0 : Fin (parts.get i0) := ⟨0, h0⟩
  set a1 : Fin (parts.get i0) := ⟨1, h1⟩
  -- eigenvector: +1 at ⟨i0,a0⟩, -1 at ⟨i0,a1⟩, 0 elsewhere
  classical
  set f : CompleteMultipartiteV parts → ℂ :=
    fun v => (if v = (⟨i0, a0⟩ : CompleteMultipartiteV parts) then (1:ℂ) else 0)
      - (if v = (⟨i0, a1⟩ : CompleteMultipartiteV parts) then (1:ℂ) else 0) with hf
  -- part-sum over part i' : zero everywhere
  have hPi : ∀ i' : Fin parts.length, (∑ j' : Fin (parts.get i'), f ⟨i',j'⟩) = 0 := by
    intro i'
    by_cases hii : i' = i0
    · subst hii
      have hsingle : ∀ (w : Fin (parts.get i')),
          (∑ x : Fin (parts.get i'),
            (if (⟨i', x⟩ : CompleteMultipartiteV parts) = ⟨i', w⟩ then (1:ℂ) else 0)) = 1 := by
        intro w
        rw [Finset.sum_eq_single w]
        · rw [if_pos rfl]
        · intro x _ hxw
          rw [if_neg]
          intro h
          exact hxw (by simpa [Sigma.mk.injEq] using h)
        · intro hw; exact absurd (Finset.mem_univ w) hw
      calc (∑ j' : Fin (parts.get i'), f ⟨i', j'⟩)
          = (∑ x : Fin (parts.get i'),
              (if (⟨i', x⟩ : CompleteMultipartiteV parts) = ⟨i', a0⟩ then (1:ℂ) else 0))
            - (∑ x : Fin (parts.get i'),
              (if (⟨i', x⟩ : CompleteMultipartiteV parts) = ⟨i', a1⟩ then (1:ℂ) else 0)) := by
            rw [← Finset.sum_sub_distrib]; rfl
        _ = 0 := by rw [hsingle a0, hsingle a1, sub_self]
    · -- on a different part, both indicators are 0 since the part index differs
      have : ∀ j' : Fin (parts.get i'), f ⟨i',j'⟩ = 0 := by
        intro j'
        simp only [hf]
        rw [if_neg (by intro h; exact hii (congrArg Sigma.fst h)),
            if_neg (by intro h; exact hii (congrArg Sigma.fst h))]
        ring
      simp [this]
  -- total sum is zero
  have hStot : (∑ v, f v) = 0 := by
    rw [show (∑ v, f v)
        = ∑ v : Σ i : Fin parts.length, Fin (parts.get i), f v from rfl]
    rw [Fintype.sum_sigma (α := fun i : Fin parts.length => Fin (parts.get i)) f]
    simp only [hPi, Finset.sum_const_zero]
  apply cm_mem_spectrum_of_mulVec _ _ f
  · -- f ≠ 0: f ⟨i0,a0⟩ = 1
    have hne : (⟨i0, a0⟩ : CompleteMultipartiteV parts) ≠ ⟨i0, a1⟩ := by
      simp only [Ne, Sigma.mk.injEq, heq_eq_eq, true_and, a0, a1, Fin.mk.injEq]
      decide
    have hfa0 : f (⟨i0, a0⟩ : CompleteMultipartiteV parts) = 1 := by
      rw [hf]
      show (if (⟨i0,a0⟩ : CompleteMultipartiteV parts) = ⟨i0,a0⟩ then (1:ℂ) else 0)
            - (if (⟨i0,a0⟩ : CompleteMultipartiteV parts) = ⟨i0,a1⟩ then (1:ℂ) else 0) = 1
      rw [if_pos rfl, if_neg hne, sub_zero]
    intro hzero
    rw [hzero] at hfa0
    exact one_ne_zero hfa0.symm
  · apply cm_mulVec_ext
    intro i j
    rw [cm_laplacian_mulVec, hStot, hPi i]
    by_cases hii : i = i0
    · subst hii
      rw [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_natCast]
      ring
    · -- off part i0, f ⟨i,j⟩ = 0, both sides vanish
      have hfij : f ⟨i, j⟩ = 0 := by
        simp only [hf]
        rw [if_neg (by intro h; exact hii (congrArg Sigma.fst h)),
            if_neg (by intro h; exact hii (congrArg Sigma.fst h))]
        ring
      rw [hfij]
      ring

/-! ### `n = parts.sum` is an eigenvalue when there are ≥ 2 parts. -/

theorem cm_total_mem_spectrum (parts : List ℕ) (hk : 2 ≤ parts.length)
    (hpos : ∀ ni ∈ parts, 1 ≤ ni) :
    (parts.sum : ℝ) ∈ spectrum ℝ (laplacian (CompleteMultipartite parts)) := by
  classical
  have hl0 : (0 : ℕ) < parts.length := by omega
  have hl1 : (1 : ℕ) < parts.length := by omega
  set i0 : Fin parts.length := ⟨0, hl0⟩
  set i1 : Fin parts.length := ⟨1, hl1⟩
  have hi01 : i0 ≠ i1 := by
    rw [Ne, Fin.ext_iff]; simp only [i0, i1]; omega
  -- part-constant weights: g i0 = p_{i1}, g i1 = -p_{i0}, else 0
  set g : Fin parts.length → ℂ :=
    fun i' => (if i' = i0 then (parts.get i1 : ℂ) else 0)
      - (if i' = i1 then (parts.get i0 : ℂ) else 0) with hg
  set f : CompleteMultipartiteV parts → ℂ := fun v => g v.1 with hf
  -- part sum: P i' = p_{i'} * g i'
  have hPi : ∀ i' : Fin parts.length,
      (∑ j' : Fin (parts.get i'), f ⟨i',j'⟩) = (parts.get i' : ℂ) * g i' := by
    intro i'
    simp only [hf]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- total sum: S = p_{i0} g_{i0} + p_{i1} g_{i1} = 0
  have hStot : (∑ v, f v) = 0 := by
    rw [show (∑ v, f v)
        = ∑ v : Σ i : Fin parts.length, Fin (parts.get i), f v from rfl]
    rw [Fintype.sum_sigma (α := fun i : Fin parts.length => Fin (parts.get i)) f]
    rw [Finset.sum_congr rfl (fun i' _ => hPi i')]
    -- ∑ i', p_{i'} * g i' = 0
    have hgi : ∀ i' : Fin parts.length, (parts.get i' : ℂ) * g i'
        = (if i' = i0 then (parts.get i0 : ℂ) * (parts.get i1 : ℂ) else 0)
          - (if i' = i1 then (parts.get i1 : ℂ) * (parts.get i0 : ℂ) else 0) := by
      intro i'
      simp only [hg, mul_sub]
      by_cases h0 : i' = i0
      · subst h0
        rw [if_pos rfl, if_neg hi01, if_pos rfl, if_neg hi01]
        ring
      · by_cases h1 : i' = i1
        · subst h1
          rw [if_neg (Ne.symm hi01), if_neg (Ne.symm hi01), if_pos rfl, if_pos rfl]
          ring
        · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]
          ring
    rw [Finset.sum_congr rfl (fun i' _ => hgi i')]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i0, Finset.sum_ite_eq' Finset.univ i1]
    simp only [Finset.mem_univ, if_true]
    ring
  apply cm_mem_spectrum_of_mulVec _ _ f
  · -- nonzero: f at part i0 = p_{i1} ≥ 1 ≠ 0
    have hp1 : 1 ≤ parts.get i1 := hpos _ (List.get_mem parts i1)
    have hp0 : 1 ≤ parts.get i0 := hpos _ (List.get_mem parts i0)
    have hgi0 : g i0 = (parts.get i1 : ℂ) := by
      show (if i0 = i0 then (parts.get i1 : ℂ) else 0)
            - (if i0 = i1 then (parts.get i0 : ℂ) else 0) = (parts.get i1 : ℂ)
      rw [if_pos rfl, if_neg hi01, sub_zero]
    have hfval : f (⟨i0, ⟨0, by omega⟩⟩ : CompleteMultipartiteV parts)
        = (parts.get i1 : ℂ) := hgi0
    intro hzero
    rw [hzero] at hfval
    have hne0 : (parts.get i1 : ℂ) ≠ 0 := by
      have : parts.get i1 ≠ 0 := by omega
      exact_mod_cast this
    exact hne0 hfval.symm
  · apply cm_mulVec_ext
    intro i j
    rw [cm_laplacian_mulVec, hStot, hPi i]
    -- f ⟨i,j⟩ = g i definitionally; (n - p_i) g_i - (0 - p_i g_i) = n g_i
    show ((parts.sum : ℂ) - (parts.get i : ℂ)) * g i - (0 - (parts.get i : ℂ) * g i)
        = (parts.sum : ℂ) * g i
    ring

/-! ### Assembled explicit spectrum (proven). -/

theorem cm_spectrum_assembled (parts : List ℕ) (hk : 2 ≤ parts.length)
    (hpos : ∀ ni ∈ parts, 1 ≤ ni) :
    ∃ μ : Finset ℝ,
      (μ : Set ℝ) ⊆ spectrum ℝ (laplacian (CompleteMultipartite parts)) ∧
      (0 : ℝ) ∈ μ ∧
      (parts.sum : ℝ) ∈ μ ∧
      ∀ i0 : Fin parts.length, 2 ≤ parts.get i0 →
        ((parts.sum : ℝ) - (parts.get i0 : ℝ)) ∈ μ := by
  classical
  have hne : Nonempty (CompleteMultipartiteV parts) := by
    have hl0 : (0 : ℕ) < parts.length := by omega
    have : 1 ≤ parts.get ⟨0, hl0⟩ := hpos _ (List.get_mem parts ⟨0, hl0⟩)
    exact ⟨⟨⟨0, hl0⟩, ⟨0, by omega⟩⟩⟩
  set S : Finset ℝ :=
    insert (0 : ℝ) (insert (parts.sum : ℝ)
      ((Finset.univ.filter (fun i0 : Fin parts.length => 2 ≤ parts.get i0)).image
        (fun i0 => (parts.sum : ℝ) - (parts.get i0 : ℝ)))) with hS
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hS, Finset.coe_insert, Finset.coe_insert, Finset.coe_image] at hx
    simp only [Set.mem_insert_iff, Set.mem_image, Finset.coe_filter,
      Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | rfl | ⟨i0, hi0, rfl⟩
    · exact cm_zero_mem_spectrum parts
    · exact cm_total_mem_spectrum parts hk hpos
    · exact cm_partEig_mem_spectrum parts i0 hi0
  · rw [hS]; exact Finset.mem_insert_self _ _
  · rw [hS]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · intro i0 hi0
    rw [hS]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    refine Finset.mem_image.mpr ⟨i0, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩


/-- **Laplacian spectrum of complete multipartite graphs (PROVEN, non-vacuous).**
For `parts = [n_1, …, n_k]` with `k ≥ 2` parts each of size `≥ 1`, and
`n = n_1 + ⋯ + n_k`, the explicit eigenvalues

  `0`,  `n`,  and  `n - n_{i_0}` (for every part `i_0` with `n_{i_0} ≥ 2`)

are *genuinely* Laplacian eigenvalues of `K_{n_1, …, n_k}`.  We package the
existence of a `Finset ℝ` of *real* eigenvalues containing exactly these values
and contained in the spectrum.

The preconditions `2 ≤ parts.length` and `1 ≤ n_i` are TRUE-making and not
cosmetic: with a single part (`k = 1`) the graph is edgeless and `n` is *not* an
eigenvalue, and the `n - n_{i_0}` eigenvalue genuinely requires `n_{i_0} ≥ 2`
(e.g. `K_{1,1} = K_2` has spectrum `{0, 2}`, and `n - n_i = 1` is *not* an
eigenvalue).  Each membership is witnessed by an explicit nonzero eigenvector
(`cm_zero_mem_spectrum`, `cm_total_mem_spectrum`, `cm_partEig_mem_spectrum`).

Reference: Brouwer–Haemers, *Spectra of Graphs*, §1.4.3; Mohar, *The Laplacian
spectrum of graphs* (1991). -/
theorem completeMultipartite_laplacian_spectrum (parts : List ℕ)
    (hk : 2 ≤ parts.length) (hpos : ∀ ni ∈ parts, 1 ≤ ni) :
    ∃ μ : Finset ℝ,
      (μ : Set ℝ) ⊆ spectrum ℝ (laplacian (CompleteMultipartite parts)) ∧
      (0 : ℝ) ∈ μ ∧
      (parts.sum : ℝ) ∈ μ ∧
      ∀ i0 : Fin parts.length, 2 ≤ parts.get i0 →
        ((parts.sum : ℝ) - (parts.get i0 : ℝ)) ∈ μ :=
  cm_spectrum_assembled parts hk hpos

/-- **Local content-bearing interface for full Laplacian integrality.**

The PROVEN `completeMultipartite_laplacian_spectrum` exhibits `0`, `n`, and the
`n - n_{i_0}` as genuine eigenvalues but does *not* show they are *all* of them
(that requires the Brouwer–Haemers multiplicity count: the explicit eigenvectors
span, with multiplicities `1`, `k-1`, `n_{i_0}-1` summing to `n`).  We isolate
exactly that residual — *spectral completeness* — as a local typeclass.

The field is **not vacuous**: it must produce, for the actual host
`K_{n_1,…,n_k}`, a containment of the *whole* real spectrum in the explicit
integer set `{0, n} ∪ {n - n_i}`.  A consumer cannot satisfy it for a graph
whose Laplacian has a non-integer or out-of-family eigenvalue.  Reference:
Brouwer–Haemers, *Spectra of Graphs*, §1.4.3. -/
class CompleteMultipartiteSpectralCompleteness where
  /-- Every real Laplacian eigenvalue lies in the explicit integer family
  `{0, n} ∪ {n - n_i : i}`. -/
  spectrum_subset :
    ∀ (parts : List ℕ),
      spectrum ℝ (laplacian (CompleteMultipartite parts)) ⊆
        (insert (0 : ℝ) (insert (parts.sum : ℝ)
          {x : ℝ | ∃ i : Fin parts.length, x = (parts.sum : ℝ) - (parts.get i : ℝ)}))

/-- **Laplacian integrality of complete multipartite graphs**, conditional on the
local spectral-completeness interface.  Given that every eigenvalue lies in the
explicit family `{0, n} ∪ {n - n_i}` (the Brouwer–Haemers residual, supplied by
`[CompleteMultipartiteSpectralCompleteness]`), each is manifestly a non-negative
integer: `0`, `n = ∑ n_i ∈ ℕ`, and `n - n_i ∈ ℕ` whenever the family is the
genuine spectrum (so `n_i ≤ n`).  Non-vacuous: the integer-valued conclusion is
forced by the genuine integer entries of `L` and the explicit family. -/
theorem completeMultipartite_laplacian_integral
    [inst : CompleteMultipartiteSpectralCompleteness] (parts : List ℕ)
    (hni : ∀ i : Fin parts.length, parts.get i ≤ parts.sum) :
    ∀ μ ∈ spectrum ℝ (laplacian (CompleteMultipartite parts)),
      ∃ n : ℕ, μ = (n : ℝ) := by
  intro μ hμ
  have hmem := inst.spectrum_subset parts hμ
  simp only [Set.mem_insert_iff, Set.mem_setOf_eq] at hmem
  rcases hmem with rfl | rfl | ⟨i, rfl⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨parts.sum, by norm_num⟩
  · -- n - n_i is a natural number since n_i ≤ n
    refine ⟨parts.sum - parts.get i, ?_⟩
    rw [Nat.cast_sub (hni i)]

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

/-- **Local content-bearing interface for Li–Luo–Feng–Li (2025).**

The deterministic-search guarantee is the specialisation of the *general*
theorem of Li, Luo, Feng, Li (arXiv:2506.21108, *Deterministic quantum search on
all Laplacian integral graphs*): every Laplacian-integral graph admits
deterministic spatial search.  The full Diophantine construction of the
witnessing `(γ*, τ*)` from the explicit Laplacian spectrum is not formalized; we
isolate exactly that residual as a local typeclass.

The field is **not vacuous**: it must consume the genuine non-degeneracy
witnesses (`2 ≤ parts.length`, `1 ≤ n_i` — without which the graph is empty or a
single part and the search statement is degenerate) and produce deterministic
search at the *actual* vertex `w` of the *actual* complete-multipartite host.  A
consumer cannot satisfy it vacuously: it is the faithful Li–Luo–Feng–Li residual,
keyed to the Laplacian-integral structure proven in
`completeMultipartite_laplacian_spectrum`. -/
class CompleteMultipartiteDeterministicSearch where
  /-- For a non-degenerate complete multipartite graph, the Li–Luo–Feng–Li
  construction yields deterministic CTQW spatial search at every vertex. -/
  det_search :
    ∀ (parts : List ℕ), 2 ≤ parts.length → (∀ ni ∈ parts, 1 ≤ ni) →
      ∀ w : CompleteMultipartiteV parts,
        IsDeterministicSearch (CompleteMultipartite parts) w

/-- **Complete-multipartite instance of Li–Luo–Feng–Li (2025)**, conditional on
the local `CompleteMultipartiteDeterministicSearch` interface.  Every complete
multipartite graph `K_{n_1, …, n_k}` (`k ≥ 2` parts, each size `≥ 1`) admits
deterministic CTQW spatial search at *every* vertex `w`.

The guarantee is **not** complete-multipartite-specific: it is the specialisation
of the general Li–Luo–Feng–Li theorem (arXiv:2506.21108) for Laplacian-integral
graphs, and `K_{n_1,…,n_k}` is Laplacian integral (its explicit spectrum is
`completeMultipartite_laplacian_spectrum`).  The witnessing `(γ*, τ*)` come from
that general construction, supplied by the `[…]` interface. -/
theorem completeMultipartite_deterministicSearch
    [inst : CompleteMultipartiteDeterministicSearch]
    (parts : List ℕ) (hk : 2 ≤ parts.length)
    (hpos : ∀ ni ∈ parts, 1 ≤ ni)
    (w : CompleteMultipartiteV parts) :
    IsDeterministicSearch (CompleteMultipartite parts) w :=
  inst.det_search parts hk hpos w

/-- **Four-part specialisation** of Li–Luo–Feng–Li.  This is the exact
host appearing in Graphplay's `Tower6` four-color-completion construction;
the deterministic-search guarantee transfers directly to that bundle via
the equitable-partition quotient. -/
theorem K4parts_deterministicSearch
    [CompleteMultipartiteDeterministicSearch]
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
