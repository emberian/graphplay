/-
# Graphplay.PST.UniversalRatio

**The spectral ratio condition forced by K-fractional revival.**

This module closes the necessity half of the Chan–Coutinho–Tamon–Vinet–Zhan
revival/ratio circle for the subset framework of `Graphplay.PST.Universal`.  It
sits downstream of both `Graphplay.PST.Universal` (the `D_K` framework:
`IsKFractionalRevival`, `IsKRatioCondition`) and `Graphplay.PST.Periodicity`
(whose `2π`-periodicity extraction this generalizes), so it can use both freely.

**The honest statement.**  The naive necessity claim — "K-fractional revival at
some `τ > 0` forces the joint eigenvalue support `S_K` into a *single*
arithmetic progression (`IsKRatioCondition`)" — is **false** for `|K| ≥ 2`:
`Graphplay.PST.isKFractionalRevival_univ` exhibits revival on `K = univ` at
*every* time for *every* graph, while a generic spectrum (e.g. `{0, 1, √2}`
extended to the supports of a weighted graph, or `{±1, ±√2}` for a disjoint
union of two weighted edges) lies in no arithmetic progression.  What revival at
`τ` genuinely forces is a **residue-class structure**:

> the supported eigenvalues fall into **at most `|K|` classes** modulo
> `(2π/τ)·ℤ`  (`IsKRatioClassCondition`, proven below in
> `isKRatioClassCondition_of_fractionalRevival`).

For `|K| = 1` one class *is* a single progression, and the statement
specializes to Godsil's periodicity necessity: revival on `{u}` is periodicity
at `u`, and the support of `u` lands in one progression of gap `2π/τ`
(`isKRatioCondition_of_fractionalRevival_singleton` — the originally documented
`IsKRatioCondition` conclusion, true in exactly this case).

**Proof architecture (all axiom-clean, no Diophantine approximation).**
1. Revival iterates: `K`-invariance of `U(τ)` composes to `U(nτ)` for every
   `n : ℕ` (`isKFractionalRevival_nat_mul`).
2. Group the spectral decomposition by the *phase value* `c = e^{-iτλ}`: the
   class projectors `F_c = Σ_{e^{-iτλᵢ} = c} uᵢuᵢᴴ` (`phaseProj`) satisfy
   `U(nτ) = Σ_c cⁿ F_c`.  The iterated leak conditions are then a Vandermonde
   system in the distinct values `c`; an exact finite annihilation argument
   (`vanish_of_powerSums`, no determinants) kills every class leak:
   `(F_c)_{j,k} = 0` for `j ∉ K`, `k ∈ K` (`phaseProj_leak_eq_zero`).
3. The class projectors are Hermitian, mutually annihilating idempotent blocks
   (`phaseProj_mul`); for each *supported* class the witness column `F_c e_k`
   is a nonzero vector supported inside `K`, and distinct classes give
   orthogonal columns.  Linear independence inside `ℂ^K` bounds the number of
   supported classes by `|K|` (`card_supportedClasses_le`).
4. Within one class, phase equality extracts `λ - λ' ∈ (2π/τ)·ℤ` exactly as in
   the periodicity forward direction (`Complex.exp_eq_exp_iff_exists_int`).

References:
* A. Chan, G. Coutinho, C. Tamon, L. Vinet, H. Zhan, *Quantum fractional
  revival on graphs*, arXiv:2004.01129, §4 (the spectral conditions for
  fractional revival).
* C. Godsil, *Periodic graphs*, arXiv:1009.5375 (the `|K| = 1` specialization).
-/

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Graphplay.PST.Universal
import Graphplay.PST.Periodicity

open scoped Matrix Classical
open NormedSpace

universe u

namespace Graphplay
namespace PST

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## §1 Iterated revival -/

/-- **Revival iterates.**  If the `K`-supported subspace is invariant under
`U(τ)` then it is invariant under every power `U(nτ) = U(τ)ⁿ`: the leak
amplitudes at time `n·τ` vanish for all `n : ℕ` (at `n = 0` the evolution is
the identity, whose off-diagonal entries vanish). -/
theorem isKFractionalRevival_nat_mul (G : WeightedGraph V) (K : Finset V) (τ : ℝ)
    (hrev : IsKFractionalRevival G K τ) (n : ℕ) :
    IsKFractionalRevival G K ((n : ℝ) * τ) := by
  induction n with
  | zero =>
      intro k hk j hj
      have hjk : j ≠ k := fun hh => hj (hh ▸ hk)
      rw [show ((0 : ℕ) : ℝ) * τ = 0 from by push_cast; ring, G.evolve_zero,
        Matrix.one_apply_ne hjk]
  | succ n ih =>
      intro k hk j hj
      rw [show ((n + 1 : ℕ) : ℝ) * τ = (n : ℝ) * τ + τ from by push_cast; ring,
        G.evolve_add, Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases hx : x ∈ K
      · rw [ih x hx j hj, zero_mul]
      · rw [hrev k hk x hx, mul_zero]

/-! ## §2 Phase-class projectors -/

/-- The **phase** of eigenindex `i` at time `τ`: `e^{-iτλᵢ}`.  Two eigenindices
are in the same *class* iff their phases coincide, i.e. iff
`τ(λᵢ - λⱼ) ∈ 2πℤ`. -/
noncomputable def phaseAt (G : WeightedGraph V) (τ : ℝ) (i : V) : ℂ :=
  Complex.exp (-(Complex.I * (τ : ℂ)) * ((G.herm.eigenvalues i : ℝ) : ℂ))

/-- The **phase-class projector** `F_c`: the spectral projector onto the span of
all eigenvectors whose phase at time `τ` equals `c`, written through the
eigenvector unitary as `U · diag(𝟙[phase = c]) · Uᴴ`.  The evolution at every
multiple of `τ` is a linear combination of these finitely many projectors. -/
noncomputable def phaseProj (G : WeightedGraph V) (τ : ℝ) (c : ℂ) :
    Matrix V V ℂ :=
  eigU G * Matrix.diagonal (fun i => if phaseAt G τ i = c then (1 : ℂ) else 0)
    * (eigU G)ᴴ

/-- Entrywise form of the class projector:
`(F_c)_{x,y} = Σ_{i : phase i = c} (eigU)_{x,i} · conj (eigU)_{y,i}`. -/
theorem phaseProj_apply (G : WeightedGraph V) (τ : ℝ) (c : ℂ) (x y : V) :
    phaseProj G τ c x y
      = ∑ i : V, (if phaseAt G τ i = c then (1 : ℂ) else 0)
          * (eigU G x i * star (eigU G y i)) := by
  unfold phaseProj
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply]
    ring
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ hk, mul_zero]
  · intro hh
    exact absurd (Finset.mem_univ i) hh

/-- The class projector is Hermitian. -/
theorem phaseProj_conjTranspose (G : WeightedGraph V) (τ : ℝ) (c : ℂ) :
    (phaseProj G τ c)ᴴ = phaseProj G τ c := by
  unfold phaseProj
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose]
  rw [show star (fun i => if phaseAt G τ i = c then (1 : ℂ) else 0)
      = fun i => if phaseAt G τ i = c then (1 : ℂ) else 0 from funext fun i => by
    by_cases hh : phaseAt G τ i = c <;> simp [hh]]
  rw [Matrix.mul_assoc]

/-- Distinct classes annihilate; one class is idempotent:
`F_c · F_d = [c = d] · F_c`. -/
theorem phaseProj_mul (G : WeightedGraph V) (τ : ℝ) (c d : ℂ) :
    phaseProj G τ c * phaseProj G τ d
      = if c = d then phaseProj G τ c else 0 := by
  have hUU : ∀ X : Matrix V V ℂ, (eigU G)ᴴ * (eigU G * X) = X := fun X => by
    rw [← Matrix.mul_assoc, conjTranspose_mul_eigU, Matrix.one_mul]
  have key : ∀ d₁ d₂ : V → ℂ,
      (eigU G * Matrix.diagonal d₁ * (eigU G)ᴴ)
        * (eigU G * Matrix.diagonal d₂ * (eigU G)ᴴ)
      = eigU G * Matrix.diagonal (fun i => d₁ i * d₂ i) * (eigU G)ᴴ := by
    intro d₁ d₂
    rw [← Matrix.diagonal_mul_diagonal d₁ d₂]
    simp only [Matrix.mul_assoc]
    rw [hUU (Matrix.diagonal d₂ * (eigU G)ᴴ)]
  by_cases hcd : c = d
  · subst hcd
    rw [if_pos rfl]
    unfold phaseProj
    rw [key]
    have hsq : (fun i => (if phaseAt G τ i = c then (1 : ℂ) else 0)
          * (if phaseAt G τ i = c then (1 : ℂ) else 0))
        = fun i => if phaseAt G τ i = c then (1 : ℂ) else 0 :=
      funext fun i => by by_cases hh : phaseAt G τ i = c <;> simp [hh]
    rw [hsq]
  · rw [if_neg hcd]
    unfold phaseProj
    rw [key]
    have hzero : (fun i => (if phaseAt G τ i = c then (1 : ℂ) else 0)
          * (if phaseAt G τ i = d then (1 : ℂ) else 0))
        = fun _ => (0 : ℂ) :=
      funext fun i => by
        by_cases hh : phaseAt G τ i = c
        · simp [hh, hcd]
        · simp [hh]
    rw [hzero, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]

/-- **Power expansion of the iterated walk over phase classes.**  For every
`n : ℕ`, summing `cⁿ · F_c` over the (finitely many) phase values reconstructs
the evolution at time `n·τ`, entrywise:
`U(nτ)_{x,y} = Σ_{c} cⁿ (F_c)_{x,y}`. -/
theorem sum_phasePow_phaseProj_apply (G : WeightedGraph V) (τ : ℝ) (n : ℕ)
    (x y : V) :
    ∑ c ∈ Finset.univ.image (phaseAt G τ), c ^ n * phaseProj G τ c x y
      = G.evolve ((n : ℝ) * τ) x y := by
  rw [evolve_eq_eigU_sum]
  rw [Finset.sum_congr rfl
    (fun c _ => by rw [phaseProj_apply, Finset.mul_sum])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hcollapse : ∑ c ∈ Finset.univ.image (phaseAt G τ),
      c ^ n * ((if phaseAt G τ i = c then (1 : ℂ) else 0)
        * (eigU G x i * star (eigU G y i)))
      = (phaseAt G τ i) ^ n * (eigU G x i * star (eigU G y i)) := by
    rw [Finset.sum_eq_single (phaseAt G τ i)]
    · rw [if_pos rfl, one_mul]
    · intro c _ hne
      rw [if_neg (fun hh => hne hh.symm), zero_mul, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ i)) hnot
  rw [hcollapse]
  unfold phaseAt
  rw [← Complex.exp_nat_mul]
  rw [show (n : ℂ) * (-(Complex.I * (τ : ℂ)) * ((G.herm.eigenvalues i : ℝ) : ℂ))
      = -(Complex.I * (((n : ℝ) * τ : ℝ) : ℂ)) * ((G.herm.eigenvalues i : ℝ) : ℂ)
    from by push_cast; ring]
  ring

/-! ## §3 The annihilation argument (exact finite Vandermonde) -/

/-- **Exact annihilation from vanishing power sums.**  If a finitely supported
family `f` over distinct complex nodes `C` satisfies `Σ_c cⁿ f(c) = 0` for every
`n : ℕ`, then `f` vanishes on `C`.  Proven without determinants: multiplying the
power identities by the coefficients of `∏_{t ∈ C, t ≠ c₀}(X - t)` isolates
`f(c₀)` with the nonzero factor `∏ (c₀ - t)`. -/
theorem vanish_of_powerSums {C : Finset ℂ} {f : ℂ → ℂ}
    (h : ∀ n : ℕ, ∑ c ∈ C, c ^ n * f c = 0) : ∀ c₀ ∈ C, f c₀ = 0 := by
  have aux : ∀ (T : Finset ℂ) (n : ℕ),
      ∑ c ∈ C, (∏ t ∈ T, (c - t)) * c ^ n * f c = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro n; simpa using h n
    | @insert t T htT ih =>
        intro n
        have hexpand : ∀ c : ℂ, (∏ x ∈ insert t T, (c - x)) * c ^ n * f c
            = (∏ x ∈ T, (c - x)) * c ^ (n + 1) * f c
              - t * ((∏ x ∈ T, (c - x)) * c ^ n * f c) := by
          intro c
          rw [Finset.prod_insert htT, pow_succ]
          ring
        rw [Finset.sum_congr rfl (fun c _ => hexpand c), Finset.sum_sub_distrib,
          ih (n + 1), ← Finset.mul_sum, ih n, mul_zero, sub_zero]
  intro c₀ hc₀
  have h0 := aux (C.erase c₀) 0
  rw [Finset.sum_eq_single c₀] at h0
  · have hprod : (∏ t ∈ C.erase c₀, (c₀ - t)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr
        (fun t ht => sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase ht)))
    have h1 : (∏ t ∈ C.erase c₀, (c₀ - t)) * f c₀ = 0 := by simpa using h0
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hprod
    · exact h2
  · intro c hc hne
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hc⟩) (sub_self c),
      zero_mul, zero_mul]
  · intro hc
    exact absurd hc₀ hc

/-- **Revival kills every class leak.**  Under `K`-fractional revival at `τ`,
each individual class projector already satisfies the leak condition:
`(F_c)_{j,k} = 0` for every source `k ∈ K` and destination `j ∉ K`.  The
iterated leak identities `Σ_c cⁿ (F_c)_{j,k} = U(nτ)_{j,k} = 0` form an exact
Vandermonde system over the distinct phase values, annihilated by
`vanish_of_powerSums`. -/
theorem phaseProj_leak_eq_zero (G : WeightedGraph V) (K : Finset V) {τ : ℝ}
    (hrev : IsKFractionalRevival G K τ) {k j : V} (hk : k ∈ K) (hj : j ∉ K)
    (c : ℂ) :
    phaseProj G τ c j k = 0 := by
  by_cases hc : c ∈ Finset.univ.image (phaseAt G τ)
  · refine vanish_of_powerSums (C := Finset.univ.image (phaseAt G τ))
      (f := fun c => phaseProj G τ c j k) (fun n => ?_) c hc
    rw [sum_phasePow_phaseProj_apply]
    exact isKFractionalRevival_nat_mul G K τ hrev n k hk j hj
  · rw [phaseProj_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg (fun hh => hc (by
        rw [← hh]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i))),
      zero_mul]

/-! ## §4 Counting the supported classes -/

/-- The diagonal of a class projector is a (real, nonnegative) sum of squared
eigenvector amplitudes over the class. -/
theorem phaseProj_diag_eq (G : WeightedGraph V) (τ : ℝ) (c : ℂ) (k : V) :
    phaseProj G τ c k k
      = ((∑ i : V, if phaseAt G τ i = c then ‖eigU G k i‖ ^ 2 else 0 : ℝ) : ℂ) := by
  rw [phaseProj_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hh : phaseAt G τ i = c
  · rw [if_pos hh, if_pos hh, one_mul, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  · rw [if_neg hh, if_neg hh, zero_mul, Complex.ofReal_zero]

/-- A class supported at `k` (some eigenindex `i` of that phase has
`(eigU)_{k,i} ≠ 0`) has strictly positive diagonal there: `(F_c)_{k,k} ≠ 0`. -/
theorem phaseProj_diag_ne_zero (G : WeightedGraph V) (τ : ℝ) {k i : V}
    (hne : eigU G k i ≠ 0) :
    phaseProj G τ (phaseAt G τ i) k k ≠ 0 := by
  rw [phaseProj_diag_eq, Complex.ofReal_ne_zero]
  have hpos : 0 < ∑ j : V,
      if phaseAt G τ j = phaseAt G τ i then ‖eigU G k j‖ ^ 2 else 0 := by
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · by_cases hh : phaseAt G τ j = phaseAt G τ i
      · rw [if_pos hh]; positivity
      · rw [if_neg hh]
    · rw [if_pos rfl]
      exact pow_pos (norm_pos_iff.mpr hne) 2
  exact ne_of_gt hpos

/-- **Column orthogonality across classes.**  The Hermitian, mutually
annihilating structure of the class projectors gives, for any witness columns:
`Σ_x conj((F_c)_{x,y}) (F_d)_{x,z} = [c = d] · (F_c)_{y,z}`. -/
theorem phaseProj_col_inner (G : WeightedGraph V) (τ : ℝ) (c d : ℂ) (y z : V) :
    ∑ x : V, star (phaseProj G τ c x y) * phaseProj G τ d x z
      = if c = d then phaseProj G τ c y z else 0 := by
  have h1 : ∑ x : V, star (phaseProj G τ c x y) * phaseProj G τ d x z
      = ((phaseProj G τ c)ᴴ * phaseProj G τ d) y z := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun x _ => by rw [Matrix.conjTranspose_apply])
  rw [h1, phaseProj_conjTranspose, phaseProj_mul,
    apply_ite (fun M : Matrix V V ℂ => M y z)]
  by_cases hcd : c = d
  · rw [if_pos hcd, if_pos hcd]
  · rw [if_neg hcd, if_neg hcd, Matrix.zero_apply]

/-- **At most `|K|` supported phase classes.**  Under `K`-fractional revival at
`τ`, the phases `e^{-iτλ}` of the eigenindices supported on `K` take at most
`|K|` distinct values: each supported class contributes a nonzero witness
column `F_c e_k` confined to `K` (by `phaseProj_leak_eq_zero`), and distinct
classes give orthogonal columns — a linearly independent family inside `ℂ^K`.

This is the genuine spectral content of revival (for `|K| = 1` it says all
supported phases coincide, i.e. periodicity's phase collapse). -/
theorem card_supportedClasses_le (G : WeightedGraph V) (K : Finset V) {τ : ℝ}
    (hrev : IsKFractionalRevival G K τ) :
    ((Finset.univ.filter (fun i : V => ∃ k ∈ K, eigU G k i ≠ 0)).image
        (phaseAt G τ)).card
      ≤ K.card := by
  set SC := (Finset.univ.filter (fun i : V => ∃ k ∈ K, eigU G k i ≠ 0)).image
    (phaseAt G τ) with hSC
  -- Witness data for each supported class: an eigenindex of that phase and a
  -- vertex of `K` supporting it.
  have hwit : ∀ c : {c // c ∈ SC}, ∃ ik : V × V,
      phaseAt G τ ik.1 = c.1 ∧ ik.2 ∈ K ∧ eigU G ik.2 ik.1 ≠ 0 := by
    rintro ⟨c, hc⟩
    rw [hSC] at hc
    obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp hc
    obtain ⟨k, hk, hne⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨(i, k), hpi, hk, hne⟩
  choose wit hwitp hwitK hwitne using hwit
  -- The witness columns, restricted to `K`.
  set vec : {c // c ∈ SC} → (↥K → ℂ) :=
    fun c => fun k => phaseProj G τ c.1 (k : V) ((wit c).2) with hvec
  have hli : LinearIndependent ℂ vec := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c₀
    have hD : phaseProj G τ c₀.1 ((wit c₀).2) ((wit c₀).2) ≠ 0 := by
      have hd := phaseProj_diag_ne_zero G τ (hwitne c₀)
      rwa [hwitp c₀] at hd
    have hS : ∑ k : ↥K, star (vec c₀ k) * (∑ c, g c • vec c) k = 0 := by
      rw [hg]
      simp
    have hexpand : ∀ k : ↥K, star (vec c₀ k) * (∑ c, g c • vec c) k
        = ∑ c, g c * (star (vec c₀ k) * vec c k) := by
      intro k
      rw [Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hexpand k), Finset.sum_comm] at hS
    have hcollapse : ∀ c : {c // c ∈ SC},
        ∑ k : ↥K, g c * (star (vec c₀ k) * vec c k)
          = g c * (if c₀.1 = c.1
              then phaseProj G τ c₀.1 ((wit c₀).2) ((wit c).2) else 0) := by
      intro c
      rw [← Finset.mul_sum]
      congr 1
      have hres : ∑ k : ↥K, star (vec c₀ k) * vec c k
          = ∑ x : V, star (phaseProj G τ c₀.1 x ((wit c₀).2))
              * phaseProj G τ c.1 x ((wit c).2) := by
        simp only [hvec]
        rw [Finset.sum_coe_sort K (fun x : V =>
          star (phaseProj G τ c₀.1 x ((wit c₀).2))
            * phaseProj G τ c.1 x ((wit c).2))]
        exact Finset.sum_subset (Finset.subset_univ K) (fun x _ hx => by
          rw [phaseProj_leak_eq_zero G K hrev (hwitK c) hx, mul_zero])
      rw [hres, phaseProj_col_inner]
    rw [Finset.sum_congr rfl (fun c _ => hcollapse c)] at hS
    have hsingle : ∑ c : {c // c ∈ SC}, g c * (if c₀.1 = c.1
        then phaseProj G τ c₀.1 ((wit c₀).2) ((wit c).2) else 0)
        = g c₀ * phaseProj G τ c₀.1 ((wit c₀).2) ((wit c₀).2) := by
      rw [Finset.sum_eq_single c₀]
      · rw [if_pos rfl]
      · intro c _ hne
        rw [if_neg (fun hh => hne (Subtype.ext hh.symm)), mul_zero]
      · intro hc
        exact absurd (Finset.mem_univ c₀) hc
    rw [hsingle] at hS
    rcases mul_eq_zero.mp hS with h1 | h1
    · exact h1
    · exact absurd h1 hD
  have hcardle := hli.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe]
    at hcardle

/-! ## §5 The ratio-class condition -/

/-- **Phase equality extracts the integer.**  Two eigenindices with the same
phase at time `τ ≠ 0` have eigenvalues differing by an integer multiple of the
quantum `2π/τ` (the periodicity-style `2π`-extraction via
`Complex.exp_eq_exp_iff_exists_int`). -/
theorem eigenvalue_eq_add_int_of_phaseAt_eq (G : WeightedGraph V) {τ : ℝ}
    (hτ : τ ≠ 0) {a b : V} (h : phaseAt G τ a = phaseAt G τ b) :
    ∃ m : ℤ, G.herm.eigenvalues a
      = G.herm.eigenvalues b + (2 * Real.pi / τ) * (m : ℝ) := by
  unfold phaseAt at h
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨-n, ?_⟩
  have himeq : (-(Complex.I * (τ : ℂ)) * ((G.herm.eigenvalues a : ℝ) : ℂ)).im
      = (-(Complex.I * (τ : ℂ)) * ((G.herm.eigenvalues b : ℝ) : ℂ)
          + n * (2 * Real.pi * Complex.I)).im := by rw [hn]
  simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re]
    at himeq
  -- `τ·λ_a = τ·λ_b - 2π·n`; divide by `τ ≠ 0`.
  have hkey : G.herm.eigenvalues a - G.herm.eigenvalues b
      = (2 * Real.pi / τ) * ((-n : ℤ) : ℝ) := by
    rw [div_mul_eq_mul_div, eq_div_iff hτ]
    push_cast
    nlinarith [himeq]
  linarith [hkey]

/-- **The `K`-ratio condition in residue-class form** (the honest necessary
spectral condition for `K`-fractional revival at time `τ`).  The joint
eigenvalue support of `K` is covered by at most `|K|` arithmetic progressions
with the common gap `2π/τ`: there is a base set `B` of at most `|K|` reals such
that every supported eigenvalue is `b + (2π/τ)·m` for some `b ∈ B`, `m ∈ ℤ`.

For `|K| = 1` this is the single-progression `IsKRatioCondition` (gap `2π/τ`),
i.e. Godsil's periodicity ratio condition.  For `|K| ≥ 2` the multi-class form
is sharp: the single-progression strengthening is false (see the module
docstring). -/
def IsKRatioClassCondition (G : WeightedGraph V) (K : Finset V) (τ : ℝ) : Prop :=
  ∃ B : Finset ℝ, B.card ≤ K.card ∧
    ∀ lam : ℝ, (∃ k ∈ K, lam ∈ EigenvalueSupport G k) →
      ∃ b ∈ B, ∃ m : ℤ, lam = b + (2 * Real.pi / τ) * (m : ℝ)

/-- **Necessity of the ratio-class condition** (Chan–Coutinho–Tamon–Vinet–Zhan,
arXiv:2004.01129, necessity direction, residue-class form; fully proven,
axiom-clean).  `K`-fractional revival at time `τ ≠ 0` forces the joint
eigenvalue support of `K` into at most `|K|` residue classes modulo
`(2π/τ)·ℤ`. -/
theorem isKRatioClassCondition_of_fractionalRevival (G : WeightedGraph V)
    (K : Finset V) {τ : ℝ} (hτ : τ ≠ 0)
    (hrev : IsKFractionalRevival G K τ) :
    IsKRatioClassCondition G K τ := by
  set SC := (Finset.univ.filter (fun i : V => ∃ k ∈ K, eigU G k i ≠ 0)).image
    (phaseAt G τ) with hSC
  -- one representative eigenindex per supported class
  have hrep : ∀ c : {c // c ∈ SC}, ∃ i : V, phaseAt G τ i = c.1 := by
    rintro ⟨c, hc⟩
    rw [hSC] at hc
    obtain ⟨i, _, hpi⟩ := Finset.mem_image.mp hc
    exact ⟨i, hpi⟩
  choose rep hrepp using hrep
  refine ⟨Finset.univ.image (fun c : {c // c ∈ SC} => G.herm.eigenvalues (rep c)),
    ?_, ?_⟩
  · calc (Finset.univ.image
          (fun c : {c // c ∈ SC} => G.herm.eigenvalues (rep c))).card
        ≤ (Finset.univ : Finset {c // c ∈ SC}).card := Finset.card_image_le
      _ = SC.card := by rw [Finset.card_univ, Fintype.card_coe]
      _ ≤ K.card := card_supportedClasses_le G K hrev
  · rintro lam ⟨k, hkK, i, hil, hine⟩
    have hiF : i ∈ Finset.univ.filter (fun i : V => ∃ k ∈ K, eigU G k i ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, k, hkK, hine⟩
    have hcSC : phaseAt G τ i ∈ SC := by
      rw [hSC]
      exact Finset.mem_image_of_mem _ hiF
    refine ⟨G.herm.eigenvalues (rep ⟨phaseAt G τ i, hcSC⟩),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    -- same class ⇒ eigenvalue difference in `(2π/τ)·ℤ`
    have hphase : phaseAt G τ (rep ⟨phaseAt G τ i, hcSC⟩) = phaseAt G τ i :=
      hrepp ⟨phaseAt G τ i, hcSC⟩
    obtain ⟨m, hm⟩ := eigenvalue_eq_add_int_of_phaseAt_eq G hτ hphase.symm
    exact ⟨m, by rw [← hil]; exact hm⟩

/-- **The `|K| = 1` case: periodicity forces the (single-progression) ratio
condition** — exactly the originally documented `IsKRatioCondition` conclusion,
which is true precisely in this case.  Fractional revival on a singleton `{u}`
at `τ > 0` is periodicity at `u` (the off-`u` column dies), and a single class
of gap `2π/τ` is a single arithmetic progression covering the support of `u`.

Reference: Godsil, *Periodic graphs* (arXiv:1009.5375), Thm 6.1 (necessity);
CCTVZ arXiv:2004.01129 (`|K| = 1` revival = periodicity). -/
theorem isKRatioCondition_of_fractionalRevival_singleton (G : WeightedGraph V)
    (u : V) (h : ∃ τ : ℝ, 0 < τ ∧ IsKFractionalRevival G {u} τ) :
    IsKRatioCondition G {u} := by
  obtain ⟨τ, hτpos, hrev⟩ := h
  obtain ⟨B, hBcard, hB⟩ :=
    isKRatioClassCondition_of_fractionalRevival G {u} (ne_of_gt hτpos) hrev
  rw [Finset.card_singleton] at hBcard
  by_cases hBne : B.Nonempty
  · obtain ⟨b₀, hb₀⟩ := hBne
    refine ⟨2 * Real.pi / τ, b₀, by positivity, ?_⟩
    intro lam hlam
    obtain ⟨b, hb, mm, hmm⟩ := hB lam hlam
    have hbb : b = b₀ := Finset.card_le_one.mp hBcard b hb b₀ hb₀
    exact ⟨mm, by rw [← hbb]; exact hmm⟩
  · refine ⟨1, 0, one_pos, ?_⟩
    intro lam hlam
    obtain ⟨b, hb, -⟩ := hB lam hlam
    rw [Finset.not_nonempty_iff_eq_empty.mp hBne] at hb
    exact absurd hb (Finset.notMem_empty b)

end PST
end Graphplay
