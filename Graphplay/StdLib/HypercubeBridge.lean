/-
# Graphplay.StdLib.HypercubeBridge

Shared infrastructure for transporting hypercube results between the
**coordinate models** on `Fin (2^n)` (bitwise XOR adjacency, as in
`Graphplay.PST.GodsilRatio`, and Hamming-distance adjacency, as in
`Graphplay.StdLib.Hypercube`) and the **iterated-Cartesian model**
`HypercubeProduct.hypercubeP n`, where the dynamical theorems are proven
unconditionally.

Three independent toolkits live here (everything upstream of
`Graphplay.StdLib.Hypercube`, so both that module and
`Graphplay.PST.GodsilRatio` can import it):

1. **Single-set-bit arithmetic.**  The classic bit trick
   `x &&& (x - 1) = 0 ∧ x ≠ 0 ↔ x` is a power of two
   (`and_pred_eq_zero_iff_two_pow`), proven by strong induction on the binary
   representation.  This is what recognizes the bitwise XOR adjacency
   `(u ^^^ v) ≠ 0 ∧ (u ^^^ v) &&& (u ^^^ v - 1) = 0` as Hamming distance `1`.

2. **Diagonal of the product-cube propagator.**  `U(t)_{ww} = (cos t)^n` on
   `hypercubeP n` (`hypercubeP_evolve_diag`), from the single-edge diagonal
   `K₂.evolve t b b = cos t` (`K2_evolve_diag`, by the Hadamard
   diagonalization of the Pauli-`X` adjacency) and the Kronecker factorization
   `evolve_cartesianProduct_apply`.

3. **Cesàro mean of a periodic function.**  For `g` continuous and
   `T`-periodic with `T > 0`,
   `T⁻¹ ∫₀ᵀ g → (∫₀^T g)/T` as the horizon grows
   (`tendsto_intervalAverage_of_periodic`), by squeezing between the
   floor-counted whole-period bounds of
   `Function.Periodic.sInf_add_zsmul_le_integral_of_pos`; plus the Wallis
   value `∫₀^π cos²ⁿ = π · C(2n,n)/4ⁿ` (`integral_cos_pow_even_pi`), the
   central-binomial average-return engine for the hypercube.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Bitwise
import Graphplay.StdLib.HypercubeProduct

open scoped Matrix
open NormedSpace

namespace Graphplay
namespace StdLib
namespace HypercubeBridge

/-! ## 1. Single-set-bit arithmetic -/

/-- A power of two and its predecessor share no set bits: `2^i &&& (2^i - 1) = 0`. -/
theorem two_pow_and_pred (i : ℕ) : 2 ^ i &&& (2 ^ i - 1) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
  rcases eq_or_ne i j with h | h <;> simp [h]

/-- **The `x &&& (x-1)` power-of-two trick.**  A positive natural number has
`x &&& (x - 1) = 0` iff it is a power of two (equivalently: has exactly one set
bit).  Strong induction on the binary representation: the odd case forces
`x = 1`, and the even case `x = 2y` reduces to `y` via
`(2y) &&& (2y - 1) = 2·(y &&& (y - 1))`. -/
theorem and_pred_eq_zero_iff_two_pow :
    ∀ x : ℕ, 0 < x → (x &&& (x - 1) = 0 ↔ ∃ i, x = 2 ^ i) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rcases Nat.even_or_odd x with ⟨y, hyy⟩ | ⟨y, hyy⟩
    · -- even case: `x = 2y` with `y > 0`
      have hx2 : x = 2 * y := by omega
      have hypos : 0 < y := by omega
      have key : x &&& (x - 1) = 2 * (y &&& (y - 1)) := by
        apply Nat.eq_of_testBit_eq
        intro j
        cases j with
        | zero =>
          rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
          have h1 : x % 2 = 0 := by omega
          have h2 : 2 * (y &&& (y - 1)) % 2 = 0 := by omega
          simp [h1, h2]
        | succ j =>
          rw [Nat.testBit_and, Nat.testBit_add_one, Nat.testBit_add_one, Nat.testBit_add_one]
          have hd1 : x / 2 = y := by omega
          have hd2 : (x - 1) / 2 = y - 1 := by omega
          have hd3 : 2 * (y &&& (y - 1)) / 2 = y &&& (y - 1) := by omega
          rw [hd1, hd2, hd3, Nat.testBit_and]
      constructor
      · intro h0
        have hy0 : y &&& (y - 1) = 0 := by omega
        obtain ⟨i, hi⟩ := (ih y (by omega) hypos).mp hy0
        exact ⟨i + 1, by rw [hx2, hi, pow_succ]; ring⟩
      · rintro ⟨i, hi⟩
        cases i with
        | zero => norm_num at hi; omega
        | succ i =>
          have hp : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
          have hyi : y = 2 ^ i := by omega
          have hz : y &&& (y - 1) = 0 := (ih y (by omega) hypos).mpr ⟨i, hyi⟩
          omega
    · -- odd case: `x = 2y + 1`, forced to be `1`
      have hx2 : x = 2 * y + 1 := hyy
      have key : x &&& (x - 1) = 2 * y := by
        apply Nat.eq_of_testBit_eq
        intro j
        cases j with
        | zero =>
          rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
          have h1 : (x - 1) % 2 = 0 := by omega
          have h2 : 2 * y % 2 = 0 := by omega
          simp [h1, h2]
        | succ j =>
          rw [Nat.testBit_and, Nat.testBit_add_one, Nat.testBit_add_one, Nat.testBit_add_one]
          have hd1 : x / 2 = y := by omega
          have hd2 : (x - 1) / 2 = y := by omega
          have hd3 : 2 * y / 2 = y := by omega
          rw [hd1, hd2, hd3, Bool.and_self]
      constructor
      · intro h0
        exact ⟨0, by omega⟩
      · rintro ⟨i, hi⟩
        cases i with
        | zero => norm_num at hi; omega
        | succ i =>
          have hp : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
          omega

/-! ## 2. Diagonal of the product-cube propagator -/

open HypercubeProduct

section ExpDiag
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The Hadamard diagonalizer `U = !![1,1;1,-1]`. -/
private def hadU : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

private theorem hadU_mul_half : hadU * ((1 / 2 : ℂ) • hadU) = 1 := by
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU_isUnit : IsUnit hadU := by
  refine ⟨⟨hadU, (1 / 2 : ℂ) • hadU, hadU_mul_half, ?_⟩, rfl⟩
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU_inv : hadU⁻¹ = (1 / 2 : ℂ) • hadU := by
  apply Matrix.inv_eq_right_inv; exact hadU_mul_half

private theorem diag_fin_two (a b : ℂ) :
    (Matrix.diagonal ![a, b]) = !![a, 0; 0, b] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem half_smul_hadU :
    ((1 / 2 : ℂ) • hadU) = !![(1 : ℂ) / 2, 1 / 2; 1 / 2, -(1 / 2)] := by
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem X_eq_conj_diag :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU * (Matrix.diagonal ![1, -1]) * hadU⁻¹ := by
  rw [hadU_inv, diag_fin_two, half_smul_hadU]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- `exp(s•X)` fully expanded as a `2×2` literal. -/
private theorem exp_smul_X_lit (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![(NormedSpace.exp s + NormedSpace.exp (-s)) / 2,
            (NormedSpace.exp s - NormedSpace.exp (-s)) / 2;
           (NormedSpace.exp s - NormedSpace.exp (-s)) / 2,
            (NormedSpace.exp s + NormedSpace.exp (-s)) / 2] := by
  have hsmul : s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU * (Matrix.diagonal ![s, -s]) * hadU⁻¹ := by
    have hd : (Matrix.diagonal ![s, -s] : Matrix (Fin 2) (Fin 2) ℂ)
        = s • Matrix.diagonal ![1, -1] := by
      rw [← Matrix.diagonal_smul]; congr 1; funext k; fin_cases k <;> simp
    rw [X_eq_conj_diag, hd, mul_smul_comm, smul_mul_assoc]
  rw [hsmul, Matrix.exp_conj _ _ hadU_isUnit, Matrix.exp_diagonal]
  have hdiag : (fun i => NormedSpace.exp (![s, -s] i))
      = (![NormedSpace.exp s, NormedSpace.exp (-s)] : Fin 2 → ℂ) := by
    funext k; fin_cases k <;> simp
  rw [Pi.exp_def, hdiag, hadU_inv, diag_fin_two, half_smul_hadU]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- The diagonal of the single-edge propagator: `K₂.evolve t b b = cos t`.
Both diagonal entries of `exp(-(it)·X)` equal `(e^{-it} + e^{it})/2 = cos t`. -/
theorem K2_evolve_diag (t : ℝ) (b : Fin 2) :
    K2.evolve t b b = ((Real.cos t : ℝ) : ℂ) := by
  have h1 : Complex.exp (Complex.I * ((t : ℝ) : ℂ))
      = ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I := by
    rw [show Complex.I * ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I]
  have h2 : Complex.exp (-(Complex.I * ((t : ℝ) : ℂ)))
      = ((Real.cos t : ℝ) : ℂ) - ((Real.sin t : ℝ) : ℂ) * Complex.I := by
    rw [show -(Complex.I * ((t : ℝ) : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hval : (NormedSpace.exp (-(Complex.I * ((t : ℝ) : ℂ)))
      + NormedSpace.exp (-(-(Complex.I * ((t : ℝ) : ℂ))))) / 2
      = ((Real.cos t : ℝ) : ℂ) := by
    rw [neg_neg, ← Complex.exp_eq_exp_ℂ, h1, h2]
    ring
  unfold WeightedGraph.evolve
  rw [K2_adj, exp_smul_X_lit]
  fin_cases b <;> simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.zero_eta,
    Fin.mk_one] <;> exact hval

/-- The diagonal of the product-cube propagator: `U(t)_{ww} = (cos t)^n` on
`hypercubeP n`, by the Kronecker factorization over the `n` edge factors. -/
theorem hypercubeP_evolve_diag (t : ℝ) :
    ∀ (n : ℕ) (w : HCVert n),
      (hypercubeP n).evolve t w w = ((Real.cos t : ℝ) : ℂ) ^ n
  | 0, w => by
      show trivialGraph.evolve t w w = _
      rw [pow_zero]
      unfold WeightedGraph.evolve trivialGraph
      simp only [smul_zero, NormedSpace.exp_zero, Matrix.one_apply_eq]
  | (n + 1), w => by
      obtain ⟨b, s⟩ := w
      show (WeightedGraph.cartesianProduct K2 (hypercubeP n)).evolve t (b, s) (b, s) = _
      rw [WeightedGraph.evolve_cartesianProduct_apply, K2_evolve_diag,
        hypercubeP_evolve_diag t n s, pow_succ, mul_comm]

end ExpDiag

/-! ## 3. The Wallis integral and the Cesàro mean of a periodic function -/

open Filter intervalIntegral

/-- **Wallis, even case, in central-binomial form.**
`∫₀^π cos²ⁿ t dt = π · C(2n,n)/4ⁿ`.  Induction on `n` via the reduction
formula `integral_cos_pow` (the boundary terms vanish at `0` and `π`) and the
central-binomial recurrence `(n+1)·C(2n+2,n+1) = 2(2n+1)·C(2n,n)`. -/
theorem integral_cos_pow_even_pi (n : ℕ) :
    ∫ t in (0 : ℝ)..Real.pi, Real.cos t ^ (2 * n)
      = Real.pi * ((Nat.centralBinom n : ℝ) / 4 ^ n) := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2, integral_cos_pow, Real.sin_pi, Real.sin_zero, ih]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hcbR : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
        = 2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hcb1 : (Nat.centralBinom (k + 1) : ℝ)
        = 2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) / ((k : ℝ) + 1) := by
      rw [eq_div_iff hk1]; linear_combination hcbR
    rw [hcb1]
    have h4 : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
    have h4k : (4 : ℝ) ^ k ≠ 0 := by positivity
    rw [h4]
    push_cast
    field_simp
    ring

/-- `⌊t/T⌋/t → T⁻¹` as `t → ∞` (for `T > 0`): squeeze between
`T⁻¹ - t⁻¹` and `T⁻¹`. -/
theorem tendsto_floor_div_atTop {T : ℝ} (hT : 0 < T) :
    Tendsto (fun t : ℝ => (⌊t / T⌋ : ℝ) / t) atTop (nhds T⁻¹) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun t : ℝ => T⁻¹ - t⁻¹) (h := fun _ : ℝ => T⁻¹)
  · simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero (𝕜 := ℝ))
  · exact tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hT0 : T ≠ 0 := hT.ne'
    have hfl : t / T - 1 < (⌊t / T⌋ : ℝ) := Int.sub_one_lt_floor (t / T)
    have heq : (t / T - 1) * t⁻¹ = T⁻¹ - t⁻¹ := by field_simp
    calc T⁻¹ - t⁻¹ = (t / T - 1) * t⁻¹ := heq.symm
      _ ≤ (⌊t / T⌋ : ℝ) * t⁻¹ :=
          mul_le_mul_of_nonneg_right hfl.le (inv_nonneg.mpr ht.le)
      _ = (⌊t / T⌋ : ℝ) / t := (div_eq_mul_inv _ _).symm
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hT0 : T ≠ 0 := hT.ne'
    have heq : (t / T) * t⁻¹ = T⁻¹ := by field_simp
    calc (⌊t / T⌋ : ℝ) / t = (⌊t / T⌋ : ℝ) * t⁻¹ := div_eq_mul_inv _ _
      _ ≤ (t / T) * t⁻¹ :=
          mul_le_mul_of_nonneg_right (Int.floor_le _) (inv_nonneg.mpr ht.le)
      _ = T⁻¹ := heq

/-- **Cesàro mean of a continuous periodic function.**  If `g` is continuous
and `T`-periodic with `T > 0`, then the running time-average
`t⁻¹ ∫₀ᵗ g` converges to the period mean `(∫₀^T g)/T`.  Proof: the primitive
is squeezed between `sInf/sSup`-shifted whole-period counts
(`Function.Periodic.sInf_add_zsmul_le_integral_of_pos` and its `sSup` mirror),
and `⌊t/T⌋/t → T⁻¹`. -/
theorem tendsto_intervalAverage_of_periodic {g : ℝ → ℝ} {T : ℝ}
    (hg : Function.Periodic g T) (hT : 0 < T) (hcont : Continuous g) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x in (0 : ℝ)..t, g x) atTop
      (nhds ((∫ x in (0 : ℝ)..T, g x) / T)) := by
  have h_int : IntervalIntegrable g MeasureTheory.volume 0 T :=
    hcont.intervalIntegrable 0 T
  set I := ∫ x in (0 : ℝ)..T, g x with hI
  set lo := sInf ((fun t => ∫ x in (0 : ℝ)..t, g x) '' Set.Icc 0 T) with hlo
  set hi := sSup ((fun t => ∫ x in (0 : ℝ)..t, g x) '' Set.Icc 0 T) with hhi
  have haux : ∀ c : ℝ,
      Tendsto (fun t : ℝ => t⁻¹ * (c + (⌊t / T⌋ : ℝ) * I)) atTop (nhds (I / T)) := by
    intro c
    have h1 : Tendsto (fun t : ℝ => c * t⁻¹ + ((⌊t / T⌋ : ℝ) / t) * I) atTop
        (nhds (c * 0 + T⁻¹ * I)) :=
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c).add
        ((tendsto_floor_div_atTop hT).mul_const I)
    have heq : (fun t : ℝ => c * t⁻¹ + ((⌊t / T⌋ : ℝ) / t) * I)
        = fun t : ℝ => t⁻¹ * (c + (⌊t / T⌋ : ℝ) * I) := by
      funext t; rw [div_eq_mul_inv]; ring
    have hval : c * 0 + T⁻¹ * I = I / T := by rw [mul_zero, zero_add, inv_mul_eq_div]
    rw [heq, hval] at h1
    exact h1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (haux lo) (haux hi)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := hg.sInf_add_zsmul_le_integral_of_pos h_int hT t
    rw [zsmul_eq_mul] at h
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ht.le)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := hg.integral_le_sSup_add_zsmul_of_pos h_int hT t
    rw [zsmul_eq_mul] at h
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ht.le)

end HypercubeBridge
end StdLib
end Graphplay
