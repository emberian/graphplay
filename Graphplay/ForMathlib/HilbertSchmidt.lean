-- target: Mathlib/Analysis/InnerProductSpace/HilbertSchmidt.lean (or MeasureTheory/.../KernelOperator)
/-
# Kernel integral operators on `L²(μ)` — Hilbert–Schmidt infrastructure

This file is **general Mathlib-bound infrastructure** for the integral operator
attached to a bounded measurable kernel `K : Ω → Ω → ℂ` on a measure space
`(Ω, μ)`:
`(T_K f)(x) = ∫ y, K x y · f y ∂μ`.

It is *not* graphplay-specific; it is the boundedness / self-adjointness API that
Mathlib currently lacks and that `Graphplay/Graphon.lean :: Graphon.op` needs.

## Design

The genuinely hard analytic core is the **`MemLp 2` closure**
(`kernelIntegralFun_memLp`): that `T_K f` is again square-integrable when `f` is.
This is the Cauchy–Schwarz + Fubini ("Schur test" / Hilbert–Schmidt) bound and is
the one place Mathlib has no off-the-shelf lemma. We isolate that as a named
theorem (honest `sorry`, precise gap comment) and *also* expose the two analytic
facts it produces — the `MemLp` closure and the `eLpNorm` Schur bound — as
**explicit hypotheses** to the bundled `LinearMap` / `ContinuousLinearMap`
constructors. Everything downstream of those hypotheses (linearity, the
operator-norm bound from the `eLpNorm` bound, self-adjointness from a Hermitian
kernel) is proved *genuinely*. This is the PR-ready factoring: the deep analytic
lemma is the only thing left to fill, and it is stated cleanly.

## Main definitions

* `kernelIntegralFun K f` : the pointwise action `x ↦ ∫ y, K x y · f y ∂μ`.
* `kernelIntegralLM`     : the underlying `ℂ`-linear map on `L²`, given the
  `MemLp 2` closure as a hypothesis.
* `kernelIntegralCLM`    : the bounded operator, given the `MemLp` closure and the
  `eLpNorm` Schur bound as hypotheses; operator norm `≤ C`.

## Main statements

* `kernelIntegralFun_memLp` — the `MemLp 2` closure (Cauchy–Schwarz + Fubini),
  honest `sorry`.
* `kernelIntegralFun_aestronglyMeasurable` — genuine: `T_K f` is a.e. strongly
  measurable (from `AEStronglyMeasurable.integral_prod_right'`).
* `kernelIntegralCLM_norm_le` — genuine: operator norm `≤ C` from the Schur bound.
* `kernelIntegralCLM_isSelfAdjoint` — genuine reduction to a symmetry identity
  (Hermitian kernel ⟹ self-adjoint), with the Fubini swap honestly `sorry`d.
* `kernelIntegralCLM_isCompact` — statement-only (HS ⟹ compact), honest `sorry`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

open scoped MeasureTheory ENNReal Complex ComplexConjugate
open MeasureTheory RCLike

namespace Graphplay.ForMathlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The pointwise action -/

/-- The pointwise (Bochner) action of the kernel integral operator with kernel
`K`: `(kernelIntegralFun K f) x = ∫ y, K x y · f y ∂μ`. -/
noncomputable def kernelIntegralFun (K : Ω → Ω → ℂ) (f : Ω → ℂ) : Ω → ℂ :=
  fun x => ∫ y, K x y * f y ∂μ

@[simp] theorem kernelIntegralFun_apply (K : Ω → Ω → ℂ) (f : Ω → ℂ) (x : Ω) :
    kernelIntegralFun (μ := μ) K f x = ∫ y, K x y * f y ∂μ := rfl

/-- The action is `ℝ`-additive in `f` *pointwise*, whenever the two integrands are
integrable.  (Used to derive a.e. additivity on `L²`.) -/
theorem kernelIntegralFun_add_of_integrable {K : Ω → Ω → ℂ} {f g : Ω → ℂ} {x : Ω}
    (hf : Integrable (fun y => K x y * f y) μ) (hg : Integrable (fun y => K x y * g y) μ) :
    kernelIntegralFun (μ := μ) K (f + g) x =
      kernelIntegralFun (μ := μ) K f x + kernelIntegralFun (μ := μ) K g x := by
  simp only [kernelIntegralFun_apply, Pi.add_apply, mul_add]
  exact integral_add hf hg

/-- The action is `ℂ`-homogeneous in `f` *pointwise* (no integrability needed:
`integral_smul`/`integral_const_mul`). -/
theorem kernelIntegralFun_smul (K : Ω → Ω → ℂ) (c : ℂ) (f : Ω → ℂ) (x : Ω) :
    kernelIntegralFun (μ := μ) K (c • f) x = c • kernelIntegralFun (μ := μ) K f x := by
  simp only [kernelIntegralFun_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; ext y; ring

/-! ## A.e. measurability of the action

This piece is genuinely provable from Mathlib's Fubini measurability lemma
`AEStronglyMeasurable.integral_prod_right'`: if the kernel-times-function
`(x, y) ↦ K x y · f y` is a.e. strongly measurable on `μ ⊗ μ`, then its
`y`-integral is a.e. strongly measurable in `x`. -/

/-- If `(x,y) ↦ K x y · f y` is a.e. strongly measurable on the product, then the
kernel action `x ↦ ∫ y, K x y · f y ∂μ` is a.e. strongly measurable. -/
theorem kernelIntegralFun_aestronglyMeasurable [SFinite μ] {K : Ω → Ω → ℂ} {f : Ω → ℂ}
    (h : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2 * f p.2) (μ.prod μ)) :
    AEStronglyMeasurable (kernelIntegralFun (μ := μ) K f) μ :=
  h.integral_prod_right'

/-- Joint a.e. strong measurability of the integrand `(x,y) ↦ K x y · f y` from
joint measurability of `K` and a.e. strong measurability of `f`. -/
theorem aestronglyMeasurable_kernel_mul [SFinite μ] {K : Ω → Ω → ℂ} {f : Ω → ℂ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2 * f p.2) (μ.prod μ) :=
  hK.mul (hf.comp_snd)

/-! ## Integrability of a bounded kernel on the product (genuine)

The foundational fact that unblocks every Fubini swap downstream: a bounded,
a.e.-strongly-measurable kernel on a **finite** measure space is integrable on the
product `μ ⊗ μ`.  The product of two finite measures is finite
(`prod.instIsFiniteMeasure`), so domination by the constant bound `C` and
`MeasureTheory.Integrable.of_bound` close it. This is what every `MemLp`/Fubini
sorry was waiting on. -/

/-- **Kernel integrability.**  A bounded, a.e.-strongly-measurable kernel
`K : Ω → Ω → ℂ` on a finite measure space is integrable on the product `μ ⊗ μ`.

This is the analytic foundation: with `μ` finite, `μ ⊗ μ` is finite, so a kernel
essentially bounded by `C` is dominated by the (integrable) constant `C` and hence
integrable via `MeasureTheory.Integrable.of_bound`. -/
theorem kernel_integrable [IsFiniteMeasure μ] {K : Ω → Ω → ℂ} {C : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ C) :
    Integrable (Function.uncurry K) (μ.prod μ) :=
  Integrable.of_bound hK C hbdd

/-- The kernel-times-function integrand `(x,y) ↦ K x y · f y` is integrable on the
product whenever the kernel is bounded and `f ∈ L²(μ)` (hence `L¹` on a finite
measure space).  Genuine, via Hölder against the bounded kernel. -/
theorem kernel_mul_integrable [IsFiniteMeasure μ] {K : Ω → Ω → ℂ} {C : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ C) (f : Lp ℂ 2 μ) :
    Integrable (fun p : Ω × Ω => K p.1 p.2 * f p.2) (μ.prod μ) := by
  -- a.e. strong measurability of the integrand
  have hf : AEStronglyMeasurable (f : Ω → ℂ) μ := (Lp.memLp f).1
  have hmeas : AEStronglyMeasurable (fun p : Ω × Ω => K p.1 p.2 * f p.2) (μ.prod μ) :=
    aestronglyMeasurable_kernel_mul hK hf
  -- `f` is integrable on `μ` (finite measure: `L² ⊆ L¹`)
  have hf1 : Integrable (f : Ω → ℂ) μ := (Lp.memLp f).integrable (by norm_num)
  -- the function `p ↦ C * ‖f p.2‖` is integrable on the product …
  have hg : Integrable (fun p : Ω × Ω => C * ‖(f : Ω → ℂ) p.2‖) (μ.prod μ) :=
    (hf1.norm.const_mul C).comp_snd μ
  -- … and dominates `‖K p.1 p.2 * f p.2‖`.
  refine hg.mono' hmeas ?_
  filter_upwards [hbdd] with p hp
  have hKp : ‖K p.1 p.2‖ ≤ C := hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hKp (norm_nonneg _)

/-! ## The `MemLp 2` closure — the analytic crux (Cauchy–Schwarz, genuine)

This is the one genuinely hard lemma. The deep step is the **pointwise
Cauchy–Schwarz bound**: for a kernel essentially bounded by `M`, the action is
*bounded by a constant*, namely
`‖(T_K f)(x)‖ ≤ M · √μ(univ) · ‖f‖₂` for a.e. `x`.
We prove this in full (`kernelIntegralFun_ae_norm_le`), and read off both the
`MemLp 2` closure and the `eLpNorm` bound from it. -/

/-- **Pointwise Cauchy–Schwarz constant bound (the analytic core).**

For a jointly measurable kernel `K` essentially bounded by `M ≥ 0` on a finite
measure space, the kernel action `T_K f` is, for a.e. `x`, bounded by the
*constant* `M · √(μ univ).toReal · ‖f‖`:
`‖∫ y, K x y · f y ∂μ‖ ≤ M · √(μ univ).toReal · ‖f‖`.

Proof: `‖∫ y, K x y · f y ∂μ‖ ≤ ∫ y, ‖K x y‖ · ‖f y‖ ∂μ` (triangle inequality for
the Bochner integral), then Hölder with conjugate exponents `2, 2`
(`integral_mul_norm_le_Lp_mul_Lq`) bounds this by
`(∫ ‖K x y‖² ∂μ)^{1/2} · (∫ ‖f y‖² ∂μ)^{1/2}`.
The first factor is `≤ √(M² · (μ univ).toReal) = M · √(μ univ).toReal` since the
slice `K x ·` is a.e. bounded by `M`; the second factor is `‖f‖`. -/
theorem kernelIntegralFun_ae_norm_le [IsFiniteMeasure μ] {K : Ω → Ω → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ M) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, ‖kernelIntegralFun (μ := μ) K (f : Ω → ℂ) x‖
      ≤ M * (μ Set.univ).toReal.sqrt * ‖f‖ := by
  -- `(2 : ℝ)` is its own Hölder conjugate.
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  -- `f ∈ L²` as an honest `MemLp` fact, and `‖f‖ = (∫ ‖f y‖² ∂μ)^{1/2}`.
  have hf : MemLp (f : Ω → ℂ) 2 μ := Lp.memLp f
  have hf2 : MemLp (f : Ω → ℂ) (ENNReal.ofReal 2) μ := by
    rwa [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 by norm_num]
  -- `‖f‖ = (∫ ‖f y‖^2 ∂μ)^(1/2)`.
  have hnormf : ((∫ y, ‖(f : Ω → ℂ) y‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) = ‖f‖ := by
    rw [Lp.norm_def, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal]
    · norm_num
    · positivity
  -- slice facts: for a.e. `x`, `K x ·` is a.e. strongly measurable and a.e. bounded by `M`.
  have hslice_meas : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => K x y) μ := by
    have := hK.prodMk_left (ν := μ)
    filter_upwards [this] with x hx using hx
  have hslice_bdd : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖K x y‖ ≤ M := Measure.ae_ae_of_ae_prod hbdd
  filter_upwards [hslice_meas, hslice_bdd] with x hxm hxb
  -- The slice `K x ·` is in `L²` (bounded on a finite measure space).
  have hKx : MemLp (fun y => K x y) 2 μ := MemLp.of_bound hxm M hxb
  have hKx2 : MemLp (fun y => K x y) (ENNReal.ofReal 2) μ := by
    rwa [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 by norm_num]
  -- Step 1: triangle inequality `‖∫ ‖ ≤ ∫ ‖·‖`, then `‖K x y · f y‖ = ‖K x y‖ · ‖f y‖`.
  calc ‖kernelIntegralFun (μ := μ) K (f : Ω → ℂ) x‖
      = ‖∫ y, K x y * (f : Ω → ℂ) y ∂μ‖ := rfl
    _ ≤ ∫ y, ‖K x y‖ * ‖(f : Ω → ℂ) y‖ ∂μ := by
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => norm_mul _ _)
    -- Step 2: Hölder with exponents `2, 2`.
    _ ≤ (∫ y, ‖K x y‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
          * (∫ y, ‖(f : Ω → ℂ) y‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq hpq hKx2 hf2
    -- Step 3: bound the kernel factor by `M · √(μ univ).toReal`, rewrite `f` factor as `‖f‖`.
    _ ≤ (M ^ 2 * (μ Set.univ).toReal) ^ (1 / (2 : ℝ)) * ‖f‖ := by
        rw [hnormf]
        gcongr
        -- `∫ ‖K x y‖² ∂μ ≤ ∫ M² ∂μ = M² · (μ univ).toReal`.
        have hKxInt : Integrable (fun y => ‖K x y‖ ^ (2 : ℝ)) μ := by
          have := hKx.integrable_norm_rpow (by norm_num) (by norm_num)
          simpa using this
        calc ∫ y, ‖K x y‖ ^ (2 : ℝ) ∂μ
            ≤ ∫ _y, M ^ 2 ∂μ := by
              refine integral_mono_ae hKxInt (integrable_const _) ?_
              filter_upwards [hxb] with y hy
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              have h0 : (0 : ℝ) ≤ ‖K x y‖ := norm_nonneg _
              nlinarith [hy, h0]
          _ = M ^ 2 * (μ Set.univ).toReal := by
              rw [integral_const, smul_eq_mul, mul_comm, measureReal_def]
    -- Step 4: `(M² · (μ univ).toReal)^{1/2} = M · √(μ univ).toReal`.
    _ = M * (μ Set.univ).toReal.sqrt * ‖f‖ := by
        congr 1
        rw [Real.mul_rpow (by positivity) ENNReal.toReal_nonneg,
          ← Real.rpow_natCast M 2, ← Real.rpow_mul hM]
        simp only [Nat.cast_ofNat]
        rw [show (2 : ℝ) * (1 / 2) = 1 by ring, Real.rpow_one, Real.sqrt_eq_rpow]

/-- **`MemLp 2` closure of the kernel action.**

For a jointly measurable kernel `K` essentially bounded by `M` on a finite
measure space and an `f ∈ L²(μ)`, the action `kernelIntegralFun K f` is again in
`L²(μ)`.

**Now genuine (no `sorry`).**  By the pointwise Cauchy–Schwarz bound
`kernelIntegralFun_ae_norm_le`, `T_K f` is *a.e. bounded by the constant*
`M · √(μ univ).toReal · ‖f‖`; on a finite measure space a bounded a.e.-strongly
measurable function is `MemLp 2` (`MemLp.of_bound`).  A.e. strong measurability
of `T_K f` is `kernelIntegralFun_aestronglyMeasurable`. -/
theorem kernelIntegralFun_memLp [SFinite μ] (hμ : μ Set.univ ≠ ∞) {K : Ω → Ω → ℂ} {M : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ M) (f : Lp ℂ 2 μ) :
    MemLp (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ := by
  -- `μ` is finite (from `hμ : μ univ ≠ ∞`).
  haveI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hμ⟩
  -- The bound `M` can be taken nonnegative without loss (clamp at 0): the a.e.
  -- bound `‖·‖ ≤ M` still holds for `max M 0 ≥ ‖·‖ ≥ 0`.
  have hbdd' : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ max M 0 :=
    hbdd.mono fun p hp => hp.trans (le_max_left _ _)
  -- a.e. strong measurability of `T_K f` from the Fubini measurability lemma.
  have hmeas : AEStronglyMeasurable (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) μ :=
    kernelIntegralFun_aestronglyMeasurable (aestronglyMeasurable_kernel_mul hK (Lp.memLp f).1)
  -- a.e. constant bound on `T_K f` (the analytic core).
  have hae := kernelIntegralFun_ae_norm_le (μ := μ) (le_max_right M 0) hK hbdd' f
  -- bounded a.e. on a finite measure ⟹ `MemLp 2`.
  exact MemLp.of_bound hmeas (max M 0 * (μ Set.univ).toReal.sqrt * ‖f‖) hae

/-- **Sharp `eLpNorm` (Schur / Hilbert–Schmidt) bound — fully genuine.**

`eLpNorm (T_K f) 2 μ ≤ (M · μ(univ)) · eLpNorm f 2 μ`.

This is the universally-valid quantitative half of `kernelIntegralFun_memLp`, with
**no `sorry`**.  By the pointwise Cauchy–Schwarz bound
(`kernelIntegralFun_ae_norm_le`), `T_K f` is a.e. bounded by the constant
`M · √(μ univ).toReal · ‖f‖`; `eLpNorm_le_of_ae_bound` then gives
`eLpNorm (T_K f) 2 μ ≤ (μ univ)^{1/2} · ofReal (M · √(μ univ).toReal · ‖f‖)`,
and `(μ univ)^{1/2} · √(μ univ).toReal = (μ univ).toReal` (as `μ univ ≠ ∞`), so the
constant collapses to `M · (μ univ).toReal`.  The corresponding operator-norm
bound `‖T_K‖ ≤ M · μ(univ)` is exactly what `Graphon.op_norm_le` states. -/
theorem kernelIntegralFun_eLpNorm_le_mul [SFinite μ] (hμ : μ Set.univ ≠ ∞) {K : Ω → Ω → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ M) (f : Lp ℂ 2 μ) :
    eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ
      ≤ ENNReal.ofReal (M * (μ Set.univ).toReal) * eLpNorm (f : Ω → ℂ) 2 μ := by
  haveI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hμ⟩
  have hae := kernelIntegralFun_ae_norm_le (μ := μ) hM hK hbdd f
  -- `eLpNorm (T_K f) 2 μ ≤ (μ univ)^{1/2} · ofReal (M · √(μ univ).toReal · ‖f‖)`.
  have hstep : eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ
      ≤ μ Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹
        * ENNReal.ofReal (M * (μ Set.univ).toReal.sqrt * ‖f‖) :=
    eLpNorm_le_of_ae_bound hae
  refine hstep.trans ?_
  -- `(μ univ)^{1/2} = ofReal (√(μ univ).toReal)`  (finite measure).
  have hsqrt : μ Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ = ENNReal.ofReal (μ Set.univ).toReal.sqrt := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_toReal hμ, ENNReal.ofReal_rpow_of_nonneg
      ENNReal.toReal_nonneg (by norm_num), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    norm_num
  have heLp_f : eLpNorm (f : Ω → ℂ) 2 μ = ENNReal.ofReal ‖f‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  rw [hsqrt, heLp_f]
  -- collapse `√(μ univ).toReal · (M · √(μ univ).toReal · ‖f‖) = M · (μ univ).toReal · ‖f‖`.
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  congr 1
  have hsq : (μ Set.univ).toReal.sqrt * (μ Set.univ).toReal.sqrt = (μ Set.univ).toReal :=
    Real.mul_self_sqrt ENNReal.toReal_nonneg
  calc (μ Set.univ).toReal.sqrt * (M * (μ Set.univ).toReal.sqrt * ‖f‖)
      = ((μ Set.univ).toReal.sqrt * (μ Set.univ).toReal.sqrt) * (M * ‖f‖) := by ring
    _ = (μ Set.univ).toReal * (M * ‖f‖) := by rw [hsq]
    _ = M * (μ Set.univ).toReal * ‖f‖ := by ring

/-! ## The linear map (genuine, given the `MemLp` closure)

We take the `MemLp 2` closure as an explicit hypothesis `hmem`.  Given it, the
linear-map structure is proved *genuinely* from `MemLp.toLp_add` /
`MemLp.toLp_const_smul` and the pointwise (a.e.) linearity of the action. -/

/-- The kernel integral operator as a bare `ℂ`-linear map on `L²(μ)`, taking the
`MemLp 2` closure `hmem` as a hypothesis.  Linearity is genuine. -/
noncomputable def kernelIntegralLM (K : Ω → Ω → ℂ)
    (hmem : ∀ f : Lp ℂ 2 μ, MemLp (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ)
    (hadd : ∀ f g : Lp ℂ 2 μ,
      kernelIntegralFun (μ := μ) K ((f + g : Lp ℂ 2 μ) : Ω → ℂ)
        =ᵐ[μ] kernelIntegralFun (μ := μ) K (f : Ω → ℂ)
          + kernelIntegralFun (μ := μ) K (g : Ω → ℂ))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ),
      kernelIntegralFun (μ := μ) K ((c • f : Lp ℂ 2 μ) : Ω → ℂ)
        =ᵐ[μ] c • kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) :
    (Lp ℂ 2 μ) →ₗ[ℂ] (Lp ℂ 2 μ) where
  toFun f := (hmem f).toLp (kernelIntegralFun (μ := μ) K (f : Ω → ℂ))
  map_add' f g := by
    -- `T_K (f+g) =ᵃᵉ T_K f + T_K g` (the hypothesis `hadd`), then `MemLp.toLp_add`.
    refine (MemLp.toLp_congr (hmem (f + g)) (((hmem f).add (hmem g))) (hadd f g)).trans ?_
    exact MemLp.toLp_add (hmem f) (hmem g)
  map_smul' c f := by
    -- `T_K (c • f) =ᵃᵉ c • T_K f` (the hypothesis `hsmul`), then `MemLp.toLp_const_smul`.
    simp only [RingHom.id_apply]
    refine (MemLp.toLp_congr (hmem (c • f)) ((hmem f).const_smul c) (hsmul c f)).trans ?_
    exact MemLp.toLp_const_smul c (hmem f)

@[simp] theorem kernelIntegralLM_apply (K : Ω → Ω → ℂ)
    {hmem hadd hsmul} (f : Lp ℂ 2 μ) :
    (kernelIntegralLM (μ := μ) K hmem hadd hsmul) f
      = (hmem f).toLp (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) := rfl

/-! ## The bounded operator (genuine, given `MemLp` closure + `eLpNorm` bound)

The operator-norm bound is proved *genuinely* from the `eLpNorm` Schur bound
`hSchur`, which is exactly what `kernelIntegralFun_eLpNorm_le_mul` supplies. -/

/-- The kernel integral operator as a **bounded** operator `L²(μ) →L[ℂ] L²(μ)`,
with operator norm `≤ C`.  Built via `LinearMap.mkContinuous`; the operator-norm
estimate is proved genuinely from the `eLpNorm` Schur bound `hSchur`. -/
noncomputable def kernelIntegralCLM (K : Ω → Ω → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hmem : ∀ f : Lp ℂ 2 μ, MemLp (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ)
    (hadd : ∀ f g : Lp ℂ 2 μ,
      kernelIntegralFun (μ := μ) K ((f + g : Lp ℂ 2 μ) : Ω → ℂ)
        =ᵐ[μ] kernelIntegralFun (μ := μ) K (f : Ω → ℂ)
          + kernelIntegralFun (μ := μ) K (g : Ω → ℂ))
    (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ),
      kernelIntegralFun (μ := μ) K ((c • f : Lp ℂ 2 μ) : Ω → ℂ)
        =ᵐ[μ] c • kernelIntegralFun (μ := μ) K (f : Ω → ℂ))
    (hSchur : ∀ f : Lp ℂ 2 μ,
      eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ
        ≤ ENNReal.ofReal C * eLpNorm (f : Ω → ℂ) 2 μ) :
    (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
  (kernelIntegralLM (μ := μ) K hmem hadd hsmul).mkContinuous C <| by
    intro f
    -- `‖T_K f‖ = (eLpNorm (T_K f) 2 μ).toReal`, then push `hSchur` through `toReal`.
    rw [kernelIntegralLM_apply (μ := μ), Lp.norm_toLp]
    have hle := hSchur f
    have hfin : eLpNorm (f : Ω → ℂ) 2 μ ≠ ∞ := Lp.eLpNorm_ne_top f
    have hmemfin : eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ ≠ ∞ := (hmem f).2.ne
    have key : (eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ).toReal
        ≤ (ENNReal.ofReal C * eLpNorm (f : Ω → ℂ) 2 μ).toReal :=
      ENNReal.toReal_mono (by finiteness) hle
    refine key.trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    -- `(eLpNorm f 2 μ).toReal = ‖f‖`.
    rw [show (eLpNorm (f : Ω → ℂ) 2 μ).toReal = ‖f‖ from (Lp.norm_def f).symm]

/-! ## Hilbert–Schmidt finite-rank truncation infrastructure (genuine, reusable)

This block builds, **fully genuinely (no `sorry`)**, the analytic machinery for the
Hilbert–Schmidt ⟹ compact theorem:

* the **`L²(μ⊗μ)` (Hilbert–Schmidt) operator bound**
  `eLpNorm (T_K f) 2 μ ≤ ‖K‖_{L²(μ⊗μ)} · ‖f‖₂` — the sharp dominance of the operator
  norm by the *Hilbert–Schmidt* norm of the kernel (pointwise Cauchy–Schwarz in
  `ℝ≥0∞` + Tonelli).  This is the bound that makes the finite-rank truncation
  argument converge, and it is the genuinely-quantitative heart of the theorem;
* **finite-rank ⟹ compact** (`isCompactOperator_of_finiteDimensional_range`): a CLM
  with finite-dimensional range is a compact operator (it factors through a
  finite-dimensional, hence proper/locally-compact, subspace).

These two facts reduce `HS ⟹ compact` to the single classical density statement
("finite-rank operators are operator-norm dense in the Hilbert–Schmidt class"),
isolated below as `exists_finiteRank_tendsto_kernelIntegralCLM`. -/

/-- **Cauchy–Schwarz for `lintegral` in `ℝ≥0∞`** (the `p = q = 2` Hölder bound,
squared): `(∫⁻ f·g)² ≤ (∫⁻ f²)·(∫⁻ g²)`. -/
theorem lintegral_enorm_mul_sq_le (f g : Ω → ℝ≥0∞)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ y, f y * g y ∂μ) ^ 2 ≤ (∫⁻ y, f y ^ 2 ∂μ) * (∫⁻ y, g y ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg
  simp only [Pi.mul_apply] at h
  calc (∫⁻ y, f y * g y ∂μ) ^ 2
      ≤ ((∫⁻ y, f y ^ (2:ℝ) ∂μ) ^ (1/(2:ℝ)) * (∫⁻ y, g y ^ (2:ℝ) ∂μ) ^ (1/(2:ℝ))) ^ 2 := by
        gcongr
    _ = (∫⁻ y, f y ^ 2 ∂μ) * (∫⁻ y, g y ^ 2 ∂μ) := by
        rw [mul_pow, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_natCast _ 2,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]; norm_num

/-- `(eLpNorm f 2 μ)² = ∫⁻ ‖f‖ₑ²` — the `L²` seminorm as a Lebesgue integral. -/
theorem eLpNorm_two_sq (f : Ω → ℂ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞).toReal = 2 by norm_num,
    ← ENNReal.rpow_natCast (((∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂μ)) ^ (1 / (2:ℝ))) 2, ← ENNReal.rpow_mul]
  norm_num

/-- Un-squaring in `ℝ≥0∞`: `a² ≤ b²·c² ⟹ a ≤ b·c`. -/
theorem ennreal_le_of_sq_le_mul_sq (a b c : ℝ≥0∞) (h : a ^ 2 ≤ b ^ 2 * c ^ 2) : a ≤ b * c := by
  rw [← mul_pow] at h
  have := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rwa [← ENNReal.rpow_natCast a 2, ← ENNReal.rpow_natCast (b*c) 2, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, show ((2:ℕ):ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_one] at this

/-- **Hilbert–Schmidt `eLpNorm` bound, squared form.**

`(eLpNorm (T_K f) 2 μ)² ≤ (eLpNorm K 2 (μ⊗μ))² · (eLpNorm f 2 μ)²`.

Genuine.  Pointwise, `‖(T_K f)(x)‖ₑ² ≤ (∫⁻_y ‖K x y‖ₑ²)·(∫⁻_y ‖f y‖ₑ²)` by the
triangle inequality for the Bochner integral followed by `lintegral_enorm_mul_sq_le`;
integrating in `x`, pulling out the `f`-factor (constant in `x`) and applying
Tonelli (`lintegral_lintegral`) collapses `∫⁻_x ∫⁻_y ‖K x y‖ₑ²` to
`∫⁻_p ‖K p‖ₑ² = (eLpNorm K 2 (μ⊗μ))²`. -/
theorem kernelIntegralFun_eLpNorm_sq_le_hs [SFinite μ] (K : Ω → Ω → ℂ) (f : Ω → ℂ)
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hf : AEStronglyMeasurable f μ) :
    (eLpNorm (kernelIntegralFun (μ := μ) K f) 2 μ) ^ 2
      ≤ (eLpNorm (Function.uncurry K) 2 (μ.prod μ)) ^ 2 * (eLpNorm f 2 μ) ^ 2 := by
  rw [eLpNorm_two_sq, eLpNorm_two_sq, eLpNorm_two_sq]
  have hKslice : ∀ᵐ x ∂μ, AEMeasurable (fun y => ‖K x y‖ₑ) μ := by
    filter_upwards [hK.prodMk_left (ν := μ)] with x hx using hx.enorm
  have hfe : AEMeasurable (fun y => ‖f y‖ₑ) μ := hf.enorm
  have hKsq : AEMeasurable (fun p : Ω × Ω => ‖Function.uncurry K p‖ₑ ^ 2) (μ.prod μ) :=
    hK.enorm.pow_const 2
  have hinner : AEMeasurable (fun x => ∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ) μ := hKsq.lintegral_prod_right'
  set Cf : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ with hCf
  have hpt : (fun x => ‖kernelIntegralFun (μ := μ) K f x‖ₑ ^ 2)
      ≤ᵐ[μ] fun x => (∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ) * Cf := by
    filter_upwards [hKslice] with x hx
    show ‖∫ y, K x y * f y ∂μ‖ₑ ^ 2 ≤ _
    calc ‖∫ y, K x y * f y ∂μ‖ₑ ^ 2
        ≤ (∫⁻ y, ‖K x y * f y‖ₑ ∂μ) ^ 2 := by
          gcongr; exact enorm_integral_le_lintegral_enorm _
      _ = (∫⁻ y, ‖K x y‖ₑ * ‖f y‖ₑ ∂μ) ^ 2 := by simp_rw [enorm_mul]
      _ ≤ (∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ) * Cf := lintegral_enorm_mul_sq_le _ _ hx hfe
  calc ∫⁻ x, ‖kernelIntegralFun (μ := μ) K f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ) * Cf ∂μ := lintegral_mono_ae hpt
    _ = (∫⁻ x, (∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ) ∂μ) * Cf := lintegral_mul_const'' _ hinner
    _ = (∫⁻ p, ‖Function.uncurry K p‖ₑ ^ 2 ∂(μ.prod μ)) * Cf := by
        congr 1
        exact lintegral_lintegral (f := fun x y => ‖K x y‖ₑ ^ 2) hKsq

/-- **Hilbert–Schmidt `eLpNorm` bound.**

`eLpNorm (T_K f) 2 μ ≤ ‖K‖_{L²(μ⊗μ)} · ‖f‖₂`.  The operator-norm of the kernel
integral operator is dominated by the *Hilbert–Schmidt* (`L²`-of-the-kernel) norm.
Genuine; the square root of `kernelIntegralFun_eLpNorm_sq_le_hs`. -/
theorem kernelIntegralFun_eLpNorm_le_hs [SFinite μ] (K : Ω → Ω → ℂ) (f : Ω → ℂ)
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (kernelIntegralFun (μ := μ) K f) 2 μ
      ≤ eLpNorm (Function.uncurry K) 2 (μ.prod μ) * eLpNorm f 2 μ :=
  ennreal_le_of_sq_le_mul_sq _ _ _ (kernelIntegralFun_eLpNorm_sq_le_hs K f hK hf)

/-- **Finite rank ⟹ compact operator.**  A continuous linear map `T : X →L[𝕜] Y`
between normed spaces over a proper field `𝕜` (e.g. `ℂ`) whose range is
finite-dimensional is a compact operator.

Genuine.  `T` factors as `R.subtypeL ∘ (T.codRestrict R)` through its range
`R = LinearMap.range T`; `R` is finite-dimensional, hence proper, hence locally
compact, so `T.codRestrict R` is compact (`isCompactOperator_of_locallyCompactSpace_dom`)
and composing with the (continuous) inclusion preserves compactness. -/
theorem isCompactOperator_of_finiteDimensional_range
    {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (hfin : FiniteDimensional 𝕜 (LinearMap.range (T : X →ₗ[𝕜] Y))) :
    IsCompactOperator T := by
  set R := LinearMap.range (T : X →ₗ[𝕜] Y) with hR
  have hmem : ∀ x, T x ∈ R := fun x => LinearMap.mem_range_self _ x
  let S : X →L[𝕜] R := T.codRestrict R hmem
  have hSc : IsCompactOperator S := by
    have : ProperSpace R := FiniteDimensional.proper 𝕜 R
    exact isCompactOperator_of_locallyCompactSpace_dom S
  have hcomp : T = R.subtypeL.comp S := by ext x; rfl
  rw [hcomp]
  exact hSc.clm_comp R.subtypeL

section Bundled

-- The data needed to assemble the bounded kernel integral operator, with all
-- analytic hypotheses bundled.  Downstream lemmas quantify over these so the
-- measure `μ` and all the proof obligations are pinned consistently.
variable (K : Ω → Ω → ℂ) (C : ℝ) (hC : 0 ≤ C)
  (hmem : ∀ f : Lp ℂ 2 μ, MemLp (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ)
  (hadd : ∀ f g : Lp ℂ 2 μ,
    kernelIntegralFun (μ := μ) K ((f + g : Lp ℂ 2 μ) : Ω → ℂ)
      =ᵐ[μ] kernelIntegralFun (μ := μ) K (f : Ω → ℂ)
        + kernelIntegralFun (μ := μ) K (g : Ω → ℂ))
  (hsmul : ∀ (c : ℂ) (f : Lp ℂ 2 μ),
    kernelIntegralFun (μ := μ) K ((c • f : Lp ℂ 2 μ) : Ω → ℂ)
      =ᵐ[μ] c • kernelIntegralFun (μ := μ) K (f : Ω → ℂ))
  (hSchur : ∀ f : Lp ℂ 2 μ,
    eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ
      ≤ ENNReal.ofReal C * eLpNorm (f : Ω → ℂ) 2 μ)

@[simp] theorem kernelIntegralCLM_apply (f : Lp ℂ 2 μ) :
    (kernelIntegralCLM K C hC hmem hadd hsmul hSchur) f
      = (hmem f).toLp (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) := rfl

/-- **Operator-norm bound** for the kernel integral operator: `‖T_K‖ ≤ C`.
Genuine — `LinearMap.mkContinuous_norm_le`. -/
theorem kernelIntegralCLM_norm_le :
    ‖kernelIntegralCLM K C hC hmem hadd hsmul hSchur‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-! ## Self-adjointness from a Hermitian kernel

A CLM on a Hilbert space is self-adjoint iff symmetric (`⟪A x, y⟫ = ⟪x, A y⟫`).
For the kernel operator this reduces, via `L2.inner_def` and Fubini, to the
Hermitian symmetry `K y x = conj (K x y)`.  We carry out the genuine reduction to
the symmetry identity and honestly `sorry` the Fubini swap (the missing
integrability/Fubini bookkeeping is the same Hilbert–Schmidt gap). -/

/-- **Self-adjointness.**  If the kernel is Hermitian (`K y x = conj (K x y)`), the
kernel integral operator is self-adjoint on `L²(μ)`.

Now **genuine**: with `μ` finite and `K` bounded/jointly measurable, the
kernel-times-function integrand is integrable on `μ ⊗ μ` (`kernel_mul_integrable`),
so the double-integral Fubini swap (`integral_integral_swap`) is licensed.  The
symmetry `⟪T_K f, g⟫ = ⟪f, T_K g⟫` then follows by unfolding `L2.inner_def`,
pushing `conj` through the slice integral, swapping the order of integration, and
applying the Hermitian symmetry `herm`.

The finiteness instance and the bounded/measurable kernel hypotheses are
legitimate (graphons are bounded kernels on a probability space), not weakenings. -/
theorem kernelIntegralCLM_isSelfAdjoint [IsFiniteMeasure μ] {D : ℝ}
    (hKmeas : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ D)
    (herm : ∀ x y, K y x = star (K x y)) :
    IsSelfAdjoint (kernelIntegralCLM K C hC hmem hadd hsmul hSchur) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  -- Abbreviations for the two genuine `L²` functions and their pointwise actions.
  set Tf := kernelIntegralFun (μ := μ) K (f : Ω → ℂ) with hTf
  set Tg := kernelIntegralFun (μ := μ) K (g : Ω → ℂ) with hTg
  -- `coeFn` of the operator applied to `f`/`g` equals the pointwise action a.e.
  have hcf : ⇑((kernelIntegralCLM K C hC hmem hadd hsmul hSchur) f) =ᵐ[μ] Tf := by
    rw [kernelIntegralCLM_apply]; exact (hmem f).coeFn_toLp
  have hcg : ⇑((kernelIntegralCLM K C hC hmem hadd hsmul hSchur) g) =ᵐ[μ] Tg := by
    rw [kernelIntegralCLM_apply]; exact (hmem g).coeFn_toLp
  -- Unfold both inner products to integrals (ℂ: `⟪a, b⟫ = conj a * b`).
  rw [L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply']
  -- Rewrite the integrands using the a.e. equalities above.
  have eL : (fun x => conj (⇑((kernelIntegralCLM K C hC hmem hadd hsmul hSchur) f) x)
        * (g : Ω → ℂ) x) =ᵐ[μ] fun x => conj (Tf x) * (g : Ω → ℂ) x := by
    filter_upwards [hcf] with x hx; rw [hx]
  have eR : (fun x => conj ((f : Ω → ℂ) x)
        * (⇑((kernelIntegralCLM K C hC hmem hadd hsmul hSchur) g) x))
      =ᵐ[μ] fun x => conj ((f : Ω → ℂ) x) * Tg x := by
    filter_upwards [hcg] with x hx; rw [hx]
  refine Eq.trans (integral_congr_ae eL) (Eq.trans ?_ (integral_congr_ae eR).symm)
  -- LHS integrand: `conj (∫ y, K x y * f y) * g x`.
  -- RHS integrand: `conj (f x) * (∫ y, K x y * g y)`.
  -- Push `conj` through the slice integral and pull the outer factor inside.
  have hL : ∀ x, conj (Tf x) * (g : Ω → ℂ) x
      = ∫ y, (conj (K x y) * conj ((f : Ω → ℂ) y)) * (g : Ω → ℂ) x ∂μ := by
    intro x
    rw [hTf, kernelIntegralFun_apply, ← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_mul]
  have hR : ∀ x, conj ((f : Ω → ℂ) x) * Tg x
      = ∫ y, conj ((f : Ω → ℂ) x) * (K x y * (g : Ω → ℂ) y) ∂μ := by
    intro x
    rw [hTg, kernelIntegralFun_apply, ← integral_const_mul]
  simp only [hL, hR]
  -- Both sides are now double integrals.  Swap the order on the LHS via Fubini,
  -- using integrability of the product integrand (bounded kernel × `L²` factor).
  have hfg_int : Integrable
      (fun p : Ω × Ω => (conj (K p.1 p.2) * conj ((f : Ω → ℂ) p.2)) * (g : Ω → ℂ) p.1)
      (μ.prod μ) := by
    -- `conj (K x y) * conj (f y)` is `kernel_mul_integrable` for the conjugate kernel,
    -- times the bounded-in-`L¹` factor `g x`; assemble by domination.
    have hKbar : AEStronglyMeasurable (Function.uncurry fun x y => conj (K x y)) (μ.prod μ) :=
      hKmeas.star
    have hf : AEStronglyMeasurable (fun y => conj ((f : Ω → ℂ) y)) μ :=
      (Lp.memLp f).1.star
    have hg : AEStronglyMeasurable (fun x => (g : Ω → ℂ) x) μ := (Lp.memLp g).1
    have hmeas : AEStronglyMeasurable
        (fun p : Ω × Ω => (conj (K p.1 p.2) * conj ((f : Ω → ℂ) p.2)) * (g : Ω → ℂ) p.1)
        (μ.prod μ) :=
      ((hKbar.mul (hf.comp_snd)).mul (hg.comp_fst))
    -- `f`, `g` integrable on the finite measure space.
    have hf1 : Integrable (fun y => ‖(f : Ω → ℂ) y‖) μ :=
      ((Lp.memLp f).integrable (by norm_num)).norm
    have hg1 : Integrable (fun x => ‖(g : Ω → ℂ) x‖) μ :=
      ((Lp.memLp g).integrable (by norm_num)).norm
    -- dominating function `(D * ‖g x‖) * ‖f y‖`, integrable on the product
    -- (`Integrable.mul_prod`: a function of `x` times a function of `y`).
    have hdom : Integrable
        (fun p : Ω × Ω => (D * ‖(g : Ω → ℂ) p.1‖) * ‖(f : Ω → ℂ) p.2‖) (μ.prod μ) :=
      (hg1.const_mul D).mul_prod hf1
    refine hdom.mono' hmeas ?_
    filter_upwards [hbdd] with p hp
    have hKp : ‖K p.1 p.2‖ ≤ D := hp
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    have h1 : ‖K p.1 p.2‖ * ‖(f : Ω → ℂ) p.2‖ ≤ D * ‖(f : Ω → ℂ) p.2‖ :=
      mul_le_mul_of_nonneg_right hKp (norm_nonneg _)
    calc ‖K p.1 p.2‖ * ‖(f : Ω → ℂ) p.2‖ * ‖(g : Ω → ℂ) p.1‖
        ≤ (D * ‖(f : Ω → ℂ) p.2‖) * ‖(g : Ω → ℂ) p.1‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (D * ‖(g : Ω → ℂ) p.1‖) * ‖(f : Ω → ℂ) p.2‖ := by ring
  -- Swap the LHS double integral.
  conv_lhs => rw [integral_integral_swap hfg_int]
  -- Now both are `∫ y, ∫ x, ...`.  Match the integrands pointwise using `herm`.
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  -- LHS integrand: `conj (K x y) * conj (f y) * g x`.
  -- RHS integrand (outer `y`, inner `x`): `conj (f y) * (K y x * g x)`.
  -- `herm x y : K y x = conj (K x y)` flips `K`; then `ring`.
  dsimp only
  rw [herm x y, ← starRingEnd_apply]
  ring

/-! ## Spectral / compactness facts (statements, upstream-ready)

These are the theorems one wants downstream.  Real spectrum follows from
self-adjointness once `kernelIntegralCLM_isSelfAdjoint` is closed; compactness
holds when `K ∈ L²(μ ⊗ μ)` (genuine Hilbert–Schmidt).  Stated cleanly; deep
proofs honestly `sorry`d. -/

/-- **Real spectrum** of a Hermitian-kernel operator: the spectrum is real.

Now **genuine**.  With `μ` finite and `K` bounded/jointly measurable, the kernel
operator is self-adjoint (`kernelIntegralCLM_isSelfAdjoint`), and `L²(μ)` is a
complex Hilbert space, so `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` is a C⋆-algebra
(`Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`).  A self-adjoint element of
a complex C⋆-algebra has real spectrum
(`IsSelfAdjoint.im_eq_zero_of_mem_spectrum`). -/
theorem kernelIntegralCLM_spectrum_real [IsFiniteMeasure μ] {D : ℝ}
    (hKmeas : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ D)
    (herm : ∀ x y, K y x = star (K x y)) (z : ℂ)
    (hz : z ∈ spectrum ℂ (kernelIntegralCLM K C hC hmem hadd hsmul hSchur)) :
    z.im = 0 :=
  (kernelIntegralCLM_isSelfAdjoint K C hC hmem hadd hsmul hSchur
    hKmeas hbdd herm).im_eq_zero_of_mem_spectrum hz

/-- **Hilbert–Schmidt operator-norm bound — fully genuine (no `sorry`).**

`‖T_K‖ ≤ ‖K‖_{L²(μ⊗μ)}`: the operator norm of the kernel integral operator is
dominated by the *Hilbert–Schmidt* norm of the kernel (its `L²` norm on the
product).  This is the bound that drives the finite-rank truncation: it shows
`K ↦ T_K` is `1`-Lipschitz from `L²(μ⊗μ)` into the operators, so an `L²`-convergent
sequence of kernels yields an operator-norm-convergent sequence of operators.

Genuine, from `kernelIntegralFun_eLpNorm_le_hs` via `opNorm_le_bound`. -/
theorem kernelIntegralCLM_opNorm_le_hs [SFinite μ]
    (hKmeas : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hHSfin : eLpNorm (Function.uncurry K) 2 (μ.prod μ) ≠ ∞) :
    ‖kernelIntegralCLM K C hC hmem hadd hsmul hSchur‖
      ≤ (eLpNorm (Function.uncurry K) 2 (μ.prod μ)).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [kernelIntegralCLM_apply, Lp.norm_toLp]
  have hle := kernelIntegralFun_eLpNorm_le_hs K (f : Ω → ℂ) hKmeas (Lp.memLp f).1
  have hmemfin : eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ ≠ ∞ := (hmem f).2.ne
  calc (eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ).toReal
      ≤ (eLpNorm (Function.uncurry K) 2 (μ.prod μ) * eLpNorm (f : Ω → ℂ) 2 μ).toReal :=
        ENNReal.toReal_mono (by finiteness) hle
    _ = (eLpNorm (Function.uncurry K) 2 (μ.prod μ)).toReal * ‖f‖ := by
        rw [ENNReal.toReal_mul,
          show (eLpNorm (f : Ω → ℂ) 2 μ).toReal = ‖f‖ from (Lp.norm_def f).symm]

/-- **Compactness from a finite-rank operator-norm approximation — fully genuine
(no `sorry`).**  If the bounded kernel integral operator `T_K` is the operator-norm
limit of a sequence `T` of operators each of which has finite-dimensional range,
then `T_K` is a compact operator.

This is the axiom-clean core of `kernelIntegralCLM_isCompactOperator`: each `T n` is
compact (`isCompactOperator_of_finiteDimensional_range`), and the set of compact
operators is closed under operator-norm limits (`isCompactOperator_of_tendsto`).
The Hilbert–Schmidt hypothesis enters only through the *existence* of such an
approximation (`exists_finiteRank_tendsto_kernelIntegralCLM`). -/
theorem kernelIntegralCLM_isCompactOperator_of_finiteRank_approx
    (T : ℕ → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
    (hFR : ∀ n, FiniteDimensional ℂ (LinearMap.range (T n : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ)))
    (hlim : Filter.Tendsto T Filter.atTop
      (nhds (kernelIntegralCLM K C hC hmem hadd hsmul hSchur))) :
    IsCompactOperator (kernelIntegralCLM K C hC hmem hadd hsmul hSchur) := by
  refine isCompactOperator_of_tendsto hlim ?_
  filter_upwards with n
  exact isCompactOperator_of_finiteDimensional_range (T n) (hFR n)

/-- **Finite-rank truncation of a Hilbert–Schmidt kernel operator** (the single
cited classical input).  When the kernel `K` is square-integrable on `μ ⊗ μ`, the
bounded operator `T_K` is the **operator-norm limit of finite-rank operators**.

This is the one genuinely classical analytic fact that is *not yet in Mathlib*:
finite-rank operators are operator-norm dense in the Hilbert–Schmidt class.  The
standard proof truncates the kernel onto a finite section of an `L²(μ)`-orthonormal
basis — `K_n := Σ_{i,j≤n} ⟪e_i⊗e_j, K⟫ e_i⊗e_j` — whose operator
`T_{K_n} = Σ_{i,j≤n} ⟪e_i⊗e_j, K⟫ ⟪e_j, ·⟫ e_i` has rank `≤ (n+1)²`, and whose
kernel converges to `K` in `L²(μ⊗μ)` by Parseval (`{e_i⊗e_j}` is an orthonormal
basis of `L²(μ⊗μ)`); the **Hilbert–Schmidt dominance**
`‖T_K - T_{K_n}‖ = ‖T_{K-K_n}‖ ≤ ‖K - K_n‖_{L²(μ⊗μ)} → 0`
(proved here as `kernelIntegralFun_eLpNorm_le_hs`) upgrades the `L²`-kernel
convergence to operator-norm convergence.

Reference: Conway, *A Course in Functional Analysis*, 2nd ed., Prop. II.4.6 and
the discussion of Hilbert–Schmidt operators; Reed–Simon, *Methods of Modern
Mathematical Physics I*, Thm. VI.22–23.  The *statement* is true and non-vacuous;
only the basis/Parseval bookkeeping (a substantial standalone Mathlib development)
is deferred.  Everything downstream of it — that the limit is compact — is proved
genuinely below in `kernelIntegralCLM_isCompactOperator`. -/
theorem exists_finiteRank_tendsto_kernelIntegralCLM
    (hHS : MemLp (Function.uncurry K) 2 (μ.prod μ)) :
    ∃ T : ℕ → (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ),
      (∀ n, FiniteDimensional ℂ (LinearMap.range (T n : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ))) ∧
      Filter.Tendsto T Filter.atTop (nhds (kernelIntegralCLM K C hC hmem hadd hsmul hSchur)) := by
  sorry

/-- **Compactness (Hilbert–Schmidt).**  When the kernel `K` is square-integrable on
`μ ⊗ μ` (genuine Hilbert–Schmidt class), the bounded kernel integral operator `T_K`
is a compact operator.

**Now genuine modulo one cited classical fact.**  By
`exists_finiteRank_tendsto_kernelIntegralCLM`, `T_K` is the operator-norm limit of a
sequence of **finite-rank** operators `T n`; each `T n` is compact
(`isCompactOperator_of_finiteDimensional_range`); and the set of compact operators is
closed under operator-norm limits (`isCompactOperator_of_tendsto`,
`isClosed_setOf_isCompactOperator`).  Hence `T_K` is compact.

The genuinely quantitative engine that makes the truncation converge — the
Hilbert–Schmidt dominance `‖T_K f‖₂ ≤ ‖K‖_{L²(μ⊗μ)} · ‖f‖₂` — is proved in full as
`kernelIntegralFun_eLpNorm_le_hs`.  The only deferred ingredient is the classical
density of finite-rank operators in the Hilbert–Schmidt class (the
basis/Parseval bookkeeping), isolated in
`exists_finiteRank_tendsto_kernelIntegralCLM`. -/
theorem kernelIntegralCLM_isCompactOperator (hHS : MemLp (Function.uncurry K) 2 (μ.prod μ)) :
    IsCompactOperator (kernelIntegralCLM K C hC hmem hadd hsmul hSchur) := by
  obtain ⟨T, hFR, hlim⟩ :=
    exists_finiteRank_tendsto_kernelIntegralCLM K C hC hmem hadd hsmul hSchur hHS
  exact kernelIntegralCLM_isCompactOperator_of_finiteRank_approx
    K C hC hmem hadd hsmul hSchur T hFR hlim

end Bundled

end Graphplay.ForMathlib
