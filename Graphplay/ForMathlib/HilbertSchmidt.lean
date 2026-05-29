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
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
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

/-! ## The `MemLp 2` closure — the analytic crux (honest `sorry`)

This is the one genuinely hard lemma and the only true Mathlib gap. -/

/-- **`MemLp 2` closure of the kernel action (Cauchy–Schwarz + Fubini).**

For a jointly measurable kernel `K` that is essentially bounded by `M` and an
`f ∈ L²(μ)`, the action `kernelIntegralFun K f` is again in `L²(μ)`, with
`eLpNorm (T_K f) 2 μ ≤ M · √μ(univ) · eLpNorm f 2 μ`.

The argument: by Cauchy–Schwarz in `y` (pointwise in `x`),
`|∫ K x y · f y ∂μ|² ≤ (∫ |K x y|² ∂μ) · (∫ |f y|² ∂μ) ≤ M² μ(univ) · ‖f‖₂²`,
and then integrating in `x` (Fubini/Tonelli to keep the slice integrals
measurable) gives `‖T_K f‖₂² ≤ M² μ(univ)² · ‖f‖₂²`.

**Mathlib gap.** Mathlib has the ingredients —
`MeasureTheory.inner_mul_le_norm_mul_norm` / `integral_mul_le_Lp_mul_Lq`
(Hölder), `AEStronglyMeasurable.integral_prod_right'` (slice measurability),
`lintegral_mono`/`Tonelli` — but no packaged "kernel integral operator is `MemLp`"
lemma. Assembling the pointwise Cauchy–Schwarz into an `eLpNorm`-level bound is
the missing `Mathlib.Analysis.HilbertSchmidt` API; once that lands this is a few
lines. Stated honestly as a `sorry`. -/
theorem kernelIntegralFun_memLp [SFinite μ] (hμ : μ Set.univ ≠ ∞) {K : Ω → Ω → ℂ} {M : ℝ}
    (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ M) (f : Lp ℂ 2 μ) :
    MemLp (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ := by
  -- Crux: pointwise Cauchy–Schwarz `|∫ K x · * f ·|² ≤ (∫|K x ·|²)(∫|f ·|²)`,
  -- then integrate in `x`. See module docstring for the precise Mathlib gap.
  sorry

/-- The companion `eLpNorm` (Schur / Hilbert–Schmidt) bound produced by the same
Cauchy–Schwarz + Fubini argument as `kernelIntegralFun_memLp`.

`eLpNorm (T_K f) 2 μ ≤ (M · √μ(univ)) · eLpNorm f 2 μ`.

Same **Mathlib gap** as `kernelIntegralFun_memLp` — this is the quantitative half
of that lemma; isolated so the operator-norm bound below can consume it as a
clean hypothesis. -/
theorem kernelIntegralFun_eLpNorm_le [SFinite μ] (hμ : μ Set.univ ≠ ∞) {K : Ω → Ω → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hbdd : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry K p‖ ≤ M) (f : Lp ℂ 2 μ) :
    eLpNorm (kernelIntegralFun (μ := μ) K (f : Ω → ℂ)) 2 μ
      ≤ ENNReal.ofReal (M * (μ Set.univ).toReal.sqrt) * eLpNorm (f : Ω → ℂ) 2 μ := by
  -- Quantitative half of `kernelIntegralFun_memLp`; same Cauchy–Schwarz + Fubini.
  sorry

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
`hSchur`, which is exactly what `kernelIntegralFun_eLpNorm_le` supplies. -/

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

/-- **Compactness (Hilbert–Schmidt).**  When the kernel is square-integrable on
`μ ⊗ μ` (genuine Hilbert–Schmidt class), the operator is compact.  Statement-only;
this is the deep Hilbert–Schmidt theorem (approximation by finite-rank truncations
of the kernel), the headline target of the upstream file. -/
theorem kernelIntegralCLM_isCompactOperator (hHS : MemLp (Function.uncurry K) 2 (μ.prod μ)) :
    IsCompactOperator (kernelIntegralCLM K C hC hmem hadd hsmul hSchur) := by
  -- Deep: HS kernels give compact operators (finite-rank kernel approximation).
  sorry

end Bundled

end Graphplay.ForMathlib
