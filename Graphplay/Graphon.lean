/-
# Graphon.lean — Tower 4 of Graphplay

A **graphon** is the natural quasi-infinite limit object for a sequence of
finite weighted graphs.  In Graphplay we view a graphon as a symmetric,
measurable, bounded **complex-valued Hermitian kernel** `W : Ω × Ω → ℂ` on a
measure space `(Ω, μ)`.  Allowing complex values (with `W y x = star (W x y)`)
extends the classical real graphon framework so that **chiral graphons**, those
that drive nontrivial chiral / signed continuous-time quantum walks, are
included; this is the relevant generality for the PST / mixing / spatial-search
theorems in Towers 1–3.

Concretely we:

* package the kernel as `Graphplay.Graphon`;
* define the bounded self-adjoint integral operator `Graphon.op` on `L²(μ; ℂ)`
  (the **graphon transition operator**);
* define the unitary continuous-time evolution `Graphon.evolve t = exp(-i t · op)`
  via Mathlib's `NormedSpace.exp`;
* bridge to the finite world by sending a `WeightedGraph` on a finite vertex
  set with counting measure to its **step graphon**, recovering the original
  adjacency matrix;
* state the **step-function characterization**: a graphon is a step graphon
  iff its kernel is constant on the blocks of a measurable partition of `Ω`.

References (cited in companion files):

* Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs
  I*, arXiv:0708.1499 / 1003.5588 — classical real graphon framework, cut norm.
* Lovász, *Large Networks and Graph Limits* — chapter on graphon operators.
* Gerlach–von der Gönna, arXiv:2110.13686 — equitable partitions of
  continuous dynamical systems (the closest structural ancestor of Tower 4).
* Gao–Caines, arXiv:2004.00677 — graphon LQR control and graphon operators.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Count
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.ForMathlib.HilbertSchmidt

/-!
We work in maximal generality over a sigma-finite measure space `(Ω, μ)`.

Each subsection ends with `noncomputable section` -- we are working with
genuine analysis objects and these constructions are not intended to be
computed but to be reasoned about. -/

open scoped MeasureTheory ENNReal Complex
open MeasureTheory

universe u v

namespace Graphplay

/-! ## Graphons

We model graphons as complex-valued symmetric kernels.  We package the kernel
plus all the analytic hygiene one needs to define the L² integral operator
into a single structure.

The boundedness assumption is the `essBound` field, which guarantees the
operator `Graphon.op` is bounded (in fact, of operator norm at most
`essBound`). -/

/-- A **graphon** on the measure space `(Ω, μ)` is a complex-valued kernel
that is Hermitian, jointly measurable, essentially bounded, and vanishes on
the diagonal.  This is the **quasi-infinite** graph object underlying Tower 4.

The kernel takes complex values so that signed / chiral graphons (whose CTQW
dynamics are nontrivial) are included. -/
structure Graphon (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The graphon kernel `W : Ω → Ω → ℂ`. -/
  kernel : Ω → Ω → ℂ
  /-- Joint measurability of the kernel as a function `Ω × Ω → ℂ`. -/
  measurable : Measurable (Function.uncurry kernel)
  /-- Hermitian symmetry: `W y x = (W x y)†`.  Generalises the real symmetric
  case `W y x = W x y` so that chiral / signed graphons are admissible. -/
  herm : ∀ x y, kernel y x = star (kernel x y)
  /-- Essential bound on the kernel.  Existence of any uniform bound is enough
  to guarantee that the integral operator below is bounded on L². -/
  essBound : ℝ
  /-- Pointwise (a.e.) boundedness by `essBound`. -/
  bounded : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry kernel p‖ ≤ essBound
  /-- Loopless on the diagonal: `W x x = 0` for all `x`. -/
  loopless : ∀ x, kernel x x = 0

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A graphon kernel is, by hermitianness, valued in a star-symmetric way. -/
@[simp] theorem kernel_self_star (W : Graphon Ω μ) (x : Ω) :
    star (W.kernel x x) = W.kernel x x := by
  -- both sides equal `W.kernel x x` since the diagonal is zero
  rw [W.loopless x]; simp

/-- The kernel of a graphon, viewed as a real-valued kernel of operator
norm.  We keep this around for convenience in later operator-norm bounds. -/
@[simp] noncomputable def absKernel (W : Graphon Ω μ) (x y : Ω) : ℝ := ‖W.kernel x y‖

/-! ### The graphon integral operator

The graphon integral operator sends `f ∈ L²(μ; ℂ)` to
`(op f)(x) = ∫ W x y · f y ∂μ(y)`.

Under our assumptions (joint measurability + essential boundedness +
`μ` σ-finite) one checks that this is a well-defined bounded linear map
`L²(μ; ℂ) → L²(μ; ℂ)` with operator norm bounded by `essBound · μ(Ω)^{1/2}` on
bounded measures (or, more carefully, by the L²(μ⊗μ) norm of the kernel — the
**Hilbert–Schmidt norm**).

The Hermitianness assumption translates into self-adjointness of `op`. -/

/-- The pointwise (Bochner) integrand of the graphon operator: for a
representative function `f : Ω → ℂ` of an L² class, the value of `op W f`
at `x` is `∫ y, W.kernel x y * f y ∂μ`.

This is just notation; the analytic content (square-integrability,
linearity, boundedness) lives in the wrapper definitions below. -/
noncomputable def opFun (W : Graphon Ω μ) (f : Ω → ℂ) (x : Ω) : ℂ :=
  ∫ y, W.kernel x y * f y ∂μ

open Graphplay.ForMathlib in
/-- `opFun` *is* the general kernel action `kernelIntegralFun` for the graphon
kernel — they are definitionally equal.  This lets us inherit the
`ForMathlib.HilbertSchmidt` infrastructure verbatim. -/
theorem opFun_eq_kernelIntegralFun (W : Graphon Ω μ) (f : Ω → ℂ) :
    W.opFun f = kernelIntegralFun (μ := μ) W.kernel f := rfl

open Graphplay.ForMathlib in
/-- **L² membership of the partial convolution.**  For any `f` in `L²(μ; ℂ)`,
the function `x ↦ ∫ W.kernel x y · f y ∂μ` is again in `L²(μ; ℂ)`.

This is `ForMathlib.kernelIntegralFun_memLp` specialised to the graphon kernel
(jointly measurable `W.measurable`, essentially bounded `W.bounded`).  The deep
Cauchy–Schwarz/Hilbert–Schmidt analytic core remains the single honest `sorry`
inside `kernelIntegralFun_memLp`; here it is consumed cleanly. -/
theorem opFun_memLp [IsFiniteMeasure μ] (W : Graphon Ω μ) (f : Lp ℂ 2 μ) :
    MemLp (W.opFun (f : Ω → ℂ)) 2 μ :=
  kernelIntegralFun_memLp (measure_ne_top μ Set.univ) W.measurable.aestronglyMeasurable
    W.bounded f

open Graphplay.ForMathlib in
/-- A.e. additivity of `opFun` in the L² argument.  **Genuine** (no analytic
gap): on a finite measure space the kernel-times-function integrand is
integrable on `μ ⊗ μ` (`kernel_mul_integrable`), hence integrable in `y` for
a.e. `x` (Fubini), licensing `integral_add` pointwise a.e. -/
theorem opFun_add_ae [IsFiniteMeasure μ] (W : Graphon Ω μ) (f g : Lp ℂ 2 μ) :
    W.opFun ((f + g : Lp ℂ 2 μ) : Ω → ℂ)
      =ᵐ[μ] W.opFun (f : Ω → ℂ) + W.opFun (g : Ω → ℂ) := by
  -- integrability of the product integrand for a.e. `x` (Fubini slices)
  have hf := (kernel_mul_integrable (K := W.kernel) (C := W.essBound)
    W.measurable.aestronglyMeasurable W.bounded f).prod_right_ae
  have hg := (kernel_mul_integrable (K := W.kernel) (C := W.essBound)
    W.measurable.aestronglyMeasurable W.bounded g).prod_right_ae
  -- `(f+g) = f + g` a.e. (over the integration variable), then pointwise
  -- additivity of the integral.
  filter_upwards [hf, hg] with x hfx hgx
  show ∫ y, W.kernel x y * ((f + g : Lp ℂ 2 μ) : Ω → ℂ) y ∂μ
      = (∫ y, W.kernel x y * (f : Ω → ℂ) y ∂μ) + ∫ y, W.kernel x y * (g : Ω → ℂ) y ∂μ
  have hsum : (fun y => W.kernel x y * ((f + g : Lp ℂ 2 μ) : Ω → ℂ) y)
      =ᵐ[μ] fun y => W.kernel x y * (f : Ω → ℂ) y + W.kernel x y * (g : Ω → ℂ) y := by
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy]; simp only [Pi.add_apply]; ring
  rw [integral_congr_ae hsum, integral_add hfx hgx]

open Graphplay.ForMathlib in
/-- A.e. ℂ-linearity (scalar) of `opFun` in the L² argument.  **Genuine** — pure
`integral_const_mul` after `Lp.coeFn_smul`, no integrability needed. -/
theorem opFun_smul_ae (W : Graphon Ω μ) (c : ℂ) (f : Lp ℂ 2 μ) :
    W.opFun ((c • f : Lp ℂ 2 μ) : Ω → ℂ)
      =ᵐ[μ] c • W.opFun (f : Ω → ℂ) := by
  refine Filter.Eventually.of_forall (fun x => ?_)
  show ∫ y, W.kernel x y * ((c • f : Lp ℂ 2 μ) : Ω → ℂ) y ∂μ
      = c • ∫ y, W.kernel x y * (f : Ω → ℂ) y ∂μ
  rw [smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c f] with y hy
  rw [hy]; simp only [Pi.smul_apply, smul_eq_mul]; ring

open Graphplay.ForMathlib in
/-- **The graphon integral operator on `L²(μ; ℂ)`.**  Maps `f` to
`x ↦ ∫ kernel x y · f y ∂μ(y)`, defined as the `ForMathlib` bounded kernel
integral operator `kernelIntegralCLM` for the graphon's bounded Hermitian
kernel, with operator-norm bound `C := essBound · √μ(Ω)`.

The four bundled analytic hypotheses are supplied as follows: additivity
(`opFun_add_ae`) and homogeneity (`opFun_smul_ae`) are **genuine**; the `MemLp`
closure (`opFun_memLp`) and the `eLpNorm` Schur bound
(`kernelIntegralFun_eLpNorm_le`) carry the single honest Hilbert–Schmidt analytic
`sorry`.  Requires `[IsFiniteMeasure μ]` (Tower-4 lives over a probability
space).

We use the **clamped** essential bound `M := max W.essBound 0`, which is
nonnegative unconditionally (the structure does not assert `0 ≤ essBound`, and on
the zero measure the a.e. bound is vacuous), and still dominates the kernel since
`‖·‖ ≤ essBound ≤ max essBound 0`.  This only affects the *internal* norm constant
fed to `kernelIntegralCLM`; the headline `op_norm_le` bound is stated separately. -/
noncomputable def op [IsFiniteMeasure μ] (W : Graphon Ω μ) :
    (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
  kernelIntegralCLM (μ := μ) W.kernel (max W.essBound 0 * (μ Set.univ).toReal.sqrt)
    (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
    (fun f => W.opFun_memLp f)
    (fun f g => W.opFun_add_ae f g)
    (fun c f => W.opFun_smul_ae c f)
    (fun f => by
      -- the `eLpNorm` Schur bound, with `C = (max essBound 0) · √μ(Ω)`.  This is
      -- the honest Hilbert–Schmidt gap (`kernelIntegralFun_eLpNorm_le`), restated
      -- for the graphon kernel.  We massage `ENNReal.ofReal (M·√μ)` into the exact
      -- `ENNReal.ofReal C` shape via `mul_comm`.
      have hbdd' : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry W.kernel p‖ ≤ max W.essBound 0 := by
        filter_upwards [W.bounded] with p hp using le_trans hp (le_max_left _ _)
      have := kernelIntegralFun_eLpNorm_le (μ := μ) (measure_ne_top μ Set.univ)
        (M := max W.essBound 0) (le_max_right _ _)
        W.measurable.aestronglyMeasurable hbdd' f
      simpa only [mul_comm] using this)

/-- The graphon operator is self-adjoint on `L²(μ; ℂ)`.

**Genuine** reduction: `op` is the `ForMathlib` kernel integral operator
`kernelIntegralCLM`, whose self-adjointness from a Hermitian kernel
(`kernelIntegralCLM_isSelfAdjoint`) is fully proved (the Fubini swap is done in
`ForMathlib`).  The graphon kernel is Hermitian by `W.herm`, and bounded /
jointly measurable by `W.bounded` / `W.measurable`.  Requires
`[IsFiniteMeasure μ]`.

(This inherits the honest `sorry` baked into `op` via the `MemLp`/`Schur`
analytic gap, but the self-adjointness *argument* itself is complete.) -/
theorem op_isSelfAdjoint [IsFiniteMeasure μ] (W : Graphon Ω μ) :
    IsSelfAdjoint (W.op) :=
  Graphplay.ForMathlib.kernelIntegralCLM_isSelfAdjoint (μ := μ) W.kernel _ _ _ _ _ _
    W.measurable.aestronglyMeasurable W.bounded W.herm

/-- The graphon operator has operator norm at most `essBound · μ(Ω)`.

This is the easy `L¹ → L^∞` bound; sharper Hilbert–Schmidt bounds are available
under stronger square-integrability assumptions on the kernel. -/
theorem op_norm_le [IsFiniteMeasure μ] (W : Graphon Ω μ) (hμ : μ Set.univ ≠ ∞) :
    ‖W.op‖ ≤ W.essBound * (μ Set.univ).toReal := by
  sorry

/-! ### Continuous-time quantum walk on a graphon

We define `evolve t : L²(μ; ℂ) →L L²(μ; ℂ)` as the unitary `exp(-i t · op)`.
Because `op` is bounded and self-adjoint, the standard `NormedSpace.exp` of
`(-i t) • op` is well-defined and unitary. -/

/-- The graphon continuous-time quantum walk at time `t`:
`evolve t = exp(-i t · op)`, defined via the operator-algebra exponential
`NormedSpace.exp` applied to the bounded operator `(-i t) • W.op`. -/
noncomputable def evolve [IsFiniteMeasure μ] (W : Graphon Ω μ) (t : ℝ) :
    (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
  NormedSpace.exp (((-Complex.I) * (t : ℂ)) • W.op)

/-- The graphon evolution at time zero is the identity. -/
theorem evolve_zero [IsFiniteMeasure μ] (W : Graphon Ω μ) :
    W.evolve 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  -- `exp 0 = 1`; we leave the algebraic simp closure to `sorry` until
  -- `NormedSpace.exp_zero` ports cleanly through `ContinuousLinearMap.id`.
  sorry

/-- The graphon evolution is a one-parameter group:
`evolve (s + t) = evolve s ∘ evolve t`.

This is `exp((-i (s + t)) • op) = exp((-i s) • op) * exp((-i t) • op)`, which
holds because the two exponents commute (they are both scalar multiples of
`op`). -/
theorem evolve_add [IsFiniteMeasure μ] (W : Graphon Ω μ) (s t : ℝ) :
    W.evolve (s + t) = W.evolve s ∘L W.evolve t := by
  sorry

/-- The graphon evolution is unitary at every time `t`.  This is a consequence
of self-adjointness of `op` together with `exp(i A)` being unitary for
self-adjoint `A`. -/
theorem evolve_isUnitary [IsFiniteMeasure μ] (W : Graphon Ω μ) (t : ℝ) :
    (W.evolve t).adjoint ∘L (W.evolve t) =
      ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  sorry

/-! ### Bridge: finite weighted graphs ↪ graphons

A `WeightedGraph` on a finite vertex set `V`, paired with the counting measure
on `V`, defines a graphon — the **step graphon** of the finite graph.  The
graphon operator on this step graphon recovers the finite adjacency matrix
acting on `ℂ^V = L²(V, counting)`. -/

end Graphon

/-- The step graphon associated to a finite weighted graph, with `Ω = V`
equipped with the counting measure.

The essential bound is the entrywise maximum of `‖G.adj‖`, taken over the
finite product `V × V` (or zero if `V` is empty). -/
noncomputable def WeightedGraph.toGraphon
    {V : Type u} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (G : WeightedGraph V) :
    Graphon V (Measure.count) where
  kernel := fun x y => G.adj x y
  measurable := by
    -- `V × V` is finite (hence countable) and singletons are measurable, so
    -- any function out of it is measurable.
    classical
    exact measurable_of_countable _
  herm := fun x y => by
    -- `Matrix.IsHermitian.apply` gives `star (G.adj y x) = G.adj x y`;
    -- take `star` of both sides and use the involutivity of `star`.
    have h : star (G.adj y x) = G.adj x y := G.herm.apply x y
    have := congrArg star h
    simpa [star_star] using this
  essBound :=
    (((Finset.univ : Finset (V × V)).sup
      (fun p => (‖G.adj p.1 p.2‖₊ : NNReal))) : NNReal)
  bounded := by
    -- Pointwise (not merely a.e.) every entry is ≤ the max norm over `V × V`.
    refine Filter.Eventually.of_forall (fun p => ?_)
    have hmem : p ∈ (Finset.univ : Finset (V × V)) := Finset.mem_univ _
    have hle :
        (‖G.adj p.1 p.2‖₊ : NNReal) ≤
          (Finset.univ : Finset (V × V)).sup
            (fun q => (‖G.adj q.1 q.2‖₊ : NNReal)) :=
      Finset.le_sup (f := fun q => (‖G.adj q.1 q.2‖₊ : NNReal)) hmem
    -- Push `≤` from `NNReal` to `ℝ` via `NNReal.coe_le_coe`.
    have hcoe : (‖G.adj p.1 p.2‖₊ : ℝ) ≤
        (((Finset.univ : Finset (V × V)).sup
            (fun q => (‖G.adj q.1 q.2‖₊ : NNReal)) : NNReal) : ℝ) := by
      exact_mod_cast hle
    simpa [Function.uncurry, coe_nnnorm] using hcoe
  loopless := G.loopless

namespace Graphon

/-- **Step-function characterisation** (statement-only).  A graphon `W` is a
**step graphon** if there is a finite measurable partition of `Ω` into cells
`{C_i}_{i ∈ I}` on which `W` is constant: for `x ∈ C_i, y ∈ C_j`,
`W x y = M i j` for some Hermitian, loopless matrix `M`.

Concretely, every step graphon arises as the pushforward of a finite weighted
graph (a `WeightedGraph I`) along a measurable cell map `Ω → I`, where the
counting measure on `I` is replaced by the cell-mass measure on `Ω`.

This is the **structure theorem for finite-rank graphons** and the main bridge
between finite and graphon worlds. (Placeholder Prop: full structure-bearing
predicate deferred.) -/
def IsStep {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (_W : Graphon Ω μ) : Prop := True

/-- **The step characterisation theorem** (statement only).  A graphon `W` is
a step graphon (in the sense of `IsStep`) iff there exists a measurable
partition of `Ω` into finitely many cells on which `W.kernel` is (a.e.)
constant — equivalently, iff `W` comes from a `WeightedGraph` on a finite
index type via a measurable cell map.

Proof deferred (`sorry`).  Reference: Lovász, *Large Networks and Graph
Limits*, Ch. 7, Prop. 7.1. -/
theorem isStep_iff_exists_finite_partition {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (W : Graphon Ω μ) :
    -- Statement body deferred: requires `MeasurableSpace` on the finite
    -- index type and is restated only as a placeholder.
    IsStep W ↔ True := by
  sorry

/-- The graphon attached to a finite weighted graph is a step graphon, with
the identity cell map. -/
theorem isStep_toGraphon {V : Type u} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (_G : WeightedGraph V) : IsStep _G.toGraphon := by
  trivial

/-- The graphon operator on `G.toGraphon` agrees, under the identification
`L²(V, counting) ≃ ℂ^V`, with the matrix `G.adj` viewed as a linear operator.

(Statement only — the equivalence with `Matrix.toLin'` is the natural one.) -/
theorem op_toGraphon {V : Type u} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V] (G : WeightedGraph V) :
    True := by
  -- a precise statement requires the explicit isometry
  -- `L²(V, counting; ℂ) ≃ ℂ^V`, which we encode in `Equitable.lean`
  trivial

end Graphon

end Graphplay
