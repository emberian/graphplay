/-
# Graphplay.Integrations.EpsDynamics

**Hermitian Duhamel perturbation: dynamics are `|t|·ε`-robust, with no
exponential blowup in time.**

The generic Lipschitz bound for the exponential map on a Banach algebra,
`‖exp x − exp y‖ ≤ ‖x − y‖ · e^{max(‖x‖,‖y‖)}`, degrades exponentially in the
evolution time.  For *quantum* dynamics it is wildly pessimistic: when `H, K`
are Hermitian, both evolutions `e^{-itH}, e^{-itK}` are unitary, and the
Duhamel principle

  `e^{-itH} − e^{-itK} = ∫₀ᵗ e^{-i(t-s)H} (−i)(H−K) e^{-isK} ds`

exhibits the difference as a time-integral of operators each of L²-operator
norm exactly `‖H − K‖` — unitaries on both flanks preserve the norm.  Hence

  `‖e^{-itH} − e^{-itK}‖ ≤ |t| · ‖H − K‖`        (`evolve_perturbation`),

*linear* in time, the textbook stability estimate for quantum simulation
(e.g. Lloyd, *Universal quantum simulators*, Science 273 (1996); Childs et al.,
*Toward the first quantum simulation with quantum speedup*, PNAS 115 (2018),
Lemma 1).  Hermiticity is load-bearing: for the nilpotent pair
`H = [[0,a],[0,0]]`, `K = 0` the difference `e^{-itH} − 1 = -itH` grows like
`|t|·|a|` only by accident of nilpotency; for non-normal `H` with a Jordan
block the true growth is polynomial-to-exponential in `t` and the unitary
flanks are simply absent.

Downstream payoff (`epsEquitable_quotient_dynamics`): if `G` is within `ε` of
a graph `Geq` carrying an equitable partition, then the *exact* quotient
intertwining `evolve_cellInflateVec` for `Geq` transfers to `G` with error
`|t|·ε·‖lift w‖` — every dynamical statement proved through a quotient (PST,
mixing, routing) survives an `ε`-perturbation of the host with a certified
linear-in-time error bar.

All matrix norms in this file are the **L²-operator norm** (the C*-norm of
`Mathlib.Analysis.CStarAlgebra.Matrix`): unitary invariance is false for the
`linfty` matrix norm, so the scoped `Matrix.Norms.L2Operator` instances are
essential, not cosmetic.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Spectral

open scoped Matrix Matrix.Norms.L2Operator
open NormedSpace

universe u v

namespace Graphplay

namespace EpsDynamics

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ### Part 1: the unitary-invariance toolkit for the L² operator norm.

A unitary matrix has operator norm at most `1` (exactly `1` when `V` is
nonempty, but `≤ 1` is what composition bounds need, and it is true even for
`V = ∅`).  Consequently multiplication by a unitary on either side preserves
the L² operator norm, and `U *ᵥ ·` preserves the Euclidean norm of vectors.
-/

/-- The identity matrix has L²-operator norm at most `1` (it is the identity
operator; equality holds iff `V` is nonempty). -/
theorem l2_opNorm_one_le : ‖(1 : Matrix V V ℂ)‖ ≤ 1 := by
  calc ‖(1 : Matrix V V ℂ)‖
      = ‖Matrix.toEuclideanCLM (n := V) (𝕜 := ℂ) 1‖ := Matrix.cstar_norm_def 1
    _ = ‖(1 : EuclideanSpace ℂ V →L[ℂ] EuclideanSpace ℂ V)‖ := by rw [map_one]
    _ ≤ 1 := by rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id_le

/-- A unitary matrix (`Uᴴ U = 1`) has L²-operator norm at most `1`.  This is
the C*-identity `‖U‖² = ‖UᴴU‖ = ‖1‖ ≤ 1`. -/
theorem l2_opNorm_le_one_of_unitary {U : Matrix V V ℂ} (hU : Uᴴ * U = 1) :
    ‖U‖ ≤ 1 := by
  have hsq : ‖U‖ * ‖U‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hU]
    exact l2_opNorm_one_le
  nlinarith [norm_nonneg U]

/-- **Unitary invariance of the Euclidean norm**: `‖U x‖₂ = ‖x‖₂` for unitary
`U`.  Both inequalities come from `‖U‖ ≤ 1` (applied to `U` and to `Uᴴ`,
recovering `x` as `Uᴴ (U x)`). -/
theorem norm_mulVec_of_unitary {U : Matrix V V ℂ} (hU : Uᴴ * U = 1)
    (x : EuclideanSpace ℂ V) :
    ‖(EuclideanSpace.equiv V ℂ).symm (U *ᵥ x)‖ = ‖x‖ := by
  refine le_antisymm ?_ ?_
  · calc ‖(EuclideanSpace.equiv V ℂ).symm (U *ᵥ x)‖
        ≤ ‖U‖ * ‖x‖ := Matrix.l2_opNorm_mulVec U x
      _ ≤ 1 * ‖x‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_le_one_of_unitary hU) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  · have hrec : (EuclideanSpace.equiv V ℂ).symm
        (Uᴴ *ᵥ ((EuclideanSpace.equiv V ℂ).symm (U *ᵥ x))) = x := by
      show (EuclideanSpace.equiv V ℂ).symm (Uᴴ *ᵥ (U *ᵥ x)) = x
      rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
      exact (EuclideanSpace.equiv V ℂ).symm_apply_apply x
    have hUH : ‖Uᴴ‖ ≤ 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]
      exact l2_opNorm_le_one_of_unitary hU
    calc ‖x‖
        = ‖(EuclideanSpace.equiv V ℂ).symm
            (Uᴴ *ᵥ ((EuclideanSpace.equiv V ℂ).symm (U *ᵥ x)))‖ := by rw [hrec]
      _ ≤ ‖Uᴴ‖ * ‖(EuclideanSpace.equiv V ℂ).symm (U *ᵥ x)‖ :=
        Matrix.l2_opNorm_mulVec Uᴴ _
      _ ≤ 1 * ‖(EuclideanSpace.equiv V ℂ).symm (U *ᵥ x)‖ :=
        mul_le_mul_of_nonneg_right hUH (norm_nonneg _)
      _ = ‖(EuclideanSpace.equiv V ℂ).symm (U *ᵥ x)‖ := one_mul _

/-- Left multiplication by a unitary preserves the L²-operator norm. -/
theorem l2_opNorm_unitary_mul {U : Matrix V V ℂ} (hU : Uᴴ * U = 1)
    (M : Matrix V V ℂ) : ‖U * M‖ = ‖M‖ := by
  refine le_antisymm ?_ ?_
  · calc ‖U * M‖ ≤ ‖U‖ * ‖M‖ := Matrix.l2_opNorm_mul U M
      _ ≤ 1 * ‖M‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_le_one_of_unitary hU) (norm_nonneg M)
      _ = ‖M‖ := one_mul _
  · have hM : Uᴴ * (U * M) = M := by rw [← mul_assoc, hU, one_mul]
    have hUH : ‖Uᴴ‖ ≤ 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]; exact l2_opNorm_le_one_of_unitary hU
    calc ‖M‖ = ‖Uᴴ * (U * M)‖ := by rw [hM]
      _ ≤ ‖Uᴴ‖ * ‖U * M‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖U * M‖ := mul_le_mul_of_nonneg_right hUH (norm_nonneg _)
      _ = ‖U * M‖ := one_mul _

/-- Right multiplication by a unitary preserves the L²-operator norm. -/
theorem l2_opNorm_mul_unitary {U : Matrix V V ℂ} (hU : Uᴴ * U = 1)
    (M : Matrix V V ℂ) : ‖M * U‖ = ‖M‖ := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  refine le_antisymm ?_ ?_
  · calc ‖M * U‖ ≤ ‖M‖ * ‖U‖ := Matrix.l2_opNorm_mul M U
      _ ≤ ‖M‖ * 1 :=
        mul_le_mul_of_nonneg_left (l2_opNorm_le_one_of_unitary hU) (norm_nonneg M)
      _ = ‖M‖ := mul_one _
  · have hM : (M * U) * Uᴴ = M := by rw [mul_assoc, hU', mul_one]
    have hUH : ‖Uᴴ‖ ≤ 1 := by
      rw [Matrix.l2_opNorm_conjTranspose]; exact l2_opNorm_le_one_of_unitary hU
    calc ‖M‖ = ‖(M * U) * Uᴴ‖ := by rw [hM]
      _ ≤ ‖M * U‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖M * U‖ * 1 := mul_le_mul_of_nonneg_left hUH (norm_nonneg _)
      _ = ‖M * U‖ := mul_one _

/-! ### Part 2: `exp` of a skew-Hermitian generator is unitary, and the
Duhamel perturbation bound. -/

/-- `exp (z • M)` is unitary whenever `M` is Hermitian and `z` is purely
imaginary (`star z = -z`).  The generator `z • M` is then skew-Hermitian, so
its exponential's adjoint `exp(-z • M)` is its inverse — `exp_conjTranspose`
plus `exp_add_of_commute` on the (commuting) pair `±z • M`. -/
theorem exp_smul_unitary {M : Matrix V V ℂ} (hM : M.IsHermitian)
    {z : ℂ} (hz : star z = -z) :
    (NormedSpace.exp (z • M))ᴴ * NormedSpace.exp (z • M) = 1 := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hM.eq, hz]
  have hcomm : Commute ((-z) • M) (z • M) :=
    ((Commute.refl M).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hcomm]
  have : (-z) • M + z • M = 0 := by rw [← add_smul, neg_add_cancel, zero_smul]
  rw [this, NormedSpace.exp_zero]

/-- The time-dependent scalar `-(i t)` is purely imaginary, packaged for the
two generator phases used in the Duhamel interpolation. -/
private theorem star_I_mul_sub (a b : ℝ) :
    star (Complex.I * a - Complex.I * b) = -(Complex.I * a - Complex.I * b) := by
  simp only [star_sub, star_mul', Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal]
  ring

/-- **Hermitian Duhamel perturbation bound (the keystone).**

For Hermitian `H, K` and any real time `t`,

  `‖exp(-(it) • H) − exp(-(it) • K)‖ ≤ |t| · ‖H − K‖`

in the L²-operator norm.  Proof: the interpolation
`φ(s) = exp(-(i(t−s)) • H) · exp(-(is) • K)` has endpoint values
`φ(0) = e^{-itH}`, `φ(t) = e^{-itK}` and derivative
`φ'(s) = e^{-i(t−s)H} · (i(H−K)) · e^{-isK}`, whose norm is exactly
`‖H − K‖` by unitary invariance of both flanks.  The fundamental theorem of
calculus then bounds the endpoint difference by `|t| · ‖H − K‖` — **no**
`e^{|t|}` factor, unlike the generic Banach-algebra Lipschitz estimate.

Hermiticity of *both* matrices is needed: it makes the flanking exponentials
unitary.  (For a single Jordan block `H`, `‖e^{-itH}‖` itself grows
polynomially and the conclusion fails with any constant.) -/
theorem norm_exp_sub_exp_le_of_isHermitian {H K : Matrix V V ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (t : ℝ) :
    ‖NormedSpace.exp ((-(Complex.I * t)) • H)
        - NormedSpace.exp ((-(Complex.I * t)) • K)‖
      ≤ |t| * ‖H - K‖ := by
  -- The two exponential factors differentiate in `s` (chain rule through the
  -- complex phases `i·s − i·t` and `−i·s`, which have derivatives `i`, `−i`).
  have hf₁ : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => NormedSpace.exp ((Complex.I * u - Complex.I * t) • H))
        (Complex.I • (NormedSpace.exp ((Complex.I * s - Complex.I * t) • H) * H))
        s := by
    intro s
    have hc : HasDerivAt (fun u : ℝ => Complex.I * u - Complex.I * t)
        Complex.I s := by
      simpa using ((hasDerivAt_id s).ofReal_comp.const_mul Complex.I).sub_const
        (Complex.I * (t : ℂ))
    simpa only [Function.comp_def] using
      HasDerivAt.scomp (𝕜 := ℝ) s
        (hasDerivAt_exp_smul_const H ((Complex.I * s - Complex.I * t : ℂ))) hc
  have hf₂ : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => NormedSpace.exp ((-(Complex.I * u)) • K))
        ((-Complex.I) • (K * NormedSpace.exp ((-(Complex.I * s)) • K))) s := by
    intro s
    have hc : HasDerivAt (fun u : ℝ => -(Complex.I * u)) (-Complex.I) s := by
      simpa using ((hasDerivAt_id s).ofReal_comp.const_mul Complex.I).neg
    simpa only [Function.comp_def] using
      HasDerivAt.scomp (𝕜 := ℝ) s
        (hasDerivAt_exp_smul_const' K ((-(Complex.I * s) : ℂ))) hc
  -- The interpolation differentiates to the Duhamel integrand everywhere
  -- (product rule, then regroup the scalars across the product).
  have hderiv : ∀ s : ℝ,
      HasDerivAt
        (fun u : ℝ => NormedSpace.exp ((Complex.I * u - Complex.I * t) • H)
          * NormedSpace.exp ((-(Complex.I * u)) • K))
        (NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
          * (Complex.I • (H - K)) * NormedSpace.exp ((-(Complex.I * s)) • K))
        s := by
    intro s
    have halg : NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
          * (Complex.I • (H - K)) * NormedSpace.exp ((-(Complex.I * s)) • K)
        = Complex.I • (NormedSpace.exp ((Complex.I * s - Complex.I * t) • H) * H)
            * NormedSpace.exp ((-(Complex.I * s)) • K)
          + NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
            * ((-Complex.I) • (K * NormedSpace.exp ((-(Complex.I * s)) • K))) := by
      simp only [mul_assoc, smul_mul_assoc, mul_smul_comm, sub_eq_add_neg, add_mul,
        mul_add, smul_add, neg_mul, mul_neg, smul_neg, neg_smul]
    rw [halg]
    exact (hf₁ s).mul (hf₂ s)
  -- The integrand is continuous (its factors are differentiable), hence
  -- interval-integrable.
  have hcont : Continuous fun s : ℝ =>
      NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
        * (Complex.I • (H - K)) * NormedSpace.exp ((-(Complex.I * s)) • K) := by
    have he₁ : Continuous fun s : ℝ =>
        NormedSpace.exp ((Complex.I * s - Complex.I * t) • H) :=
      continuous_iff_continuousAt.mpr fun s => (hf₁ s).continuousAt
    have he₂ : Continuous fun s : ℝ =>
        NormedSpace.exp ((-(Complex.I * s)) • K) :=
      continuous_iff_continuousAt.mpr fun s => (hf₂ s).continuousAt
    exact (he₁.mul continuous_const).mul he₂
  -- Fundamental theorem of calculus on `[0, t]` (in either order).
  have hkey : (∫ s in (0:ℝ)..t,
        NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
          * (Complex.I • (H - K)) * NormedSpace.exp ((-(Complex.I * s)) • K))
      = (NormedSpace.exp ((Complex.I * t - Complex.I * t) • H)
          * NormedSpace.exp ((-(Complex.I * t)) • K))
        - (NormedSpace.exp ((Complex.I * (0:ℝ) - Complex.I * t) • H)
          * NormedSpace.exp ((-(Complex.I * (0:ℝ))) • K)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hcont.intervalIntegrable 0 t)
  -- The integrand has norm exactly `‖H − K‖`: unitaries flank `i(H−K)`.
  have hbound : ∀ s : ℝ,
      ‖NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
        * (Complex.I • (H - K)) * NormedSpace.exp ((-(Complex.I * s)) • K)‖
      = ‖H - K‖ := by
    intro s
    have hU₁ : (NormedSpace.exp ((Complex.I * s - Complex.I * t) • H))ᴴ
        * NormedSpace.exp ((Complex.I * s - Complex.I * t) • H) = 1 :=
      exp_smul_unitary hH (star_I_mul_sub s t)
    have hU₂ : (NormedSpace.exp ((-(Complex.I * s)) • K))ᴴ
        * NormedSpace.exp ((-(Complex.I * s)) • K) = 1 := by
      refine exp_smul_unitary hK ?_
      have h0 : (-(Complex.I * s) : ℂ) = Complex.I * (0:ℝ) - Complex.I * s := by
        simp
      rw [h0]
      exact star_I_mul_sub 0 s
    calc ‖NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
          * (Complex.I • (H - K)) * NormedSpace.exp ((-(Complex.I * s)) • K)‖
        = ‖NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
            * (Complex.I • (H - K))‖ := l2_opNorm_mul_unitary hU₂ _
      _ = ‖Complex.I • (H - K)‖ := l2_opNorm_unitary_mul hU₁ _
      _ = ‖H - K‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  -- Endpoint values of the interpolation.
  have hφt : NormedSpace.exp ((Complex.I * t - Complex.I * t) • H)
        * NormedSpace.exp ((-(Complex.I * t)) • K)
      = NormedSpace.exp ((-(Complex.I * t)) • K) := by
    rw [sub_self, zero_smul, NormedSpace.exp_zero, one_mul]
  have hφ0 : NormedSpace.exp ((Complex.I * (0:ℝ) - Complex.I * t) • H)
        * NormedSpace.exp ((-(Complex.I * (0:ℝ))) • K)
      = NormedSpace.exp ((-(Complex.I * t)) • H) := by
    rw [Complex.ofReal_zero, mul_zero, zero_sub, neg_zero, zero_smul,
      NormedSpace.exp_zero, mul_one]
  rw [hφt, hφ0] at hkey
  -- Assemble.
  calc ‖NormedSpace.exp ((-(Complex.I * t)) • H)
        - NormedSpace.exp ((-(Complex.I * t)) • K)‖
      = ‖NormedSpace.exp ((-(Complex.I * t)) • K)
          - NormedSpace.exp ((-(Complex.I * t)) • H)‖ := norm_sub_rev _ _
    _ = ‖∫ s in (0:ℝ)..t,
          NormedSpace.exp ((Complex.I * s - Complex.I * t) • H)
            * (Complex.I • (H - K))
            * NormedSpace.exp ((-(Complex.I * s)) • K)‖ := by rw [hkey]
    _ ≤ ‖H - K‖ * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => (hbound s).le
    _ = |t| * ‖H - K‖ := by rw [sub_zero, mul_comm]

/-- **`ε`-robustness of the quantum walk** (`evolve` form of the Duhamel
bound): two weighted graphs whose adjacency matrices are `ε`-close in
L²-operator norm have evolutions that stay `|t|·ε`-close for all time. -/
theorem evolve_perturbation (G G' : WeightedGraph V) (t : ℝ) :
    ‖G.evolve t - G'.evolve t‖ ≤ |t| * ‖G.adj - G'.adj‖ :=
  norm_exp_sub_exp_le_of_isHermitian G.herm G'.herm t

/-! ### Part 3: `ε`-equitable quotient dynamics.

If `G` is `ε`-close to a graph `Geq` carrying an equitable partition `P`,
then evolving a lifted quotient state under `G` and lifting the
quotient-evolved state differ by at most `|t|·ε·‖lift‖`: the exact
intertwining `evolve_cellInflateVec` for `Geq` plus one Duhamel leg.
-/

variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The exact quotient intertwining of `Spectral.evolve_cellInflateVec`,
restated through `WeightedGraph.evolve` (the two generator phases
`-(i·t)` and `(-t)·i` differ only by `ring`). -/
theorem evolve_mulVec_cellInflateVec (Geq : WeightedGraph V)
    (P : EquitablePartition Geq I) (w : I → ℂ) (t : ℝ) :
    (Geq.evolve t) *ᵥ P.cellInflateVec w
      = P.cellInflateVec
          ((NormedSpace.exp ((-(t : ℂ) * Complex.I) • P.symmQuotient)) *ᵥ w) := by
  have hsc : (-(Complex.I * (t : ℂ))) = (-(t : ℂ) * Complex.I) := by ring
  show (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • Geq.adj)) *ᵥ P.cellInflateVec w = _
  rw [hsc]
  exact P.evolve_cellInflateVec w t

/-- **`ε`-equitable quotient dynamics.**  Let `Geq` carry an equitable
partition `P` and let `G` be any weighted graph with
`‖G.adj − Geq.adj‖ ≤ ε` (L²-operator norm).  Then for every quotient state
`w` and every time `t`, evolving the lift of `w` under the *perturbed* walk
`G` tracks the lift of the quotient-evolved state to within

  `|t| · ε · ‖lift w‖₂`.

The two legs: `(G.evolve t − Geq.evolve t) *ᵥ lift w` is controlled by the
Duhamel bound, and `Geq.evolve t` intertwines the lift *exactly*
(`evolve_cellInflateVec`) — the second leg contributes zero error.  The
bound is uniform in the partition: only the operator-norm distance of the
hosts and the energy `‖lift w‖₂` of the initial state enter. -/
theorem epsEquitable_quotient_dynamics (G Geq : WeightedGraph V)
    (P : EquitablePartition Geq I) {ε : ℝ} (hR : ‖G.adj - Geq.adj‖ ≤ ε)
    (t : ℝ) (w : I → ℂ) :
    ‖(EuclideanSpace.equiv V ℂ).symm
        ((G.evolve t) *ᵥ P.cellInflateVec w
          - P.cellInflateVec
              ((NormedSpace.exp ((-(t : ℂ) * Complex.I) • P.symmQuotient)) *ᵥ w))‖
      ≤ |t| * ε * ‖(EuclideanSpace.equiv V ℂ).symm (P.cellInflateVec w)‖ := by
  have hop : ‖G.evolve t - Geq.evolve t‖ ≤ |t| * ε :=
    (evolve_perturbation G Geq t).trans
      (mul_le_mul_of_nonneg_left hR (abs_nonneg t))
  -- The Duhamel leg, stated for an abstract vector `ℓ` first: applying
  -- `l2_opNorm_mulVec` directly at the (large) `cellInflateVec` term sends the
  -- unifier into deep `whnf` of the lift; an `∀ ℓ` cut keeps it linear.
  have key : ∀ ℓ : V → ℂ,
      ‖(EuclideanSpace.equiv V ℂ).symm ((G.evolve t - Geq.evolve t) *ᵥ ℓ)‖
        ≤ |t| * ε * ‖(EuclideanSpace.equiv V ℂ).symm ℓ‖ := by
    intro ℓ
    calc ‖(EuclideanSpace.equiv V ℂ).symm ((G.evolve t - Geq.evolve t) *ᵥ ℓ)‖
        ≤ ‖G.evolve t - Geq.evolve t‖ * ‖(EuclideanSpace.equiv V ℂ).symm ℓ‖ :=
          Matrix.l2_opNorm_mulVec _ _
      _ ≤ |t| * ε * ‖(EuclideanSpace.equiv V ℂ).symm ℓ‖ :=
          mul_le_mul_of_nonneg_right hop (norm_nonneg _)
  -- The exact intertwining leg: rewrite the compared state as a single
  -- perturbed-evolution image, then apply the Duhamel leg.
  have hre : (G.evolve t) *ᵥ P.cellInflateVec w
        - P.cellInflateVec
            ((NormedSpace.exp ((-(t : ℂ) * Complex.I) • P.symmQuotient)) *ᵥ w)
      = (G.evolve t - Geq.evolve t) *ᵥ P.cellInflateVec w := by
    rw [← evolve_mulVec_cellInflateVec Geq P w t, ← Matrix.sub_mulVec]
  rw [hre]
  exact key (P.cellInflateVec w)

end EpsDynamics

end Graphplay
