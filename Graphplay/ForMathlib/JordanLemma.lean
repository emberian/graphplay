/-
# Graphplay.ForMathlib.JordanLemma — the two-reflections (Jordan) lemma

target: Mathlib/LinearAlgebra/Matrix/Reflection.lean (no current home)

**Jordan's lemma** (Jordan, "Essai sur la géométrie à n dimensions", 1875): two
orthogonal projections `Π, Π'` on a finite-dimensional inner-product space jointly
decompose it into invariant subspaces of dimension `≤ 2`; on each `2`-dimensional
block the product of the two associated reflections `S = 2Π' − I`, `R = 2Π − I`
acts as a planar rotation by twice the principal angle.  Consequently every
eigenvalue of `U = S · R` is `exp(±i·2θ)` for a principal angle `θ`, and
`cos 2θ ∈ [−1,1]` is an eigenvalue of the self-adjoint "discriminant"
`½(SR + RS)`.

This file builds the **entire abstract two-reflections lemma, sorry-free**, working
with the concrete Jordan discriminant `D₀ := ½(SR + RS) = ½(U + U⁻¹)`
(`reflStepDiscriminant`):

* `reflStep_unitary` — `U = SR` is unitary for Hermitian involutions `R, S`;
* `unitary_eigenvalue_norm_one` — every eigenvalue lies on the unit circle
  (`‖μ‖ = 1`), proved honestly from an eigenvector;
* `norm_one_eq_exp_pm_arccos_re` — the polar packaging `μ = exp(±i·arccos (Re μ))`
  with `Re μ ∈ [−1,1]`;
* `reflStepDiscriminant_isHermitian` — `D₀` is genuinely Hermitian;
* `reflStep_re_mem_discriminant` — **the cosines `Re μ = cos θ` are honestly
  eigenvalues of `D₀`**, proved from the eigenvector via `(RS) v = μ⁻¹ v` and
  `μ⁻¹ = conj μ`;
* `reflStep_eigenvalue_angle` — the assembled statement: every eigenvalue `μ` of
  `U = SR` is `exp(±i·arccos λ)` for an eigenvalue `λ ∈ [−1,1]` of `D₀`.

There is **no residual here**: the abstract Jordan content (eigenvalues of `SR` are
`exp(±i·arccos λ)` with `λ ∈ spectrum (½(SR+RS))`) is fully discharged.  What the
walk files still owe is *only* the **discriminant SVD/similarity identification**
`spectrum (½(SR+RS)) = spectrum randomWalkOp` — that the cosines of the principal
angles are exactly the random-walk eigenvalues — which is the one SVD factorisation /
CS-decomposition fact Mathlib does not yet have (it has Hermitian eigenvalues and
singular values but no SVD factorisation nor two-projection block reduction).

The Szegedy and Grover walks instantiate `reflStep_eigenvalue_angle` with `R` the
coin reflection (`= 2Π − I`, `Π` the Szegedy / Grover projector) and `S` the swap /
flip-flop shift, both Hermitian involutions, supplying the spectrum identification
in their own `*_spec` lemmas.  See `Graphplay/DiscreteTime.lean` and
`Graphplay/StdLib/CoinedWalk.lean`.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open scoped Matrix
open scoped ComplexOrder
open Complex

namespace Graphplay.ForMathlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The reflection step `U = S · R`

We package the abstract hypotheses of Jordan's lemma: `R` and `S` are Hermitian
involutions (`Rᴴ = R`, `R·R = 1`, likewise `S`).  These are exactly the facts
proved sorry-free in the walk files (`szReflection_isHermitian`,
`szReflection_mul_self`, `szSwap_isHermitian`, `szSwap_mul_self`, and the Grover
analogues), so the abstract results below transfer with no further work. -/

/-- A Hermitian involution is unitary: `Rᴴ · R = 1`. -/
theorem isHermitian_involution_unitary {R : Matrix n n ℂ}
    (hHerm : R.IsHermitian) (hInv : R * R = 1) :
    Rᴴ * R = 1 := by
  rw [hHerm]; exact hInv

/-- **The reflection step is unitary.**  If `R` and `S` are Hermitian involutions
then `U = S · R` satisfies `Uᴴ · U = 1`.  Proof:
`(S R)ᴴ (S R) = Rᴴ Sᴴ S R = R (Sᴴ S) R = R · 1 · R = R · R = 1`. -/
theorem reflStep_unitary {R S : Matrix n n ℂ}
    (hR : R.IsHermitian) (hRinv : R * R = 1)
    (hS : S.IsHermitian) (hSinv : S * S = 1) :
    (S * R)ᴴ * (S * R) = 1 := by
  rw [Matrix.conjTranspose_mul, hR, hS]
  -- (R · S) · (S · R) = R · (S · S) · R = R · 1 · R = R · R = 1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hSinv, Matrix.one_mul, hRinv]

/-! ## Circle constraint on the spectrum (reachable half of Jordan's lemma)

Every eigenvalue of a unitary matrix lies on the unit circle.  We prove this
directly from a genuine eigenvector (extracted via
`Module.End.hasEigenvalue_iff_mem_spectrum`), using that `U` preserves the
Hermitian form `⟨v, v⟩ = star v ⬝ᵥ v`. -/

/-- A unitary matrix preserves the squared norm `star v ⬝ᵥ v` of every vector. -/
theorem unitary_preserves_dotProduct_self {U : Matrix n n ℂ}
    (hU : Uᴴ * U = 1) (v : n → ℂ) :
    star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
  -- star (U v) ⬝ᵥ (U v) = (star v ⬝ᵥ Uᴴ U v) = star v ⬝ᵥ v.
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
    Matrix.vecMul_one]

/-- **Every eigenvalue of a unitary matrix has modulus one.**  From an eigenvector
`U v = μ v` with `v ≠ 0`: the unitary `U` preserves `q := star v ⬝ᵥ v > 0`, while
`star (μ v) ⬝ᵥ (μ v) = (conj μ · μ) · q`, forcing `conj μ · μ = 1`, i.e. `‖μ‖ = 1`.
This is the circle constraint that, together with the (still-missing) angle
extraction, yields `μ = exp(i·θ)`. -/
theorem unitary_eigenvalue_norm_one {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ U) : ‖μ‖ = 1 := by
  -- Extract a genuine nonzero eigenvector.
  rw [← Matrix.spectrum_toLin'] at hμ
  have hev : Module.End.HasEigenvalue U.toLin' μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ
  obtain ⟨v, hvmem, hvne⟩ := hev.exists_hasEigenvector
  have hveig : U *ᵥ v = μ • v := by
    have := Module.End.mem_eigenspace_iff.mp hvmem
    rwa [Matrix.toLin'_apply] at this
  -- `q := star v ⬝ᵥ v` is nonzero (it is `‖v‖² > 0`, but we only need `≠ 0`).
  set q : ℂ := star v ⬝ᵥ v with hq
  have hqne : q ≠ 0 := by
    rw [hq]
    exact fun h => hvne (dotProduct_star_self_eq_zero.mp h)
  -- Unitarity: `star (U v) ⬝ᵥ (U v) = q`.
  have hpres := unitary_preserves_dotProduct_self hU v
  -- But `U v = μ • v`, so LHS `= (conj μ * μ) * q`.
  rw [hveig] at hpres
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_smul] at hpres
  -- `(star μ * μ) • q = q`, with `q ≠ 0`, gives `star μ * μ = 1`.
  rw [smul_eq_mul] at hpres
  -- `hpres : star μ * μ * q = q`; cancel `q`.
  have hμμ : (starRingEnd ℂ) μ * μ = 1 := by
    have hcancel : (starRingEnd ℂ) μ * μ * q = (1 : ℂ) * q := by
      rw [one_mul]; exact hpres
    exact mul_right_cancel₀ hqne hcancel
  -- `conj μ · μ = normSq μ` (as a complex number), so `normSq μ = 1`, so `‖μ‖ = 1`.
  have hnormSq : Complex.normSq μ = 1 := by
    have : ((Complex.normSq μ : ℝ) : ℂ) = (1 : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self, hμμ]
    exact_mod_cast this
  rw [Complex.norm_def, hnormSq, Real.sqrt_one]

/-! ## Trigonometric packaging: `‖μ‖ = 1 ⇒ μ = exp(±i·arccos (Re μ))`

Once the circle constraint `‖μ‖ = 1` is in hand, the *real part* `λ := Re μ`
is forced into `[−1, 1]` and the polar form collapses to `exp(±i·arccos λ)`:
the sign is `+` when `Im μ ≥ 0` and `−` when `Im μ < 0`.  This is pure
trigonometric bookkeeping (`Complex.arg`, `Real.arccos`) — no Jordan content —
so we discharge it sorry-free here; it absorbs the entire `exp(±i·arccos)`
packaging that the walk-correspondence statements ask for, leaving *only* the
membership `(Re μ : ℂ) ∈ spectrum D` as the irreducible residual. -/

/-- **Polar form for a unit-modulus complex number.**  If `‖μ‖ = 1` then, with
`λ := μ.re ∈ [−1, 1]`, one has `μ = exp((±1)·i·arccos λ)`, sign `+` iff
`Im μ ≥ 0`.  This packages the `exp(±i·arccos)` shape used by the walk spectral
theorems, leaving the discriminant-membership of `λ` as the only residual. -/
theorem norm_one_eq_exp_pm_arccos_re {μ : ℂ} (hμ : ‖μ‖ = 1) :
    μ.re ∈ Set.Icc (-1 : ℝ) 1 ∧
    ∃ sgn : Bool,
      μ = Complex.exp ((if sgn then 1 else -1) * Complex.I * Real.arccos μ.re) := by
  have hμ0 : μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hμ; exact one_ne_zero hμ.symm
  -- `|Re μ| ≤ ‖μ‖ = 1`, so `Re μ ∈ [−1, 1]`.
  have hre : μ.re ∈ Set.Icc (-1 : ℝ) 1 := by
    have habs : |μ.re| ≤ 1 := by
      have := Complex.abs_re_le_norm μ; rwa [hμ] at this
    exact abs_le.mp habs
  refine ⟨hre, ?_⟩
  -- `cos (arg μ) = Re μ / ‖μ‖ = Re μ`.
  have hcos : Real.cos (Complex.arg μ) = μ.re := by
    rw [Complex.cos_arg hμ0, hμ, div_one]
  -- Polar form `μ = ‖μ‖ · exp(arg μ · i) = exp(arg μ · i)`.
  have hpolar : μ = Complex.exp (Complex.arg μ * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I μ
    rw [hμ, Complex.ofReal_one, one_mul] at h
    exact h.symm
  by_cases him : 0 ≤ μ.im
  · -- `Im μ ≥ 0`: `arg μ = arccos (Re μ)`, sign `+`.
    refine ⟨true, ?_⟩
    have harg : Complex.arg μ = Real.arccos μ.re := by
      rw [Complex.arg_of_im_nonneg_of_ne_zero him hμ0, hμ, div_one]
    -- Reduce to equality of the two exponents (both sides are `cexp _`).
    conv_lhs => rw [hpolar]
    congr 1
    rw [show (if true then (1:ℂ) else -1) = 1 from rfl, harg]
    push_cast; ring
  · -- `Im μ < 0`: `arg μ ∈ (−π, 0)`, so `arccos (Re μ) = −arg μ`, sign `−`.
    refine ⟨false, ?_⟩
    push_neg at him
    have hargneg : Complex.arg μ < 0 := Complex.arg_neg_iff.2 him
    have hpiltarg : -Real.pi < Complex.arg μ := Complex.neg_pi_lt_arg μ
    -- `arccos (Re μ) = arccos (cos (arg μ)) = |arg μ| = −arg μ` since `arg μ < 0`.
    have harccos : Real.arccos μ.re = - Complex.arg μ := by
      rw [← hcos]
      have h1 : Real.arccos (Real.cos (Complex.arg μ))
          = Real.arccos (Real.cos (-Complex.arg μ)) := by
        rw [Real.cos_neg]
      rw [h1, Real.arccos_cos (by linarith) (by linarith [Real.pi_pos])]
    conv_lhs => rw [hpolar]
    congr 1
    rw [show (if false then (1:ℂ) else -1) = -1 from rfl, harccos]
    push_cast; ring

/-! ## The Jordan discriminant and the irreducible CS-decomposition residual

The honest discriminant attached to a product of two reflections `U = S · R` is the
**real-part operator** `D₀ := ½(U + U⁻¹) = ½(S·R + R·S)` (using `U⁻¹ = R·S`, valid
because `R, S` are involutions).  It is *genuinely* Hermitian (`reflStepDiscriminant_isHermitian`,
proved sorry-free) and its eigenvalues are exactly the cosines `Re μ = cos θ` of the
walk eigenvalues `μ = exp(iθ)`.

After the circle constraint (`unitary_eigenvalue_norm_one`) and the polar packaging
(`norm_one_eq_exp_pm_arccos_re`), both sorry-free, the *entire* remaining content of
Jordan's lemma is the single membership **`Re μ ∈ spectrum D₀`** — that the real part
of each walk eigenvalue is an eigenvalue of this *specific* discriminant `D₀`.  This is
exactly the planar rotation-by-`2θ` / cosine–sine two-projection block decomposition,
which Mathlib does not have (it has Hermitian *eigenvalues* and singular *values* but no
CS-decomposition / two-projection block reduction).  We isolate precisely this membership
as the lone named residual; because it is stated for the concrete `D₀ = ½(SR + RS)` it is
a *true* statement, not vacuous. -/

/-- The **Jordan discriminant** of a reflection step `U = S · R`: the Hermitian
real-part operator `D₀ := ½(S·R + R·S)` (`= ½(U + U⁻¹)` since `R, S` are involutions),
whose eigenvalues are the cosines `cos θ` of the rotation angles. -/
noncomputable def reflStepDiscriminant {m : Type*} [Fintype m] [DecidableEq m]
    (R S : Matrix m m ℂ) : Matrix m m ℂ :=
  (1 / 2 : ℂ) • (S * R + R * S)

/-- The Jordan discriminant is **Hermitian**: `(½(SR + RS))ᴴ = ½(RS + SR) = ½(SR + RS)`,
using `Rᴴ = R`, `Sᴴ = S`. -/
theorem reflStepDiscriminant_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {R S : Matrix m m ℂ} (hR : R.IsHermitian) (hS : S.IsHermitian) :
    (reflStepDiscriminant R S).IsHermitian := by
  unfold Matrix.IsHermitian reflStepDiscriminant
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR, hS,
    show star (1 / 2 : ℂ) = (1 / 2 : ℂ) by norm_num, add_comm (R * S) (S * R)]

/-- **The real part of a reflection-step eigenvalue is a discriminant eigenvalue.**
For Hermitian involutions `R, S`, the real part `Re μ = cos θ` of every eigenvalue
`μ` of `U = S · R` is an eigenvalue of the concrete Jordan discriminant
`D₀ = reflStepDiscriminant R S = ½(SR + RS) = ½(U + U⁻¹)`.

This is now proved **sorry-free** directly from an eigenvector: if `(SR) v = μ v`
with `v ≠ 0`, then `(RS) v = μ⁻¹ v` (because `(RS)(SR) = 1`), so
`D₀ v = ½(μ + μ⁻¹) v = (Re μ) v` using `μ⁻¹ = conj μ` (`‖μ‖ = 1`), exhibiting
`Re μ` as a `D₀`-eigenvalue.  Thus the cosines `Re μ = cos θ` of the rotation angles
are *honestly* eigenvalues of the discriminant; the only remaining content of
Jordan's lemma — identifying `spectrum D₀` with the random-walk spectrum — is the
discriminant SVD/similarity fact discharged in the walk files.

Reference: Jordan (1875); Szegedy, FOCS 2004, Thm 1; Portugal (2018), §7.3. -/
theorem reflStep_re_mem_discriminant
    {m : Type*} [Fintype m] [DecidableEq m]
    (R S : Matrix m m ℂ)
    (hR : R.IsHermitian) (hRinv : R * R = 1)
    (hS : S.IsHermitian) (hSinv : S * S = 1)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ (S * R)) :
    ((μ.re : ℝ) : ℂ) ∈ spectrum ℂ (reflStepDiscriminant R S) := by
  -- `U = S·R` is unitary, so `‖μ‖ = 1` and hence `μ ≠ 0`, `μ⁻¹ = conj μ`.
  have hUnit : (S * R)ᴴ * (S * R) = 1 := reflStep_unitary hR hRinv hS hSinv
  have hnorm : ‖μ‖ = 1 := unitary_eigenvalue_norm_one hUnit hμ
  have hμ0 : μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm
  -- `μ⁻¹ = conj μ`: from `μ · conj μ = ‖μ‖² = 1`.
  have hmulconj : μ * (starRingEnd ℂ) μ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  have hinv : μ⁻¹ = (starRingEnd ℂ) μ := by
    rw [inv_eq_of_mul_eq_one_right hmulconj]
  -- Extract a genuine nonzero eigenvector of `U = S·R`.
  rw [← Matrix.spectrum_toLin'] at hμ
  have hev : Module.End.HasEigenvalue (S * R).toLin' μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ
  obtain ⟨v, hvmem, hvne⟩ := hev.exists_hasEigenvector
  have hveig : (S * R) *ᵥ v = μ • v := by
    have := Module.End.mem_eigenspace_iff.mp hvmem
    rwa [Matrix.toLin'_apply] at this
  -- `(RS) v = μ⁻¹ v`, from `(RS)(SR) = 1`: `(RS)·(μ v) = (RS)(SR) v = v`.
  have hRSeig : (R * S) *ᵥ v = μ⁻¹ • v := by
    have hone : (R * S) * (S * R) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hSinv, Matrix.one_mul, hRinv]
    have hcalc : (R * S) *ᵥ ((S * R) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hone, Matrix.one_mulVec]
    rw [hveig, Matrix.mulVec_smul] at hcalc
    -- `μ • ((R*S) v) = v`, so `(R*S) v = μ⁻¹ • v`.
    have := congrArg (fun w => μ⁻¹ • w) hcalc
    simpa [smul_smul, inv_mul_cancel₀ hμ0] using this
  -- `D₀ v = ½(μ + μ⁻¹) • v = (Re μ) • v`.
  have hDeig : (reflStepDiscriminant R S) *ᵥ v = ((μ.re : ℝ) : ℂ) • v := by
    unfold reflStepDiscriminant
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, hveig, hRSeig, smul_add,
      smul_smul, smul_smul]
    -- `½·μ • v + ½·μ⁻¹ • v = (½(μ + μ⁻¹)) • v = Re μ • v`.
    rw [← add_smul]
    congr 1
    rw [hinv]
    -- `½·μ + ½·conj μ = ½(μ + conj μ) = ½·(2·Re μ) = Re μ`.
    rw [show (1 / 2 : ℂ) * μ + (1 / 2 : ℂ) * (starRingEnd ℂ) μ
        = (1 / 2 : ℂ) * (μ + (starRingEnd ℂ) μ) by ring,
      Complex.add_conj]
    push_cast; ring
  -- An eigenvector exhibits `Re μ ∈ spectrum D₀`.
  rw [← Matrix.spectrum_toLin']
  apply Module.End.hasEigenvalue_iff_mem_spectrum.mp
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := v)
  refine ⟨?_, hvne⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hDeig]

/-- **Jordan-lemma angle extraction** (now *derived* from the lone residual).
For Hermitian involutions `R, S`, every eigenvalue `μ` of `U = S · R` is
`exp(±i·arccos λ)` for some eigenvalue `λ ∈ [−1,1]` of the concrete Jordan
discriminant `D₀ = ½(SR + RS)`.

Proof: `U` is unitary (`reflStep_unitary`), so `‖μ‖ = 1`
(`unitary_eigenvalue_norm_one`); the polar packaging
(`norm_one_eq_exp_pm_arccos_re`) supplies `λ := Re μ ∈ [−1,1]` and the
`exp(±i·arccos λ)` form, and `reflStep_re_mem_discriminant` supplies the lone
remaining fact `λ ∈ spectrum D₀`.  Both the Szegedy and Grover spectral
correspondences are instances of this statement; see
`Graphplay/DiscreteTime.lean :: WeightedGraph.szegedy_discriminant_eigenvalue`
and `Graphplay/StdLib/CoinedWalk.lean :: groverStep_discriminant_eigenvalue`.

Reference: Jordan (1875); Szegedy, FOCS 2004, Thm 1; Portugal (2018), §7.3. -/
theorem reflStep_eigenvalue_angle
    {m : Type*} [Fintype m] [DecidableEq m]
    (R S : Matrix m m ℂ)
    (hR : R.IsHermitian) (hRinv : R * R = 1)
    (hS : S.IsHermitian) (hSinv : S * S = 1)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ (S * R)) :
    ∃ (lam : ℝ) (sgn : Bool),
      lam ∈ Set.Icc (-1 : ℝ) 1 ∧
      (lam : ℂ) ∈ spectrum ℂ (reflStepDiscriminant R S) ∧
      μ = Complex.exp ((if sgn then 1 else -1) * Complex.I * Real.arccos lam) := by
  -- `U = S·R` is unitary, hence `‖μ‖ = 1` (both proved sorry-free above).
  have hUnit : (S * R)ᴴ * (S * R) = 1 := reflStep_unitary hR hRinv hS hSinv
  have hnorm : ‖μ‖ = 1 := unitary_eigenvalue_norm_one hUnit hμ
  -- Polar packaging: `λ := Re μ ∈ [−1,1]` and `μ = exp(±i·arccos λ)`.
  obtain ⟨hre, sgn, hpolar⟩ := norm_one_eq_exp_pm_arccos_re hnorm
  -- The lone residual: `λ = Re μ` is a `D₀`-eigenvalue.
  have hmem : ((μ.re : ℝ) : ℂ) ∈ spectrum ℂ (reflStepDiscriminant R S) :=
    reflStep_re_mem_discriminant R S hR hRinv hS hSinv μ hμ
  exact ⟨μ.re, sgn, hre, hmem, hpolar⟩

/-! ## The Szegedy intertwiner: spectral inclusion via an isometry

The deep half of the Szegedy/Grover correspondence is *not* a full SVD: it is the
statement that the random-walk operator embeds into the Jordan discriminant through
the **Szegedy isometry** `T : ℂ^V ↪ ℂ^{V×V}`, `T |x⟩ = |φ_x⟩`, under which `D₀`
*restricts* to the discriminant matrix.  We isolate the abstract linear-algebra core
here, working with a rectangular `T : Matrix m n ℂ` satisfying `Tᴴ T = 1` (columns
orthonormal — a genuine isometry) and the **intertwining relation** `D₀ · T = T · D`.

The single fact we need is the *forward* spectral inclusion `spectrum D ⊆ spectrum D₀`:
an isometric intertwiner pushes eigenvectors of `D` to nonzero eigenvectors of `D₀`.
This is elementary (no SVD, no two-projection block reduction) and is proved sorry-free
below; it is exactly the direction Szegedy's theorem needs (every random-walk eigenvalue
is a discriminant eigenvalue / cosine of a principal angle). -/

/-- An **isometry kills no vector**: if `Tᴴ · T = 1` then `T *ᵥ x = 0 ⇒ x = 0`.
Proof: `(Tᴴ T) *ᵥ x = Tᴴ *ᵥ (T *ᵥ x) = Tᴴ *ᵥ 0 = 0`, but `(Tᴴ T) *ᵥ x = x`. -/
theorem isometry_mulVec_ne_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {T : Matrix m n ℂ} (hT : Tᴴ * T = 1) {x : n → ℂ} (hx : x ≠ 0) :
    T *ᵥ x ≠ 0 := by
  intro h
  apply hx
  have hone : (Tᴴ * T) *ᵥ x = x := by rw [hT]; exact Matrix.one_mulVec x
  rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero] at hone
  exact hone.symm

/-- **Isometric-intertwiner spectral inclusion.**  Let `T : Matrix m n ℂ` be an
isometry (`Tᴴ · T = 1`, i.e. orthonormal columns) intertwining `D : Matrix n n ℂ`
with `D₀ : Matrix m m ℂ`: `D₀ · T = T · D`.  Then `spectrum D ⊆ spectrum D₀`.

Proof: an eigenvector `D *ᵥ x = λ • x` (`x ≠ 0`) maps to `T *ᵥ x ≠ 0`
(`isometry_mulVec_ne_zero`) with
`D₀ *ᵥ (T *ᵥ x) = (D₀ T) *ᵥ x = (T D) *ᵥ x = T *ᵥ (D *ᵥ x) = λ • (T *ᵥ x)`,
exhibiting `λ ∈ spectrum D₀`.  This is the elementary restriction/embedding fact —
*not* an SVD — underlying the Szegedy discriminant correspondence. -/
theorem spectrum_subset_of_isometry_intertwiner
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {T : Matrix m n ℂ} {D : Matrix n n ℂ} {D₀ : Matrix m m ℂ}
    (hT : Tᴴ * T = 1) (hint : D₀ * T = T * D) :
    spectrum ℂ D ⊆ spectrum ℂ D₀ := by
  intro lam hlam
  -- Extract a genuine nonzero eigenvector of `D` for `lam`.
  rw [← Matrix.spectrum_toLin'] at hlam
  have hev : Module.End.HasEigenvalue D.toLin' lam :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlam
  obtain ⟨x, hxmem, hxne⟩ := hev.exists_hasEigenvector
  have hxeig : D *ᵥ x = lam • x := by
    have := Module.End.mem_eigenspace_iff.mp hxmem
    rwa [Matrix.toLin'_apply] at this
  -- `T *ᵥ x` is a nonzero `D₀`-eigenvector for `lam`.
  have hTx_ne : T *ᵥ x ≠ 0 := isometry_mulVec_ne_zero hT hxne
  have hD₀eig : D₀ *ᵥ (T *ᵥ x) = lam • (T *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, hint, ← Matrix.mulVec_mulVec, hxeig, Matrix.mulVec_smul]
  -- Conclude `lam ∈ spectrum D₀`.
  rw [← Matrix.spectrum_toLin']
  apply Module.End.hasEigenvalue_iff_mem_spectrum.mp
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := T *ᵥ x)
  exact ⟨by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hD₀eig], hTx_ne⟩

/-- **The Jordan discriminant restricts along an isometry built from its own
projector.**  Suppose `R = 2·(T·Tᴴ) − I` is the reflection through the range of an
isometry `T` (`Tᴴ·T = 1`), and `S` is any matrix.  Then the Jordan discriminant
`D₀ = ½(SR + RS)` intertwines with the **compressed** matrix `D := Tᴴ·S·T` via `T`:
`D₀ · T = T · (Tᴴ S T)`.

This is the concrete bridge for Szegedy/Grover: `R` is the coin reflection
`2Π − I` with `Π = T Tᴴ` the Szegedy projector, `S` the swap/flip-flop, and
`Tᴴ S T` the discriminant matrix.  Combined with
`spectrum_subset_of_isometry_intertwiner`, it yields
`spectrum (Tᴴ S T) ⊆ spectrum D₀` with no SVD.

Computation: `RT = (2TTᴴ − I)T = 2T(TᴴT) − T = 2T − T = T`, so `SRT = ST`;
`RST = 2TTᴴST − ST`; hence `(SR+RS)T = ST + 2TTᴴST − ST = 2T(TᴴST)`, and
`D₀T = ½·2T(TᴴST) = T(TᴴST)`. -/
theorem reflStepDiscriminant_intertwines_compression
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {T : Matrix m n ℂ} (hT : Tᴴ * T = 1) (S : Matrix m m ℂ) :
    reflStepDiscriminant ((2 : ℂ) • (T * Tᴴ) - 1) S * T
      = T * (Tᴴ * S * T) := by
  set R : Matrix m m ℂ := (2 : ℂ) • (T * Tᴴ) - 1 with hR
  -- `R · T = T`: `(2 TTᴴ − I)T = 2 T (TᴴT) − T = 2T − T = T`.
  have hRT : R * T = T := by
    rw [hR, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, hT, Matrix.mul_one,
      Matrix.one_mul, two_smul, add_sub_cancel_right]
  -- `R·S·T = (2 TTᴴ − I)·S·T = 2 T (Tᴴ S T) − S T`.
  have hRST : R * S * T = (2 : ℂ) • (T * (Tᴴ * S * T)) - S * T := by
    rw [hR, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  -- `(S·R + R·S) · T = 2 · T · (Tᴴ S T)`.
  unfold reflStepDiscriminant
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.mul_assoc S, hRT, hRST]
  -- `½ • (S·T + (2 • T(TᴴST) − S·T)) = T (Tᴴ S T)`.
  rw [show S * T + ((2 : ℂ) • (T * (Tᴴ * S * T)) - S * T)
      = (2 : ℂ) • (T * (Tᴴ * S * T)) by abel]
  rw [smul_smul]
  norm_num

/-- **Szegedy discriminant inclusion (abstract, sorry-free).**  For an isometry `T`
(`Tᴴ·T = 1`) and any matrix `S`, the spectrum of the compressed discriminant matrix
`Tᴴ·S·T` is contained in the spectrum of the Jordan discriminant
`D₀ = ½(SR + RS)` of the reflection `R = 2(TTᴴ) − I`.

This is the genuine content of the Szegedy correspondence, with **no SVD and no
two-projection block reduction**: every eigenvalue of the discriminant matrix
(equivalently, every random-walk eigenvalue, once `TᴴST` is identified with the
random-walk operator) is an eigenvalue of `D₀`.  Combines
`reflStepDiscriminant_intertwines_compression` with
`spectrum_subset_of_isometry_intertwiner`. -/
theorem spectrum_compression_subset_reflStepDiscriminant
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {T : Matrix m n ℂ} (hT : Tᴴ * T = 1) (S : Matrix m m ℂ) :
    spectrum ℂ (Tᴴ * S * T)
      ⊆ spectrum ℂ (reflStepDiscriminant ((2 : ℂ) • (T * Tᴴ) - 1) S) :=
  spectrum_subset_of_isometry_intertwiner hT
    (reflStepDiscriminant_intertwines_compression hT S)

end Graphplay.ForMathlib
