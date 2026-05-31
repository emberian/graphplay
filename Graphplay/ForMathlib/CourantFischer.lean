/-
# Graphplay.ForMathlib.CourantFischer

**Codimension-one Courant–Fischer for Hermitian matrices.**

Mathlib supplies the extremal-eigenvalue Rayleigh theory and the antitone
eigenbasis (`IsHermitian.eigenvalues₀`), but not the codimension-`1` min-max
that, after projecting out a known bottom eigenvector, identifies the *next*
eigenvalue with the constrained Rayleigh infimum.  This file develops it from
the spectral theorem, in the concrete `Matrix`/`dotProduct` vocabulary, for the
special case that powers Fiedler's algebraic-connectivity characterisation: a
Hermitian, positive-semidefinite matrix `A` (`0 ≤ eigenvalues`) with a known
null vector `v₁` (`A *ᵥ v₁ = 0`, the realised bottom eigenvector), whose
constrained Rayleigh infimum over `v₁^⊥` equals the second-smallest eigenvalue
`eigenvalues₀ ⟨card − 2, _⟩`.

The two spectral hinges (`hermitianForm_re_eq_sum`, `normSq_eq_sum`) write the
numerator and denominator of the Rayleigh quotient as sums of eigenvalue-weighted
squared eigencoordinates; the infimum identity is then a convex-combination lower
bound (`≥`, via `le_csInf`) and an explicit eigenvector witness (`≤`, via
`csInf_le`).
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix
open WithLp

namespace Graphplay
namespace CourantFischer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Spectral hinges: numerator and denominator in eigencoordinates -/

/-- Spectral expansion of the Hermitian quadratic form:
`(star x ⬝ᵥ A *ᵥ x).re = ∑ᵢ λᵢ ‖⟨vᵢ, x⟩‖²`. -/
theorem hermitianForm_re_eq_sum (A : Matrix V V ℂ) (hA : A.IsHermitian) (x : V → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re
      = ∑ i, (hA.eigenvalues i) * ‖inner ℂ (hA.eigenvectorBasis i) (toLp 2 x)‖ ^ 2 := by
  have form_expand : star (ofLp (toLp 2 x : EuclideanSpace ℂ V)) ⬝ᵥ (A *ᵥ ofLp (toLp 2 x))
      = ∑ i, (hA.eigenvalues i : ℂ)
          * (‖inner ℂ (hA.eigenvectorBasis i) (toLp 2 x : EuclideanSpace ℂ V)‖ ^ 2 : ℝ) := by
    set y : EuclideanSpace ℂ V := toLp 2 x
    have hx : ofLp y = ∑ i, (inner ℂ (hA.eigenvectorBasis i) y) • (ofLp (hA.eigenvectorBasis i)) := by
      conv_lhs => rw [← hA.eigenvectorBasis.sum_repr y, ofLp_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hA.eigenvectorBasis.repr_apply_apply, ofLp_smul]
    have hAx : A *ᵥ ofLp y
        = ∑ i, ((inner ℂ (hA.eigenvectorBasis i) y) * (hA.eigenvalues i : ℂ))
            • ofLp (hA.eigenvectorBasis i) := by
      conv_lhs => rw [hx]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, mul_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    rw [hAx, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
    have hdb : star (ofLp y) ⬝ᵥ ofLp (hA.eigenvectorBasis i)
        = (starRingEnd ℂ) (inner ℂ (hA.eigenvectorBasis i) y) := by
      rw [Matrix.star_dotProduct]
      congr 1
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rw [hdb]
    set c := inner ℂ (hA.eigenvectorBasis i) y
    have hcc : c * (hA.eigenvalues i : ℂ) * (starRingEnd ℂ) c
        = (hA.eigenvalues i : ℂ) * (c * (starRingEnd ℂ) c) := by ring
    rw [hcc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [ofLp_toLp] at form_expand
  rw [form_expand, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- Parseval: the squared norm in the eigenbasis coordinates,
`∑ᵤ ‖xᵤ‖² = ∑ᵢ ‖⟨vᵢ, x⟩‖²`. -/
theorem normSq_eq_sum (A : Matrix V V ℂ) (hA : A.IsHermitian) (x : V → ℂ) :
    (∑ u, ‖x u‖ ^ 2) = ∑ i, ‖inner ℂ (hA.eigenvectorBasis i) (toLp 2 x)‖ ^ 2 := by
  rw [hA.eigenvectorBasis.sum_sq_norm_inner_right, EuclideanSpace.norm_sq_eq]

/-! ## Eigenbasis index bookkeeping -/

/-- The reindexing equiv `V ≃ Fin (card V)` underlying `eigenvalues`/`eigenvectorBasis`:
`eigenvalues i = eigenvalues₀ (eIdx i)`. -/
noncomputable def eIdx (V : Type*) [Fintype V] :
    V ≃ Fin (Fintype.card V) :=
  (Fintype.equivOfCardEq (Fintype.card_fin _)).symm

theorem eigenvalues_eq_eigenvalues₀ (A : Matrix V V ℂ) (hA : A.IsHermitian) (i : V) :
    hA.eigenvalues i = hA.eigenvalues₀ (eIdx V i) := rfl

/-- The squared-norm denominator is positive for `x ≠ 0`. -/
theorem normSq_pos_of_ne_zero (x : V → ℂ) (hx : x ≠ 0) : 0 < ∑ u, ‖x u‖ ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
  simp only [Pi.zero_apply] at hi
  have : ‖x i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
  positivity

/-! ## The abstract Rayleigh set over `v₁^⊥` -/

/-- Abstract Rayleigh set of a matrix over vectors orthogonal to `v₁`. -/
noncomputable def rayleighSetMat (A : Matrix V V ℂ) (v₁ : V → ℂ) : Set ℝ :=
  { r : ℝ | ∃ x : V → ℂ, x ≠ 0 ∧ (∑ u, (star v₁ u) * x u = 0) ∧
      r = (star x ⬝ᵥ (A *ᵥ x)).re / ∑ u, ‖x u‖ ^ 2 }

/-! ### The smallest eigenvalue is `0`, located at the last (antitone) slot -/

/-- The smallest eigenvalue is `eigenvalues₀ ⟨card V - 1, _⟩` (the last antitone slot),
and it equals `0` here because the null vector `v₁` is a nonzero null vector and all
eigenvalues are `≥ 0`. -/
theorem eigenvalues₀_last_eq_zero
    (A : Matrix V V ℂ) (hA : A.IsHermitian) (h : 2 ≤ Fintype.card V)
    (v₁ : V → ℂ) (hv₁ : v₁ ≠ 0) (hbot : A *ᵥ v₁ = 0)
    (hmin : ∀ i, 0 ≤ hA.eigenvalues i) :
    hA.eigenvalues₀ ⟨Fintype.card V - 1, by omega⟩ = 0 := by
  set n := Fintype.card V
  have hge : 0 ≤ hA.eigenvalues₀ ⟨n - 1, by omega⟩ := by
    have := hmin (eIdx V |>.symm ⟨n - 1, by omega⟩)
    rwa [eigenvalues_eq_eigenvalues₀, Equiv.apply_symm_apply] at this
  set y : EuclideanSpace ℂ V := toLp 2 v₁ with hy
  set d : V → ℂ := fun i => inner ℂ (hA.eigenvectorBasis i) y with hd
  have hexp : y = ∑ i, d i • hA.eigenvectorBasis i := by
    conv_lhs => rw [← hA.eigenvectorBasis.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA.eigenvectorBasis.repr_apply_apply]
  have hAexp : (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) = 0 := by
    -- `A *ᵥ v₁ = 0` written out in the eigenbasis expansion of `v₁`.
    have hmv : A *ᵥ ofLp y
        = ofLp (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) := by
      have hofy : ofLp y = ∑ i, d i • ofLp (hA.eigenvectorBasis i) := by
        rw [congrArg ofLp hexp, ofLp_sum]; rfl
      rw [hofy, Matrix.mulVec_sum, ofLp_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, mul_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ), ofLp_smul]
      rfl
    -- `ofLp y = v₁`, and `A *ᵥ v₁ = 0`.
    have hofy : ofLp y = v₁ := by rw [hy, ofLp_toLp]
    rw [hofy, hbot] at hmv
    have : ofLp (0 : EuclideanSpace ℂ V)
        = ofLp (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) := by
      rw [ofLp_zero, ← hmv]
    exact (ofLp_injective (p := 2) this).symm
  have hdne : ∃ i₀, d i₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hv₁
    have hy0 : y = 0 := by
      rw [hexp]; refine Finset.sum_eq_zero fun i _ => ?_
      rw [hcon i, zero_smul]
    have : ofLp y = 0 := by rw [hy0, ofLp_zero]
    rwa [hy, ofLp_toLp] at this
  obtain ⟨i₀, hi₀⟩ := hdne
  have hindep : d i₀ * (hA.eigenvalues i₀ : ℂ) = 0 := by
    have hinner := congrArg (fun z => inner ℂ z (hA.eigenvectorBasis i₀)) hAexp
    simp only at hinner
    rw [hA.eigenvectorBasis.orthonormal.inner_left_fintype, inner_zero_left] at hinner
    have := congrArg (starRingEnd ℂ) hinner
    rwa [starRingEnd_self_apply, map_zero] at this
  have hlam0 : (hA.eigenvalues i₀ : ℝ) = 0 := by
    rcases mul_eq_zero.mp hindep with hc | hc
    · exact absurd hc hi₀
    · exact_mod_cast hc
  have hub : hA.eigenvalues₀ ⟨n - 1, by omega⟩ ≤ 0 := by
    rw [← hlam0, eigenvalues_eq_eigenvalues₀]
    exact hA.eigenvalues₀_antitone (by
      refine Fin.mk_le_mk.mpr ?_
      exact Nat.le_sub_one_of_lt (eIdx V i₀).2)
  linarith

/-! ### Two named eigenbasis vertices: the bottom and the second-from-bottom -/

/-- The vertex carrying the smallest (bottom) eigenvalue: `eIdx`-preimage of the
last antitone slot `card V − 1`. -/
noncomputable def botVert (V : Type*) [Fintype V] (h : 2 ≤ Fintype.card V) : V :=
  (eIdx V).symm ⟨Fintype.card V - 1, by omega⟩

/-- The vertex carrying the second-smallest eigenvalue: `eIdx`-preimage of slot
`card V − 2`. -/
noncomputable def secondVert (V : Type*) [Fintype V] (h : 2 ≤ Fintype.card V) : V :=
  (eIdx V).symm ⟨Fintype.card V - 2, by omega⟩

theorem eigenvalues_secondVert (A : Matrix V V ℂ) (hA : A.IsHermitian)
    (h : 2 ≤ Fintype.card V) :
    hA.eigenvalues (secondVert V h) = hA.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ := by
  rw [eigenvalues_eq_eigenvalues₀, secondVert, Equiv.apply_symm_apply]

theorem eIdx_botVert (h : 2 ≤ Fintype.card V) :
    eIdx V (botVert V h) = ⟨Fintype.card V - 1, by omega⟩ := by
  rw [botVert, Equiv.apply_symm_apply]

/-- Every non-bottom vertex has eigenvalue at least the second-smallest. -/
theorem secondEigenvalue_le_of_ne_bot (A : Matrix V V ℂ) (hA : A.IsHermitian)
    (h : 2 ≤ Fintype.card V) (i : V) (hi : i ≠ botVert V h) :
    hA.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ ≤ hA.eigenvalues i := by
  rw [eigenvalues_eq_eigenvalues₀]
  apply hA.eigenvalues₀_antitone
  -- `eIdx i ≤ card - 2` since the only index `≥ card-1` is `card-1`, attained only at `botVert`.
  rw [Fin.le_def]
  show (eIdx V i).1 ≤ Fintype.card V - 2
  have hlt : (eIdx V i).1 < Fintype.card V := (eIdx V i).2
  by_contra hcon
  push_neg at hcon
  -- `card - 2 < eIdx i` and `eIdx i < card` forces `eIdx i = card - 1 = eIdx botVert`.
  have hval : (eIdx V i).1 = Fintype.card V - 1 := by omega
  apply hi
  have heq : eIdx V i = ⟨Fintype.card V - 1, by omega⟩ := Fin.ext hval
  rw [← eIdx_botVert h] at heq
  exact (eIdx V).injective heq

/-! ### The eigencoordinate of the bottom vector vanishes under the constraint

When the second-smallest eigenvalue is positive, the bottom eigenvalue `0` is
simple, the null vector `v₁` is supported entirely on the bottom eigenvector, and
orthogonality to `v₁` forces the bottom eigencoordinate of `x` to vanish. -/
theorem botCoord_eq_zero_of_constraint
    (A : Matrix V V ℂ) (hA : A.IsHermitian) (h : 2 ≤ Fintype.card V)
    (v₁ : V → ℂ) (hv₁ : v₁ ≠ 0) (hbot : A *ᵥ v₁ = 0)
    (hmin : ∀ i, 0 ≤ hA.eigenvalues i)
    (hpos : 0 < hA.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩)
    (x : V → ℂ) (hortho : ∑ u, (star v₁ u) * x u = 0) :
    inner ℂ (hA.eigenvectorBasis (botVert V h)) (toLp 2 x : EuclideanSpace ℂ V) = 0 := by
  set y₁ : EuclideanSpace ℂ V := toLp 2 v₁ with hy₁
  set yx : EuclideanSpace ℂ V := toLp 2 x with hyx
  -- coordinates of v₁ in the eigenbasis
  set d : V → ℂ := fun i => inner ℂ (hA.eigenvectorBasis i) y₁ with hd
  -- A v₁ = 0 forces `d i * λ i = 0` for each i (same computation as the last-slot lemma).
  have hexp : y₁ = ∑ i, d i • hA.eigenvectorBasis i := by
    conv_lhs => rw [← hA.eigenvectorBasis.sum_repr y₁]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA.eigenvectorBasis.repr_apply_apply]
  have hAexp : (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) = 0 := by
    have hmv : A *ᵥ ofLp y₁
        = ofLp (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) := by
      have hofy : ofLp y₁ = ∑ i, d i • ofLp (hA.eigenvectorBasis i) := by
        rw [congrArg ofLp hexp, ofLp_sum]; rfl
      rw [hofy, Matrix.mulVec_sum, ofLp_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, mul_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ), ofLp_smul]
      rfl
    have hofy : ofLp y₁ = v₁ := by rw [hy₁, ofLp_toLp]
    rw [hofy, hbot] at hmv
    have : ofLp (0 : EuclideanSpace ℂ V)
        = ofLp (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) := by
      rw [ofLp_zero, ← hmv]
    exact (ofLp_injective (p := 2) this).symm
  -- each coordinate equation: `d i * λ i = 0`
  have hcoord : ∀ i, d i * (hA.eigenvalues i : ℂ) = 0 := by
    intro i
    have hinner := congrArg (fun z => inner ℂ z (hA.eigenvectorBasis i)) hAexp
    simp only at hinner
    rw [hA.eigenvectorBasis.orthonormal.inner_left_fintype, inner_zero_left] at hinner
    have := congrArg (starRingEnd ℂ) hinner
    rwa [starRingEnd_self_apply, map_zero] at this
  -- for non-bottom `i`, `λ i > 0`, so `d i = 0`.
  have hdzero : ∀ i, i ≠ botVert V h → d i = 0 := by
    intro i hi
    have hlampos : 0 < hA.eigenvalues i :=
      lt_of_lt_of_le hpos (secondEigenvalue_le_of_ne_bot A hA h i hi)
    have hne : (hA.eigenvalues i : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hlampos
    rcases mul_eq_zero.mp (hcoord i) with hc | hc
    · exact hc
    · exact absurd hc hne
  -- `d (botVert) ≠ 0`, else `v₁ = 0`.
  have hdbot : d (botVert V h) ≠ 0 := by
    intro hzero
    apply hv₁
    have hy0 : y₁ = 0 := by
      rw [hexp]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hb : i = botVert V h
      · rw [hb, hzero, zero_smul]
      · rw [hdzero i hb, zero_smul]
    have : ofLp y₁ = 0 := by rw [hy0, ofLp_zero]
    rwa [hy₁, ofLp_toLp] at this
  -- The constraint, expanded in the eigenbasis, collapses to the bottom term.
  -- `inner y₁ yx = ∑ i, conj (d i) * C i`, where `C i = inner (vᵢ) yx`.
  set C : V → ℂ := fun i => inner ℂ (hA.eigenvectorBasis i) yx with hC
  have hconstr : inner ℂ y₁ yx = (0 : ℂ) := by
    rw [hy₁, hyx, EuclideanSpace.inner_toLp_toLp, dotProduct]
    rw [show (0 : ℂ) = ∑ u, (star v₁ u) * x u from hortho.symm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Pi.star_apply]; ring
  have hsum : inner ℂ y₁ yx = ∑ i, (starRingEnd ℂ) (d i) * C i := by
    rw [← hA.eigenvectorBasis.sum_inner_mul_inner y₁ yx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd, hC]
    rw [inner_conj_symm]
  rw [hconstr] at hsum
  -- only the bottom term survives.
  have honly : ∑ i, (starRingEnd ℂ) (d i) * C i
      = (starRingEnd ℂ) (d (botVert V h)) * C (botVert V h) := by
    rw [← Finset.sum_subset (Finset.subset_univ {botVert V h})]
    · rw [Finset.sum_singleton]
    · intro i _ hi
      have : i ≠ botVert V h := by simpa using hi
      rw [hdzero i this, map_zero, zero_mul]
  rw [honly] at hsum
  have : C (botVert V h) = 0 := by
    rcases mul_eq_zero.mp hsum.symm with hc | hc
    · exact absurd ((starRingEnd ℂ).injective.eq_iff.mp (by rw [hc, map_zero])) hdbot
    · exact hc
  rw [hC] at this
  exact this

/-! ### Nonnegativity / bounded-belowness of the Rayleigh set -/

/-- Under `0 ≤ eigenvalues` (PSD), every Rayleigh quotient is nonnegative. -/
theorem rayleighSetMat_nonneg (A : Matrix V V ℂ) (hA : A.IsHermitian)
    (hmin : ∀ i, 0 ≤ hA.eigenvalues i) (v₁ : V → ℂ) :
    ∀ r ∈ rayleighSetMat A v₁, 0 ≤ r := by
  rintro r ⟨x, hx, _, rfl⟩
  apply div_nonneg
  · rw [hermitianForm_re_eq_sum A hA x]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hmin i) (by positivity)
  · exact (normSq_pos_of_ne_zero x hx).le

theorem bddBelow_rayleighSetMat (A : Matrix V V ℂ) (hA : A.IsHermitian)
    (hmin : ∀ i, 0 ≤ hA.eigenvalues i) (v₁ : V → ℂ) :
    BddBelow (rayleighSetMat A v₁) :=
  ⟨0, fun _ hr => rayleighSetMat_nonneg A hA hmin v₁ _ hr⟩

/-! ### The Rayleigh value of an eigenvector

For `x = ofLp (eigenvectorBasis j)`, the Rayleigh quotient is exactly the
eigenvalue `eigenvalues j`. -/
theorem rayleigh_eigenvector (A : Matrix V V ℂ) (hA : A.IsHermitian) (j : V) :
    (star (ofLp (hA.eigenvectorBasis j)) ⬝ᵥ (A *ᵥ ofLp (hA.eigenvectorBasis j))).re
        / ∑ u, ‖(ofLp (hA.eigenvectorBasis j)) u‖ ^ 2
      = hA.eigenvalues j := by
  -- numerator: `⟨vⱼ, A vⱼ⟩.re = λⱼ ‖vⱼ‖² = λⱼ`.
  set v : V → ℂ := ofLp (hA.eigenvectorBasis j) with hv
  have htoLp : (toLp 2 v : EuclideanSpace ℂ V) = hA.eigenvectorBasis j := by
    rw [hv]
  have hite := orthonormal_iff_ite (𝕜 := ℂ).mp hA.eigenvectorBasis.orthonormal
  have hden : (∑ u, ‖v u‖ ^ 2) = 1 := by
    rw [normSq_eq_sum A hA v, htoLp]
    rw [Finset.sum_eq_single j]
    · rw [hite j j, if_pos rfl]; norm_num
    · intro i _ hij
      rw [hite i j, if_neg hij]; simp
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hnum : (star v ⬝ᵥ (A *ᵥ v)).re = hA.eigenvalues j := by
    rw [hermitianForm_re_eq_sum A hA v, htoLp]
    rw [Finset.sum_eq_single j]
    · rw [hite j j, if_pos rfl]; norm_num
    · intro i _ hij
      rw [hite i j, if_neg hij]; simp
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hnum, hden, div_one]

/-! ### Constraint and inner product

The dot-product constraint `∑ star(v₁ u) * x u` is the Euclidean inner product
`⟨v₁, x⟩` (in the `toLp` model). -/

theorem constraint_eq_inner (v₁ x : V → ℂ) :
    (∑ u, (star v₁ u) * x u)
      = inner ℂ (toLp 2 v₁ : EuclideanSpace ℂ V) (toLp 2 x : EuclideanSpace ℂ V) := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Pi.star_apply]; ring

/-- An eigenvector with eigenvalue `0` is a null vector (`A *ᵥ ofLp vⱼ = 0`). -/
theorem mulVec_eigenvector_eq_zero (A : Matrix V V ℂ) (hA : A.IsHermitian) (j : V)
    (hj : hA.eigenvalues j = 0) :
    A *ᵥ ofLp (hA.eigenvectorBasis j) = 0 := by
  rw [hA.mulVec_eigenvectorBasis, hj]
  simp

/-! ### A null Rayleigh witness orthogonal to `v₁` when `λ₂ = 0`

When the second-smallest eigenvalue vanishes, both `botVert` and `secondVert`
carry eigenvalue `0`; a suitable combination of them (with a fall-back) is a
nonzero `0`-eigenvector orthogonal to `v₁`. -/
theorem exists_null_witness
    (A : Matrix V V ℂ) (hA : A.IsHermitian) (h : 2 ≤ Fintype.card V)
    (v₁ : V → ℂ) (hv₁ : v₁ ≠ 0) (hbot : A *ᵥ v₁ = 0)
    (hmin : ∀ i, 0 ≤ hA.eigenvalues i)
    (hlam2_zero : hA.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ = 0) :
    ∃ x : V → ℂ, x ≠ 0 ∧ (∑ u, (star v₁ u) * x u = 0) ∧ A *ᵥ x = 0 := by
  set b : V := botVert V h with hb
  set s : V := secondVert V h with hs
  have hbs : b ≠ s := by
    rw [hb, hs, botVert, secondVert]
    intro hc
    have := (eIdx V).symm.injective hc
    have h2 : (⟨Fintype.card V - 1, by omega⟩ : Fin (Fintype.card V))
        = ⟨Fintype.card V - 2, by omega⟩ := this
    have := Fin.mk.injEq .. ▸ h2
    omega
  have heb : hA.eigenvalues b = 0 := by
    rw [hb, botVert, eigenvalues_eq_eigenvalues₀, Equiv.apply_symm_apply]
    exact eigenvalues₀_last_eq_zero A hA h v₁ hv₁ hbot hmin
  have hes : hA.eigenvalues s = 0 := by
    rw [hs, eigenvalues_secondVert A hA h]; exact hlam2_zero
  -- inner products of `v₁` with the two bottom eigenvectors
  set vb : EuclideanSpace ℂ V := hA.eigenvectorBasis b with hvb
  set vs : EuclideanSpace ℂ V := hA.eigenvectorBasis s with hvs
  set pb : ℂ := inner ℂ (toLp 2 v₁ : EuclideanSpace ℂ V) vb with hpb
  set ps : ℂ := inner ℂ (toLp 2 v₁ : EuclideanSpace ℂ V) vs with hps
  by_cases hboth : pb = 0 ∧ ps = 0
  · -- fall-back: `v_bot` itself is orthogonal to `v₁`.
    refine ⟨ofLp vb, ?_, ?_, ?_⟩
    · -- nonzero
      have hne := hA.eigenvectorBasis.orthonormal.ne_zero b
      intro hc
      apply hne
      have : (toLp 2 (ofLp vb) : EuclideanSpace ℂ V) = toLp 2 (0 : V → ℂ) := by rw [hc]
      simpa [hvb] using this
    · -- constraint: `⟨v₁, v_bot⟩ = 0`.
      rw [constraint_eq_inner]
      rw [show (toLp 2 (ofLp vb) : EuclideanSpace ℂ V) = vb from rfl, ← hpb, hboth.1]
    · rw [show ofLp vb = ofLp (hA.eigenvectorBasis b) from rfl]
      exact mulVec_eigenvector_eq_zero A hA b heb
  · -- general: `w = ps • v_bot − pb • v_s` is nonzero, `0`-eigen, and `⊥ v₁`.
    set w : EuclideanSpace ℂ V := ps • vb - pb • vs with hw
    refine ⟨ofLp w, ?_, ?_, ?_⟩
    · -- nonzero: `(ps, pb) ≠ 0` and `vb, vs` orthonormal independent.
      intro hc
      have hw0 : w = 0 := by
        have : (toLp 2 (ofLp w) : EuclideanSpace ℂ V) = toLp 2 (0 : V → ℂ) := by rw [hc]
        simpa using this
      have hite := orthonormal_iff_ite (𝕜 := ℂ) |>.mp hA.eigenvectorBasis.orthonormal
      -- pair with `vb`: `ps = 0`.
      have hpsz : ps = 0 := by
        have hp := congrArg (fun z => inner ℂ z vb) hw0
        simp only [inner_zero_left] at hp
        rw [hw, inner_sub_left, inner_smul_left, inner_smul_left, hvb, hvs, hite b b,
          hite s b, if_pos rfl, if_neg (Ne.symm hbs)] at hp
        simpa using hp
      have hpbz : pb = 0 := by
        have hp := congrArg (fun z => inner ℂ z vs) hw0
        simp only [inner_zero_left] at hp
        rw [hw, inner_sub_left, inner_smul_left, inner_smul_left, hvb, hvs, hite b s,
          hite s s, if_neg hbs, if_pos rfl] at hp
        simpa using hp
      exact hboth ⟨hpbz, hpsz⟩
    · -- constraint: `⟨v₁, w⟩ = ps ⟨v₁,vb⟩ − pb ⟨v₁,vs⟩ = ps·pb − pb·ps = 0`.
      rw [constraint_eq_inner, show (toLp 2 (ofLp w) : EuclideanSpace ℂ V) = w from rfl, hw,
        inner_sub_right, inner_smul_right, inner_smul_right, ← hpb, ← hps]
      ring
    · -- `0`-eigen: `A *ᵥ (ps•v_bot − pb•v_s) = ps·0 − pb·0 = 0`.
      rw [show ofLp w = ps • ofLp vb - pb • ofLp vs from by rw [hw, ofLp_sub, ofLp_smul, ofLp_smul]]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
        show ofLp vb = ofLp (hA.eigenvectorBasis b) from rfl,
        show ofLp vs = ofLp (hA.eigenvectorBasis s) from rfl,
        mulVec_eigenvector_eq_zero A hA b heb, mulVec_eigenvector_eq_zero A hA s hes]
      simp

/-- The eigencoordinate `⟨vⱼ, v₁⟩` of a null vector `v₁` vanishes whenever the
eigenvalue `λⱼ` is nonzero (the null vector lives in the `0`-eigenspace). -/
theorem eigencoord_null_eq_zero
    (A : Matrix V V ℂ) (hA : A.IsHermitian)
    (v₁ : V → ℂ) (hbot : A *ᵥ v₁ = 0) (j : V) (hj : hA.eigenvalues j ≠ 0) :
    inner ℂ (hA.eigenvectorBasis j) (toLp 2 v₁ : EuclideanSpace ℂ V) = 0 := by
  set y₁ : EuclideanSpace ℂ V := toLp 2 v₁ with hy₁
  set d : V → ℂ := fun i => inner ℂ (hA.eigenvectorBasis i) y₁ with hd
  have hexp : y₁ = ∑ i, d i • hA.eigenvectorBasis i := by
    conv_lhs => rw [← hA.eigenvectorBasis.sum_repr y₁]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA.eigenvectorBasis.repr_apply_apply]
  have hAexp : (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) = 0 := by
    have hmv : A *ᵥ ofLp y₁
        = ofLp (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) := by
      have hofy : ofLp y₁ = ∑ i, d i • ofLp (hA.eigenvectorBasis i) := by
        rw [congrArg ofLp hexp, ofLp_sum]; rfl
      rw [hofy, Matrix.mulVec_sum, ofLp_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, mul_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ), ofLp_smul]
      rfl
    have hofy : ofLp y₁ = v₁ := by rw [hy₁, ofLp_toLp]
    rw [hofy, hbot] at hmv
    have : ofLp (0 : EuclideanSpace ℂ V)
        = ofLp (∑ i, (d i * (hA.eigenvalues i : ℂ)) • hA.eigenvectorBasis i) := by
      rw [ofLp_zero, ← hmv]
    exact (ofLp_injective (p := 2) this).symm
  have hcoord : d j * (hA.eigenvalues j : ℂ) = 0 := by
    have hinner := congrArg (fun z => inner ℂ z (hA.eigenvectorBasis j)) hAexp
    simp only at hinner
    rw [hA.eigenvectorBasis.orthonormal.inner_left_fintype, inner_zero_left] at hinner
    have := congrArg (starRingEnd ℂ) hinner
    rwa [starRingEnd_self_apply, map_zero] at this
  have hne : (hA.eigenvalues j : ℂ) ≠ 0 := by exact_mod_cast hj
  exact (mul_eq_zero.mp hcoord).resolve_right hne

/-! ### THE RESIDUAL: codimension-`1` Courant–Fischer -/

/-- **Abstract codimension-`1` Courant–Fischer for a PSD Hermitian matrix with a
known null vector.**  The constrained Rayleigh infimum over `v₁^⊥` equals the
second-smallest eigenvalue `eigenvalues₀ ⟨card − 2, _⟩`.

`≥` is the convex-combination lower bound (every constrained Rayleigh quotient is
`≥ λ₂`, since the bottom eigencoordinate is killed when `λ₂ > 0`, and the bound is
vacuous `≥ 0` when `λ₂ = 0`); `≤` is the explicit eigenvector witness
`x = v₂` (`secondVert`), which is automatically orthogonal to `v₁` (distinct
eigenspaces when `λ₂ > 0`; otherwise the witness is a `0`-eigenvector orthogonal
to `v₁`). -/
theorem inf_rayleighSetMat_eq_secondEigenvalue₀
    (A : Matrix V V ℂ) (hA : A.IsHermitian) (h : 2 ≤ Fintype.card V)
    (v₁ : V → ℂ) (hv₁ : v₁ ≠ 0)
    (hbot : A *ᵥ v₁ = 0)
    (hmin : ∀ i, 0 ≤ hA.eigenvalues i) :
    sInf (rayleighSetMat A v₁) = hA.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ := by
  set lam2 : ℝ := hA.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ with hlam2
  have hbdd := bddBelow_rayleighSetMat A hA hmin v₁
  -- `lam2 ≥ 0`.
  have hlam2_nonneg : 0 ≤ lam2 := by
    rw [hlam2, ← eigenvalues_secondVert A hA h]; exact hmin _
  -- ## `≥` : `lam2` lower-bounds every Rayleigh quotient on `v₁^⊥`.
  have hge : ∀ r ∈ rayleighSetMat A v₁, lam2 ≤ r := by
    rintro r ⟨x, hx, hortho, rfl⟩
    have hDpos : 0 < ∑ u, ‖x u‖ ^ 2 := normSq_pos_of_ne_zero x hx
    rw [le_div_iff₀ hDpos, hermitianForm_re_eq_sum A hA x, normSq_eq_sum A hA x,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    -- termwise `lam2 * ‖cᵢ‖² ≤ λᵢ * ‖cᵢ‖²`.
    rcases eq_or_lt_of_le hlam2_nonneg with hzero | hpos
    · -- `lam2 = 0`: bound is `0 ≤ λᵢ ‖cᵢ‖²`.
      rw [← hzero, zero_mul]
      exact mul_nonneg (hmin i) (by positivity)
    · -- `lam2 > 0`: bottom eigenvalue is simple; the bottom coordinate vanishes.
      by_cases hib : i = botVert V h
      · -- bottom term: `‖c_b‖² = 0` by the constraint.
        have hczero : inner ℂ (hA.eigenvectorBasis (botVert V h))
            (toLp 2 x : EuclideanSpace ℂ V) = 0 :=
          botCoord_eq_zero_of_constraint A hA h v₁ hv₁ hbot hmin (by rw [← hlam2]; exact hpos)
            x hortho
        rw [hib, hczero]; simp
      · -- non-bottom term: `lam2 ≤ λᵢ`.
        have hle : lam2 ≤ hA.eigenvalues i := by
          rw [hlam2]; exact secondEigenvalue_le_of_ne_bot A hA h i hib
        exact mul_le_mul_of_nonneg_right hle (by positivity)
  -- ## A member of the set with value `lam2` (gives both `≤` and nonemptiness).
  have hmem : lam2 ∈ rayleighSetMat A v₁ := by
    by_cases hpos : 0 < lam2
    · -- Case B: witness `x = v₂` (`secondVert`); it is `⊥ v₁` since `λ₂ > 0`.
      set s : V := secondVert V h with hs
      set xs : V → ℂ := ofLp (hA.eigenvectorBasis s) with hxs
      have hes : hA.eigenvalues s ≠ 0 := by
        rw [hs, eigenvalues_secondVert A hA h, ← hlam2]; exact ne_of_gt hpos
      have hxs_ne : xs ≠ 0 := by
        rw [hxs]
        have hne := hA.eigenvectorBasis.orthonormal.ne_zero s
        intro hc
        apply hne
        have : (toLp 2 (ofLp (hA.eigenvectorBasis s)) : EuclideanSpace ℂ V) = toLp 2 0 := by rw [hc]
        simpa using this
      -- constraint: `⟨v_s, v₁⟩ = 0` because `λ_s ≠ 0`.
      have hortho : ∑ u, (star v₁ u) * xs u = 0 := by
        have hcs := eigencoord_null_eq_zero A hA v₁ hbot s hes
        rw [hxs, constraint_eq_inner,
          show (toLp 2 (ofLp (hA.eigenvectorBasis s)) : EuclideanSpace ℂ V)
            = hA.eigenvectorBasis s from rfl,
          ← inner_conj_symm, hcs, map_zero]
      have hval : (star xs ⬝ᵥ (A *ᵥ xs)).re / ∑ u, ‖xs u‖ ^ 2 = lam2 := by
        rw [hxs, rayleigh_eigenvector A hA s, hs, eigenvalues_secondVert A hA h]
      exact ⟨xs, hxs_ne, hortho, hval.symm⟩
    · -- Case A: `lam2 = 0`; a `0`-eigenvector orthogonal to `v₁` realises `0`.
      push_neg at hpos
      have hlam2_zero : lam2 = 0 := le_antisymm hpos hlam2_nonneg
      obtain ⟨x, hxne, hxor, hxnull⟩ := exists_null_witness A hA h v₁ hv₁ hbot hmin hlam2_zero
      have hval : (star x ⬝ᵥ (A *ᵥ x)).re / ∑ u, ‖x u‖ ^ 2 = lam2 := by
        rw [hxnull, hlam2_zero]; simp
      exact ⟨x, hxne, hxor, hval.symm⟩
  -- combine: `sInf ≤ lam2` (witness) and `lam2 ≤ sInf` (lower bound).
  exact le_antisymm (csInf_le hbdd hmem) (le_csInf ⟨lam2, hmem⟩ hge)

end CourantFischer
end Graphplay
