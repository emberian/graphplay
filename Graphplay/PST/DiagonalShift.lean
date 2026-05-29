/-
# Graphplay.PST.DiagonalShift

**PST/CTQW amplitudes are invariant under diagonal (scalar) shifts of the
Hamiltonian.**

The continuous-time quantum walk evolves by `U(τ) = exp(-iτ A)`.  Adding a
scalar multiple `d · I` of the identity to the Hamiltonian only multiplies the
evolution operator by a *global phase*:

  `exp(-iτ (A + d·I)) = e^{-iτ d} · exp(-iτ A)`

because `A` and `d·I` commute and `exp` of a scalar multiple of the identity is
a scalar multiple of the identity.  When `d` is real the phase `e^{-iτ d}` has
modulus `1`, so every Born-rule modulus `‖U(τ) j i‖` is unchanged; in
particular the off-diagonal moduli (which control PST / fractional revival) are
identical for `A` and `A + d·I`.

This resolves the loopless obstruction in
`Graphplay.Dowsing.BundlePSTLift`: the symmetric quotient `symmQuotient` of an
equitable partition is Hermitian but generally has *nonzero diagonal* (the
intra-cell mass / regularity degree), so it is not directly a `WeightedGraph`.
Subtracting its own diagonal `diagonal (symmQuotient.diag)` zeroes the diagonal
(yielding a genuine loopless Hermitian `WeightedGraph`) and, since the diagonal
of a Hermitian matrix is real, only shifts the Hamiltonian by a real diagonal
— but the quotient diagonal is constant per cell only in the regular case; the
fully general statement is the per-scalar shift proved here, which the bundle
lift applies cellwise after the regularity normalization.

References: the pseudo-equitable theory of arXiv:2411.09157; the diagonal-shift
invariance is folklore (Bachman–Tamon arXiv:1108.0339, Godsil
"State transfer on graphs").
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Graphplay.Weighted
import Graphplay.Equitable

open scoped Matrix
open NormedSpace

universe u v

namespace Graphplay

variable {I : Type u} [Fintype I] [DecidableEq I]

/-! ## 1. Exponential of a diagonal-shifted matrix factors as a global phase. -/

omit [Fintype I] in
/-- `c • (1 : Matrix I I ℂ)` is the diagonal matrix with constant entry `c`. -/
theorem smul_one_eq_diagonal (c : ℂ) :
    c • (1 : Matrix I I ℂ) = Matrix.diagonal (fun _ => c) := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp

/-- The matrix exponential of `c • (1 : Matrix I I ℂ)` is the scalar
`NormedSpace.exp c` times the identity.  Uses `Matrix.exp_diagonal`. -/
theorem exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix I I ℂ)) = NormedSpace.exp c • (1 : Matrix I I ℂ) := by
  rw [smul_one_eq_diagonal, Matrix.exp_diagonal, smul_one_eq_diagonal]
  congr 1
  funext i
  rw [Pi.exp_def]

/-- **Diagonal-shift factorization.**  For any `M : Matrix I I ℂ`, scalar
`d : ℂ`, and time `τ`,

  `exp(-(iτ) • (M + d•1)) = e^{-iτd} • exp(-(iτ) • M)`,

i.e. shifting the Hamiltonian by `d•I` multiplies the evolution by the global
phase `e^{-iτd}`.

The proof: `M` and `d•1` commute (the identity is central), so
`exp_add_of_commute` splits the exponential; the `d•1` factor is a scalar
exponential by `exp_smul_one`. -/
theorem exp_add_smul_one (M : Matrix I I ℂ) (d : ℂ) (τ : ℂ) :
    NormedSpace.exp (-(Complex.I * τ) • (M + d • (1 : Matrix I I ℂ)))
      = NormedSpace.exp (-(Complex.I * τ * d)) •
          NormedSpace.exp (-(Complex.I * τ) • M) := by
  -- Distribute the scalar over the sum.
  have hsmul : (-(Complex.I * τ)) • (M + d • (1 : Matrix I I ℂ))
      = (-(Complex.I * τ)) • M + (-(Complex.I * τ * d)) • (1 : Matrix I I ℂ) := by
    rw [smul_add, smul_smul]
    congr 2
    ring
  rw [hsmul]
  -- The two summands commute: `(c • 1)` is central.
  have hcomm : Commute ((-(Complex.I * τ)) • M)
      ((-(Complex.I * τ * d)) • (1 : Matrix I I ℂ)) := by
    refine Commute.smul_right ?_ _
    refine Commute.smul_left ?_ _
    exact (Commute.one_right M)
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one]
  -- Goal: `X * (s • 1) = s • X`.
  rw [Matrix.mul_smul, Matrix.mul_one]

/-! ## 2. The global phase is a unit modulus, so off-diagonal moduli match. -/

/-- For real `d`, the global phase `e^{-iτd}` has modulus one. -/
theorem norm_exp_neg_I_mul (τ d : ℝ) :
    ‖NormedSpace.exp (-(Complex.I * (τ : ℂ) * (d : ℂ)))‖ = 1 := by
  rw [← Complex.exp_eq_exp_ℂ]
  -- `-(I·τ·d) = (-(τ*d)) · I`, a real multiple of `I`.
  rw [show -(Complex.I * (τ : ℂ) * (d : ℂ)) = ((-(τ * d) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Diagonal-shift modulus invariance.**  For real `d`, every entry of the
shifted evolution operator has the *same modulus* as the corresponding entry of
the unshifted one:

  `‖exp(-(iτ)•(M + d•1)) j i‖ = ‖exp(-(iτ)•M) j i‖`.

(The statement holds for all `i, j`, including the diagonal, because the shift
is a pure global phase.  The `i ≠ j` case is the one relevant to PST.) -/
theorem norm_exp_shifted_entry_eq (M : Matrix I I ℂ) (τ d : ℝ) (i j : I) :
    ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • (M + (d : ℂ) • (1 : Matrix I I ℂ)))) j i‖
      = ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • M)) j i‖ := by
  rw [exp_add_smul_one M (d : ℂ) (τ : ℂ)]
  -- The shifted matrix is `phase • (unshifted)`; read off entry `(j, i)`.
  rw [Matrix.smul_apply, norm_smul, norm_exp_neg_I_mul, one_mul]

/-! ## 3. The diagonal-zeroed (loopless) symmetric quotient.

A Hermitian matrix `M` (such as `EquitablePartition.symmQuotient`) generally has
nonzero diagonal, so it is not directly a `WeightedGraph`.  We subtract its own
diagonal `diagonal M.diag` to obtain a *loopless* Hermitian matrix.  When the
diagonal is the *constant* scalar `d` (the regular-fiber case, where every cell
shares the same intra-cell regularity degree), the subtraction is the scalar
shift `-(d • 1)`, so by §2 all off-diagonal CTQW moduli are unchanged — this is
exactly what lets `BundlePSTLift` wrap the quotient as a `WeightedGraph` without
the loopless `sorry`.
-/

omit [Fintype I] in
/-- The diagonal matrix carved out of a Hermitian matrix is itself Hermitian
(its diagonal entries are self-adjoint). -/
theorem isHermitian_diagonal_diag {M : Matrix I I ℂ} (hM : M.IsHermitian) :
    (Matrix.diagonal M.diag).IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  rw [Matrix.diag_apply, isSelfAdjoint_iff]
  exact hM.apply i i

/-- **Loopless symmetric quotient.**  Given a Hermitian matrix `M`, subtract its
own diagonal to obtain a genuine loopless Hermitian `WeightedGraph` on `I`.
Applied to `EquitablePartition.symmQuotient` this discharges the `loopless`
field of the bundle quotient. -/
noncomputable def looplessOfHermitian (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    WeightedGraph I where
  adj := M - Matrix.diagonal M.diag
  herm := hM.sub (isHermitian_diagonal_diag hM)
  loopless := by
    intro i
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.diag_apply, sub_self]

/-- Off-diagonal entries of `looplessOfHermitian M hM` agree with those of `M`:
the diagonal subtraction only touches the diagonal. -/
theorem looplessOfHermitian_apply_off {M : Matrix I I ℂ} (hM : M.IsHermitian)
    {i j : I} (hij : i ≠ j) :
    (looplessOfHermitian M hM).adj i j = M i j := by
  show (M - Matrix.diagonal M.diag) i j = M i j
  rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, sub_zero]

/-- The loopless matrix is the original shifted by `-(d • 1)` *when the diagonal
is the constant scalar `d`*.  This is the bridge to the global-phase lemma. -/
theorem looplessOfHermitian_eq_sub_smul_one {M : Matrix I I ℂ} (hM : M.IsHermitian)
    {d : ℂ} (hdiag : ∀ i, M.diag i = d) :
    (looplessOfHermitian M hM).adj = M + (-d) • (1 : Matrix I I ℂ) := by
  show M - Matrix.diagonal M.diag = M + (-d) • (1 : Matrix I I ℂ)
  rw [smul_one_eq_diagonal]
  have : Matrix.diagonal M.diag = Matrix.diagonal (fun _ : I => d) := by
    congr 1; funext i; exact hdiag i
  rw [this]
  rw [sub_eq_add_neg, ← Matrix.diagonal_neg]

/-- **PST modulus invariance for the loopless quotient (constant-diagonal /
regular case).**  If the Hermitian matrix `M` has constant real diagonal
`d : ℝ`, then for `i ≠ j` the off-diagonal CTQW modulus of the loopless,
diagonal-zeroed matrix `looplessOfHermitian M` equals that of `M` itself:

  `‖exp(-(iτ)•(looplessOfHermitian M).adj) j i‖ = ‖exp(-(iτ)•M) j i‖`.

Hence wrapping the symmetric quotient as a loopless `WeightedGraph` preserves
all PST / fractional-revival moduli.  The constant-real-diagonal hypothesis is
exactly the regular-fiber situation of the bundle lift, where every cell shares
the same intra-cell regularity degree. -/
theorem pst_modulus_eq {M : Matrix I I ℂ} (hM : M.IsHermitian)
    {d : ℝ} (hdiag : ∀ i, M.diag i = (d : ℂ)) (τ : ℝ) (i j : I) :
    ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • (looplessOfHermitian M hM).adj)) j i‖
      = ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • M)) j i‖ := by
  -- The loopless matrix is `M + (-d) • 1`, a scalar shift; apply §2.
  rw [looplessOfHermitian_eq_sub_smul_one hM hdiag]
  -- `norm_exp_shifted_entry_eq` is stated with shift `(c : ℝ) • 1`; here `c = -d`.
  have := norm_exp_shifted_entry_eq M τ (-d) i j
  -- align the casts `((-d : ℝ) : ℂ) = (-d : ℂ)`.
  rw [show ((-d : ℝ) : ℂ) = (-(d : ℂ)) by push_cast; ring] at this
  -- `M + (-(d:ℂ)) • 1` is the loopless adjacency.
  exact this

end Graphplay
