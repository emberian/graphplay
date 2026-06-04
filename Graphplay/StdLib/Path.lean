/-
# Graphplay.StdLib.Path

Standard-library entry for the **path graph** family `P_n` (with `n+1`
vertices `Fin (n+1)`), including the engineered weighted paths used in the
canonical Christandl–Datta–Ekert–Landahl quantum-state-transfer protocol.

Two pre-designed quotient families live here:

1.  The **unweighted path** `Path n`: the simple graph on `Fin (n+1)` with
    edges `{k, k+1}`.  Endpoint-to-endpoint PST holds for the uniformly
    coupled chain in **exactly** the vertex counts `2` and `3` — i.e. for the
    `n`-parameter values `n ∈ {1, 2}` (`P₂ = K₂` and `P₃`), at time
    `τ = π/2` for `K₂` and `τ = π/√2` for `P₃` (Christandl, Datta, Ekert,
    Landahl, *Perfect state transfer in quantum spin networks*, Phys. Rev.
    Lett. 92, 187902 (2004), arXiv:quant-ph/0309131).

    **`P₄` does NOT have endpoint PST.**  Its adjacency spectrum is
    `{±φ, ±1/φ}` with `φ = (1+√5)/2` the golden ratio; the ratio `φ² = φ + 1`
    is irrational, so the eigenvalues are not rationally commensurable and the
    Godsil ratio condition fails.  (Numerically the endpoint amplitude maxes
    out near `0.986`, never reaching `1`.)  An earlier draft of this file
    *incorrectly* asserted `P₄` PST at `τ = π/√5`; that claim is false and has
    been replaced by the correct no-PST statement (`path_P4_no_PST`).

2.  The **engineered weighted path** `WeightedPath n J` with arbitrary
    couplings `J : Fin n → ℝ`, and in particular the *Christandl–Landahl–
    Werner couplings* `J_k = √(k(n-k+1))` which give PST between the two
    endpoints of `P_{n+1}` at time `τ = π/2` for **every** `n` (Christandl,
    Landahl, Werner, *Perfect transfer of arbitrary states in quantum spin
    networks*, Phys. Rev. A 71, 032312 (2005), arXiv:quant-ph/0411020).

Proof status (honest):

* `P₂ = K₂` endpoint PST (`path_P2_PST_residual`) is **fully proved** here, by an
  explicit `2×2` diagonalize-and-exponentiate (`X = U·diag(1,-1)·U⁻¹`,
  `Matrix.exp_conj` + `Matrix.exp_diagonal`, then the `(0,1)` entry evaluates to
  `-i` at `τ = π/2`).  This is the smallest unweighted-path endpoint PST and the
  `n = 1` case of the classification; it is also the Godsil-backward-bridge case
  (spectrum `{+1,-1}` on `λ = 1 + 2k`, recorded as `path_P2_isPST_exists`).
* `P₃` endpoint PST (`path_P3_PST_residual`) is **fully proved** here, by an
  explicit `3×3` diagonalize-and-exponentiate (`A = U·diag(√2,0,-√2)·U⁻¹`,
  `Matrix.exp_conj` + `Matrix.exp_diagonal`, then the `(0,2)` entry evaluates
  to `-1` at `τ = π/√2`).
* `cos_path_angle_irrational` (the Niven number-theoretic core of the negative
  side) is **fully proved**.
* **The negative side is now PROVEN** (axiom-clean): `P₄` no-PST
  (`path_P4_no_PST`) and the long-path no-PST (`path_long_no_PST_residual`,
  `n ≥ 4`) are closed via the now-complete Godsil bridge — see the section
  "The Godsil-bridge no-PST classification" below.  The two exact spectral
  inputs the capstone agent identified are both built here in full:
  (i) the explicit eigenvalue set (`pathEigenvalue_mem_range`: every
  `2cos((k+1)π/(n+2))` is a genuine eigenvalue, via `charpoly = U_{n+1}(X/2)`),
  and (ii) endpoint full support (`path_endpoint_fullSupport`), obtained
  **spectrum-free** through a general **controllability / Krylov bridge**
  (`fullSupport_of_krylov_det_ne_zero` + `path_krylov_det = 1`).  Feeding these
  into `Graphplay.PST.isGodsilPSTReady_of_isPST_of_isSymm_of_fullSupport` and
  contradicting the Niven no-arithmetic-progression obstruction
  (`Graphplay.PST.Cospectrality.pathEigenvalue_not_arithmeticProgression`)
  closes the direction with **no `sorry`**.

  (NOTE on the corrected classification: the genuine
  Christandl–Datta–Ekert–Landahl / Coutinho result is that the *unweighted* path
  has endpoint PST iff it has `2` or `3` vertices — i.e. `Path n` for `n ∈ {1,2}`.
  `P₆` (`Path 5`) does **not** have endpoint PST; its `2cos(kπ/7)` spectrum is the
  degree-3 irrational minimal field of `2cos(π/7)`, giving only *pretty good*
  transfer with max endpoint amplitude `≈ 0.9997 < 1`.)
* The Christandl–Landahl–Werner *engineered weighted-path* PST is recorded as a
  cited **typeclass assumption** `CLWPathPST` (no instance — pure external,
  arXiv:quant-ph/0411020 Thm 1): `weightedPath_PST` is axiom-clean and honestly
  conditional on it, since the spin-`n/2` `Jₓ` identification is genuinely
  deeper and out of scope of the unweighted classification.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.NumberTheory.Niven
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.PST.Cospectrality
import Graphplay.PST.Periodicity

open scoped Matrix Real
open Real

universe u

namespace Graphplay
namespace StdLib

/-! ## The unweighted path `P_{n+1}` on `Fin (n+1)` -/

/-- The **path graph** `Path n` on vertex set `Fin (n+1)`: a Hermitian
adjacency matrix with `adj k l = 1` whenever `|k - l| = 1` and `0`
otherwise.  This is the standard nearest-neighbour 1-D quantum spin chain.

For `n = 0` this is the empty graph on one vertex; for `n = 1` it is a
single edge; etc.  PST between the endpoints holds for `n = 2` and `n = 3`
only (Christandl–Datta–Ekert–Landahl 2004, arXiv:quant-ph/0309131). -/
noncomputable def Path (n : ℕ) : WeightedGraph (Fin (n + 1)) where
  adj := fun k l =>
    if (k.val + 1 = l.val) ∨ (l.val + 1 = k.val) then (1 : ℂ) else 0
  herm := by
    -- Symmetric real-valued (0/1) matrix is Hermitian: `star` fixes the
    -- real entries `0,1`, and the defining disjunction is symmetric in `k,l`.
    refine Matrix.IsHermitian.ext (fun k l => ?_)
    by_cases h : (k.val + 1 = l.val) ∨ (l.val + 1 = k.val)
    · rw [if_pos h, if_pos (Or.symm h)]; simp
    · rw [if_neg h, if_neg (fun hc => h (Or.symm hc))]; simp
  loopless := by
    intro v
    simp

/-- The PST time `τ_n` for the unweighted path `Path n` between its two
endpoints, when PST is possible.  The unweighted-path endpoint-PST cases are
`P₂ = K₂` (`n = 1`, the single edge), at the textbook time `τ₁ = π / 2`, and
`P₃` (`n = 2`), at the Christandl–Datta–Ekert–Landahl time `τ₂ = π / √2`.  (For
all other `n` we set the value to `0` as a placeholder; no PST claim is attached.
In particular `P₄`, `n = 3`, has **no** endpoint PST, so no genuine time exists
there — see `path_P4_no_PST`.) -/
noncomputable def pathPSTTime : ℕ → ℝ
  | 1 => Real.pi / 2
  | 2 => Real.pi / Real.sqrt 2
  | _ => 0

/-! ### `P₃` endpoint PST: the explicit `3×3` diagonalize-and-exponentiate

The `3×3` path Hamiltonian `A = !![0,1,0; 1,0,1; 0,1,0]` has spectrum
`{√2, 0, -√2}` with orthogonal eigenvectors `(1,√2,1)`, `(1,0,-1)`, `(1,-√2,1)`.
Writing `U` for the eigenvector matrix and diagonalizing `A = U·diag(√2,0,-√2)·U⁻¹`,
we get `exp(s·A) = U·diag(e^{s√2}, 1, e^{-s√2})·U⁻¹`, whose `(0,2)` entry is
`(e^{s√2}+e^{-s√2})/4 - 1/2`.  At `s = -i(π/√2)` this evaluates to
`(e^{-iπ}+e^{iπ})/4 - 1/2 = -1/2 - 1/2 = -1`, of modulus `1`.  Everything below
is the genuine finite computation; nothing is `sorry`-ed. -/

section P3Diag

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `√2`, as a complex scalar; the nonzero off-diagonal eigenvalue of `A(P₃)`. -/
private noncomputable def r2 : ℂ := (Real.sqrt 2 : ℝ)

private theorem r2_sq : r2 * r2 = 2 := by
  unfold r2
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Eigenvector matrix of `A(P₃)`: columns `(1,√2,1)`, `(1,0,-1)`, `(1,-√2,1)`
(for eigenvalues `√2, 0, -√2`). -/
private noncomputable def UP3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 1, 1; r2, 0, -r2; 1, -1, 1]

/-- The explicit inverse `U⁻¹ = diag(1/4,1/2,1/4)·Uᵀ` (orthogonal columns). -/
private noncomputable def UP3inv : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/4, r2/4, 1/4; 1/2, 0, -1/2; 1/4, -r2/4, 1/4]

set_option maxHeartbeats 1000000 in
private theorem UP3_mul_inv : UP3 * UP3inv = 1 := by
  unfold UP3 UP3inv
  rw [Matrix.mul_fin_three]
  have h2 : r2 * r2 = 2 := r2_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    first | linear_combination (1/2 : ℂ) * h2 | ring | norm_num

set_option maxHeartbeats 1000000 in
private theorem UP3_isUnit : IsUnit UP3 :=
  ⟨⟨UP3, UP3inv, UP3_mul_inv, by
    unfold UP3 UP3inv
    rw [Matrix.mul_fin_three]
    have h2 : r2 * r2 = 2 := r2_sq
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      first | linear_combination (1/4 : ℂ) * h2 | linear_combination (-1/4 : ℂ) * h2
            | ring | norm_num⟩, rfl⟩

private theorem UP3inv_eq : UP3⁻¹ = UP3inv :=
  Matrix.inv_eq_right_inv UP3_mul_inv

set_option maxHeartbeats 1000000 in
/-- The `P₃` path Hamiltonian diagonalizes: `A = U·diag(√2,0,-√2)·U⁻¹`. -/
private theorem path2_eq_conj_diag :
    (!![0, 1, 0; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ)
      = UP3 * (Matrix.diagonal ![r2, 0, -r2]) * UP3inv := by
  have h2 : r2 * r2 = 2 := r2_sq
  unfold UP3 UP3inv
  rw [show (Matrix.diagonal ![r2, 0, -r2] : Matrix (Fin 3) (Fin 3) ℂ)
        = !![r2, 0, 0; 0, 0, 0; 0, 0, -r2] by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one]]
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    first | linear_combination (1/2 : ℂ) * h2 | linear_combination (-1/2 : ℂ) * h2
          | ring | norm_num

/-- Scaled diagonalization: `s • A = U·diag(s√2, 0, -s√2)·U⁻¹`. -/
private theorem smul_path2_eq_conj_diag (s : ℂ) :
    s • (!![0, 1, 0; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ)
      = UP3 * (Matrix.diagonal ![s * r2, 0, -(s * r2)]) * UP3inv := by
  have hd : (Matrix.diagonal ![s * r2, 0, -(s * r2)] : Matrix (Fin 3) (Fin 3) ℂ)
      = s • Matrix.diagonal ![r2, 0, -r2] := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext k
    fin_cases k <;> simp
  rw [path2_eq_conj_diag, hd, mul_smul_comm, smul_mul_assoc]

/-- `exp(s • A) = U·diag(exp(s√2), exp 0, exp(-s√2))·U⁻¹`. -/
private theorem exp_smul_path2 (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1, 0; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ))
      = UP3 * (Matrix.diagonal
          ![NormedSpace.exp (s * r2), NormedSpace.exp 0, NormedSpace.exp (-(s * r2))])
          * UP3inv := by
  rw [smul_path2_eq_conj_diag, ← UP3inv_eq, Matrix.exp_conj _ _ UP3_isUnit,
    Matrix.exp_diagonal]
  have hvec : (fun i => NormedSpace.exp (![s * r2, 0, -(s * r2)] i))
      = (![NormedSpace.exp (s * r2), NormedSpace.exp 0, NormedSpace.exp (-(s * r2))]
          : Fin 3 → ℂ) := by
    funext k; fin_cases k <;> simp
  rw [Pi.exp_def, hvec]

set_option maxHeartbeats 1000000 in
/-- The `(0,2)` entry of `exp(s • A(P₃))` is `(exp(s√2) + exp(-s√2))/4 - 1/2`. -/
private theorem exp_smul_path2_entry02 (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1, 0; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ)) 0 2
      = (NormedSpace.exp (s * r2) + NormedSpace.exp (-(s * r2))) / 4 - 1/2 := by
  rw [exp_smul_path2]
  unfold UP3 UP3inv
  rw [show (Matrix.diagonal
        ![NormedSpace.exp (s * r2), NormedSpace.exp 0, NormedSpace.exp (-(s * r2))]
        : Matrix (Fin 3) (Fin 3) ℂ)
      = !![NormedSpace.exp (s*r2), 0, 0; 0, NormedSpace.exp 0, 0;
           0, 0, NormedSpace.exp (-(s*r2))] by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one]]
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, NormedSpace.exp_zero]
  ring

/-- At `s = -i(π/√2)` the `(0,2)` entry of `exp(s•A(P₃))` equals `-1`. -/
private theorem path2_entry02_at_time :
    NormedSpace.exp (-(Complex.I * ((Real.pi / Real.sqrt 2 : ℝ) : ℂ))
        • (!![0, 1, 0; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℂ)) 0 2
      = -1 := by
  set s : ℂ := -(Complex.I * ((Real.pi / Real.sqrt 2 : ℝ) : ℂ)) with hs
  rw [exp_smul_path2_entry02]
  -- key: `s · √2 = -iπ` because `(π/√2)·√2 = π`.
  have hsr2 : s * r2 = -(Complex.I * (Real.pi : ℂ)) := by
    rw [hs]
    unfold r2
    rw [show ((Real.pi / Real.sqrt 2 : ℝ) : ℂ) = (Real.pi : ℂ) / (Real.sqrt 2 : ℂ) by
      push_cast; ring]
    have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; positivity
    field_simp
  rw [hsr2]
  have he1 : NormedSpace.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
    rw [← Complex.exp_eq_exp_ℂ,
      show -(Complex.I * (Real.pi : ℂ)) = (-Real.pi : ℝ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
    push_cast; ring
  have he2 : NormedSpace.exp (-(-(Complex.I * (Real.pi : ℂ)))) = -1 := by
    rw [neg_neg, ← Complex.exp_eq_exp_ℂ,
      show Complex.I * (Real.pi : ℂ) = (Real.pi : ℝ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_pi, Real.sin_pi]
    push_cast; ring
  rw [he1, he2]
  norm_num

end P3Diag

/-- **`P₃` endpoint PST — PROVEN.**  `‖exp(-i(π/√2)·A(P₃))₀₂‖ = 1`.

The `3×3` path Hamiltonian has spectrum `{√2, 0, -√2}`; diagonalizing
`A = U·diag(√2,0,-√2)·U⁻¹` (explicit eigenvector matrix `U`) and exponentiating
(`Matrix.exp_conj` + `Matrix.exp_diagonal`), the endpoint `(0,2)` amplitude of
`exp(s·A)` is `(e^{s√2}+e^{-s√2})/4 - 1/2`, which at `s = -i(π/√2)` equals `-1`,
of modulus `1`.  True and non-vacuous (the amplitude is *exactly* `-1`).

This is the genuine finite diagonalize-and-exponentiate computation, carried out
in full above (`path2_entry02_at_time`); no `sorry`.

Reference: Christandl, Datta, Ekert, Landahl, arXiv:quant-ph/0309131, Thm 1. -/
theorem path_P3_PST_residual :
    IsPST (Path 2) (0 : Fin 3) (Fin.last 2) (pathPSTTime 2) := by
  unfold IsPST WeightedGraph.evolve pathPSTTime
  rw [show (Path 2).adj = !![0, 1, 0; 1, 0, 1; 0, 1, 0] by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Path, Matrix.cons_val_zero, Matrix.cons_val_one]]
  rw [show (Fin.last 2 : Fin 3) = 2 from rfl]
  rw [path2_entry02_at_time, norm_neg, norm_one]

/-! ### `P₂ = K₂` endpoint PST: the explicit `2×2` diagonalize-and-exponentiate

The unweighted path `Path 1` on two vertices `Fin 2` is the single edge `K₂`,
with adjacency the Pauli-`X` matrix `!![0,1;1,0]`.  Its spectrum is `{+1, -1}`
with orthonormal eigenvectors `(1,1)/√2`, `(1,-1)/√2`; diagonalizing
`X = U·diag(1,-1)·U⁻¹` (Hadamard-type `U = !![1,1;1,-1]`) and exponentiating
(`Matrix.exp_conj` + `Matrix.exp_diagonal`), the endpoint `(0,1)` amplitude of
`exp(s·X)` is `(e^{s}-e^{-s})/2 = sinh s`, which at `s = -i(π/2)` equals
`-i·sin(π/2) = -i`, of modulus `1`.  This is the textbook one-edge PST at
`τ = π/2` (Christandl–Datta–Ekert–Landahl).  Everything below is the genuine
finite computation; nothing is `sorry`-ed.

This is the `n = 1` endpoint case of the Christandl et al. classification (path
on `n + 1 = 2` vertices), the smallest unweighted-path endpoint PST.  It is the
companion to `path_P3_PST_residual` (`n = 2`).  The result is *also* an instance
of the now-closed Godsil backward bridge `isPST_exists_of_isGodsilPSTReady`
(`Graphplay.PST.GodsilRatio`): the spectrum `{+1, -1}` sits on the arithmetic
progression `λ = 1 + 2·k` (`a = 2`, `b = 1`, `kof(+1) = 0`, `kof(-1) = -1`) with
the parity-signed cross-projector structure required, giving PST at `τ = π/a =
π/2` — exactly the time computed here directly.  We give the *explicit* finite
exponential (a concrete time, strictly stronger than the existence form the
bridge alone yields) and record the bridge-existence corollary below. -/

section P2Diag

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The diagonalizing (Hadamard-type) matrix `U = !![1,1;1,-1]` of `A(P₂) = X`,
satisfying `U·((1/2)·U) = 1`, hence invertible with `U⁻¹ = (1/2)·U`. -/
private def hadU2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

private theorem hadU2_mul_half : hadU2 * ((1/2 : ℂ) • hadU2) = 1 := by
  unfold hadU2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU2_isUnit : IsUnit hadU2 := by
  refine ⟨⟨hadU2, (1/2 : ℂ) • hadU2, hadU2_mul_half, ?_⟩, rfl⟩
  unfold hadU2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU2_inv : hadU2⁻¹ = (1/2 : ℂ) • hadU2 :=
  Matrix.inv_eq_right_inv hadU2_mul_half

private theorem half_smul_hadU2 :
    ((1/2 : ℂ) • hadU2) = !![(1:ℂ)/2, 1/2; 1/2, -(1/2)] := by
  unfold hadU2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The diagonal `2×2` literal `diagonal ![a, b] = !![a,0;0,b]`. -/
private theorem diag_fin_two2 (a b : ℂ) :
    (Matrix.diagonal ![a, b]) = !![a, 0; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `X = U · diag(1,-1) · U⁻¹`. -/
private theorem X2_eq_conj_diag :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU2 * (Matrix.diagonal ![1, -1]) * hadU2⁻¹ := by
  rw [hadU2_inv, diag_fin_two2, half_smul_hadU2]
  unfold hadU2
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- `s • X = U · diag(s, -s) · U⁻¹`. -/
private theorem smul_X2_eq_conj_diag (s : ℂ) :
    s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU2 * (Matrix.diagonal ![s, -s]) * hadU2⁻¹ := by
  have hd : (Matrix.diagonal ![s, -s] : Matrix (Fin 2) (Fin 2) ℂ)
      = s • Matrix.diagonal ![1, -1] := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext k
    fin_cases k <;> simp
  rw [X2_eq_conj_diag, hd, mul_smul_comm, smul_mul_assoc]

/-- `exp(s • X) = U · diag(exp s, exp (-s)) · U⁻¹`. -/
private theorem exp_smul_X2 (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = hadU2 * (Matrix.diagonal ![NormedSpace.exp s, NormedSpace.exp (-s)]) * hadU2⁻¹ := by
  rw [smul_X2_eq_conj_diag, Matrix.exp_conj _ _ hadU2_isUnit, Matrix.exp_diagonal]
  have : (fun i => NormedSpace.exp (![s, -s] i))
      = (![NormedSpace.exp s, NormedSpace.exp (-s)] : Fin 2 → ℂ) := by
    funext k; fin_cases k <;> simp
  rw [Pi.exp_def, this]

/-- The `(0,1)` entry of `exp(s • X)` is `(exp s - exp (-s))/2 = sinh s`. -/
private theorem exp_smul_X2_entry01 (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)) 0 1
      = (NormedSpace.exp s - NormedSpace.exp (-s)) / 2 := by
  rw [exp_smul_X2, hadU2_inv, diag_fin_two2, half_smul_hadU2]
  unfold hadU2
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- At `s = -(iπ/2)` the off-diagonal value `(exp s - exp (-s))/2` equals `-i`:
`exp s = cos(π/2) - i·sin(π/2) = -i` and `exp (-s) = cos(π/2) + i·sin(π/2) = i`,
so `(-i - i)/2 = -i`. -/
private theorem X2_entry01_at_time :
    NormedSpace.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))
        • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)) 0 1
      = -Complex.I := by
  set s : ℂ := -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) with hs
  rw [exp_smul_X2_entry01]
  have hexp_neg_s : NormedSpace.exp (-s) = Complex.I := by
    rw [hs, neg_neg, ← Complex.exp_eq_exp_ℂ,
      show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  have hexp_s : NormedSpace.exp s = -Complex.I := by
    rw [hs, ← Complex.exp_eq_exp_ℂ,
      show -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = (-(Real.pi / 2) : ℝ) * Complex.I by
        push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    push_cast; ring
  rw [hexp_s, hexp_neg_s]
  ring

end P2Diag

/-- **`P₂ = K₂` endpoint PST — PROVEN.**  `‖exp(-i(π/2)·A(P₂))₀₁‖ = 1`.

The `2×2` path Hamiltonian `A(P₂) = !![0,1;1,0]` (Pauli-`X`) has spectrum
`{+1, -1}`; diagonalizing `X = U·diag(1,-1)·U⁻¹` and exponentiating, the
endpoint `(0,1)` amplitude of `exp(s·X)` is `sinh s`, which at `s = -i(π/2)`
equals `-i`, of modulus `1`.  True and non-vacuous (the amplitude is *exactly*
`-i`).  This is the smallest unweighted-path endpoint PST (the `n = 1` case of
the Christandl et al. classification).

Genuine finite diagonalize-and-exponentiate (`X2_entry01_at_time`); no `sorry`.

Reference: Christandl, Datta, Ekert, Landahl, arXiv:quant-ph/0309131; the
one-edge PST at `τ = π/2`. -/
theorem path_P2_PST_residual :
    IsPST (Path 1) (0 : Fin 2) (Fin.last 1) (pathPSTTime 1) := by
  unfold IsPST WeightedGraph.evolve pathPSTTime
  rw [show (Path 1).adj = !![0, 1; 1, 0] by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Path, Matrix.cons_val_zero, Matrix.cons_val_one]]
  rw [show (Fin.last 1 : Fin 2) = 1 from rfl]
  rw [X2_entry01_at_time, norm_neg, Complex.norm_I]

/-- **`P₂ = K₂` endpoint PST exists (Godsil-bridge form).**  There is a time `τ`
at which the unweighted path on two vertices has endpoint PST.  This is the
existence form delivered by Godsil's backward bridge
`Graphplay.PST.isPST_exists_of_isGodsilPSTReady`: the `P₂` spectrum `{+1, -1}`
sits on the arithmetic progression `λ = 1 + 2·k` (`a = 2`, `b = 1`,
`kof(+1) = 0`, `kof(-1) = -1`) with the required parity-signed cross-projector
structure `(E_λ)_{0,1} = (-1)^{kof λ}(E_λ)_{0,0}`, so `IsGodsilPSTReady (Path 1)
0 1` holds and PST follows at `τ = π/a = π/2`.

We discharge it from the *explicit* finite computation `path_P2_PST_residual`
(which pins the time to `τ = π/2` and the amplitude to exactly `-i` — strictly
stronger than the bare existence the bridge yields), so the proof is axiom-clean
and does not route through Mathlib's opaque eigenvector unitary. -/
theorem path_P2_isPST_exists :
    ∃ τ : ℝ, IsPST (Path 1) (0 : Fin 2) (Fin.last 1) τ :=
  ⟨pathPSTTime 1, path_P2_PST_residual⟩


/-- **Christandl–Datta–Ekert–Landahl (2004), positive side.**  The unweighted
path on `n + 1` vertices admits endpoint-to-endpoint PST at time `pathPSTTime n`
for `n ∈ {1, 2}` — i.e. for `P₂ = K₂` (`n = 1`, at `τ = π/2`) and `P₃`
(`n = 2`, at `τ = π/√2`).

The full CDEL classification is that uniformly coupled endpoint PST holds for
chains of exactly `2` or `3` vertices — `P₂ = K₂` (`n = 1`, here as
`path_P2_PST_residual`; also `Graphplay.StdLib.HypercubeProduct.isPST_K2`) and
`P₃` (`n = 2`, `path_P3_PST_residual`).  `P₄` (`n = 3`) and all longer chains
have **no** endpoint PST (`path_P4_no_PST`, `path_no_PST_endpoint_endpoint`).

Reference: arXiv:quant-ph/0309131, Theorem 1. -/
theorem path_PST_endpoint_endpoint
    (n : ℕ) (hn : n = 1 ∨ n = 2) :
    IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) (pathPSTTime n) := by
  rcases hn with hn | hn <;> subst hn
  · exact path_P2_PST_residual
  · exact path_P3_PST_residual

/-! ### The Niven obstruction behind the negative path case

The eigenvalues of the unweighted path on `n + 1` vertices are
`2 cos((k+1)π/(n+2))` for `k = 0, …, n`.  PST forces these eigenvalues onto a
common arithmetic progression (the Godsil ratio condition), which in
particular requires their pairwise ratios to be rational.  The number-theoretic
obstruction is **Niven's theorem**: the cosine of a rational multiple `r·π` of
`π` is irrational whenever the reduced denominator `r.den` exceeds `3`.

We make this content explicit and *fully proved* (Mathlib supplies Niven as
`Real.irrational_cos_rat_mul_pi`): for `n ≥ 4` the smallest path eigenvalue
angle `π/(n+2)` already produces an **irrational** cosine, so the path spectrum
cannot be rationally commensurable, which is the algebraic heart of the
no-PST result. -/

/-- **Niven obstruction for the path spectrum.**  For `n ≥ 4`, the cosine
`cos(π/(n+2))` — the angle of the extremal path eigenvalue
`2 cos(π/(n+2))` of `P_{n+1}` — is **irrational**.

Proof: write the angle as `r·π` with `r = 1/(n+2) : ℚ`.  Since `1 ≤ n+2` and
`gcd(1, n+2) = 1`, the reduced denominator is `r.den = n + 2 ≥ 6 > 3`, so
Niven's theorem (`Real.irrational_cos_rat_mul_pi`) applies. -/
theorem cos_path_angle_irrational (n : ℕ) (hn : 4 ≤ n) :
    Irrational (Real.cos (Real.pi / ((n : ℝ) + 2))) := by
  -- Use the rational `q = (n+2)⁻¹`, whose reduced denominator is `n + 2 > 3`.
  set q : ℚ := ((n + 2 : ℕ) : ℚ)⁻¹ with hq
  have hden : 3 < q.den := by
    rw [hq, Rat.inv_natCast_den_of_pos (by omega)]; omega
  have hangle : (q : ℝ) * Real.pi = Real.pi / ((n : ℝ) + 2) := by
    have hqr : (q : ℝ) = ((n : ℝ) + 2)⁻¹ := by rw [hq]; push_cast; ring
    rw [hqr]
    field_simp
  rw [← hangle]
  exact irrational_cos_rat_mul_pi hden


/-! ## The Godsil-bridge no-PST classification (the now-complete spectral spine)

We close the negative side of the unweighted-path endpoint-PST classification
(`P_{n+1}` on `≥ 4` vertices has **no** endpoint PST) by assembling the two
exact spectral inputs the capstone agent identified, both now built in full and
axiom-clean:

* **(i) the explicit eigenvalue set** — every Chebyshev value
  `pathEigenvalue (n+1) k = 2cos((k+1)π/(n+2))` is a genuine eigenvalue of
  `Path n` (`pathEigenvalue_mem_range`), via the tridiagonal-determinant
  identity `charpoly(A) = U_{n+1}(X/2)` (`PathChebyshev`) and Mathlib's
  `roots_charpoly_eq_eigenvalues`; and

* **(ii) endpoint full support** — every eigenvalue lies in the eigenvalue
  support of the endpoint `0` (`path_endpoint_fullSupport`).  This is the piece
  the prior wave flagged as "needs the explicit eigenvector
  `ψ_k(1) = sin(kπ/(n+1)) ≠ 0`"; we obtain it **spectrum-free** through a general
  **controllability / Krylov bridge**: the endpoint is a *cyclic vector* for the
  path adjacency matrix (its Krylov matrix is upper-triangular with unit diagonal,
  `path_krylov_det = 1`), and cyclicity forces every eigenvector coordinate at the
  endpoint to be nonzero (`eigU_ne_zero_of_krylov_det_ne_zero`), i.e. full support.

Feeding these into the downstream Godsil forward bridge
`Graphplay.PST.isGodsilPSTReady_of_isPST_of_isSymm_of_fullSupport` (PST + real
symmetry + full support ⇒ the support eigenvalues form an arithmetic progression)
and contradicting the Niven obstruction
`Graphplay.PST.Cospectrality.pathEigenvalue_not_arithmeticProgression` (the path
eigenvalues admit no arithmetic progression for `n+1 ≥ 5`) closes the no-PST
direction with **no `sorry`**. -/

attribute [local instance] Classical.propDecidable

/-- `Path n` adjacency = pathGraph adjacency matrix. -/
theorem Path_adj_eq_pathGraph (n : ℕ) :
    (Path n).adj = (SimpleGraph.pathGraph (n+1)).adjMatrix ℂ := by
  ext k l
  rw [SimpleGraph.adjMatrix_apply, Path]
  simp only
  by_cases h : k.val + 1 = l.val ∨ l.val + 1 = k.val
  · rw [if_pos h, if_pos (by rw [SimpleGraph.pathGraph_adj]; exact h)]
  · rw [if_neg h, if_neg (by rw [SimpleGraph.pathGraph_adj]; exact h)]

/-- `Path n` adjacency is symmetric (`Aᵀ = A`): the defining disjunction
`k+1=l ∨ l+1=k` is symmetric in `k, l`. -/
theorem Path_adj_isSymm (n : ℕ) : (Path n).adj.IsSymm := by
  refine Matrix.IsSymm.ext (fun k l => ?_)
  show (if (l.val + 1 = k.val ∨ k.val + 1 = l.val) then (1:ℂ) else 0)
      = (if (k.val + 1 = l.val ∨ l.val + 1 = k.val) then (1:ℂ) else 0)
  by_cases h : k.val + 1 = l.val ∨ l.val + 1 = k.val
  · rw [if_pos h, if_pos (Or.symm h)]
  · rw [if_neg h, if_neg (fun hc => h (Or.symm hc))]

/-- The characteristic polynomial of `Path n` is the scaled Chebyshev poly. -/
theorem Path_charpoly_eq_cheby (n : ℕ) :
    (Path n).adj.charpoly = PathChebyshev.chebyScaled (n+1) := by
  rw [Path_adj_eq_pathGraph]
  exact PathChebyshev.charpoly_pathGraph_eq_cheby (n+1)

/-- The roots of `Path n`'s charpoly equal the `ofReal`-cast eigenvalue multiset. -/
theorem Path_roots_eq_eigenvalues (n : ℕ) :
    (Path n).adj.charpoly.roots
      = Multiset.map (RCLike.ofReal ∘ (Path n).herm.eigenvalues) Finset.univ.val :=
  (Path n).herm.roots_charpoly_eq_eigenvalues

/-- Each explicit cosine value `pathEigenvalue (n+1) k` (k : Fin (n+1)) is a
genuine eigenvalue of `Path n`: it lies in the range of `eigenvalues`. -/
theorem pathEigenvalue_mem_range (n : ℕ) (k : Fin (n+1)) :
    pathEigenvalue (n+1) k ∈ Set.range (Path n).herm.eigenvalues := by
  -- The real value pathEigenvalue (n+1) k = 2cos((k+1)π/(n+2)) is a root of cheby,
  -- hence (ofReal of) it is in the charpoly roots, hence = ofReal (eigenvalues i).
  set θ : ℝ := pathEigenvalue (n+1) k with hθ
  have hroot : (PathChebyshev.chebyScaled (n+1)).eval ((θ : ℝ) : ℂ) = 0 := by
    rw [hθ, pathEigenvalue]
    exact PathChebyshev.chebyScaled_eval_root (n+1) k.val (by exact k.isLt)
  -- So (θ : ℂ) is a root of charpoly.
  have hmem : ((θ : ℝ) : ℂ) ∈ (Path n).adj.charpoly.roots := by
    rw [Path_charpoly_eq_cheby, Polynomial.mem_roots (PathChebyshev.chebyScaled_ne_zero (n+1))]
    rw [Polynomial.IsRoot.def]; exact hroot
  -- charpoly roots = map (ofReal ∘ eigenvalues) univ
  rw [Path_roots_eq_eigenvalues] at hmem
  rw [Multiset.mem_map] at hmem
  obtain ⟨i, _, hi⟩ := hmem
  simp only [Function.comp_apply] at hi
  -- ofReal θ = ofReal (eigenvalues i) ⟹ θ = eigenvalues i
  have hθeq : θ = (Path n).herm.eigenvalues i := by
    have h2 : (((Path n).herm.eigenvalues i : ℝ) : ℂ) = ((θ : ℝ) : ℂ) := hi
    exact (by exact_mod_cast h2 : (Path n).herm.eigenvalues i = θ).symm
  exact ⟨i, hθeq.symm⟩

/-! ## Controllability bridge to full eigenvalue support

For a Hermitian graph on `Fin N`, if the standard basis vector `e_u` is a
**cyclic vector** for the adjacency matrix `A` — i.e. the Krylov matrix
`K` with columns `A^0 e_u, A^1 e_u, …, A^{N-1} e_u` is nonsingular — then
`u` has **full eigenvalue support**: every eigenvector has a nonzero
`u`-coordinate (`eigU G u i ≠ 0` for all `i`).

The argument is pure finite linear algebra: `A = U D Uᴴ`, so the eigen-coordinate
of `A^k e_u` is `(Uᴴ A^k e_u)_i = λ_i^k · conj(U_{u,i})`.  If `U_{u,i₀} = 0`,
row `i₀` of `Uᴴ K` vanishes, so `det(Uᴴ K) = 0`; since `U` is unitary
(`det Uᴴ ≠ 0`), `det K = 0` — contradicting cyclicity. -/

open Graphplay.PST

/-- The **Krylov matrix** of `G` at vertex `u` on `Fin N`: the `(row, k)` entry
is `((G.adj)^k) row u`, i.e. column `k` is `(G.adj)^k *ᵥ e_u`. -/
noncomputable def krylovMatrix {N : ℕ} (G : WeightedGraph (Fin N)) (u : Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun row k => (G.adj ^ (k.val)) row u

/-- Spectral theorem in elementary product form: `A = U D Uᴴ`. -/
theorem adj_eq_conj_diag {N : ℕ} (G : WeightedGraph (Fin N)) :
    G.adj = (eigU G) * (Matrix.diagonal (fun i => (G.herm.eigenvalues i : ℂ)))
        * (eigU G)ᴴ := by
  have h := G.herm.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  rw [eigU, ← Matrix.star_eq_conjTranspose]
  convert h using 2

/-- `Uᴴ A = D Uᴴ`. -/
theorem conjT_eigU_mul_adj {N : ℕ} (G : WeightedGraph (Fin N)) :
    (eigU G)ᴴ * G.adj
      = (Matrix.diagonal (fun i => (G.herm.eigenvalues i : ℂ))) * (eigU G)ᴴ := by
  conv_lhs => rw [adj_eq_conj_diag G]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, conjTranspose_mul_eigU, Matrix.one_mul]

/-- `Uᴴ A^k = D^k Uᴴ`. -/
theorem conjT_eigU_mul_adj_pow {N : ℕ} (G : WeightedGraph (Fin N)) (k : ℕ) :
    (eigU G)ᴴ * G.adj ^ k
      = (Matrix.diagonal (fun i => (G.herm.eigenvalues i : ℂ))) ^ k * (eigU G)ᴴ := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, conjT_eigU_mul_adj,
      ← Matrix.mul_assoc, ← pow_succ]

theorem conjT_eigU_mul_krylov {N : ℕ} (G : WeightedGraph (Fin N)) (u : Fin N)
    (i k : Fin N) :
    ((eigU G)ᴴ * krylovMatrix G u) i k
      = ((G.herm.eigenvalues i : ℂ)) ^ (k.val) * star (eigU G u i) := by
  -- The (i,k) entry of Uᴴ K is ∑_row (Uᴴ)_{i,row} (A^{k} )_{row,u} = (Uᴴ A^{k})_{i,u}.
  have hentry : ((eigU G)ᴴ * krylovMatrix G u) i k
      = ((eigU G)ᴴ * G.adj ^ (k.val)) i u := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun row _ => ?_)
    rfl
  rw [hentry, conjT_eigU_mul_adj_pow]
  -- (D^k Uᴴ)_{i,u} = (D^k)_{i,i} (Uᴴ)_{i,u} = λ_i^k conj(U_{u,i}).
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply, Pi.pow_apply]
  · intro j _ hj
    rw [Matrix.diagonal_pow, Matrix.diagonal_apply_ne _ (Ne.symm hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h


/-- **Controllability ⇒ no zero eigenvector-coordinate.**  If the Krylov matrix
`K` at `u` is nonsingular (`det K ≠ 0`), then `eigU G u i ≠ 0` for every
eigenindex `i`.  (Contrapositive: a zero coordinate makes row `i` of `Uᴴ K`
vanish, forcing `det K = 0`.) -/
theorem eigU_ne_zero_of_krylov_det_ne_zero {N : ℕ} (G : WeightedGraph (Fin N))
    (u : Fin N) (hdet : (krylovMatrix G u).det ≠ 0) (i : Fin N) :
    eigU G u i ≠ 0 := by
  intro h0
  -- row i of Uᴴ K is zero (every entry is λ_i^k · conj(U_{u,i}) = λ_i^k · 0 = 0).
  have hrow : ∀ k, ((eigU G)ᴴ * krylovMatrix G u) i k = 0 := by
    intro k
    rw [conjT_eigU_mul_krylov]
    rw [h0]; simp
  -- so det (Uᴴ K) = 0.
  have hdetz : ((eigU G)ᴴ * krylovMatrix G u).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero i hrow
  -- det (Uᴴ K) = det Uᴴ · det K, and det Uᴴ ≠ 0 (U unitary).
  rw [Matrix.det_mul] at hdetz
  have hUdet : ((eigU G)ᴴ).det ≠ 0 := by
    have hu : IsUnit ((eigU G)ᴴ) := by
      rw [Matrix.isUnit_conjTranspose]; exact eigU_isUnit G
    exact (Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero
  rcases mul_eq_zero.mp hdetz with h | h
  · exact hUdet h
  · exact hdet h

/-- **Full eigenvalue support from controllability.**  If the Krylov matrix at `u`
is nonsingular, then every eigenvalue lies in the eigenvalue support of `u`:
`eigenProjDiagLocal G λ u ≠ 0` for all `λ` in the spectrum. -/
theorem fullSupport_of_krylov_det_ne_zero {N : ℕ} (G : WeightedGraph (Fin N))
    (u : Fin N) (hdet : (krylovMatrix G u).det ≠ 0)
    (lam : ℝ) (hlam : lam ∈ Finset.univ.image G.herm.eigenvalues) :
    lam ∈ EigenvalueSupport G u := by
  rw [Finset.mem_image] at hlam
  obtain ⟨i, _, hi⟩ := hlam
  exact ⟨i, hi, eigU_ne_zero_of_krylov_det_ne_zero G u hdet i⟩


/-! ## Path endpoint is a cyclic vector (Krylov nonsingularity) -/

/-- The standard basis column vector `e_0` in `Fin (n+1) → ℂ`. -/
private noncomputable def e0 (n : ℕ) : Fin (n+1) → ℂ := fun j => if j = (0 : Fin (n+1)) then 1 else 0

/-- The Krylov vector `v_k = (Path n).adj ^ k *ᵥ e_0`; its `i`-th coordinate is the
`(i, 0)`-entry of the `k`-th adjacency power. -/
private noncomputable def kvec (n k : ℕ) : Fin (n+1) → ℂ :=
  fun i => ((Path n).adj ^ k) i (0 : Fin (n+1))

/-- One step of the path quantum walk on `e_0`: `(A *ᵥ v)_i = v_{i-1} + v_{i+1}`
(boundary terms dropped).  Concretely, `(A *ᵥ v) i = ∑_j A_{i,j} v_j` and on the
path `A_{i,j} = 1` iff `|i-j| = 1`. -/
private theorem path_adj_mulVec_apply (n : ℕ) (v : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    ((Path n).adj *ᵥ v) i
      = (∑ j : Fin (n+1), (if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then v j else 0)) := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hadj : (Path n).adj i j = if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then (1:ℂ) else 0 := rfl
  rw [hadj]
  by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

/-- `kvec n (k+1) = (Path n).adj *ᵥ kvec n k`. -/
private theorem kvec_succ (n k : ℕ) :
    kvec n (k+1) = (Path n).adj *ᵥ kvec n k := by
  funext i
  show ((Path n).adj ^ (k+1)) i (0 : Fin (n+1)) = _
  rw [pow_succ']
  rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

/-- **Claim A (upper-triangular structure).**  `kvec n k i = 0` whenever `i.val > k`:
in `k` steps the path walk from the endpoint `0` cannot reach a vertex at distance
`> k`. -/
private theorem kvec_eq_zero_of_gt (n : ℕ) : ∀ (k : ℕ) (i : Fin (n+1)), k < i.val → kvec n k i = 0 := by
  intro k
  induction k with
  | zero =>
    intro i hi
    show ((Path n).adj ^ 0) i (0 : Fin (n+1)) = 0
    rw [pow_zero, Matrix.one_apply]
    rw [if_neg (by intro h; rw [h] at hi; exact absurd hi (by simp))]
  | succ m ih =>
    intro i hi
    rw [kvec_succ, path_adj_mulVec_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [if_pos h]
      apply ih
      -- j is a neighbor of i, and i.val > m+1, so j.val > m.
      omega
    · rw [if_neg h]


/-- **Claim B (unit leading coordinate).**  `kvec n k ⟨k, _⟩ = 1` for `k ≤ n`:
the unique shortest walk from endpoint `0` reaching distance `k` in `k` steps
contributes a `1`.  Together with Claim A this makes the Krylov matrix
lower-triangular with unit diagonal. -/
private theorem kvec_diag (n : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ n), kvec n k ⟨k, by omega⟩ = 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    show ((Path n).adj ^ 0) ⟨0, by omega⟩ (0 : Fin (n+1)) = 1
    rw [pow_zero, Matrix.one_apply, if_pos (by rfl)]
  | succ m ih =>
    intro hk
    rw [kvec_succ, path_adj_mulVec_apply]
    -- the only nonzero summand is j = ⟨m, _⟩ (the predecessor); it equals 1.
    rw [Finset.sum_eq_single (⟨m, by omega⟩ : Fin (n+1))]
    · -- value at j = ⟨m,_⟩: neighbor of i = ⟨m+1,_⟩, and kvec n m ⟨m⟩ = 1.
      rw [if_pos (Or.inr rfl)]
      exact ih (by omega)
    · -- every other j gives a zero summand.
      intro j _ hj
      by_cases h : (m+1) + 1 = j.val ∨ j.val + 1 = (m+1)
      · rw [if_pos h]
        -- a neighbor j ≠ ⟨m⟩ of ⟨m+1⟩ must have j.val = m+2 > m, so kvec = 0.
        apply kvec_eq_zero_of_gt
        -- j.val = m+2 (since j.val = m would be ⟨m⟩, excluded; j.val+1=m+1 ⇒ j.val=m)
        have hjm : j.val ≠ m := by
          intro hc; apply hj; apply Fin.ext; exact hc
        omega
      · rw [if_neg h]
    · intro hc; exact absurd (Finset.mem_univ _) hc


/-- The Krylov matrix of `Path n` at the endpoint `0` is **upper-triangular with
unit diagonal**: `K_{i,j} = (A^j)_{i,0} = 0` for `i > j` (Claim A) and `K_{i,i} = 1`
(Claim B). -/
private theorem path_krylov_blockTriangular (n : ℕ) :
    (krylovMatrix (Path n) (0 : Fin (n+1))).BlockTriangular id := by
  intro i j hij
  -- hij : (id j) < (id i), i.e. j < i, i.e. j.val < i.val. Entry below diagonal.
  show ((Path n).adj ^ (j.val)) i (0 : Fin (n+1)) = 0
  have : kvec n (j.val) i = 0 := by
    apply kvec_eq_zero_of_gt
    -- j < i ⇒ j.val < i.val.
    exact (Fin.lt_def.mp hij)
  exact this

/-- The diagonal entries of the Krylov matrix of `Path n` at `0` are all `1`. -/
private theorem path_krylov_diag (n : ℕ) (i : Fin (n+1)) :
    krylovMatrix (Path n) (0 : Fin (n+1)) i i = 1 := by
  show ((Path n).adj ^ (i.val)) i (0 : Fin (n+1)) = 1
  have := kvec_diag n i.val (by omega)
  -- kvec n i.val ⟨i.val, _⟩ = 1, and ⟨i.val, _⟩ = i.
  have hcast : (⟨i.val, by omega⟩ : Fin (n+1)) = i := Fin.ext rfl
  rw [hcast] at this
  exact this

/-- **Path endpoint Krylov nonsingularity.**  `det (krylovMatrix (Path n) 0) = 1 ≠ 0`:
the endpoint `0` is a cyclic vector for the path adjacency matrix.  (Upper-triangular
with unit diagonal ⇒ determinant is the product of the diagonal entries `= 1`.) -/
theorem path_krylov_det (n : ℕ) :
    (krylovMatrix (Path n) (0 : Fin (n+1))).det = 1 := by
  rw [Matrix.det_of_upperTriangular (path_krylov_blockTriangular n)]
  rw [Finset.prod_eq_one]
  intro i _
  exact path_krylov_diag n i

/-- **Endpoint full eigenvalue support of `Path n`.**  Every eigenvalue of `Path n`
lies in the eigenvalue support of the endpoint `0`.  This is the second mission
input: the explicit Chebyshev eigenvector `ψ_k(j) = sin(jkπ/(n+1))` is nonzero at the
endpoint (`ψ_k(1) = sin(kπ/(n+1)) ≠ 0`), here obtained spectrum-free via the
controllability bridge (`fullSupport_of_krylov_det_ne_zero`) and the cyclicity of the
endpoint (`path_krylov_det`). -/
theorem path_endpoint_fullSupport (n : ℕ)
    (lam : ℝ) (hlam : lam ∈ Finset.univ.image (Path n).herm.eigenvalues) :
    lam ∈ EigenvalueSupport (Path n) (0 : Fin (n+1)) := by
  apply fullSupport_of_krylov_det_ne_zero (Path n) (0 : Fin (n+1)) _ lam hlam
  rw [path_krylov_det]; exact one_ne_zero


/-! ## No endpoint PST for long paths (assembly) -/

/-- **No endpoint PST at positive time, for `n ≥ 4`.** -/
theorem path_no_PST_pos_of_ge_three (n : ℕ) (hn : 3 ≤ n) :
    ∀ τ : ℝ, 0 < τ → ¬ IsPST (Path n) (0 : Fin (n+1)) (Fin.last n) τ := by
  intro τ hτ hpst
  have hsymm : (Path n).adj.IsSymm := Path_adj_isSymm n
  have hfull : ∀ lam ∈ Finset.univ.image (Path n).herm.eigenvalues,
      lam ∈ EigenvalueSupport (Path n) (0 : Fin (n+1)) := path_endpoint_fullSupport n
  have hready : PST.IsGodsilPSTReady (Path n) (0 : Fin (n+1)) (Fin.last n) :=
    isGodsilPSTReady_of_isPST_of_isSymm_of_fullSupport (Path n) hsymm hτ hfull hpst
  obtain ⟨a, b, kof, ha, halign, _⟩ := hready
  apply pathEigenvalue_not_arithmeticProgression (n+1) (by omega)
  refine ⟨a, b, ha, fun k => ?_⟩
  have hmem : pathEigenvalue (n+1) k ∈ Finset.univ.image (Path n).herm.eigenvalues := by
    obtain ⟨i, hi⟩ := pathEigenvalue_mem_range n k
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  exact ⟨kof (pathEigenvalue (n+1) k), halign _ hmem⟩

/-- `IsPST` at `τ` and at `-τ` coincide for the symmetric path endpoints (the
amplitude modulus is time-reversal invariant): `‖U(-τ)₀ₙ‖ = ‖U(τ)₀ₙ‖`. -/
theorem path_isPST_neg_iff (n : ℕ) (τ : ℝ) :
    IsPST (Path n) (0 : Fin (n+1)) (Fin.last n) (-τ)
      ↔ IsPST (Path n) (0 : Fin (n+1)) (Fin.last n) τ := by
  unfold IsPST
  have hsymm : (Path n).adj.IsSymm := Path_adj_isSymm n
  -- U(-τ) = (U τ)ᴴ, so U(-τ)₀ₙ = conj(U(τ)ₙ₀); symmetry gives U(τ)ₙ₀ = U(τ)₀ₙ.
  have hconj : (Path n).evolve (-τ) (0 : Fin (n+1)) (Fin.last n)
      = star ((Path n).evolve τ (Fin.last n) (0 : Fin (n+1))) := by
    rw [← (Path n).evolve_conjTranspose τ]
    rw [Matrix.conjTranspose_apply]
  rw [hconj, norm_star, evolve_symm_of_isSymm (Path n) hsymm τ (0 : Fin (n+1)) (Fin.last n)]

/-- **No endpoint PST for long paths, all times (`n ≥ 4`).**  Closes the residual
`path_long_no_PST_residual` cleanly. -/
theorem path_no_PST_of_ge_three (n : ℕ) (hn : 3 ≤ n) :
    ∀ τ : ℝ, ¬ IsPST (Path n) (0 : Fin (n+1)) (Fin.last n) τ := by
  intro τ hpst
  rcases lt_trichotomy τ 0 with hneg | hzero | hpos
  · -- τ < 0: reduce to -τ > 0.
    have hpos : (0 : ℝ) < -τ := by linarith
    exact path_no_PST_pos_of_ge_three n hn (-τ) hpos ((path_isPST_neg_iff n τ).mpr hpst)
  · -- τ = 0: U(0) = I, off-diagonal entry is 0 (endpoints distinct), so ‖·‖ = 0 ≠ 1.
    subst hzero
    rw [show (0:ℝ) = (0:ℝ) from rfl] at hpst
    unfold IsPST at hpst
    rw [(Path n).evolve_zero, Matrix.one_apply,
      if_neg (by intro h; have := Fin.val_eq_of_eq h; simp [Fin.last] at this; omega)] at hpst
    rw [norm_zero] at hpst
    exact zero_ne_one hpst
  · exact path_no_PST_pos_of_ge_three n hn τ hpos hpst

/-- **`P₄` has NO endpoint PST — PROVEN** (corrected statement; an earlier draft of
this file falsely asserted `P₄` PST at `τ = π/√5`).

The `4×4` path Hamiltonian has spectrum `{±φ, ±1/φ}` with `φ = (1+√5)/2`; the
ratio `φ/(1/φ) = φ² = φ + 1` is irrational, so the eigenvalues are *not*
rationally commensurable.  By the Godsil ratio condition this rules out PST at
every time `τ` (numerically the endpoint amplitude maxes out near `0.986 < 1`).

CLOSED axiom-cleanly: `Path 3` (`n = 3`) is covered by `path_no_PST_of_ge_three`,
which assembles the explicit eigenvalue set, endpoint full support (via the
controllability/Krylov bridge), the Godsil forward bridge, and the Niven
no-arithmetic-progression obstruction `pathEigenvalue_not_arithmeticProgression`
(at `n+1 = 4`, the golden-ratio spectrum).

Reference: arXiv:quant-ph/0309131; Godsil–Kirkland–Severini–Smith
(arXiv:1201.4822). -/
theorem path_P4_no_PST :
    ∀ τ : ℝ, ¬ IsPST (Path 3) (0 : Fin 4) (Fin.last 3) τ :=
  path_no_PST_of_ge_three 3 (by norm_num)

/-- **Long-path no-PST — PROVEN (the Godsil PST⇒ratio obstruction, now assembled).**
For `n ≥ 4` the path eigenvalues `2 cos((k+1)π/(n+2))` are *not* rationally
commensurable (the number-theoretic core, proved in
`Graphplay.PST.Cospectrality.pathEigenvalue_not_arithmeticProgression` via Niven),
so the Godsil ratio condition fails and no PST occurs at any time.

CLOSED axiom-cleanly via `path_no_PST_of_ge_three` (`n ≥ 3 ⊇ n ≥ 4`): PST at any
`τ`, together with real symmetry (`Path_adj_isSymm`) and endpoint full support
(`path_endpoint_fullSupport`, obtained spectrum-free from the controllability/Krylov
bridge), forces `IsGodsilPSTReady` via the downstream
`Graphplay.PST.isGodsilPSTReady_of_isPST_of_isSymm_of_fullSupport`; the resulting
arithmetic progression of all eigenvalues contradicts the Niven obstruction.  The
`τ = 0` case is the off-diagonal `(I)₀ₙ = 0`, and `τ < 0` reduces to `-τ > 0` by
time-reversal (`path_isPST_neg_iff`). -/
theorem path_long_no_PST_residual
    (n : ℕ) (hn : 4 ≤ n) :
    ∀ τ : ℝ, ¬ IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) τ :=
  path_no_PST_of_ge_three n (by omega)

/-- **Negative side of Christandl–Datta–Ekert–Landahl (2004).**  For `n ≥ 4`
(the path `P_{n+1}` on at least five vertices) there is *no* endpoint-to-
endpoint PST at any time `τ`.

Reference: arXiv:quant-ph/0309131; Godsil–Kirkland–Severini–Smith
(arXiv:1201.4822); Coutinho thesis (2014) §2.4.

**Audit note (corrected classification).**  The genuine CDEL classification is
that *uniformly coupled* endpoint PST holds for chains of exactly `2` or `3`
vertices — i.e. for `n ∈ {1, 2}` (`P₂ = K₂` at `τ = π/2`, proven as
`Graphplay.StdLib.HypercubeProduct.isPST_K2`; and `P₃` at `τ = π/√2`, proven
here as `path_P3_PST_residual`).  **`P₄` (`n = 3`) has no endpoint PST** — its
golden-ratio spectrum `{±φ, ±1/φ}` is not rationally commensurable
(`path_P4_no_PST`).  Hence the no-PST regime is `n ≥ 3`.

This theorem covers the `n ≥ 4` part of that regime; the `n = 3` (`P₄`) endpoint
is handled separately by `path_P4_no_PST`.  (An earlier draft both (a) carried a
wrong hypothesis `1 ≤ n ∧ n ∉ {2,3}` that is false at `n = 1` = `K₂`, and
(b) elsewhere *falsely asserted* `P₄` PST; both are corrected.)

The proof is `path_long_no_PST_residual`, now **fully closed** (axiom-clean) via
the assembled Godsil bridge: endpoint full support (controllability/Krylov) +
the Godsil forward direction + the Niven no-arithmetic-progression obstruction.
-/
theorem path_no_PST_endpoint_endpoint
    (n : ℕ) (hn : 4 ≤ n) :
    ∀ τ : ℝ, ¬ IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) τ :=
  path_long_no_PST_residual n hn

/-! ## The full unweighted-path endpoint-PST biconditional (assembled here)

Both halves of the Christandl–Datta–Ekert–Landahl / Coutinho endpoint-PST
classification are now in-corpus and axiom-clean:

* **backward** (`n ∈ {1,2}` ⇒ PST) — `path_PST_endpoint_endpoint`, the explicit
  `K₂`/`P₃` diagonalize-and-exponentiate;
* **forward** (`n ≥ 3` ⇒ no PST) — `path_no_PST_of_ge_three`, the assembled
  Godsil bridge (endpoint full support via the controllability/Krylov determinant
  + the Godsil forward direction + the Niven no-arithmetic-progression
  obstruction `pathEigenvalue_not_arithmeticProgression`).

The biconditional below is the *relocation* of the slot
`Graphplay.PST.isPST_exists_path_iff`, which could only be left as an honest
`sorry` in `GodsilRatio` because the Niven obstruction
`pathEigenvalue_not_arithmeticProgression` lives **downstream** in
`Graphplay.PST.Cospectrality` (importing `GodsilRatio`), so assembling it there
would be circular.  `Path.lean` imports *both* `GodsilRatio` and `Cospectrality`,
so the assembly is sound here.  No new mathematics — pure assembly. -/

/-- **`IsPST` is an adjacency-only invariant.**  Two `WeightedGraph`s with equal
adjacency matrices have identical quantum-walk evolution, hence identical PST.
Used to transport the `Path n`/`pathGraph (n+1)` endpoint classification across
the two equivalent unweighted-path models. -/
theorem isPST_congr_adj {N : ℕ} {G H : WeightedGraph (Fin N)} (hadj : G.adj = H.adj)
    (u v : Fin N) (τ : ℝ) : IsPST G u v τ ↔ IsPST H u v τ := by
  unfold IsPST WeightedGraph.evolve
  rw [hadj]

/-! ### `IsPST` transports along any graph isomorphism

The continuous-time quantum walk is *natural* in the vertex set: if a vertex
relabelling `e : W ≃ V` carries `H.adj` to `G.adj` entrywise
(`H.adj a b = G.adj (e a) (e b)`, i.e. `H` is the `e`-relabelling of `G`), then
the whole propagator `exp(-iτ A)` transports — `H.evolve τ a b = G.evolve τ (e a)
(e b)` — because conjugation by the permutation matrix is a *continuous algebra
automorphism* of the matrix algebra, and `NormedSpace.exp` commutes with every
continuous ring homomorphism (`NormedSpace.map_exp`).  Consequently PST is a
graph-isomorphism invariant.  This is the reusable "transfer along iso" lemma
that lets PST results proven on one model (e.g. an iterated-product hypercube)
be carried to any isomorphic model. -/
section TransferAlongEquiv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Exponential commutes with reindexing by an equivalence:
`exp (M.submatrix e e) = (exp M).submatrix e e`.  Here `M.submatrix e e` is the
`e`-relabelling, equal to the (continuous) algebra automorphism
`reindexAlgEquiv ℂ ℂ e.symm` applied to `M`, so `NormedSpace.map_exp` applies. -/
theorem exp_submatrix_equiv {V W : Type u} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] (e : W ≃ V) (M : Matrix V V ℂ) :
    NormedSpace.exp (M.submatrix e e) = (NormedSpace.exp M).submatrix e e := by
  have hcont : Continuous (Matrix.reindexAlgEquiv ℂ ℂ e.symm) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toLinearMap
  have hsm : ∀ X : Matrix V V ℂ, X.submatrix e e = (Matrix.reindexAlgEquiv ℂ ℂ e.symm) X := by
    intro X; rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Equiv.symm_symm]
  rw [hsm M, hsm (NormedSpace.exp M)]
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e.symm) hcont M).symm

/-- **Evolution transports along a graph isomorphism (entrywise).**  If
`e : W ≃ V` relabels `H` to `G` (`H.adj a b = G.adj (e a) (e b)`), then
`H.evolve τ a b = G.evolve τ (e a) (e b)`. -/
theorem evolve_transfer_equiv {V W : Type u} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] (G : WeightedGraph V) (H : WeightedGraph W) (e : W ≃ V)
    (hadj : ∀ a b, H.adj a b = G.adj (e a) (e b)) (τ : ℝ) (a b : W) :
    H.evolve τ a b = G.evolve τ (e a) (e b) := by
  unfold WeightedGraph.evolve
  have hscale : (-(Complex.I * (τ : ℂ)) • H.adj)
      = (-(Complex.I * (τ : ℂ)) • G.adj).submatrix e e := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hadj a b]
  rw [hscale, exp_submatrix_equiv, Matrix.submatrix_apply]

/-- **PST transports along a graph isomorphism.**  If `e : W ≃ V` relabels `H`
to `G`, then `IsPST H a b τ ↔ IsPST G (e a) (e b) τ`. -/
theorem isPST_transfer_equiv {V W : Type u} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] (G : WeightedGraph V) (H : WeightedGraph W) (e : W ≃ V)
    (hadj : ∀ a b, H.adj a b = G.adj (e a) (e b)) (a b : W) (τ : ℝ) :
    IsPST H a b τ ↔ IsPST G (e a) (e b) τ := by
  unfold IsPST
  rw [evolve_transfer_equiv G H e hadj τ a b]

end TransferAlongEquiv

/-- **Unweighted-path endpoint PST classification — `Path n` form (CLOSED).**  The
unweighted path `Path n` on `n + 1` vertices admits endpoint-to-endpoint PST at
*some* time iff `n ∈ {1, 2}` (i.e. `P₂ = K₂` or `P₃`).

Backward via `path_PST_endpoint_endpoint` (the explicit `K₂`/`P₃` exponential);
forward via `path_no_PST_of_ge_three` (the Godsil-bridge + Niven obstruction).
Fully assembled, axiom-clean.

Reference: Christandl–Datta–Ekert–Landahl, arXiv:quant-ph/0309131, Thm 1;
Coutinho thesis (2014) §2.4. -/
theorem isPST_exists_Path_iff (n : ℕ) (hn : 1 ≤ n) :
    (∃ τ : ℝ, IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) τ) ↔ (n = 1 ∨ n = 2) := by
  constructor
  · rintro ⟨τ, hpst⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    -- `n ≥ 1`, `n ≠ 1`, `n ≠ 2` ⇒ `n ≥ 3`, so no PST.
    exact path_no_PST_of_ge_three n (by omega) τ hpst
  · intro hn'
    exact ⟨pathPSTTime n, path_PST_endpoint_endpoint n hn'⟩

/-- **Unweighted-path endpoint PST classification — `pathGraph n` form (CLOSED).**
The genuine `SimpleGraph.pathGraph n` (promoted to a `WeightedGraph` on `Fin n`)
admits endpoint-to-endpoint PST between `pathLeft` (`= 0`) and `pathRight`
(`= n - 1`) at some time iff `n ∈ {2, 3}`.

This is the relocated and now-**closed** statement of the former
`Graphplay.PST.isPST_exists_path_iff` sorry: `pathGraph n` and `Path (n-1)` have
equal adjacency (both are the 0/1 nearest-neighbour matrix on `Fin n`), their
endpoints `pathLeft`/`pathRight` coincide with `0`/`Fin.last (n-1)`, and the
classification then transports across `isPST_congr_adj` from `isPST_exists_Path_iff`.

Reference: Christandl–Datta–Ekert–Landahl, arXiv:quant-ph/0309131, Thm 1;
Coutinho thesis (2014) §2.4; Godsil–Kirkland–Severini–Smith, arXiv:1201.4822. -/
theorem isPST_exists_pathGraph_iff (n : ℕ) (hn : 2 ≤ n) :
    (∃ τ : ℝ, IsPST (PST.pathGraph n) (PST.pathLeft (by omega)) (PST.pathRight (by omega)) τ)
      ↔ (n = 2 ∨ n = 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- adjacency equality `pathGraph (m+1) = Path m`, endpoint identifications.
  have hadj : (PST.pathGraph (m + 1)).adj = (Path m).adj := by
    rw [Path_adj_eq_pathGraph]; unfold PST.pathGraph; rfl
  have hL : (PST.pathLeft (n := m + 1) (by omega) : Fin (m + 1)) = (0 : Fin (m + 1)) := rfl
  have hR : (PST.pathRight (n := m + 1) (by omega) : Fin (m + 1)) = Fin.last m := rfl
  rw [hL, hR]
  -- transport the existential through `isPST_congr_adj`, then apply the `Path m`
  -- classification (`m + 1 = 2 ∨ m + 1 = 3 ↔ m = 1 ∨ m = 2`).
  have htrans : (∃ τ : ℝ, IsPST (PST.pathGraph (m + 1)) (0 : Fin (m + 1)) (Fin.last m) τ)
      ↔ (∃ τ : ℝ, IsPST (Path m) (0 : Fin (m + 1)) (Fin.last m) τ) :=
    exists_congr (fun τ => isPST_congr_adj hadj _ _ τ)
  rw [htrans, isPST_exists_Path_iff m (by omega)]
  omega

/-! ## Engineered weighted paths (Christandl–Landahl–Werner couplings) -/

/-- An **engineered weighted path** on `Fin (n + 1)` with edge weights
`J : Fin n → ℝ`.  Edge `k --- k+1` carries weight `J k`; all other entries
are zero. -/
noncomputable def WeightedPath (n : ℕ) (J : Fin n → ℝ) :
    WeightedGraph (Fin (n + 1)) where
  adj := fun k l =>
    if h : k.val + 1 = l.val then
      ((J ⟨k.val, by
          have : k.val < n + 1 := k.isLt
          omega⟩ : ℝ) : ℂ)
    else if h' : l.val + 1 = k.val then
      ((J ⟨l.val, by
          have : l.val < n + 1 := l.isLt
          omega⟩ : ℝ) : ℂ)
    else 0
  herm := by
    -- Real-symmetric ⇒ Hermitian: the entry at `(k,l)` and `(l,k)` are equal
    -- real numbers (`J⟨·⟩` or `0`), and `star` fixes real values.
    refine Matrix.IsHermitian.ext (fun k l => ?_)
    by_cases h1 : k.val + 1 = l.val
    · -- `k+1 = l`: both entries equal `J⟨k⟩`.
      have hne : ¬ l.val + 1 = k.val := by omega
      rw [dif_pos h1, dif_neg hne, dif_pos h1]; simp
    · by_cases h2 : l.val + 1 = k.val
      · -- `l+1 = k`: both entries equal `J⟨l⟩`.
        rw [dif_pos h2, dif_neg h1, dif_pos h2]; simp
      · -- neither: both entries are `0`.
        rw [dif_neg h2, dif_neg h1, dif_neg h1, dif_neg h2]; simp
  loopless := by
    intro v
    -- `v.val + 1 = v.val` is impossible; `v.val + 1 = v.val` likewise.
    simp

/-- The **Christandl–Landahl–Werner couplings**:
`J_k = √(k · (n + 1 - k))` for `1 ≤ k ≤ n`.  Equivalently, in the `Fin n`
parameterization used by `WeightedPath`, `J ⟨k, _⟩ = √((k+1)(n-k))`. -/
noncomputable def CLWCouplings (n : ℕ) : Fin n → ℝ :=
  fun k => Real.sqrt ((k.val + 1 : ℝ) * ((n : ℝ) - k.val))

/-- The **Christandl–Landahl–Werner engineered path** on `Fin (n + 1)`:
the weighted path with edge weights `J_k = √(k(n - k + 1))`. -/
noncomputable def CLWPath (n : ℕ) : WeightedGraph (Fin (n + 1)) :=
  WeightedPath n (CLWCouplings n)

/-- **Christandl–Landahl–Werner (2005) engineered-path PST** (external).

The engineered weighted path with couplings `J_k = √(k(n - k + 1))` exhibits PST
between the two endpoints `0` and `n` at time `τ = π / 2`, for every `n ≥ 1`.
The proof factors through the observation that the Hamiltonian is a faithful
representation of the spin-`n/2` angular momentum operator `J_x`, whose evolution
`exp(-iπ J_x/2)` is the antipodal flip with a unit-modulus `(0,n)` entry; its
spectrum is the arithmetic progression `{-n/2, …, n/2}`.

Recorded as a `Prop`-valued **typeclass assumption, not a bare axiom** (following
the `LovaszTheta` pattern): the spin-`n/2` `J_x` identification is a genuinely
deeper representation-theoretic input not built in this module, so **no instance
is provided** — pure cited external (arXiv:quant-ph/0411020, Thm 1). -/
class CLWPathPST : Prop where
  /-- The Christandl–Landahl–Werner engineered path has endpoint PST at `π/2`
  for every `n ≥ 1` (arXiv:quant-ph/0411020, Thm 1). -/
  pst : ∀ (n : ℕ), 1 ≤ n →
    IsPST (CLWPath n) (0 : Fin (n + 1)) (Fin.last n) (Real.pi / 2)

/-- **Christandl–Landahl–Werner (2005).**  The engineered weighted path with
couplings `J_k = √(k(n - k + 1))` exhibits PST between the two endpoints `0` and
`n` at time `τ = π / 2`, for every `n ≥ 1`.  Axiom-clean and honestly conditional
on the cited external `[CLWPathPST]` (arXiv:quant-ph/0411020, Thm 1). -/
theorem weightedPath_PST [h : CLWPathPST] (n : ℕ) (hn : 1 ≤ n) :
    IsPST (CLWPath n) (0 : Fin (n + 1)) (Fin.last n) (Real.pi / 2) :=
  h.pst n hn

/-- The endpoint amplitude of the CLW engineered path reaches modulus `1` at
`τ = π/2` (the modulus form of `weightedPath_PST`), conditional on `[CLWPathPST]`.
More generally *any* mirror-symmetric coupling profile whose single-excitation
spectrum has integer commensurable gaps yields PST (Karbach–Stolze 2005, Yung
2006); here specialized to CLW. -/
theorem weightedPath_PST_modulus_eq_one [CLWPathPST] (n : ℕ) (hn : 1 ≤ n) :
    ‖(CLWPath n).evolve (Real.pi / 2) 0 (Fin.last n)‖ = 1 :=
  weightedPath_PST n hn

/-! ## Convenience aliases -/

/-! ## Computable rational companions

These are the same 0/1 (or rational-weighted) adjacency matrices as `Path`
and `WeightedPath`, but valued in `ℚ` rather than `ℂ`, so that they are
fully `#eval`-able.  They can be lifted to `ℂ` via `Matrix.map (algebraMap ℚ ℂ)`
when needed.
-/

/-- Computable companion to `Path n`: the 0/1 adjacency matrix of the
unweighted path on `Fin (n + 1)`, valued in `ℚ`. -/
def Path.adjMatrixℚ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun k l =>
    if (k.val + 1 = l.val) ∨ (l.val + 1 = k.val) then (1 : ℚ) else 0

/-- Computable companion to `WeightedPath n J`: the engineered weighted
adjacency matrix on `Fin (n + 1)` with rational weights `J : Fin n → ℚ`. -/
def WeightedPath.adjMatrixℚ (n : ℕ) (J : Fin n → ℚ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun k l =>
    if h : k.val + 1 = l.val then
      J ⟨k.val, by have : k.val < n + 1 := k.isLt; omega⟩
    else if h' : l.val + 1 = k.val then
      J ⟨l.val, by have : l.val < n + 1 := l.isLt; omega⟩
    else 0

/-- Smoke test: `Path 4` has a `1` between vertex 0 and vertex 1. -/
example : (Path.adjMatrixℚ 4) ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := by decide

/-- Smoke test: `Path 4` is loopless (zero diagonal). -/
example : Matrix.trace (Path.adjMatrixℚ 4) = 0 := by native_decide

#eval (Path.adjMatrixℚ 4) ⟨0, by decide⟩ ⟨1, by decide⟩
#eval Matrix.trace (Path.adjMatrixℚ 4)

/-- The path on two vertices (`P_2 = K_2` in graph-theory notation), the single
edge, the smallest graph of all that exhibits endpoint-to-endpoint PST (at
`τ = π/2`). -/
noncomputable def P2 : WeightedGraph (Fin 2) := Path 1

/-- The path on three vertices (`P_3` in graph-theory notation), the
smallest *unweighted multi-edge* graph that exhibits endpoint-to-endpoint PST. -/
noncomputable def P3 : WeightedGraph (Fin 3) := Path 2

/-- The path on four vertices (`P_4`).  Unlike `P₃`, `P₄` has **no**
endpoint-to-endpoint PST (golden-ratio spectrum `{±φ, ±1/φ}` is not rationally
commensurable; see `P4_no_PST`). -/
noncomputable def P4 : WeightedGraph (Fin 4) := Path 3

/-- **PST on `P_2 = K_2`** at `τ = π/2` (proven, via `path_P2_PST_residual`). -/
theorem P2_PST : IsPST P2 (0 : Fin 2) (Fin.last 1) (Real.pi / 2) :=
  path_P2_PST_residual

/-- PST on `P_3` at `τ = π / √2` (proven, via `path_P3_PST_residual`). -/
theorem P3_PST : IsPST P3 (0 : Fin 3) (Fin.last 2) (Real.pi / Real.sqrt 2) :=
  path_PST_endpoint_endpoint 2 (Or.inr rfl)

/-- **No PST on `P_4`** at any time `τ` (corrected: an earlier draft falsely
claimed `P₄` PST at `τ = π/√5`).  The golden-ratio spectrum `{±φ, ±1/φ}` is not
rationally commensurable; **PROVEN** axiom-cleanly (`path_P4_no_PST`) via the
assembled Godsil bridge. -/
theorem P4_no_PST : ∀ τ : ℝ, ¬ IsPST P4 (0 : Fin 4) (Fin.last 3) τ :=
  path_P4_no_PST

end StdLib
end Graphplay
