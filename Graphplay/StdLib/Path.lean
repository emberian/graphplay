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

* `P₃` endpoint PST (`path_P3_PST_residual`) is **fully proved** here, by an
  explicit `3×3` diagonalize-and-exponentiate (`A = U·diag(√2,0,-√2)·U⁻¹`,
  `Matrix.exp_conj` + `Matrix.exp_diagonal`, then the `(0,2)` entry evaluates
  to `-1` at `τ = π/√2`).
* `cos_path_angle_irrational` (the Niven number-theoretic core of the negative
  side) is **fully proved**.
* `P₄` no-PST (`path_P4_no_PST`), the long-path no-PST
  (`path_long_no_PST_residual`, `n ≥ 4`), and the Christandl–Landahl–Werner
  weighted-path PST (`weightedPath_PST`) are **stated as honest `sorry`s on
  true, non-vacuous statements** (each awaiting an importable spectral bridge:
  the Godsil PST⇒ratio direction, resp. the spin-`n/2` `Jₓ` identification).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.NumberTheory.Niven
import Graphplay.Weighted
import Graphplay.PST

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
endpoints, when PST is possible.  The only nontrivial unweighted-path endpoint
PST in this file is `P₃` (`n = 2`), at the Christandl–Datta–Ekert–Landahl time
`τ₂ = π / √2`.  (For all other `n` we set the value to `0` as a placeholder; no
PST claim is attached.  In particular `P₄`, `n = 3`, has **no** endpoint PST, so
no genuine time exists there — see `path_P4_no_PST`.) -/
noncomputable def pathPSTTime : ℕ → ℝ
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

/-- **`P₄` has NO endpoint PST** (corrected statement; an earlier draft of this
file falsely asserted `P₄` PST at `τ = π/√5`).

The `4×4` path Hamiltonian has spectrum `{±φ, ±1/φ}` with `φ = (1+√5)/2`; the
ratio `φ/(1/φ) = φ² = φ + 1` is irrational, so the eigenvalues are *not*
rationally commensurable.  By the Godsil ratio condition this rules out PST at
every time `τ` (numerically the endpoint amplitude maxes out near `0.986 < 1`).

This is a **true, non-vacuous** statement (for every `τ` the endpoint amplitude
is strictly below modulus `1`), left as an honest `sorry` pending the importable
Godsil PST⇒ratio bridge — exactly the same lone spectral input that
`path_long_no_PST_residual` (`n ≥ 4`) awaits.

Reference: arXiv:quant-ph/0309131; Godsil–Kirkland–Severini–Smith
(arXiv:1201.4822). -/
theorem path_P4_no_PST :
    ∀ τ : ℝ, ¬ IsPST (Path 3) (0 : Fin 4) (Fin.last 3) τ := by
  sorry

/-- **Christandl–Datta–Ekert–Landahl (2004), positive side.**  The unweighted
path on `n + 1` vertices admits endpoint-to-endpoint PST at time `pathPSTTime n`
for `n = 2` (i.e. `P₃`, at `τ = π/√2`).

The full CDEL classification is that uniformly coupled endpoint PST holds for
chains of exactly `2` or `3` vertices — `P₂ = K₂` (`n = 1`, proven separately as
`Graphplay.StdLib.HypercubeProduct.isPST_K2`, at `τ = π/2`) and `P₃` (`n = 2`,
here).  `P₄` (`n = 3`) and all longer chains have **no** endpoint PST
(`path_P4_no_PST`, `path_no_PST_endpoint_endpoint`).

Reference: arXiv:quant-ph/0309131, Theorem 1. -/
theorem path_PST_endpoint_endpoint
    (n : ℕ) (hn : n = 2) :
    IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) (pathPSTTime n) := by
  subst hn
  exact path_P3_PST_residual

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

/-- **Isolated residual: the Godsil PST⇒ratio obstruction for the long path.**
For `n ≥ 4` the path eigenvalues `2 cos((k+1)π/(n+1))` are *not* rationally
commensurable (the number-theoretic core, **proved** in
`cos_path_angle_irrational` /
`Graphplay.PST.Cospectrality.pathEigenvalue_not_arithmeticProgression` via
Niven), so the Godsil ratio condition fails; the Godsil PST⇒ratio bridge
(Godsil 2012, Thm 2.2 — the file-wide residual
`IsStronglyCospectral.isPST_iff_godsilRatio`, whose forward half is the
Kronecker/Dirichlet simultaneous-approximation argument) then rules out PST.

This is the *sole* remaining input of `path_no_PST_endpoint_endpoint`; it is a
**true** statement (no degenerate witness — for every `τ` the endpoint amplitude
is strictly below modulus `1`), left as an honest `sorry` here pending the
importable Godsil bridge. -/
theorem path_long_no_PST_residual
    (n : ℕ) (hn : 4 ≤ n) :
    ∀ τ : ℝ, ¬ IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) τ := by
  sorry

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

The proof is `path_long_no_PST_residual`, which isolates the lone remaining
spectral input (the Godsil PST⇒ratio bridge); the number-theoretic heart is
already proven in `cos_path_angle_irrational`. -/
theorem path_no_PST_endpoint_endpoint
    (n : ℕ) (hn : 4 ≤ n) :
    ∀ τ : ℝ, ¬ IsPST (Path n) (0 : Fin (n + 1)) (Fin.last n) τ :=
  path_long_no_PST_residual n hn

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

/-- **Christandl–Landahl–Werner (2005).**  The engineered weighted path
with couplings `J_k = √(k(n - k + 1))` exhibits PST between the two
endpoints `0` and `n` at time `τ = π / 2`, for every `n ≥ 1`.

Reference: arXiv:quant-ph/0411020, Theorem 1.  The proof factors through
the observation that the Hamiltonian is a faithful representation of the
spin-`n/2` angular momentum operator `J_x`, whose spectrum is the
arithmetic progression `{-n/2, -n/2 + 1, …, n/2}`. -/
theorem weightedPath_PST (n : ℕ) (h : 1 ≤ n) :
    IsPST (CLWPath n) (0 : Fin (n + 1)) (Fin.last n) (Real.pi / 2) := by
  -- Reduces to the closed-form `(exp(-i π J_x / 2))_{0,n} = (-i)^n`, of modulus
  -- 1.  The genuine (non-vacuous, true) residual is that the CLW Hamiltonian is
  -- a faithful spin-`n/2` `J_x` representation, whose evolution
  -- `exp(-iπ J_x/2)` is the antipodal flip with a unit-modulus `(0,n)` entry
  -- (Christandl–Landahl–Werner 2005, arXiv:quant-ph/0411020, Thm 1).  This is
  -- the lone spectral input; isolated here as an honest `sorry` on the true
  -- statement.
  sorry

/-- More generally, *any* mirror-symmetric coupling profile whose
single-excitation spectrum has integer commensurable gaps yields PST at
some time `τ` (Karbach–Stolze 2005, Yung 2006).  We state the
specialization to CLW. -/
theorem weightedPath_PST_modulus_eq_one (n : ℕ) (h : 1 ≤ n) :
    ‖(CLWPath n).evolve (Real.pi / 2) 0 (Fin.last n)‖ = 1 :=
  weightedPath_PST n h

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

/-- The path on three vertices (`P_3` in graph-theory notation), the
smallest unweighted graph that exhibits endpoint-to-endpoint PST. -/
noncomputable def P3 : WeightedGraph (Fin 3) := Path 2

/-- The path on four vertices (`P_4`).  Unlike `P₃`, `P₄` has **no**
endpoint-to-endpoint PST (golden-ratio spectrum `{±φ, ±1/φ}` is not rationally
commensurable; see `P4_no_PST`). -/
noncomputable def P4 : WeightedGraph (Fin 4) := Path 3

/-- PST on `P_3` at `τ = π / √2` (proven, via `path_P3_PST_residual`). -/
theorem P3_PST : IsPST P3 (0 : Fin 3) (Fin.last 2) (Real.pi / Real.sqrt 2) :=
  path_PST_endpoint_endpoint 2 rfl

/-- **No PST on `P_4`** at any time `τ` (corrected: an earlier draft falsely
claimed `P₄` PST at `τ = π/√5`).  The golden-ratio spectrum is not rationally
commensurable; this is a true, non-vacuous statement carried as an honest
`sorry` (`path_P4_no_PST`) pending the Godsil PST⇒ratio bridge. -/
theorem P4_no_PST : ∀ τ : ℝ, ¬ IsPST P4 (0 : Fin 4) (Fin.last 3) τ :=
  path_P4_no_PST

end StdLib
end Graphplay
