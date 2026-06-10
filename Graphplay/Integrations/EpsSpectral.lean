/-
# Graphplay.Integrations.EpsSpectral

**ε-approximate eigenpairs for approximately-equitable operators.**

`EquitablePartition.spectrum_subset` (Graphplay.Spectral) lifts every quotient
eigenvalue of an *exactly* equitable partition to an exact eigenvalue of the
host operator.  A learned operator `G` is never exactly equitable: it sits at
L²-operator-norm distance `≤ ε` from an equitable reference `Geq`.  This file
proves the ε-version of that spine:

1. `approx_eigenvector_of_eps_residual` — a quotient eigenpair `(μ, w)` of
   `P.symmQuotient` lifts to an ε-approximate eigenpair of `G.adj`:
   `‖G.adj (lift w) − μ · lift w‖₂ ≤ ε · ‖lift w‖₂`.  The exact intertwining
   `adj_mulVec_liftVec` disposes of `Geq`; `Matrix.l2_opNorm_mulVec` bounds the
   perturbation `(G − Geq) (lift w)`.

2. `exists_host_eigenvalue_near` — the residual bound for Hermitian matrices:
   an ε-approximate real eigenpair `(μ, v)`, `v ≠ 0`, localizes a genuine
   eigenvalue within `ε` of `μ`.  Expanding `v` in
   `Matrix.IsHermitian.eigenvectorBasis`, Parseval turns the residual into
   `∑ₖ (λₖ − μ)² |cₖ|²`; if every `|λₖ − μ| > ε` this exceeds `ε² ‖v‖²`,
   contradicting the hypothesis.  Hermiticity is needed: a Jordan block has
   tiny residuals at points far from its (defective) spectrum.

3. `exists_eigenvalue_near_of_quotient_eigenpair` — the composite, **certified
   eigenvalue localization**: every real quotient eigenvalue of a nearby
   equitable operator lies within `ε` of a genuine eigenvalue of the learned
   host, without ever diagonalizing the host.  The nondegeneracy hypotheses
   carry the content: `w ≠ 0` and nonempty cells make the lifted witness
   nonzero (an empty-celled partition lifts every `w` to `0`, for which the
   residual bound holds at any `μ` and localizes nothing).
-/

import Graphplay.Spectral
import Graphplay.Integrations.StateSpaceDSL
import Graphplay.ForMathlib.CourantFischer
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped Matrix Matrix.Norms.L2Operator
open WithLp

namespace Graphplay

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- `liftVec` is ℂ-homogeneous: scaling the quotient-side coefficients scales
the lifted state vector. -/
theorem EquitablePartition.liftVec_smul {G : WeightedGraph V}
    (P : EquitablePartition G I) (μ : ℂ) (w : I → ℂ) :
    P.liftVec (μ • w) = μ • P.liftVec w := by
  funext x
  simp only [liftVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **ε-approximate eigenvector lift.**  If `G` is within `ε` of an equitable
operator `Geq` (L² operator norm) and `(μ, w)` is an eigenpair of the
symmetric quotient of `Geq`'s partition, then the cell-uniform lift of `w` is
an ε-approximate eigenvector of `G.adj` with the *same* eigenvalue `μ`.

The equitable part is handled *exactly* by the intertwining
`adj_mulVec_liftVec`, so the entire residual is the perturbation
`(G.adj − Geq.adj)` applied to the lift — bounded by the operator norm.  No
hypothesis on `G` beyond proximity is used: in particular `G` need not admit
any equitable partition itself. -/
theorem EquitablePartition.approx_eigenvector_of_eps_residual
    (G Geq : WeightedGraph V) (P : EquitablePartition Geq I)
    {ε : ℝ} (hR : ‖G.adj - Geq.adj‖ ≤ ε)
    (μ : ℂ) (w : I → ℂ) (hw : P.symmQuotient.mulVec w = μ • w) :
    ‖(toLp 2 (G.adj.mulVec (P.liftVec w) - μ • P.liftVec w) : EuclideanSpace ℂ V)‖
      ≤ ε * ‖(toLp 2 (P.liftVec w) : EuclideanSpace ℂ V)‖ := by
  -- The reference operator reproduces the eigenpair exactly.
  have hGeq : Geq.adj.mulVec (P.liftVec w) = μ • P.liftVec w := by
    rw [P.adj_mulVec_liftVec, hw, P.liftVec_smul]
  -- So the residual is exactly the perturbation acting on the lift.
  have hres : G.adj.mulVec (P.liftVec w) - μ • P.liftVec w
      = (G.adj - Geq.adj).mulVec (P.liftVec w) := by
    rw [Matrix.sub_mulVec, hGeq]
  rw [hres]
  have hop := Matrix.l2_opNorm_mulVec (G.adj - Geq.adj)
    (toLp 2 (P.liftVec w) : EuclideanSpace ℂ V)
  exact le_trans hop (mul_le_mul_of_nonneg_right hR (norm_nonneg _))

/-- **Residual bound ⟹ eigenvalue localization** for Hermitian matrices: if
`‖H v − μ v‖₂ ≤ ε ‖v‖₂` for a *nonzero* `v` and real `μ`, some eigenvalue of
`H` lies within `ε` of `μ`.

In the eigenbasis the residual has coordinates `(λₖ − μ) cₖ`, so by Parseval
`‖Hv − μv‖² = ∑ₖ (λₖ − μ)² |cₖ|²`.  If every eigenvalue kept distance `> ε`
this sum would strictly exceed `ε² ∑ₖ |cₖ|² = ε² ‖v‖²` (some `cₖ ≠ 0` since
`v ≠ 0`) — contradiction.  `v ≠ 0` is essential: `v = 0` satisfies the
residual bound for every `μ`. -/
theorem exists_host_eigenvalue_near
    (H : Matrix V V ℂ) (hH : H.IsHermitian) (μ : ℝ) {ε : ℝ}
    (v : V → ℂ) (hv : v ≠ 0)
    (hres : ‖(toLp 2 (H.mulVec v - (μ : ℂ) • v) : EuclideanSpace ℂ V)‖
      ≤ ε * ‖(toLp 2 v : EuclideanSpace ℂ V)‖) :
    ∃ k, |hH.eigenvalues k - μ| ≤ ε := by
  by_contra hcon
  push Not at hcon
  set r : V → ℂ := H.mulVec v - (μ : ℂ) • v with hrdef
  -- Eigencoordinates of the residual: `⟨eₖ, r⟩ = (λₖ − μ) ⟨eₖ, v⟩`.
  have key : ∀ i : V,
      inner ℂ (hH.eigenvectorBasis i) (toLp 2 r : EuclideanSpace ℂ V)
        = ((hH.eigenvalues i : ℂ) - (μ : ℂ))
            * inner ℂ (hH.eigenvectorBasis i) (toLp 2 v : EuclideanSpace ℂ V) := by
    intro i
    set e : V → ℂ := ofLp (hH.eigenvectorBasis i) with he
    have hb : (toLp 2 e : EuclideanSpace ℂ V) = hH.eigenvectorBasis i := by
      rw [he, toLp_ofLp]
    rw [← hb, EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_toLp_toLp]
    -- goal: `r ⬝ᵥ star e = ((λᵢ : ℂ) − μ) * (v ⬝ᵥ star e)`
    have hHe : H *ᵥ e = hH.eigenvalues i • e := by
      rw [he]; exact hH.mulVec_eigenvectorBasis i
    have hvm : star e ᵥ* H = star (H *ᵥ e) := by
      rw [Matrix.star_mulVec, hH.eq]
    have hmain : (H *ᵥ v) ⬝ᵥ star e = (hH.eigenvalues i : ℂ) * (v ⬝ᵥ star e) := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, hvm, hHe, star_smul, star_trivial,
        smul_dotProduct, dotProduct_comm, Complex.real_smul]
    calc r ⬝ᵥ star e
        = (H *ᵥ v) ⬝ᵥ star e - (μ : ℂ) * (v ⬝ᵥ star e) := by
          rw [hrdef, sub_dotProduct, smul_dotProduct, smul_eq_mul]
      _ = ((hH.eigenvalues i : ℂ) - (μ : ℂ)) * (v ⬝ᵥ star e) := by
          rw [hmain]; ring
  -- Parseval for the residual, with the coordinates rewritten via `key`.
  have hPr : ‖(toLp 2 r : EuclideanSpace ℂ V)‖ ^ 2
      = ∑ i, (hH.eigenvalues i - μ) ^ 2
          * ‖inner ℂ (hH.eigenvectorBasis i) (toLp 2 v : EuclideanSpace ℂ V)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h1 : ∑ u, ‖(toLp 2 r : EuclideanSpace ℂ V) u‖ ^ 2 = ∑ u, ‖r u‖ ^ 2 := rfl
    rw [h1, CourantFischer.normSq_eq_sum H hH r]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i, norm_mul, mul_pow]
    congr 1
    have hcast : (hH.eigenvalues i : ℂ) - (μ : ℂ)
        = ((hH.eigenvalues i - μ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- Parseval for `v`.
  have hPv : ‖(toLp 2 v : EuclideanSpace ℂ V)‖ ^ 2
      = ∑ i, ‖inner ℂ (hH.eigenvectorBasis i) (toLp 2 v : EuclideanSpace ℂ V)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact CourantFischer.normSq_eq_sum H hH v
  -- `v ≠ 0` gives a positive coordinate mass and `ε ≥ 0`.
  have hvlp : (toLp 2 v : EuclideanSpace ℂ V) ≠ 0 := by
    intro hc
    exact hv (by simpa using congrArg ofLp hc)
  have hvpos : 0 < ‖(toLp 2 v : EuclideanSpace ℂ V)‖ := norm_pos_iff.mpr hvlp
  have hεnn : 0 ≤ ε := by
    nlinarith [norm_nonneg (toLp 2 r : EuclideanSpace ℂ V), hres, hvpos]
  have hsum_pos : 0 < ∑ i,
      ‖inner ℂ (hH.eigenvectorBasis i) (toLp 2 v : EuclideanSpace ℂ V)‖ ^ 2 := by
    rw [← CourantFischer.normSq_eq_sum H hH v]
    exact CourantFischer.normSq_pos_of_ne_zero v hv
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_lt_of_sum_lt
    (f := fun _ : V => (0 : ℝ))
    (g := fun i => ‖inner ℂ (hH.eigenvectorBasis i)
      (toLp 2 v : EuclideanSpace ℂ V)‖ ^ 2)
    (by simpa using hsum_pos)
  -- If every eigenvalue stays farther than `ε`, the residual mass is too big.
  have hstrict : ε ^ 2 * ∑ i,
        ‖inner ℂ (hH.eigenvectorBasis i) (toLp 2 v : EuclideanSpace ℂ V)‖ ^ 2
      < ∑ i, (hH.eigenvalues i - μ) ^ 2
        * ‖inner ℂ (hH.eigenvectorBasis i) (toLp 2 v : EuclideanSpace ℂ V)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
    · have h2 : ε ^ 2 ≤ (hH.eigenvalues i - μ) ^ 2 := by
        nlinarith [hcon i, hεnn, abs_nonneg (hH.eigenvalues i - μ),
          sq_abs (hH.eigenvalues i - μ)]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    · have h2 : ε ^ 2 < (hH.eigenvalues i₀ - μ) ^ 2 := by
        nlinarith [hcon i₀, hεnn, abs_nonneg (hH.eigenvalues i₀ - μ),
          sq_abs (hH.eigenvalues i₀ - μ)]
      exact mul_lt_mul_of_pos_right h2 hi₀
  -- Square the residual hypothesis and contradict.
  have hsq : ‖(toLp 2 r : EuclideanSpace ℂ V)‖ ^ 2
      ≤ ε ^ 2 * ‖(toLp 2 v : EuclideanSpace ℂ V)‖ ^ 2 := by
    nlinarith [hres, norm_nonneg (toLp 2 r : EuclideanSpace ℂ V),
      norm_nonneg (toLp 2 v : EuclideanSpace ℂ V), hεnn]
  rw [hPr, hPv] at hsq
  linarith [hstrict, hsq]

/-- **Certified eigenvalue localization.**  If the learned operator `G` is
within `ε` (L² operator norm) of an equitable operator `Geq`, then every real
eigenvalue `μ` of the symmetric quotient of `Geq`'s partition — computed on
the small index set `I` — lies within `ε` of a genuine eigenvalue of `G.adj`.

The certificate `(Geq, P, hR)` pins the host spectrum without diagonalizing
the host: combine the exact intertwining on the equitable part
(`approx_eigenvector_of_eps_residual`) with the Hermitian residual bound
(`exists_host_eigenvalue_near`).  The nonzero quotient eigenvector and
nonempty cells guarantee a nonzero lifted witness. -/
theorem EquitablePartition.exists_eigenvalue_near_of_quotient_eigenpair
    (G Geq : WeightedGraph V) (P : EquitablePartition Geq I)
    {ε : ℝ} (hR : ‖G.adj - Geq.adj‖ ≤ ε)
    (μ : ℝ) (w : I → ℂ) (hw : P.symmQuotient.mulVec w = (μ : ℂ) • w)
    (hwne : w ≠ 0) (hcells : ∀ i, 0 < P.cellCard i) :
    ∃ k, |G.herm.eigenvalues k - μ| ≤ ε := by
  have hlift : P.liftVec w ≠ 0 := by
    have heq : P.liftVec w = P.cellInflateVec w := (P.cellInflateVec_eq_sum w).symm
    rw [heq]
    exact P.cellInflateVec_ne_zero_of_ne_zero w hwne hcells
  exact exists_host_eigenvalue_near G.adj G.herm μ (P.liftVec w) hlift
    (P.approx_eigenvector_of_eps_residual G Geq hR (μ : ℂ) w hw)
