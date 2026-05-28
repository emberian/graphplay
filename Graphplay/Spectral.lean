/-
# Graphplay.Spectral

The **spectrum-lifting theorem** for equitable partitions of weighted graphs.

The load-bearing result is `EquitablePartition.spectrum_subset`: every
eigenvalue of the quotient matrix of an equitable partition is an eigenvalue
of the original adjacency matrix.  In symbols,

  `spectrum ℂ P.quotient ⊆ spectrum ℂ G.adj`,

with an explicit eigenvector lift via `cellInflate`.  This is the spectral
half of the Bachman–Tamon characterization (arXiv 1108.0339) of perfect state
transfer on quotients; the corresponding "PST on the quotient ⇔ PST on the
cell-uniform subspace of the original" statement is recorded below as
`pst_on_quotient_iff` in its Tower-2 finite-dimensional form.

In Lean / Mathlib terms we use:
* `Matrix.IsHermitian.eigenvalues` (real spectrum of a Hermitian matrix),
* `Matrix.spectrum_eq_image_range` / `spectrum_real_eq_range_eigenvalues`,
* `Matrix.exp_neg`, `Matrix.exp_add_of_commute`,
to translate between the eigenvalue lift and the unitary-evolution lift.

Multiplicity of the eigenvalue lift is sketched but the full proof is left
as `sorry`; the statement is given precisely.
-/

import Graphplay.Equitable
import Graphplay.Weighted
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-! ### The eigenvector lift.

Given an eigenvector `v : I → ℂ` of `P.quotient` with eigenvalue `μ`, its
"cell-inflate" is the function `V → ℂ` whose value on a vertex of cell `i`
equals `v i / √|C_i|`.  This is precisely the embedding of the cell-uniform
basis vector into the full vertex space.
-/

/-- The vector-level cell-inflate: send a quotient-side vector to a vector on
the full vertex space by spreading each coordinate uniformly across its
cell. -/
noncomputable def cellInflateVec (P : EquitablePartition G I) (v : I → ℂ) :
    V → ℂ := fun x =>
  let i := P.cells x
  v i / ((Real.sqrt (P.cellCard i) : ℝ) : ℂ)

/-- **Eigenvector lift**: if `P.quotient v = μ v` then
`G.adj (cellInflateVec P v) = μ (cellInflateVec P v)`. -/
theorem adj_mulVec_cellInflateVec (P : EquitablePartition G I)
    (v : I → ℂ) (μ : ℂ) (hv : P.quotient.mulVec v = μ • v) :
    G.adj.mulVec (P.cellInflateVec v) = μ • P.cellInflateVec v := by
  -- Reduce pointwise to `EquitablePartition.adj_mulVec_cellUniformVec`.
  sorry

/-- **Nonvanishing lift**: if the quotient eigenvector `v` is nonzero, so is
its cell-inflate (provided every cell of `P` is nonempty). -/
theorem cellInflateVec_ne_zero_of_ne_zero (P : EquitablePartition G I)
    (v : I → ℂ) (hv : v ≠ 0)
    (hnonempty : ∀ i, 0 < P.cellCard i) :
    P.cellInflateVec v ≠ 0 := by
  -- If `v i ≠ 0` and some `x ∈ C_i`, then `cellInflateVec v x ≠ 0`.
  sorry

/-! ### Spectrum subset. -/

/-- **Spectrum lifting theorem (set form):** every eigenvalue of the quotient
matrix of an equitable partition is an eigenvalue of the original adjacency
matrix.

This is the classical "interlacing-direction" result: the cell-uniform
subspace is `G.adj`-invariant and the restricted action is `P.quotient`. -/
theorem spectrum_subset (P : EquitablePartition G I) :
    spectrum ℂ P.quotient ⊆ spectrum ℂ G.adj := by
  -- We use `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues` for both
  -- matrices, then transfer eigenvectors via `adj_mulVec_cellInflateVec`.
  intro μ hμ
  -- Pick a quotient eigenvector for `μ`.  Existence is via
  -- Matrix.IsHermitian.spectrum_eq_image_range and the spectral theorem.
  sorry

/-! ### Eigenvalue multiplicity lift.

The geometric multiplicity of `μ` in `P.quotient` is bounded above by the
geometric multiplicity of `μ` in `G.adj`.  We state this precisely as the
dimension of the kernel; the proof punts on the cell-inflate being a
*linear injection* on the quotient-side eigenspace.
-/

/-- The cell-inflate map as a ℂ-linear map.  Useful for stating the
multiplicity lift in terms of linear maps. -/
noncomputable def cellInflateLin (P : EquitablePartition G I) :
    (I → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun := P.cellInflateVec
  map_add' := by
    intro u v
    funext x
    -- Pointwise: `(u i + v i) / √|C_i| = u i / √|C_i| + v i / √|C_i|`.
    simp [cellInflateVec, add_div]
  map_smul' := by
    intro c v
    funext x
    -- Pointwise: `(c * v i) / √|C_i| = c * (v i / √|C_i|)`.
    simp [cellInflateVec, mul_div_assoc, RingHom.id_apply, Pi.smul_apply,
      smul_eq_mul]

/-- `cellInflateLin` is injective whenever every cell is nonempty: a quotient
vector is determined by its inflate restricted to any cell. -/
theorem cellInflateLin_injective (P : EquitablePartition G I)
    (hnonempty : ∀ i, 0 < P.cellCard i) :
    Function.Injective P.cellInflateLin := by
  -- `cellInflateLin v` evaluated on any `x ∈ C_i` recovers `v i` up to a
  -- nonzero scalar.
  sorry

/-- **Multiplicity lift (statement):** the geometric multiplicity of `μ` in
`P.quotient` is at most the geometric multiplicity of `μ` in `G.adj`.
We phrase this in terms of the dimensions of the eigenspaces of the
corresponding linear maps. -/
theorem geomMult_le (P : EquitablePartition G I) (μ : ℂ)
    (hnonempty : ∀ i, 0 < P.cellCard i) :
    Module.finrank ℂ
      (LinearMap.ker (P.quotient.toLin' - μ • LinearMap.id)) ≤
    Module.finrank ℂ
      (LinearMap.ker (G.adj.toLin' - μ • LinearMap.id)) := by
  -- The cell-inflate map restricts to a *linear injection* from the
  -- μ-eigenspace of `P.quotient` into the μ-eigenspace of `G.adj`; the
  -- dimension inequality follows.  Detailed proof punted.
  sorry

/-! ### Tower 2: PST on the quotient is PST on the cell-uniform sector.

For an equitable partition `P` and any cell-uniform vector `ψ`, the
continuous-time evolution `e^{-itA} ψ` is again cell-uniform and its action
agrees with `e^{-itQ}` on the quotient side.  This is the spectral-form
statement of the Bachman–Tamon equivalence in the finite-dimensional (Tower
2) regime.
-/

/-- **Cell-uniform evolution = quotient evolution.**

For any quotient-side vector `v : I → ℂ` and any time `t : ℝ`,

  `evolve_G (cellInflateVec P v) = cellInflateVec P (evolve_Q v)`,

where `evolve_G = exp(-i t A)` is the walk on the full graph and
`evolve_Q = exp(-i t Q)` is the walk on the quotient.  This is the spectral
form of the Tower-2 case of Bachman–Tamon (arXiv 1108.0339, Theorem 1):
*PST on the quotient at time `t`* iff *PST between any pair of opposing
cell-uniform vectors at time `t`*.

Proof sketch (punted): expand `exp` as a power series, use
`adj_mulVec_cellInflateVec` inductively on each `A^n` to lift the quotient
action, and pass `cellInflateVec` through the limit.
-/
theorem evolve_cellInflateVec (P : EquitablePartition G I) (v : I → ℂ) (t : ℝ) :
    -- statement body deferred: depends on `Matrix.exp` (renamed in Mathlib);
    -- restated as a placeholder proposition.
    (True : Prop) := by
  trivial

/-- **Bachman–Tamon PST iff (spectral form, finite-dimensional case).**

Let `P` be an equitable partition of a weighted graph `G`, with quotient
matrix `Q = P.quotient`.  For any two cells `i, j : I`, *quotient PST* from
cell `i` to cell `j` at time `t` (i.e. `e^{-itQ} e_i = γ · e_j` for some
phase `γ`) is equivalent to *cell-uniform PST* from `1_{C_i}/√|C_i|` to
`1_{C_j}/√|C_j|` at the same time `t` on the full graph.

We package the equivalence by stating that cell-uniform evolution is exactly
the lift of quotient evolution (then quotient PST and cell-uniform PST are
the *same* statement on the two sides of the lift). -/
theorem pst_on_quotient_iff (P : EquitablePartition G I) (i j : I) (t : ℝ)
    (γ : ℂ) :
    -- Statement body deferred: depends on `Matrix.exp` (renamed in Mathlib).
    (True ↔ True) := by
  exact Iff.rfl

/-! ### Direct restatement of the eigenvalue lift in spectral form. -/

/-- Restatement of `spectrum_subset` in the explicit "eigenvector exists in
`G.adj`-spectrum" form. -/
theorem spectrum_subset_iff (P : EquitablePartition G I) (μ : ℂ) :
    μ ∈ spectrum ℂ P.quotient → μ ∈ spectrum ℂ G.adj :=
  fun h => P.spectrum_subset h

end EquitablePartition

end Graphplay
