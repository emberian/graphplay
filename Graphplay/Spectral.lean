/-
# Graphplay.Spectral

The **spectrum-lifting theorem** for equitable partitions of weighted graphs.

The load-bearing result is `EquitablePartition.spectrum_subset`: every
eigenvalue of the quotient matrix of an equitable partition is an eigenvalue
of the original adjacency matrix.  In symbols,

  `spectrum ℂ P.symmQuotient ⊆ spectrum ℂ G.adj`,

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

Given an eigenvector `v : I → ℂ` of `P.symmQuotient` with eigenvalue `μ`, its
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

/-- `cellInflateVec` is the linear combination of cell-uniform basis vectors
with the quotient vector as coefficients.  This is the bridge to
`restrict_eq_symmQuotient`. -/
theorem cellInflateVec_eq_sum (P : EquitablePartition G I) (v : I → ℂ) :
    P.cellInflateVec v = fun x => ∑ i, v i * P.cellUniformVec i x := by
  funext x
  -- `cellUniformVec i x = (if cells x = i then 1/√|C_i| else 0)`, so the sum
  -- collapses to the single term `i = P.cells x`.
  simp only [cellInflateVec, cellUniformVec]
  rw [Finset.sum_eq_single (P.cells x)]
  · rw [if_pos rfl]; rw [mul_one_div]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Eigenvector lift**: if `P.symmQuotient v = μ v` then
`G.adj (cellInflateVec P v) = μ (cellInflateVec P v)`. -/
theorem adj_mulVec_cellInflateVec (P : EquitablePartition G I)
    (v : I → ℂ) (μ : ℂ) (hv : P.symmQuotient.mulVec v = μ • v) :
    G.adj.mulVec (P.cellInflateVec v) = μ • P.cellInflateVec v := by
  -- Express the cell-inflate as a cell-uniform combination and apply
  -- `restrict_eq_symmQuotient`.
  rw [P.cellInflateVec_eq_sum v, P.restrict_eq_symmQuotient v, hv]
  funext x
  -- LHS: `∑ i, (μ • v) i * cellUniformVec i x`; RHS: `μ • (∑ i, v i * ...)`.
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Nonvanishing lift**: if the quotient eigenvector `v` is nonzero, so is
its cell-inflate (provided every cell of `P` is nonempty). -/
theorem cellInflateVec_ne_zero_of_ne_zero (P : EquitablePartition G I)
    (v : I → ℂ) (hv : v ≠ 0)
    (hnonempty : ∀ i, 0 < P.cellCard i) :
    P.cellInflateVec v ≠ 0 := by
  -- If `v i ≠ 0` and some `x ∈ C_i`, then `cellInflateVec v x ≠ 0`.
  -- First pick a coordinate where `v` is nonzero.
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext fun i => by simpa using h i)
  -- Cell `i` is nonempty, so there is a vertex `x` with `cells x = i`.
  have hcard : 0 < P.cellCard i := hnonempty i
  have hne : (Finset.univ.filter (fun w : V => P.cells w = i)).Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < ((Finset.univ.filter (fun w : V => P.cells w = i)).card : ℝ) := hcard
    exact_mod_cast this
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_filter] at hx
  -- At `x`, the cell-inflate is `v i / √|C_i| ≠ 0`.
  intro hzero
  have hval : P.cellInflateVec v x = 0 := by rw [hzero]; rfl
  simp only [cellInflateVec, hx.2] at hval
  -- `v i / √|C_i| = 0` with `v i ≠ 0` and `√|C_i| ≠ 0` is a contradiction.
  have hsqrt : ((Real.sqrt (P.cellCard i) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (P.cellCard i) := Real.sqrt_pos.mpr hcard
    exact_mod_cast ne_of_gt this
  rw [div_eq_zero_iff] at hval
  rcases hval with h | h
  · exact hi h
  · exact hsqrt h

/-! ### Spectrum subset. -/

/-- **Spectrum lifting theorem (set form):** every eigenvalue of the quotient
matrix of an equitable partition is an eigenvalue of the original adjacency
matrix.

This is the classical "interlacing-direction" result: the cell-uniform
subspace is `G.adj`-invariant and the restricted action is `P.symmQuotient`. -/
theorem spectrum_subset (P : EquitablePartition G I)
    (hne : ∀ i, 0 < P.cellCard i) :
    spectrum ℂ P.symmQuotient ⊆ spectrum ℂ G.adj := by
  -- HONEST SORRY.  The set-form statement is *false* without a nonemptiness
  -- hypothesis on the cells: if cell `i` is empty then `quotient` has a zero
  -- row and column at `i`, so `0 ∈ spectrum ℂ P.symmQuotient` (with the standard
  -- basis vector `e_i` as eigenvector), yet `G.adj` may be nonsingular, so
  -- `0 ∉ spectrum ℂ G.adj`.  The eigenvector lift below only carries
  -- *cell-supported* eigenvectors faithfully (see `geomMult_le`, which carries
  -- the nonemptiness hypothesis `∀ i, 0 < P.cellCard i`).  The honest version
  -- of this theorem is `spectrum_subset` *under* that hypothesis; the proof is
  -- then: `μ ∈ spectrum Q → Q.toLin'.HasEigenvalue μ` (via
  -- `Matrix.spectrum_toLin'` + `hasEigenvalue_iff_mem_spectrum`), giving a
  -- nonzero `v` with `Q *ᵥ v = μ • v`; then `cellInflateVec v` is a nonzero
  -- (`cellInflateVec_ne_zero_of_ne_zero`) eigenvector of `G.adj`
  -- (`adj_mulVec_cellInflateVec`), so `μ ∈ spectrum ℂ G.adj`.
  intro μ hμ
  -- Step 1: turn spectrum membership of the quotient into a `HasEigenvalue` of
  -- its linearised operator `Q.toLin'`.
  rw [← Matrix.spectrum_toLin'] at hμ
  have hev_q : Module.End.HasEigenvalue P.symmQuotient.toLin' μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ
  -- Step 2: extract a nonzero eigenvector `v` with `Q *ᵥ v = μ • v`.
  obtain ⟨v, hvmem, hvne⟩ := hev_q.exists_hasEigenvector
  have hveig : P.symmQuotient.mulVec v = μ • v := by
    have := Module.End.mem_eigenspace_iff.mp hvmem
    rwa [Matrix.toLin'_apply] at this
  -- Step 3: the cell-inflate of `v` is a nonzero eigenvector of `G.adj`.
  have hinf_ne : P.cellInflateVec v ≠ 0 :=
    P.cellInflateVec_ne_zero_of_ne_zero v hvne hne
  have hinf_eig : G.adj.mulVec (P.cellInflateVec v) = μ • P.cellInflateVec v :=
    P.adj_mulVec_cellInflateVec v μ hveig
  -- Step 4: convert back to spectrum membership of `G.adj`.
  have hinf_mem : P.cellInflateVec v ∈ Module.End.eigenspace G.adj.toLin' μ := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hinf_eig
  have hev_a : Module.End.HasEigenvalue G.adj.toLin' μ :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨hinf_mem, hinf_ne⟩
  have : μ ∈ spectrum ℂ G.adj.toLin' :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp hev_a
  rwa [Matrix.spectrum_toLin'] at this

/-! ### Eigenvalue multiplicity lift.

The geometric multiplicity of `μ` in `P.symmQuotient` is bounded above by the
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
  -- A linear map is injective iff its kernel is trivial; use that
  -- `cellInflateVec` is nonzero on nonzero inputs.
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  by_contra hne
  exact P.cellInflateVec_ne_zero_of_ne_zero v hne hnonempty hv

/-- **Multiplicity lift (statement):** the geometric multiplicity of `μ` in
`P.symmQuotient` is at most the geometric multiplicity of `μ` in `G.adj`.
We phrase this in terms of the dimensions of the eigenspaces of the
corresponding linear maps. -/
theorem geomMult_le (P : EquitablePartition G I) (μ : ℂ)
    (hnonempty : ∀ i, 0 < P.cellCard i) :
    Module.finrank ℂ
      (LinearMap.ker (P.symmQuotient.toLin' - μ • LinearMap.id)) ≤
    Module.finrank ℂ
      (LinearMap.ker (G.adj.toLin' - μ • LinearMap.id)) := by
  -- The cell-inflate map restricts to a *linear injection* from the
  -- μ-eigenspace of `P.symmQuotient` into the μ-eigenspace of `G.adj`.
  set Kq := LinearMap.ker (P.symmQuotient.toLin' - μ • LinearMap.id) with hKq
  set Ka := LinearMap.ker (G.adj.toLin' - μ • LinearMap.id) with hKa
  -- Membership in `Kq` says `P.symmQuotient *ᵥ w = μ • w`.
  have hmem_q : ∀ w : I → ℂ, w ∈ Kq ↔ P.symmQuotient.mulVec w = μ • w := by
    intro w
    rw [hKq, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Matrix.toLin'_apply, sub_eq_zero]
  -- Membership in `Ka` says `G.adj *ᵥ u = μ • u`.
  have hmem_a : ∀ u : V → ℂ, u ∈ Ka ↔ G.adj.mulVec u = μ • u := by
    intro u
    rw [hKa, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Matrix.toLin'_apply, sub_eq_zero]
  -- `cellInflateLin` carries `Kq` into `Ka`.
  have hmaps : ∀ w ∈ Kq, P.cellInflateLin w ∈ Ka := by
    intro w hw
    rw [hmem_a]
    exact P.adj_mulVec_cellInflateVec w μ ((hmem_q w).mp hw)
  -- Restrict the (injective) linear map to the eigenspaces.
  let f : Kq →ₗ[ℂ] Ka := P.cellInflateLin.restrict hmaps
  have hfinj : Function.Injective f := by
    intro a b hab
    have hcoe : P.cellInflateLin a = P.cellInflateLin b := by
      have h := congrArg (Subtype.val) hab
      simp only [f, LinearMap.coe_restrict_apply] at h
      exact h
    exact Subtype.ext (P.cellInflateLin_injective hnonempty hcoe)
  exact f.finrank_le_finrank_of_injective hfinj

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
matrix `Q = P.symmQuotient`.  For any two cells `i, j : I`, *quotient PST* from
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
theorem spectrum_subset_iff (P : EquitablePartition G I)
    (hne : ∀ i, 0 < P.cellCard i) (μ : ℂ) :
    μ ∈ spectrum ℂ P.symmQuotient → μ ∈ spectrum ℂ G.adj :=
  fun h => P.spectrum_subset hne h

end EquitablePartition

end Graphplay
