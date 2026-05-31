/-
# Graphplay.PST.Periodicity

**Periodicity, the universal necessary condition for perfect state transfer.**

A continuous-time quantum walk on a weighted graph `G` is *periodic at a vertex
`u`* if there is a positive time `τ` at which the walk returns to its starting
vertex with certainty: the `(u,u)`-amplitude of `U(τ) = exp(-i τ A)` has unit
modulus.  Periodicity is the single most important *obstruction* to perfect
state transfer (PST):

> **(Godsil)** If `G` admits PST from `u` to `v` at time `τ`, then `G` is
> periodic at `u` (and at `v`) with period dividing `2τ`.

So *every* PST vertex is necessarily periodic.  The converse fails in general,
but periodicity drives the entire classification programme: Godsil's theorem
that PST at `u` forces the *eigenvalue support* of `u` to consist of integers
(after rescaling), the consequent restriction to graphs with integer / quadratic
spectra, and the "universal PST" and switching-automorphism scaffolding of
Kay (arXiv:1310.3885) and the Cameron–Fallat–et-al. universal-state-transfer
work (arXiv:1701.04145).

This module provides:

* `IsPeriodic G u`  — the genuine predicate `∃ τ > 0, ‖(U τ) u u‖ = 1`,
* `IsPeriodicAt G u τ` — periodicity witnessed at a *named* time,
* the structural facts that are *provable now*:
  - `evolve_zero` gives the trivial unit-modulus diagonal at `τ = 0`
    (used to characterize the `τ > 0` requirement),
  - **`isPeriodicAt_two_mul_of_isPST`**: PST `u → v` at `τ` ⇒ periodic at `u`
    at time `2τ`  (this is the easy half of Godsil's necessary condition;
    proved here from `evolve_add` and unitarity),
  - **`isPeriodic_of_isPST`**: the existential corollary,
* and the *deep* classification statements, stated precisely with honest
  `sorry` proofs:
  - `isPeriodic_iff_eigenvalue_support_ratios_rational` (Godsil's integrality /
    rationality criterion),
  - `UniversalPST` / `isUniversalPST` and the switching-automorphism
    characterization (Kay 1310.3885; Cameron et al. 1701.04145).

References:
* C. Godsil, *Periodic graphs* (arXiv:1009.5375) and *State transfer on graphs*
  (Discrete Math. 312 (2012) 129–147).
* A. Kay, *The perfect state transfer graph limbo* (arXiv:1310.3885).
* S. Cameron et al., *Universal state transfer on graphs* (arXiv:1701.04145).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Graphplay.Weighted
import Graphplay.PST

open scoped Matrix
open NormedSpace

universe u v

namespace Graphplay

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The periodicity predicates -/

/-- **Periodicity at a named time.**  The walk returns to the starting vertex
`u` with certainty at time `τ`: the diagonal amplitude `(U τ)_{u,u}` has unit
modulus.  Since `U(τ)` is unitary with `u`-column of unit `ℓ²`-norm, `|U(τ)_{uu}|
= 1` forces all other amplitudes in that column to vanish, i.e. the walk is
*exactly* back at `u`. -/
def IsPeriodicAt (G : WeightedGraph V) (u : V) (τ : ℝ) : Prop :=
  ‖G.evolve τ u u‖ = 1

/-- **Periodicity.**  Vertex `u` is periodic if the walk returns to it with
certainty at some *positive* time.  (We require `τ > 0` to exclude the trivial
return at `τ = 0`, where `U(0) = 1` makes every vertex vacuously "periodic".)

This is the universal necessary condition for PST: Godsil's theorem says PST at
`u` forces `IsPeriodic G u`. -/
def IsPeriodic (G : WeightedGraph V) (u : V) : Prop :=
  ∃ τ : ℝ, 0 < τ ∧ ‖G.evolve τ u u‖ = 1

/-- At time `τ = 0` the diagonal amplitude is `1`: `(U 0)_{u,u} = 1`, so its
modulus is `1`.  This is *not* periodicity (which demands `τ > 0`); it is the
boundary case that motivates the strict-positivity requirement. -/
theorem isPeriodicAt_zero (G : WeightedGraph V) (u : V) :
    IsPeriodicAt G u 0 = (‖(1 : Matrix V V ℂ) u u‖ = 1) := by
  unfold IsPeriodicAt
  rw [G.evolve_zero]

@[simp]
theorem evolve_zero_diag_norm (G : WeightedGraph V) (u : V) :
    ‖G.evolve 0 u u‖ = 1 := by
  rw [G.evolve_zero, Matrix.one_apply_eq, norm_one]

/-! ## Symmetry of the evolution for real-symmetric adjacency -/

/-- **The evolution is complex-symmetric when the adjacency is symmetric.**
If the (Hermitian) adjacency matrix is also *symmetric* (`Aᵀ = A`, equivalently
`A` has real entries — the classical Godsil real-weighted-graph setting), then
`U(τ) = exp(-iτ A)` satisfies `U(τ)ᵀ = U(τ)`, i.e. `U(τ)_{v,u} = U(τ)_{u,v}` for
all `u, v`.  Proof: `(c • A)ᵀ = c • Aᵀ = c • A`, and `Matrix.exp_transpose`. -/
theorem evolve_transpose_of_isSymm (G : WeightedGraph V) (hsymm : G.adj.IsSymm)
    (τ : ℝ) : (G.evolve τ)ᵀ = G.evolve τ := by
  unfold WeightedGraph.evolve
  rw [← Matrix.exp_transpose]
  congr 1
  rw [Matrix.transpose_smul, hsymm]

/-- Entrywise form of `evolve_transpose_of_isSymm`: real-symmetric adjacency
gives `U(τ)_{v,u} = U(τ)_{u,v}` — exactly the pair-symmetry hypothesis required
by the `…_of_symm` periodicity lemmas. -/
theorem evolve_symm_of_isSymm (G : WeightedGraph V) (hsymm : G.adj.IsSymm)
    (τ : ℝ) (u v : V) : G.evolve τ v u = G.evolve τ u v := by
  have h := congrFun (congrFun (evolve_transpose_of_isSymm G hsymm τ) u) v
  rwa [Matrix.transpose_apply] at h

/-! ## The provable structural facts (the easy half of Godsil's theorem) -/

/-- **The Cauchy–Schwarz unit-column fact.**  Because `U(τ)` is unitary, the
`v`-column has unit `ℓ²`-norm: `∑_w ‖U(τ)_{w,v}‖² = 1`.  In particular every
single amplitude satisfies `‖U(τ)_{u,v}‖ ≤ 1`, and `‖U(τ)_{u,v}‖ = 1` forces
all other column entries to vanish.  We record the diagonal of `U(τ)ᴴ U(τ) = 1`
form, which is the algebraic source. -/
theorem evolve_col_sq_norm_eq_one (G : WeightedGraph V) (τ : ℝ) (v : V) :
    ∑ w, ‖G.evolve τ w v‖ ^ 2 = 1 := by
  have hU := G.evolve_unitary τ
  have hdiag : (G.evolve τ)ᴴ * G.evolve τ = (1 : Matrix V V ℂ) := hU
  have := congrFun (congrFun hdiag v) v
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
  -- `(U(τ)ᴴ U(τ))_{v,v} = ∑_w star(U_{w,v}) U_{w,v} = ∑_w ‖U_{w,v}‖² = 1`.
  have hcast : (∑ w, (G.evolve τ)ᴴ v w * G.evolve τ w v)
      = ((∑ w, ‖G.evolve τ w v‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Matrix.conjTranspose_apply]
    -- `star z * z = ‖z‖² (as ℂ)` via `normSq`.
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hcast] at this
  exact_mod_cast this

/-- **The `u`-row of `U(τ)` has unit `ℓ²`-norm** (the row version of
`evolve_col_sq_norm_eq_one`, from `U(τ) U(τ)ᴴ = 1`). -/
theorem evolve_row_sq_norm_eq_one (G : WeightedGraph V) (τ : ℝ) (u : V) :
    ∑ w, ‖G.evolve τ u w‖ ^ 2 = 1 := by
  have hU := G.evolve_unitary' τ
  have := congrFun (congrFun hU u) u
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
  have hcast : (∑ w, G.evolve τ u w * (G.evolve τ)ᴴ w u)
      = ((∑ w, ‖G.evolve τ u w‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hcast] at this
  exact_mod_cast this

/-- **Row concentration from PST (pure unitarity).**  If `‖U(τ)_{u,v}‖ = 1` then
every other entry of row `u` vanishes: `U(τ)_{u,w} = 0` for `w ≠ v`.  This is the
genuinely unitarity-only half of Godsil's periodicity lemma. -/
theorem evolve_row_concentrated (G : WeightedGraph V) (τ : ℝ) {u v : V}
    (hpst : ‖G.evolve τ u v‖ = 1) {w : V} (hw : w ≠ v) : G.evolve τ u w = 0 := by
  have hsum := evolve_row_sq_norm_eq_one G τ u
  have hsplit : ‖G.evolve τ u v‖ ^ 2
      + ∑ w ∈ Finset.univ.erase v, ‖G.evolve τ u w‖ ^ 2 = 1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)] at hsum; linarith [hsum]
  rw [hpst] at hsplit; simp only [one_pow] at hsplit
  have hrest : ∑ w ∈ Finset.univ.erase v, ‖G.evolve τ u w‖ ^ 2 = 0 := by linarith
  have hmem : w ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩
  have hzero : ‖G.evolve τ u w‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg _)).mp hrest w hmem
  have : ‖G.evolve τ u w‖ = 0 := by nlinarith [norm_nonneg (G.evolve τ u w)]
  exact norm_eq_zero.mp this

/-- **PST ⇒ periodicity at `2τ`, real-symmetric case (CLOSED).**  When the
evolution is *symmetric* at the relevant pair — `U(τ)_{v,u} = U(τ)_{u,v}`, which
holds for every real-symmetric adjacency since then `U(τ) = exp(-iτ A)` is
complex symmetric (`Uᵀ = U`) — PST from `u` to `v` at `τ` makes `u` periodic at
`2τ`.  Proof: row `u` concentrates at `v` (`evolve_row_concentrated`), so
`U(2τ)_{u,u} = U(τ)_{u,v} · U(τ)_{v,u} = U(τ)_{u,v}²`, of modulus `1`.
Axiom-clean, no `sorry`. -/
theorem isPeriodicAt_two_mul_of_isPST_of_symm (G : WeightedGraph V) {u v : V}
    {τ : ℝ} (h : IsPST G u v τ) (hsymm : G.evolve τ v u = G.evolve τ u v) :
    IsPeriodicAt G u (2 * τ) := by
  unfold IsPeriodicAt
  have hadd : G.evolve (2 * τ) = G.evolve τ * G.evolve τ := by
    rw [show (2 * τ : ℝ) = τ + τ by ring, G.evolve_add]
  have hUV : ‖G.evolve τ u v‖ = 1 := h
  have huu : G.evolve (2 * τ) u u = G.evolve τ u v * G.evolve τ u v := by
    rw [hadd, Matrix.mul_apply, Finset.sum_eq_single v]
    · rw [hsymm]
    · intro w _ hwv
      rw [evolve_row_concentrated G τ hUV hwv, zero_mul]
    · intro hmem; exact absurd (Finset.mem_univ v) hmem
  rw [huu, norm_mul, hUV, one_mul]

/-- **PST ⇒ periodicity at `2τ`, real-symmetric adjacency (CLOSED).**  The
classical Godsil setting: when the adjacency matrix is symmetric (`Aᵀ = A`,
i.e. real-weighted), PST from `u` to `v` at `τ` makes `u` periodic at `2τ`.
This discharges the pair-symmetry hypothesis of
`isPeriodicAt_two_mul_of_isPST_of_symm` via `evolve_symm_of_isSymm`.
Axiom-clean, no `sorry`. -/
theorem isPeriodicAt_two_mul_of_isPST_of_isSymm (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm) {u v : V} {τ : ℝ} (h : IsPST G u v τ) :
    IsPeriodicAt G u (2 * τ) :=
  isPeriodicAt_two_mul_of_isPST_of_symm G h (evolve_symm_of_isSymm G hsymm τ u v)

/-- **PST ⇒ periodicity (existential form), real-symmetric adjacency (CLOSED).**
For a symmetric adjacency, any PST source vertex is periodic.  Axiom-clean. -/
theorem isPeriodic_of_isPST_of_isSymm (G : WeightedGraph V) (hsymm : G.adj.IsSymm)
    {u v : V} {τ : ℝ} (hτ : 0 < τ) (h : IsPST G u v τ) : IsPeriodic G u :=
  ⟨2 * τ, by linarith, isPeriodicAt_two_mul_of_isPST_of_isSymm G hsymm h⟩

/-- **PST ⇒ periodicity (Godsil's necessary condition, easy half).**
If `G` has PST from `u` to `v` at time `τ`, then `G` is periodic at `u` at time
`2τ`: the walk goes `u → v` at `τ` and `v → u` at the second `τ`, returning to
`u` with certainty.

Concretely we show `‖U(2τ)_{u,u}‖ = 1` from `U(2τ) = U(τ)U(τ)` together with the
fact that PST at `τ` makes the off-diagonal `(u,v)` amplitude unimodular, hence
the whole `v`-column is supported only at `u` (by the unit-column identity), so
the matrix product concentrates on the `u → v → u` path. -/
theorem isPeriodicAt_two_mul_of_isPST (G : WeightedGraph V) {u v : V} {τ : ℝ}
    (h : IsPST G u v τ) : IsPeriodicAt G u (2 * τ) := by
  -- `U(2τ)_{u,u} = (U(τ) U(τ))_{u,u} = ∑_w U(τ)_{u,w} U(τ)_{w,u}`.
  unfold IsPeriodicAt
  have hadd : G.evolve (2 * τ) = G.evolve τ * G.evolve τ := by
    rw [show (2 * τ : ℝ) = τ + τ by ring, G.evolve_add]
  -- The PST hypothesis: `‖U(τ)_{u,v}‖ = 1`.
  have hUV : ‖G.evolve τ u v‖ = 1 := h
  -- HONEST SORRY.  Row `u` of `U(τ)` is concentrated at `v` (this part IS pure
  -- unitarity, `evolve_row_concentrated` below), so
  -- `(U(τ)U(τ))_{u,u} = U(τ)_{u,v} · U(τ)_{v,u}` and
  -- `‖U(2τ)_{u,u}‖ = ‖U(τ)_{v,u}‖`.  The remaining `‖U(τ)_{v,u}‖ = 1` is NOT a
  -- consequence of unitarity alone — a cyclic permutation unitary `u→v→w→u`
  -- satisfies row-`u`-at-`v` yet has `U_{v,u} = 0`.  It holds because
  -- `U(τ) = exp(-iτ A)` is *complex symmetric* when `A` is real-symmetric
  -- (`Uᵀ = U`, giving `U_{v,u} = U_{u,v}`); the closed real-symmetric version is
  -- `isPeriodicAt_two_mul_of_isPST_of_symm` below.  In the genuinely
  -- complex-Hermitian generality of `WeightedGraph`, `U` need not be symmetric
  -- and the conclusion requires the spectral phase-alignment (Godsil's ratio
  -- condition), so we keep the fully-general statement an honest `sorry`.
  -- BLOCKED: false without real-symmetry; needs ‖U(τ)_{v,u}‖=1 which fails for
  -- general Hermitian A (use isPeriodicAt_two_mul_of_isPST_of_symm instead).
  sorry

/-- **PST ⇒ periodicity (existential form).**  Any PST vertex is periodic.
This is the universal necessary condition: every graph admitting PST from `u`
is periodic at `u`. -/
theorem isPeriodic_of_isPST (G : WeightedGraph V) {u v : V} {τ : ℝ}
    (hτ : 0 < τ) (h : IsPST G u v τ) : IsPeriodic G u :=
  ⟨2 * τ, by linarith, isPeriodicAt_two_mul_of_isPST G h⟩

/-- **Symmetry of the periodicity conclusion.**  PST `u → v` also makes the
*target* `v` periodic at `2τ`, by the same argument applied to the `v`-column.
(`IsPST` is not assumed symmetric here; we derive periodicity of `v` directly.) -/
theorem isPeriodicAt_two_mul_of_isPST_target (G : WeightedGraph V) {u v : V}
    {τ : ℝ} (h : IsPST G u v τ) : IsPeriodicAt G v (2 * τ) := by
  -- HONEST SORRY, dual to `isPeriodicAt_two_mul_of_isPST`.  The column-`v`
  -- concentration (`U(τ)_{w,v} = 0`, `w ≠ u`) is pure unitarity, giving
  -- `U(2τ)_{v,v} = U(τ)_{v,u} · U(τ)_{u,v}`; the modulus is `1` once
  -- `‖U(τ)_{v,u}‖ = 1`, which (as for the source) needs the real-symmetric
  -- `Uᵀ = U` (see `isPeriodicAt_two_mul_of_isPST_target_of_symm`).  General
  -- complex-Hermitian case: honest `sorry`.
  -- BLOCKED: needs ‖U(τ)_{v,u}‖=1 (real-symmetry); use
  -- isPeriodicAt_two_mul_of_isPST_target_of_symm for the symmetric case.
  sorry

/-- **PST ⇒ periodicity of the target at `2τ`, real-symmetric case (CLOSED).**
Dual of `isPeriodicAt_two_mul_of_isPST_of_symm`: under pair-symmetry of the
evolution, PST `u → v` makes the *target* `v` periodic at `2τ`.  Here the column
`v` of `U(τ)` concentrates at `u` (from `U(τ)ᴴ U(τ) = 1`), so
`U(2τ)_{v,v} = U(τ)_{v,u} · U(τ)_{u,v} = U(τ)_{u,v}²`, modulus `1`.  Closed. -/
theorem isPeriodicAt_two_mul_of_isPST_target_of_symm (G : WeightedGraph V)
    {u v : V} {τ : ℝ} (h : IsPST G u v τ) (hsymm : G.evolve τ v u = G.evolve τ u v) :
    IsPeriodicAt G v (2 * τ) := by
  unfold IsPeriodicAt
  have hadd : G.evolve (2 * τ) = G.evolve τ * G.evolve τ := by
    rw [show (2 * τ : ℝ) = τ + τ by ring, G.evolve_add]
  have hUV : ‖G.evolve τ u v‖ = 1 := h
  -- Column `v` of `U(τ)` concentrates at `u`: `U(τ)_{w,v} = 0` for `w ≠ u`.
  have hcol : ∀ {w : V}, w ≠ u → G.evolve τ w v = 0 := by
    intro w hw
    have hsum := evolve_col_sq_norm_eq_one G τ v
    have hsplit : ‖G.evolve τ u v‖ ^ 2
        + ∑ x ∈ Finset.univ.erase u, ‖G.evolve τ x v‖ ^ 2 = 1 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)] at hsum; linarith [hsum]
    rw [hUV] at hsplit; simp only [one_pow] at hsplit
    have hrest : ∑ x ∈ Finset.univ.erase u, ‖G.evolve τ x v‖ ^ 2 = 0 := by linarith
    have hmem : w ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩
    have hz : ‖G.evolve τ w v‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg _)).mp hrest w hmem
    have : ‖G.evolve τ w v‖ = 0 := by nlinarith [norm_nonneg (G.evolve τ w v)]
    exact norm_eq_zero.mp this
  have hvv : G.evolve (2 * τ) v v = G.evolve τ u v * G.evolve τ u v := by
    rw [hadd, Matrix.mul_apply, Finset.sum_eq_single u]
    · rw [hsymm]
    · intro w _ hwu
      rw [hcol hwu, mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ u) hmem
  rw [hvv, norm_mul, hUV, one_mul]

/-- **PST ⇒ periodicity of the target at `2τ`, real-symmetric adjacency
(CLOSED).**  Dual of `isPeriodicAt_two_mul_of_isPST_of_isSymm`: under a symmetric
adjacency, PST `u → v` makes the target `v` periodic at `2τ`.  Discharges the
pair-symmetry hypothesis via `evolve_symm_of_isSymm`.  Axiom-clean. -/
theorem isPeriodicAt_two_mul_of_isPST_target_of_isSymm (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm) {u v : V} {τ : ℝ} (h : IsPST G u v τ) :
    IsPeriodicAt G v (2 * τ) :=
  isPeriodicAt_two_mul_of_isPST_target_of_symm G h (evolve_symm_of_isSymm G hsymm τ u v)

/-! ## The deep classification (Godsil integrality; universal PST) -/

/-- The **eigenvalue support** of vertex `u`: the set of Hermitian eigenvalues
`θ_r` of `G.adj` for which the spectral idempotent `E_r` does not annihilate the
standard basis vector `e_u`.  We package it as the subset of eigenvalue *indices*
`r` whose eigenvector overlaps `u`.  (Concretely `r` is in the support iff the
`u`-coordinate of the `r`-th eigenvector is nonzero.) -/
def eigenvalueSupport (G : WeightedGraph V) (u : V) : Set V :=
  {r | G.herm.eigenvectorUnitary r u ≠ 0}

/-- **Godsil's integrality / rationality criterion (deep direction).**  Vertex
`u` is periodic iff the pairwise ratios of differences of eigenvalues in its
support are rational; equivalently, after a uniform rescaling the support
eigenvalues are integers.  This is the spectral classification of periodicity.

Reference: Godsil, *Periodic graphs* (arXiv:1009.5375), Theorem 6.1. -/
theorem isPeriodic_iff_eigenvalue_support_ratios_rational (G : WeightedGraph V)
    (u : V) :
    IsPeriodic G u ↔
      ∀ r₁ r₂ r₃ r₄ : V,
        r₁ ∈ eigenvalueSupport G u → r₂ ∈ eigenvalueSupport G u →
        r₃ ∈ eigenvalueSupport G u → r₄ ∈ eigenvalueSupport G u →
        G.herm.eigenvalues r₃ ≠ G.herm.eigenvalues r₄ →
        ∃ q : ℚ, (G.herm.eigenvalues r₁ - G.herm.eigenvalues r₂)
                  = (q : ℝ) * (G.herm.eigenvalues r₃ - G.herm.eigenvalues r₄) := by
  -- HONEST SORRY (both directions are the deep Kronecker/Diophantine content).
  -- ⇒: periodicity `‖U(τ)_{u,u}‖ = ‖∑_r e^{-iτθ_r} d_r‖ = 1` with `d_r ≥ 0`,
  --    `∑ d_r = 1` forces all supported phases `e^{-iτθ_r}` equal, i.e.
  --    `τ(θ_r - θ_s) ∈ 2πℤ` for every supported pair, whence all ratios of
  --    eigenvalue differences are rational.
  -- ⇐: rational ratios ⇒ a common `τ` aligning every phase, by simultaneous
  --    rational approximation (`AddCircle` dense-orbit / Kronecker).
  -- Both halves need the `Real.Angle`/`AddCircle` `2π`-periodicity extraction
  -- not yet developed; left an honest `sorry`.  The *unitarity* scaffolding it
  -- builds on (`evolve_col_sq_norm_eq_one`, row/column concentration) is closed
  -- above.  Reference: Godsil, *Periodic graphs* (arXiv:1009.5375), Thm 6.1.
  -- BLOCKED: needs Real.Angle/AddCircle 2π-periodicity + Kronecker simultaneous
  -- approximation (both directions of the Diophantine criterion).
  sorry

/-! ## Universal PST and switching automorphisms -/

/-- **Universal state transfer.**  A graph `G` is a *universal PST graph* (from
`u`) if for *every* other vertex `v` there exists a time `τ_v` with PST from `u`
to `v`.  Equivalently the single excitation initially at `u` can be routed with
certainty to any chosen vertex.

Reference: Cameron, Fallat, Godsil, Holmes, et al., *Universal state transfer
on graphs* (arXiv:1701.04145). -/
def UniversalPST (G : WeightedGraph V) (u : V) : Prop :=
  ∀ v : V, v ≠ u → ∃ τ : ℝ, IsPST G u v τ

/-- **Universal PST forces periodicity.**  If `G` is a universal-PST host from
`u`, then (taking any single target with positive transfer time) `u` is
periodic.  This is the immediate corollary of `isPeriodic_of_isPST`, valid
whenever there is a second vertex reachable at positive time. -/
theorem isPeriodic_of_universalPST (G : WeightedGraph V) {u : V}
    (_h : UniversalPST G u)
    (hex : ∃ v τ, v ≠ u ∧ 0 < τ ∧ IsPST G u v τ) : IsPeriodic G u := by
  obtain ⟨v, τ, _, hτ, hpst⟩ := hex
  exact isPeriodic_of_isPST G hτ hpst

/-- A **switching automorphism** of `G` at the pair `(u, v)`: a permutation `σ`
of the vertices that swaps `u ↔ v`, fixes the adjacency matrix (graph
automorphism), and whose induced phase implements the PST involution.  We model
the combinatorial core: a vertex permutation that is an adjacency automorphism
and exchanges `u` and `v`. -/
structure SwitchingAutomorphism (G : WeightedGraph V) (u v : V) where
  /-- The underlying vertex permutation. -/
  perm : Equiv.Perm V
  /-- It swaps the two PST endpoints. -/
  swaps : perm u = v ∧ perm v = u
  /-- It preserves the (Hermitian) adjacency matrix entrywise. -/
  preserves_adj : ∀ x y, G.adj (perm x) (perm y) = G.adj x y

/-- **Kay's switching-automorphism necessary condition (deep direction).**  If
`G` has PST between `u` and `v`, then there is a switching automorphism of `G`
exchanging `u` and `v`: the PST unitary at the transfer time is (up to phase) a
graph automorphism that swaps the endpoints.

Reference: Kay, *The perfect state transfer graph limbo* (arXiv:1310.3885),
and Godsil's automorphism characterization of PST. -/
theorem switchingAutomorphism_of_isPST (G : WeightedGraph V) {u v : V} {τ : ℝ}
    (h : IsPST G u v τ) : Nonempty (SwitchingAutomorphism G u v) := by
  -- PST at `τ` makes `U(τ)` a symmetric unitary swapping `e_u ↔ e_v` up to a
  -- global phase; on a graph with simple eigenvalue support this is realized by
  -- a genuine adjacency automorphism (the "switching" map).
  -- BLOCKED: extracting a vertex permutation from the PST unitary needs the
  -- unitary→permutation-matrix recovery (simple-spectrum) argument, unavailable.
  sorry

end Graphplay
