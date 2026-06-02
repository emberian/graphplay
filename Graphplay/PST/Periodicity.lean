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
  - **`isPeriodicAt_two_mul_of_isPST`**: for a real-symmetric (`Aᵀ = A`, Godsil)
    adjacency, PST `u → v` at `τ` ⇒ periodic at `u` at time `2τ`  (the easy half
    of Godsil's necessary condition; proved from `evolve_add`, unitarity, and the
    complex-symmetry `Uᵀ = U` of the real-symmetric evolution),
  - **`isPeriodic_of_isPST`**: the existential corollary (real-symmetric),
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
import Graphplay.PST.GodsilRatio

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
theorem isPeriodicAt_two_mul_of_isPST (G : WeightedGraph V) (hsymm : G.adj.IsSymm)
    {u v : V} {τ : ℝ} (h : IsPST G u v τ) : IsPeriodicAt G u (2 * τ) :=
  -- For a real-symmetric (`Aᵀ = A`) adjacency — the classical Godsil weighted-graph
  -- setting — the evolution `U(τ) = exp(-iτ A)` is complex symmetric (`Uᵀ = U`),
  -- so `U(τ)_{v,u} = U(τ)_{u,v}` and the unimodular `(u,v)` amplitude propagates to
  -- the `(v,u)` amplitude, giving `‖U(2τ)_{u,u}‖ = ‖U(τ)_{u,v}²‖ = 1`.  The
  -- real-symmetry hypothesis is *necessary*: in the genuinely complex-Hermitian
  -- generality of `WeightedGraph` the statement is false (a cyclic permutation
  -- unitary `u→v→w→u` is row-`u`-concentrated at `v` yet has `U_{v,u} = 0`).
  -- Discharged via the existing symmetric closed form.
  isPeriodicAt_two_mul_of_isPST_of_isSymm G hsymm h

/-- **PST ⇒ periodicity (existential form).**  Any PST vertex is periodic, for a
real-symmetric (Godsil) adjacency.  This is the universal necessary condition:
every (real-weighted) graph admitting PST from `u` is periodic at `u`. -/
theorem isPeriodic_of_isPST (G : WeightedGraph V) (hsymm : G.adj.IsSymm) {u v : V}
    {τ : ℝ} (hτ : 0 < τ) (h : IsPST G u v τ) : IsPeriodic G u :=
  ⟨2 * τ, by linarith, isPeriodicAt_two_mul_of_isPST G hsymm h⟩

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

/-- **Symmetry of the periodicity conclusion.**  PST `u → v` also makes the
*target* `v` periodic at `2τ`, by the same argument applied to the `v`-column,
for a real-symmetric (`Aᵀ = A`, Godsil) adjacency.  Discharged via the existing
symmetric closed form `…_target_of_isSymm`.  (The real-symmetry hypothesis is
necessary: in the genuinely complex-Hermitian generality of `WeightedGraph` the
evolution need not be complex-symmetric and `‖U(τ)_{v,u}‖ = 1` can fail.) -/
theorem isPeriodicAt_two_mul_of_isPST_target (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm) {u v : V} {τ : ℝ} (h : IsPST G u v τ) :
    IsPeriodicAt G v (2 * τ) :=
  isPeriodicAt_two_mul_of_isPST_target_of_isSymm G hsymm h

/-! ## The deep classification (Godsil integrality; universal PST) -/

/-- The **eigenvalue support** of vertex `u`: the set of Hermitian eigenvalues
`θ_r` of `G.adj` for which the spectral idempotent `E_r` does not annihilate the
standard basis vector `e_u`.  We package it as the subset of eigenvalue *indices*
`r` whose eigenvector overlaps `u`.  (Concretely `r` is in the support iff the
`u`-coordinate of the `r`-th eigenvector is nonzero, i.e. the `(u, r)` entry of
the eigenvector unitary `U` — equivalently `eigU G u r` — is nonzero.  This is
the genuine per-vertex support `E_{θ_r} e_u ≠ 0`: the `u`-diagonal of the
spectral projector is `∑_{i : θ_i = θ_r} ‖U_{u,i}‖²`, nonzero iff some such
`U_{u,i} ≠ 0`.) -/
def eigenvalueSupport (G : WeightedGraph V) (u : V) : Set V :=
  {r | G.herm.eigenvectorUnitary u r ≠ 0}

/-! ### The periodicity forward direction (CLOSED, axiom-clean)

The forward half of Godsil's rationality criterion is now genuinely proven.
Its analytic core is a *convex-combination equality* lemma: if a finite convex
combination `∑ w_i ζ_i` of unit-modulus complex numbers `ζ_i` (`w_i ≥ 0`,
`∑ w_i = 1`) again has modulus `1`, then every `ζ_i` with `w_i > 0` equals the
combination.  Applied to the eigenbasis expansion
`U(τ)_{u,u} = ∑_i ‖U_{u,i}‖² e^{-iτ θ_i}` (weights the row-`u` Born
probabilities, which sum to `1`), periodicity `‖U(τ)_{u,u}‖ = 1` forces every
*supported* phase `e^{-iτ θ_r}` to equal the single value `U(τ)_{u,u}` — hence
all supported phases coincide, giving `τ(θ_r - θ_s) ∈ 2πℤ` and rational ratios.
-/

/-- **Convex-combination equality** (the analytic spine).  A finite convex
combination of unit-modulus complex numbers that itself has modulus `1` is
"saturated": every term with positive weight equals the combination.  Proof:
`Re(\bar S · ζ_i) ≤ 1` with weighted sum `= Re(\bar S S) = ‖S‖² = 1` and total
weight `1`, so each positive-weight term saturates `Re = 1`, forcing
`\bar S ζ_i = 1`, i.e. `ζ_i = S`. -/
theorem convex_unit_saturate {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hnorm : ‖∑ i ∈ s, (w i : ℂ) * z i‖ = 1) :
    ∀ i ∈ s, 0 < w i → z i = ∑ j ∈ s, (w j : ℂ) * z j := by
  set S : ℂ := ∑ j ∈ s, (w j : ℂ) * z j with hS
  have hSS : star S * S = ((‖S‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hexpand : (star S * S).re = ∑ i ∈ s, w i * (star S * z i).re := by
    conv_lhs => rw [hS]
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show star S * ((w i : ℂ) * z i) = (w i : ℂ) * (star S * z i) by ring,
       Complex.re_ofReal_mul]
  have hkey : ∑ i ∈ s, w i * (star S * z i).re = 1 := by
    rw [← hexpand, hSS, Complex.ofReal_re, hnorm]; norm_num
  have hbound : ∀ i ∈ s, w i * (star S * z i).re ≤ w i := by
    intro i hi
    have h1 : (star S * z i).re ≤ ‖star S * z i‖ := Complex.re_le_norm _
    have h2 : ‖star S * z i‖ = 1 := by rw [norm_mul, norm_star, hnorm, hz i hi, mul_one]
    rw [h2] at h1; nlinarith [hw i hi, h1]
  have hzero : ∀ i ∈ s, w i - w i * (star S * z i).re = 0 := by
    have hsum2 : ∑ i ∈ s, (w i - w i * (star S * z i).re) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, hkey]; ring
    intro i hi
    have hnn : ∀ j ∈ s, 0 ≤ w j - w j * (star S * z j).re := fun j hj => by
      linarith [hbound j hj]
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum2 i hi
  intro i hi hpos
  have hre1 : (star S * z i).re = 1 := by
    have hz0 := hzero i hi
    have hfac : w i * (1 - (star S * z i).re) = 0 := by ring_nf; linarith [hz0]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h (ne_of_gt hpos)
    · linarith [h]
  have hw1 : star S * z i = 1 := by
    set t : ℂ := star S * z i with ht
    have hn : ‖t‖ = 1 := by rw [ht, norm_mul, norm_star, hnorm, hz i hi, mul_one]
    have h2 : t.re ^ 2 + t.im ^ 2 = 1 := by
      have hsq := Complex.normSq_eq_norm_sq t
      rw [Complex.normSq_apply] at hsq; rw [hn] at hsq; nlinarith [hsq]
    have him : t.im = 0 := by nlinarith [sq_nonneg t.im, hre1]
    apply Complex.ext
    · rw [hre1]; rfl
    · rw [him]; rfl
  have hSstar : S * star S = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  calc z i = (S * star S) * z i := by rw [hSstar, one_mul]
    _ = S * (star S * z i) := by ring
    _ = S * 1 := by rw [hw1]
    _ = S := by rw [mul_one]

/-- The row-`u` Born probabilities `‖U_{u,i}‖²` (eigenbasis amplitudes) sum to
`1`: it is the `(u,u)` diagonal of `U Uᴴ = 1`. -/
theorem eigU_row_normSq (G : WeightedGraph V) (u : V) :
    ∑ i : V, ‖PST.eigU G u i‖ ^ 2 = 1 := by
  have h := PST.eigU_mul_conjTranspose G
  have huu := congrFun (congrFun h u) u
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at huu
  have hcast : (∑ x : V, PST.eigU G u x * (PST.eigU G)ᴴ x u)
      = ((∑ x : V, ‖PST.eigU G u x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hcast] at huu
  exact_mod_cast huu

/-- The walk diagonal as a convex combination of eigenphases:
`U(τ)_{u,u} = ∑_i ‖U_{u,i}‖² e^{-iτ θ_i}`. -/
theorem evolve_diag_convex (G : WeightedGraph V) (τ : ℝ) (u : V) :
    G.evolve τ u u = ∑ i : V, (‖PST.eigU G u i‖ ^ 2 : ℂ)
      * Complex.exp (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues i : ℂ)) := by
  rw [PST.evolve_eq_eigU_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.star_def]
  rw [show PST.eigU G u i
        * Complex.exp (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues i : ℂ))
        * (starRingEnd ℂ) (PST.eigU G u i)
      = (PST.eigU G u i * (starRingEnd ℂ) (PST.eigU G u i))
        * Complex.exp (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues i : ℂ)) by ring]
  congr 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

/-- **Periodicity collapses all supported phases.**  If `‖U(τ)_{u,u}‖ = 1`, then
for every eigenindex `r` in the support of `u` (`U_{u,r} ≠ 0`) the eigenphase
`e^{-iτ θ_r}` equals the single value `U(τ)_{u,u}`.  Immediate from
`convex_unit_saturate` applied to the convex expansion `evolve_diag_convex`. -/
theorem supported_phase_eq_diag (G : WeightedGraph V) (u : V) (τ : ℝ)
    (hper : ‖G.evolve τ u u‖ = 1) (r : V) (hr : PST.eigU G u r ≠ 0) :
    Complex.exp (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues r : ℂ))
      = G.evolve τ u u := by
  have hconv := convex_unit_saturate (Finset.univ) (fun i => ‖PST.eigU G u i‖ ^ 2)
    (fun i => Complex.exp (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues i : ℂ)))
    (fun i _ => sq_nonneg _)
    (by simpa using eigU_row_normSq G u)
    (fun i _ => by rw [Complex.norm_exp]; simp)
    (by simp only [Complex.ofReal_pow]; rw [← evolve_diag_convex G τ u]; exact hper)
    r (Finset.mem_univ r) (by positivity)
  simp only [Complex.ofReal_pow] at hconv
  rw [hconv, ← evolve_diag_convex G τ u]

/-- **The backward (Diophantine) half of Godsil's periodicity criterion — the
single isolated residual.**  If every ratio of differences of supported
eigenvalues is rational, then `u` is periodic.  This is the genuine open piece:
rational ratios mean the supported eigenvalues lie in an arithmetic progression
`b + a·k`, and one must produce a *single* time `τ > 0` with `e^{-iτ θ_r}` equal
across the (finite) support — a simultaneous Diophantine/Kronecker approximation
(`τ = 2π/a` aligns all phases once the spacing `a` is extracted).  The phase
*alignment ⇒ periodicity* step then reuses `convex_unit_saturate` /
`evolve_diag_convex` in reverse.

Honest `sorry`: needs the `AddCircle`/Kronecker simultaneous-approximation
extraction of the common spacing `a` from the rational-ratio hypothesis, not yet
developed.  Reference: Godsil, *Periodic graphs* (arXiv:1009.5375), Thm 6.1
(sufficiency). -/
theorem periodic_of_support_ratios_rational (G : WeightedGraph V) (u : V)
    (_h : ∀ r₁ r₂ r₃ r₄ : V,
        r₁ ∈ eigenvalueSupport G u → r₂ ∈ eigenvalueSupport G u →
        r₃ ∈ eigenvalueSupport G u → r₄ ∈ eigenvalueSupport G u →
        G.herm.eigenvalues r₃ ≠ G.herm.eigenvalues r₄ →
        ∃ q : ℚ, (G.herm.eigenvalues r₁ - G.herm.eigenvalues r₂)
                  = (q : ℝ) * (G.herm.eigenvalues r₃ - G.herm.eigenvalues r₄)) :
    IsPeriodic G u := by
  -- BLOCKED: backward Diophantine direction (extract common spacing `a`, set
  -- `τ = 2π/a`, align all supported phases) — AddCircle/Kronecker simultaneous
  -- approximation, not yet developed.
  sorry

/-- **Godsil's integrality / rationality criterion.**  Vertex `u` is periodic iff
the pairwise ratios of differences of eigenvalues in its support are rational;
equivalently, after a uniform rescaling the support eigenvalues are integers.
This is the spectral classification of periodicity.

The **forward direction is fully proven** here (axiom-clean): periodicity forces
all supported eigenphases equal (`supported_phase_eq_diag`), so for supported
`r, s` we have `e^{-iτ θ_r} = e^{-iτ θ_s}`, i.e. `τ(θ_r - θ_s) ∈ 2πℤ`
(`Complex.exp_eq_exp_iff_exists_int`); writing each supported difference as an
integer multiple of the common quantum `2π/τ` makes every ratio rational.

The **backward direction** (rational ratios ⇒ a common `τ` aligning every
supported phase, by simultaneous Diophantine / Kronecker approximation) is the
single remaining residual, isolated in the named lemma
`periodic_of_support_ratios_rational` below.

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
  constructor
  · -- FORWARD (CLOSED): periodicity ⇒ rational ratios of supported differences.
    rintro ⟨τ, hτpos, hper⟩ r₁ r₂ r₃ r₄ h₁ h₂ h₃ h₄ hne34
    -- All supported phases equal `U(τ)_{u,u}`; pairwise equal phases give
    -- `τ(θ_r - θ_s) ∈ 2πℤ`.
    have hphase : ∀ {a b : V}, a ∈ eigenvalueSupport G u → b ∈ eigenvalueSupport G u →
        ∃ n : ℤ, τ * (G.herm.eigenvalues a - G.herm.eigenvalues b) = 2 * Real.pi * n := by
      intro a b ha hb
      have hea := supported_phase_eq_diag G u τ hper a ha
      have heb := supported_phase_eq_diag G u τ hper b hb
      have heq : Complex.exp (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues a : ℂ))
          = Complex.exp (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues b : ℂ)) := by
        rw [hea, heb]
      rw [Complex.exp_eq_exp_iff_exists_int] at heq
      obtain ⟨n, hn⟩ := heq
      refine ⟨-n, ?_⟩
      have himeq : (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues a : ℂ)).im
          = (-(Complex.I * (τ : ℂ)) * (G.herm.eigenvalues b : ℂ)
              + n * (2 * Real.pi * Complex.I)).im := by rw [hn]
      simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re] at himeq
      push_cast; nlinarith [himeq]
    obtain ⟨n12, h12⟩ := hphase h₁ h₂
    obtain ⟨n34, h34⟩ := hphase h₃ h₄
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hn34 : n34 ≠ 0 := by
      intro h0; rw [h0] at h34; simp at h34
      rcases h34 with h | h
      · exact absurd h (ne_of_gt hτpos)
      · exact hne34 (by linarith [h])
    have hn34R : (n34 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn34
    refine ⟨(n12 : ℚ) / (n34 : ℚ), ?_⟩
    have hd12 : G.herm.eigenvalues r₁ - G.herm.eigenvalues r₂ = 2 * Real.pi * n12 / τ := by
      rw [eq_div_iff (ne_of_gt hτpos)]; linarith [h12]
    have hd34 : G.herm.eigenvalues r₃ - G.herm.eigenvalues r₄ = 2 * Real.pi * n34 / τ := by
      rw [eq_div_iff (ne_of_gt hτpos)]; linarith [h34]
    rw [hd12, hd34, Rat.cast_div]
    push_cast
    field_simp
  · -- BACKWARD: rational ratios ⇒ periodic.  Isolated as a named residual.
    exact periodic_of_support_ratios_rational G u

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
theorem isPeriodic_of_universalPST (G : WeightedGraph V) (hsymm : G.adj.IsSymm)
    {u : V} (_h : UniversalPST G u)
    (hex : ∃ v τ, v ≠ u ∧ 0 < τ ∧ IsPST G u v τ) : IsPeriodic G u := by
  obtain ⟨v, τ, _, hτ, hpst⟩ := hex
  exact isPeriodic_of_isPST G hsymm hτ hpst

/-- A **switching (vertex-permutation) automorphism** of `G` at the pair
`(u, v)`: a permutation `σ` of the vertices that swaps `u ↔ v` and fixes the
adjacency matrix (graph automorphism).  This is the *combinatorial* upgrade of
Kay's switching map — a genuine `Equiv.Perm V` adjacency automorphism.

**Caveat (why no unconditional existence theorem from PST in this file).**  Kay's
switching map `T = E₊ − E₋` (the spectral idempotents split by the parity of
`e^{−iτ θ_r}`) is an *orthogonal involution commuting with `A`* and sending the
`u`-state to the `v`-state, but it is a genuine 0/1 *permutation* matrix only
under the integer/simple-spectrum hypotheses of Kay 1310.3885.  In the
complex-Hermitian generality of `WeightedGraph` a PST host need not be
vertex-transitive, so no `SwitchingAutomorphism` (genuine vertex permutation)
need exist.  The provable operator-level content is captured by
`SwitchingUnitary` and `switchingUnitary_of_isPST` below. -/
structure SwitchingAutomorphism (G : WeightedGraph V) (u v : V) where
  /-- The underlying vertex permutation. -/
  perm : Equiv.Perm V
  /-- It swaps the two PST endpoints. -/
  swaps : perm u = v ∧ perm v = u
  /-- It preserves the (Hermitian) adjacency matrix entrywise. -/
  preserves_adj : ∀ x y, G.adj (perm x) (perm y) = G.adj x y

/-- A **switching unitary** of `G` at the pair `(u, v)` and time `τ`: the
operator-level content of Kay's switching map that PST genuinely supplies.  It is
a *unitary* `W` on the vertex Hilbert space that carries the `u`-basis state to a
unit-modulus phase multiple of the `v`-basis state — i.e. it swaps the two
endpoints *as states* (up to a global phase), the modulus-1 amplitude witnessing
perfect transfer.

This is exactly what `T = E₊ − E₋` does at the spectral level, *minus* the
unprovable (in this generality) upgrade to a 0/1 permutation matrix.  The witness
in `switchingUnitary_of_isPST` is the evolution `U(τ)` itself. -/
structure SwitchingUnitary (G : WeightedGraph V) (u v : V) (τ : ℝ) where
  /-- The underlying unitary on the vertex space. -/
  mat : Matrix V V ℂ
  /-- It is unitary: `Wᴴ W = 1`. -/
  unitary : mat.conjTranspose * mat = 1
  /-- The transfer phase (the `(u,v)` amplitude). -/
  phase : ℂ
  /-- The phase has unit modulus (perfect transfer). -/
  phase_unit : ‖phase‖ = 1
  /-- `W` sends the `u`-basis state to `phase · e_v`: the `u`-row of `W` is
  concentrated at `v` with amplitude `phase`. -/
  swaps_state : ∀ w : V, mat u w = if w = v then phase else 0

/-- **Kay's switching map, operator level (CLOSED).**  If `G` has PST between `u`
and `v` at time `τ`, then the evolution unitary `U(τ)` is a *switching unitary*:
a unitary on the vertex space carrying the `u`-state to a unit-modulus phase
multiple of the `v`-state.  This is the genuine, hypothesis-free content of Kay's
switching map `T = E₊ − E₋` at the operator level.

Axiom-clean, no `sorry`: unitarity is `evolve_unitary`, and the state-swap is
`evolve_row_concentrated` (the `u`-row concentrates at `v`, modulus 1) packaged
as the explicit `u`-row of `U(τ)`.

**Not strengthened to `SwitchingAutomorphism`** (a genuine `Equiv.Perm V`
adjacency automorphism): that holds only under the integer/simple-spectrum
hypotheses of Kay 1310.3885 (which pin `T` to a 0/1 permutation), absent here —
PST hosts need not be vertex-transitive.  See the caveat on `SwitchingAutomorphism`.

Reference: Kay, *The perfect state transfer graph limbo* (arXiv:1310.3885);
Godsil's automorphism characterization of PST. -/
theorem switchingUnitary_of_isPST (G : WeightedGraph V) {u v : V} {τ : ℝ}
    (h : IsPST G u v τ) : Nonempty (SwitchingUnitary G u v τ) :=
  ⟨{ mat := G.evolve τ
     unitary := G.evolve_unitary τ
     phase := G.evolve τ u v
     phase_unit := h
     swaps_state := fun w => by
       by_cases hw : w = v
       · subst hw; simp
       · rw [if_neg hw]
         exact evolve_row_concentrated G τ h hw }⟩

end Graphplay
