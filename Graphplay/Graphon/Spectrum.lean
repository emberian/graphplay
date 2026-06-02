/-
# Graphon/Spectrum.lean — Continuous vs. discrete spectrum, Tower 4 closure

The classical PST machinery built on top of `Graphon/Equitable.lean` and
`Graphon/PST.lean` lives **entirely inside the cell-uniform subspace** of
`L²(Ω, μ; ℂ)`, which by `cellUniformSubspace_isClosed` is a *finite-dimensional*
closed subspace (its dimension is `Fintype.card I`).  In that finite world the
spectrum is automatically pure point, the Godsil ratio condition applies, and
cell-uniform PST reduces to finite-graph PST.

However, the **full** graphon operator `T_W := W.op` acts on a genuinely
infinite-dimensional Hilbert space and can have **continuous spectrum** — points
`λ ∈ spectrum ℂ T_W` for which the resolvent `(T_W - λ)⁻¹` fails to be a
bounded inverse but for which there is **no L²-eigenstate**.  In physical
language these are "wave-packet" or "scattering" eigenstates: generalised
eigenstates that exist only as distributions, not as honest L² vectors.

Tower 4's honest closing move is therefore to:

1.  Distinguish *pointwise* (eigenvalue, with L²-eigenstate), *continuous*
    (resolvent fails to be bounded-invertible but no L²-eigenstate exists)
    and *residual* spectrum (vacuous for self-adjoint operators).
2.  Verify that the **cell-uniform sector is always purely discrete** — it
    is finite-dimensional — and that PST is decoupled from the continuous
    spectrum in the orthogonal "fiber sector".
3.  Generalise PST to **wave-packet transfer**: unit-fidelity evolution
    between two arbitrary L²-functions, not necessarily eigenstates of
    `T_W`.
4.  Identify graphons whose spectrum is **purely continuous** (e.g. the
    constant-edge graphon, limit of complete graphs `K_n` under the cut
    norm); for these no cell-uniform PST is possible because the only
    invariant cell-uniform subspace is the (one-dimensional) constants.
5.  Lift the L1-Tower **strong cospectrality** notion to graphons, so that
    Tower-4 PST has the same syntactic shape as the finite predecessor.

Mathlib references used in statements:

* `Mathlib.MeasureTheory.Function.L2Space` — `Lp ℂ 2 μ` Hilbert space;
* `Mathlib.Analysis.NormedSpace.Spectrum` — `spectrum 𝕜 T`, the resolvent
  set, and basic API for bounded operators;
* `Mathlib.Analysis.NormedSpace.OperatorNorm.Bounded` — bounded operators on
  Banach/Hilbert spaces;
* `Mathlib.Analysis.InnerProductSpace.Spectrum` — finite-dimensional
  spectral theorem (used in the cell-uniform sector);
* `Mathlib.Topology.Algebra.Module.WeakDual` — context for generalised
  eigenstates (we do not formalise distributions here, only state the
  L²-eigenvalue condition).

Statement-only file: every theorem proof is `sorry`, but the definitions
typecheck and the propositional shape matches the finite predecessor.

References for the spectral content:

* Reed–Simon, *Methods of Modern Mathematical Physics* I, Theorem VII.5
  (decomposition of self-adjoint spectra into pure-point, absolutely
  continuous, singular continuous parts);
* Lovász, *Large Networks and Graph Limits*, §7.5 (graphon operator
  spectrum as a limit of finite spectra);
* Xie–Tamon, arXiv:2301.07251 (no infinite PST tail), the canonical
  reference for the path-tail-of-`K_n` example whose graphon limit has a
  non-trivial continuous tail-sector spectrum.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Graphplay.Graphon.Equitable
import Graphplay.Graphon.PST

open scoped MeasureTheory ENNReal Complex BigOperators Matrix
open MeasureTheory

universe u v

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {W : Graphon Ω μ}

/-! ## 1. Pointwise, continuous, and residual spectrum

For a bounded self-adjoint operator `T : H →L[ℂ] H` on a Hilbert space `H`,
the spectrum `spectrum ℂ T ⊆ ℂ` decomposes into three disjoint subsets:

* **Point spectrum** `σ_p(T) := { λ | ∃ v ≠ 0, T v = λ v }` — the
  honest eigenvalues with L²-eigenvectors.
* **Continuous spectrum** `σ_c(T) := { λ ∈ spectrum ∖ σ_p(T)
                                          | range (T - λ) is dense }` —
  the resolvent fails to be a bounded inverse, but there is no honest
  eigenvector.
* **Residual spectrum** `σ_r(T) := { λ ∈ spectrum ∖ σ_p(T)
                                          | range (T - λ) is not dense }` —
  empty for self-adjoint operators (Reed–Simon, I.VII.1).

Mathlib provides `spectrum ℂ T`; the finer decomposition is not yet
formalised, so we encode it ourselves in terms of `Module.End.HasEigenvalue`
and the closure of the range of `T - λ`. -/

/-- The **L²-eigenvalue condition**: there is a non-zero `v ∈ L²(μ)` with
`W.op v = λ • v`.  This is the *point spectrum* of the graphon operator. -/
def IsL2Eigenvalue (W : Graphon Ω μ) (lam : ℂ) : Prop :=
  ∃ v : Lp ℂ 2 μ, v ≠ 0 ∧ W.op v = lam • v

/-- The **point spectrum** `σ_p(T_W)` of the graphon operator. -/
def pointSpectrum (W : Graphon Ω μ) : Set ℂ := { lam | W.IsL2Eigenvalue lam }

/-- A spectral point `λ` is **in the continuous spectrum** if:
1.  `λ ∈ spectrum ℂ W.op` (so the resolvent fails to be bounded-invertible);
2.  `λ ∉ pointSpectrum W` (so there is **no** L²-eigenvector); and
3.  the range of `W.op - λ • id` is **dense** in `L²(μ)` (no residual
    spectrum, which is automatic for self-adjoint operators but we record
    the condition).

This is the **continuous spectrum** `σ_c(T_W)`. -/
def continuousSpectrum (W : Graphon Ω μ) : Set ℂ :=
  { lam | lam ∈ spectrum ℂ W.op ∧ lam ∉ W.pointSpectrum ∧
      Dense (Set.range (W.op - lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ))) }

/-- The **residual spectrum** is empty for self-adjoint operators.  We
record the definition for symmetry. -/
def residualSpectrum (W : Graphon Ω μ) : Set ℂ :=
  { lam | lam ∈ spectrum ℂ W.op ∧ lam ∉ W.pointSpectrum ∧
      ¬ Dense (Set.range (W.op - lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ))) }

/-- The point spectrum is contained in the spectrum: an L²-eigenvalue makes
`lam • 1 - W.op` non-injective, hence not a unit. -/
theorem pointSpectrum_subset_spectrum (W : Graphon Ω μ) :
    W.pointSpectrum ⊆ spectrum ℂ W.op := by
  rintro lam ⟨v, hv_ne, hv_eig⟩
  rw [spectrum.mem_iff]
  intro hunit
  -- `(algebraMap ℂ _ lam - W.op) v = lam • v - W.op v = 0` while `v ≠ 0`.
  have hker : (algebraMap ℂ ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) lam - W.op) v = 0 := by
    rw [ContinuousLinearMap.sub_apply, hv_eig, Algebra.algebraMap_eq_smul_one]
    show (lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) v - lam • v = 0
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, sub_self]
  obtain ⟨u, hu⟩ := hunit
  have hinj : Function.Injective (algebraMap ℂ ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) lam - W.op) := by
    rw [← hu]
    intro a b hab
    have : (↑u⁻¹ * ↑u : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) a
        = (↑u⁻¹ * ↑u : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) b := by
      simp only [ContinuousLinearMap.mul_apply]
      rw [show (u : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) a = (u : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) b
        from hab]
    rwa [u.inv_mul, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply] at this
  exact hv_ne (hinj (by rw [hker, map_zero]))

/-- The point, continuous, and residual spectrum together cover the spectrum
of `W.op`.  (Standard, c.f. Reed–Simon I, Theorem VI.5.) -/
theorem spectrum_eq_point_union_continuous_union_residual (W : Graphon Ω μ) :
    spectrum ℂ W.op =
      W.pointSpectrum ∪ W.continuousSpectrum ∪ W.residualSpectrum := by
  ext lam
  constructor
  · intro hlam
    by_cases hp : lam ∈ W.pointSpectrum
    · exact Or.inl (Or.inl hp)
    · by_cases hd : Dense (Set.range (W.op - lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)))
      · exact Or.inl (Or.inr ⟨hlam, hp, hd⟩)
      · exact Or.inr ⟨hlam, hp, hd⟩
  · rintro ((hp | hc) | hr)
    · exact W.pointSpectrum_subset_spectrum hp
    · exact hc.1
    · exact hr.1

/-- For self-adjoint operators (such as `W.op`), the **residual spectrum is
empty**.  Reed–Simon I, Theorem VII.1. -/
theorem residualSpectrum_empty (W : Graphon Ω μ) :
    W.residualSpectrum = (∅ : Set ℂ) := by
  -- standard: if `λ ∈ spectrum ∖ σ_p`, denseness of range follows from
  -- self-adjointness via the orthogonal-complement characterisation of
  -- range closure.
  ext lam
  simp only [residualSpectrum, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hspec, hnp, hndense⟩
  -- The operator `T = W.op - lam • id`.
  set T : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
    W.op - lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) with hT
  -- `W.op` is self-adjoint, so its spectral points are real: `conj lam = lam`.
  have hsa : IsSelfAdjoint W.op := W.op_isSelfAdjoint
  have hreal : (starRingEnd ℂ) lam = lam := by
    rw [Complex.conj_eq_iff_im]; exact hsa.im_eq_zero_of_mem_spectrum hspec
  -- The adjoint of `T` is `W.op - conj(lam) • id = W.op - lam • id = T`.
  have hTadj : ContinuousLinearMap.adjoint T = T := by
    rw [hT, map_sub, map_smulₛₗ, ContinuousLinearMap.adjoint_id, hsa.adjoint_eq, hreal]
  -- `¬Dense (range T)` ⟹ `(range T)ᗮ ≠ ⊥`, providing a nonzero kernel vector of `Tᴴ = T`.
  -- range of `T` as a submodule has carrier `Set.range ⇑T`.
  have hndense' : ¬ Dense (↑(LinearMap.range (T : (Lp ℂ 2 μ) →ₗ[ℂ] (Lp ℂ 2 μ))) :
      Set (Lp ℂ 2 μ)) := hndense
  -- Denseness ↔ orthogonal complement is `⊥`.
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff] at hndense'
  -- So `(range T)ᗮ ≠ ⊥`; extract a nonzero `v` with `Tᴴ v = 0`, i.e. `T v = 0`.
  have hne : (LinearMap.range (T : (Lp ℂ 2 μ) →ₗ[ℂ] (Lp ℂ 2 μ)))ᗮ ≠ ⊥ := hndense'
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hne
  -- `v ∈ (range T)ᗮ = ker Tᴴ`.
  have hker : v ∈ LinearMap.ker (ContinuousLinearMap.adjoint T :
      (Lp ℂ 2 μ) →ₗ[ℂ] (Lp ℂ 2 μ)) := by
    rw [← ContinuousLinearMap.orthogonal_range T]
    exact hv_mem
  rw [hTadj, LinearMap.mem_ker] at hker
  -- `T v = 0` gives `W.op v = lam • v`, so `lam ∈ pointSpectrum`, contradicting `hnp`.
  have heig : W.op v = lam • v := by
    have : T v = 0 := hker
    rw [hT, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, sub_eq_zero] at this
    exact this
  exact hnp ⟨v, hv_ne, heig⟩

/-- **Consequence:** the spectrum of a graphon operator splits into the
point and continuous parts only. -/
theorem spectrum_eq_point_union_continuous (W : Graphon Ω μ) :
    spectrum ℂ W.op = W.pointSpectrum ∪ W.continuousSpectrum := by
  rw [spectrum_eq_point_union_continuous_union_residual W,
    residualSpectrum_empty W, Set.union_empty]

/-! ## 2. The "has pure point spectrum" / "has continuous spectrum" predicates -/

/-- `W` has **pure point spectrum** if the spectrum of its operator is
entirely accounted for by L²-eigenvalues.  Equivalently the continuous
spectrum is empty.

In this regime classical finite-style spectral arguments — diagonalisation,
the Godsil ratio condition for PST — apply *globally* on `L²(μ)`.

This is the "well-behaved" Tower-4 regime. -/
def HasPointSpectrum (W : Graphon Ω μ) : Prop :=
  W.continuousSpectrum = (∅ : Set ℂ)

/-- `W` has **non-trivial continuous spectrum** if there exists some
`λ ∈ spectrum` that is in the continuous part, i.e. there is no L²-eigenvector
witnessing it.

This is the "honest infinite-dimensional" regime; classical PST arguments do
not apply, and the cell-uniform sector decouples from the wave-packet sector
(see `cellUniformPST_decouples_from_continuous` below). -/
def HasContinuousSpectrum (W : Graphon Ω μ) : Prop :=
  W.continuousSpectrum ≠ (∅ : Set ℂ)

/-- These two predicates are negations. -/
theorem hasPointSpectrum_iff_not_hasContinuousSpectrum (W : Graphon Ω μ) :
    W.HasPointSpectrum ↔ ¬ W.HasContinuousSpectrum := by
  unfold HasPointSpectrum HasContinuousSpectrum
  constructor
  · intro h hc; exact hc h
  · intro h
    by_contra h2
    exact h h2

/-! ## 3. Examples: discrete vs. continuous, cell-uniform sector

We catalogue the canonical examples promised by the file header. -/

/-! ### 3a. Cell-uniform sector is always discrete

The cell-uniform subspace `P.cellUniformSubspace` is finite-dimensional (it
is isometric to `EuclideanSpace ℂ I`).  Any bounded operator on a
finite-dimensional Hilbert space has pure point spectrum.  Therefore the
restriction of `W.op` to `P.cellUniformSubspace` has only point spectrum,
and that point spectrum equals the spectrum of the finite Hermitian matrix
`P.quotient`. -/

/-- The cell-uniform sector is finite-dimensional, isomorphic to `ℂ^I`. -/
theorem cellUniformSubspace_finiteDimensional
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    FiniteDimensional ℂ P.cellUniformSubspace :=
  -- the cell-uniform subspace is the span of the finite range of `cellIndicator`,
  -- hence finite-dimensional over `ℂ`.
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- **Cell-uniform discrete spectrum.**  Restricted to the cell-uniform
subspace, the graphon operator has **pure point spectrum**, and that
spectrum is exactly the spectrum of the finite matrix `P.quotient`.

This is the analytic content of the headline lifting theorem combined with
the fact that `cellUniformSubspace` is finite-dimensional. -/
theorem cellUniform_pointSpectrum [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    spectrum ℂ (Matrix.toEuclideanLin P.symmQuotient) ⊆ W.pointSpectrum := by
  -- by `op_restrict_eq_quotient`, any eigenvector of `P.symmQuotient` on `ℂ^I`
  -- transports across `cellUniformIsometry` to an L²-eigenvector of `W.op`.
  intro lam hlam
  -- Step 1: extract a nonzero eigenvector `v` of `toEuclideanLin symmQuotient`.
  have hev : Module.End.HasEigenvalue (Matrix.toEuclideanLin P.symmQuotient) lam :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlam
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff] at hv
  obtain ⟨hv_mem, hv_ne⟩ := hv
  have hv_eig : (Matrix.toEuclideanLin P.symmQuotient) v = lam • v :=
    Module.End.mem_eigenspace_iff.mp hv_mem
  -- Step 2: `B v` is a nonzero L²-eigenvector of `W.op`.
  refine ⟨P.cellUniformIsometry v, ?_, ?_⟩
  · intro h0
    exact hv_ne (P.cellUniformIsometry.injective (by rw [h0, map_zero]))
  · rw [Graphon.op_restrict_eq_quotient P v, hv_eig, map_smul]

/-! ### 3a′. Spectral convergence of the symmetric-quotient sequence

The freshly-proven matrix+time continuity lemmas of `Graphon/Limit.lean`
(`IsPST_finite_of_tendsto`, …) pass *amplitude* conditions to a limit.  The
companion **spectral** fact — that the eigenvalue set of a convergent matrix
sequence is itself limit-closed — is pure finite-dimensional matrix analysis and
is genuinely reachable here, because for an `n × n` matrix the spectrum is the
**zero set of the characteristic determinant** `λ ↦ det(λ•1 − H)`, a polynomial
in `(H, λ)` and hence jointly continuous.  Zeros of a continuous family pass to
the limit, so the spectrum is closed under simultaneous matrix/eigenvalue
convergence.

This is the spectral analogue of the Limit-file convergence theorems, and the
bridge to `pointSpectrum`: when the matrices are the **symmetric quotients**
`H n = P_n.symmQuotient` of a graphon equitable-partition sequence converging to
`Plim.symmQuotient`, any convergent sequence of their (real) eigenvalues lands in
`spectrum ℂ Plim.symmQuotient`, hence — by `cellUniform_pointSpectrum` — in
`pointSpectrum Wlim`.  No spectral-measure machinery is required, and the proof
is axiom-clean. -/

/-- **The spectrum is closed under simultaneous matrix + eigenvalue limits.**  If
`H n → Hlim` (entrywise) in `Matrix I I ℂ` and `lam n ∈ spectrum ℂ (H n)` with
`lam n → lamlim`, then `lamlim ∈ spectrum ℂ Hlim`.

The engine is `λ ∈ spectrum ℂ H ↔ det(λ•1 − H) = 0` (over the field `ℂ`,
`spectrum.mem_iff` + `Matrix.isUnit_iff_isUnit_det` + `isUnit_iff_ne_zero`)
together with joint continuity of `(H, λ) ↦ det(λ•1 − H)`
(`Continuous.matrix_det`).  Pure matrix-analytic, axiom-clean. -/
theorem spectrum_isClosed_of_tendsto
    {I : Type v} [Fintype I] [DecidableEq I]
    {H : ℕ → Matrix I I ℂ} {Hlim : Matrix I I ℂ}
    (hH : Filter.Tendsto H Filter.atTop (nhds Hlim))
    {lam : ℕ → ℂ} {lamlim : ℂ}
    (hlam : Filter.Tendsto lam Filter.atTop (nhds lamlim))
    (h_spec : ∀ n, lam n ∈ spectrum ℂ (H n)) :
    lamlim ∈ spectrum ℂ Hlim := by
  classical
  -- The characteristic determinant `g (M, z) = det(z•1 − M)`.
  set g : Matrix I I ℂ × ℂ → ℂ :=
    fun p => Matrix.det ((p.2 • (1 : Matrix I I ℂ)) - p.1) with hg
  -- `z ∈ spectrum ℂ M ↔ g (M, z) = 0`, over the field `ℂ`.
  have hmem : ∀ (M : Matrix I I ℂ) (z : ℂ),
      z ∈ spectrum ℂ M ↔ g (M, z) = 0 := by
    intro M z
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, hg]
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  -- Each `g (H n, lam n) = 0`.
  have hzero : ∀ n, g (H n, lam n) = 0 := fun n => (hmem (H n) (lam n)).mp (h_spec n)
  -- `g` is continuous: `det` of the continuous family `(M, z) ↦ z•1 − M`.
  have hg_cont : Continuous g := by
    refine Continuous.matrix_det ?_
    exact ((continuous_snd.smul continuous_const).sub continuous_fst)
  -- `(H n, lam n) → (Hlim, lamlim)`, so `g (H n, lam n) → g (Hlim, lamlim)`.
  have hpair : Filter.Tendsto (fun n => (H n, lam n)) Filter.atTop
      (nhds (Hlim, lamlim)) := hH.prodMk_nhds hlam
  have hgt : Filter.Tendsto (fun n => g (H n, lam n)) Filter.atTop (nhds (g (Hlim, lamlim))) :=
    (hg_cont.tendsto _).comp hpair
  -- The sequence is constantly `0`; by uniqueness of limits `g (Hlim, lamlim) = 0`.
  have hg0 : g (Hlim, lamlim) = 0 := by
    have hconst : Filter.Tendsto (fun n => g (H n, lam n)) Filter.atTop (nhds 0) := by
      simp only [hzero]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hgt hconst
  exact (hmem Hlim lamlim).mpr hg0

/-- **Eigenvalue convergence into the graphon point spectrum.**  Let
`P_n : GraphonEquitablePartition (W_n)` be a sequence whose symmetric quotients
`H n = P_n.symmQuotient` converge to the symmetric quotient `Plim.symmQuotient`
of a limit graphon `(Wlim, Plim)`.  If `lam n` is a (real) eigenvalue of `H n`
for each `n` and `lam n → lamlim`, then the limiting eigenvalue `lamlim` is a
genuine **L²-eigenvalue** of the limit graphon operator: `lamlim ∈
pointSpectrum Wlim`.

This composes the pure-matrix `spectrum_isClosed_of_tendsto` with the
cell-uniform spectral bridge `cellUniform_pointSpectrum` (which embeds the finite
symmetric-quotient spectrum into the graphon point spectrum via the cell-uniform
isometry).  It is the spectral counterpart of `pst_time_convergence`: amplitudes
*and* eigenvalues both transport to the graphon limit.  Axiom-clean. -/
theorem pointSpectrum_tendsto_of_symmQuotient_tendsto
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {I : Type v} [Fintype I] [DecidableEq I]
    {Wlim : Graphon Ω μ} (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    {H : ℕ → Matrix I I ℂ}
    (hH : Filter.Tendsto H Filter.atTop (nhds Plim.symmQuotient))
    {lam : ℕ → ℂ} {lamlim : ℂ}
    (hlam : Filter.Tendsto lam Filter.atTop (nhds lamlim))
    (h_spec : ∀ n, lam n ∈ spectrum ℂ (H n)) :
    lamlim ∈ Wlim.pointSpectrum := by
  -- Step 1: the limit eigenvalue is in the spectrum of the limit symmetric quotient.
  have hlim_spec : lamlim ∈ spectrum ℂ Plim.symmQuotient :=
    spectrum_isClosed_of_tendsto hH hlam h_spec
  -- Step 2: `spectrum ℂ symmQuotient = spectrum ℂ (toEuclideanLin symmQuotient)`
  -- (`toEuclideanLin` is `toLin` in the standard orthonormal basis, and matrix→End
  -- in a fixed basis is an algebra equivalence, which preserves the spectrum), then
  -- embed into `pointSpectrum` via the cell-uniform isometry bridge.
  have hlin_spec : lamlim ∈ spectrum ℂ (Matrix.toEuclideanLin Plim.symmQuotient) := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.spectrum_toLin]
    exact hlim_spec
  exact cellUniform_pointSpectrum Plim hlin_spec

/-! ### 3b. Step graphons (finite weighted graphs) — purely discrete -/

/-- A **step graphon** is one whose kernel is constant on the blocks of a
finite measurable partition.  In Graphplay these are exactly the kernels
that arise from finite weighted graphs by `Graphon.ofWeighted`.

For step graphons there is a *finest* equitable partition whose cell-uniform
subspace is all of `L²(μ)`; consequently the graphon operator has **pure
point spectrum** equal to the spectrum of the associated finite matrix.

We state the existence of such a partition as a hypothesis-shaped predicate
and the spectral consequence as a separate theorem. -/
def IsStepGraphon (W : Graphon Ω μ) : Prop :=
  ∃ (J : Type v) (_ : Fintype J) (_ : DecidableEq J)
    (P : @GraphonEquitablePartition Ω _ μ J _ _ W),
      P.cellUniformSubspace = ⊤

/-- In finite dimensions every spectral point of `W.op` is an L²-eigenvalue:
`spectrum ℂ W.op ⊆ pointSpectrum W`.  This is the bridge from the
operator-algebra spectrum (`spectrum ℂ` of a `→L[ℂ]`) to the eigenvalue
spectrum, via `ContinuousLinearMap.spectrum_eq` and the finite-dimensional
`Module.End.hasEigenvalue_iff_mem_spectrum`. -/
theorem spectrum_subset_pointSpectrum_of_finiteDimensional (W : Graphon Ω μ)
    [FiniteDimensional ℂ (Lp ℂ 2 μ)] :
    spectrum ℂ W.op ⊆ W.pointSpectrum := by
  intro lam hlam
  -- `lam ∈ spectrum` of the CLM equals `lam ∈ spectrum` of its underlying End.
  rw [ContinuousLinearMap.spectrum_eq] at hlam
  -- in finite dim this means `W.op` has eigenvalue `lam` (as an endomorphism).
  have hev : Module.End.HasEigenvalue (W.op : Module.End ℂ (Lp ℂ 2 μ)) lam :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlam
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff] at hv
  obtain ⟨hv_mem, hv_ne⟩ := hv
  exact ⟨v, hv_ne, Module.End.mem_eigenspace_iff.mp hv_mem⟩

/-- **Step graphons have pure point spectrum.**  Their spectrum is the
spectrum of a finite Hermitian matrix (the quotient adjacency for the finest
equitable partition), and there is no continuous part. -/
theorem isStepGraphon_hasPointSpectrum (W : Graphon Ω μ)
    (hW : W.IsStepGraphon) : W.HasPointSpectrum := by
  -- if the cell-uniform subspace is all of L²(μ), then L²(μ) is
  -- finite-dimensional and every spectral point is an eigenvalue
  obtain ⟨J, _, _, P, hP⟩ := hW
  -- the whole space `L²(μ)` equals the (finite-dim) cell-uniform subspace.
  haveI : FiniteDimensional ℂ (Lp ℂ 2 μ) := by
    have hfd : FiniteDimensional ℂ P.cellUniformSubspace :=
      cellUniformSubspace_finiteDimensional P
    have : FiniteDimensional ℂ (⊤ : Submodule ℂ (Lp ℂ 2 μ)) := hP ▸ hfd
    exact (Submodule.topEquiv.finiteDimensional)
  -- pure point: continuousSpectrum is empty since every spectral point is an eigenvalue.
  rw [HasPointSpectrum]
  ext lam
  simp only [continuousSpectrum, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hspec, hnp, _⟩
  exact hnp (spectrum_subset_pointSpectrum_of_finiteDimensional W hspec)

/-! ### 3c. Constant-edge graphon (limit of `K_n`) — purely continuous off
the one-dimensional cell-uniform fiber.

The constant graphon `W ≡ c` on `[0,1]` with Lebesgue measure is the
cut-norm limit of `K_n / n`.  Its integral operator `T_W = c · (1 ⊗ 1)` is
**rank one**:

* The only non-zero eigenvalue is `c · μ(Ω)` (with eigenvector the constant
  function `1`).
* The orthogonal complement (mean-zero functions) is annihilated, but **not**
  because every such function is an L²-eigenvector of eigenvalue 0 — rather
  because `0` is in the **continuous spectrum** of the rank-one operator
  restricted to that complement.

(*Technically* on the mean-zero complement the rank-one operator acts as 0,
so 0 is an eigenvalue of infinite multiplicity.  The "continuous spectrum"
phenomenon we care about appears for the graphon limit of `K_n + P_n` — see
below.  We record the rank-one example for completeness.) -/

/-- **Constant graphon predicate.**  `W` is constant if its kernel equals a
fixed scalar `c` almost everywhere off the diagonal. -/
def IsConstant (W : Graphon Ω μ) (c : ℂ) : Prop :=
  ∀ᵐ p ∂(μ.prod μ), p.1 ≠ p.2 → W.kernel p.1 p.2 = c

/-- **Constant-graphon slice integral (atomless case).**  For a constant graphon
`W ≡ c` over an *atomless* finite measure, the per-vertex flux slice integral is
explicit:  `∫ y, W.kernel x y ∂μ = c · μ(Ω)` for `μ`-a.e. `x`.

This is the genuine analytic core of the constant-graphon spectrum: the
product-a.e. constancy hypothesis `IsConstant c` becomes, by Fubini
(`Measure.ae_ae_of_ae_prod`), a per-row a.e. statement; under `[NoAtoms μ]`
each singleton `{x}` is `μ`-null, so the diagonal exclusion `y ≠ x` drops out
and the slice integrand is `c` for a.e. `y`.  The atomless hypothesis is genuine
— on an atomic measure the diagonal `W.kernel x x = 0` (looplessness) contributes
and the slice integral is `c · (μ(Ω) − μ{x})`, *not* `c · μ(Ω)`. -/
theorem constant_op_slice [NoAtoms μ] (W : Graphon Ω μ) (c : ℂ)
    (hW : W.IsConstant c) :
    ∀ᵐ x ∂μ, (∫ y, W.kernel x y ∂μ) = c * (μ Set.univ).toReal := by
  -- Fubini: from product-a.e. to per-row a.e.
  have hrow : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, x ≠ y → W.kernel x y = c :=
    Measure.ae_ae_of_ae_prod hW
  filter_upwards [hrow] with x hx
  -- Under `[NoAtoms μ]`, `{x}` is null, so `∀ᵐ y, y ≠ x`.
  have hne : ∀ᵐ y ∂μ, y ≠ x := by
    have : μ {x} = 0 := measure_singleton x
    rw [ae_iff]
    simpa only [not_not] using this
  -- Combine: the integrand is `c` a.e.
  have hae : (fun y => W.kernel x y) =ᵐ[μ] fun _ => c := by
    filter_upwards [hx, hne] with y hyc hyne
    exact hyc (Ne.symm hyne)
  rw [integral_congr_ae hae, integral_const, Complex.real_smul]
  show ((μ.real Set.univ : ℝ) : ℂ) * c = c * ((μ Set.univ).toReal : ℂ)
  rw [show (μ.real Set.univ : ℝ) = (μ Set.univ).toReal from rfl]
  ring

/-- A constant non-zero graphon has a single non-zero L²-eigenvalue
(the constant function `1`); the orthogonal complement has spectrum `{0}`,
and the only invariant cell-uniform sector is one-dimensional.

**Proven** for the canonical *atomless* constant graphon (the `K_n`-limit
regime, e.g. Lebesgue measure on `[0,1]`): the witness is the constant
function `1 ∈ L²(μ)` (`indicatorConstLp` over the whole space).  By
`constant_op_slice` the slice integral `∫ y, W.kernel x y ∂μ = c · μ(Ω)` for
a.e. `x`, so `W.op 1 = (c · μ(Ω)) • 1`.  The `[NoAtoms μ]` hypothesis is the
genuine atomless requirement (see `constant_op_slice`). -/
theorem constant_pointSpectrum [NoAtoms μ] (W : Graphon Ω μ) (c : ℂ) (_hc : c ≠ 0)
    (hW : W.IsConstant c) (hμ : μ Set.univ ≠ ∞) (hμ0 : μ Set.univ ≠ 0) :
    (c * (μ Set.univ).toReal) ∈ W.pointSpectrum := by
  classical
  -- The constant function `1 ∈ L²(μ)` as `indicatorConstLp` over the whole space.
  set one : Lp ℂ 2 μ := MeasureTheory.indicatorConstLp 2 MeasurableSet.univ hμ (1 : ℂ) with hone
  refine ⟨one, ?_, ?_⟩
  · -- `one ≠ 0`: its norm is `‖1‖ · μ(univ)^{1/2} ≠ 0` since `μ(univ) ≠ 0`.
    intro h0
    have hn : ‖one‖ = 0 := by rw [h0, norm_zero]
    rw [hone, MeasureTheory.norm_indicatorConstLp (by norm_num) (by norm_num)] at hn
    simp only [norm_one, one_mul] at hn
    have : (μ Set.univ).toReal = 0 := by
      have := Real.rpow_eq_zero_iff_of_nonneg ENNReal.toReal_nonneg |>.1 hn
      exact this.1
    exact hμ0 ((ENNReal.toReal_eq_zero_iff _).1 this |>.resolve_right hμ)
  · -- `W.op one = (c · μ(univ)) • one`: compare coeFns a.e.
    apply Lp.ext
    -- LHS coeFn `=ᵐ opFun one`.
    have hLHS : ⇑(W.op one) =ᵐ[μ] W.opFun ((one : Ω → ℂ)) := by
      unfold Graphon.op
      rw [Graphplay.ForMathlib.kernelIntegralCLM_apply]
      exact (W.opFun_memLp one).coeFn_toLp
    -- `one`'s coeFn is `=ᵐ fun _ => 1`.
    have hone_coe : ⇑one =ᵐ[μ] fun _ => (1 : ℂ) := by
      rw [hone]
      filter_upwards [MeasureTheory.indicatorConstLp_coeFn
        (hs := MeasurableSet.univ) (hμs := hμ) (c := (1 : ℂ))] with x hx
      rw [hx, Set.indicator_of_mem (Set.mem_univ x)]
    -- RHS coeFn `=ᵐ fun _ => (c·μ(univ)) · 1`.
    have hRHS : ⇑((c * (μ Set.univ).toReal) • one)
        =ᵐ[μ] fun _ => (c * (μ Set.univ).toReal) * (1 : ℂ) := by
      filter_upwards [Lp.coeFn_smul (c * (μ Set.univ).toReal) one, hone_coe] with x hx hx2
      rw [hx, Pi.smul_apply, hx2, smul_eq_mul]
    -- the slice integral is constant a.e.
    refine hLHS.trans (Filter.EventuallyEq.trans ?_ hRHS.symm)
    filter_upwards [constant_op_slice W c hW, hone_coe] with x hslice hone_x
    show (∫ y, W.kernel x y * (one : Ω → ℂ) y ∂μ) = (c * (μ Set.univ).toReal) * 1
    rw [mul_one]
    -- replace `one y` by `1` a.e. inside the integral, then apply the slice value.
    have : (fun y => W.kernel x y * (one : Ω → ℂ) y) =ᵐ[μ] fun y => W.kernel x y := by
      filter_upwards [hone_coe] with y hy
      rw [hy, mul_one]
    rw [integral_congr_ae this, hslice]

/-! ### 3d. The Xie–Tamon graphon (`K_n + path-n`) — continuous tail sector.

Xie–Tamon (arXiv:2301.07251) showed that augmenting `K_n` with a path of
length `n` destroys PST on the original cell-uniform sector.  In the
graphon limit, the path-tail becomes a **continuous-spectrum sector**:
the operator restricted to the tail is unitarily equivalent to a
multiplication operator on `L²([0,1])`, which has purely continuous
spectrum.

We record only the existence statement. -/
structure HasContinuousTailSector (W : Graphon Ω μ) : Prop where
  /-- A non-trivial closed subspace where the restriction of `W.op` has
  purely continuous spectrum. -/
  exists_tail :
    ∃ (S : Submodule ℂ (Lp ℂ 2 μ)),
      S ≠ ⊥ ∧ IsClosed (S : Set (Lp ℂ 2 μ)) ∧
      (∀ f ∈ S, W.op f ∈ S) ∧
      -- the restriction of `W.op` to `S` has **no** L²-eigenvectors: the sector
      -- is purely continuous, i.e. every nonzero `f ∈ S` fails the eigenvalue
      -- equation for every scalar `lam`.
      (∀ f ∈ S, f ≠ 0 → ∀ lam : ℂ, W.op f ≠ lam • f)

/-- The Xie–Tamon construction (statement only): there is a graphon `W`
which has both a non-trivial cell-uniform PST sector **and** a continuous
tail sector. -/
theorem xieTamon_exists_continuous_tail :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsFiniteMeasure μ)
      (W : Graphon Ω μ),
      W.HasContinuousSpectrum ∧ W.HasContinuousTailSector := by
  -- the explicit construction is `K_n + path-n` regularised; statement only.
  --
  -- HONEST GAP — *not* wired to `SpectralMeasureSelfAdjoint`, and here is why.
  -- The literature interface `Graphplay.LiteratureInterfaces.SpectralMeasureSelfAdjoint`
  -- certifies the existence of *some* self-adjoint operator `T` on *some* abstract
  -- Hilbert space `H` carrying a **single** no-eigenvector vector `v`
  -- (`exists_continuous_sector : ∃ H T, IsSelfAdjoint T ∧ ∃ v ≠ 0, ∀ lam, T v ≠ lam • v`).
  -- That is strictly weaker than what this theorem's conclusion demands:
  --
  --   * `HasContinuousTailSector` requires a *whole closed `W.op`-invariant
  --     subspace* `S ≠ ⊥` in which **every** nonzero vector fails the eigenvalue
  --     equation — the interface supplies one such vector, not an invariant
  --     subspace of them, and `span{v}` is not `op`-invariant (precisely because
  --     `T v` is not a scalar multiple of `v`);
  --   * `HasContinuousSpectrum` requires `continuousSpectrum W ≠ ∅`, a property of
  --     the *concrete graphon integral operator's* spectrum, whereas `T` lives on
  --     an abstract `H` with no `Graphon.op W = T` realisation available (graphon
  --     ops are integral operators with specific kernel structure; not every
  --     self-adjoint operator is one).
  --
  -- The interface itself documents that wiring `T` to `Graphon.op` is the
  -- consumer's remaining obligation.  Supplying that bridge in a form strong
  -- enough to close the conclusion would have to additionally assume the
  -- invariant-subspace / all-vectors-no-eigenvector data — i.e. essentially the
  -- conclusion itself — which would be a *vacuous* threading.  We therefore leave
  -- this honest: the genuine missing content is the spectral theory of
  -- multiplication operators (purely continuous spectrum) for the concrete
  -- `K_n + path-n` graphon, beyond both Mathlib and the abstract existence
  -- certified by `SpectralMeasureSelfAdjoint`.
  sorry

/-! ## 4. PST under a continuous spectrum: the cell-uniform sector decouples

The key Tower-4 observation: even when the *full* graphon operator has a
non-trivial continuous spectrum, **cell-uniform PST depends only on the
discrete part of the spectrum that lives inside the cell-uniform subspace**.

This is because:
1.  The cell-uniform subspace is invariant under `W.op` (and therefore
    under `W.evolve τ`).
2.  Inner products between cell indicators only see the cell-uniform sector.
3.  On the cell-uniform sector, spectrum is automatically pure point (the
    sector is finite-dimensional). -/

/-- **Cell-uniform PST decouples from the continuous spectrum.**

Cell-uniform PST `IsCellUniformPST W P i j τ` holds *iff* the finite
Hermitian matrix `P.quotient` satisfies the Godsil ratio condition between
standard-basis vectors `E_i, E_j` (this is `IsPST_finite P.quotient i j τ`,
already stated in `Graphon/PST.lean`).

In particular **the continuous part of `spectrum ℂ W.op` is invisible** to
this question; only the eigenvalues of `P.quotient` matter.

We state the theorem in the language of the existing `IsCellUniformPST` and
`IsPST_finite` predicates from `Graphon/PST.lean`. -/
theorem cellUniformPST_decouples_from_continuous
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) (τ : ℝ) :
    -- cell-uniform PST depends only on the discrete part of the spectrum,
    -- restricted to the (finite-dimensional, hence pure-point) cell-uniform
    -- subspace: it is exactly finite PST on the symmetric quotient matrix
    -- `P.symmQuotient`, with no reference to the continuous part of `W.op`.
    IsCellUniformPST W P i j τ ↔ IsPST_finite P.symmQuotient i j τ :=
  -- genuine: this is the headline PST theorem of `Graphon/PST.lean`, which is
  -- itself proven (modulo the single named `exp`-lift gap it depends on).
  Graphon.cellUniformPST_iff_quotientPST P i j τ

/-! ## 5. Wave-packet PST: a generalisation to non-eigenstate transfer

For graphons with continuous spectrum, "perfect transfer between
eigenstates" is **not the right concept** — there may be no L²-eigenstates
at all.  The generalisation is **wave-packet PST**: pick any two
normalised L²-functions `φ₀, φ₁` and ask whether `W.evolve τ` sends `φ₀`
to (a phase times) `φ₁` exactly.

This recovers cell-uniform PST when `φ₀ = e_i, φ₁ = e_j`. -/

/-- **Wave-packet (perfect) transfer.**  Two normalised L²-states `φ₀, φ₁`
and a time `τ` exhibit *wave-packet PST* if
$$ \big| \langle \varphi_1,\; W.\mathrm{evolve}(\tau)\; \varphi_0 \rangle \big|
    = 1.$$
Equivalently, `W.evolve τ φ₀ = e^{i α} • φ₁` for some phase `α ∈ ℝ`.

This is the natural Tower-4 analogue of finite-graph PST that survives the
existence of continuous spectrum: `φ₀, φ₁` need not be eigenstates. -/
def IsWavePacketTransfer (W : Graphon Ω μ) (phi0 phi1 : Lp ℂ 2 μ) (τ : ℝ) :
    Prop :=
  ‖phi0‖ = 1 ∧ ‖phi1‖ = 1 ∧
  ‖inner ℂ phi1 (W.evolve τ phi0)‖ = 1

/-- Cell-uniform PST is a special case of wave-packet PST. -/
theorem isCellUniformPST_iff_isWavePacketTransfer
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) (τ : ℝ) :
    IsCellUniformPST W P i j τ ↔
      W.IsWavePacketTransfer (P.cellIndicator i) (P.cellIndicator j) τ := by
  -- normalisation of `cellIndicator` plus unfolding both definitions
  have hi : ‖P.cellIndicator i‖ = 1 :=
    (Graphon.cellIndicator_orthonormal P).norm_eq_one i
  have hj : ‖P.cellIndicator j‖ = 1 :=
    (Graphon.cellIndicator_orthonormal P).norm_eq_one j
  unfold IsCellUniformPST IsWavePacketTransfer
  constructor
  · intro h; exact ⟨hi, hj, h⟩
  · intro h; exact h.2.2

/-- **Wave-packet PST is exact phase transfer.**  For normalised states
`φ₀, φ₁`, wave-packet PST at time `τ` is equivalent to `W.evolve τ` sending
`φ₀` to a **unit phase** times `φ₁`:
$$ \mathrm{WavePacketPST} \iff \exists\, \alpha \in \mathbb{R},\;
   W.\mathrm{evolve}(\tau)\,\varphi_0 = e^{i\alpha}\,\varphi_1. $$
This is the genuine "transfer up to a phase" reformulation of the
modulus-one inner-product condition (Cauchy–Schwarz equality case for unit
vectors), and is the right Tower-4 shape of the finite Godsil criterion.

The `HasPointSpectrum` hypothesis is recorded for context (in the pure-point
regime the phase `α` is computed from the eigenvalue ratios, the Godsil
condition); the equivalence itself holds generally for unit vectors.  **Proven**
axiom-cleanly via the `Lp` Cauchy–Schwarz equality characterisation
`norm_inner_eq_norm_iff` (colinearity with a unit-modulus scalar) plus the
unitarity of `evolve`. -/
theorem isWavePacketTransfer_pointSpectrum
    (W : Graphon Ω μ) (phi0 phi1 : Lp ℂ 2 μ) (τ : ℝ)
    (_h : W.HasPointSpectrum)
    (hphi0 : ‖phi0‖ = 1) (hphi1 : ‖phi1‖ = 1) :
    W.IsWavePacketTransfer phi0 phi1 τ ↔
      ∃ α : ℝ, W.evolve τ phi0 = (Complex.exp (Complex.I * α)) • phi1 := by
  -- the modulus-one overlap of two unit vectors is the Cauchy–Schwarz equality
  -- case, which forces colinearity with a unit-modulus (hence phase) scalar.
  -- First, `W.evolve τ` is norm-preserving (unitary), so `‖evolve τ φ₀‖ = 1`.
  have hnorm_evolve : ‖W.evolve τ phi0‖ = 1 := by
    have hinner : (inner ℂ (W.evolve τ phi0) (W.evolve τ phi0) : ℂ)
        = (inner ℂ phi0 phi0 : ℂ) := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      have hu := congrFun (congrArg
        (fun (T : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) => (T : Lp ℂ 2 μ → Lp ℂ 2 μ))
        (W.evolve_isUnitary τ)) phi0
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.id_apply] at hu
      rw [hu]
    have h2 : ((‖W.evolve τ phi0‖ : ℂ)) ^ 2 = ((‖phi0‖ : ℂ)) ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at hinner
      exact hinner
    have h3 : ‖W.evolve τ phi0‖ ^ 2 = ‖phi0‖ ^ 2 := by exact_mod_cast h2
    rw [hphi0] at h3
    nlinarith [norm_nonneg (W.evolve τ phi0), h3]
  constructor
  · -- forward: modulus-one overlap ⟹ colinearity with unit scalar.
    rintro ⟨_, _, hpst⟩
    have hphi1_ne : phi1 ≠ 0 := by
      intro h; rw [h, norm_zero] at hphi1; exact zero_ne_one hphi1
    have hev_ne : W.evolve τ phi0 ≠ 0 := by
      intro h; rw [h, norm_zero] at hnorm_evolve; exact zero_ne_one hnorm_evolve
    -- Cauchy–Schwarz equality: `evolve τ φ₀ = r • φ₁` with `r ≠ 0`.
    have heq : ‖(inner ℂ phi1 (W.evolve τ phi0) : ℂ)‖ = ‖phi1‖ * ‖W.evolve τ phi0‖ := by
      rw [hpst, hphi1, hnorm_evolve, mul_one]
    obtain ⟨r, hr_ne, hr⟩ := (norm_inner_eq_norm_iff hphi1_ne hev_ne).1 heq
    -- `‖r‖ = 1` since `‖evolve τ φ₀‖ = ‖r‖ · ‖φ₁‖`.
    have hr_norm : ‖r‖ = 1 := by
      have : ‖W.evolve τ phi0‖ = ‖r‖ * ‖phi1‖ := by rw [hr, norm_smul]
      rw [hnorm_evolve, hphi1, mul_one] at this
      exact this.symm
    -- A unit-modulus complex `r` is `exp(I·arg r)`.
    refine ⟨r.arg, ?_⟩
    rw [hr]
    congr 1
    have := Complex.norm_mul_exp_arg_mul_I r
    rw [hr_norm, Complex.ofReal_one, one_mul] at this
    rw [mul_comm (Complex.I)]; exact this.symm
  · -- reverse: `evolve τ φ₀ = exp(I·α) • φ₁` ⟹ modulus-one overlap.
    rintro ⟨α, hα⟩
    refine ⟨hphi0, hphi1, ?_⟩
    rw [hα, inner_smul_right, norm_mul, Complex.norm_exp]
    have hre : (Complex.I * (α : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
    -- `⟪φ₁, φ₁⟫ = (‖φ₁‖ : ℂ)^2`, so its norm is `‖φ₁‖^2 = 1`.
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    rw [hphi1]
    simp

/-! ## 6. Failure modes: purely continuous spectrum kills PST

A graphon whose **entire** spectrum is continuous has *no* L²-eigenstates,
hence no eigenstate-PST.  Cell-uniform PST is also impossible unless the
cell-uniform subspace is the trivial constants — and even there the only
possible "transfer" is the identity.

The canonical example is the constant-edge graphon limit of `K_n` modulo
its 1-dimensional constant sector. -/

/-- **Wave-packet transfer forces the return amplitude to vanish.**  If two
normalised L²-states `φ₀ ⊥ φ₁` exhibit wave-packet PST at time `τ`, then the
*return amplitude* `⟨φ₀, W.evolve τ φ₀⟩` is **zero**: the evolved state has left
the initial direction entirely (it sits on the `φ₁` ray).

**False→true migration.**  The original headline here —
*"if `pointSpectrum W = ∅` then no wave-packet PST between orthogonal states at
any `τ ≠ 0`"* — is **FALSE** as stated, and the "BLOCKED on spectral measures"
note was masking a genuine counterexample, not just a missing Mathlib lemma:

  Take `W.op` unitarily equivalent to multiplication by `x` on `L²([0,1])`
  (purely **continuous** spectrum, so `pointSpectrum W = ∅`), and `φ₀` the
  constant `1`.  Its spectral measure is Lebesgue on `[0,1]`, whose
  characteristic function `⟨φ₀, evolve τ φ₀⟩ = ∫₀¹ e^{-iτx} dx = (e^{-iτ}-1)/(-iτ)`
  **vanishes** at `τ = 2π`.  Set `φ₁ := W.evolve (2π) φ₀`.  Then `‖φ₁‖ = 1`
  (unitarity), `⟨φ₀, φ₁⟩ = 0` (the integral above is `0`), so `φ₀ ⊥ φ₁` is an
  orthogonal normalised pair — yet `‖⟨φ₁, evolve (2π) φ₀⟩‖ = ‖⟨φ₁,φ₁⟩‖ = 1`, i.e.
  wave-packet PST **holds** at `τ = 2π ≠ 0`.  Pure continuity does **not**
  preclude wave-packet transfer.

The genuine content surviving this counterexample is the **necessary condition**
stated here, and it is exactly the spectral fact the false claim was groping at:
wave-packet PST is the Cauchy–Schwarz equality case for unit vectors, which
forces `W.evolve τ φ₀` to be a unit-modulus multiple of `φ₁`; orthogonality
`φ₀ ⊥ φ₁` then kills the overlap with `φ₀`.  No spectral-measure machinery is
needed — `evolve` unitarity plus the `Lp` equality case suffice, and the proof
is axiom-clean.  (In the counterexample this reads: `⟨φ₀, evolve(2π) φ₀⟩ = 0`,
which is precisely the vanishing of the characteristic function.) -/
theorem wavePacketTransfer_imp_returnAmplitude_zero
    (W : Graphon Ω μ)
    (phi0 phi1 : Lp ℂ 2 μ) (hphi : inner ℂ phi0 phi1 = (0 : ℂ))
    (τ : ℝ) (hwp : W.IsWavePacketTransfer phi0 phi1 τ) :
    (inner ℂ phi0 (W.evolve τ phi0) : ℂ) = 0 := by
  obtain ⟨hphi0, hphi1, hpst⟩ := hwp
  -- `W.evolve τ` is norm-preserving (unitary), so `‖evolve τ φ₀‖ = 1`.
  have hnorm_evolve : ‖W.evolve τ phi0‖ = 1 := by
    have hinner : (inner ℂ (W.evolve τ phi0) (W.evolve τ phi0) : ℂ)
        = (inner ℂ phi0 phi0 : ℂ) := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
      have hu := congrFun (congrArg
        (fun (T : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) => (T : Lp ℂ 2 μ → Lp ℂ 2 μ))
        (W.evolve_isUnitary τ)) phi0
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.id_apply] at hu
      rw [hu]
    have h2 : ((‖W.evolve τ phi0‖ : ℂ)) ^ 2 = ((‖phi0‖ : ℂ)) ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at hinner
      exact hinner
    have h3 : ‖W.evolve τ phi0‖ ^ 2 = ‖phi0‖ ^ 2 := by exact_mod_cast h2
    rw [hphi0] at h3
    nlinarith [norm_nonneg (W.evolve τ phi0), h3]
  -- Cauchy–Schwarz equality case: `evolve τ φ₀ = r • φ₁` for some scalar `r`.
  have hphi1_ne : phi1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hphi1; exact zero_ne_one hphi1
  have hev_ne : W.evolve τ phi0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm_evolve; exact zero_ne_one hnorm_evolve
  have heq : ‖(inner ℂ phi1 (W.evolve τ phi0) : ℂ)‖ = ‖phi1‖ * ‖W.evolve τ phi0‖ := by
    rw [hpst, hphi1, hnorm_evolve, mul_one]
  obtain ⟨r, _hr_ne, hr⟩ := (norm_inner_eq_norm_iff hphi1_ne hev_ne).1 heq
  -- `⟨φ₀, evolve τ φ₀⟩ = ⟨φ₀, r • φ₁⟩ = r · ⟨φ₀, φ₁⟩ = r · 0 = 0`.
  rw [hr, inner_smul_right, hphi, mul_zero]

/-- **Constant-graphon quotient entry (atomless case).**  For a constant
graphon `W ≡ c` over an atomless finite measure and *any* equitable partition
`P`, the per-vertex cell-to-cell flux is `Q i j = c · μ(C_j)`.

This is the genuine analytic step previously flagged as the open `op`/`quotient`
slice integral.  It is `constant_op_slice` localised to the cell `C_j`: the
slice integrand `[cells z = j] · W.kernel x z` equals `[cells z = j] · c` for
a.e. `z` (by atomlessness + `IsConstant`), and the integral of the cell-`j`
indicator times `c` is `c · μ(C_j)`.  Existence of a good representative
`x ∈ C_i` uses that `C_i` has positive mass, so it meets the co-null good set. -/
theorem constant_quotient_apply [NoAtoms μ] (W : Graphon Ω μ) (c : ℂ)
    (hW : W.IsConstant c) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) :
    P.quotient i j = c * (μ (P.cell j)).toReal := by
  classical
  -- Fubini: per-row a.e. constancy.
  have hrow : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, x ≠ y → W.kernel x y = c :=
    Measure.ae_ae_of_ae_prod hW
  -- The "good x" set: those for which the slice integral over `C_j` is `c·μ(C_j)`.
  have hgood : ∀ᵐ x ∂μ,
      (∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ) = c * (μ (P.cell j)).toReal := by
    filter_upwards [hrow] with x hx
    have hne : ∀ᵐ y ∂μ, y ≠ x := by
      rw [ae_iff]; simpa only [not_not] using measure_singleton x
    -- the slice integrand is `[cells z = j] · c` for a.e. `z`.
    have hae : (fun z => (if P.cells z = j then W.kernel x z else 0))
        =ᵐ[μ] fun z => (if P.cells z = j then c else 0) := by
      filter_upwards [hx, hne] with z hzc hzne
      by_cases hzj : P.cells z = j
      · rw [if_pos hzj, if_pos hzj, hzc (Ne.symm hzne)]
      · rw [if_neg hzj, if_neg hzj]
    rw [integral_congr_ae hae]
    -- `∫ z, [cells z = j] • c = (∫ z, [cells z = j]) • c = c · μ(C_j)`.
    have hind : (fun z => (if P.cells z = j then c else 0))
        = fun z => (P.cell j).indicator (fun _ => c) z := by
      funext z; unfold GraphonEquitablePartition.cell
      by_cases hzj : P.cells z = j
      · rw [if_pos hzj, Set.indicator_of_mem (show z ∈ P.cells ⁻¹' {j} from hzj)]
      · rw [if_neg hzj, Set.indicator_of_notMem (show z ∉ P.cells ⁻¹' {j} from hzj)]
    rw [hind, MeasureTheory.integral_indicator_const _ (P.measurableSet_cell j),
      Complex.real_smul]
    show ((μ.real (P.cell j) : ℝ) : ℂ) * c = c * ((μ (P.cell j)).toReal : ℂ)
    rw [show (μ.real (P.cell j) : ℝ) = (μ (P.cell j)).toReal from rfl]; ring
  -- A good representative `x₀ ∈ C_i` exists (good set is co-null, `C_i` has mass).
  obtain ⟨x₀, hx₀good, hx₀mem⟩ : ∃ x₀, (∫ z, (if P.cells z = j then W.kernel x₀ z else 0) ∂μ)
      = c * (μ (P.cell j)).toReal ∧ x₀ ∈ P.cell i := by
    by_contra hcon
    push_neg at hcon
    -- then `C_i ⊆ {x | slice ≠ c·μ(C_j)}`, contradicting `C_i` positive and the good set co-null.
    have hsub : P.cell i ⊆ {x | ¬ (∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ)
        = c * (μ (P.cell j)).toReal} := fun x hx hslice => hcon x hslice hx
    have hnull : μ {x | ¬ (∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ)
        = c * (μ (P.cell j)).toReal} = 0 := hgood
    have : μ (P.cell i) = 0 := measure_mono_null hsub hnull
    exact (ne_of_gt (P.cell_pos i)) this
  rw [P.quotient_apply_of_mem i j hx₀mem, hx₀good]

/-- **Constant graphon: the symmetric quotient is the rank-one outer product**
`symmQuotient i j = c · √μ(C_i) · √μ(C_j)`.

This is the genuine algebraic core of the constant-graphon spectral picture,
now fully reachable from the proven slice integral `constant_quotient_apply`
(`Q i j = c · μ(C_j)`) plus the definition `symmQuotient i j =
√μ_i · Q i j / √μ_j`: the `μ_j / √μ_j = √μ_j` cancellation (cells have positive
mass, `cellMass_pos`) leaves the **rank-one** outer product `c · √μ_i · √μ_j`.
Equivalently `symmQuotient = (c · μ(Ω)) · |ψ⟩⟨ψ|` with `ψ_i = √(μ_i / μ(Ω))`. -/
theorem constant_symmQuotient_eq [NoAtoms μ] (W : Graphon Ω μ) (c : ℂ)
    (hW : W.IsConstant c) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) :
    P.symmQuotient i j
      = c * (Real.sqrt (P.cellMass i) : ℂ) * (Real.sqrt (P.cellMass j) : ℂ) := by
  -- `symmQuotient i j = √μ_i · Q i j / √μ_j` with `Q i j = c · μ(C_j) = c · μ_j`.
  unfold GraphonEquitablePartition.symmQuotient
  rw [constant_quotient_apply W c hW P i j]
  -- `μ_j = (μ (P.cell j)).toReal = cellMass j`, and `√μ_j ≠ 0`.
  have hcellMass_j : (μ (P.cell j)).toReal = P.cellMass j := rfl
  have hsj : (Real.sqrt (P.cellMass j) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (P.cellMass_pos j))
  -- `μ_j = √μ_j · √μ_j`, so `μ_j / √μ_j = √μ_j`.
  rw [hcellMass_j]
  have hsq : (P.cellMass j : ℂ) = (Real.sqrt (P.cellMass j) : ℂ) * (Real.sqrt (P.cellMass j) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (P.cellMass_pos j))]
  rw [hsq]
  field_simp

/-! ### Rank-one matrix-exponential machinery for the constant graphon

The constant-graphon symmetric quotient is `c · (v vᵀ)` with `v_i = √μ(C_i)` —
a scalar multiple of a **rank-one idempotent** `E_{ij} = √μ_i √μ_j / s`
(`s := Σ_k μ(C_k)`).  We prove the closed-form matrix exponential of a scalar
multiple of any idempotent, then read off the off-diagonal modulus to get the
non-degenerate triviality theorem below. -/

/-- **Exponential of a scalar multiple of an idempotent matrix.**  If `E` is
idempotent (`E * E = E`) then `exp(z • E) = 1 + (eᶻ − 1) • E`.  This is the
honest analytic core of the rank-one constant-graphon spectrum: the exponential
series telescopes because `(z • E)ⁿ = zⁿ • E` for `n ≥ 1`.  Proved entrywise in
the native (entrywise-topology) matrix exponential via `exp_eq_tsum_rat`. -/
theorem exp_smul_idempotent (E : Matrix I I ℂ) (hE : E * E = E) (z : ℂ) :
    NormedSpace.exp (z • E) = 1 + (Complex.exp z - 1) • E := by
  classical
  have hpow : ∀ n : ℕ, (z • E) ^ (n + 1) = z ^ (n + 1) • E := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one, pow_one]
    | succ m ih => rw [pow_succ, ih, smul_mul_smul_comm, hE, ← pow_succ]
  have hexp : NormedSpace.exp (z • E) = ∑' n : ℕ, ((Nat.factorial n : ℚ)⁻¹) • (z • E) ^ n := by
    rw [NormedSpace.exp_eq_tsum_rat]
  have hsumScalar : Summable (fun n => ((Nat.factorial n : ℚ)⁻¹) • z ^ n : ℕ → ℂ) :=
    NormedSpace.expSeries_summable' (𝕂 := ℚ) z
  have hsumG : Summable (fun n => (((Nat.factorial n : ℚ)⁻¹) • z ^ n) • E) :=
    hsumScalar.smul_const E
  have hsumCorr : Summable (fun n : ℕ => if n = 0 then (1 - E : Matrix I I ℂ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    rw [if_neg (by simpa using hn)]
  have hfeq : (fun n => ((Nat.factorial n : ℚ)⁻¹) • (z • E) ^ n)
      = fun n => (((Nat.factorial n : ℚ)⁻¹) • z ^ n) • E
          + (if n = 0 then (1 - E : Matrix I I ℂ) else 0) := by
    funext n
    cases n with
    | zero =>
      rw [if_pos rfl, pow_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
        one_smul, one_smul, one_smul]
      abel
    | succ m =>
      rw [hpow m, if_neg (Nat.succ_ne_zero m), add_zero, smul_assoc]
  rw [hexp, hfeq, hsumG.tsum_add hsumCorr]
  rw [Summable.tsum_smul_const hsumScalar E]
  rw [(hasSum_ite_eq 0 (1 - E)).tsum_eq]
  have hscalarval : (∑' n : ℕ, ((Nat.factorial n : ℚ)⁻¹) • z ^ n : ℂ) = Complex.exp z := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_rat]
  rw [hscalarval, sub_smul, one_smul]
  abel

/-- `√μ_k · √μ_k = μ_k` (as a complex scalar); cells have positive mass. -/
theorem sqrt_cellMass_mul_self (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (k : I) :
    (Real.sqrt (P.cellMass k) : ℂ) * (Real.sqrt (P.cellMass k) : ℂ) = (P.cellMass k : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (P.cellMass_pos k))]

/-- The **rank-one idempotent** `E_{ij} = √μ(C_i) · √μ(C_j) / (Σ_k μ(C_k))`
underlying the constant-graphon symmetric quotient.  Equals `|ψ⟩⟨ψ|` with
`ψ_i = √(μ_i / s)` a unit vector. -/
noncomputable def constRankOne (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    Matrix I I ℂ :=
  fun i j => (Real.sqrt (P.cellMass i) : ℂ) * (Real.sqrt (P.cellMass j) : ℂ)
    / ((∑ k : I, P.cellMass k : ℝ) : ℂ)

/-- `constRankOne` is genuinely idempotent: `E * E = E` (because `ψ` is a unit
vector, `Σ_k μ_k / s = 1`). -/
theorem constRankOne_idem [Nonempty I] (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    constRankOne P * constRankOne P = constRankOne P := by
  classical
  obtain ⟨k0⟩ := (inferInstance : Nonempty I)
  have hs_ne : ((∑ k : I, P.cellMass k : ℝ) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Finset.sum_pos (fun k _ => P.cellMass_pos k) ⟨k0, Finset.mem_univ k0⟩)
  ext a b
  rw [Matrix.mul_apply]
  show (∑ m : I, ((Real.sqrt (P.cellMass a) : ℂ) * (Real.sqrt (P.cellMass m) : ℂ)
        / ((∑ k : I, P.cellMass k : ℝ) : ℂ))
      * ((Real.sqrt (P.cellMass m) : ℂ) * (Real.sqrt (P.cellMass b) : ℂ)
        / ((∑ k : I, P.cellMass k : ℝ) : ℂ)))
    = (Real.sqrt (P.cellMass a) : ℂ) * (Real.sqrt (P.cellMass b) : ℂ)
        / ((∑ k : I, P.cellMass k : ℝ) : ℂ)
  have hstep : ∀ m : I, ((Real.sqrt (P.cellMass a) : ℂ) * (Real.sqrt (P.cellMass m) : ℂ)
        / ((∑ k : I, P.cellMass k : ℝ) : ℂ))
      * ((Real.sqrt (P.cellMass m) : ℂ) * (Real.sqrt (P.cellMass b) : ℂ)
        / ((∑ k : I, P.cellMass k : ℝ) : ℂ))
      = ((Real.sqrt (P.cellMass a) : ℂ) * (Real.sqrt (P.cellMass b) : ℂ)
          / ((∑ k : I, P.cellMass k : ℝ) : ℂ) / ((∑ k : I, P.cellMass k : ℝ) : ℂ))
        * (P.cellMass m : ℂ) := by
    intro m
    rw [← sqrt_cellMass_mul_self P m]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hstep m), ← Finset.mul_sum]
  have hsum : (∑ m : I, (P.cellMass m : ℂ)) = ((∑ k : I, P.cellMass k : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
  rw [hsum, div_mul_cancel₀ _ hs_ne]

/-- For a constant graphon, the symmetric quotient is the **rank-one outer
product** `symmQuotient = (c · s) • constRankOne` (`s = Σ_k μ(C_k)`). -/
theorem constant_symmQuotient_eq_smul_rankOne [NoAtoms μ] (W : Graphon Ω μ) (c : ℂ)
    (hW : W.IsConstant c) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    P.symmQuotient = (c * ((∑ k : I, P.cellMass k : ℝ) : ℂ)) • constRankOne P := by
  classical
  ext a b
  rw [constant_symmQuotient_eq W c hW P a b]
  show (c * (Real.sqrt (P.cellMass a) : ℂ) * (Real.sqrt (P.cellMass b) : ℂ))
    = (c * ((∑ k : I, P.cellMass k : ℝ) : ℂ))
      * ((Real.sqrt (P.cellMass a) : ℂ) * (Real.sqrt (P.cellMass b) : ℂ)
        / ((∑ k : I, P.cellMass k : ℝ) : ℂ))
  by_cases hI : Nonempty I
  · obtain ⟨k0⟩ := hI
    have hs_ne : ((∑ k : I, P.cellMass k : ℝ) : ℂ) ≠ 0 := by
      simp only [Ne, Complex.ofReal_eq_zero]
      exact ne_of_gt (Finset.sum_pos (fun k _ => P.cellMass_pos k) ⟨k0, Finset.mem_univ k0⟩)
    field_simp
  · exact absurd ⟨a⟩ hI

/-- For a constant graphon over a nonempty cell index, the constant `c` is
**real**: the symmetric quotient is Hermitian (`symmQuotient_isHermitian`), and
its diagonal entry `c · μ_k` must then equal its own conjugate, forcing
`conj c = c`. -/
theorem constant_isReal [NoAtoms μ] (W : Graphon Ω μ) (c : ℂ)
    (hW : W.IsConstant c) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (k : I) :
    (starRingEnd ℂ) c = c := by
  have hherm := P.symmQuotient_isHermitian
  have hkk : star (P.symmQuotient k k) = P.symmQuotient k k := by
    have := congrFun (congrFun hherm.eq k) k
    rw [Matrix.conjTranspose_apply] at this
    exact this
  rw [constant_symmQuotient_eq W c hW P k k] at hkk
  have hmk : (Real.sqrt (P.cellMass k) : ℂ) * (Real.sqrt (P.cellMass k) : ℂ) = (P.cellMass k : ℂ) :=
    sqrt_cellMass_mul_self P k
  rw [mul_assoc, hmk] at hkk
  rw [star_mul', Complex.star_def, Complex.conj_ofReal] at hkk
  have hμne : (P.cellMass k : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (P.cellMass_pos k)
  exact mul_right_cancel₀ hμne hkk

/-- **Constant graphon: cell-uniform PST between distinct cells forces `i = j`,
under a non-degeneracy hypothesis.**

The bare claim "`PST ⟹ i = j`" is **FALSE** for the constant graphon: `K_2`
(two equal-mass cells, phase `π`) exhibits genuine PST between its two distinct
cells.  The off-diagonal modulus of `exp(-iτ · symmQuotient)` is
`|e^{-iτ c s} − 1| · √μ_j √μ_i / s ≤ 2 √μ_i √μ_j / s` (`s = Σ_k μ(C_k)`), which
attains the bound `1` exactly at the degenerate equal-mass `K_2` configuration.

The genuine theorem adds the **non-degeneracy hypothesis** `hnd : 2 √μ_i √μ_j < s`
(equivalently `√(μ_i μ_j) < s/2`, ruling out the equal-mass-`K_2` pair).  Then the
off-diagonal modulus is *strictly* below `1`, so cell-uniform PST between distinct
cells is impossible, forcing `i = j`.

Proof: `symmQuotient = (c·s) • E` for the rank-one idempotent `E`
(`constant_symmQuotient_eq_smul_rankOne`); `c` is real
(`constant_isReal`) so the propagator phase `e^{-iτ c s}` has modulus one;
`exp_smul_idempotent` gives `exp(-iτ·symmQuotient)_{ji} = (e^{-iτcs} − 1)·E_{ji}`
for `i ≠ j`; its modulus is `≤ 2·√μ_i√μ_j/s < 1`, contradicting the PST
unit-modulus condition. -/
theorem constant_graphon_pst_trivial [NoAtoms μ]
    (W : Graphon Ω μ) (c : ℂ) (hW : W.IsConstant c)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i j : I) (τ : ℝ) (hτ : τ ≠ 0)
    (hnd : 2 * Real.sqrt (P.cellMass i) * Real.sqrt (P.cellMass j) < ∑ k : I, P.cellMass k) :
    IsCellUniformPST W P i j τ → i = j := by
  classical
  intro hpst
  by_contra hij
  haveI : Nonempty I := ⟨i⟩
  set s : ℝ := ∑ k : I, P.cellMass k with hs_def
  have hs_pos : 0 < s := Finset.sum_pos (fun k _ => P.cellMass_pos k) ⟨i, Finset.mem_univ i⟩
  -- cell-uniform PST reduces to finite PST on the Hermitian symmetric quotient
  have hfin : IsPST_finite P.symmQuotient i j τ :=
    (Graphon.cellUniformPST_iff_quotientPST P i j τ).mp hpst
  rw [Graphon.IsPST_finite] at hfin
  -- symmQuotient = (c·s) • E  ⟹  the exponent is z • E
  have hQ : P.symmQuotient = (c * (s : ℂ)) • constRankOne P :=
    constant_symmQuotient_eq_smul_rankOne W c hW P
  set z : ℂ := -(Complex.I * (τ : ℂ)) * (c * (s : ℂ)) with hz_def
  have hexp_smul : -(Complex.I * (τ : ℂ)) • P.symmQuotient = z • constRankOne P := by
    rw [hQ, smul_smul]
  rw [hexp_smul, exp_smul_idempotent (constRankOne P) (constRankOne_idem P) z] at hfin
  -- (j,i) entry: distinct cells, so the identity term vanishes
  have hentry : (1 + (Complex.exp z - 1) • constRankOne P) j i
      = (Complex.exp z - 1) * constRankOne P j i := by
    rw [Matrix.add_apply, Matrix.one_apply_ne (Ne.symm hij), Matrix.smul_apply, smul_eq_mul,
      zero_add]
  rw [hentry] at hfin
  -- read off ‖entry‖ = ‖eᶻ − 1‖ · (√μ_j √μ_i / s)
  have hEji_nonneg : (0 : ℝ) ≤ Real.sqrt (P.cellMass j) * Real.sqrt (P.cellMass i) / s :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (le_of_lt hs_pos)
  have hEji : constRankOne P j i
      = ((Real.sqrt (P.cellMass j) * Real.sqrt (P.cellMass i) / s : ℝ) : ℂ) := by
    simp only [constRankOne, hs_def]
    push_cast
    ring
  rw [hEji, norm_mul, Complex.norm_real, Real.norm_of_nonneg hEji_nonneg] at hfin
  -- ‖eᶻ − 1‖ ≤ 2, because `c` real ⟹ `z` purely imaginary ⟹ ‖eᶻ‖ = 1
  have hc_real : (starRingEnd ℂ) c = c := constant_isReal W c hW P i
  have hz_re : z.re = 0 := by
    rw [hz_def]
    have hcim : c.im = 0 := Complex.conj_eq_iff_im.mp hc_real
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hcim]
    ring
  have hnorm_exp_z : ‖Complex.exp z‖ = 1 := by
    rw [Complex.norm_exp, hz_re, Real.exp_zero]
  have hle2 : ‖Complex.exp z - 1‖ ≤ 2 := by
    calc ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm_exp_z, norm_one]; norm_num
  -- 1 = ‖eᶻ−1‖ · (√μ_j√μ_i/s) ≤ 2·√μ_i√μ_j/s < 1 — contradiction
  have hbound : (1 : ℝ) ≤ 2 * (Real.sqrt (P.cellMass j) * Real.sqrt (P.cellMass i) / s) := by
    rw [← hfin]
    exact mul_le_mul_of_nonneg_right hle2 hEji_nonneg
  have hlt : 2 * (Real.sqrt (P.cellMass j) * Real.sqrt (P.cellMass i) / s) < 1 := by
    rw [mul_div_assoc'] at hbound ⊢
    rw [div_lt_one hs_pos]
    have hcomm : 2 * (Real.sqrt (P.cellMass j) * Real.sqrt (P.cellMass i))
        = 2 * Real.sqrt (P.cellMass i) * Real.sqrt (P.cellMass j) := by ring
    rw [hcomm]
    exact hnd
  linarith [hbound, hlt]

/-! ## 6½. Matrix-level forward Godsil extraction (PST ⟹ strong cospectrality)

The headline `cellUniformPST_implies_stronglyCospectral` reduces, via
`cellUniformPST_iff_quotientPST`, to **finite** PST on the Hermitian quotient
`P.symmQuotient`.  The Tower-1 spectral-projector spine
(`Graphplay.PST.isPST_imp_isStronglyCospectral`) proves the forward
"PST ⟹ strong cospectrality" extraction, but it is phrased over a
`WeightedGraph` — and `symmQuotient` has a (generally non-constant) **non-zero
diagonal** (the per-cell self-flux), so it is *not loopless* and does not fit
the `WeightedGraph` interface.

We therefore replicate the (short) projector-algebra forward extraction here,
for an **arbitrary** Hermitian matrix `H : Matrix I I ℂ`, keyed off
`Matrix.IsHermitian`.  This is the exact analogue of the Tower-1 spine, built
on Mathlib's `IsHermitian.eigenvectorUnitary` / `spectral_theorem` and the
matrix exponential, and is axiom-clean.

Note the phase is `‖ε‖ = 1` (the **chiral** unit-circle phase), *not* `±1`:
`symmQuotient` is genuinely complex-Hermitian (its entries
`√μ_i · Q_{ij} / √μ_j` inherit the complex graphon kernel `Q`), so the
real-symmetric `±1` constraint is false in general.  This matches the finite
Tower-1 `IsStronglyCospectral` (`‖ε‖ = 1`) and the file's own Section-7
documentation. -/

namespace HermProj

variable {I : Type v} [Fintype I] [DecidableEq I]
variable {H : Matrix I I ℂ} (hH : H.IsHermitian)

/-- The eigenvector unitary of `H` (columns = orthonormal eigenvectors). -/
noncomputable def U (hH : H.IsHermitian) : Matrix I I ℂ :=
  (hH.eigenvectorUnitary : Matrix I I ℂ)

/-- `U Uᴴ = 1`. -/
theorem U_mul_conjTranspose : U hH * (U hH)ᴴ = (1 : Matrix I I ℂ) := by
  unfold U; rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.coe_mul_star_self hH.eigenvectorUnitary

/-- `Uᴴ U = 1`. -/
theorem conjTranspose_mul_U : (U hH)ᴴ * U hH = (1 : Matrix I I ℂ) := by
  unfold U; rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.coe_star_mul_self hH.eigenvectorUnitary

/-- `U` is a unit matrix. -/
theorem U_isUnit : IsUnit (U hH) :=
  isUnit_iff_exists.mpr ⟨(U hH)ᴴ, U_mul_conjTranspose hH, conjTranspose_mul_U hH⟩

/-- Column orthonormality of `U`: `(Uᴴ U)_{i,j} = δ`. -/
theorem U_col_orthonormal (i j : I) :
    ∑ x : I, star (U hH x i) * U hH x j = if i = j then 1 else 0 := by
  have h := conjTranspose_mul_U hH
  have hij := congrFun (congrFun h i) j
  rw [Matrix.mul_apply] at hij
  simp only [Matrix.conjTranspose_apply, Matrix.one_apply] at hij
  rw [← hij]

/-- The continuous-time evolution `exp(-(iτ)•H)`. -/
noncomputable def evolve (hH : H.IsHermitian) (τ : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H)

/-- **Spectral-evolution bridge.**  The `(u,v)` entry of `exp(-(iτ)•H)` is the
eigenbasis trigonometric sum. -/
theorem evolve_eq_U_sum (τ : ℝ) (u v : I) :
    evolve hH τ u v
      = ∑ k : I, U hH u k
          * Complex.exp (-(Complex.I * (τ : ℂ)) * (hH.eigenvalues k : ℂ))
          * star (U hH v k) := by
  classical
  set c : ℂ := -(Complex.I * (τ : ℂ)) with hc
  -- Spectral theorem: H = U * diag(λ) * Uᴴ.
  have hspec : H
      = (U hH) * (Matrix.diagonal (fun k => (hH.eigenvalues k : ℂ)))
          * (U hH)ᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [U, ← Matrix.star_eq_conjTranspose]
    convert h using 2
  have hdiagsmul : c • (Matrix.diagonal (fun k => (hH.eigenvalues k : ℂ)))
      = (Matrix.diagonal (fun k => c * (hH.eigenvalues k : ℂ))) := by
    rw [← Matrix.diagonal_smul]; rfl
  have hinv : (U hH)⁻¹ = (U hH)ᴴ := by
    apply Matrix.inv_eq_right_inv; exact U_mul_conjTranspose hH
  have hscale : c • H
      = (U hH) * (Matrix.diagonal (fun k => c * (hH.eigenvalues k : ℂ)))
          * (U hH)⁻¹ := by
    rw [hinv]; conv_lhs => rw [hspec]
    rw [← hdiagsmul, mul_smul_comm, smul_mul_assoc]
  have hexpdiag :
      NormedSpace.exp (Matrix.diagonal (fun k => c * (hH.eigenvalues k : ℂ)))
        = Matrix.diagonal (fun k => Complex.exp (c * (hH.eigenvalues k : ℂ))) := by
    rw [Matrix.exp_diagonal]; congr 1; funext k
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  have hevolve : evolve hH τ
      = (U hH)
          * Matrix.diagonal (fun k => Complex.exp (c * (hH.eigenvalues k : ℂ)))
          * (U hH)⁻¹ := by
    unfold evolve
    rw [← hc, hscale, Matrix.exp_conj _ _ (U_isUnit hH), hexpdiag]
  rw [hevolve, hinv, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply, mul_assoc]
  · intro l _ hl; rw [Matrix.diagonal_apply_ne _ hl, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The **spectral projector** `E_λ` onto the `λ`-eigenspace of `H`, as a
matrix; its `(u,v)` entry is `∑_{k : λ_k = λ} U_{uk} · conj U_{vk}`. -/
noncomputable def proj (hH : H.IsHermitian) (lam : ℝ) : Matrix I I ℂ :=
  fun u v => ∑ k : I, if hH.eigenvalues k = lam then U hH u k * star (U hH v k) else 0

/-- The diagonal projector entry (a sum of squared norms), as a real number. -/
noncomputable def projDiag (hH : H.IsHermitian) (lam : ℝ) (u : I) : ℝ :=
  ∑ k : I, if hH.eigenvalues k = lam then ‖U hH u k‖ ^ 2 else 0

/-- The diagonal entry of the projector matrix is the (real) diagonal entry. -/
theorem proj_diag (lam : ℝ) (u : I) :
    proj hH lam u u = (projDiag hH lam u : ℂ) := by
  rw [proj, projDiag, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : hH.eigenvalues k = lam
  · simp only [h, if_true]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · simp only [h, if_false, Complex.ofReal_zero]

/-- The diagonal projector entry is nonnegative. -/
theorem projDiag_nonneg (lam : ℝ) (u : I) : 0 ≤ projDiag hH lam u := by
  rw [projDiag]; apply Finset.sum_nonneg; intro k _
  by_cases h : hH.eigenvalues k = lam
  · simp only [h, if_true]; positivity
  · simp only [h, if_false, le_refl]

/-- The projector matrix is self-adjoint: `(E_λ)_{v,u} = conj (E_λ)_{u,v}`. -/
theorem proj_conjTranspose_apply (lam : ℝ) (a b : I) :
    proj hH lam b a = star (proj hH lam a b) := by
  unfold proj; rw [star_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : hH.eigenvalues k = lam
  · simp only [h, if_true]; rw [star_mul', star_star, mul_comm]
  · simp only [h, if_false, star_zero]

/-- The `(u,w)` entry of `E_λ E_μ` collapses to the diagonal-supported sum. -/
theorem proj_mul_entry (lam mu : ℝ) (u w : I) :
    (proj hH lam * proj hH mu) u w
      = ∑ k, (if hH.eigenvalues k = lam ∧ hH.eigenvalues k = mu
                then U hH u k * star (U hH w k) else 0) := by
  rw [Matrix.mul_apply]
  show (∑ x : I,
      (∑ k, if hH.eigenvalues k = lam then U hH u k * star (U hH x k) else 0) *
      (∑ l, if hH.eigenvalues l = mu then U hH x l * star (U hH w l) else 0)) = _
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : hH.eigenvalues k = lam
  · have step : (∑ l, ∑ x,
        (if hH.eigenvalues k = lam then U hH u k * star (U hH x k) else 0) *
        (if hH.eigenvalues l = mu then U hH x l * star (U hH w l) else 0))
        = ∑ l, (if hH.eigenvalues l = mu then U hH u k * star (U hH w l) else 0) *
              (if k = l then (1:ℂ) else 0) := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [hk, if_true]
      by_cases hl : hH.eigenvalues l = mu
      · simp only [hl, if_true]
        rw [← U_col_orthonormal hH k l, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_); ring
      · simp only [hl, if_false]
        rw [zero_mul, Finset.sum_eq_zero]; intro x _; ring
    rw [step, Finset.sum_eq_single k]
    · simp only [if_true, mul_one]
      by_cases hl : hH.eigenvalues k = mu
      · rw [if_pos hl, if_pos (And.intro hk hl)]
      · rw [if_neg hl, if_neg (fun hc => hl hc.2)]
    · intro l _ hkl; rw [if_neg (Ne.symm hkl), mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  · simp only [hk, false_and, if_false, zero_mul, Finset.sum_const_zero]

/-- **Idempotency** of the spectral projector: `E_λ E_λ = E_λ`. -/
theorem proj_idem (lam : ℝ) : proj hH lam * proj hH lam = proj hH lam := by
  ext u w; rw [proj_mul_entry]; unfold proj
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : hH.eigenvalues k = lam
  · simp only [h, and_self, if_true]
  · simp only [h, false_and, if_false]

/-- **Orthogonality** of distinct spectral projectors: `E_λ E_μ = 0` for `λ ≠ μ`. -/
theorem proj_orthogonal (lam mu : ℝ) (hne : lam ≠ mu) :
    proj hH lam * proj hH mu = 0 := by
  ext u w; rw [proj_mul_entry]
  rw [Matrix.zero_apply, Finset.sum_eq_zero]
  intro k _
  by_cases h : hH.eigenvalues k = lam
  · rw [if_neg]; rintro ⟨h1, h2⟩; exact hne (h1.symm.trans h2)
  · rw [if_neg]; rintro ⟨h1, _⟩; exact h h1

/-- The `(u,v)` entry of the evolution expands as a sum over eigenvalues. -/
theorem evolve_eq_projSum (τ : ℝ) (u v : I) :
    evolve hH τ u v
      = ∑ lam ∈ (Finset.univ.image hH.eigenvalues),
          Complex.exp (-(Complex.I * (τ : ℂ)) * (lam : ℂ)) * proj hH lam u v := by
  rw [evolve_eq_U_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := hH.eigenvalues)
        (t := Finset.univ.image hH.eigenvalues)
        (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ k))]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [proj, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : hH.eigenvalues k = lam
  · simp only [h, if_true]; ring
  · simp only [h, if_false, mul_zero]

/-- The evolution expands as `U(τ) = ∑_λ e^{-iτλ} E_λ`. -/
theorem evolve_eq_sum_proj (τ : ℝ) :
    evolve hH τ
      = ∑ lam ∈ (Finset.univ.image hH.eigenvalues),
          Complex.exp (-(Complex.I * (τ : ℂ)) * (lam : ℂ)) • proj hH lam := by
  ext u v
  rw [evolve_eq_projSum, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul]

/-- `E_μ U(τ) = e^{-iτμ} E_μ`. -/
theorem proj_mul_evolve (τ : ℝ) (mu : ℝ)
    (hmu : mu ∈ Set.range hH.eigenvalues) :
    proj hH mu * evolve hH τ
      = Complex.exp (-(Complex.I * (τ : ℂ)) * (mu : ℂ)) • proj hH mu := by
  rw [evolve_eq_sum_proj, Finset.mul_sum, Finset.sum_eq_single mu]
  · rw [Matrix.mul_smul, proj_idem]
  · intro lam _ hlam
    rw [Matrix.mul_smul, proj_orthogonal hH mu lam (Ne.symm hlam), smul_zero]
  · intro hmem
    exfalso; apply hmem
    obtain ⟨k, hk⟩ := hmu
    rw [Finset.mem_image]; exact ⟨k, Finset.mem_univ k, hk⟩

/-- The conjugate-transpose of the propagator is the reverse-time propagator:
`(U(τ))ᴴ = U(-τ) = exp(-(i(-τ))•H)`. -/
theorem evolve_conjTranspose (τ : ℝ) :
    (evolve hH τ)ᴴ = evolve hH (-τ) := by
  unfold evolve
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, hH.eq]
  congr 1
  simp only [star_neg, star_mul', Complex.star_def, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  push_cast
  ring

/-- `evolve` is unitary: `U(τ) (U(τ))ᴴ = 1`. -/
theorem evolve_mul_conjTranspose (τ : ℝ) :
    evolve hH τ * (evolve hH τ)ᴴ = (1 : Matrix I I ℂ) := by
  rw [evolve_conjTranspose]
  unfold evolve
  rw [← Matrix.exp_add_of_commute]
  · rw [show -(Complex.I * (τ : ℂ)) • H + -(Complex.I * ((-τ : ℝ) : ℂ)) • H = 0 by
        rw [← add_smul]; push_cast; rw [show -(Complex.I * (τ:ℂ)) + -(Complex.I * (-(τ:ℂ))) = 0 by ring, zero_smul]]
    exact NormedSpace.exp_zero
  · exact ((Commute.refl H).smul_left _).smul_right _

/-- The `u`-row of `U(τ)` has unit `ℓ²`-norm. -/
theorem evolve_row_normSq (τ : ℝ) (u : I) :
    ∑ w : I, ‖evolve hH τ u w‖ ^ 2 = 1 := by
  have h := evolve_mul_conjTranspose hH τ
  have huu : (evolve hH τ * (evolve hH τ)ᴴ) u u = (1 : Matrix I I ℂ) u u := by rw [h]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at huu
  have key : ∑ w : I, evolve hH τ u w * (evolve hH τ)ᴴ w u
      = ((∑ w : I, ‖evolve hH τ u w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [key] at huu
  exact_mod_cast huu

/-- **PST forces the rest of the row to vanish.** -/
theorem evolve_eq_zero_of_pst (τ : ℝ) (u v : I)
    (hpst : ‖evolve hH τ u v‖ = 1) (w : I) (hw : w ≠ v) :
    evolve hH τ u w = 0 := by
  have hsum := evolve_row_normSq hH τ u
  have hsplit : ‖evolve hH τ u v‖ ^ 2
      + ∑ w ∈ Finset.univ.erase v, ‖evolve hH τ u w‖ ^ 2 = 1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)] at hsum; linarith [hsum]
  rw [hpst] at hsplit; simp only [one_pow] at hsplit
  have hrest : ∑ w ∈ Finset.univ.erase v, ‖evolve hH τ u w‖ ^ 2 = 0 := by linarith
  have hzero : ‖evolve hH τ u w‖ ^ 2 = 0 := by
    have hmem : w ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg _)).mp hrest w hmem
  have : ‖evolve hH τ u w‖ = 0 := by nlinarith [norm_nonneg (evolve hH τ u w)]
  exact norm_eq_zero.mp this

/-- `U(τ)ᴴ` entry is the conjugate of the transposed entry: needed for the
column relation. -/
theorem evolve_neg_eq_star (τ : ℝ) (b u : I) :
    evolve hH (-τ) b u = star (evolve hH τ u b) := by
  have := congrFun (congrFun (evolve_conjTranspose hH τ) b) u
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]

/-- **Column relation from PST.**  With `γ := U(τ) u v` (modulus 1), for every
eigenvalue `μ` and every `a`:
`e^{iτμ} (E_μ)_{a,u} = conj γ · (E_μ)_{a,v}`. -/
theorem proj_col_relation (τ : ℝ) (u v : I)
    (hpst : ‖evolve hH τ u v‖ = 1) (mu : ℝ)
    (hmu : mu ∈ Set.range hH.eigenvalues) (a : I) :
    Complex.exp (Complex.I * (τ : ℂ) * (mu : ℂ)) * proj hH mu a u
      = star (evolve hH τ u v) * proj hH mu a v := by
  have hmul := proj_mul_evolve hH (-τ) mu hmu
  have hau := congrFun (congrFun hmul a) u
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at hau
  have hexp : Complex.exp (-(Complex.I * ((-τ : ℝ) : ℂ)) * (mu : ℂ))
      = Complex.exp (Complex.I * (τ : ℂ) * (mu : ℂ)) := by
    congr 1; push_cast; ring
  rw [hexp] at hau
  rw [← hau, Finset.sum_eq_single v]
  · rw [evolve_neg_eq_star hH τ v u]; ring
  · intro b _ hbv
    rw [evolve_neg_eq_star hH τ b u, evolve_eq_zero_of_pst hH τ u v hpst b hbv,
      star_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ v) h

/-- **PST implies cospectrality** (diagonal equality). -/
theorem pst_imp_cospectral (τ : ℝ) (u v : I)
    (hpst : ‖evolve hH τ u v‖ = 1) (mu : ℝ)
    (hmu : mu ∈ Set.range hH.eigenvalues) :
    projDiag hH mu u = projDiag hH mu v := by
  set γ := evolve hH τ u v with hγ
  have hγnorm : ‖γ‖ = 1 := hpst
  have hu := proj_col_relation hH τ u v hpst mu hmu u
  have hv := proj_col_relation hH τ u v hpst mu hmu v
  rw [proj_diag] at hu
  rw [proj_diag] at hv
  rw [proj_conjTranspose_apply] at hv
  set E := proj hH mu u v with hE
  set p := Complex.exp (Complex.I * (τ : ℂ) * (mu : ℂ)) with hp
  have hpnorm : ‖p‖ = 1 := by rw [hp, Complex.norm_exp]; simp
  have huc : γ * star E = star p * (projDiag hH mu u : ℂ) := by
    have h2 := congrArg star hu
    rw [star_mul', star_mul', star_star] at h2
    rw [show star ((projDiag hH mu u : ℝ) : ℂ) = ((projDiag hH mu u : ℝ) : ℂ)
        from Complex.conj_ofReal _] at h2
    linear_combination -h2
  have hpp : p * star p = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hpnorm]; norm_num
  have hγγ : γ * star γ = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hγnorm]; norm_num
  have key : (projDiag hH mu u : ℂ) = (projDiag hH mu v : ℂ) := by
    have lhs : p * (γ * star E) = (projDiag hH mu u : ℂ) := by
      rw [huc, ← mul_assoc]; rw [show p * star p = 1 from hpp, one_mul]
    have rhs : γ * (p * star E) = (projDiag hH mu v : ℂ) := by
      rw [hv, ← mul_assoc, hγγ, one_mul]
    rw [← lhs, ← rhs]; ring
  exact_mod_cast key

/-- **Strong cospectrality** of basis vectors `i, j` for a Hermitian matrix
`H`: for every eigenvalue `λ`, the cross projector entry `(E_λ)_{i,j}` is a
unit-modulus phase times the geometric mean of the diagonal entries.  This is
the chiral (`‖ε‖ = 1`) projector-parallelism condition. -/
def IsStronglyCospectral (hH : H.IsHermitian) (i j : I) : Prop :=
  ∀ lam : ℝ, lam ∈ Set.range hH.eigenvalues →
    ∃ ε : ℂ, ‖ε‖ = 1 ∧
      proj hH lam i j
        = ε * Complex.ofReal (Real.sqrt (projDiag hH lam i * projDiag hH lam j))

/-- **PST ⟹ strong cospectrality** for a bare Hermitian matrix.  This is the
matrix-level analogue of Godsil's necessary condition
(`Graphplay.PST.isPST_imp_isStronglyCospectral`), proven axiom-cleanly here so
it applies to `symmQuotient` (which is Hermitian but not loopless, hence not a
`WeightedGraph`). -/
theorem pst_imp_stronglyCospectral (τ : ℝ) (i j : I)
    (hpst : ‖evolve hH τ i j‖ = 1) :
    IsStronglyCospectral hH i j := by
  intro mu hmu
  set γ := evolve hH τ i j with hγ
  have hγnorm : ‖γ‖ = 1 := hpst
  set p := Complex.exp (Complex.I * (τ : ℂ) * (mu : ℂ)) with hp
  have hpnorm : ‖p‖ = 1 := by rw [hp, Complex.norm_exp]; simp
  have hcosp := pst_imp_cospectral hH τ i j hpst mu hmu
  have hu := proj_col_relation hH τ i j hpst mu hmu i
  rw [proj_diag] at hu
  set E := proj hH mu i j with hE
  have hγγ : γ * star γ = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hγnorm]; norm_num
  have hEval : E = γ * p * (projDiag hH mu i : ℂ) := by
    have : γ * (p * (projDiag hH mu i : ℂ)) = γ * (star γ * E) := by rw [hu]
    rw [← mul_assoc, ← mul_assoc, hγγ, one_mul] at this
    rw [← this]
  refine ⟨γ * p, ?_, ?_⟩
  · rw [norm_mul, hγnorm, hpnorm, one_mul]
  · rw [hEval]
    congr 1
    rw [← hcosp]
    norm_cast
    rw [Real.sqrt_mul_self (projDiag_nonneg hH mu i)]

end HermProj

/-! ## 7. Strong cospectrality on graphons (Tower-4 lift of L1)

In Tower 1 (`Graphplay/PST.lean`) we have the finite notion of **strong
cospectrality** between two vertices `u, v` of a finite weighted graph
`H`: the spectral projections of `H` onto each eigenspace either agree at
`u, v` or differ only by a sign.  This is the natural sufficient
condition for PST (Coutinho–Godsil 2016).

The graphon-level lift is between two *cells* `i, j` of an equitable
partition — equivalently, between the normalised cell indicators
`e_i, e_j ∈ L²(μ)`.  Because the cell-uniform subspace is
finite-dimensional and `W.op` restricts to a Hermitian matrix
`P.quotient` there, the natural definition is **strong cospectrality of
the standard basis vectors `E_i, E_j ∈ ℂ^I` for the matrix `P.quotient`**.

We state it via existence of a spectral decomposition of `P.quotient`. -/

/-- **Strong cospectrality on the quotient.**  For the finite Hermitian
symmetric-quotient matrix `P.symmQuotient` and two cells `i, j`, strong
cospectrality holds when, for every eigenvalue `λ`, the spectral projectors
`E_λ` of `P.symmQuotient` send the standard basis vectors `E_i, E_j` to
**parallel** vectors: the cross projector entry `(E_λ)_{i,j}` is a
unit-modulus phase times the geometric mean of the diagonal entries
`(E_λ)_{i,i}, (E_λ)_{j,j}`.

This is the chiral (`‖ε‖ = 1`) Tower-1 strong-cospectrality predicate
(`Graphplay.PST.IsStronglyCospectral`), specialised to the Hermitian quotient
via `HermProj.IsStronglyCospectral`.  We use the **chiral** unit-circle phase
rather than the real-symmetric `±1`: `P.symmQuotient` is genuinely
complex-Hermitian (its entries `√μ_i · Q_{ij} / √μ_j` inherit the complex
graphon kernel `Q`), so the `±1` constraint is false in general; `‖ε‖ = 1`
is what PST actually delivers and matches the finite Tower-1 definition.

We call this the **cell-strong-cospectrality** of cells `i, j`. -/
def IsCellStronglyCospectral
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) : Prop :=
  HermProj.IsStronglyCospectral P.symmQuotient_isHermitian i j

/-- **Graphon strong cospectrality** of cells `i, j` of an equitable
partition `P`.  Equivalent (by the headline lifting theorem) to strong
cospectrality of the standard basis vectors of the quotient matrix. -/
def IsGraphonStronglyCospectral
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) : Prop :=
  IsCellStronglyCospectral P i j

/-- **Tower-4 strong-cospectrality theorem.**  The graphon-level
strong-cospectrality of cells `i, j` for `(W, P)` agrees with finite
strong-cospectrality of `E_i, E_j` for the quotient matrix `P.quotient`.

(This is the equitable-partition lift, stated using the headline lifting
identification of `W.op|_{cellUniform}` with `P.quotient`.) -/
theorem isGraphonStronglyCospectral_iff_quotient
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) :
    IsGraphonStronglyCospectral P i j ↔ IsCellStronglyCospectral P i j := by
  rfl

/-- **Strong cospectrality is necessary for cell-uniform PST.**  If
cell-uniform PST holds between `i` and `j` at some time `τ`, then `i, j`
are graphon-strongly-cospectral.

This is the graphon lift of Coutinho–Godsil's necessary condition. -/
theorem cellUniformPST_implies_stronglyCospectral
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) (τ : ℝ)
    (h : IsCellUniformPST W P i j τ) :
    IsGraphonStronglyCospectral P i j := by
  -- Step 1: cell-uniform PST reduces to finite PST on the Hermitian quotient
  -- `P.symmQuotient`: `IsPST_finite P.symmQuotient i j τ`, i.e. the `(j,i)` entry
  -- of `exp(-(iτ)·symmQuotient)` has modulus 1.
  have hfin : IsPST_finite P.symmQuotient i j τ :=
    (Graphon.cellUniformPST_iff_quotientPST P i j τ).mp h
  -- This is exactly `‖HermProj.evolve symmQuotient_isHermitian τ j i‖ = 1`.
  have hpst : ‖HermProj.evolve P.symmQuotient_isHermitian τ j i‖ = 1 := hfin
  -- Step 2: apply the matrix-level forward Godsil extraction to get
  -- `HermProj.IsStronglyCospectral` of basis vectors `j, i`.
  have hsc_ji : HermProj.IsStronglyCospectral P.symmQuotient_isHermitian j i :=
    HermProj.pst_imp_stronglyCospectral P.symmQuotient_isHermitian τ j i hpst
  -- Step 3: strong cospectrality is symmetric, so we obtain it for `i, j`.
  rw [isGraphonStronglyCospectral_iff_quotient, IsCellStronglyCospectral]
  intro lam hlam
  obtain ⟨ε, hε, heq⟩ := hsc_ji lam hlam
  -- `(E_λ)_{i,j} = star ((E_λ)_{j,i})`; `star ε` is still a phase; the geometric
  -- mean is symmetric in `i, j`.
  refine ⟨star ε, by rw [norm_star, hε], ?_⟩
  have hconj := HermProj.proj_conjTranspose_apply P.symmQuotient_isHermitian lam j i
  -- `proj _ lam i j = star (proj _ lam j i) = star (ε * sqrt(d_j d_i))`.
  rw [hconj, heq, star_mul']
  congr 1
  rw [Complex.star_def, Complex.conj_ofReal, mul_comm (HermProj.projDiag _ lam j)]

/-! ## 8. Tower-4 closing remarks

This file closes the Tower-4 loop by clarifying:

* The **cell-uniform sector is always finite-dimensional**, hence has
  pure point spectrum.  Cell-uniform PST is therefore a finite-spectral
  statement (Section 4).
* The **continuous part of the spectrum is invisible** to cell-uniform
  PST.  This is what makes the Tower-1 → Tower-4 lift work despite the
  apparent infinite-dimensionality of `L²(μ)`.
* Honest infinite-dimensional PST is captured by **wave-packet
  transfer** (Section 5), which is the right setting for proving
  impossibility results about graphons with purely continuous spectrum
  (Section 6).
* The **Tower-4 strong cospectrality** definition reduces, by the
  headline lifting theorem, to finite-matrix strong cospectrality on
  the quotient (Section 7).

In other words: Tower-4 PST is "finite PST with extra L² hygiene"
because the cell-uniform subspace is finite-dimensional.  This is the
honest answer to "what happens to PST under continuous spectrum". -/

end Graphon

end Graphplay
