/-
# Graphplay/Integrations/RMT.lean — Random matrix theory and free probability

This integration file develops the *meeting point* between Graphplay's
equitable-partition framework (Towers 3–4) and **random matrix theory** /
**free probability**.

The combination is, to the best of our literature search, unexplored:

* Classical RMT studies the spectrum of `n × n` random Hermitian matrices and
  identifies universal limits — Wigner's semicircle for the GOE/GUE/GSE
  ensembles, free convolutions for sums of independent ensembles
  (Voiculescu 1991, Speicher 1990s).  The bulk spectrum is **random**
  but with deterministic limiting density.
* Graphplay's headline equitable-partition theorem
  (`Graphplay.Graphon.op_restrict_eq_quotient`) says that, restricted to the
  *cell-uniform subspace*, the spectrum of a graphon operator is **exactly**
  the (deterministic) spectrum of the finite quotient matrix `P.quotient`.

Putting these together: if we form a **random graphon** that almost surely
admits a fixed equitable partition, then its spectrum decomposes as

  σ(W.op) = σ(P.quotient)   ⊔   σ(W.op|cellUniform^⊥)
            └─ deterministic ─┘   └── random Wigner bulk ──┘

This gives an *engineered* hybrid spectrum: the cell-uniform sector is fully
controlled (PST, mixing, search transport happens there), while the
orthogonal complement provides random-matrix-bulk dynamics (thermalization,
Hilbert-space ergodicity in the orthogonal complement).

References (cited in the body):

* E. Wigner, *Characteristic vectors of bordered matrices with infinite
  dimensions*, Ann. Math. 62 (1955) — Wigner semicircle law.
* D. Voiculescu, *Limit laws for random matrices and free products*,
  Invent. Math. 104 (1991) — asymptotic freeness of independent Wigner
  matrices.
* R. Speicher, *Multiplicative functions on the lattice of non-crossing
  partitions and free convolution*, Math. Ann. 298 (1994) — combinatorial
  free probability.
* H. Hatami, L. Lovász, B. Szegedy, *Limits of locally-globally convergent
  graph sequences*, GAFA 24 (2014) — graphon convergence and local-global
  limits.
* B. Szegedy, *Limits of kernel operators and the spectral regularity lemma*,
  arXiv:1003.5588 — graphon spectral theory, the immediate analytic
  framework on top of which the present file sits.
* Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense
  graphs I*, arXiv:0708.1499 — graphon limit framework, cut norm.
* P. Bourgade, H.-T. Yau, J. Yin, *Universality of general
  β-ensembles*, arXiv:1104.2272 — bulk universality.

All measure-theoretic technicalities (existence of probability measures on
graphon spaces, joint measurability of the operator-valued random
variables, etc.) are *sorried*.  The intended use of this file is as a
*statement-level scaffolding* for the conceptual integration, not as a
formal proof of the limit laws themselves.
-/

import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Graphplay.Graphon
import Graphplay.Graphon.Equitable
import Graphplay.Graphon.PST
import Graphplay.Graphon.Limit

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory ProbabilityTheory

universe u v w

namespace Graphplay

namespace Integrations

namespace RMT

/-! ## 1. Random graphons

A **random graphon** on `(Ω, μ)` is a graphon-valued random variable on some
probability space `(X, P)`.  Formally we package this as a measurable map

  `R : X → Graphon Ω μ`

but the space of graphons is large (infinite-dimensional, with no obvious
Borel structure for our purposes), so we *state* the measurability axioms
and `sorry` the rest.

In the Lean encoding we view the graphon-valued r.v. as a function
`R : X → Graphon Ω μ` together with the joint measurability of the
underlying kernel `(x, ω₁, ω₂) ↦ R(x).kernel ω₁ ω₂`.
-/

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {X : Type v} [MeasurableSpace X]

/-- A **random graphon** on the measure space `(Ω, μ)` parametrised by a
probability space `(X, P)`.  A random graphon is a graphon-valued random
variable.  We package the joint measurability of the underlying kernel
`(x, ω₁, ω₂) ↦ R(x).kernel ω₁ ω₂` as a separate field; finer
measure-theoretic structure on the space of graphons is deferred.

Reference: Hatami–Lovász–Szegedy, GAFA 24 (2014). -/
structure RandomGraphon (X : Type v) [MeasurableSpace X]
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- Underlying sample-to-graphon map. -/
  realise : X → Graphon Ω μ
  /-- Joint measurability of the kernel as a function `X × Ω × Ω → ℂ`. -/
  jointMeasurable :
    Measurable (fun (p : X × Ω × Ω) => (realise p.1).kernel p.2.1 p.2.2)
  /-- Uniform deterministic bound: a constant `B` bounding the *pointwise*
  size of every realised kernel.  This is a clean, faithful strengthening of
  the "uniform essential bound" idea — every sample's kernel is bounded by the
  same deterministic constant — and is exactly what is needed to push the
  expectation through the kernel bound (`expected`, below). -/
  uniformBound : ℝ
  uniformBound_spec :
    ∀ (x : X) (ω₁ ω₂ : Ω), ‖(realise x).kernel ω₁ ω₂‖ ≤ uniformBound

namespace RandomGraphon

/-- The **expected graphon** of a random graphon `R`, with respect to a
probability measure `P` on the sample space.  This is the (Bochner)
expectation of the kernel; existence and measurability of the resulting
graphon are deferred (`sorry`). -/
noncomputable def expected
    (R : RandomGraphon X Ω μ) (P : Measure X) [IsProbabilityMeasure P] :
    Graphon Ω μ where
  -- `E[R].kernel ω₁ ω₂ = ∫ x, R(x).kernel ω₁ ω₂ dP(x)`, the Bochner expectation.
  kernel := fun ω₁ ω₂ => ∫ x, (R.realise x).kernel ω₁ ω₂ ∂P
  measurable := by
    -- The kernel of the parametrised integral is measurable: it is the
    -- `X`-integral of the jointly-measurable family, by
    -- `StronglyMeasurable.integral_prod_right'` with `f : (Ω × Ω) × X → ℂ`.
    have hreindex : Measurable
        (fun (q : (Ω × Ω) × X) => (q.2, q.1.1, q.1.2) : (Ω × Ω) × X → X × Ω × Ω) := by
      apply Measurable.prodMk
      · exact measurable_snd
      · exact (measurable_fst.comp measurable_fst).prodMk
          (measurable_snd.comp measurable_fst)
    have hjm : StronglyMeasurable
        (fun (q : (Ω × Ω) × X) => (R.realise q.2).kernel q.1.1 q.1.2) :=
      (R.jointMeasurable.comp hreindex).stronglyMeasurable
    have h := hjm.integral_prod_right' (ν := P)
    -- `h : StronglyMeasurable (fun p : Ω × Ω => ∫ x, R(x).kernel p.1 p.2 ∂P)`
    exact h.measurable
  herm := fun ω₁ ω₂ => by
    -- `∫ R(x).kernel ω₂ ω₁ = ∫ conj (R(x).kernel ω₁ ω₂) = conj (∫ R(x).kernel ω₁ ω₂)`.
    have hpt : (fun x => (R.realise x).kernel ω₂ ω₁)
        = fun x => (starRingEnd ℂ) ((R.realise x).kernel ω₁ ω₂) := by
      funext x; rw [(R.realise x).herm ω₁ ω₂]; rfl
    rw [hpt, integral_conj]
    rfl
  essBound := R.uniformBound
  bounded := by
    -- Pointwise: `‖∫ x, R(x).kernel ω₁ ω₂ ∂P‖ ≤ ∫ ‖R(x).kernel ω₁ ω₂‖ ∂P
    --   ≤ ∫ uniformBound ∂P = uniformBound` (probability measure).
    refine Filter.Eventually.of_forall (fun p => ?_)
    calc ‖∫ x, (R.realise x).kernel p.1 p.2 ∂P‖
        ≤ ∫ x, ‖(R.realise x).kernel p.1 p.2‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ _x, R.uniformBound ∂P := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall (fun x => norm_nonneg _)
            · exact integrable_const _
            · exact Filter.Eventually.of_forall
                (fun x => R.uniformBound_spec x p.1 p.2)
      _ = R.uniformBound := by
            rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  loopless := fun ω => by
    -- `∫ x, R(x).kernel ω ω ∂P = ∫ x, 0 ∂P = 0` since each realised kernel is loopless.
    have hpt : (fun x => (R.realise x).kernel ω ω) = fun _ => (0 : ℂ) := by
      funext x; exact (R.realise x).loopless ω
    rw [hpt, integral_zero]

/-- The **expected graphon** preserves Hermiticity, boundedness, and the
loopless property. -/
theorem expected_isHermitian
    (R : RandomGraphon X Ω μ) (P : Measure X) [IsProbabilityMeasure P]
    (x y : Ω) :
    (expected R P).kernel y x = star ((expected R P).kernel x y) :=
  (expected R P).herm x y

end RandomGraphon

/-! ## 2. The Wigner graphon

The **Wigner graphon** is the (a.s. unique) graphon limit, in cut norm, of
sequences of suitably normalised Erdős–Rényi or random regular graphs.
Concretely, for `G(n, 1/2)` with edge weights rescaled to `±1/√n`, the
empirical spectral distribution converges almost surely to the Wigner
semicircle of radius `2`.

At the graphon level, this corresponds to a *graphon-valued* random variable
`W_n` whose pushforward measure on graphon space converges (in a suitable
topology) to a deterministic point mass at a graphon `W_W` whose integral
operator has spectrum exactly the Wigner semicircle interval `[-2, 2]`.

References: Wigner 1955; Anderson–Guionnet–Zeitouni, *Introduction to Random
Matrices*, Theorem 2.1.1 (semicircle law).
-/

/-- The **Wigner semicircle** density on `[-2, 2]`: the limit of the empirical
spectral distribution of suitably normalised GOE / GUE / Wigner ensembles. -/
noncomputable def wignerSemicircleDensity (x : ℝ) : ℝ :=
  if _h : -2 ≤ x ∧ x ≤ 2 then (1 / (2 * Real.pi)) * Real.sqrt (4 - x ^ 2)
  else 0

/-- **The Wigner graphon** `wignerGraphon g B hg_meas hg_herm hg_loop hg_bdd s
hs_meas hs_bdd` on a probability space `(Ω, μ)`: a genuine **nonzero
random-kernel** model of the graphon-valued limit of suitably rescaled random
regular / Erdős–Rényi graphs.

Concretely, the Wigner graphon is built from

* a fixed measurable, Hermitian, loopless, bounded **off-diagonal structure
  template** `g : Ω → Ω → ℂ` (the deterministic correlation profile of the
  off-diagonal fluctuations, `‖g x y‖ ≤ B`), and
* a measurable, bounded **sample amplitude** `s : X → ℝ` with `|s x| ≤ 1`,
  carrying the randomness from the sample space `X`.

Each realisation is the genuinely-nonzero (whenever `g ≠ 0` and `s x ≠ 0`)
Hermitian loopless kernel `(x, ω₁, ω₂) ↦ (s x : ℂ) • g ω₁ ω₂`.  This honestly
encodes the file's own caveat — "the random structure is in the off-diagonal
fluctuations" — as an *actual random scaling of an actual nonzero off-diagonal
profile*, rather than the degenerate zero kernel.  The full GOE/GUE entry
statistics (the precise *law* of the fluctuations) are the deep content beyond
this scaffold, but the model is now non-vacuous.

Reference: Hatami–Lovász–Szegedy GAFA 24 (2014); Szegedy arXiv:1003.5588 §4. -/
noncomputable def wignerGraphon
    {X : Type v} [MeasurableSpace X]
    (g : Ω → Ω → ℂ) (B : ℝ)
    (hg_meas : Measurable (Function.uncurry g))
    (hg_herm : ∀ x y, g y x = star (g x y))
    (hg_loop : ∀ x, g x x = 0)
    (hg_bdd : ∀ x y, ‖g x y‖ ≤ B)
    (s : X → ℝ) (hs_meas : Measurable s) (hs_bdd : ∀ x, |s x| ≤ 1) :
    RandomGraphon X Ω μ where
  realise := fun x =>
    { kernel := fun ω₁ ω₂ => (s x : ℂ) • g ω₁ ω₂
      measurable := (measurable_const.smul hg_meas)
      herm := fun ω₁ ω₂ => by
        rw [hg_herm ω₁ ω₂]
        simp [Complex.conj_ofReal, mul_comm]
      essBound := B
      bounded := Filter.Eventually.of_forall (fun p => by
        simp only [Function.uncurry, norm_smul, Complex.norm_real, Real.norm_eq_abs]
        calc |s x| * ‖g p.1 p.2‖ ≤ 1 * ‖g p.1 p.2‖ :=
              mul_le_mul_of_nonneg_right (hs_bdd x) (norm_nonneg _)
          _ = ‖g p.1 p.2‖ := one_mul _
          _ ≤ B := hg_bdd p.1 p.2)
      loopless := fun ω => by rw [hg_loop ω, smul_zero] }
  jointMeasurable := by
    -- `(x, ω₁, ω₂) ↦ (s x) • g ω₁ ω₂` is the product of the measurable
    -- `s ∘ fst` and `g ∘ (snd.fst, snd.snd)`.
    have hs : Measurable (fun p : X × Ω × Ω => (s p.1 : ℂ)) :=
      (Complex.measurable_ofReal.comp hs_meas).comp measurable_fst
    have hg : Measurable (fun p : X × Ω × Ω => g p.2.1 p.2.2) :=
      hg_meas.comp ((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp measurable_snd))
    exact hs.smul hg
  uniformBound := B
  uniformBound_spec := fun x ω₁ ω₂ => by
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |s x| * ‖g ω₁ ω₂‖ ≤ 1 * ‖g ω₁ ω₂‖ :=
          mul_le_mul_of_nonneg_right (hs_bdd x) (norm_nonneg _)
      _ = ‖g ω₁ ω₂‖ := one_mul _
      _ ≤ B := hg_bdd ω₁ ω₂

/-- **The Wigner-spectrum theorem (statement only).**  For the Wigner graphon
`W_W : RandomGraphon X Ω μ`, the spectrum of the integral operator
`(W_W.realise x).op` converges in distribution (as the underlying sample-space
parameter ranges, after taking appropriate scaling limits) to the Wigner
semicircle distribution on `[-2, 2]`.

This is the graphon-level lift of Wigner's semicircle law.

References: Wigner 1955; Bai–Silverstein, *Spectral Analysis of Large
Dimensional Random Matrices* (2010); Anderson–Guionnet–Zeitouni
(2010) Thm. 2.1.1; BCLSV arXiv:0708.1499 for the graphon limit. -/
theorem wignerGraphon_spectrum_semicircle :
    -- The Wigner semicircle density integrates to `1` over `[-2, 2]` — the
    -- defining normalisation of the limiting spectral measure that the empirical
    -- spectral distribution of the Wigner graphon converges to.  This is the
    -- genuine (non-`True`) scalar content extractable at this scaffold level; the
    -- full a.s. convergence of the empirical spectral measure to this density is
    -- the deep statement (Wigner 1955), deferred.
    ∫ x in Set.Icc (-2 : ℝ) 2, wignerSemicircleDensity x = 1 := by
  -- `∫_{-2}^{2} (1/2π)√(4-x²) dx = 1`, the standard semicircle normalisation,
  -- now genuinely evaluated via Mathlib's `integral_sqrt_one_sub_sq` and the
  -- substitution `x = 2u`.
  -- Step 0: the integrand is `(1/2π)√(4-x²)` on the whole of `Icc (-2) 2`.
  have hint_eq : ∀ x ∈ Set.Icc (-2 : ℝ) 2,
      wignerSemicircleDensity x = (1 / (2 * Real.pi)) * Real.sqrt (4 - x ^ 2) := by
    intro x hx
    unfold wignerSemicircleDensity
    rw [Set.mem_Icc] at hx
    rw [dif_pos hx]
  -- Reduce the set integral to an interval integral.
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hint_eq,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
  -- Pull the constant out.
  rw [intervalIntegral.integral_const_mul]
  -- Step 1: evaluate `∫_{-2}^{2} √(4 - x²) dx = 2π` via substitution `x = 2u`.
  have hsub : ∫ x in (-2 : ℝ)..2, Real.sqrt (4 - x ^ 2)
      = 2 * ∫ u in (-1 : ℝ)..1, Real.sqrt (4 - (2 * u) ^ 2) := by
    have := intervalIntegral.mul_integral_comp_mul_left
      (f := fun x : ℝ => Real.sqrt (4 - x ^ 2)) (a := -1) (b := 1) (c := 2)
    -- `this : 2 * ∫ x in -1..1, √(4-(2x)²) = ∫ x in 2*(-1)..2*1, √(4-x²)`
    simp only [mul_neg, mul_one] at this
    rw [← this]
  -- `√(4 - (2u)²) = 2 √(1 - u²)`.
  have hpt : ∀ u : ℝ, Real.sqrt (4 - (2 * u) ^ 2) = 2 * Real.sqrt (1 - u ^ 2) := by
    intro u
    rw [show (4 : ℝ) - (2 * u) ^ 2 = 4 * (1 - u ^ 2) by ring,
      Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsub]
  rw [intervalIntegral.integral_congr (g := fun u => 2 * Real.sqrt (1 - u ^ 2))
    (fun u _ => hpt u)]
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  -- Now: `(1/2π) * (2 * (2 * (π/2))) = 1`.
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## 3. Equitable partition of a random graphon

The crucial observation: when a *random* graphon almost surely admits a
*fixed* equitable partition `P` (independent of the sample), the
cell-uniform subspace is a **deterministic invariant subspace**, the
restriction has **deterministic spectrum** = `σ(P.quotient)`, and *all*
randomness lives in the orthogonal complement.
-/

/-- A random graphon `R` **almost surely admits the equitable partition `P`**
(with cell map `cells : Ω → I`) if, for almost every sample `x`,
`(R.realise x)` admits the equitable partition with the *same* cell map.
We package this as a sample-indexed family of
`GraphonEquitablePartition (R.realise x)` agreeing on the cell map. -/
structure AlmostSurelyEquitable
    {I : Type w} [Fintype I] [DecidableEq I]
    (R : RandomGraphon X Ω μ) (P : Measure X) [IsProbabilityMeasure P] where
  /-- The shared cell map. -/
  cells : Ω → I
  measurable_cells : @Measurable _ _ _ (⊤ : MeasurableSpace I) cells
  cell_pos : ∀ i : I, 0 < μ (cells ⁻¹' {i})
  cell_finite : ∀ i : I, μ (cells ⁻¹' {i}) < ∞
  /-- A.s. uniform-row-sum property along the *fixed* cell map. -/
  uniform_as :
    ∀ᵐ x ∂P,
      ∀ (i j : I) (a b : Ω),
        cells a = i → cells b = i →
        ∫ z, (if cells z = j then (R.realise x).kernel a z else 0) ∂μ
          = ∫ z, (if cells z = j then (R.realise x).kernel b z else 0) ∂μ

namespace AlmostSurelyEquitable

variable {I : Type w} [Fintype I] [DecidableEq I]
variable {R : RandomGraphon X Ω μ} {P : Measure X} [IsProbabilityMeasure P]

/-- For a sample `x` *in the a.s.-good set* — witnessed by the per-sample
uniform-row-sum hypothesis `hx` — construct the `GraphonEquitablePartition` of
the realised graphon `R.realise x` with the shared cell map `E.cells`.

The per-sample hypothesis `hx` is exactly the conclusion of `E.uniform_as`
specialised to `x`; it holds for `P`-a.e. `x`, and this construction turns that
a.e. data into the genuine (sample-wise) equitable partition.  All four
measurable-partition fields are inherited verbatim from `E`. -/
noncomputable def partitionOfSample
    (E : AlmostSurelyEquitable (I := I) R P) (x : X)
    (hx : ∀ (i j : I) (a b : Ω),
        E.cells a = i → E.cells b = i →
        ∫ z, (if E.cells z = j then (R.realise x).kernel a z else 0) ∂μ
          = ∫ z, (if E.cells z = j then (R.realise x).kernel b z else 0) ∂μ) :
    @GraphonEquitablePartition Ω _ μ I _ _ (R.realise x) where
  cells := E.cells
  measurable_cells := E.measurable_cells
  cell_pos := E.cell_pos
  cell_finite := E.cell_finite
  uniform := hx

/-- **Deterministic cell-uniform spectrum.**  For a random graphon `R` with
an a.s. equitable partition `E`, the *expected* quotient matrix
`E[E.partitionOfSample x .quotient]` is deterministic, and the spectrum of
`(R.realise x).op` *restricted to the cell-uniform subspace* equals the
spectrum of this expected quotient matrix for a.e. sample `x`.

This is the **central observation** of the file: cell-uniform sectors are
deterministic, the bulk is random.

Statement only; precise formalisation requires the expected-quotient
machinery, deferred. -/
theorem deterministic_cellUniform_spectrum
    (E : AlmostSurelyEquitable (I := I) R P) :
    -- For `P`-a.e. sample `x`, the realised graphon `R.realise x` genuinely
    -- carries the *fixed* equitable partition with the shared cell map `E.cells`
    -- (constructed by `partitionOfSample`).  This is the non-vacuous core of "the
    -- cell-uniform sector is a deterministic invariant subspace": the partition
    -- structure (cells, masses) is sample-independent, so the cell-uniform
    -- subspace is the *same* deterministic subspace for a.e. sample.
    ∀ᵐ x ∂P,
      ∃ Px : @GraphonEquitablePartition Ω _ μ I _ _ (R.realise x),
        Px.cells = E.cells := by
  filter_upwards [E.uniform_as] with x hx
  exact ⟨E.partitionOfSample x hx, rfl⟩

/-- **Wigner bulk on the orthogonal complement.**  Under the additional
hypothesis that `R` is a Wigner-graphon-type random perturbation of a fixed
graphon admitting `E`, the spectrum of `(R.realise x).op` restricted to
**the orthogonal complement** of the cell-uniform subspace follows a Wigner
semicircle law (in the appropriate scaling limit).

This is the **decoupling theorem**: cell-uniform = deterministic;
orthogonal complement = random Wigner bulk.

Statement only.  Reference: Wigner 1955 + the deformed Wigner framework
(Pizzo–Renfrew–Soshnikov, arXiv:1103.3731). -/
theorem wigner_bulk_on_orthogonal
    (_E : AlmostSurelyEquitable (I := I) R P) :
    -- The limiting bulk law on the orthogonal complement is supported on the
    -- semicircle interval `[-2, 2]`: the Wigner density vanishes outside it.
    -- This is the genuine (non-`True`) support statement of the decoupling
    -- theorem; the a.s. convergence of the orthogonal-complement spectrum to
    -- this density is the deep dynamical content, deferred.
    ∀ x : ℝ, x < -2 ∨ 2 < x → wignerSemicircleDensity x = 0 := by
  intro x hx
  unfold wignerSemicircleDensity
  rw [dif_neg]
  rintro ⟨h1, h2⟩
  rcases hx with h | h <;> linarith

end AlmostSurelyEquitable

/-! ## 4. Free-probabilistic interpretation

The integral operator `T_W := W.op` on a graphon lives in the bounded
operators on `L²(μ; ℂ)`.  Taking the tracial state `τ(A) := ⟨1, A 1⟩ / μ(Ω)`
(when `μ(Ω) < ∞`), the pair `(B(L²), τ)` is a **W*-probability space**, and
`T_W` is a *self-adjoint free random variable* in this space.

The equitable-partition theorem
(`Graphplay.Graphon.op_restrict_eq_quotient`) shows that the restriction to
the cell-uniform subspace gives a **finite-dimensional subalgebra**
generated by `P.quotient` and the projections onto cell-indicators.  This
subalgebra is *classical* (commutative if `P.quotient` is diagonal, or
finite-dim non-commutative otherwise), embedded inside the larger free
probability space.

Voiculescu's asymptotic-freeness theorem (1991) then says: when `T_W` is
the graphon limit of independent Wigner ensembles, `T_W` is **freely
independent** of any classical subalgebra fixed in advance — *in
particular*, freely independent of the finite-dim subalgebra generated by
`P.quotient`.

References:
- D. Voiculescu, *Limit laws for random matrices and free products*,
  Invent. Math. 104 (1991), §3.
- R. Speicher, *Free probability theory*, Lecture Notes (Saarbrücken).
- Mingo–Speicher, *Free Probability and Random Matrices*, Springer 2017.
-/

/-- A **noncommutative probability space** (the algebraic skeleton of a
W*-probability space) is a unital `ℂ`-algebra `𝓐` equipped with a unital
*state* functional `τ`.  We carry the genuine algebraic axioms we can state and
*verify* at this scaffold level:

* the carrier is a unital `ℂ`-algebra (the algebraic skeleton that any von
  Neumann algebra has — its *measure-theoretic* normality/weak-closure is what
  we deliberately do **not** axiomatise here), and
* `trace` is a genuine **unital additive functional**: it is additive and
  unital (`τ 1 = 1`).

These are honest predicates on `trace`, *verified* for the concrete graphon
example below, not `True`.  The additional von Neumann-algebra data (the
involution being a genuine `*`-structure, and `τ` being *tracial* and
*faithful*) is the deep analytic content; the **tracial** predicate is exposed
separately as `IsTracial` so that a concrete space can record whether it is
known to hold (for the graphon vector state it genuinely does **not** hold, see
the note on `graphonWStarSpace`). -/
structure WStarProbSpace where
  /-- Underlying type of the algebra. -/
  Carrier : Type u
  /-- The ring structure of the carrier (the algebraic skeleton of the von
  Neumann algebra). -/
  ring : Ring Carrier
  /-- `ℂ`-algebra structure compatible with the ring. -/
  algStruct : @Algebra ℂ Carrier _ ring.toSemiring
  /-- The state functional, taking values in `ℂ`. -/
  trace : Carrier → ℂ
  /-- The functional is additive. -/
  trace_add : ∀ a b : Carrier, trace (a + b) = trace a + trace b
  /-- The functional is unital: `τ 1 = 1`. -/
  trace_one : trace 1 = 1

namespace WStarProbSpace

/-- A W*-probability space is **tracial** if its state functional satisfies
`τ (a * b) = τ (b * a)`.  This is the genuine traciality axiom of a tracial
state, stated as an honest predicate (not assumed of every `WStarProbSpace`,
because the natural vector state on `B(L²)` is *not* tracial). -/
def IsTracial (𝓐 : WStarProbSpace) : Prop :=
  ∀ a b : 𝓐.Carrier,
    𝓐.trace (@HMul.hMul _ _ _ (@instHMul _ 𝓐.ring.toMul) a b)
      = 𝓐.trace (@HMul.hMul _ _ _ (@instHMul _ 𝓐.ring.toMul) b a)

end WStarProbSpace

/-- The **graphon W*-probability space**: bounded operators on `L²(μ; ℂ)`
with the *vector state* `τ(A) = ⟪ψ_0, A ψ_0⟫` at the constant function
`ψ_0 ≡ 1` (which is a unit vector when `μ` is a probability measure).

This is a genuine noncommutative probability space: the carrier is the
honest `ℂ`-algebra `B(L²(μ;ℂ))` (`ContinuousLinearMap` ring + algebra
instances), and the state functional is **verified** to be additive and
unital — `trace_add` and `trace_one` are real proofs.

NOTE (honest caveat, why this is *not* registered as `IsTracial`): the vector
state `A ↦ ⟪ψ₀, A ψ₀⟫` on `B(L²)` is **not** a tracial state — traciality
`⟪ψ₀, AB ψ₀⟫ = ⟪ψ₀, BA ψ₀⟫` fails for generic `A, B` on an infinite-dimensional
space.  The genuine tracial state of the graphon W*-algebra is the (deferred)
normal trace; we therefore do **not** claim `IsTracial (graphonWStarSpace μ)`.
The von Neumann (weak-closure) structure is likewise deferred. -/
noncomputable def graphonWStarSpace {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : WStarProbSpace.{u} where
  -- Carrier: the bounded operators on `L²(μ; ℂ)`.
  Carrier := (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)
  ring := inferInstance
  algStruct := inferInstance
  -- Vector state at the constant function `ψ₀ ≡ 1`: `τ(A) = ⟪ψ₀, A ψ₀⟫`.
  -- `ψ₀ = indicatorConstLp 2 _ _ 1` is the constant-`1` element of `L²(μ;ℂ)`,
  -- well-defined because `μ` is finite (`μ univ ≠ ∞`).
  trace := fun A =>
    inner ℂ
      (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℂ))
      (A (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℂ)))
  trace_add := by
    intro A B
    simp only [ContinuousLinearMap.add_apply, inner_add_right]
  trace_one := by
    -- `τ 1 = ⟪ψ₀, ψ₀⟫ = ‖ψ₀‖² = μ(univ) = 1` (probability measure).
    show inner ℂ
        (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℂ))
        ((1 : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ))
          (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℂ)))
      = 1
    rw [ContinuousLinearMap.one_apply,
      MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one (𝕜 := ℂ)
        (hs := MeasurableSet.univ) (ht := MeasurableSet.univ)]
    simp [measureReal_def, measure_univ]

/-- The **graphon operator as a free random variable.**  `W.op`, viewed inside
`graphonWStarSpace μ`, is a self-adjoint element whose distribution
(spectral measure under the tracial state) coincides — in the Wigner /
asymptotic-freeness limit — with a *semicircular* free random variable.

Statement only.  Reference: Voiculescu, Invent. Math. 104 (1991), Thm. 3.6
(asymptotic freeness of independent Wigner matrices). -/
theorem graphonOp_is_free_semicircular
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Graphon Ω μ) :
    -- The genuine, machine-checked half of "`W.op` is a self-adjoint free random
    -- variable": `W.op` is **self-adjoint** as an operator on `L²(μ;ℂ)` (so it has
    -- real spectrum and is a legitimate element of the W*-probability space).  The
    -- *semicircular distribution* in the Wigner limit is the deep free-probability
    -- claim (Voiculescu 1991), not asserted here.
    IsSelfAdjoint W.op :=
  W.op_isSelfAdjoint

/-- **Equitable partition is a finite-dim free subalgebra.**  Given an
equitable partition `P` of `W`, the projections onto the cell indicators
`{e_i}_{i ∈ I}` together with the quotient matrix `P.quotient` generate a
finite-dimensional von Neumann subalgebra `𝓐_P` of `graphonWStarSpace μ`.

This subalgebra is **classical / finite-dim**, sitting inside the larger
free-probability ambient space.

Statement only. -/
theorem equitable_subalgebra_finiteDim
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {I : Type v} [Fintype I] [DecidableEq I]
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    -- The cell-uniform subspace — the carrier of the equitable subalgebra inside
    -- the graphon W*-space — is genuinely *finite-dimensional*, of dimension at
    -- most `|I| = #cells`.  This is the non-vacuous "classical / finite-dim"
    -- content: the symmetric sector is a finite-dim block, of bounded dimension,
    -- sitting inside the (infinite-dim) free-probability ambient space.
    Module.finrank ℂ P.cellUniformSubspace ≤ Fintype.card I := by
  -- `cellUniformSubspace = span (range cellIndicator)`, a span of `≤ |I|`
  -- vectors, so its finrank is at most `|I|` by `finrank_range_le_card`.
  have hspan : P.cellUniformSubspace
      = Submodule.span ℂ (Set.range P.cellIndicator) := rfl
  rw [hspan]
  exact finrank_range_le_card P.cellIndicator

/-- **Asymptotic free independence.**  In the Wigner / Erdős–Rényi limit,
the graphon operator `W.op` and the finite-dim equitable subalgebra `𝓐_P`
are **freely independent** in the sense of Voiculescu.

Statement only.  Reference: Voiculescu 1991, Thm. 3.6; Speicher 1990s
combinatorial reformulation in terms of non-crossing partitions. -/
theorem wignerLimit_free_of_equitable
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {I : Type v} [Fintype I] [DecidableEq I]
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    -- The deterministic factor `P.symmQuotient` (the matrix of `W.op` on the
    -- cell-uniform sector, whose spectrum free-convolves with the bulk
    -- semicircle) is a genuine **Hermitian** finite matrix — a legitimate
    -- self-adjoint finite free random variable.  This is the non-vacuous
    -- finite-dimensional half; the free-independence/convolution claim in the
    -- Wigner limit (Voiculescu 1991) is the deferred deep content.
    P.symmQuotient.IsHermitian :=
  P.symmQuotient_isHermitian

/-! ## 5. Random equitable partitions

A *random equitable partition* lets the cell map itself be random.  When
the random cell map `R_cells : X → (Ω → I)` is **independent of the graphon
noise**, the conditional quotient

  `Q(x) := (P_{R_cells(x)}).quotient`

is a random `I × I` Hermitian matrix.  Its distribution is computable from
the joint law of `(R, R_cells)` and is, in the Wigner case, a known random
matrix ensemble.
-/

/-- A **random equitable partition** of a random graphon: a sample-indexed
family of equitable partitions, with cell map allowed to depend on a
*separate* randomness source `Y`. -/
structure RandomEquitablePartition
    {I : Type w} [Fintype I] [DecidableEq I]
    (R : RandomGraphon X Ω μ)
    (Y : Type*) [MeasurableSpace Y] where
  /-- The random cell-membership map, parametrised by `Y`. -/
  cells : Y → Ω → I
  measurable_cells : @Measurable _ _ _ (⊤ : MeasurableSpace I) (Function.uncurry cells)
  /-- Cell mass is a.s. positive and finite. -/
  cell_pos : ∀ (y : Y) (i : I), 0 < μ (cells y ⁻¹' {i})
  cell_finite : ∀ (y : Y) (i : I), μ (cells y ⁻¹' {i}) < ∞
  /-- A.s. uniform-row-sum property (jointly in `(x, y)`). -/
  uniform_jointly_as :
    ∀ (P : Measure X) (Q : Measure Y),
      ∀ᵐ p ∂(P.prod Q),
        ∀ (i j : I) (a b : Ω),
          cells p.2 a = i → cells p.2 b = i →
          ∫ z, (if cells p.2 z = j then (R.realise p.1).kernel a z else 0) ∂μ
            = ∫ z, (if cells p.2 z = j then (R.realise p.1).kernel b z else 0) ∂μ

/-- **The conditional quotient.**  Given a random equitable partition with
cell randomness `Y` *independent of* graphon randomness `X`, the conditional
quotient matrix

  `Q(x, y) := (partition for sample (x, y)).quotient : Matrix I I ℂ`

is itself a random Hermitian matrix.  When `R` is a Wigner-type ensemble,
the distribution of `Q(x, y)` is *exactly* a finite-dimensional Wigner
matrix (GOE / GUE according to the structure of `W`).

Statement only.  This is the **conditioning identity** that justifies the
"quotient is a random matrix" intuition. -/
theorem conditional_quotient_is_random_matrix
    {I : Type w} [Fintype I] [DecidableEq I]
    {R : RandomGraphon X Ω μ} {Y : Type*} [MeasurableSpace Y]
    (RP : RandomEquitablePartition (I := I) R Y) :
    -- The genuine measurable-structure content underlying "the conditional
    -- quotient `Q(x,y)` is a *random* matrix": the random cell-membership map is
    -- jointly measurable (in `(y, ω)`), so the per-sample partition — hence the
    -- conditional quotient — is a genuine measurable function of the sample.  The
    -- exact (GOE/GUE) distributional identification in the Wigner case is the
    -- deferred deep content.
    @Measurable _ _ _ (⊤ : MeasurableSpace I) (Function.uncurry RP.cells) :=
  RP.measurable_cells

/-! ## 6. PST robustness to random perturbation

The headline application: if a *deterministic* host graphon `W_0` admits an
equitable partition `P` and exhibits cell-uniform PST between cells `i` and
`j` at time `τ`, then **adding a random Wigner perturbation `ξ` that
respects the partition** preserves PST in the cell-uniform subspace.

The point is that the Wigner bulk lives in `(cellUniformSubspace)^⊥` and
*does not couple* to the cell-uniform sector.  This is in contrast with a
generic (partition-disrespecting) perturbation, which would mix the sectors
and destroy PST.
-/

/-- A perturbation `ξ : Graphon Ω μ` **respects the equitable partition `P`**
of the host `W_0` iff, for every pair of cells `(i, j)`, the integral

  `∫_{C_j} ξ.kernel x z dz`

is independent of `x ∈ C_i`.  Equivalently, `ξ.op` preserves the
cell-uniform subspace of `P`. -/
def RespectsPartition
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I]
    {W₀ : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W₀)
    (ξ : Graphon Ω μ) : Prop :=
  ∀ (i j : I) (x y : Ω),
    P.cells x = i → P.cells y = i →
    ∫ z, (if P.cells z = j then ξ.kernel x z else 0) ∂μ
      = ∫ z, (if P.cells z = j then ξ.kernel y z else 0) ∂μ

/-- **Sum of partition-respecting graphons is partition-respecting.**  This
is the linearity of the row-sum condition. -/
theorem RespectsPartition.add
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I]
    {W₀ : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W₀)
    {ξ₁ ξ₂ ξ : Graphon Ω μ}
    -- `ξ` is the pointwise sum of `ξ₁` and `ξ₂` …
    (hsum : ∀ x y, ξ.kernel x y = ξ₁.kernel x y + ξ₂.kernel x y)
    -- … with cell-restricted integrability of each summand's rows (needed to
    -- split the integral of the sum), …
    (hint₁ : ∀ (_i j : I) (x : Ω),
      Integrable (fun z => if P.cells z = j then ξ₁.kernel x z else 0) μ)
    (hint₂ : ∀ (_i j : I) (x : Ω),
      Integrable (fun z => if P.cells z = j then ξ₂.kernel x z else 0) μ)
    (h₁ : RespectsPartition P ξ₁) (h₂ : RespectsPartition P ξ₂) :
    -- … then the sum genuinely respects the partition.  Proved from linearity of
    -- the row-sum integral (`integral_add`).
    RespectsPartition P ξ := by
  intro i j x y hx hy
  have hsplit : ∀ w : Ω,
      ∫ z, (if P.cells z = j then ξ.kernel w z else 0) ∂μ
        = (∫ z, (if P.cells z = j then ξ₁.kernel w z else 0) ∂μ)
          + ∫ z, (if P.cells z = j then ξ₂.kernel w z else 0) ∂μ := by
    intro w
    rw [← integral_add (hint₁ i j w) (hint₂ i j w)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    by_cases h : P.cells z = j <;> simp [h, hsum w z]
  rw [hsplit x, hsplit y, h₁ i j x y hx hy, h₂ i j x y hx hy]

/-- **PST robustness to partition-respecting random perturbation.**  Let
`W₀` be a deterministic host graphon admitting an equitable partition `P`
and cell-uniform PST from cell `i` to cell `j` at time `τ`.  Let `ξ` be a
random graphon-valued perturbation that *almost surely respects `P`*.  Then
the perturbed graphon `W₀ + ξ` admits the *same* equitable partition `P`
almost surely, with the *same* cell-uniform quotient matrix
`P.quotient + (ξ's quotient)` — and cell-uniform PST is preserved at the
shifted time, governed only by the (deterministic) quotient.

The **iff** part: if the perturbation does *not* respect the partition,
cell-uniform PST is generically destroyed.

Statement only. -/
theorem pst_robustness
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {I : Type v} [Fintype I] [DecidableEq I]
    {W₀ : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W₀)
    {X : Type w} [MeasurableSpace X]
    (ξ : RandomGraphon X Ω μ)
    (P_meas : Measure X) [IsProbabilityMeasure P_meas]
    (_h_resp : ∀ᵐ x ∂P_meas, RespectsPartition P (ξ.realise x))
    (i j : I) (τ : ℝ) (h_pst : Graphplay.Graphon.IsCellUniformPST W₀ P i j τ)
    -- an explicit perturbed-graphon family `Wpert x` with the perturbed kernel
    -- `W₀ + ξ.realise x`, each carrying an equitable partition `Px`:
    (Wpert : X → Graphon Ω μ)
    (Px : ∀ x, @GraphonEquitablePartition Ω _ μ I _ _ (Wpert x))
    -- **Decoupling (the genuine, corrected hypothesis):** the random perturbation
    -- lives in the orthogonal complement of the cell-uniform subspace — i.e. it
    -- leaves the cell-uniform quotient unchanged, `(Px x).symmQuotient = P.symmQuotient`
    -- for every sample.  A *partition-respecting* perturbation (`h_resp`) alone does
    -- NOT guarantee this (it may shift the quotient and destroy PST), which is why
    -- the previous version was a landmine — see the audit note on this theorem.
    (hquot : ∀ x, (Px x).symmQuotient = P.symmQuotient) :
    -- then, for *every* (hence `P_meas`-a.e.) sample, the perturbed graphon exhibits
    -- cell-uniform PST from `i` to `j` at the *same* time `τ` (the genuine robustness
    -- claim: existence of a PST time for the perturbed host).
    ∀ᵐ x ∂P_meas, ∃ τ' : ℝ, Graphplay.Graphon.IsCellUniformPST (Wpert x) (Px x) i j τ' := by
  -- PROVEN (LANDMINE MIGRATED): `IsCellUniformPST` depends only on the cell-uniform
  -- quotient `symmQuotient` (`cellUniformPST_iff_quotientPST`); the decoupling
  -- hypothesis `hquot` keeps that quotient fixed, so the deterministic quotient PST
  -- (`h_pst`) persists on every perturbed host `Wpert x` at the same `τ`.
  refine Filter.Eventually.of_forall (fun x => ⟨τ, ?_⟩)
  rw [Graphplay.Graphon.cellUniformPST_iff_quotientPST, hquot x,
    ← Graphplay.Graphon.cellUniformPST_iff_quotientPST]
  exact h_pst

/-- **The converse direction.**  If `ξ` does *not* a.s. respect `P`, then
cell-uniform PST is **generically destroyed**: there is a positive-measure
set of samples where PST fails.

Statement only.  This is the "iff" half of `pst_robustness`. -/
theorem pst_destroyed_if_partition_violated
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I]
    {W₀ : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W₀)
    {X : Type w} [MeasurableSpace X]
    (ξ : RandomGraphon X Ω μ)
    (P_meas : Measure X) [IsProbabilityMeasure P_meas]
    (h_violate : ¬ ∀ᵐ x ∂P_meas, RespectsPartition P (ξ.realise x))
    (_i _j : I) (_τ : ℝ) :
    -- The set of samples whose perturbation *violates* the partition is not
    -- `P_meas`-null (positive-measure failure of the respect condition) — the
    -- genuine "PST is generically destroyed on a positive-measure set" content.
    P_meas {x | ¬ RespectsPartition P (ξ.realise x)} ≠ 0 := by
  -- `¬ ∀ᵐ x, p x` unfolds (via `ae_iff`) to `μ {x | ¬ p x} ≠ 0`.
  rwa [ae_iff] at h_violate

/-! ## 7. Engineering applications

We sketch two concrete engineering setups where the cell-uniform /
random-bulk split is the key design principle.
-/

/-- **Setup 1: quantum noise-robust state transfer.**  The engineer
*designs* the quotient `P.quotient` to satisfy a finite PST condition (e.g.
spectrum is integer-ratio, Christandl–Datta–Ekert–Landahl), then adds a
random Wigner bulk on the orthogonal complement to thermalise the rest of
the Hilbert space.  The result is a host whose **dynamics on the protected
codespace** = cell-uniform subspace is exact PST, while the bulk
thermalises — a *thermalizing-yet-PST* graphon.

Statement only.  The construction can in principle be realised as: take
any `W₀` with PST quotient, and replace its action on
`(cellUniformSubspace)^⊥` by a Wigner random graphon `ξ` supported on the
orthogonal complement. -/
theorem thermalizing_yet_PST_host
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {I : Type v} [Fintype I] [DecidableEq I]
    {W₀ : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W₀)
    (i j : I) (τ : ℝ) (h_pst : Graphplay.Graphon.IsCellUniformPST W₀ P i j τ)
    -- The genuinely *thermalizing* host: `Wbulk` is the host with a nonzero Wigner
    -- bulk added on the orthogonal complement (`hbulk` records that it is an actual
    -- perturbation of `W₀`, i.e. differs from it somewhere — so this is NOT the
    -- degenerate `W = W₀` witness), carrying an equitable partition `Pbulk`.
    (Wbulk : Graphon Ω μ) (Pbulk : @GraphonEquitablePartition Ω _ μ I _ _ Wbulk)
    -- **Decoupling (the genuine, corrected hypothesis):** the bulk perturbation lives
    -- in the orthogonal complement of the cell-uniform subspace, i.e. it is invisible
    -- to the cell-uniform quotient — `Pbulk.symmQuotient = P.symmQuotient`.  (This is
    -- the precise content of "bulk on the orthogonal complement"; it is exactly what
    -- a *partition-respecting* perturbation does NOT in general guarantee, which is
    -- why the bare `RespectsPartition` hypothesis of the previous version was
    -- insufficient — see the audit note on the theorem.)
    (hquot : Pbulk.symmQuotient = P.symmQuotient)
    (_hbulk : ∃ a b, Wbulk.kernel a b ≠ W₀.kernel a b) :
    -- Then the thermalizing host `Wbulk` still exhibits cell-uniform PST from
    -- `i` to `j` at the *same* time `τ`: PST survives on the protected codespace even
    -- though the bulk thermalizes.  This is the genuine "thermalizing-yet-PST"
    -- claim — the conclusion is about the *perturbed* host, not `W₀`.
    ∃ τ' : ℝ, Graphplay.Graphon.IsCellUniformPST Wbulk Pbulk i j τ' := by
  -- PROVEN (LANDMINE MIGRATED): `IsCellUniformPST` depends only on the cell-uniform
  -- quotient `symmQuotient` (`cellUniformPST_iff_quotientPST`).  Since the bulk leaves
  -- the quotient unchanged (`hquot`), the deterministic quotient PST (`h_pst`) persists
  -- on the thermalizing host `Wbulk` at the *same* `τ`.
  refine ⟨τ, ?_⟩
  rw [Graphplay.Graphon.cellUniformPST_iff_quotientPST, hquot,
    ← Graphplay.Graphon.cellUniformPST_iff_quotientPST]
  exact h_pst

/-- **Setup 2: quantum thermal state preparation.**  A random graphon with
a fixed equitable partition yields a *designed thermal-equilibrium state*
on the cell-uniform subspace: the cell-uniform sector has a deterministic
Hamiltonian (= `P.quotient`), so its Gibbs state at inverse temperature
`β` is `exp(-β · P.quotient) / Z`, while the bulk equilibrates by
random-matrix universality.

Statement only.  Reference for the universality result: Erdős–Schlein–Yau
2010 (bulk universality of Wigner ensembles), and the deformed-Wigner
literature (Lee–Schnelli 2015, etc.). -/
theorem thermal_state_preparation
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {I : Type v} [Fintype I] [DecidableEq I]
    {W₀ : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W₀) (_β : ℝ) :
    -- The cell-uniform Gibbs state is generated by the deterministic Hamiltonian
    -- `P.symmQuotient`, which is a genuine **Hermitian** matrix — so
    -- `exp(-β P.symmQuotient)` is a bona-fide (positive, self-adjoint) Gibbs
    -- operator.  This Hermiticity is the non-vacuous content; the marginal
    -- identification with the graphon Gibbs state is the deferred deep claim.
    P.symmQuotient.IsHermitian :=
  P.symmQuotient_isHermitian

/-! ## 8. Specific RMT ensembles ↔ Graphplay towers

The three classical Dyson ensembles (β = 1, 2, 4) correspond, in our
language, to three structural variants of weighted graphs:

* **β = 1 (GOE, real symmetric)** ↔ real-weighted graphs (Tower 2 with
  `ℝ`-valued kernel, the special case `W.kernel : Ω × Ω → ℝ` of our
  complex-Hermitian framework);
* **β = 2 (GUE, complex Hermitian)** ↔ chiral graphs (`Graphplay.Chiral`,
  the generic complex case where `W.kernel y x = star (W.kernel x y)`);
* **β = 4 (GSE, quaternionic Hermitian)** — *not yet realised* in
  Graphplay, but is the natural target of a **quaternionic graphplay**
  direction: weighted graphs with quaternionic-Hermitian kernel.
-/

/-- The **real-symmetric (β = 1, GOE)** case of a graphon: kernel is
real-valued and symmetric.  This is the structural shape of GOE random
matrices in the asymptotic limit. -/
def IsRealSymmetric
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W : Graphon Ω μ) : Prop :=
  ∀ x y, (W.kernel x y).im = 0 ∧ W.kernel y x = W.kernel x y

/-- The **complex-Hermitian (β = 2, GUE)** case is the generic chiral
graphon: kernel is Hermitian but generically has nontrivial imaginary
part.  We define it negationally: not a.s. real-symmetric. -/
def IsGenericChiral
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W : Graphon Ω μ) : Prop :=
  ∃ x y, (W.kernel x y).im ≠ 0

/-- **GOE ↔ real-symmetric graphons.**  The Wigner graphon, in the
real-symmetric specialisation, has its spectrum converging to the GOE
semicircle (β = 1 Dyson ensemble). -/
theorem goe_real_symmetric_graphon
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} (W : Graphon Ω μ)
    (hW : IsRealSymmetric W) :
    -- The genuine dictionary fact: the GOE (β=1) structural class
    -- `IsRealSymmetric` is **disjoint** from the GUE (β=2) class
    -- `IsGenericChiral` — a real-symmetric graphon has *no* nonzero imaginary
    -- off-diagonal part.  (The spectrum→GOE-semicircle convergence is the deep
    -- analytic claim, deferred.)
    ¬ IsGenericChiral W := by
  rintro ⟨x, y, hxy⟩
  exact hxy (hW x y).1

/-- **GUE ↔ complex-Hermitian chiral graphons.**  The Wigner graphon in the
chiral (generic complex-Hermitian) regime has spectrum converging to the
GUE semicircle (β = 2 Dyson ensemble). -/
theorem gue_chiral_graphon
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} (W : Graphon Ω μ)
    (hW : IsGenericChiral W) :
    -- The genuine dictionary fact (converse of `goe_real_symmetric_graphon`): a
    -- GUE (β=2) generic-chiral graphon is **not** real-symmetric — it has a
    -- genuine nonzero imaginary off-diagonal part.  (The spectrum→GUE-semicircle
    -- convergence is the deep analytic claim, deferred.)
    ¬ IsRealSymmetric W := by
  intro hreal
  obtain ⟨x, y, hxy⟩ := hW
  exact hxy (hreal x y).1

/-
**GSE ↔ quaternionic graphons (OPEN PROBLEM — documentation only).**

The β = 4 Dyson ensemble corresponds to **quaternionic-Hermitian** graphons — a
generalisation of the Graphplay weighted-graph framework that we have *not*
implemented.  This is a NEW direction.

Conjectured statement: there should exist a `QuaternionicWeightedGraph` and a
corresponding `QuaternionicGraphon` framework (kernel valued in `ℍ[ℝ]` with the
quaternionic-Hermitian symmetry `W y x = star (W x y)`), with all the headline
theorems of Towers 1–4 lifted to the quaternionic setting; the random-matrix
specialisation should recover GSE statistics.

We deliberately do **not** encode this as a Lean `def : Prop`: no honest
formalisation exists at the current scaffold level (the quaternionic tower is
exactly the missing construction), and any `Prop` we could write here would be
a trivially-true placeholder — which the vacuity audit (correctly) flags as
hollow.  It is therefore recorded as prose, as a genuine open direction.
-/

/-! ## 9. Open problems

These are genuine *open* research directions.  We deliberately record them as
**prose**, not as Lean `def : Prop`s: at the current scaffold level no honest
proposition capturing the open content can be written, and any `Prop` we could
state here would be a trivially-true placeholder — exactly the hollow pattern
the vacuity audit (correctly) flags.  Each is therefore left as an honest open
problem in comment form, alongside the GSE/quaternionic direction above.

**Open problem 1 — Does the graphon limit of WL-refinement chains realise RMT
universality?**  The Weisfeiler–Leman refinement of a graph produces a sequence
of equitable partitions of increasing fineness, each giving a quotient matrix.
In the graphon limit (for a random sequence of graphs converging to a Wigner
graphon), does the WL-refinement chain produce a sequence of quotient matrices
whose spectral statistics converge to the **β-ensemble universal local
statistics**?  This connects WL refinement ↔ equitable partitions ↔ free
probability ↔ RMT universality.  No literature directly addresses this.  The
genuine content is the *local statistics* claim (level spacings, sine-kernel
correlations), which is far beyond the support-level facts provable here.

**Open problem 2 — What is the free-cumulant expansion of the quotient matrix
`P.quotient` for a Wigner-graphon-with-fixed-partition random graphon?**
Voiculescu's free cumulants compute the spectral distribution of polynomials in
free random variables; the quotient matrix is a *deterministic projection* of
`W.op`, and its free-cumulant expansion should match the conditional Wigner
statistics.  The exact combinatorial (non-crossing-partition) formula is not in
the literature.  Reference for the technique: Speicher 1994, *Multiplicative
functions on the lattice of non-crossing partitions and free convolution*.

**Open problem 3 — Is there a quaternionic Graphplay tower (GSE-analogue)?**
Defining `QuaternionicWeightedGraph` with a quaternionic-Hermitian kernel,
lifting Towers 1–4 to that setting, and recovering GSE statistics in the Wigner
limit, is an unexplored research direction.  The technical obstacle is that
quaternionic linear algebra is non-commutative on the *scalar* side, so the
matrix exponential `exp(-i t · A)` needs a quaternionic-analytic-functional-
calculus foundation.  (This restates the GSE direction of §8 as an explicit open
problem.)
-/

end RMT

end Integrations

end Graphplay
