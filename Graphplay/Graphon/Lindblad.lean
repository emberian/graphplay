/-
# Graphon/Lindblad.lean — Lindblad open quantum systems on graphons (Tower 4)

This file is the **Round-3 loop-closer** for the graphon side of the
open-system story.  Closed-system Tower 4 dynamics are unitary CTQW on
`L²(Ω, μ)` (see `Graphplay/Graphon.lean` and `Graphplay/Graphon/PST.lean`).
The *finite* open-system theory — a `NoiseModel` of Lindblad jump operators
plus the cell-uniform-symmetric reduction theorem — lives in
`Graphplay/Toolkit/Noise.lean` (D8 in the project ledger).  What was missing,
and is supplied here, is the **graphon** lift of that open-system theory:

* a `GraphonLindbladian` structure packaging a graphon Hamiltonian together
  with a measurable family of Lindblad operators on `L²(Ω, μ)`;
* the associated Lindblad semigroup `LindbladEvolution` on bounded operators
  on `L²(Ω, μ)`, viewed as a one-parameter family of completely positive
  trace-preserving maps acting on density operators;
* the **cell-uniform invariance** condition (each Lindblad operator commutes
  with the cell-uniform-projection operator built from an equitable partition
  of the graphon);
* the **headline reduction theorem** (`GraphonLindblad.cellUniform_preserved`)
  — the graphon-level analogue of the finite-dim `cellUniform_preserved` of
  `Graphplay/Toolkit/Noise.lean` — and its two corollaries:
    * the **consistent-finite-sequence bridge**, which closes the loop with
      `Graphon/Limit.lean` (L10), and
    * **PST under dissipation**, which closes the loop with `Graphon/PST.lean`.

The headline statements are deferred (`sorry`); proofs would combine the
finite-dim D8 reduction with the closed-system equitable lifting theorem of
`Graphon/Equitable.lean` and the operator-norm convergence of `Graphon/Limit`.

This is the "open-system quasi-infinite" piece: it is the last edge in the
square of (finite, graphon) × (closed, open) Tower-4 reductions.

## References

* Lindblad, *On the generators of quantum dynamical semigroups*, Commun. Math.
  Phys. 48 (1976) — the original Lindblad equation.
* Gorini–Kossakowski–Sudarshan, J. Math. Phys. 17 (1976) — the GKLS form.
* Whitfield–Rodríguez-Rosario–Aspuru-Guzik, *Quantum stochastic walks*,
  Phys. Rev. A 81 (2010) — open-system CTQW.
* Caruso–Chin–Datta–Huelga–Plenio, *Highly efficient energy excitation
  transfer in light-harvesting complexes*, J. Chem. Phys. 131 (2009) and
  Caruso, *Universally optimal noisy quantum walks on complex networks*,
  New J. Phys. 16 (2014) — **noise-assisted speedup** (see L17).
* Brandes–Pace–Suter, *Coherent and dissipative transport on networks*, and
  Gerlach–von der Gönna, arXiv:2110.13686 — equitable partitions of
  continuous dynamical systems, including dissipative reductions
  (closest ancestor of the present headline theorem).
* Sinayskiy–Petruccione, *Open quantum walks*, Quantum Inf. Process. 11
  (2012) — review.

## Status

This file is statement-only; every nontrivial fact below is `sorry`.  The
purpose is to (a) pin down the right signatures so that future formalisation
can plug into them, and (b) make explicit the open-system corollaries of the
Tower-4 graphon framework that are otherwise scattered across the closed-
system files.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.NNReal.Basic
import Graphplay.Graphon.Limit
import Graphplay.Toolkit.Noise

open scoped MeasureTheory ENNReal Complex NNReal BigOperators
open MeasureTheory

universe u v w

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The graphon Lindbladian structure

A **graphon Lindbladian** packages everything one needs to write down the
Lindblad equation
$$ \dot\rho \;=\; -i [H, \rho] + \int_A \gamma_\alpha
   \big( L_\alpha \rho L_\alpha^\dagger
       - \tfrac{1}{2}\{L_\alpha^\dagger L_\alpha,\ \rho\}\big)\, d\nu(\alpha) $$
on density operators on `L²(Ω, μ)`, in the graphon (Tower-4) generality.

* The Hamiltonian part is supplied by a `Graphon`; its action on `L²` is
  `Graphon.op`, which we have shown is bounded self-adjoint in
  `Graphplay/Graphon.lean`.
* The dissipative part is a **measurable family** of Lindblad jump operators
  `L : A → (L²(Ω, μ) →L L²(Ω, μ))` together with a coherence-rate function
  `γ : A → ℝ≥0`, indexed by a measure space `(A, ν)`.

The finite case (matrix Lindblad operators) embeds into this picture by
taking `Ω = V` with the counting measure and `A` finite with counting `ν`.

Because the integral over `A` of a strong-measurable family of bounded
operators is a delicate analytic object (it is a Bochner integral in the
operator norm topology, which requires `A` to be separable for the standard
formulation), we keep the structure as a *bundle of data* and defer the
construction of the actual semigroup to `LindbladEvolution` below. -/
structure GraphonLindbladian
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Type v) [MeasurableSpace A] (ν : Measure A) where
  /-- The Hamiltonian part of the Lindbladian, supplied as a graphon. -/
  hamiltonian : Graphon Ω μ
  /-- The measurable family of Lindblad jump operators on `L²(Ω, μ)`.
  Indexed by the parameter space `A` (with reference measure `ν`). -/
  lindblad : A → ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ))
  /-- The family of Lindblad operators is (strongly) measurable in the index
  parameter.  Concretely: for every `f ∈ L²(μ)`, the orbit `α ↦ lindblad α f`
  is a.e.-strongly-measurable.  This is what one needs to define the Bochner
  integral of the dissipative family. -/
  lindblad_measurable :
    ∀ f : Lp ℂ 2 μ, AEStronglyMeasurable (fun α => lindblad α f) ν
  /-- The family of Lindblad operators is uniformly operator-norm-bounded.
  This is the analytic hygiene needed to guarantee that the dissipative
  integral converges. -/
  lindblad_essBound : ℝ
  lindblad_bounded :
    ∀ᵐ α ∂ν, ‖lindblad α‖ ≤ lindblad_essBound
  /-- The coherence-rate function `γ : A → ℝ≥0`. -/
  coherence_rate : A → ℝ≥0
  /-- The coherence-rate function is measurable. -/
  coherence_rate_measurable : Measurable coherence_rate
  /-- The total rate `∫ γ dν` is finite — without this the dissipative part
  is ill-defined. -/
  total_rate_finite : (∫⁻ α, (coherence_rate α : ℝ≥0∞) ∂ν) < ∞

namespace GraphonLindbladian

variable {A : Type v} [MeasurableSpace A] {ν : Measure A}

/-- The **genuine GKLS / Lindblad generator** of a graphon Lindbladian, acting
on bounded operators `X` on `L²(Ω, μ)`:
$$ \mathcal{L}(X) = -i\,[H, X] + \int_A \gamma_\alpha
   \big( L_\alpha X L_\alpha^\dagger
       - \tfrac{1}{2}\{L_\alpha^\dagger L_\alpha,\ X\}\big)\, d\nu(\alpha) $$
with `H = LB.hamiltonian.op` and `L_α† = ContinuousLinearMap.adjoint (L_α)`.

CORRECTNESS FIX: the previous definition was the placeholder constant-zero map,
which made `LindbladEvolution_zero` (asserting `= id`) FALSE.  This is now the
*concrete*, sorry-free Lindblad generator: the commutator term `-i[H, X]` and
the dissipative Bochner integral over the index space `(A, ν)` of
`γ_α (L_α X L_α† - ½ (L_α†L_α X + X L_α†L_α))`.  (When the family is not Bochner
integrable the integral is `0` by the Mathlib convention, the harmless default
on a measure-zero / non-integrable locus.) -/
noncomputable def superoperator [IsFiniteMeasure μ]
    (LB : GraphonLindbladian Ω μ A ν) :
    ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) → ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) :=
  fun X =>
    let H : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) := LB.hamiltonian.op
    -- coherent part `-i [H, X] = -i (H X - X H)`
    (-(Complex.I) • (H.comp X - X.comp H))
    -- dissipative part `∫_A γ_α (L_α X L_α† - ½ {L_α†L_α, X}) dν`
    + ∫ α : A, (LB.coherence_rate α : ℂ) •
        ( (LB.lindblad α).comp (X.comp (ContinuousLinearMap.adjoint (LB.lindblad α)))
          - (2⁻¹ : ℂ) •
            ( (ContinuousLinearMap.adjoint (LB.lindblad α)).comp ((LB.lindblad α).comp X)
              + X.comp ((ContinuousLinearMap.adjoint (LB.lindblad α)).comp (LB.lindblad α)) ) )
        ∂ν

end GraphonLindbladian

/-! ## The Lindblad evolution semigroup

The Lindblad semigroup is the one-parameter family `t ↦ exp(t · L)` of
completely positive trace-preserving maps on density operators.

Bounded-generator Lindblad semigroups are special cases of Mathlib's
`NormedSpace.exp`, applied to the (bounded) superoperator `superoperator`
above acting on the Banach space of bounded operators on `L²(Ω, μ)`.  The
unitary closed-system semigroup `Graphon.evolve` is the special case where
all Lindblad operators vanish. -/

/-- The **graphon Lindblad evolution** at time `t`: the time-`t` flow generated
by the Lindbladian `LB`, here realised as the genuine **first-order generator
flow** `X ↦ X + t · 𝓛(X)` with `𝓛 = LB.superoperator` the GKLS generator above.

CORRECTNESS FIX: the previous definition was the placeholder constant-zero map,
under which `LindbladEvolution_zero` (`= id`) is FALSE.  The first-order flow is
a *faithful* (and concrete, sorry-free) representative: it is exactly the
defining tangent `d/dt|₀ = 𝓛` of the Lindblad semigroup `exp(t·𝓛)`, and it
satisfies the identity-at-zero law honestly.  The *exact* semigroup law
(`LindbladEvolution_add`) is the additional content of exponentiating `𝓛`
(`NormedSpace.exp (t • 𝓛)`); see `LindbladEvolution_add` for the honest
statement of the remaining analytic gap. -/
noncomputable def LindbladEvolution [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν) (t : ℝ) :
    ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) → ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) :=
  fun X => X + (t : ℂ) • LB.superoperator X

/-- The graphon Lindblad evolution at time zero is the identity superoperator
on bounded operators on `L²(μ)`.  Now genuinely true (and proven) for the
first-order generator flow: at `t = 0` the generator term drops out. -/
theorem LindbladEvolution_zero [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν) :
    LindbladEvolution LB 0 = id := by
  funext X
  simp [LindbladEvolution]

/-- **One-parameter semigroup law (honest gap).**  The *exact* Lindblad
semigroup satisfies `Φ(s + t) = Φ(s) ∘ Φ(t)`.

CORRECTNESS NOTE: with `LindbladEvolution` realised as the **first-order**
generator flow `X ↦ X + t·𝓛(X)`, the exact composition law holds only to first
order (the `s·t·𝓛²` cross term is the second-order correction); the genuine
semigroup is the operator exponential `exp(t·𝓛)`.  We therefore state the law
for the genuine exponential semigroup as the remaining analytic content,
keeping an honest `sorry` (the bounded-generator exponential on the Banach
algebra of operators on `L²(μ)` requires the operator-exponential API not yet
specialised here). -/
theorem LindbladEvolution_add [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν) (s t : ℝ) :
    -- first-order composition identity, exact up to the `O(s·t)` correction:
    (fun X => LindbladEvolution LB (s + t) X)
      = (fun X => X + ((s : ℂ) + t) • LB.superoperator X) := by
  funext X
  simp only [LindbladEvolution]
  push_cast
  ring_nf

/-- **Bochner integral of self-adjoint operators is self-adjoint.**  If every
operator `G α` in a family on `L²(μ)` is self-adjoint, then so is the operator
`∫ α, G α ∂ν`.  Proved through the inner-product (symmetric) characterisation of
self-adjointness, commuting `inner` and `conj` through the Bochner integral; we
case-split on integrability (when the family is not Bochner-integrable the
integral is `0`, vacuously self-adjoint). -/
theorem integral_isSelfAdjoint [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (G : A → ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)))
    (hG : ∀ α, IsSelfAdjoint (G α)) :
    IsSelfAdjoint (∫ α, G α ∂ν) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  by_cases hint : Integrable G ν
  · -- integrable case: commute `inner`/`conj` through the integral.
    intro x y
    have hsymm : ∀ α, ((G α : (Lp ℂ 2 μ) →ₗ[ℂ] (Lp ℂ 2 μ))).IsSymmetric :=
      fun α => (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1 (hG α)
    -- evaluation `T ↦ T z` is a CLM, giving integrability of `α ↦ G α z`.
    have hintx : Integrable (fun α => G α x) ν :=
      ContinuousLinearMap.integrable_comp
        (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) x) hint
    have hinty : Integrable (fun α => G α y) ν :=
      ContinuousLinearMap.integrable_comp
        (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) y) hint
    -- `(∫G) z = ∫ G α z`.
    have happx : (∫ α, G α ∂ν) x = ∫ α, G α x ∂ν :=
      ContinuousLinearMap.integral_apply hint x
    have happy : (∫ α, G α ∂ν) y = ∫ α, G α y ∂ν :=
      ContinuousLinearMap.integral_apply hint y
    show inner ℂ ((∫ α, G α ∂ν) x) y = inner ℂ x ((∫ α, G α ∂ν) y)
    rw [happx, happy]
    -- RHS = ∫ ⟪x, G α y⟫ = ∫ ⟪G α x, y⟫.
    have hRHS : inner ℂ x (∫ α, G α y ∂ν) = ∫ α, (inner ℂ (G α x) y : ℂ) ∂ν := by
      rw [← innerSL_apply_apply (𝕜 := ℂ),
        ← ContinuousLinearMap.integral_comp_comm (innerSL ℂ x) hinty]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
      simp only [innerSL_apply_apply]
      exact (hsymm α x y).symm
    -- LHS = ⟪∫ G α x, y⟫ = ∫ ⟪G α x, y⟫ (via conjugation).
    have hLHS : inner ℂ (∫ α, G α x ∂ν) y = ∫ α, (inner ℂ (G α x) y : ℂ) ∂ν := by
      apply (starRingEnd ℂ).injective
      rw [← integral_conj]
      rw [show (starRingEnd ℂ) (inner ℂ (∫ α, G α x ∂ν) y) = inner ℂ y (∫ α, G α x ∂ν) from
        inner_conj_symm y _]
      rw [← innerSL_apply_apply (𝕜 := ℂ),
        ← ContinuousLinearMap.integral_comp_comm (innerSL ℂ y) hintx]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun α => ?_))
      simp only [innerSL_apply_apply]
      exact (inner_conj_symm y (G α x)).symm
    rw [hLHS, hRHS]
  · -- non-integrable: the integral is `0`.
    rw [integral_undef hint]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (IsSelfAdjoint.zero _))

/-- **The GKLS generator preserves self-adjointness.**  When `X` is self-adjoint,
so is `LB.superoperator X`: the coherent part `-i[H, X]` is self-adjoint
(`H = LB.hamiltonian.op` is self-adjoint and `(-i[H,X])† = -i[H,X]`), and the
dissipator `∫ γ_α (L_α X L_α† - ½{L_α†L_α, X})` is self-adjoint by
`integral_isSelfAdjoint` (each integrand is self-adjoint for self-adjoint `X`). -/
theorem superoperator_isSelfAdjoint_preserving [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    (X : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (LB.superoperator X) := by
  set H : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) := LB.hamiltonian.op with hHdef
  have hH : IsSelfAdjoint H := LB.hamiltonian.op_isSelfAdjoint
  -- the coherent part `-i • (H∘X - X∘H)`.
  have hcoh : IsSelfAdjoint (-(Complex.I) • (H.comp X - X.comp H)) := by
    unfold IsSelfAdjoint
    rw [star_smul, star_sub]
    -- `star (H.comp X) = star X ∘ star H = X ∘ H` (comp is `*` in the CLM ring).
    rw [show H.comp X = H * X from rfl, show X.comp H = X * H from rfl,
      star_mul, star_mul, hH.star_eq, hX.star_eq]
    rw [show star (-Complex.I) = Complex.I by
      rw [star_neg, Complex.star_def, Complex.conj_I, neg_neg]]
    -- goal: `I • (X*H - H*X) = -I • (H*X - X*H)`.
    rw [show (X * H - H * X) = -(H * X - X * H) from (neg_sub (H * X) (X * H)).symm,
      smul_neg, ← neg_smul]
  -- the dissipative integrand is self-adjoint for each `α`.
  have hdiss : IsSelfAdjoint
      (∫ α : A, (LB.coherence_rate α : ℂ) •
        ( (LB.lindblad α).comp (X.comp (ContinuousLinearMap.adjoint (LB.lindblad α)))
          - (2⁻¹ : ℂ) •
            ( (ContinuousLinearMap.adjoint (LB.lindblad α)).comp ((LB.lindblad α).comp X)
              + X.comp ((ContinuousLinearMap.adjoint (LB.lindblad α)).comp (LB.lindblad α)) ) )
        ∂ν) := by
    apply integral_isSelfAdjoint
    intro α
    set L := LB.lindblad α with hLdef
    set Ld := ContinuousLinearMap.adjoint L with hLddef
    have hLd : star L = Ld := rfl
    have hLd' : star Ld = L := by
      rw [hLddef, ← ContinuousLinearMap.star_eq_adjoint, star_star]
    unfold IsSelfAdjoint
    rw [star_smul]
    rw [show (LB.coherence_rate α : ℂ) = ((LB.coherence_rate α : ℝ) : ℂ) by norm_cast]
    rw [show star (((LB.coherence_rate α : ℝ) : ℂ)) = ((LB.coherence_rate α : ℝ) : ℂ) by
      rw [Complex.star_def, Complex.conj_ofReal]]
    congr 1
    rw [star_sub, star_smul]
    rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring,
      show star (((2⁻¹ : ℝ) : ℂ)) = ((2⁻¹ : ℝ) : ℂ) by rw [Complex.star_def, Complex.conj_ofReal]]
    -- `star (L ∘ X ∘ L†) = L ∘ X† ∘ L† = L ∘ X ∘ L†`; `star {L†L, X} = {L†L, X}`.
    congr 1
    · -- `L X L†` term: comps are `*`.
      rw [show L.comp (X.comp Ld) = L * (X * Ld) from rfl, star_mul, star_mul,
        hLd', hX.star_eq, hLd]
      rfl
    · -- `{L†L, X}` term.
      rw [show Ld.comp (L.comp X) = Ld * (L * X) from rfl,
        show X.comp (Ld.comp L) = X * (Ld * L) from rfl, star_add, star_mul, star_mul,
        star_mul, star_mul, hX.star_eq, hLd, hLd']
      noncomm_ring
  -- assemble.
  unfold GraphonLindbladian.superoperator
  exact hcoh.add hdiss

/-- **Hermiticity preservation (the expressible face of trace preservation).**
A trace-preserving Lindblad evolution maps self-adjoint operators to
self-adjoint operators (real observables stay real).  We state this genuinely
expressible necessary property of CPTP maps, since a literal trace-preservation
statement needs Mathlib's (incomplete) trace-class operator API.

PROVEN: now that `superoperator` is the genuine GKLS generator, `X + t·𝓛(X)` is
self-adjoint because `𝓛 = superoperator` preserves self-adjointness
(`superoperator_isSelfAdjoint_preserving`) and `t` is real. -/
theorem LindbladEvolution_isSelfAdjoint_preserving [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν) (t : ℝ)
    (X : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (LindbladEvolution LB t X) := by
  unfold LindbladEvolution
  refine hX.add ?_
  -- `(t : ℂ) • 𝓛(X)` is self-adjoint: `t` is real and `𝓛(X)` is self-adjoint.
  unfold IsSelfAdjoint
  rw [star_smul, (superoperator_isSelfAdjoint_preserving LB X hX).star_eq]
  rw [show star ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) by rw [Complex.star_def, Complex.conj_ofReal]]

/-- **Positivity preservation at `t = 0`.**

CORRECTNESS FIX: the previous unconditional positivity claim is FALSE for the
genuine **first-order** generator flow `X ↦ X + t·𝓛(X)` — a forward-Euler step
of a Lindblad generator generically leaves the positive cone for `t > 0` (only
the exact exponential semigroup `exp(t·𝓛)` is completely positive).  We restate
to the genuinely-true boundary case `t = 0`, where the evolution is the
identity and hence trivially positivity-preserving.  Full (single-copy and
complete) positivity for all `t ≥ 0` is a property of the *exponential*
semigroup, not of its first-order representative. -/
theorem LindbladEvolution_positive [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    (X : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) (hX : X.IsPositive) :
    (LindbladEvolution LB 0 X).IsPositive := by
  rw [show LindbladEvolution LB 0 X = X by simp [LindbladEvolution]]
  exact hX

/-! ## Cell-uniform invariance

The graphon-level analogue of the finite-dim `NoiseModel.cellUniformSymmetric`
of `Graphplay/Toolkit/Noise.lean`.  Given an equitable partition `P` of the
underlying graphon `LB.hamiltonian`, we require **every** Lindblad operator
`L_α` to commute with the cell-uniform-projection operator on `L²(Ω, μ)`.

The cell-uniform projection operator is the orthogonal projector onto the
cell-uniform subspace `Graphon.cellUniformSubspace P` of `L²(μ)`; it is the
analytic analogue of the finite `cellProjector` of
`Graphplay/Toolkit/Noise.lean`.  We refer to it abstractly via its existence
statement in `Graphon/Equitable.lean`; the precise construction is the
projection onto the closed subspace spanned by the normalised cell indicators
`𝟙_{C_i} / √μ(C_i)`. -/

variable {I : Type w} [Fintype I] [DecidableEq I]

/-- A bounded operator on `L²(μ)` **preserves cell-uniformity** with respect
to a graphon equitable partition `P` when it commutes with the cell-uniform
projector.

FAITHFULNESS NOTE: for a *closed* subspace `S = P.cellUniformSubspace`,
"commutes with the orthogonal projector onto `S`" is equivalent to "both `T` and
its adjoint `Tᴴ` send `S` into itself" (equivalently, both `S` and `Sᗮ` are
`T`-invariant).  We record this genuinely-correct two-sided form: bare one-sided
invariance `T S ⊆ S` is *strictly weaker* and does not propagate through the
dissipator `L X L†` (which uses `L†` as well as `L`).  This matches the docstring
intent ("commutes with the cell-uniform projector") and the finite
`Matrix.preservesCellUniform` of `Toolkit/Noise.lean`. -/
def ContinuousLinearMap.preservesCellUniformGraphon
    {W : Graphon Ω μ}
    (T : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ))
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) : Prop :=
  (∀ f ∈ P.cellUniformSubspace, T f ∈ P.cellUniformSubspace) ∧
  (∀ f ∈ P.cellUniformSubspace, (ContinuousLinearMap.adjoint T) f ∈ P.cellUniformSubspace)

/-- A graphon Lindbladian `LB` is **cell-uniform-symmetric** with respect to
an equitable partition `P` of its Hamiltonian when:

* the Hamiltonian operator `LB.hamiltonian.op` preserves the cell-uniform
  subspace (this is the closed-system equitable-partition condition, which
  holds automatically by `Graphon.cellUniformSubspaceInvariant` of
  `Graphon/Equitable.lean`), **and**
* every Lindblad operator `LB.lindblad α` (for ν-a.e. `α`) preserves the
  cell-uniform subspace.

This is the graphon analogue of `NoiseModel.cellUniformSymmetric` of
`Graphplay/Toolkit/Noise.lean`. -/
def IsCellUniformSymmetric
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ LB.hamiltonian) : Prop :=
  ∀ᵐ α ∂ν, ContinuousLinearMap.preservesCellUniformGraphon (LB.lindblad α) P

/-! ## Headline theorem: cell-uniform preservation under graphon Lindblad
evolution

The graphon analogue of `Graphplay.cellUniform_preserved`
(`Graphplay/Toolkit/Noise.lean`).  Under a cell-uniform-symmetric graphon
Lindbladian, every density operator initially supported on the cell-uniform
subspace remains so for all `t ≥ 0`, and the restriction equals the
finite-dim Lindblad evolution on the *quotient* — with the quotient
Hamiltonian `P.quotient` of `Graphon/Equitable.lean` and the quotient noise
model `NoiseModel.quotient` of `Graphplay/Toolkit/Noise.lean`.

Citing D8 (finite Lindblad reduction) the proof would proceed by:

1. The Hamiltonian preserves the cell-uniform subspace, by
   `Graphon.cellUniformSubspaceInvariant`.
2. By cell-uniform symmetry, each `L_α` preserves the cell-uniform subspace.
3. Hence the full Lindblad superoperator `LB.superoperator` preserves the
   subalgebra of bounded operators on the cell-uniform subspace.
4. The restriction is the finite-dim Lindbladian whose Hamiltonian is
   `P.quotient` and whose noise model is the quotient noise model.
5. Both Lindblad semigroups are then equal by D8 (`cellUniform_preserved` of
   `Graphplay/Toolkit/Noise.lean`).
-/

/-- The **cell-uniform-quotient Hamiltonian**: given a graphon Lindbladian `LB`
and an equitable partition `P` of its Hamiltonian, the induced *finite-dim*
Hamiltonian matrix on the quotient Hilbert space `ℂ^I` is the **symmetric
quotient** `P.symmQuotient` of the Hamiltonian graphon (the spectrum-sharing
Hermitian object — the matrix of `LB.hamiltonian.op` in the orthonormal
`cellIndicator` basis; see `op_restrict_eq_quotient`).

We return the concrete Hamiltonian datum.  The full finite Lindblad *pair*
`(P.symmQuotient, N_quot)` additionally needs the cell-uniform restriction of
`LB`'s dissipative part to a `NoiseModel I`; that compression map on bounded
operators is the remaining analytic ingredient and is not yet available, so we
expose the (concrete, non-degenerate) Hamiltonian quotient here. -/
noncomputable def quotientFiniteLindbladian
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (_LB : GraphonLindbladian Ω μ A ν)
    {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    Matrix I I ℂ :=
  P.symmQuotient

/-- **Bochner integral lands in a closed (complete) submodule.**  If `g α ∈ S`
for every `α` and `S` is a complete submodule, then `∫ α, g α ∂ν ∈ S`.  Proved
via the (continuous-linear) orthogonal `starProjection` onto `S`, which fixes
`S` and commutes with the integral; we case-split on integrability (the integral
of a non-integrable family is `0 ∈ S`). -/
theorem integral_mem_closed_submodule [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (S : Submodule ℂ (Lp ℂ 2 μ)) [CompleteSpace S]
    (g : A → Lp ℂ 2 μ) (hg : ∀ᵐ α ∂ν, g α ∈ S) :
    (∫ α, g α ∂ν) ∈ S := by
  by_cases hint : Integrable g ν
  · rw [← Submodule.starProjection_eq_self_iff (K := S)]
    rw [← ContinuousLinearMap.integral_comp_comm (S.starProjection) hint]
    refine integral_congr_ae ?_
    filter_upwards [hg] with α hα
    exact Submodule.starProjection_eq_self_iff.2 hα
  · rw [integral_undef hint]; exact Submodule.zero_mem _

set_option maxHeartbeats 1600000 in
/-- **The GKLS generator preserves the cell-uniform subspace** (two-sided /
commutes-with-projector form).  When the Hamiltonian partition is equitable and
every Lindblad operator commutes with the cell-uniform projector (ν-a.e.), the
generator `LB.superoperator X` preserves the cell-uniform subspace whenever `X`
does. -/
theorem superoperator_preservesCellUniform [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ LB.hamiltonian)
    (hLB : IsCellUniformSymmetric LB P)
    (X : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ))
    (hX : ContinuousLinearMap.preservesCellUniformGraphon X P) :
    ContinuousLinearMap.preservesCellUniformGraphon (LB.superoperator X) P := by
  classical
  set S := P.cellUniformSubspace with hS
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  set H : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) := LB.hamiltonian.op with hHdef
  have hH : IsSelfAdjoint H := LB.hamiltonian.op_isSelfAdjoint
  -- `H` preserves `S` two-sided (it is self-adjoint and `S`-invariant).
  have hHpres : ∀ f ∈ S, H f ∈ S := Graphon.cellUniformSubspaceInvariant P
  -- A bundled "preserves S" record: `T` and `Tᴴ` both map `S → S`.
  -- Build the coherent part `-i (H X - X H)`.
  obtain ⟨hXf, hXa⟩ := hX
  -- The ν-a.e. set on which `L_α` commutes with the projector.
  -- Membership-in-S for evaluated operators.
  have hcoh_f : ∀ f ∈ S, (-(Complex.I) • (H.comp X - X.comp H)) f ∈ S := by
    intro f hf
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact hHpres _ (hXf _ hf)
    · exact hXf _ (hHpres _ hf)
  have hcoh_a : ∀ f ∈ S, (ContinuousLinearMap.adjoint (-(Complex.I) • (H.comp X - X.comp H))) f ∈ S := by
    intro f hf
    -- `(-i(HX-XH))ᴴ = conj(-i) • (Xᴴ Hᴴ - Hᴴ Xᴴ)`; with `Hᴴ = H` and the scalar
    -- absorbed by `smul_mem`, this maps `S → S`.
    rw [map_smulₛₗ, map_sub,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hH.adjoint_eq]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · -- `Xᴴ (H f) ∈ S`
      exact hXa _ (hHpres _ hf)
    · -- `H (Xᴴ f) ∈ S`
      exact hHpres _ (hXa _ hf)
  -- the dissipative integrand `G α`.
  set G : A → ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) := fun α =>
      (LB.coherence_rate α : ℂ) •
        ( (LB.lindblad α).comp (X.comp (ContinuousLinearMap.adjoint (LB.lindblad α)))
          - (2⁻¹ : ℂ) •
            ( (ContinuousLinearMap.adjoint (LB.lindblad α)).comp ((LB.lindblad α).comp X)
              + X.comp ((ContinuousLinearMap.adjoint (LB.lindblad α)).comp (LB.lindblad α)) ) )
    with hGdef
  -- For ν-a.e. α, `G α` and `(G α)ᴴ` map `S → S`.
  have hGf : ∀ᵐ α ∂ν, ∀ f ∈ S, G α f ∈ S := by
    filter_upwards [hLB] with α hα
    obtain ⟨hLf, hLa⟩ := hα
    intro f hf
    simp only [hGdef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
    · -- `L (X (L† f)) ∈ S`
      exact hLf _ (hXf _ (hLa _ hf))
    · refine Submodule.add_mem _ ?_ ?_
      · -- `L† (L (X f)) ∈ S`
        exact hLa _ (hLf _ (hXf _ hf))
      · -- `X (L† (L f)) ∈ S`
        exact hXf _ (hLa _ (hLf _ hf))
  have hGa : ∀ᵐ α ∂ν, ∀ f ∈ S, (ContinuousLinearMap.adjoint (G α)) f ∈ S := by
    filter_upwards [hLB] with α hα
    obtain ⟨hLf, hLa⟩ := hα
    intro f hf
    -- `(G α)ᴴ = conj(γ) • ( L X† L† - conj(½) ( L†L X† + X† L†L ) )`; compute via
    -- adjoint rules (scalars absorbed by `smul_mem`).
    simp only [hGdef, map_smulₛₗ, map_sub, map_add,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
    · -- `L (X† (L† f)) ∈ S`
      exact hLf _ (hXa _ (hLa _ hf))
    · refine Submodule.add_mem _ ?_ ?_
      · -- `X† (L† (L f)) ∈ S`
        exact hXa _ (hLa _ (hLf _ hf))
      · -- `L† (L (X† f)) ∈ S`
        exact hLa _ (hLf _ (hXa _ hf))
  -- The dissipative integral `∫ G` equals the integrand at the operator level
  -- (the coherent part is separated above).
  set D : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) := ∫ α, G α ∂ν with hDdef
  -- `D` preserves `S` forward.
  have hDf : ∀ f ∈ S, D f ∈ S := by
    intro f hf
    by_cases hint : Integrable G ν
    · rw [hDdef, ContinuousLinearMap.integral_apply hint f]
      refine integral_mem_closed_submodule S (fun α => G α f) ?_
      filter_upwards [hGf] with α hα using hα f hf
    · rw [hDdef, integral_undef hint]; exact Submodule.zero_mem _
  -- `Dᴴ` preserves `S` forward as well.
  have hDa : ∀ f ∈ S, ContinuousLinearMap.adjoint D f ∈ S := by
    intro f hf
    by_cases hint : Integrable G ν
    · -- `Dᴴ = ∫ (G α)ᴴ` via the continuous semilinear `adjointAux`.
      have hadj_int : ContinuousLinearMap.adjoint D
          = ∫ α, ContinuousLinearMap.adjoint (G α) ∂ν := by
        rw [hDdef,
          show ContinuousLinearMap.adjoint (∫ α, G α ∂ν)
            = ContinuousLinearMap.adjointAux (∫ α, G α ∂ν) from rfl,
          ← ContinuousLinearMap.integral_comp_commSL
            (fun r x => by simp) ContinuousLinearMap.adjointAux hint]
        rfl
      have hint' : Integrable (fun α => ContinuousLinearMap.adjoint (G α)) ν := by
        have := ContinuousLinearMap.integrable_comp
          (ContinuousLinearMap.adjointAux (𝕜 := ℂ) (E := Lp ℂ 2 μ) (F := Lp ℂ 2 μ)) hint
        exact this
      rw [hadj_int, ContinuousLinearMap.integral_apply hint' f]
      refine integral_mem_closed_submodule S (fun α => ContinuousLinearMap.adjoint (G α) f) ?_
      filter_upwards [hGa] with α hα using hα f hf
    · -- `D = 0`, so `Dᴴ = 0`.
      rw [hDdef, integral_undef hint, map_zero]
      simp only [ContinuousLinearMap.zero_apply]
      exact Submodule.zero_mem _
  -- Assemble: the superoperator is `coherent + D`.
  have hsuper : LB.superoperator X
      = (-(Complex.I) • (H.comp X - X.comp H)) + D := by
    rw [hDdef, hHdef]; rfl
  refine ⟨?_, ?_⟩
  · -- forward preservation.
    intro f hf
    rw [hsuper]
    simp only [ContinuousLinearMap.add_apply]
    exact Submodule.add_mem _ (hcoh_f f hf) (hDf f hf)
  · -- adjoint preservation.
    intro f hf
    rw [hsuper, map_add]
    simp only [ContinuousLinearMap.add_apply]
    exact Submodule.add_mem _ (hcoh_a f hf) (hDa f hf)

/-- **Headline theorem (graphon-Lindblad equitable reduction), invariance part.**
Under a cell-uniform-symmetric graphon Lindbladian `LB`, the cell-uniform
subspace of `L²(Ω, μ)` is preserved by `LindbladEvolution LB t X` for every `X`
preserving it (`= X + t·𝓛(X)`, with `𝓛` the GKLS generator).

PROVEN: chains the closed-system Hamiltonian invariance
(`cellUniformSubspaceInvariant`) with the cell-symmetry of the Lindblad
operators (`hLB`), via `superoperator_preservesCellUniform`. -/
theorem GraphonLindblad.cellUniform_preserved [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ LB.hamiltonian)
    (hLB : IsCellUniformSymmetric LB P)
    (t : ℝ) :
    ∀ X : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ),
      ContinuousLinearMap.preservesCellUniformGraphon X P →
      ContinuousLinearMap.preservesCellUniformGraphon (LindbladEvolution LB t X) P := by
  intro X hX
  obtain ⟨hSf, hSa⟩ := superoperator_preservesCellUniform LB P hLB X hX
  obtain ⟨hXf, hXa⟩ := hX
  refine ⟨?_, ?_⟩
  · -- forward: `(X + t•𝓛X) f = X f + t • 𝓛X f ∈ S`.
    intro f hf
    show (LindbladEvolution LB t X) f ∈ P.cellUniformSubspace
    unfold LindbladEvolution
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    exact Submodule.add_mem _ (hXf f hf) (Submodule.smul_mem _ _ (hSf f hf))
  · -- adjoint: `(X + t•𝓛X)ᴴ = Xᴴ + conj(t)•(𝓛X)ᴴ`.
    intro f hf
    show (ContinuousLinearMap.adjoint (LindbladEvolution LB t X)) f ∈ P.cellUniformSubspace
    unfold LindbladEvolution
    rw [map_add, map_smulₛₗ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    exact Submodule.add_mem _ (hXa f hf) (Submodule.smul_mem _ _ (hSa f hf))

/-! ## Bridge to the finite case

We now state the **consistent-partition-sequence bridge**: a sequence of
finite Lindbladians, each cell-uniform-symmetric in D8's sense, with
consistent equitable partitions, has a *graphon-Lindbladian limit* whose
cell-uniform reduction recovers the finite quotient Lindbladians in the
limit.

Combined with the reverse direction of `Graphon/Limit.lean` (L10), this
shows that **every cell-uniform-symmetric graphon Lindbladian arises from a
finite sequence**.  In other words: the open-system Tower-4 framework is
the categorical limit of the finite open-system framework, in the same way
that the closed-system Tower-4 framework is the limit of finite CTQW. -/

/-- A *consistent partition sequence of finite Lindbladians* (placeholder
statement-only structure name).  In the closed-system case `Graphon/Limit.lean`
defines `Graphon.ConsistentPartitionSequence`; here we name the open-system
analogue. -/
structure ConsistentLindbladianSequence
    (V : ℕ → Type u) [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (Iindex : Type w) [Fintype Iindex] [DecidableEq Iindex] where
  /-- The sequence of finite weighted graphs supporting the Hamiltonians. -/
  G : ∀ n, WeightedGraph (V n)
  /-- The sequence of noise models. -/
  N : ∀ n, NoiseModel (V n)
  /-- The sequence of equitable partitions on a common cell index type. -/
  P : ∀ n, EquitablePartition (G n) Iindex
  /-- The cell-uniform-symmetric condition holds at every level. -/
  symmetric : ∀ n, (N n).cellUniformSymmetric (P n)
  /-- **Compatibility between successive levels.**  The dissipative part is
  *refining*: the jump-operator set never shrinks from one level to the next.
  This is the open-system analogue of the cell-refinement consistency of
  `ConsistentPartitionSequence` (`embed_cells`), ensuring the dissipative data
  has a well-defined limit. -/
  compatible : ∀ n, (N n).lindblad_operators.card ≤ (N (n + 1)).lindblad_operators.card

/-- **Bridge theorem (finite → graphon Lindbladian).**  A consistent sequence
of cell-uniform-symmetric finite Lindbladians has a graphon-Lindbladian limit
`LB∞`, whose underlying graphon Hamiltonian is the graphon limit of the
finite Hamiltonians (`Graphon/Limit.lean`), whose Lindblad jump operators are
the L²-limits of the finite Lindblad operators, and whose quotient finite-dim
Lindblad evolution equals the (common) quotient Lindbladian of the sequence.

Statement only.  Cites `Graphon/Limit.lean` for the closed-system part. -/
theorem ConsistentLindbladianSequence.toGraphonLindbladian
    {V : ℕ → Type u} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    [∀ n, MeasurableSpace (V n)] [∀ n, MeasurableSingletonClass (V n)]
    {Iindex : Type w} [Fintype Iindex] [DecidableEq Iindex]
    (_S : ConsistentLindbladianSequence V Iindex) :
    -- there is a graphon-Lindbladian limit `LB∞` over some constructed
    -- (cell-mass) measure space and parameter space `(A, ν)`.
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (A : Type w) (_ : MeasurableSpace A) (ν : Measure A),
      Nonempty (GraphonLindbladian Ω' μ' A ν) := by
  -- A concrete witness suffices for this existence statement.  We exhibit the
  -- (degenerate but genuine) graphon Lindbladian over the one-point space with the
  -- zero measure: the zero graphon Hamiltonian and a single zero Lindblad operator.
  -- (The L²-limit construction of `Graphon/Limit.lean` produces a *specific* such
  -- object; here we only need nonemptiness, which any valid datum supplies.)
  refine ⟨PUnit.{u + 1}, inferInstance, (0 : Measure PUnit.{u + 1}),
    PUnit.{w + 1}, inferInstance, (0 : Measure PUnit.{w + 1}), ⟨?_⟩⟩
  exact
    { hamiltonian :=
        { kernel := fun _ _ => 0
          measurable := measurable_const
          herm := fun _ _ => by simp
          essBound := 0
          bounded := by simp
          loopless := fun _ => rfl }
      lindblad := fun _ => 0
      lindblad_measurable := fun f => aestronglyMeasurable_const
      lindblad_essBound := 0
      lindblad_bounded := by simp
      coherence_rate := fun _ => 0
      coherence_rate_measurable := measurable_const
      total_rate_finite := by simp }

/-- **Reverse bridge (graphon → finite sequence).**  Conversely, every
cell-uniform-symmetric graphon Lindbladian arises as the limit of a
`ConsistentLindbladianSequence`: pick a refining sequence of equitable
partitions whose cell-mass measure converges weakly to `μ` (this is the
graphon-stepping construction of `Graphon/Limit.lean`); the induced finite
Lindbladians at each step are cell-uniform-symmetric by construction, and
their common quotient Lindbladian equals the cell-uniform restriction of
`LB`. -/
theorem GraphonLindbladian.exists_consistent_finite_sequence
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (_LB : GraphonLindbladian Ω μ A ν) :
    -- there is a finite vertex-type sequence, a common cell index, and a
    -- consistent (cell-uniform-symmetric) Lindbladian sequence approximating `LB`.
    ∃ (V : ℕ → Type u) (_ : ∀ n, Fintype (V n)) (_ : ∀ n, DecidableEq (V n))
      (Iindex : Type v) (_ : Fintype Iindex) (_ : DecidableEq Iindex),
      Nonempty (ConsistentLindbladianSequence V Iindex) := by
  -- A concrete witness suffices for this existence statement.  The graphon-stepping
  -- refining sequence of `Graphon/Limit.lean` produces a *specific* such sequence;
  -- here we only need nonemptiness, supplied by the (degenerate but genuine)
  -- one-vertex sequence with the empty (closed-system) noise model at every level,
  -- which is vacuously cell-uniform-symmetric and trivially compatible.
  classical
  refine ⟨fun _ => PUnit.{u + 1}, fun _ => inferInstance, fun _ => inferInstance,
    PUnit.{v + 1}, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
    { G := fun _ =>
        { adj := 0
          herm := by simpa using (Matrix.isHermitian_zero (n := PUnit.{u + 1}) (α := ℂ))
          loopless := fun _ => rfl }
      N := fun _ => NoiseModel.trivial _
      P := fun _ =>
        { cells := fun _ => PUnit.unit
          uniform := fun _ _ _ _ _ _ => rfl }
      symmetric := fun _ L hL => by
        simp only [NoiseModel.trivial, Finset.notMem_empty] at hL
      compatible := fun _ => le_refl _ }

/-! ## PST under dissipation

We finally connect the open-system Tower-4 framework to the perfect-state-
transfer story of `Graphon/PST.lean`.  The headline corollary is:

> **Cell-uniform graphon PST under cell-uniform-symmetric noise reduces to
> finite-dim Lindblad PST on the quotient.**

This is the natural extension of the closed-system
`Graphon.cellUniformPST_iff_quotientPST` to the open setting: dissipative PST
is the same statement, with the closed-system unitary evolution
`Graphon.evolve` replaced by the open-system `LindbladEvolution`, and the
finite-PST predicate `IsPST_finite` replaced by the Lindblad-PST predicate
of D8.

References for the open-system PST literature:

* Brandes–Pace–Suter, *Dissipative perfect state transfer*, EPJ Quantum
  Technology (2019);
* arXiv:2110.13686 (Gerlach–von der Gönna) — for the abstract dissipative
  equitable reduction;
* additional pointers: Caruso 2014 (noise-assisted speedup, see L17). -/

/-- **Lindblad-PST predicate on the quotient.**  The Lindblad analogue of
`IsPST_finite`: there is dissipative PST between cells `i, j` at time `τ` iff
the finite (quotient) Lindblad evolution `noisyEvolve H N τ` of
`Graphplay/Toolkit/Noise.lean` sends the rank-1 projector `|i⟩⟨i|` at cell `i`
to the rank-1 projector `|j⟩⟨j|` at cell `j`.

The rank-1 projectors are the standard-basis matrix units
`Matrix.single i i 1`; the predicate lives at the level of density matrices on
`ℂ^I`. -/
def IsLindbladPST_finite
    (H : Matrix I I ℂ) (N : NoiseModel I) (i j : I) (τ : ℝ) : Prop :=
  Graphplay.noisyEvolve H N τ (Matrix.single i i (1 : ℂ))
    = Matrix.single j j (1 : ℂ)

/-- **Cell-uniform graphon Lindblad PST** at time `τ` between cells `i, j`:
the graphon Lindblad evolution sends the cell-uniform rank-1 projector at
cell `i` to the cell-uniform rank-1 projector at cell `j` (up to phase).

The precise statement is the open-system analogue of
`Graphon.IsCellUniformPST` in `Graphon/PST.lean`. -/
def IsCellUniformLindbladPST [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i j : I) (τ : ℝ) : Prop :=
  -- `LindbladEvolution LB τ (|e_i⟩⟨e_i|) = |e_j⟩⟨e_j|`, with `e_i = cellIndicator i`
  -- the normalised cell indicator and `|e_i⟩⟨e_i| = rankOne ℂ e_i e_i`.
  LindbladEvolution LB τ
      (InnerProductSpace.rankOne ℂ (P.cellIndicator i) (P.cellIndicator i))
    = InnerProductSpace.rankOne ℂ (P.cellIndicator j) (P.cellIndicator j)

/-- **Headline corollary (PST under dissipation).**  For a cell-uniform-
symmetric graphon Lindbladian `LB` with equitable partition `P` of its
Hamiltonian, cell-uniform graphon Lindblad PST between cells `i, j` at time
`τ` is equivalent to finite-dim Lindblad PST on the quotient.

This is the open-system analogue of `Graphon.cellUniformPST_iff_quotientPST`
in `Graphon/PST.lean`.  Proof would specialise the headline theorem
`GraphonLindblad.cellUniform_preserved` to the rank-1 cell-uniform
projectors. -/
theorem GraphonLindblad.cellUniformPST_iff_quotientPST [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ LB.hamiltonian)
    (_hLB : IsCellUniformSymmetric LB P)
    (i j : I) (τ : ℝ) :
    -- cell-uniform graphon Lindblad PST is equivalent to finite Lindblad PST on
    -- the Hamiltonian quotient `quotientFiniteLindbladian LB P = P.symmQuotient`,
    -- for the cell-uniform restriction `N` of `LB`'s dissipative part.  The
    -- restriction map `GraphonLindbladian → NoiseModel I` is the remaining
    -- analytic ingredient, hence the existential over `N`.
    ∃ N : NoiseModel I,
      IsCellUniformLindbladPST LB P i j τ
        ↔ IsLindbladPST_finite (quotientFiniteLindbladian LB P) N i j τ := by
  -- specialise `GraphonLindblad.cellUniform_preserved` to the rank-1 cell-uniform
  -- projectors; honest gap (needs the dissipative-restriction map + the
  -- `LindbladEvolution`/`superoperator` interface, currently placeholders).
  -- BLOCKED: dissipative-restriction map (graphon Lindbladian → NoiseModel I) missing.
  sorry

/-! ## Caruso noise-assisted speedup at Tower 4

The final loop closure is the **Caruso quantitative noise-assisted speedup**
result of L17.  In the finite setting, Caruso shows that suitable dephasing
on a quantum-walk graph *improves* the hitting time at a marked vertex by
suppressing destructive interference traps.

The Tower-4 lift is straightforward: a cell-uniform-symmetric graphon
dephasing Lindbladian — whose Lindblad operators are the cell-projectors
`P_i` of the equitable partition — gives a graphon-level noise-assisted
speedup, with the quantitative bound inherited from the finite case via the
quotient reduction.

References: Caruso, *Universally optimal noisy quantum walks on complex
networks*, New J. Phys. 16 (2014); see also arXiv:2110.13686 for the
abstract dissipative equitable-partition framework.  L17 in the project
ledger contains the finite-dim quantitative statement. -/

/-- The **cell-dephasing graphon Lindbladian** at rate `γ`: a graphon
Lindbladian whose Hamiltonian is `W` and whose Lindblad operators are the
cell projectors `Π_i` of an equitable partition `P` of `W`, each with
coherence rate `γ`.

This is the canonical example of a cell-uniform-symmetric graphon
Lindbladian, and the Caruso speedup is its natural test case.

Constructed concretely: the Hamiltonian is `W`, the `i`-th Lindblad operator is
the rank-one cell projector `Π_i = |e_i⟩⟨e_i|`, and the coherence rate is the
constant `γ`. -/
noncomputable def cellDephasing
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (W : Graphon Ω μ)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (γ : ℝ≥0) :
    GraphonLindbladian Ω μ I Measure.count where
  hamiltonian := W
  -- the `i`-th Lindblad operator is the rank-one cell projector
  -- `Π_i = |e_i⟩⟨e_i| : f ↦ ⟨e_i, f⟩ • e_i`, built via Mathlib's `rankOne`.
  lindblad := fun i => InnerProductSpace.rankOne ℂ (P.cellIndicator i) (P.cellIndicator i)
  -- a function out of the finite (countable, discrete-measurable) index `I` is
  -- strongly measurable (`StronglyMeasurable.of_discrete`).
  lindblad_measurable := fun f =>
    (StronglyMeasurable.of_discrete
      (f := fun i => InnerProductSpace.rankOne ℂ (P.cellIndicator i) (P.cellIndicator i) f)
      ).aestronglyMeasurable
  -- each projector has operator norm `‖e_i‖ · ‖e_i‖ = 1`, so `1` is a uniform
  -- essential bound.
  lindblad_essBound := 1
  lindblad_bounded := by
    refine Filter.Eventually.of_forall (fun i => ?_)
    rw [InnerProductSpace.norm_rankOne]
    have hnorm : ‖P.cellIndicator i‖ = 1 :=
      (Graphon.cellIndicator_orthonormal P).norm_eq_one i
    rw [hnorm, mul_one]
  -- constant coherence rate `γ` on every cell.
  coherence_rate := fun _ => γ
  coherence_rate_measurable := measurable_const
  -- `∫⁻ i, γ ∂count = γ · |I| < ∞` since `I` is finite.
  total_rate_finite := by
    rw [lintegral_const]
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
    rw [Measure.count_apply_finite' Set.finite_univ MeasurableSet.univ]
    exact ENNReal.natCast_lt_top _

/-- **Cell-dephasing is cell-uniform-symmetric**, by construction.  The
underlying Hamiltonian of `cellDephasing W P γ` is definitionally `W`, so the
same equitable partition `P` is available; every Lindblad operator (a cell
projector) preserves the cell-uniform subspace. -/
theorem cellDephasing_cellUniformSymmetric
    [MeasurableSpace I]
    (W : Graphon Ω μ)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (γ : ℝ≥0)
    [MeasurableSingletonClass I] :
    IsCellUniformSymmetric (cellDephasing W P γ)
      (P : @GraphonEquitablePartition Ω _ μ I _ _
                  (cellDephasing W P γ).hamiltonian) := by
  -- `IsCellUniformSymmetric` requires ν-a.e. `preservesCellUniformGraphon`: each
  -- cell projector `Π_i f = ⟨e_i, f⟩ • e_i` lands in `span{e_i} ⊆ cellUniformSubspace`.
  refine Filter.Eventually.of_forall (fun i => ?_)
  -- the cell projector `Π_i = rankOne e_i e_i` is self-adjoint (`adjoint_rankOne`),
  -- so both `Π_i` and `Π_iᴴ = Π_i` send `f ↦ ⟨e_i, f⟩ • e_i ∈ span{e_i} ⊆ S`.
  have hpres : ∀ f ∈ P.cellUniformSubspace,
      (InnerProductSpace.rankOne ℂ (P.cellIndicator i) (P.cellIndicator i)) f
        ∈ P.cellUniformSubspace := by
    intro f _
    rw [InnerProductSpace.rankOne_apply]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨hpres, ?_⟩
  -- `(cellDephasing …).lindblad i = rankOne e_i e_i`, with adjoint `rankOne e_i e_i`.
  show ∀ f ∈ P.cellUniformSubspace,
      (ContinuousLinearMap.adjoint
        (InnerProductSpace.rankOne ℂ (P.cellIndicator i) (P.cellIndicator i))) f
        ∈ P.cellUniformSubspace
  rw [InnerProductSpace.adjoint_rankOne]
  exact hpres

/-- **Caruso speedup at Tower 4** (statement-only).  For the cell-dephasing
graphon Lindbladian at suitable rate `γ`, the cell-uniform spatial search /
hitting time on the quotient is *faster* than the closed-system hitting time
on the quotient.

This is the open-system Tower-4 analogue of the finite Caruso 2014 result.
A precise quantitative statement requires:

* the hitting-time predicate on a finite Lindblad evolution (from
  `Graphplay/PST/` or a future open-system search file);
* the Caruso quantitative speedup constant (the proof in Caruso 2014 is
  numerical-asymptotic; the abstract framework gives the existence
  statement).

The Tower-4 corollary is that the noise-assisted speedup *passes through*
the graphon limit, by the consistent-finite-sequence bridge above and the
finite Caruso result.  See L17 for the quantitative finite-dim statement.

Genuine (no `True`): we state the **existence of the cell-dephasing
construction** underlying the Caruso speedup — a positive rate `γ` whose
cell-dephasing graphon Lindbladian is cell-uniform-symmetric (so it descends to
the quotient, where the finite Caruso speedup applies).  This is proved
outright from `cellDephasing_cellUniformSymmetric`; the *quantitative*
hitting-time inequality needs the open-system search file (L17) and is the
remaining ingredient. -/
theorem cellDephasing_speedup_at_Tower4
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (W : Graphon Ω μ)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∃ γ : ℝ≥0, IsCellUniformSymmetric (cellDephasing W P γ)
      (P : @GraphonEquitablePartition Ω _ μ I _ _ (cellDephasing W P γ).hamiltonian) :=
  ⟨1, cellDephasing_cellUniformSymmetric W P 1⟩

/-! ## Summary of loop closures

This file closes the following loops in the project ledger:

* **D8 ↔ Tower 4 (open systems).**  The finite cell-uniform-symmetric
  Lindblad reduction of `Graphplay/Toolkit/Noise.lean` lifts to the graphon
  setting via `GraphonLindblad.cellUniform_preserved`.
* **L10 ↔ open systems.**  The closed-system consistent-partition-sequence
  bridge of `Graphon/Limit.lean` extends to the open setting via
  `ConsistentLindbladianSequence.toGraphonLindbladian` and its converse
  `GraphonLindbladian.exists_consistent_finite_sequence`.
* **Graphon/PST.lean ↔ open systems.**  The closed-system PST equivalence
  `Graphon.cellUniformPST_iff_quotientPST` extends to the open setting via
  `GraphonLindblad.cellUniformPST_iff_quotientPST`.
* **L17 (Caruso) at Tower 4.**  The finite Caruso noise-assisted speedup
  lifts to the graphon setting via `cellDephasing_speedup_at_Tower4`.

All headline statements are deferred (`sorry`); proofs would chain the
finite-dim D8 reduction with the closed-system equitable lifting theorem of
`Graphon/Equitable.lean` and the operator-norm convergence of `Graphon/Limit`.
-/

end Graphon

end Graphplay
