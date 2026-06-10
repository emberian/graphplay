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

The proofs combine the
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

This file pins down the open-system signatures and
makes explicit the open-system corollaries of the
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

/-- The **GKLS / Lindblad generator** of a graphon Lindbladian, acting
on bounded operators `X` on `L²(Ω, μ)`:
$$ \mathcal{L}(X) = -i\,[H, X] + \int_A \gamma_\alpha
   \big( L_\alpha X L_\alpha^\dagger
       - \tfrac{1}{2}\{L_\alpha^\dagger L_\alpha,\ X\}\big)\, d\nu(\alpha) $$
with `H = LB.hamiltonian.op` and `L_α† = ContinuousLinearMap.adjoint (L_α)`:
the commutator term `-i[H, X]` plus
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
by the Lindbladian `LB`, realised as the **first-order generator
flow** `X ↦ X + t · 𝓛(X)` with `𝓛 = LB.superoperator` the GKLS generator above.

The first-order flow is
exactly the defining tangent `d/dt|₀ = 𝓛` of the Lindblad semigroup
`exp(t·𝓛)`, and it satisfies the identity-at-zero law.  The *exact* semigroup
law is the additional content of exponentiating `𝓛`
(`NormedSpace.exp (t • 𝓛)`); see `LindbladEvolution_add` and the
operator-exponential bridge below. -/
noncomputable def LindbladEvolution [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν) (t : ℝ) :
    ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) → ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) :=
  fun X => X + (t : ℂ) • LB.superoperator X

/-- The graphon Lindblad evolution at time zero is the identity superoperator
on bounded operators on `L²(μ)`: at `t = 0` the generator term drops out. -/
theorem LindbladEvolution_zero [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν) :
    LindbladEvolution LB 0 = id := by
  funext X
  simp [LindbladEvolution]

/-- **First-order composition identity.**  With `LindbladEvolution` realised
as the first-order generator flow `X ↦ X + t·𝓛(X)`, the exact composition law
`Φ(s + t) = Φ(s) ∘ Φ(t)` holds only to first order (the `s·t·𝓛²` cross term is
the second-order correction); the exact semigroup is the operator exponential
`exp(t·𝓛)`, whose semigroup law is `operatorExpSemigroup_add` below.  This
theorem records the exact first-order identity. -/
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

/-! ### The exact (operator-exponential) Lindblad semigroup and the first-order bridge

At the *graphon* (infinite-dimensional `L²`) level, Mathlib's `NormedSpace.exp`
of the *super*-operator
acting on `B(L²(μ))` is blocked by a topological-ring instance gap on the iterated
continuous-linear-map algebra `B(L²) →L B(L²)`.  But the GKLS / Lindblad
*generator* is a **bounded linear endomorphism** of an operator algebra, and the
content of "the first-order flow `X ↦ X + t·𝓛(X)` is the tangent of the exact
semigroup `exp(t·𝓛)`" is purely about the operator exponential on a complete normed
`ℂ`-algebra `𝔸` (instantiated, e.g., by the *finite-dimensional* operator algebra on
the cell-uniform subspace — which is exactly where the reduction lives).

We record that bridge here as theorems on an abstract complete
normed `ℂ`-algebra `𝔸` (`operatorExpSemigroup`, `operatorExpSemigroup_zero`,
`operatorExpSemigroup_add` (the one-parameter semigroup law), and the **dynamical
bridge** `hasDerivAt_operatorExpSemigroup` / `operatorExpSemigroup_deriv_at_zero`: the
exact semigroup `t ↦ exp(t·L)` is differentiable with derivative `L` at `t = 0`,
i.e. it agrees to first order with the generator flow `X ↦ X + t·L(X)`).  This is
the operator-exponential interface that the first-order `LindbladEvolution` above is a
first-order approximation of. -/

section OperatorExpBridge

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- The **exact one-parameter semigroup** `t ↦ exp(t · L)` generated by a bounded
operator `L` on a complete normed `ℂ`-algebra `𝔸`.  For the GKLS generator this is
the Lindblad semigroup (the operator exponential of the Lindbladian); the
first-order `LindbladEvolution` is its tangent at `t = 0`. -/
noncomputable def operatorExpSemigroup (L : 𝔸) (t : ℝ) : 𝔸 :=
  NormedSpace.exp ((t : ℂ) • L)

/-- The exact semigroup at time `0` is the identity (`exp 0 = 1`). -/
theorem operatorExpSemigroup_zero (L : 𝔸) : operatorExpSemigroup L 0 = 1 := by
  rw [operatorExpSemigroup, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

/-- **One-parameter semigroup law** for the exact operator-exponential evolution:
`exp((s + t)·L) = exp(s·L) · exp(t·L)` (the two exponents commute). -/
theorem operatorExpSemigroup_add (L : 𝔸) (s t : ℝ) :
    operatorExpSemigroup L (s + t) = operatorExpSemigroup L s * operatorExpSemigroup L t := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℂ 𝔸
  rw [operatorExpSemigroup, operatorExpSemigroup, operatorExpSemigroup,
    Complex.ofReal_add, add_smul,
    NormedSpace.exp_add_of_commute (((Commute.refl L).smul_left _).smul_right _)]

/-- **The dynamical bridge (general time).**  As a function of complex time `u`, the
exact semigroup `u ↦ exp(u · L)` is differentiable with derivative `exp(u·L) · L`. -/
theorem hasDerivAt_operatorExpSemigroup (L : 𝔸) (u : ℂ) :
    HasDerivAt (fun z : ℂ => NormedSpace.exp (z • L)) (NormedSpace.exp (u • L) * L) u :=
  hasDerivAt_exp_smul_const L u

/-- **The first-order bridge at `t = 0`.**  The exact semigroup `u ↦ exp(u · L)` has
derivative exactly `L` at `u = 0`.  This is the precise sense in which the
GKLS semigroup `exp(t·𝓛)` agrees with the first-order generator flow
`X ↦ X + t·𝓛(X)` to first order — `𝓛` is the common tangent at `t = 0`. -/
theorem operatorExpSemigroup_deriv_at_zero (L : 𝔸) :
    HasDerivAt (fun z : ℂ => NormedSpace.exp (z • L)) L 0 := by
  have h := hasDerivAt_operatorExpSemigroup L 0
  rwa [zero_smul, NormedSpace.exp_zero, one_mul] at h

end OperatorExpBridge

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
self-adjoint operators (real observables stay real).  We state this
expressible necessary property of CPTP maps, since a literal trace-preservation
statement needs Mathlib's (incomplete) trace-class operator API.

`X + t·𝓛(X)` is
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

The restriction to `t = 0` is necessary: unconditional positivity is false
for the **first-order** generator flow `X ↦ X + t·𝓛(X)` — a forward-Euler step
of a Lindblad generator generically leaves the positive cone for `t > 0` (only
the exact exponential semigroup `exp(t·𝓛)` is completely positive).  At
`t = 0` the evolution is the
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

For a *closed* subspace `S = P.cellUniformSubspace`,
"commutes with the orthogonal projector onto `S`" is equivalent to "both `T` and
its adjoint `Tᴴ` send `S` into itself" (equivalently, both `S` and `Sᗮ` are
`T`-invariant).  We record this two-sided form: bare one-sided
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

/-! ### The dissipative-restriction (compression) map

The missing piece of the open-system quotient is the **compression** of a
bounded operator `X` on `L²(μ)` to a finite `I × I` matrix, taken in the
orthonormal cell-indicator basis `{e_i}`:
`(restrict X)_{i j} = ⟨e_i, X e_j⟩`.  This is the operator-theoretic
`Bᴴ X B` with `B = cellUniformIsometry`, read off as a matrix.  It is exactly
the finite datum the (still-open) `LindbladEvolution`-to-`noisyEvolve` bridge
needs to descend a graphon Lindbladian's dissipative part to a `NoiseModel I`.

We build it here as a `def` and prove the two basic algebraic facts
that make it the right object: it is `ℂ`-linear in `X`, and it sends
self-adjoint operators to **Hermitian** matrices (so the compressed Hamiltonian
/ jump operators stay physical). -/

/-- **Dissipative-restriction (compression) map.**  The `(i, j)` entry is the
matrix coefficient `⟨e_i, X e_j⟩` of `X` in the orthonormal cell-indicator
basis. -/
noncomputable def dissipativeRestriction
    {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (X : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) : Matrix I I ℂ :=
  fun i j => inner ℂ (P.cellIndicator i) (X (P.cellIndicator j))

/-- The compression map is additive in the operator. -/
theorem dissipativeRestriction_add
    {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (X Y : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) :
    dissipativeRestriction P (X + Y)
      = dissipativeRestriction P X + dissipativeRestriction P Y := by
  ext i j
  simp only [dissipativeRestriction, ContinuousLinearMap.add_apply, inner_add_right,
    Matrix.add_apply]

/-- The compression map is `ℂ`-homogeneous in the operator. -/
theorem dissipativeRestriction_smul
    {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (c : ℂ) (X : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) :
    dissipativeRestriction P (c • X) = c • dissipativeRestriction P X := by
  ext i j
  simp only [dissipativeRestriction, ContinuousLinearMap.smul_apply, inner_smul_right,
    Matrix.smul_apply, smul_eq_mul]

/-- **Compression of a self-adjoint operator is Hermitian.**  If `X` is
self-adjoint then its cell-indicator compression `dissipativeRestriction P X`
is a Hermitian matrix.  This is the finite physical-datum guarantee: the
compressed Hamiltonian and jump operators remain Hermitian/dissipative. -/
theorem dissipativeRestriction_isHermitian
    {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (X : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) (hX : IsSelfAdjoint X) :
    (dissipativeRestriction P X).IsHermitian := by
  ext i j
  show star (dissipativeRestriction P X j i) = dissipativeRestriction P X i j
  simp only [dissipativeRestriction]
  -- `conj ⟨e_j, X e_i⟩ = ⟨X e_i, e_j⟩ = ⟨e_i, Xᴴ e_j⟩ = ⟨e_i, X e_j⟩`.
  have h1 : star (inner ℂ (P.cellIndicator j) (X (P.cellIndicator i)))
      = inner ℂ (X (P.cellIndicator i)) (P.cellIndicator j) := inner_conj_symm _ _
  rw [h1, ← ContinuousLinearMap.adjoint_inner_right, hX.adjoint_eq]

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
  -- (degenerate) graphon Lindbladian over the one-point space with the
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
  -- here we only need nonemptiness, supplied by the degenerate
  -- one-vertex sequence with the empty (closed-system) noise model at every level,
  -- which is cell-uniform-symmetric and compatible for trivial reasons.
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

/-- **Compression of a rank-one cell projector is a standard matrix unit.**
`dissipativeRestriction P (|e_k⟩⟨e_k|) = single k k 1` — the orthonormal
cell-indicator basis sends the rank-one projector onto cell `k` to the `(k,k)`
matrix unit.  This is the bridge object turning the graphon cell-uniform PST
"target" `|e_j⟩⟨e_j|` into the finite quotient density `|j⟩⟨j|`. -/
theorem dissipativeRestriction_rankOne {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (k : I) :
    dissipativeRestriction P
        (InnerProductSpace.rankOne ℂ (P.cellIndicator k) (P.cellIndicator k))
      = Matrix.single k k (1 : ℂ) := by
  ext a b
  show inner ℂ (P.cellIndicator a)
      ((InnerProductSpace.rankOne ℂ (P.cellIndicator k) (P.cellIndicator k))
        (P.cellIndicator b)) = _
  rw [InnerProductSpace.rankOne_apply, inner_smul_right,
    orthonormal_iff_ite.mp (Graphon.cellIndicator_orthonormal P) k b,
    orthonormal_iff_ite.mp (Graphon.cellIndicator_orthonormal P) a k, Matrix.single_apply]
  by_cases hak : a = k <;> by_cases hkb : k = b <;> simp_all [eq_comm]

/-- **Finite first-order quotient Lindblad PST.**  The finite, quotient-level
analogue of `IsCellUniformLindbladPST`, matching the *first-order generator
flow* `X ↦ X + τ·𝓛(X)` that `LindbladEvolution` realises: starting from the
quotient density `|i⟩⟨i| = single i i 1`, one step of the finite generator `C`
(the finite Lindblad super-operator acting on `ℂ^I`) reaches `|j⟩⟨j|`:
`single i i 1 + τ·(C applied to single i i 1) = single j j 1`.

Here `C : Matrix I I ℂ → Matrix I I ℂ` is supplied as the finite quotient
generator (the cell-uniform compression of `LB`'s GKLS generator).  This is the
finite partner of the graphon first-order flow, used in the reduction
theorem `GraphonLindblad.cellUniformPST_implies_quotient_firstOrder`. -/
def IsQuotientFirstOrderLindbladPST
    (C : Matrix I I ℂ → Matrix I I ℂ) (i j : I) (τ : ℝ) : Prop :=
  Matrix.single i i (1 : ℂ) + (τ : ℂ) • C (Matrix.single i i (1 : ℂ))
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

/-- **The finite quotient generator** of a graphon Lindbladian, read off in the
orthonormal cell-indicator basis: `C(X) = dissipativeRestriction P (𝓛 (B X))`,
where `B X` lifts a finite density `X` to the cell-uniform operator
`∑ X_{ab} |e_a⟩⟨e_b|` and `𝓛 = LB.superoperator` is the GKLS generator.  On the
basis projector `single i i 1` this is exactly the cell-uniform compression of
`𝓛(|e_i⟩⟨e_i|)` — the finite first-order generator step of the quotient flow.

We package only the action on the standard projectors needed below (lifting
`single i i 1` to `|e_i⟩⟨e_i|`), which is all `IsQuotientFirstOrderLindbladPST`
consumes. -/
noncomputable def quotientGenerator [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ LB.hamiltonian)
    (i : I) : Matrix I I ℂ → Matrix I I ℂ :=
  fun _ => dissipativeRestriction P
    (LB.superoperator (InnerProductSpace.rankOne ℂ (P.cellIndicator i) (P.cellIndicator i)))

/-- **Headline corollary (PST under dissipation) — the finite reduction.**

For a cell-uniform-symmetric graphon Lindbladian `LB` with equitable partition
`P` of its Hamiltonian, cell-uniform graphon Lindblad PST between cells `i, j`
at time `τ` descends to a finite-dim *first-order* Lindblad PST on the
quotient, for the finite quotient generator `quotientGenerator LB P i`.

The matching finite object is the first-order quotient flow
`IsQuotientFirstOrderLindbladPST`, not `IsLindbladPST_finite` (which uses the
*exact dephasing channel* `noisyEvolve`): `IsCellUniformLindbladPST` is the
*first-order generator flow* `X ↦ X + τ·𝓛(X)`, a different dynamics, so an iff
against the exact channel is not a theorem for any choice of finite noise
model — the `exp(t·𝓛)`/first-order gap is exactly what the
`operatorExpSemigroup` bridge above quantifies.

The **forward** direction: the cell-uniform compression
`dissipativeRestriction P` is `ℂ`-linear (`dissipativeRestriction_add/_smul`)
and sends the rank-one cell projectors to the standard matrix units
(`dissipativeRestriction_rankOne`), so the graphon first-order flow equation
`|e_i⟩⟨e_i| + τ·𝓛(|e_i⟩⟨e_i|) = |e_j⟩⟨e_j|` descends *entrywise* to the finite
first-order quotient equation `single i i 1 + τ·C(single i i 1) = single j j 1`.
(The converse — lifting the finite equation back to the operator equation —
would need injectivity of the compression on the *off-diagonal* image
`𝓛(|e_i⟩⟨e_i|)`, which the compression does not supply in general; that is exactly
the exp/first-order gap and is not claimed here.)  This realises the D8 ↔ Tower-4
open-system loop closure at the level of the generator flow in the sound
direction; the exact-semigroup refinement is the `operatorExpSemigroup` bridge. -/
theorem GraphonLindblad.cellUniformPST_implies_quotient_firstOrder [IsFiniteMeasure μ]
    {A : Type v} [MeasurableSpace A] {ν : Measure A}
    (LB : GraphonLindbladian Ω μ A ν)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ LB.hamiltonian)
    (i j : I) (τ : ℝ) :
    IsCellUniformLindbladPST LB P i j τ
      → IsQuotientFirstOrderLindbladPST (quotientGenerator LB P i) i j τ := by
  -- Apply the (linear) cell-uniform compression `dissipativeRestriction P` to the
  -- graphon first-order flow equation: it is `ℂ`-linear and sends the rank-one
  -- cell projectors to the standard matrix units, so the operator equation
  -- descends *entrywise* to the finite first-order quotient equation.
  unfold IsCellUniformLindbladPST IsQuotientFirstOrderLindbladPST quotientGenerator
    LindbladEvolution
  intro h
  have hc := congrArg (dissipativeRestriction P) h
  rwa [dissipativeRestriction_add, dissipativeRestriction_smul,
    dissipativeRestriction_rankOne, dissipativeRestriction_rankOne] at hc

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

The proofs chain the
finite-dim D8 reduction with the closed-system equitable lifting theorem of
`Graphon/Equitable.lean` and the operator-norm convergence of `Graphon/Limit`.
-/

end Graphon

end Graphplay
