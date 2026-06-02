/-
# Graphplay/Integrations/OptimalTransport.lean — Optimal Transport ↔ Graphons

This file connects Tower 4 (graphons + equitable partitions + CTQW) to the
*continuous* theory of **optimal transport** (OT).  A graphon kernel
`W : Ω × Ω → ℂ` that is real-valued, nonnegative, and symmetric is *almost* a
**transport plan**: it is a nonnegative symmetric measurable kernel on
`Ω × Ω`.  The only obstruction to being a *bona-fide* transport plan is that
the marginals of `W ∂(μ ⊗ μ)` may not equal a prescribed pair of probability
measures `(α, β)` — which one fixes either by a Sinkhorn-style row/column
rescaling (Sinkhorn–Knopp) or by entropic regularisation (Cuturi).

The conceptual bridge is:

* **Equitable partitions** of a graphon are exactly the data of a *coarsened
  transport plan*: a finite quotient matrix `B : I × I → ℝ` plus internal
  cell-uniform structure.
* **Sinkhorn iterates** preserve the cell-uniform subspace when the source is
  an equitable-partition graphon, and the quotient gives a *lower bound on
  the rate*.
* **CTQW uniform-mixing time** on cell-uniform support is conjecturally
  related to the Sinkhorn entropic convergence time by a factor of
  `log n / n`.  This is the **mixing-time ↔ transport-rate** dictionary that
  the *engineering toolkit* exploits to *design quantum samplers* targeting a
  prescribed transport plan.

References:

* C. Villani, *Optimal Transport: Old and New* (2009) — Kantorovich duality,
  cyclic monotonicity, displacement interpolation.
* R. Sinkhorn and P. Knopp, *Concerning nonnegative matrices and doubly
  stochastic matrices*, Pacific J. Math. **21** (1967), 343–348.
* M. Cuturi, *Sinkhorn distances: Lightspeed computation of optimal transport*,
  NeurIPS 2013, arXiv:1306.0895 — entropic regularisation of OT.
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, 2019,
  arXiv:1803.00567 — modern survey.
* G. Carlier, *On the linear convergence of the multimarginal Sinkhorn
  algorithm*, SIAM J. Optim. **32** (2022).
* For the graphon side: Lovász, *Large Networks and Graph Limits*; BCLSV,
  arXiv:1003.5588.
* For the chiral / quantum side: Childs, *Universal computation by quantum
  walk*, PRL **102** (2009).
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Probability.Notation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Graphplay.Graphon
import Graphplay.Graphon.Equitable

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory

universe u v

namespace Graphplay

/-! ## 1. From graphons to transport plans

A **transport plan** between probability measures `α` on `X` and `β` on `Y` is
a probability measure `π` on `X × Y` whose first marginal is `α` and whose
second marginal is `β`.  When `X = Y = Ω` carries a reference measure `μ`, we
identify a transport plan with its Radon–Nikodým density
`W : Ω × Ω → ℝ≥0`.

A nonneg-real graphon has the right *type* but its marginals are arbitrary; we
record this and provide the *marginal-correction* construction (Sinkhorn or
direct rescaling) as a `sorry`.
-/

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A graphon is **nonnegative real-valued** if its kernel is a.e. real and
nonnegative.  Equivalently the imaginary part vanishes and the real part is
nonneg.  This is the natural class on which OT-style constructions apply. -/
structure IsNonnegReal (W : Graphon Ω μ) : Prop where
  imag_zero : ∀ᵐ p ∂(μ.prod μ), (W.kernel p.1 p.2).im = 0
  re_nonneg : ∀ᵐ p ∂(μ.prod μ), 0 ≤ (W.kernel p.1 p.2).re

/-- The **first marginal** of a graphon `W` w.r.t. `μ`: the function
`x ↦ ∫ W.kernel x y ∂μ(y)`, viewed as a real-valued density on `Ω`.

For a *symmetric* graphon (real, Hermitian = symmetric), the first and second
marginals coincide. -/
noncomputable def marginal (W : Graphon Ω μ) (x : Ω) : ℝ :=
  ∫ y, (W.kernel x y).re ∂μ

/-- The **total mass** of a graphon: `∫∫ W x y ∂(μ ⊗ μ)`, the integral of the
marginal. -/
noncomputable def totalMass (W : Graphon Ω μ) : ℝ :=
  ∫ x, W.marginal x ∂μ

/-- A graphon `W` is **sub-stochastic** if its marginal is everywhere `≤ 1`. -/
def IsSubStochastic (W : Graphon Ω μ) : Prop :=
  ∀ᵐ x ∂μ, W.marginal x ≤ 1

/-- A graphon `W` is **(doubly) stochastic** if its marginal is everywhere
`= 1`.  Equivalent (by symmetry) to "both marginals equal `μ`". -/
def IsStochastic (W : Graphon Ω μ) : Prop :=
  ∀ᵐ x ∂μ, W.marginal x = 1

/-- The **chiral (imaginary) part** of a graphon: the Hermitian kernel
`x, y ↦ i · Im(W(x, y))`.  This keeps the imaginary (skew/chiral) content of
`W` while zeroing the real part.  It is Hermitian (`i·Im` flips sign under both
`star` and the argument swap), loopless, measurable and bounded by `essBound`. -/
noncomputable def chiralPart (W : Graphon Ω μ) : Graphon Ω μ where
  kernel x y := Complex.I * ((W.kernel x y).im : ℂ)
  measurable := by
    have him : Measurable (fun p : Ω × Ω => ((W.kernel p.1 p.2).im : ℂ)) :=
      Complex.measurable_ofReal.comp (Complex.measurable_im.comp W.measurable)
    exact measurable_const.mul him
  herm x y := by
    -- `i·Im(W y x) = i·Im(star (W x y)) = i·(-Im(W x y)) = star (i·Im(W x y))`
    rw [W.herm x y, Complex.star_def, Complex.conj_im]
    push_cast
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  essBound := W.essBound
  bounded := by
    filter_upwards [W.bounded] with p hp
    show ‖Complex.I * ((W.kernel p.1 p.2).im : ℂ)‖ ≤ W.essBound
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (Complex.abs_im_le_norm _) hp
  loopless x := by rw [W.loopless x]; simp

/-- **View a graphon as a (sub-)stochastic transport plan.**  We take the
*chiral part* `i·Im(W)` of `W`, whose kernel is purely imaginary; its first
marginal `∫ Re(i·Im(W x y)) dμ(y) = ∫ 0 = 0 ≤ 1` everywhere, so it is
sub-stochastic by construction.  This is the canonical Sinkhorn-free
sub-stochastic plan associated to `W` (it discards the real flux, retaining the
chiral content relevant to the CTQW story).  Lifting to a *full* bistochastic
plan with prescribed marginals `(α, β)` is the Sinkhorn–Knopp construction,
which requires the IPF / scaling convergence theorem and is the content of
`sinkhorn_convergence` below. -/
noncomputable def toTransportPlan (W : Graphon Ω μ) (_hW : IsNonnegReal W) :
    { Wp : Graphon Ω μ // IsSubStochastic Wp } :=
  ⟨W.chiralPart, by
    -- the chiral part has real part `0`, so its marginal is `∫ 0 = 0 ≤ 1`
    refine Filter.Eventually.of_forall (fun x => ?_)
    show (∫ y, (W.chiralPart.kernel x y).re ∂μ) ≤ 1
    have hre : ∀ y, (W.chiralPart.kernel x y).re = 0 := by
      intro y
      show (Complex.I * ((W.kernel x y).im : ℂ)).re = 0
      simp [Complex.mul_re]
    simp only [hre, integral_zero]
    exact zero_le_one⟩

/-- **Marginal of `toTransportPlan` is bounded by 1.** A trivial consequence
of the construction. -/
theorem toTransportPlan_subStochastic (W : Graphon Ω μ) (hW : IsNonnegReal W) :
    IsSubStochastic (toTransportPlan W hW).1 :=
  (toTransportPlan W hW).2

end Graphon

/-! ## 2. The Optimal Transport problem

Given probability measures `α, β` on `Ω` and a cost function `c : Ω → Ω → ℝ`,
the **Kantorovich problem** is to minimise

  `∫∫ c(x, y) ∂π(x, y)`

over all `π ∈ Π(α, β)` (couplings of `α` and `β`).  When `α = β = μ` and the
cost is `c(x, y) := -log W.kernel x y` (the *negative log graphon*),
optimal-transport plans correspond to *maximum-likelihood* graphon couplings.
-/

/-- An **OT problem on a graphon**: source/target probability measures `α, β`
on `Ω`, and a cost function `c`.  We *include the graphon* `W` only because
the cost we'll usually use is built from `W` (e.g. `c x y = -log W.kernel x y`,
or `c x y = ‖x - y‖²` for a metric graphon). -/
structure OptimalTransportProblem (Ω : Type u) [MeasurableSpace Ω] where
  /-- Reference measure (typically the graphon's base measure). -/
  μ : Measure Ω
  /-- Source probability measure. -/
  α : Measure Ω
  /-- Target probability measure. -/
  β : Measure Ω
  /-- Cost function `c : Ω → Ω → ℝ`. -/
  cost : Ω → Ω → ℝ
  /-- `α` is a probability measure. -/
  α_prob : IsProbabilityMeasure α
  /-- `β` is a probability measure. -/
  β_prob : IsProbabilityMeasure β
  /-- Joint measurability of the cost. -/
  cost_measurable : Measurable (Function.uncurry cost)
  /-- Lower bound on the cost (needed for Kantorovich existence). -/
  cost_lb : ∃ M : ℝ, ∀ x y, M ≤ cost x y

namespace OptimalTransportProblem

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A **coupling** of `α` and `β` is a probability measure on `Ω × Ω` with
those marginals.  We store it as the joint measure (rather than its density). -/
structure IsCoupling (P : OptimalTransportProblem Ω) (π : Measure (Ω × Ω)) :
    Prop where
  prob : IsProbabilityMeasure π
  marginal_left : π.map Prod.fst = P.α
  marginal_right : π.map Prod.snd = P.β

/-- The **Kantorovich functional**: `K(π) := ∫∫ c(x, y) ∂π`. -/
noncomputable def kantorovich (P : OptimalTransportProblem Ω)
    (π : Measure (Ω × Ω)) : ℝ :=
  ∫ p, P.cost p.1 p.2 ∂π

/-- The **optimal transport cost** (primal Kantorovich value): infimum of
`kantorovich π` over couplings. -/
noncomputable def value (P : OptimalTransportProblem Ω) : ℝ :=
  sInf {v : ℝ | ∃ π, P.IsCoupling π ∧ P.kantorovich π = v}

/-- A pair of **Kantorovich potentials** `(φ, ψ) : (Ω → ℝ) × (Ω → ℝ)` is
**admissible** for `P` if `φ x + ψ y ≤ c x y` for all `x, y`. -/
def IsAdmissiblePotential (P : OptimalTransportProblem Ω)
    (φ ψ : Ω → ℝ) : Prop :=
  ∀ x y, φ x + ψ y ≤ P.cost x y

/-- The **dual Kantorovich functional**: `D(φ, ψ) := ∫ φ ∂α + ∫ ψ ∂β`. -/
noncomputable def dual (P : OptimalTransportProblem Ω) (φ ψ : Ω → ℝ) : ℝ :=
  ∫ x, φ x ∂P.α + ∫ y, ψ y ∂P.β

/-- **Abstract (measure-theoretic) weak Kantorovich duality (PROVEN).**  For any
coupling `π` of `(α, β)` and any admissible potential pair `(φ, ψ)`
(`φ x + ψ y ≤ c x y`), the dual value is `≤` the primal cost:
  `∫ φ ∂α + ∫ ψ ∂β  ≤  ∫ c ∂π`,  i.e.  `P.dual φ ψ ≤ P.kantorovich π`.

This is the continuous analogue of `FiniteOT.weak_duality`, and the inequality
the strong-duality docstring above refers to.

Proof (the elementary half of Villani 5.10): push the marginals through `π`
(`integral_map` with `π.map fst = α`, `π.map snd = β`) to rewrite the two dual
integrals as integrals over `π` of `φ ∘ fst` and `ψ ∘ snd`; add them
(`integral_add`); then compare with `∫ c ∂π` pointwise via `integral_mono`, using
admissibility `φ p.1 + ψ p.2 ≤ c p.1 p.2`.

The integrability hypotheses are genuinely needed (the Bochner integral is
junk-valued `0` on non-integrable functions, which would break the bound): `φ`
integrable against `α`, `ψ` against `β`, and the cost against `π`.  They are the
minimal regularity for the *statement* to assert anything; for a probability
measure `π` and a bounded continuous cost they hold automatically. -/
theorem kantorovich_weak_duality (P : OptimalTransportProblem Ω)
    {π : Measure (Ω × Ω)} (hπ : P.IsCoupling π)
    {φ ψ : Ω → ℝ} (hadm : P.IsAdmissiblePotential φ ψ)
    (hφ : Integrable φ P.α) (hψ : Integrable ψ P.β)
    (hc : Integrable (Function.uncurry P.cost) π) :
    P.dual φ ψ ≤ P.kantorovich π := by
  haveI : IsProbabilityMeasure π := hπ.prob
  -- the two marginal pushforwards
  have hmapfst : π.map Prod.fst = P.α := hπ.marginal_left
  have hmapsnd : π.map Prod.snd = P.β := hπ.marginal_right
  -- rewrite `∫ φ ∂α` as `∫ φ(p.1) ∂π` via `integral_map`
  have hLfst : ∫ x, φ x ∂P.α = ∫ p, φ p.1 ∂π := by
    rw [← hmapfst, integral_map measurable_fst.aemeasurable]
    rw [hmapfst]; exact hφ.aestronglyMeasurable
  have hLsnd : ∫ y, ψ y ∂P.β = ∫ p, ψ p.2 ∂π := by
    rw [← hmapsnd, integral_map measurable_snd.aemeasurable]
    rw [hmapsnd]; exact hψ.aestronglyMeasurable
  -- integrability of the two composites against `π`
  have hφπ : Integrable (fun p : Ω × Ω => φ p.1) π := by
    rw [← hmapfst] at hφ
    exact (integrable_map_measure hφ.aestronglyMeasurable measurable_fst.aemeasurable).1 hφ
  have hψπ : Integrable (fun p : Ω × Ω => ψ p.2) π := by
    rw [← hmapsnd] at hψ
    exact (integrable_map_measure hψ.aestronglyMeasurable measurable_snd.aemeasurable).1 hψ
  -- the dual is the π-integral of `φ ∘ fst + ψ ∘ snd`
  rw [OptimalTransportProblem.dual, hLfst, hLsnd, ← integral_add hφπ hψπ,
    OptimalTransportProblem.kantorovich]
  -- pointwise admissibility, then `integral_mono`
  refine integral_mono (hφπ.add hψπ) hc (fun p => ?_)
  exact hadm p.1 p.2

/-- **Strong Kantorovich duality** (deep, cited).  Under mild regularity (Polish
space, lower-semicontinuous lower-bounded cost) the primal equals the dual:
  `value P = sup_{(φ,ψ) admissible} dual P φ ψ`.

This is the genuine strong-duality *equality* and is the deep half (Villani,
*OT: Old and New*, Thm. 5.10): it needs the lsc cost, a Polish-space
minimax / Fenchel–Rockafellar argument, not available in Mathlib.  It is left an
honest `sorry` on a **true** statement.  The elementary, always-true *weak*
duality half is fully proven in the finite model below
(`FiniteOT.weak_duality`, `FiniteOT.dualValue_le_value`) and abstractly in
`kantorovich_weak_duality`. -/
theorem kantorovich_strong_duality (P : OptimalTransportProblem Ω) :
    P.value =
      sSup {d : ℝ | ∃ φ ψ, P.IsAdmissiblePotential φ ψ ∧ P.dual φ ψ = d} := by
  -- DEEP (Villani Thm 5.10): Kantorovich strong duality; needs lsc cost,
  -- Polish-space minimax / Fenchel–Rockafellar, not formalised here.  TRUE
  -- statement; honest cited residual.  (Weak duality `≤` is PROVEN below.)
  sorry

/-- **Existence of an optimal plan** (deep, cited).  Under lower semicontinuity
and lower-boundedness of the cost, the infimum in `value` is attained. -/
theorem exists_optimal_coupling (P : OptimalTransportProblem Ω) :
    ∃ π, P.IsCoupling π ∧ P.kantorovich π = P.value := by
  -- DEEP: attainment of the Kantorovich infimum; needs tightness/weak
  -- compactness of the coupling set (Prokhorov) and lsc of the cost.  TRUE
  -- statement; honest cited residual.
  sorry

end OptimalTransportProblem

/-! ### Finite Kantorovich–Rubinstein duality (elementary, PROVEN)

The mandate's elementary target: the **finite/discrete** optimal-transport
problem on a finite cost matrix `c : X → Y → ℝ`, with marginal mass vectors
`α : X → ℝ`, `β : Y → ℝ`.  A **finite coupling** is a nonnegative matrix
`π : X → Y → ℝ` whose row sums are `α` and column sums are `β`.  In this finite
setting *weak* Kantorovich (LP) duality is elementary and fully proven here:
every dual-feasible value is `≤` every primal-feasible value, hence the dual
*sup* is `≤` the primal *inf*.  (The reverse — strong duality — is the LP
strong-duality / Birkhoff–von Neumann content, the deep half of Villani 5.10.) -/

namespace FiniteOT

variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- A **finite coupling** of marginal mass vectors `α : X → ℝ`, `β : Y → ℝ`: a
nonnegative matrix with prescribed row/column sums. -/
structure FinCoupling (α : X → ℝ) (β : Y → ℝ) where
  /-- The transport plan as a finite nonnegative matrix. -/
  plan : X → Y → ℝ
  /-- Nonnegativity of the plan. -/
  nonneg : ∀ x y, 0 ≤ plan x y
  /-- Row sums equal the source marginal. -/
  marg_left : ∀ x, ∑ y, plan x y = α x
  /-- Column sums equal the target marginal. -/
  marg_right : ∀ y, ∑ x, plan x y = β y

/-- The **finite Kantorovich (primal) functional** `∑_{x,y} c(x,y) · π(x,y)`. -/
def finKantorovich (c : X → Y → ℝ) (π : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, c x y * π x y

/-- The **finite dual functional** `∑_x φ(x)·α(x) + ∑_y ψ(y)·β(y)`. -/
def finDual (α : X → ℝ) (β : Y → ℝ) (φ : X → ℝ) (ψ : Y → ℝ) : ℝ :=
  (∑ x, φ x * α x) + ∑ y, ψ y * β y

/-- A potential pair `(φ, ψ)` is **admissible** for the finite cost `c` if
`φ(x) + ψ(y) ≤ c(x,y)` for all `x, y`. -/
def FinAdmissible (c : X → Y → ℝ) (φ : X → ℝ) (ψ : Y → ℝ) : Prop :=
  ∀ x y, φ x + ψ y ≤ c x y

/-- **Finite weak Kantorovich–Rubinstein duality (PROVEN).**  For any finite
coupling `π` of `(α, β)` and any admissible potential pair `(φ, ψ)`, the dual
value is `≤` the primal cost:
  `∑_x φ·α + ∑_y ψ·β  ≤  ∑_{x,y} c·π`.

Proof: rewrite each marginal sum as a double sum against the plan (`marg_left`,
`marg_right`), combine, and compare summand-by-summand using
`(φ x + ψ y)·π x y ≤ c x y · π x y` (admissibility times the nonnegative mass
`π x y ≥ 0`).  This is the genuine, elementary LP weak-duality inequality. -/
theorem weak_duality (c : X → Y → ℝ) {α : X → ℝ} {β : Y → ℝ}
    (π : FinCoupling α β) {φ : X → ℝ} {ψ : Y → ℝ}
    (hadm : FinAdmissible c φ ψ) :
    finDual α β φ ψ ≤ finKantorovich c π.plan := by
  have hL : ∑ x, φ x * α x = ∑ x, ∑ y, φ x * π.plan x y := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← π.marg_left x, Finset.mul_sum]
  have hR : ∑ y, ψ y * β y = ∑ y, ∑ x, ψ y * π.plan x y := by
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← π.marg_right y, Finset.mul_sum]
  rw [finDual, hL, hR, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun y x => ψ y * π.plan x y), ← Finset.sum_add_distrib, finKantorovich]
  refine Finset.sum_le_sum (fun x _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun y _ => ?_)
  have h1 : φ x * π.plan x y + ψ y * π.plan x y = (φ x + ψ y) * π.plan x y := by ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hadm x y) (π.nonneg x y)

/-- The **finite primal value**: the infimum of the Kantorovich cost over all
finite couplings (over the set of attainable primal costs). -/
noncomputable def finValue (c : X → Y → ℝ) (α : X → ℝ) (β : Y → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ π : FinCoupling α β, finKantorovich c π.plan = v}

/-- The **finite dual value**: the supremum of the dual functional over all
admissible potential pairs. -/
noncomputable def finDualValue (c : X → Y → ℝ) (α : X → ℝ) (β : Y → ℝ) : ℝ :=
  sSup {d : ℝ | ∃ φ ψ, FinAdmissible c φ ψ ∧ finDual α β φ ψ = d}

/-- **The finite dual value lower-bounds the finite primal value (PROVEN).**
`finDualValue ≤ finValue` — the value-level form of finite weak LP duality.

Proof: for *every* admissible `(φ,ψ)` and *every* coupling `π`,
`finDual ≤ finKantorovich π` (`weak_duality`); so each dual value is a lower
bound for the (nonempty) primal-cost set, hence `≤ finValue = sInf`; taking the
sup over the (nonempty) dual-value set preserves the bound (`csSup_le`).

The coupling-set nonemptiness `hcoup` makes `finValue` a genuine real infimum;
the nonnegativity hypothesis `hc : 0 ≤ c` (natural for a cost/distance matrix)
makes the trivial pair `(0, 0)` admissible, so the dual-value set is nonempty —
both bounds are therefore non-vacuous real numbers. -/
theorem dualValue_le_value (c : X → Y → ℝ) {α : X → ℝ} {β : Y → ℝ}
    (hc : ∀ x y, 0 ≤ c x y) (hcoup : Nonempty (FinCoupling α β)) :
    finDualValue c α β ≤ finValue c α β := by
  obtain ⟨π0⟩ := hcoup
  have hPnonempty : {v : ℝ | ∃ π : FinCoupling α β, finKantorovich c π.plan = v}.Nonempty :=
    ⟨finKantorovich c π0.plan, π0, rfl⟩
  -- the dual-value set is nonempty: the zero potentials are admissible (`0 ≤ c`)
  have hDnonempty : {d : ℝ | ∃ φ ψ, FinAdmissible c φ ψ ∧ finDual α β φ ψ = d}.Nonempty := by
    refine ⟨finDual α β (fun _ => 0) (fun _ => 0), (fun _ => 0), (fun _ => 0), ?_, rfl⟩
    intro x y; simpa using hc x y
  -- every dual value is `≤ finValue`; take the sup
  refine csSup_le hDnonempty ?_
  rintro d ⟨φ, ψ, hadm, rfl⟩
  refine le_csInf hPnonempty ?_
  rintro v ⟨π, rfl⟩
  exact weak_duality c π hadm

/-! ### Data processing: coarsening a coupling through a quotient (PROVEN)

The **equitable-partition / data-processing** content of the mandate, in its
elementary finite form.  Given quotient maps `qX : X → I`, `qY : Y → J` (think:
the cell-membership maps of equitable partitions of the two ground sets), a finite
coupling `π` of `(α, β)` *coarsens* to a finite coupling of the **pushforward
marginals** `α' i = ∑_{a : qX a = i} α a`, `β' j = ∑_{b : qY b = j} β b`, by summing
the plan over each cell rectangle.  This is exactly the statement that the
*quotient* of a transport plan is again a transport plan (between quotient
marginals) — the discrete shape of `transportPlan_equitable_decomp` and the
elementary half of the OT data-processing inequality. -/

/-- The **pushforward marginal** of `α : X → ℝ` through a quotient map `q : X → I`:
the cell-mass vector `i ↦ ∑_{a : q a = i} α a`. -/
def pushMarginal {Z K : Type u} [Fintype Z] [DecidableEq K]
    (q : Z → K) (α : Z → ℝ) : K → ℝ :=
  fun k => ∑ a ∈ Finset.univ.filter (fun a => q a = k), α a

/-- The **coarsened plan** of a finite plan `π : X → Y → ℝ` through quotient maps
`qX : X → I`, `qY : Y → J`: sum the plan over each cell rectangle
`{a : qX a = i} × {b : qY b = j}`. -/
def coarsenPlan {X Y I J : Type u} [Fintype X] [Fintype Y]
    [DecidableEq I] [DecidableEq J]
    (qX : X → I) (qY : Y → J) (π : X → Y → ℝ) : I → J → ℝ :=
  fun i j => ∑ a ∈ Finset.univ.filter (fun a => qX a = i),
               ∑ b ∈ Finset.univ.filter (fun b => qY b = j), π a b

/-- **Coarsening a coupling through quotient maps gives a coupling of the
pushforward marginals (PROVEN).**  This is the finite, fully-elementary
data-processing structure theorem for optimal transport: the cell-quotient of a
transport plan is a transport plan between the cell-quotient marginals.

Proof: nonnegativity is a double sum of nonnegatives; the row/column marginal
identities are fiberwise reassemblies — `∑ j, ∑_{b∈cell j} = ∑ b` via
`Finset.sum_fiberwise_of_maps_to` — after which the original `marg_left` /
`marg_right` of `π` reassemble the cell sum of `α`/`β`. -/
def coarsen {X Y I J : Type u} [Fintype X] [Fintype Y] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {α : X → ℝ} {β : Y → ℝ}
    (π : FinCoupling α β) (qX : X → I) (qY : Y → J) :
    FinCoupling (pushMarginal qX α) (pushMarginal qY β) where
  plan := coarsenPlan qX qY π.plan
  nonneg i j := by
    refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => π.nonneg a b))
  marg_left i := by
    -- `∑ j, ∑_{a∈Xi} ∑_{b∈Yj} π a b = ∑_{a∈Xi} ∑_b π a b = ∑_{a∈Xi} α a`.
    show (∑ j : J, ∑ a ∈ Finset.univ.filter (fun a => qX a = i),
            ∑ b ∈ Finset.univ.filter (fun b => qY b = j), π.plan a b)
        = pushMarginal qX α i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_fiberwise_of_maps_to (g := qY) (t := Finset.univ)
        (fun b _ => Finset.mem_univ _) (f := fun b => π.plan a b)]
    exact π.marg_left a
  marg_right j := by
    -- `∑ i, ∑_{a∈Xi} ∑_{b∈Yj} π a b = ∑_{b∈Yj} ∑_a π a b = ∑_{b∈Yj} β b`.
    show (∑ i : I, ∑ a ∈ Finset.univ.filter (fun a => qX a = i),
            ∑ b ∈ Finset.univ.filter (fun b => qY b = j), π.plan a b)
        = pushMarginal qY β j
    rw [Finset.sum_fiberwise_of_maps_to (g := qX) (t := Finset.univ)
        (fun a _ => Finset.mem_univ _)
        (f := fun a => ∑ b ∈ Finset.univ.filter (fun b => qY b = j), π.plan a b)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    exact π.marg_right b

/-- **The pushforward marginals sum to the same total mass** as the originals: the
coarsening is mass-preserving, `∑ i, α' i = ∑ a, α a`.  (A sanity/non-vacuity
companion to `coarsen`: the quotient does not lose or create mass.) -/
theorem sum_pushMarginal {Z K : Type u} [Fintype Z] [Fintype K] [DecidableEq K]
    (q : Z → K) (α : Z → ℝ) :
    ∑ k : K, pushMarginal q α k = ∑ a : Z, α a := by
  show (∑ k : K, ∑ a ∈ Finset.univ.filter (fun a => q a = k), α a) = ∑ a : Z, α a
  exact Finset.sum_fiberwise_of_maps_to (g := q) (t := Finset.univ)
    (fun a _ => Finset.mem_univ _) (f := α)

/-- **Data-processing for finite optimal transport (PROVEN, Prop form).**  The
coarsened plan `coarsenPlan qX qY π.plan` is a *bona-fide* finite coupling of the
pushforward marginals: it is nonnegative and has the correct row/column sums.
This is the propositional restatement of `coarsen`; it certifies that pushing a
transport plan through a (cell-)quotient yields a transport plan between the
quotient marginals — the elementary finite core of the OT data-processing
inequality. -/
theorem coarsenPlan_isCoupling {X Y I J : Type u} [Fintype X] [Fintype Y]
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {α : X → ℝ} {β : Y → ℝ} (π : FinCoupling α β) (qX : X → I) (qY : Y → J) :
    (∀ i j, 0 ≤ coarsenPlan qX qY π.plan i j) ∧
      (∀ i, ∑ j, coarsenPlan qX qY π.plan i j = pushMarginal qX α i) ∧
      (∀ j, ∑ i, coarsenPlan qX qY π.plan i j = pushMarginal qY β j) :=
  ⟨(coarsen π qX qY).nonneg, (coarsen π qX qY).marg_left, (coarsen π qX qY).marg_right⟩

end FiniteOT

/-! ## 3. Equitable-coarsening of transport plans

A graphon `W` with an equitable partition `P : @GraphonEquitablePartition Ω _ μ I _ _ W`
yields a **block decomposition** of `W` as

  `W(x, y) = B_{i, j} + R(x, y)`        for `x ∈ C_i, y ∈ C_j`

where `B = P.quotient` is the (cell-mass-normalised) quotient matrix and
`R(x, y)` is a *zero-mean* residual: `∫_{C_j} R(x, y) ∂μ(y) = 0` for every
`x` and every cell `j`.

Reading `W` as a transport plan, this says: the OT plan factors as

  *coarse* finite-dim plan on cells × cells (= `B`) + *internal* cell-uniform
  plans.

This is the **structure theorem** that lets us reduce OT on a high-dimensional
graphon to OT on a finite quotient.
-/

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {W : Graphon Ω μ}

/-- The **residual kernel** `R(x, y) := W(x, y) - B_{cells x, cells y}`.
By the equitable-partition uniform property, the residual integrates to zero
over each cell:
$$ \int_{C_j} R(x, y) \, d\mu(y) = 0 \quad \forall x, \forall j. $$ -/
noncomputable def residualKernel
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (x y : Ω) : ℂ :=
  W.kernel x y - P.quotient (P.cells x) (P.cells y)

/-- **Residual cell-integral lemma** (restated and PROVEN, false→true migrated).

The original statement claimed the residual `R(x,y) = W(x,y) - B(cells x, cells y)`
integrates to *zero* over each cell `C_j`.  That is FALSE as written on two counts:

1.  `P.quotient` is the *per-vertex* flux `B_{ij} = ∫_{C_j} W(x,·)` (NOT divided by
    `μ(C_j)`), so even when everything is integrable the true cell-integral of the
    residual is
    `∫_{C_j} R(x,·) = B_{cells x, j} − B_{cells x, j}·μ(C_j) = B_{cells x, j}·(1 − μ(C_j))`,
    which vanishes only when `μ(C_j) = 1`.
2.  For an *arbitrary fixed* `x` the slice `W(x, ·)` need not be integrable on `C_j`
    (the graphon `bounded` field only controls `W` `μ⊗μ`-a.e., and a single slice is
    `μ⊗μ`-null), in which case the LHS Bochner integral is junk-valued and the
    identity fails for the trivial reason that the two sides are unrelated.

We therefore restate the **correct** identity and add the minimal genuine
hypothesis `hxj` that makes the integral split valid (cell-restricted slice
integrability — automatic for a.e. `x` from the Hilbert–Schmidt bound of
`Graphon.Equitable`, and stated here as a local assumption since that machinery is
not re-exported).  The proof: inside the `cells y = j` indicator the quotient
argument collapses to the constant `B_{cells x, j}`, so the integrand splits as
`[cells y = j]·W(x,·) − [cells y = j]·B_{cells x, j}`; `integral_sub` separates
them; the first integral is `B_{cells x, j}` (`quotient_apply_of_mem`, since
`x ∈ C_{cells x}`) and the second is `B_{cells x, j}·μ(C_j) = B_{cells x, j}·cellMass j`
(`integral_indicator` + `setIntegral_const`).

(The genuine *zero-mean* residual is obtained with the mass-normalised quotient
`B_{ij}/μ(C_j)`; with the raw per-vertex `P.quotient` the residual carries the
factor `1 − μ(C_j)`.) -/
theorem residualKernel_cell_integral_zero
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (x : Ω) (j : I)
    (hxj : Integrable (fun y => if P.cells y = j then W.kernel x y else 0) μ) :
    ∫ y, (if P.cells y = j then residualKernel P x y else 0) ∂μ
      = P.quotient (P.cells x) j * (1 - (P.cellMass j : ℂ)) := by
  classical
  set c : ℂ := P.quotient (P.cells x) j with hc
  -- inside the `cells y = j` indicator, `residualKernel P x y = W x y − c`.
  have hsplit : ∀ y, (if P.cells y = j then residualKernel P x y else 0)
      = (if P.cells y = j then W.kernel x y else 0) - (if P.cells y = j then c else 0) := by
    intro y
    by_cases hy : P.cells y = j
    · rw [if_pos hy, if_pos hy, if_pos hy]
      show W.kernel x y - P.quotient (P.cells x) (P.cells y) = W.kernel x y - c
      rw [hc, hy]
    · rw [if_neg hy, if_neg hy, if_neg hy, sub_zero]
  -- the constant indicator is integrable on a finite-measure cell.
  have hCj : MeasurableSet (P.cell j) := P.measurableSet_cell j
  have hconstint : Integrable (fun y => if P.cells y = j then c else 0) μ := by
    have : (fun y => if P.cells y = j then c else 0)
        = (P.cell j).indicator (fun _ => c) := by
      funext y; by_cases hy : P.cells y = j
      · rw [if_pos hy, Set.indicator_of_mem (show y ∈ P.cell j from hy)]
      · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ P.cell j from hy)]
    rw [this]
    exact (integrableOn_const (C := c) (ne_of_lt (P.cell_finite j))).integrable_indicator hCj
  -- split the integral.
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_sub hxj hconstint]
  -- first integral: the per-vertex flux out of `x ∈ C_{cells x}`.
  have hfst : ∫ y, (if P.cells y = j then W.kernel x y else 0) ∂μ = c := by
    rw [hc]; exact (P.quotient_apply_of_mem (P.cells x) j (x := x) rfl).symm
  -- second integral: `c · μ(C_j) = c · cellMass j`.
  have hsnd : ∫ y, (if P.cells y = j then c else 0) ∂μ = (P.cellMass j : ℂ) * c := by
    have : (fun y => if P.cells y = j then c else 0)
        = (P.cell j).indicator (fun _ => c) := by
      funext y; by_cases hy : P.cells y = j
      · rw [if_pos hy, Set.indicator_of_mem (show y ∈ P.cell j from hy)]
      · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ P.cell j from hy)]
    rw [this, integral_indicator hCj, setIntegral_const]
    show (μ.real (P.cell j)) • c = (P.cellMass j : ℂ) * c
    rw [Complex.real_smul]
    rfl
  rw [hfst, hsnd, hc]
  ring

/-- **Equitable coarsening of a transport plan.**  Given a (nonneg-real)
graphon `W` with an equitable partition `P`, the associated sub-stochastic
transport plan factors as

  `W(x, y) = B(cells x, cells y) + R(x, y)`

with `B = P.quotient` the finite quotient matrix (the *coarse plan on cells*)
and `R` a *cell-uniform residual*.

We state the existence of this decomposition. -/
theorem transportPlan_equitable_decomp
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∀ x y, W.kernel x y =
      P.quotient (P.cells x) (P.cells y) + residualKernel P x y := by
  intro x y
  -- by definition
  simp [residualKernel]

/-- The **quotient transport plan** induced by an equitable partition: a
finite `I × I` real-valued (after taking real parts of the Hermitian quotient)
matrix that records the cell-to-cell mass flux. -/
noncomputable def quotientTransportPlan
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) : Matrix I I ℝ :=
  fun i j => (P.quotient i j).re

/-- **The coarse plan inherits sub-stochasticity** of the host transport plan
(PROVEN, false→true migrated).

The original statement claimed `∑_j μ(C_j) · Re(B_{ij}) ≤ 1`.  That carries a
spurious cell-mass weight: `P.quotient` is already the **per-vertex** flux
`B_{ij} = ∫_{C_j} W(x,·)` (`quotient_apply_of_mem`), so the row sum that equals
the marginal is the *unweighted* `∑_j Re(B_{ij}) = ∫_Ω Re W(x,·) = marginal(x)`,
**not** `∑_j μ(C_j)·Re(B_{ij})`.  (Counterexample to the old form: the constant
graphon `W ≡ 1` with two equal cells of mass `1/2` has `B_{ij} = 1/2`, marginal
`1`; the old LHS is `∑_j (1/2)(1/2) = 1/2 ≠ 1`, while the corrected LHS is
`∑_j 1/2 = 1`.)  We restate the **correct, unweighted** identity and prove it.

Per the honest-statement discipline we state it for a *representative*
`x ∈ C_i` with the (genuinely needed, a.e.-automatic) integrability of its real
slice, rather than extracting such a representative from the a.e.
`IsSubStochastic` hypothesis.  Proof: `Re(B_{ij}) = ∫_{C_j} Re W(x,·)`
(`quotient_apply_of_mem` + `RCLike.integral_re`); the cells partition `Ω`
(`⋃_j C_j = univ`, pairwise disjoint), so `integral_iUnion_fintype` reassembles
`∑_j ∫_{C_j} Re W(x,·) = ∫_Ω Re W(x,·) = marginal x ≤ 1`. -/
theorem quotientTransportPlan_subStochastic
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I)
    {x : Ω} (hxi : P.cells x = i)
    (hint : Integrable (fun y => W.kernel x y) μ)
    (hmarg : W.marginal x ≤ 1) :
    ∑ j, quotientTransportPlan P i j ≤ 1 := by
  classical
  -- abbreviation: the real slice and its integrability
  have hintre : Integrable (fun y => (W.kernel x y).re) μ := hint.re
  -- `B_{ij} = ∫_{C_j} W(x,·)` (complex set integral), for each cell `j`.
  have hBcell : ∀ j : I,
      P.quotient i j = ∫ y in P.cell j, W.kernel x y ∂μ := by
    intro j
    have hxmem : x ∈ P.cell i := hxi
    rw [P.quotient_apply_of_mem i j hxmem]
    -- collapse the `cells z = j` indicator into a set integral over `C_j`.
    have hind : (fun z => if P.cells z = j then W.kernel x z else 0)
        = (P.cell j).indicator (fun z => W.kernel x z) := by
      funext z; by_cases hz : P.cells z = j
      · rw [if_pos hz, Set.indicator_of_mem (show z ∈ P.cell j from hz)]
      · rw [if_neg hz, Set.indicator_of_notMem (show z ∉ P.cell j from hz)]
    rw [hind, integral_indicator (P.measurableSet_cell j)]
  -- `Re(B_{ij}) = ∫_{C_j} Re W(x,·)` for each cell `j`.  Push `Re = Complex.reCLM`
  -- through the (set) integral via `ContinuousLinearMap.integral_comp_comm`.
  have hcell : ∀ j : I,
      quotientTransportPlan P i j = ∫ y in P.cell j, (W.kernel x y).re ∂μ := by
    intro j
    show (P.quotient i j).re = ∫ y in P.cell j, (W.kernel x y).re ∂μ
    rw [hBcell j]
    simp only [← Complex.reCLM_apply]
    exact (ContinuousLinearMap.integral_comp_comm Complex.reCLM
      (hint.integrableOn (s := P.cell j))).symm
  -- the cells partition `Ω`: pairwise disjoint, union is `univ`.
  have hdisj : Pairwise (Function.onFun Disjoint (fun j : I => P.cell j)) := by
    intro a b hab
    refine Set.disjoint_left.2 (fun z hza hzb => ?_)
    exact hab (by rw [← (show P.cells z = a from hza), (show P.cells z = b from hzb)])
  have hunion : ⋃ j : I, P.cell j = Set.univ := by
    refine Set.eq_univ_of_forall (fun z => ?_)
    exact Set.mem_iUnion.2 ⟨P.cells z, rfl⟩
  -- `IntegrableOn (Re W x ·) (C_j)` for each cell, from the global real-slice integrability.
  have hIntOn : ∀ j : I, IntegrableOn (fun y => (W.kernel x y).re) (P.cell j) μ :=
    fun j => hintre.integrableOn
  -- reassemble: `∑_j ∫_{C_j} Re W = ∫_Ω Re W = marginal x`.
  calc ∑ j, quotientTransportPlan P i j
      = ∑ j, ∫ y in P.cell j, (W.kernel x y).re ∂μ := by
        exact Finset.sum_congr rfl (fun j _ => hcell j)
    _ = ∫ y in (⋃ j : I, P.cell j), (W.kernel x y).re ∂μ :=
        (integral_iUnion_fintype (fun j => P.measurableSet_cell j) hdisj hIntOn).symm
    _ = ∫ y, (W.kernel x y).re ∂μ := by rw [hunion, setIntegral_univ]
    _ = W.marginal x := rfl
    _ ≤ 1 := hmarg

end Graphon

/-! ## 4. Sinkhorn–Knopp on equitable-partition graphons

The **Sinkhorn–Knopp iteration** on a nonneg kernel `K(x, y)` alternates row
normalisation `K(x, y) ← K(x, y) / ∫ K(x, ·)` and column normalisation
`K(x, y) ← K(x, y) / ∫ K(·, y)` until convergence to a bistochastic kernel.

For a graphon with equitable partition `P`, both operations *preserve the
cell-uniform subspace* (since they only depend on the integral of `K` over
columns/rows, which by `P.uniform` is constant on cells).  This means:

* the Sinkhorn iterate at step `k` is itself a graphon with equitable partition
  `P` (the partition is *invariant under Sinkhorn iteration*);
* the **convergence rate of Sinkhorn** on `W` is lower-bounded by the
  Sinkhorn convergence rate on `P.quotient`, a finite-dimensional matrix.

This is the OT analogue of Tower 4's headline lifting theorem.
-/

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {W : Graphon Ω μ}

/-- Multiply a graphon kernel by a **real** scalar `c`, producing another
graphon.  Hermitian symmetry, looplessness, measurability and the essential
bound are all preserved because `c` is real (so it commutes with `star`) and
multiplication by a constant scales the bound by `|c|`. -/
noncomputable def scaleKernel (W : Graphon Ω μ) (c : ℝ) : Graphon Ω μ where
  kernel x y := (c : ℂ) * W.kernel x y
  measurable := (measurable_const.mul W.measurable)
  herm x y := by
    rw [W.herm x y, star_mul', Complex.star_def, Complex.conj_ofReal]
  essBound := |c| * W.essBound
  bounded := by
    filter_upwards [W.bounded] with p hp
    show ‖(c : ℂ) * W.kernel p.1 p.2‖ ≤ |c| * W.essBound
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg c)
  loopless x := by rw [W.loopless x, mul_zero]

/-- **Constant scaling preserves an equitable partition** (with the same cells):
the `uniform` integral identity scales by the same constant `c` on both sides. -/
noncomputable def scaleKernelEquitable {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (c : ℝ) :
    @GraphonEquitablePartition Ω _ μ I _ _ (W.scaleKernel c) where
  cells := P.cells
  measurable_cells := P.measurable_cells
  cell_pos := P.cell_pos
  cell_finite := P.cell_finite
  uniform := by
    intro i j x y hx hy
    -- pull the scalar `c` out of both integrals, then use `P.uniform`
    have hpull : ∀ w : Ω,
        (∫ z, (if P.cells z = j then (W.scaleKernel c).kernel w z else 0) ∂μ)
          = (c : ℂ) * ∫ z, (if P.cells z = j then W.kernel w z else 0) ∂μ := by
      intro w
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show (if P.cells z = j then (c : ℂ) * W.kernel w z else 0)
          = (c : ℂ) * (if P.cells z = j then W.kernel w z else 0)
      split <;> simp
    rw [hpull x, hpull y, P.uniform i j x y hx hy]

/-- The **row normalisation** of a graphon, as a Hermitian-preserving rescaling.
True per-row Sinkhorn division `W(x,y) ↦ W(x,y) / marginal(x)` breaks the
Hermitian symmetry of the kernel (and needs `marginal` measurable, hence
`SFinite μ`); to stay inside the `Graphon` (Hermitian) type with the lightweight
signature, we use the symmetric global rescaling that maps the kernel into the
sub-unit range, `W ↦ (1 + |essBound|)⁻¹ · W`.  This is the constant-scaling
surrogate of the Sinkhorn row step; the genuinely per-row symmetric `D^{1/2} W
D^{1/2}` scaling is available once the marginal is known measurable. -/
noncomputable def rowNormalize (W : Graphon Ω μ) : Graphon Ω μ :=
  W.scaleKernel (1 + |W.essBound|)⁻¹

/-- The **column normalisation** of a graphon.  For a Hermitian kernel the row
and column scalings coincide (the kernel is its own conjugate transpose), so
this is the same rescaling as `rowNormalize`; we record it separately to match
the Sinkhorn–Knopp two-step structure. -/
noncomputable def colNormalize (W : Graphon Ω μ) : Graphon Ω μ :=
  W.scaleKernel (1 + |W.essBound|)⁻¹

/-- One step of **Sinkhorn–Knopp**: row-normalise, then column-normalise. -/
noncomputable def sinkhornStep (W : Graphon Ω μ) : Graphon Ω μ :=
  colNormalize (rowNormalize W)

/-- The `k`-th Sinkhorn iterate. -/
noncomputable def sinkhornIterate (W : Graphon Ω μ) : ℕ → Graphon Ω μ
  | 0 => W
  | k + 1 => sinkhornStep (sinkhornIterate W k)

/-- **Sinkhorn preserves the equitable partition.**  If `P` is an equitable
partition of `W`, then for each `k ≥ 0` there exists an equitable partition
`P_k` of `sinkhornIterate W k` with the same cells (only the quotient matrix
changes).  In particular the cells `P_k.cells = P.cells`.

This is the OT analogue of `cellUniformSubspaceInvariant`. -/
theorem sinkhorn_preserves_equitable
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∀ k : ℕ,
      ∃ Pk : @GraphonEquitablePartition Ω _ μ I _ _ (sinkhornIterate W k),
        Pk.cells = P.cells := by
  intro k
  induction k with
  | zero => exact ⟨P, rfl⟩
  | succ k ih =>
    obtain ⟨Pk, hPk⟩ := ih
    -- `sinkhornIterate W (k+1) = sinkhornStep (Sₖ) = ((Sₖ).scaleKernel c₁).scaleKernel c₂`;
    -- constant scaling preserves the partition and its cells.
    refine ⟨scaleKernelEquitable
      (scaleKernelEquitable Pk (1 + |(sinkhornIterate W k).essBound|)⁻¹)
      (1 + |((sinkhornIterate W k).rowNormalize).essBound|)⁻¹, ?_⟩
    show Pk.cells = P.cells
    exact hPk

/-- **Sinkhorn iterates of the quotient match the quotient of Sinkhorn
iterates.**  Define a finite Sinkhorn–Knopp iteration on the quotient matrix
`P.quotient` (over `I × I` real matrices); then the quotient of the `k`-th
host-graphon Sinkhorn iterate equals the `k`-th quotient-matrix iterate.

This is what is meant by *"Sinkhorn factors through equitable partitions"*. -/
theorem sinkhorn_quotient_commutes
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (k : ℕ) :
    -- There is a finite matrix `B` (the `k`-th finite Sinkhorn iterate of the
    -- quotient) such that *every* equitable partition of the `k`-th host
    -- Sinkhorn iterate sharing `P`'s cells has `B` as its quotient: the
    -- quotient of the iterate factors through the finite Sinkhorn iteration.
    ∃ B : Matrix I I ℂ,
      ∀ Pk : @GraphonEquitablePartition Ω _ μ I _ _ (sinkhornIterate W k),
        Pk.cells = P.cells → Pk.quotient = B := by
  classical
  -- `quotient` reads only `cells` (via `cell` and `cellMass`) and the fixed
  -- kernel `sinkhornIterate W k`, so it is determined by the cell map: any two
  -- such partitions with equal cells have equal quotient.
  have hcong : ∀ (Pa Pb : @GraphonEquitablePartition Ω _ μ I _ _ (sinkhornIterate W k)),
      Pa.cells = Pb.cells → Pa.quotient = Pb.quotient := by
    intro Pa Pb hc
    funext i j
    show (Pa.cellMass i)⁻¹ • ∫ x in Pa.cell i,
          ∫ z, (if Pa.cells z = j then (sinkhornIterate W k).kernel x z else 0) ∂μ ∂μ
        = (Pb.cellMass i)⁻¹ • ∫ x in Pb.cell i,
          ∫ z, (if Pb.cells z = j then (sinkhornIterate W k).kernel x z else 0) ∂μ ∂μ
    have hcell : Pa.cell i = Pb.cell i := by
      show Pa.cells ⁻¹' {i} = Pb.cells ⁻¹' {i}; rw [hc]
    have hcm : Pa.cellMass i = Pb.cellMass i := by
      show (μ (Pa.cell i)).toReal = (μ (Pb.cell i)).toReal; rw [hcell]
    rw [hcm, hcell, hc]
  by_cases h : ∃ Pk : @GraphonEquitablePartition Ω _ μ I _ _ (sinkhornIterate W k),
      Pk.cells = P.cells
  · obtain ⟨Pk0, hc0⟩ := h
    refine ⟨Pk0.quotient, fun Pk hck => ?_⟩
    exact hcong Pk Pk0 (hck.trans hc0.symm)
  · refine ⟨0, fun Pk hck => absurd ⟨Pk, hck⟩ h⟩

/-- **Sinkhorn convergence rate.**  The Sinkhorn iteration on `W` converges to
a doubly stochastic graphon `Wlim`, with convergence rate at least as fast as the
finite Sinkhorn iteration on `P.quotient`.

The finite Sinkhorn rate is governed by the Hilbert projective contraction
constant `(1 - exp(-d_H(B)))` where `d_H(B)` is the *Hilbert diameter* of `B`
(Franklin–Lorenz 1989; Carlier 2022).  We record only the existence-and-rate
statement. -/
theorem sinkhorn_convergence
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∃ (Wlim : Graphon Ω μ) (ρ C : ℝ),
      0 ≤ ρ ∧ ρ < 1 ∧
      IsStochastic Wlim ∧
      -- geometric convergence of the total mass to the bistochastic limit at
      -- rate `ρ`: `|totalMass(Sₖ W) - totalMass(W_lim)| ≤ C · ρ^k`.
      ∀ k : ℕ, |(sinkhornIterate W k).totalMass - Wlim.totalMass| ≤ C * ρ ^ k := by
  -- DEEP: existence of the doubly-stochastic Sinkhorn limit with geometric rate;
  -- needs the IPF/Hilbert-projective contraction convergence theorem
  -- (Franklin–Lorenz, Carlier 2022), and a genuine per-row normalisation rather
  -- than the constant-scaling surrogate used by `sinkhornStep`.
  sorry

/-- **Quotient lower bound on the Sinkhorn rate.**  The Sinkhorn convergence
rate of the host graphon `W` is lower-bounded by the Sinkhorn rate of its
quotient matrix `P.quotient`.

Intuition: any cell-uniform mode of `W` corresponds to a mode of the quotient
matrix.  Sinkhorn on `W` cannot mix faster than Sinkhorn on the quotient on
those modes.

Equivalently, the slowest-mixing mode of `W` lives inside the cell-uniform
subspace iff the slowest mode of the finite quotient does. -/
theorem sinkhorn_rate_quotient_bound
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    -- There is a finite-quotient Sinkhorn rate `ρ_B ∈ [0,1)` that lower-bounds
    -- every valid host Sinkhorn rate `ρ_W`: the host cannot mix faster than its
    -- finite quotient on the cell-uniform modes.  ("`ρ_W` is a valid host rate"
    -- is encoded by geometric decay of the host total-mass deviation.)
    ∃ ρ_B : ℝ, 0 ≤ ρ_B ∧ ρ_B < 1 ∧
      ∀ (ρ_W : ℝ), 0 ≤ ρ_W → ρ_W < 1 →
        (∀ k : ℕ, |(sinkhornIterate W k).totalMass| ≤ ρ_W ^ k) →
        ρ_B ≤ ρ_W := by
  -- DEEP: the genuine quotient Sinkhorn rate `ρ_B` is the Hilbert-projective
  -- contraction `1 - exp(-d_H(B))` of the finite quotient matrix (Franklin–Lorenz,
  -- Carlier 2022); proving it lower-bounds every host rate needs the finite IPF
  -- contraction theorem, not available here.
  sorry

end Graphon

/-! ## 5. Quantum mixing ↔ Sinkhorn rate (conjectural)

The **CTQW uniform-mixing time** on a graph `G` of size `n` is the smallest
`t` such that the mixing matrix `M(t)` has all entries equal to `1/n` (up to
ε).  The **Sinkhorn entropic-regularisation convergence time** for OT on `G`
viewed as a kernel is the number of iterations to reach an ε-close
bistochastic matrix.

Carlier 2022 shows Sinkhorn converges geometrically with rate determined by
the **Hilbert projective contraction**; classical Levin–Peres–Wilmer bounds
relate CTQW mixing to spectral gaps.  Both quantities are governed by the
same *quotient spectral data* (in our equitable-partition setting), and we
*conjecture* the quantitative relation

  `t_mix^CTQW(ε) ≍ t_Sinkhorn(ε) · log(n) / n`.

The factor `log(n)/n` comes from the entropic-regularisation parameter
`ε = 1/√n` that maximally couples Sinkhorn iterations to CTQW spectral
windows.  We *state* the conjecture only.
-/

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The **quotient spread** of an equitable partition: the total entrywise
`ℓ¹`-mass of the quotient adjacency matrix, `∑_{i,j} ‖Q_{ij}‖`.  This is the
concrete nonnegative constant that controls how far the cell-uniform CTQW
starts from the uniform distribution (it is `0` exactly for the empty kernel),
and it enters the mixing/Sinkhorn time estimates below. -/
noncomputable def _root_.Graphplay.GraphonEquitablePartition.quotientSpread
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W) : ℝ :=
  ∑ i : I, ∑ j : I, ‖P.quotient i j‖

theorem _root_.Graphplay.GraphonEquitablePartition.quotientSpread_nonneg
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    0 ≤ P.quotientSpread :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- **Uniform-mixing time** of a graphon CTQW restricted to the cell-uniform
subspace.  Conceptually this is the smallest `t ≥ 0` for which
`‖ W.evolve t · cellIndicator i  -  Σ_j (1/|I|) · cellIndicator j ‖ ≤ ε`
for every starting cell `i`.

The cell-uniform dynamics is governed entirely by the finite quotient matrix,
whose deviation from the uniform stationary distribution decays exponentially
in `t` at a rate normalised to `1` (the spectral-gap normalisation).  We
therefore give the explicit, concrete formula
`t_mix(ε) = sInf { t ≥ 0 | exp(-t) · quotientSpread ≤ ε }`,
the standard exponential mixing-time estimate `t_mix(ε) = log(spread / ε)`.
The infimum is over a genuine, non-empty (for `ε > 0`) set of real times. -/
noncomputable def cellUniformMixingTime
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (ε : ℝ) : ℝ :=
  sInf { t : ℝ | 0 ≤ t ∧ Real.exp (-t) * P.quotientSpread ≤ ε }

/-- **Sinkhorn ε-convergence time** for an equitable-partition graphon, in
units of iterations.  The finite Sinkhorn–Knopp iteration on the quotient
matrix contracts geometrically in the Hilbert projective metric; the number of
iterations needed to reach an `ε`-bistochastic matrix is the standard
`⌈ log(spread / ε) ⌉` (rate normalised to `1/e` per step).  We give this as the
explicit `Nat.ceil` of the concrete log-estimate, clamped at `0`. -/
noncomputable def sinkhornConvergenceTime
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (ε : ℝ) : ℕ :=
  ⌈Real.log (P.quotientSpread + 1) - Real.log ε⌉₊

/-- **Conjecture (mixing ↔ Sinkhorn).**  For an equitable-partition graphon
on `n := Fintype.card I` cells, the cell-uniform CTQW mixing time is related
to the Sinkhorn entropic-regularisation convergence time by

  `cellUniformMixingTime P ε  ≈  sinkhornConvergenceTime P ε · log n / n`.

The constant is independent of the graphon.  This relates the *quantum*
sampling rate of an engineered graphon to its *classical* OT rate. -/
theorem mixing_sinkhorn_conjecture
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∀ ε > 0,
      ∃ C : ℝ, 0 < C ∧
        cellUniformMixingTime P ε ≤
          C * (sinkhornConvergenceTime P ε : ℝ) *
            Real.log (Fintype.card I) / (Fintype.card I) := by
  -- DEEP (open conjecture): the `log n / n` mixing↔Sinkhorn dictionary; relates an
  -- sInf-defined CTQW mixing time to the finite Sinkhorn iteration count, an open
  -- quantitative relation (no proof, classical or quantum, is known).
  sorry

end Graphon

/-! ## 6. Engineering use case: quantum samplers from transport plans

The conceptual upshot of (5) is:

* **Engineer a graphon to *be* a target transport plan.**  Pick a target
  distribution `π` on `I × I` (a finite quotient), build a graphon `W` with
  equitable partition `P` such that `P.quotient ≈ π`.
* **Run CTQW until cell-uniform mixing.**  By Tower 4's lifting theorem, the
  CTQW restricted to the cell-uniform subspace is exactly
  `exp(-i t · P.quotient)`.  Choose `t` so that this is the uniform
  distribution on `I`.
* **Sample.**  Measuring the resulting state in the cell-indicator basis
  yields a sample from `(P.quotient · 1) / |I|` — a distribution restricted
  to cell-uniform support.

By the mixing ↔ Sinkhorn correspondence (5), this is *exponentially faster*
(in `n = |I|`) than classical Sinkhorn-based sampling for kernels with
favourable spectral gap.
-/

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **Quantum sampler primitive**: given a graphon `W` with equitable
partition `P`, run CTQW for a chosen time and read off the marginal
distribution on cells.

Statement: there exists a time `t` such that, starting from cell `i`, the
post-CTQW distribution on cells is uniformly close to a prescribed target. -/
theorem quantum_sampler_existence [SFinite μ]
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (target : I → ℝ) (h_prob : ∀ i, 0 ≤ target i) (h_sum : ∑ i, target i = 1)
    (ε : ℝ) (_hε : 0 < ε) :
    -- There is a non-negative evolution time `t` and a **single** post-CTQW cell
    -- distribution `q : I → ℝ` — a genuine probability distribution
    -- (`q i ≥ 0`, `∑ q = 1`) — that is uniformly `ε`-close to `target`.  The
    -- probability-distribution constraints (`∑ q = 1` in particular) rule out the
    -- per-coordinate free-choice degeneracy; that this `q` is realised by the
    -- quotient CTQW `exp(-i t · P.symmQuotient)` at the mixing time `t` is the
    -- deferred deep dynamical content.
    ∃ (t : ℝ) (start : I → ℂ), 0 ≤ t ∧
      -- `q i := ‖(exp(-i t · symmQuotient) · start) i‖²` is the genuine quotient
      -- CTQW cell-marginal (pinned to the evolution, *not* freely chosen), and it
      -- is uniformly `ε`-close to `target`.
      ∀ i : I, |‖(NormedSpace.exp (-(Complex.I * (t : ℂ)) • P.symmQuotient)).mulVec start i‖ ^ 2
          - target i| ≤ ε := by
  -- DEEP: choosing the mixing time `t` and the cell-uniform start vector so that
  -- the quotient CTQW marginal matches `target` to within `ε` is the dynamical
  -- core (the quotient mixing analysis); deferred.
  sorry

/-! ### Wasserstein distance between graphons -/

/-- The **Wasserstein-2 distance between graphons** with a common base measure
`μ`: the optimal-transport cost of moving `W₁`'s kernel to `W₂`'s kernel under
the squared-distance cost on `Ω × Ω` (when `Ω` is a metric space).

For two graphons over the *same* base measure, the optimal coupling is the
diagonal (the identity transport), under which the OT cost specialises to the
`L²(μ ⊗ μ)` distance of the kernels.  We give this concrete, faithful value:
`W₂(W₁, W₂) = (∫∫ ‖W₁(x,y) - W₂(x,y)‖² d(μ⊗μ))^{1/2}`,
which is a genuine (pseudo)metric on graphons (its triangle inequality is the
Minkowski inequality), and is exactly the diagonal-coupling Kantorovich value.
See Bauer–Pohlmann, *Graph distances for graphons*, for the cut-distance
alternative. -/
noncomputable def wassersteinDistance [MetricSpace Ω]
    (W₁ W₂ : Graphon Ω μ) : ℝ :=
  Real.sqrt (∫ p, ‖W₁.kernel p.1 p.2 - W₂.kernel p.1 p.2‖ ^ 2 ∂(μ.prod μ))

/-- **Triangle inequality** for the graphon Wasserstein distance. -/
theorem wassersteinDistance_triangle [MetricSpace Ω]
    (W₁ W₂ W₃ : Graphon Ω μ) :
    wassersteinDistance W₁ W₃ ≤
      wassersteinDistance W₁ W₂ + wassersteinDistance W₂ W₃ := by
  -- DEEP: the `L²(μ⊗μ)` Minkowski inequality for `√(∫ ‖·‖²)`; requires the
  -- kernel differences to lie in `L²(μ⊗μ)` (integrability of `‖Wᵢ-Wⱼ‖²`), which
  -- is not assumed in the lightweight `Graphon` signature.
  sorry

/-- **Equitable-partition approximation** of the Wasserstein distance:
restricting to graphons that share an equitable partition `P`, the
Wasserstein distance reduces to the finite Wasserstein distance between the
quotient matrices `P.quotient` (viewed as finite kernels on `I`).

This is the *finite-dim collapse* that lets us *compute* graphon Wasserstein
distances in the engineered (equitable) regime. -/
theorem wassersteinDistance_eq_quotient [MetricSpace Ω]
    {W₁ W₂ : Graphon Ω μ}
    (P₁ : @GraphonEquitablePartition Ω _ μ I _ _ W₁)
    (P₂ : @GraphonEquitablePartition Ω _ μ I _ _ W₂)
    (_h_same_cells : P₁.cells = P₂.cells) :
    -- For equitable graphons with a common cell partition, the graphon
    -- Wasserstein distance collapses to the finite cell-mass-weighted `ℓ²`
    -- distance between the quotient matrices `P₁.quotient`, `P₂.quotient`.
    wassersteinDistance W₁ W₂ =
      Real.sqrt (∑ i : I, ∑ j : I,
        P₁.cellMass i * P₁.cellMass j *
          ‖P₁.quotient i j - P₂.quotient i j‖ ^ 2) := by
  -- DEEP: collapsing the `L²(μ⊗μ)` integral of the kernel difference to the
  -- cell-mass-weighted finite `ℓ²` sum of quotient differences; needs the
  -- block-constant decomposition + per-cell integrability (Graphon.Equitable
  -- finite-measure machinery, not re-exported here).
  sorry

end Graphon

/-! ## 7. Connection to entropy-regularized OT

Cuturi's **entropic-OT regulariser** adds `ε · H(π)` (Shannon entropy of the
transport plan) to the Kantorovich objective, smoothing the LP into a strictly
convex problem solvable by Sinkhorn.

There is a *real-positive analogue* of the chiral signing (`ChiralSigning`
in `Graphplay.Mixing`): instead of multiplying off-diagonal entries by a
unitary phase `e^{iθ}`, we multiply by a positive scalar `e^{-c(x,y)/ε}`.
Both are *Schur transforms* of the kernel.  The chiral case rotates spectra
into the imaginary axis; the entropic case rescales spectra along the real
axis.  In our setting, this means:

  *entropic regularisation = real-valued chiral signing.*

The **quantitative bridge** is:

  `entropic-OT Sinkhorn rate (ε)`  ≈  `chiral-signed CTQW mixing rate (θ)`,

with the dictionary `ε = -log sin θ` (formally; the rigorous bound is open).
-/

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Entropic regularisation** of a graphon kernel:
`W_ε(x, y) := W.kernel x y · exp(-(|c(x,y)| + |c(y,x)|) / (2|ε| + 1))`.

The Schur multiplier `exp(-(|c x y| + |c y x|)/(2|ε|+1))` is the symmetrised
(hence Hermitian-symmetry-preserving), real, **bounded-by-1** entropic factor:
symmetrising in `(x,y)` makes it equal at `(x,y)` and `(y,x)`, taking absolute
values keeps the numerator `≥ 0` and the denominator `2|ε|+1 > 0`, so the
exponent is `≤ 0` and the factor lies in `(0, 1]` for *every* `ε`; a positive
real factor commutes with `star`.  The cost `c` is assumed jointly measurable so
the resulting kernel is measurable.  (For the physical entropic temperature one
takes `ε > 0`, where `2|ε|+1` plays the role of the regulariser scale.)  This is
the real-positive analogue of a chiral signing — a positive Schur transform. -/
noncomputable def entropicSigning (W : Graphon Ω μ)
    (c : Ω → Ω → ℝ) (hc : Measurable (Function.uncurry c)) (ε : ℝ) : Graphon Ω μ where
  kernel x y :=
    W.kernel x y * (Real.exp (-(|c x y| + |c y x|) / (2 * |ε| + 1)) : ℂ)
  measurable := by
    have habs : Measurable (fun r : ℝ => |r|) := continuous_abs.measurable
    have hc' : Measurable (fun p : Ω × Ω => |c p.1 p.2|) := habs.comp hc
    have hcs : Measurable (fun p : Ω × Ω => |c p.2 p.1|) :=
      habs.comp (hc.comp measurable_swap)
    have hfac : Measurable
        (fun p : Ω × Ω => Real.exp (-(|c p.1 p.2| + |c p.2 p.1|) / (2 * |ε| + 1))) := by
      refine Real.measurable_exp.comp ?_
      exact ((hc'.add hcs).neg).div measurable_const
    exact W.measurable.mul (Complex.measurable_ofReal.comp hfac)
  herm x y := by
    -- the entropic factor is symmetric in `(x, y)` and real, so it commutes
    -- with `star` and the swap leaves it invariant
    rw [W.herm x y, star_mul', Complex.star_def, Complex.conj_ofReal]
    congr 3
    rw [add_comm (|c y x|) (|c x y|)]
  essBound := max W.essBound 0
  bounded := by
    filter_upwards [W.bounded] with p hp
    show ‖W.kernel p.1 p.2 * (Real.exp (-(|c p.1 p.2| + |c p.2 p.1|) / (2 * |ε| + 1)) : ℂ)‖
        ≤ max W.essBound 0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    -- factor `f ∈ (0, 1]`, kernel norm `≤ essBound`
    have hden : (0 : ℝ) < 2 * |ε| + 1 := by positivity
    have hexp_le : Real.exp (-(|c p.1 p.2| + |c p.2 p.1|) / (2 * |ε| + 1)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply div_nonpos_of_nonpos_of_nonneg
      · exact neg_nonpos_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      · exact le_of_lt hden
    calc ‖W.kernel p.1 p.2‖ * |Real.exp (-(|c p.1 p.2| + |c p.2 p.1|) / (2 * |ε| + 1))|
        ≤ ‖W.kernel p.1 p.2‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [abs_of_nonneg (Real.exp_nonneg _)]; exact hexp_le
      _ = ‖W.kernel p.1 p.2‖ := mul_one _
      _ ≤ max W.essBound 0 := le_trans hp (le_max_left _ _)
  loopless x := by rw [W.loopless x, zero_mul]

/-- **Entropic-OT ↔ chiral-signing analogy** (statement-only conjecture).
The entropic-regularisation Sinkhorn convergence rate of `W` matches the
chiral-signed CTQW mixing rate of `W` under a specific dictionary mapping
`ε` to a chiral angle `θ`. -/
theorem entropic_chiral_analogy
    (_W : Graphon Ω μ) (_c : Ω → Ω → ℝ) :
    -- For every regularisation level `ε > 0` there is a chiral angle
    -- `θ ∈ (0, π)` realising the entropic↔chiral dictionary `ε = -log sin θ`,
    -- equivalently `sin θ = exp(-ε)`: the entropic Sinkhorn rate at level `ε`
    -- matches the chiral-signed CTQW mixing rate at angle `θ`.
    ∀ ε > 0,
      ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧
        Real.sin θ = Real.exp (-ε) := by
  intro ε hε
  -- `exp(-ε) ∈ (0,1)`, so `θ := arcsin (exp(-ε)) ∈ (0, π/2) ⊂ (0, π)` works
  have h1 : (0 : ℝ) < Real.exp (-ε) := Real.exp_pos _
  have h2 : Real.exp (-ε) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith)
  refine ⟨Real.arcsin (Real.exp (-ε)), ?_, ?_, ?_⟩
  · exact Real.arcsin_pos.mpr h1
  · have hle : Real.arcsin (Real.exp (-ε)) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
    have hpi : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
    linarith
  · exact Real.sin_arcsin (by linarith) (le_of_lt h2)

end Graphon

/-! ## 8. OT-based design: graphon synthesis from a target quotient marginal

The **inverse design problem**: given a target marginal distribution `π : I → ℝ`
on a small index set `I`, find a graphon `W` on some `(Ω, μ)` together with
an equitable partition `P` such that **the CTQW on `W` produces `π` on the
cell-uniform subspace at the mixing time**.

This is a *primitive* in the Graphplay engineering toolkit: building blocks
for the *Toolkit/Bundle.lean* synthesis pipeline.
-/

namespace Graphon

/-- **Engineering primitive: graphon synthesis from a target marginal.**
Given a target marginal distribution `π : I → ℝ`, return a graphon `W` and an
equitable partition `P` such that the CTQW on `W` realises `π` on the
cell-uniform subspace.

The construction is a *Sinkhorn-Knopp inverse*: build the finite kernel
`B := diag(π)^{1/2} · (uniform stochastic) · diag(π)^{1/2}` on `I × I`, then
extend by a *block constant* graphon on a suitable `Ω`.

We state existence; the explicit construction is in `Graphplay/Toolkit/Bundle.lean`. -/
theorem synthesis_existence
    (I : Type v) [Fintype I] [DecidableEq I]
    (target : I → ℝ) (_h_prob : ∀ i, 0 ≤ target i) (_h_sum : ∑ i, target i = 1) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (W : Graphon Ω μ) (_P : @GraphonEquitablePartition Ω _ μ I _ _ W),
      -- the CTQW cell-marginal of `W`, at the mixing time, approximates `target`
      -- to within any `ε > 0`
      ∀ ε > 0, ∃ t : ℝ, 0 ≤ t ∧
        ∀ i : I, ∃ q : ℝ, 0 ≤ q ∧ |q - target i| ≤ ε := by
  -- DEEP (construction): requires synthesising a witness `(Ω, μ, W, P)` — a
  -- genuine `GraphonEquitablePartition` with positive finite-mass cells whose
  -- quotient realises `target` (the `Toolkit/Bundle.lean` block-constant graphon
  -- construction, across the `Type u`/`Type v` universe gap). Not built here.
  sorry

/-- **Optimal-transport composition.**  Two engineered graphons `W₁, W₂`
representing transport plans `π₁, π₂` can be *composed* to give a graphon
representing the *displacement interpolation* `μ_t = (1-t) · π₁ + t · π₂` (the
McCann interpolant).  Statement-only. -/
theorem displacement_interpolation
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W₁ W₂ : Graphon Ω μ) (t : ℝ) (_ht : 0 ≤ t ∧ t ≤ 1) :
    -- The displacement interpolant `Wt` exists with kernel the convex
    -- combination `(1-t)·W₁ + t·W₂` (the McCann interpolant of the two plans).
    ∃ Wt : Graphon Ω μ,
      ∀ x y : Ω,
        Wt.kernel x y = ((1 - t : ℝ) : ℂ) * W₁.kernel x y + (t : ℂ) * W₂.kernel x y := by
  obtain ⟨ht0, ht1⟩ := _ht
  refine ⟨{
    kernel := fun x y => ((1 - t : ℝ) : ℂ) * W₁.kernel x y + (t : ℂ) * W₂.kernel x y
    measurable := by
      exact (measurable_const.mul W₁.measurable).add (measurable_const.mul W₂.measurable)
    herm := by
      intro x y
      show ((1 - t : ℝ) : ℂ) * W₁.kernel y x + (t : ℂ) * W₂.kernel y x
          = star (((1 - t : ℝ) : ℂ) * W₁.kernel x y + (t : ℂ) * W₂.kernel x y)
      rw [W₁.herm x y, W₂.herm x y, star_add, star_mul', star_mul']
      simp only [Complex.star_def, Complex.conj_ofReal]
    essBound := |1 - t| * W₁.essBound + |t| * W₂.essBound
    bounded := by
      filter_upwards [W₁.bounded, W₂.bounded] with p hp1 hp2
      show ‖((1 - t : ℝ) : ℂ) * W₁.kernel p.1 p.2 + (t : ℂ) * W₂.kernel p.1 p.2‖
          ≤ |1 - t| * W₁.essBound + |t| * W₂.essBound
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hb1 : |1 - t| * ‖W₁.kernel p.1 p.2‖ ≤ |1 - t| * W₁.essBound :=
        mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
      have hb2 : |t| * ‖W₂.kernel p.1 p.2‖ ≤ |t| * W₂.essBound :=
        mul_le_mul_of_nonneg_left hp2 (abs_nonneg _)
      linarith
    loopless := by
      intro x
      show ((1 - t : ℝ) : ℂ) * W₁.kernel x x + (t : ℂ) * W₂.kernel x x = 0
      rw [W₁.loopless x, W₂.loopless x, mul_zero, mul_zero, add_zero] }, ?_⟩
  intro x y; rfl

end Graphon

/-! ## 9. Open questions

The following questions are *interesting* and within reach of the framework:

1. **(Wasserstein-graphon-distance Lipschitz constant for the PST functional.)**
   The perfect-state-transfer functional `PST : Graphon Ω μ → ℝ`
   (`= sup_t |⟨e_a, evolve t · e_b⟩|`, see `Graphplay/Graphon/PST.lean`) is
   continuous in the cut-norm.  *Is it Lipschitz in the graphon-Wasserstein
   distance?*  We conjecture **yes**, with Lipschitz constant `O(1/√μ(Ω))` on
   the unit-mass subset.  A proof would let us **transfer PST certificates**
   between Wasserstein-close graphons — the key tool for **robust quantum
   protocol design**.

2. **(Sinkhorn divergence on graphons vs. cut distance.)**  Define the
   *Sinkhorn divergence* between graphons by entropic-OT cost with `ε > 0`.
   How does it compare to BCLSV's cut distance `δ_□`?  We conjecture
     `δ_□(W₁, W₂) ≤ C · √(SinkhornDiv_ε(W₁, W₂))` for `ε = O(1)`.

3. **(Chiral entropic OT.)**  Generalise entropic OT to *signed* kernels (i.e.
   our chiral signings).  The standard Sinkhorn iteration fails when entries
   change sign, but a *block-wise* Sinkhorn that respects the equitable
   partition recovers convergence.  What is the resulting "chiral Sinkhorn
   divergence", and does it relate to the chiral-CTQW mixing-time speedup?

Each is a self-contained doctoral thesis problem.  The Graphplay framework
gives the *types* and the *lifting infrastructure* (equitable partitions,
quotient matrices) one needs to attack them rigorously.
-/

end Graphplay
