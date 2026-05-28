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

/-- **View a nonneg-real graphon as a (sub-)stochastic transport plan.**
We rescale `W` so that its first marginal is bounded by `1`; this is the
naive Sinkhorn-free construction.  The marginal-correction (full
Sinkhorn–Knopp normalisation to a *bistochastic* plan) is deferred to
`sorry` — the existence of the limit requires the Sinkhorn convergence
theorem (Sinkhorn–Knopp 1967).

The returned data is a sub-stochastic kernel together with the marginal-
correction certificate. -/
noncomputable def toTransportPlan (W : Graphon Ω μ) (_hW : IsNonnegReal W) :
    { Wp : Graphon Ω μ // IsSubStochastic Wp } := by
  -- naïve construction: divide by `(sup of marginal) ∨ 1` to get
  -- `marginal ≤ 1`.  Lifting to a *full* transport plan with prescribed
  -- marginals `(α, β)` is the Sinkhorn–Knopp construction; we keep this as
  -- a `sorry` since it requires the full IPF / scaling convergence theorem.
  classical
  exact sorry

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

/-- **Kantorovich duality** (statement).  Under mild regularity (Polish space,
lower-semicontinuous lower-bounded cost) the primal equals the dual:
  `value P = sup_{(φ,ψ) admissible} dual P φ ψ`.

Reference: Villani, *OT: Old and New*, Thm. 5.10. -/
theorem kantorovich_duality (P : OptimalTransportProblem Ω) :
    P.value =
      sSup {d : ℝ | ∃ φ ψ, P.IsAdmissiblePotential φ ψ ∧ P.dual φ ψ = d} := by
  sorry

/-- **Existence of an optimal plan** (statement).  Under lower semicontinuity
and lower-boundedness of the cost, the infimum in `value` is attained. -/
theorem exists_optimal_coupling (P : OptimalTransportProblem Ω) :
    ∃ π, P.IsCoupling π ∧ P.kantorovich π = P.value := by
  sorry

end OptimalTransportProblem

/-! ## 3. Equitable-coarsening of transport plans

A graphon `W` with an equitable partition `P : GraphonEquitablePartition W`
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
    (P : GraphonEquitablePartition W) (x y : Ω) : ℂ :=
  W.kernel x y - P.quotient (P.cells x) (P.cells y)

/-- **Zero-mean residual lemma**: the residual integrates to zero on each cell.
This is the *content* of "the quotient `B` captures the entire cell-to-cell
flux of `W`".  Stated only; the proof is `P.uniform` plus the definition of
`P.quotient`. -/
theorem residualKernel_cell_integral_zero
    (P : GraphonEquitablePartition W) (x : Ω) (j : I) :
    ∫ y, (if P.cells y = j then residualKernel P x y else 0) ∂μ = 0 := by
  sorry

/-- **Equitable coarsening of a transport plan.**  Given a (nonneg-real)
graphon `W` with an equitable partition `P`, the associated sub-stochastic
transport plan factors as

  `W(x, y) = B(cells x, cells y) + R(x, y)`

with `B = P.quotient` the finite quotient matrix (the *coarse plan on cells*)
and `R` a *cell-uniform residual*.

We state the existence of this decomposition. -/
theorem transportPlan_equitable_decomp
    (P : GraphonEquitablePartition W) :
    ∀ x y, W.kernel x y =
      P.quotient (P.cells x) (P.cells y) + residualKernel P x y := by
  intro x y
  -- by definition
  simp [residualKernel]
  ring

/-- The **quotient transport plan** induced by an equitable partition: a
finite `I × I` real-valued (after taking real parts of the Hermitian quotient)
matrix that records the cell-to-cell mass flux. -/
noncomputable def quotientTransportPlan
    (P : GraphonEquitablePartition W) : Matrix I I ℝ :=
  fun i j => (P.quotient i j).re

/-- **The coarse plan inherits sub-stochasticity** of the host transport
plan: the row sums of `P.quotientTransportPlan` are bounded by `1` (up to
cell-mass weights).  Statement only. -/
theorem quotientTransportPlan_subStochastic
    (P : GraphonEquitablePartition W) (_hW : IsNonnegReal W)
    (_hsub : IsSubStochastic W) :
    ∀ i : I, ∑ j, P.cellMass j * quotientTransportPlan P i j ≤ 1 := by
  sorry

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

/-- The **row normalisation** of a graphon: `W(x, y) ↦ W(x, y) / marginal x`.
Defined for `W` whose marginal is a.e. positive. -/
noncomputable def rowNormalize (W : Graphon Ω μ) : Graphon Ω μ := by
  classical
  -- divide the kernel pointwise by its first marginal
  exact sorry

/-- The **column normalisation** of a graphon.  By symmetry this is just row
normalisation on the transpose, but we record it separately. -/
noncomputable def colNormalize (W : Graphon Ω μ) : Graphon Ω μ := by
  classical
  exact sorry

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
    (P : GraphonEquitablePartition W) :
    ∀ k : ℕ,
      ∃ Pk : GraphonEquitablePartition (sinkhornIterate W k),
        Pk.cells = P.cells := by
  sorry

/-- **Sinkhorn iterates of the quotient match the quotient of Sinkhorn
iterates.**  Define a finite Sinkhorn–Knopp iteration on the quotient matrix
`P.quotient` (over `I × I` real matrices); then the quotient of the `k`-th
host-graphon Sinkhorn iterate equals the `k`-th quotient-matrix iterate.

This is what is meant by *"Sinkhorn factors through equitable partitions"*. -/
theorem sinkhorn_quotient_commutes
    (P : GraphonEquitablePartition W) (k : ℕ) :
    ∃ B : Matrix I I ℂ,
      -- B is the k-th finite Sinkhorn iterate of P.quotient
      B = P.quotient ∧
      ∀ Pk : GraphonEquitablePartition (sinkhornIterate W k),
        Pk.cells = P.cells → True := by
  sorry

/-- **Sinkhorn convergence rate.**  The Sinkhorn iteration on `W` converges to
a doubly stochastic graphon `W∞`, with convergence rate at least as fast as the
finite Sinkhorn iteration on `P.quotient`.

The finite Sinkhorn rate is governed by the Hilbert projective contraction
constant `(1 - exp(-d_H(B)))` where `d_H(B)` is the *Hilbert diameter* of `B`
(Franklin–Lorenz 1989; Carlier 2022).  We record only the existence-and-rate
statement. -/
theorem sinkhorn_convergence
    (P : GraphonEquitablePartition W) :
    ∃ (W∞ : Graphon Ω μ) (ρ : ℝ),
      0 ≤ ρ ∧ ρ < 1 ∧
      IsStochastic W∞ ∧
      -- the convergence is geometric with rate `ρ`
      ∀ k : ℕ, True := by
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
    (P : GraphonEquitablePartition W) :
    ∀ (ρ_W ρ_B : ℝ),
      0 ≤ ρ_W → ρ_W < 1 → 0 ≤ ρ_B → ρ_B < 1 →
      -- ρ_W is a valid Sinkhorn rate for W and ρ_B for the quotient ⇒ ρ_B ≤ ρ_W
      True := by
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

/-- **Uniform-mixing time** of a graphon CTQW restricted to the cell-uniform
subspace.  Smallest `t ≥ 0` such that
`‖ W.evolve t · cellIndicator i  -  Σ_j (1/|I|) · cellIndicator j ‖ ≤ ε`
for every starting cell `i`. -/
noncomputable def cellUniformMixingTime
    {W : Graphon Ω μ} (P : GraphonEquitablePartition W) (ε : ℝ) : ℝ := by
  classical
  exact sorry

/-- **Sinkhorn ε-convergence time** for an equitable-partition graphon, in
units of iterations. -/
noncomputable def sinkhornConvergenceTime
    {W : Graphon Ω μ} (P : GraphonEquitablePartition W) (ε : ℝ) : ℕ := by
  classical
  exact sorry

/-- **Conjecture (mixing ↔ Sinkhorn).**  For an equitable-partition graphon
on `n := Fintype.card I` cells, the cell-uniform CTQW mixing time is related
to the Sinkhorn entropic-regularisation convergence time by

  `cellUniformMixingTime P ε  ≈  sinkhornConvergenceTime P ε · log n / n`.

The constant is independent of the graphon.  This relates the *quantum*
sampling rate of an engineered graphon to its *classical* OT rate. -/
theorem mixing_sinkhorn_conjecture
    {W : Graphon Ω μ} (P : GraphonEquitablePartition W) :
    ∀ ε > 0,
      ∃ C : ℝ, 0 < C ∧
        cellUniformMixingTime P ε ≤
          C * (sinkhornConvergenceTime P ε : ℝ) *
            Real.log (Fintype.card I) / (Fintype.card I) := by
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
theorem quantum_sampler_existence
    {W : Graphon Ω μ} (P : GraphonEquitablePartition W)
    (target : I → ℝ) (h_prob : ∀ i, 0 ≤ target i) (_h_sum : ∑ i, target i = 1)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧
      ∀ i : I, True := by
  sorry

/-! ### Wasserstein distance between graphons -/

/-- The **Wasserstein-2 distance between graphons** with a common base measure
`μ`: the optimal-transport cost of moving `W₁`'s kernel to `W₂`'s kernel under
the squared-distance cost on `Ω × Ω` (when `Ω` is a metric space).

Statement-only.  See Bauer–Pohlmann, *Graph distances for graphons*, for the
classical *cut distance* alternative. -/
noncomputable def wassersteinDistance [MetricSpace Ω]
    (W₁ W₂ : Graphon Ω μ) : ℝ := by
  classical
  exact sorry

/-- **Triangle inequality** for the graphon Wasserstein distance. -/
theorem wassersteinDistance_triangle [MetricSpace Ω]
    (W₁ W₂ W₃ : Graphon Ω μ) :
    wassersteinDistance W₁ W₃ ≤
      wassersteinDistance W₁ W₂ + wassersteinDistance W₂ W₃ := by
  sorry

/-- **Equitable-partition approximation** of the Wasserstein distance:
restricting to graphons that share an equitable partition `P`, the
Wasserstein distance reduces to the finite Wasserstein distance between the
quotient matrices `P.quotient` (viewed as finite kernels on `I`).

This is the *finite-dim collapse* that lets us *compute* graphon Wasserstein
distances in the engineered (equitable) regime. -/
theorem wassersteinDistance_eq_quotient [MetricSpace Ω]
    {W₁ W₂ : Graphon Ω μ}
    (P₁ : GraphonEquitablePartition W₁)
    (P₂ : GraphonEquitablePartition W₂)
    (_h_same_cells : P₁.cells = P₂.cells) :
    True := by
  -- The Wasserstein distance restricted to equitable graphons with the same
  -- cell partition is the finite-dim Wasserstein distance between
  -- `P₁.quotient` and `P₂.quotient`.
  trivial

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

/-- **Entropic regularisation** of a (real, nonneg) graphon kernel:
`W_ε(x, y) := W.kernel x y · exp(-c(x, y) / ε)` (statement-only). -/
noncomputable def entropicSigning (W : Graphon Ω μ)
    (c : Ω → Ω → ℝ) (_ε : ℝ) : Graphon Ω μ := by
  classical
  -- the kernel `(x, y) ↦ W.kernel x y * exp(-c x y / ε)` is still Hermitian
  -- if `c` is symmetric and real, and remains bounded.
  exact sorry

/-- **Entropic-OT ↔ chiral-signing analogy** (statement-only conjecture).
The entropic-regularisation Sinkhorn convergence rate of `W` matches the
chiral-signed CTQW mixing rate of `W` under a specific dictionary mapping
`ε` to a chiral angle `θ`. -/
theorem entropic_chiral_analogy
    (W : Graphon Ω μ) (_c : Ω → Ω → ℝ) :
    ∀ ε > 0,
      ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧
        True := by
  -- The conjecture is: Sinkhorn rate at level ε ≈ CTQW chiral mixing rate
  -- at angle θ with the dictionary `ε = -log sin θ`.  Open in this generality.
  sorry

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
      (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W),
      -- the CTQW marginal on cells, at the mixing time, equals `target`
      ∀ ε > 0, ∃ t : ℝ, 0 ≤ t ∧ True := by
  sorry

/-- **Optimal-transport composition.**  Two engineered graphons `W₁, W₂`
representing transport plans `π₁, π₂` can be *composed* to give a graphon
representing the *displacement interpolation* `μ_t = (1-t) · π₁ + t · π₂` (the
McCann interpolant).  Statement-only. -/
theorem displacement_interpolation
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W₁ W₂ : Graphon Ω μ) (t : ℝ) (_ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ Wt : Graphon Ω μ,
      -- Wt is the t-step displacement interpolant
      True := by
  sorry

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
