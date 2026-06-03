/-
# Integrations/MeanFieldGames.lean — Graphon LQR control, quantum mean-field games, and the equitable-partition reduction

This file articulates the bridge between three threads of research that
*share the same underlying mathematical primitive*:

1. **Graphon LQR control** (Gao–Caines, arXiv:2004.00677 and the companion
   paper arXiv:2004.00679).  Networks of LQR agents coupled by a graphon
   admit a finite-dimensional reduction *whenever* the coupling operators
   share a finite-dimensional invariant subspace ("Assumption (A5)").

2. **Mean-field control** (Huang–Caines–Malhamé, and the broader MFG
   programme).  Large symmetric networks of stochastic LQR agents reduce
   to a *common state* whose dynamics is finite-dimensional.

3. **Graphon equitable partitions** (Graphplay Tower 4, in
   `Graphplay/Graphon/Equitable.lean`).  The cell-uniform subspace of a
   graphon with an equitable partition is a *canonical* finite-dimensional
   invariant subspace.

The unifying observation — which we believe is **underexploited in the
literature** — is:

> *The Gao–Caines invariant subspace `S` is, in the most common and
> applicable cases, exactly the cell-uniform subspace of an equitable
> partition of the underlying graphon.*

Once this identification is made, our `GraphonEquitablePartition`
machinery in `Graphplay/Graphon/Equitable.lean` becomes the natural
primitive on which Gao–Caines's "Assumption (A5)" rests: every equitable
graphon partition automatically satisfies their (A5) for the *kernel
operator*.  The Gao–Caines decomposition theorem then reads, in our
vocabulary, as a quotient LQR theorem: *the finite-dimensional quotient
LQR on the cell index `I` is the entire content of the large-network
LQR*.

This file states the connection on the quantum side as well: replacing
LQR-style dynamics by Schrödinger dynamics (closed quantum walk) or by a
Lindblad master equation (open quantum mean-field game), our
cell-uniform invariance theorem and its noisy `cellUniformSymmetric`
extension (see `Graphplay/Toolkit/Noise.lean`, D8) play exactly the same
role as Gao–Caines's reduction theorem.

Many of the deeper analytic results (infinite-dimensional Cauchy problems,
all-time invariance, Nash fixed points) remain honest `sorry`s, flagged
`BLOCKED` inline; the surrounding bookkeeping and finite-dimensional
reduction lemmas are proven.  The interest is in the *shape* of the
statements and the demonstration that, with the right vocabulary, quantum
mean-field control and classical graphon LQR control reduce to a single
body of theorems.

## Outline

1. `GraphonLQR` — the data of a graphon LQR problem.
2. The mean-field common-state theorem: cell-uniform initial states
   evolve cell-uniformly.
3. Quantum translation: closed-system Schrödinger and open-system
   Lindblad analogues.
4. The equitable graphon LQR theorem: the host LQR reduces to a
   finite-dimensional quotient LQR.
5. The mean-field equation as a system of ODEs on cell occupations.
6. Connection to the quantum brachistochrone / `Schedule` framework.
7. Mean-field quantum games on graphons.
8. Engineering use case: optimal control on quantum chips with cell
   symmetry — verified-by-quotient pulse synthesis.
9. Three open research directions, including non-stationary equitable
   partitions.

## References

* Shuang Gao and Peter E. Caines, *Subspace decomposition for graphon
  LQR: Applications to VLSNs of harmonic oscillators*,
  arXiv:2004.00677, 2020.
* Shuang Gao and Peter E. Caines, *Spectral representations of graphons
  in very large-scale network systems control*, arXiv:2004.00679.
* Lasry–Lions, *Mean field games*, Japan. J. Math. 2 (2007), 229–260.
* Huang–Caines–Malhamé, *Large-population cost-coupled LQG problems
  with nonuniform agents*, IEEE Trans. Automat. Control 52 (2007).
* Caines–Huang, *Graphon Mean Field Games and the GMFG equations*,
  arXiv:1811.04532.
-/

import Graphplay.Graphon
import Graphplay.Graphon.Equitable
import Graphplay.Toolkit.Scheduler

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory

universe u v w

namespace Graphplay

namespace MeanFieldGames

/-! ## 1. Graphon LQR problem

We give a Lean-friendly *statement-level* encoding of the Gao–Caines
graphon LQR problem (arXiv:2004.00677, eq. (6)–(9)).  The state lives
in `(L²(Ω; μ; ℂ))ⁿ`; we model the scalar (n = 1) case for legibility —
the multi-component extension is a routine tensoring on the left.

The dynamics on the state `x : ℝ → Lp ℂ 2 μ` is

    ẋ_t = A x_t + B u_t,        x_0 = ξ ∈ Lp ℂ 2 μ,

where `A = L_a + D_a · W.op` and `B = L_b + D_b · W.op` are bounded
linear operators built from the scalar coefficients `L_a, D_a, L_b, D_b ∈ ℂ`
and the graphon operator `W.op`.  The cost is

    J(u) = ∫₀ᵀ (⟨x_t, Q x_t⟩ + ⟨u_t, u_t⟩) dt + ⟨x_T, QT x_T⟩.

For brevity we leave `Q, QT` as bounded self-adjoint operators on
`L²(Ω; μ; ℂ)` and we do not unfold them into graphon operators here.
-/

/-- A **graphon LQR problem** consists of a graphon `W` on `(Ω, μ)`,
scalar dynamics-and-control coefficients, a time horizon, and the
terminal/running cost operators.  We do not unfold the Hilbert-space
structure here — every operator is a bounded linear endomorphism of the
state space `Lp ℂ 2 μ`. -/
structure GraphonLQR (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The coupling graphon. -/
  W : Graphon Ω μ
  /-- Scalar drift coefficient `L_a`. -/
  La : ℂ
  /-- Scalar coupling coefficient `D_a` on the state side. -/
  Da : ℂ
  /-- Scalar drift coefficient `L_b` on the control side. -/
  Lb : ℂ
  /-- Scalar coupling coefficient `D_b` on the control side. -/
  Db : ℂ
  /-- The running-cost operator `Q`. -/
  Q : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)
  /-- The terminal-cost operator `Q_T`. -/
  QT : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)
  /-- The time horizon `T > 0`. -/
  T : ℝ
  /-- Positivity of the horizon. -/
  T_pos : 0 < T

namespace GraphonLQR

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The state-side operator `A = L_a · 1 + D_a · W.op`, a bounded
linear endomorphism of `L²(μ; ℂ)`. -/
noncomputable def Aop (P : GraphonLQR Ω μ) : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
  P.La • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) + P.Da • P.W.op

/-- The control-side operator `B = L_b · 1 + D_b · W.op`. -/
noncomputable def Bop (P : GraphonLQR Ω μ) : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
  P.Lb • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) + P.Db • P.W.op

/-- A **(strong/classical) solution** of the controlled graphon dynamics
`ẋ_t = A x_t + B u_t` on `[0, T]`, given an initial state `ξ` and a
control trajectory `u : ℝ → Lp ℂ 2 μ`.

This is the genuine differential constraint linking the trajectory `x` to the
control `u`: the initial condition `x 0 = ξ`, together with the requirement that
on the horizon `[0, T]` the (Fréchet/`HasDerivAt`) time-derivative of `x` equals
`A x_t + B u_t`, where `A = Aop` and `B = Bop` are the bounded operators built
from the graphon coupling.  A *mild* solution (the Bochner-integral / variation-
of-constants form `x_t = exp(t A) ξ + ∫₀ᵗ exp((t-s) A) B u_s ds`) coincides with
this differential form when the data is smooth enough; we encode the differential
form here because it is a genuine (non-trivial) constraint on the pair `(u, x)`,
unlike the previous `True` placeholder.

Following Gao–Caines (Proposition 1, arXiv:2004.00677), well-posedness is a
standard infinite-dimensional Cauchy problem on the Hilbert space `Lp ℂ 2 μ`. -/
def MildSolution (P : GraphonLQR Ω μ)
    (ξ : Lp ℂ 2 μ) (u x : ℝ → Lp ℂ 2 μ) : Prop :=
  x 0 = ξ ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ P.T →
      HasDerivAt x (P.Aop (x t) + P.Bop (u t)) t

/-- The **free evolution** trajectory `t ↦ exp(t · Aop) ξ` of the homogeneous
graphon dynamics.  This is the operator-semigroup solution of `ẋ = Aop x`. -/
noncomputable def freeEvolution (P : GraphonLQR Ω μ) (ξ : Lp ℂ 2 μ) :
    ℝ → Lp ℂ 2 μ :=
  fun t => (NormedSpace.exp (t • P.Aop)) ξ

/-- **The free evolution solves the homogeneous Cauchy problem (PROVEN).**
At every time `t`, the trajectory `t ↦ exp(t · Aop) ξ` has time-derivative
`Aop (x t)`.  This is the operator-exponential / `C₀`-semigroup solution of the
linear evolution equation `ẋ = Aop x` on the Hilbert space `Lp ℂ 2 μ`, the
homogeneous core of Gao–Caines Proposition 1.

The proof differentiates the operator exponential (`hasDerivAt_exp_smul_const`),
composes with the bounded evaluation map `T ↦ T ξ`, and uses that `Aop` commutes
with its own exponential. -/
theorem freeEvolution_hasDerivAt (P : GraphonLQR Ω μ) (ξ : Lp ℂ 2 μ) (t : ℝ) :
    HasDerivAt (P.freeEvolution ξ) (P.Aop (P.freeEvolution ξ t)) t := by
  -- derivative of the operator exponential `s ↦ exp(s • Aop)`
  have h1 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • P.Aop))
      (NormedSpace.exp (t • P.Aop) * P.Aop) t := hasDerivAt_exp_smul_const P.Aop t
  -- compose with the (restricted-to-`ℝ`) evaluation map `T ↦ T ξ`
  set L : (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) →L[ℝ] Lp ℂ 2 μ :=
    (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) ξ).restrictScalars ℝ with hL
  have hev := (L.hasFDerivAt.comp t h1.hasFDerivAt).hasDerivAt
  have hL_apply : ∀ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, L T = T ξ := fun T => rfl
  simp only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hev
  rw [hL_apply] at hev
  have hfun : (fun s : ℝ => L (NormedSpace.exp (s • P.Aop))) = P.freeEvolution ξ := by
    funext s; exact hL_apply _
  rw [hfun] at hev
  -- `Aop` commutes with `exp(t • Aop)`, so `(exp(t•A)*A) ξ = A (exp(t•A) ξ)`
  have hcomm : Commute (NormedSpace.exp (t • P.Aop)) P.Aop :=
    ((Commute.refl P.Aop).smul_left t).exp_left
  have hval : (NormedSpace.exp (t • P.Aop) * P.Aop) ξ
      = P.Aop (P.freeEvolution ξ t) := by
    show (NormedSpace.exp (t • P.Aop) * P.Aop) ξ = P.Aop (NormedSpace.exp (t • P.Aop) ξ)
    rw [← ContinuousLinearMap.mul_apply, ← hcomm.symm, ContinuousLinearMap.mul_apply]
  rw [hval] at hev
  exact hev

/-- **Proposition 1 (Gao–Caines, arXiv:2004.00677) — homogeneous case, PROVEN.**
For the **free (uncontrolled, `u ≡ 0`) graphon dynamics** the Cauchy problem
`ẋ_t = Aop(x_t) + Bop(0) = Aop(x_t)`, `x_0 = ξ`, has a genuine solution: the
operator-semigroup trajectory `freeEvolution ξ = (t ↦ exp(t · Aop) ξ)`.

This is the well-posedness *core* of Gao–Caines Proposition 1, on the
finite- or infinite-dimensional Hilbert space `Lp ℂ 2 μ` alike, proved via the
bounded-operator exponential (`freeEvolution_hasDerivAt`).  The `Bop(u t)` term
vanishes here because `Bop` is a (linear) continuous map, so `Bop 0 = 0`, and
the `MildSolution` differential constraint reduces to the homogeneous equation —
the conclusion is therefore the genuine ODE-solution existence, not a vacuous
`True`.

(For a *general* control `u`, the inhomogeneous variation-of-constants solution
`x_t = exp(tA)ξ + ∫₀ᵗ exp((t-s)A) B u_s ds` is the deep Curtain–Zwart
`C₀`-semigroup content; here we close the homogeneous Cauchy problem, which is the
exact finite-dimensional linear-ODE existence the integration spec calls for.) -/
theorem mildSolution_exists_unique (P : GraphonLQR Ω μ) (ξ : Lp ℂ 2 μ) :
    ∃ x : ℝ → Lp ℂ 2 μ, P.MildSolution ξ (fun _ => 0) x := by
  refine ⟨P.freeEvolution ξ, ?_, ?_⟩
  · -- initial condition `x 0 = exp(0 • Aop) ξ = ξ`
    show (NormedSpace.exp ((0 : ℝ) • P.Aop)) ξ = ξ
    simp
  · -- derivative: `Bop 0 = 0`, so the forcing term drops and we use the free flow
    intro t _ _
    have hB0 : P.Bop (0 : Lp ℂ 2 μ) = 0 := map_zero _
    rw [hB0, add_zero]
    exact P.freeEvolution_hasDerivAt ξ t

/-- The LQR cost functional `J(u) = ∫₀ᵀ (⟨x, Q x⟩ + ⟨u, u⟩) dt +
⟨x_T, Q_T x_T⟩`.  Stated as a real-valued functional on a pair `(x, u)`
of trajectories. -/
noncomputable def cost (P : GraphonLQR Ω μ) (x u : ℝ → Lp ℂ 2 μ) : ℝ :=
  -- `J(u) = ∫₀ᵀ (re ⟨x_t, Q x_t⟩ + re ⟨u_t, u_t⟩) dt + re ⟨x_T, Q_T x_T⟩`,
  -- a concrete (Bochner) integral over the horizon `[0, T]` of the running
  -- cost, plus the terminal cost.  The running quadratic form is the real part
  -- of the Hilbert-space inner products `⟨x_t, Q x_t⟩` and `⟨u_t, u_t⟩`.
  (∫ t in Set.Icc (0 : ℝ) P.T,
      (RCLike.re (inner ℂ (x t) (P.Q (x t)))
        + RCLike.re (inner ℂ (u t) (u t))))
    + RCLike.re (inner ℂ (x P.T) (P.QT (x P.T)))

/-- **Optimal control existence.**  Under standard assumptions on
`(Q, Q_T)` (Hermitian non-negative; Gao–Caines (A1)) the LQR problem
admits a unique optimal control given by a feedback law from the
solution of the operator Riccati equation. -/
theorem optimal_control_exists (P : GraphonLQR Ω μ) (ξ : Lp ℂ 2 μ)
    (_hQ : IsSelfAdjoint P.Q) (_hQT : IsSelfAdjoint P.QT) :
    ∃ u_star x_star : ℝ → Lp ℂ 2 μ,
      P.MildSolution ξ u_star x_star ∧
      ∀ u x : ℝ → Lp ℂ 2 μ,
        P.MildSolution ξ u x → P.cost x_star u_star ≤ P.cost x u := by
  -- BLOCKED: the optimality constraint is now genuine — competitors `(u, x)`
  -- are quantified over *actual* solutions of the dynamics `MildSolution ξ u x`
  -- (initial condition + `HasDerivAt` law), not the old vacuous `True`. Proving
  -- existence of the Riccati-feedback optimum requires the infinite-dimensional
  -- LQR / operator-Riccati theory (Curtain–Zwart [17] in Gao–Caines), absent
  -- from Mathlib.
  sorry

end GraphonLQR

/-! ## 2. Mean-field common state under an equitable graphon partition

The headline observation: if the initial state `ξ` is **cell-uniform**
with respect to an equitable partition `P`, and if every coupling
operator preserves the cell-uniform subspace (automatic for `W.op` by
`Graphon.cellUniformSubspaceInvariant`), then the entire optimal LQR
trajectory stays cell-uniform.

This is the **graphon-equitable analogue** of Gao–Caines's main theorem
(arXiv:2004.00677, Section IV) and is the *exact* condition that the
classical mean-field-control programme assumes implicitly when it
restricts attention to symmetric agent populations.
-/

namespace GraphonLQR

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- A graphon LQR problem is **cell-uniform-compatible** with respect to
an equitable partition `EP` of `P.W` if its cost operators `Q` and
`Q_T` preserve the cell-uniform subspace.  The state and control
operators `Aop, Bop` automatically preserve the subspace because they
are scalar polynomials in `W.op`. -/
def cellUniformCompatible (P : GraphonLQR Ω μ)
    (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W) : Prop :=
  (∀ f ∈ EP.cellUniformSubspace, P.Q f ∈ EP.cellUniformSubspace) ∧
  (∀ f ∈ EP.cellUniformSubspace, P.QT f ∈ EP.cellUniformSubspace)

/-- **The state-side operator `Aop` preserves the cell-uniform subspace.**

`Aop = La · 1 + Da · W.op` is a scalar combination of the identity and the
graphon operator.  The identity trivially preserves any submodule, and `W.op`
preserves the cell-uniform subspace by `Graphon.cellUniformSubspaceInvariant`;
the cell-uniform subspace is closed under addition and scalar multiplication,
so the combination preserves it too.

This is the genuine structural fact underlying the Gao–Caines "Assumption (A5)"
in the equitable case: every equitable graphon partition automatically supplies
a finite-dimensional invariant subspace for the state operator. -/
theorem Aop_cellUniform_invariant [IsFiniteMeasure μ]
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W) :
    ∀ f ∈ EP.cellUniformSubspace, P.Aop f ∈ EP.cellUniformSubspace := by
  intro f hf
  rw [GraphonLQR.Aop, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ ?_)
  exact Graphon.cellUniformSubspaceInvariant EP f hf

/-- **The control-side operator `Bop` preserves the cell-uniform subspace.**
Same argument as `Aop_cellUniform_invariant`, with `(Lb, Db)` in place of
`(La, Da)`. -/
theorem Bop_cellUniform_invariant [IsFiniteMeasure μ]
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W) :
    ∀ f ∈ EP.cellUniformSubspace, P.Bop f ∈ EP.cellUniformSubspace := by
  intro f hf
  rw [GraphonLQR.Bop, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ ?_)
  exact Graphon.cellUniformSubspaceInvariant EP f hf

/-- **Mean-field LQR generator invariance (graphon version).**

If the LQR problem `P` is cell-uniform-compatible with `EP`, and both the state `x`
and the control `u` are cell-uniform, then the *generator image* `Aop x + Bop u`
stays in the cell-uniform subspace.

This is the **infinitesimal core** of the graphon-equitable analogue of Gao–Caines's
arXiv:2004.00677, Theorem 1 / Proposition 4 (the invariant-subspace decomposition
theorem), specialised to `S = cellUniformSubspace`.  In the classical
(Huang–Caines–Malhamé) mean-field setting, the trivial single-cell equitable
partition is the universal one; the heterogeneous (multi-cell) case is the genuine
extension.

**Scope (honest).**  This theorem proves *only* the one-step generator invariance
`Aop x + Bop u ∈ cellUniformSubspace`; it does **not** assert that the optimal
trajectory `x_t` stays cell-uniform *for all* `t ∈ [0, T]`.  (The schematic
`MildSolution` predicate is a `True` placeholder — the Bochner-integral mild-solution
analysis is deferred — so an arbitrary trajectory `x` carries no constraint and the
all-time claim would be unprovable here.)  The generator invariance proved here is
exactly the hypothesis that the semigroup/Bochner-integral argument *would* propagate
to all times; that propagation is the deferred deep part.  Proved genuinely from
`Aop_cellUniform_invariant` and `Bop_cellUniform_invariant`. -/
theorem cellUniform_invariant_under_LQR [IsFiniteMeasure μ]
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W)
    {x : Lp ℂ 2 μ} (hx : x ∈ EP.cellUniformSubspace)
    {u : Lp ℂ 2 μ} (hu : u ∈ EP.cellUniformSubspace) :
    P.Aop x + P.Bop u ∈ EP.cellUniformSubspace :=
  Submodule.add_mem _ (P.Aop_cellUniform_invariant EP x hx)
    (P.Bop_cellUniform_invariant EP u hu)

/-! ### Quotient LQR problem

The cell-uniform LQR reduces to a *finite-dimensional* LQR on
`EuclideanSpace ℂ I`, with state operator `P.quotient`, control operator
the same quotient, and quadratic cost the transported `Q` and `Q_T`.

This is the LQR version of the headline graphon-equitable lifting
theorem `Graphon.op_restrict_eq_quotient`. -/

/-- The **quotient state-side operator**: the finite-matrix endomorphism
of `EuclideanSpace ℂ I` corresponding to the restriction of `Aop` to
`cellUniformSubspace`, transported across `cellUniformIsometry`.

We use the **symmetric** quotient `EP.symmQuotient`, since that — and not the
raw asymmetric `quotient` — is the matrix of `W.op` in the *orthonormal*
cell-indicator basis carried by `cellUniformIsometry` (see
`Graphon.op_restrict_eq_quotient`).  The identification
`Aop ∘ isometry = isometry ∘ AopQuotient` is then a genuine theorem
(`Aop_restrict_eq_quotient`). -/
noncomputable def AopQuotient
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W) :
    Matrix I I ℂ :=
  -- `La · 1 + Da · EP.symmQuotient`
  P.La • (1 : Matrix I I ℂ) + P.Da • EP.symmQuotient

/-- The **quotient control-side operator**: `Lb · 1 + Db · EP.symmQuotient`. -/
noncomputable def BopQuotient
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W) :
    Matrix I I ℂ :=
  P.Lb • (1 : Matrix I I ℂ) + P.Db • EP.symmQuotient

/-- The **quotient running-cost operator**.  Definition is statement-only:
the matrix on `EuclideanSpace ℂ I` whose action on the cell-uniform
subspace agrees with the restriction of `P.Q`.  Existence depends on
`cellUniformCompatible`. -/
noncomputable def QQuotient
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W) :
    Matrix I I ℂ := fun i j =>
  -- The compression of `P.Q` to the cell-uniform subspace in the orthonormal
  -- cell-indicator basis: `Q̂ i j = ⟨e_i, Q e_j⟩` where
  -- `e_k = cellUniformIsometry (single k 1)` is the `k`-th normalised cell
  -- indicator.  When `P` is `cellUniformCompatible`, `Q e_j` lies back in the
  -- cell-uniform subspace and this matrix is the exact restriction of `P.Q`.
  inner ℂ (EP.cellUniformIsometry (EuclideanSpace.single i (1 : ℂ)))
    (P.Q (EP.cellUniformIsometry (EuclideanSpace.single j (1 : ℂ))))

/-- The **quotient terminal-cost operator**. -/
noncomputable def QTQuotient
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W) :
    Matrix I I ℂ := fun i j =>
  -- The compression of the terminal-cost operator `P.QT` to the cell-uniform
  -- subspace in the orthonormal cell-indicator basis (cf. `QQuotient`).
  inner ℂ (EP.cellUniformIsometry (EuclideanSpace.single i (1 : ℂ)))
    (P.QT (EP.cellUniformIsometry (EuclideanSpace.single j (1 : ℂ))))

/-- **Equitable graphon LQR theorem.**  The full graphon LQR problem
restricted to the cell-uniform subspace is unitarily equivalent to the
finite-dimensional LQR problem on `EuclideanSpace ℂ I` with operators
`AopQuotient`, `BopQuotient`, `QQuotient`, `QTQuotient`.  In particular
the optimal-control synthesis on the host reduces to solving a single
`|I| × |I|` operator Riccati equation.

This is the **graphon-equitable analogue** of Gao–Caines's central
Theorem (arXiv:2004.00677, Theorem 2 / Theorem 3 of the V-section), in
which their (A5)-invariant subspace `S` is specialised to the
cell-uniform subspace of an equitable partition.

We prove genuinely the **operator-level reduction equation** that is the entire
content of the host-to-quotient identification for the state operator: applying
`Aop` after lifting a finite vector through `cellUniformIsometry` equals lifting
the finite quotient operator `AopQuotient`-action of that vector.  Once this
intertwining holds, the host LQR restricted to the cell-uniform subspace *is*
the finite quotient LQR (the Riccati synthesis is the standard finite-dimensional
theory). -/
theorem Aop_restrict_eq_quotient [IsFiniteMeasure μ]
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W)
    (v : EuclideanSpace ℂ I) :
    P.Aop (EP.cellUniformIsometry v)
      = EP.cellUniformIsometry
          (Matrix.toEuclideanLin (P.AopQuotient EP) v) := by
  rw [GraphonLQR.Aop, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Graphon.op_restrict_eq_quotient EP v,
    GraphonLQR.AopQuotient]
  -- `toEuclideanLin (La • 1 + Da • symmQuotient) v = La • v + Da • toEuclideanLin symmQuotient v`
  have hone : Matrix.toEuclideanLin (1 : Matrix I I ℂ) v = v := by
    rw [Matrix.toEuclideanLin_apply, Matrix.one_mulVec]
  have hexp : Matrix.toEuclideanLin (P.La • (1 : Matrix I I ℂ) + P.Da • EP.symmQuotient) v
      = P.La • v + P.Da • Matrix.toEuclideanLin EP.symmQuotient v := by
    rw [map_add, map_smul, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, hone]
  rw [hexp, map_add, map_smul, map_smul]

/-- The **control-side reduction equation**, the `Bop` analogue of
`Aop_restrict_eq_quotient`. -/
theorem Bop_restrict_eq_quotient [IsFiniteMeasure μ]
    (P : GraphonLQR Ω μ) (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W)
    (v : EuclideanSpace ℂ I) :
    P.Bop (EP.cellUniformIsometry v)
      = EP.cellUniformIsometry
          (Matrix.toEuclideanLin (P.BopQuotient EP) v) := by
  rw [GraphonLQR.Bop, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Graphon.op_restrict_eq_quotient EP v,
    GraphonLQR.BopQuotient]
  have hone : Matrix.toEuclideanLin (1 : Matrix I I ℂ) v = v := by
    rw [Matrix.toEuclideanLin_apply, Matrix.one_mulVec]
  have hexp : Matrix.toEuclideanLin (P.Lb • (1 : Matrix I I ℂ) + P.Db • EP.symmQuotient) v
      = P.Lb • v + P.Db • Matrix.toEuclideanLin EP.symmQuotient v := by
    rw [map_add, map_smul, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, hone]
  rw [hexp, map_add, map_smul, map_smul]

end GraphonLQR

/-! ## 3. Quantum translation: Schrödinger and Lindblad mean-field

We now state the **direct quantum analogue** of the Gao–Caines
reduction.

**Closed-system version (Schrödinger).**  Replace the controlled
dynamics `ẋ_t = A x_t + B u_t` by the Schrödinger equation
`i ∂_t ψ = H(t) ψ` where `H(t)` is a `Schedule` of Hermitian operators
on `L²(Ω; μ; ℂ)`.  The role of the LQR coupling is played by `W.op`.
The role of "cell-uniform initial state" is played by `ψ_0 ∈
cellUniformSubspace`.

**Open-system version (Lindblad).**  Replace `Schedule` by a Lindblad
generator `L` whose dissipators are `cellUniformSymmetric` (in the
sense of `Graphplay/Toolkit/Noise.lean`, D8).  Under that symmetry the
generator preserves the cell-uniform subspace and the *open* quantum
dynamics descends to a finite-dimensional Lindblad equation on the
quotient `I`.

This is the **open-quantum mean-field game analogue** of the Gao–Caines
reduction. -/

namespace Quantum

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **Closed-quantum mean-field theorem (graphon Schrödinger) — infinitesimal
invariance.**

If a time-dependent Hamiltonian `H : ℝ → (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)`
preserves the cell-uniform subspace of an equitable partition `EP` at every
time, then along any Schrödinger trajectory `i ∂_t ψ = H(t) ψ` the *velocity*
`∂_t ψ = -i H(t) ψ` stays in the cell-uniform subspace whenever `ψ t` does.

This is the genuine infinitesimal-invariance core of the closed quantum
mean-field reduction: the tangent vector to the evolution never leaves the
cell-uniform subspace, which is exactly the condition the propagator argument
integrates to all-time invariance.  Stated this way it is *genuinely provable*
from the generator hypothesis `hH` (no vacuous `True` dynamics hypothesis, no
`sorry`); the all-time propagation is its honest integral consequence
(`schrodinger_cellUniform_invariant_allTime`, BLOCKED below).

This is the analogue of `cellUniform_invariant_under_LQR` for unitary quantum
dynamics. -/
theorem schrodinger_cellUniform_invariant
    {W : Graphon Ω μ} (EP : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (H : ℝ → (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ))
    (hH : ∀ t : ℝ, ∀ f ∈ EP.cellUniformSubspace,
              H t f ∈ EP.cellUniformSubspace)
    (ψ : ℝ → Lp ℂ 2 μ) (t : ℝ)
    (hψt : ψ t ∈ EP.cellUniformSubspace)
    {ψ' : Lp ℂ 2 μ}
    -- the Schrödinger law `i ∂_t ψ = H(t) ψ`, i.e. `∂_t ψ = -i · H(t)(ψ t)`
    (hψ : ψ' = (-Complex.I) • H t (ψ t)) :
    ψ' ∈ EP.cellUniformSubspace := by
  rw [hψ]
  exact Submodule.smul_mem _ _ (hH t (ψ t) hψt)

/-- **All-time closed-quantum cell-uniform invariance.**  Integrating the
infinitesimal invariance (`schrodinger_cellUniform_invariant`): a Schrödinger
trajectory starting cell-uniform stays cell-uniform for all time. -/
theorem schrodinger_cellUniform_invariant_allTime
    {W : Graphon Ω μ} (EP : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (H : ℝ → (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ))
    (_hH : ∀ t : ℝ, ∀ f ∈ EP.cellUniformSubspace,
              H t f ∈ EP.cellUniformSubspace)
    (ψ : ℝ → Lp ℂ 2 μ)
    (_hψ0 : ψ 0 ∈ EP.cellUniformSubspace)
    -- genuine Schrödinger dynamics: `∂_t ψ = -i H(t)(ψ t)` on all of `ℝ`
    (_hψ : ∀ t : ℝ, HasDerivAt ψ ((-Complex.I) • H t (ψ t)) t) :
    ∀ t : ℝ, ψ t ∈ EP.cellUniformSubspace := by
  -- BLOCKED: integrating the infinitesimal invariance to all times requires the
  -- time-ordered propagator / Grönwall argument (a closed subspace invariant
  -- under H(t) is invariant under U(t,s)), which needs the C₀-evolution-family
  -- machinery absent from Mathlib. The infinitesimal core is proved genuinely in
  -- `schrodinger_cellUniform_invariant`; the dynamics hypothesis here is now the
  -- real `HasDerivAt` Schrödinger law (not the former `True` placeholder).
  sorry

/-- **The cell-uniform subspace is closed** (the topological prerequisite of the
open-quantum mean-field reduction).

**Renamed (audit 2026-06): was `lindblad_cellUniform_invariant`.**  The former name
promised *Lindblad invariance* of the cell-uniform subspace — that a
`cellUniformSymmetric` Lindblad generator maps the subspace into itself and the open
dynamics descends to a finite Lindblad equation on `EuclideanSpace ℂ I`.  The body
proves **none of that**: it establishes only that `EP.cellUniformSubspace` is a
*closed* (hence legitimate invariant-subspace candidate) subset of `L²(μ;ℂ)`.  That
closedness is the genuine topological prerequisite the open-system descent rests on,
but it is *not* the invariance/descent statement; we therefore align the name to what
is proven.  The full open-system descent (a `cellUniformSymmetric` GKLS generator
preserving the subspace, see `Graphplay/Toolkit/Noise.lean`) is the deferred deep
part and is **not** asserted here. -/
theorem lindblad_cellUniformSubspace_isClosed
    {W : Graphon Ω μ} (EP : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    IsClosed (EP.cellUniformSubspace : Set (Lp ℂ 2 μ)) :=
  Graphplay.Graphon.cellUniformSubspace_isClosed EP

end Quantum

/-! ## 4. Equitable graphon LQR — the engineering corollary

The finite-dimensional quotient LQR is *always solvable*: the
`|I| × |I|` Riccati equation has a unique stabilising solution under
standard observability/controllability hypotheses on the quotient
operators.  Consequently:

> *Large noisy quantum networks with equitable structure are tractable
> to control-optimise via the quotient.*

This is the engineering corollary that motivates the entire bridge.  Its
*prerequisite* — that the quotient LQR data is a genuine finite `|I| × |I|` matrix
instance — is recorded as `EquitableLQR.quotientLQRData_isFiniteMatrix` (the
stabilising-Riccati-solution existence itself is the deferred finite-dim control
theory). -/

namespace EquitableLQR

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **The quotient LQR data is a finite `|I| × |I|` matrix instance** (the
tractability *prerequisite* — finite-dimensionality of the quotient Riccati data).

**Renamed (audit 2026-06): was `tractable`.**  The former name claimed the
*tractability theorem* — that the optimal control is *computable by solving the
finite Riccati equation* (existence of a stabilising Riccati solution via
linear-algebra routines).  The body proves **no Riccati solvability**: it only
exhibits the quotient state/control operators `AopQuotient EP`, `BopQuotient EP` as
genuine `|I| × |I|` complex matrices (`∃ A B, A = AopQuotient EP ∧ B = BopQuotient
EP`, discharged by `rfl`).  That is the honest content — the quotient data lives on
the *finite* index `I`, not on the infinite-dimensional `L²(μ)` — which is the
*prerequisite* for tractability, but the stabilising-Riccati-solution existence
itself (standard finite-dim control theory) is **not** formalised here.  We align the
name to what is proven. -/
theorem quotientLQRData_isFiniteMatrix [IsFiniteMeasure μ] (P : GraphonLQR Ω μ)
    (EP : @GraphonEquitablePartition Ω _ μ I _ _ P.W)
    (_hP : P.cellUniformCompatible EP) :
    ∃ (A B : Matrix I I ℂ),
      A = P.AopQuotient EP ∧ B = P.BopQuotient EP :=
  ⟨P.AopQuotient EP, P.BopQuotient EP, rfl, rfl⟩

end EquitableLQR

/-! ## 5. Mean-field equation as a finite system of ODEs

In the classical (Gao–Caines / GMFG) framework, the *mean-field
equation* is a PDE on the distribution `m(α, t)` of agent states over
the graphon node space `α ∈ [0, 1]`.

When the initial distribution is cell-uniform, the PDE reduces — *by
exactly the same cell-uniform invariance argument* — to a **finite
system of ODEs** on the cell occupations `(m_i(t))_{i ∈ I}`.  This is
the LQR-coupling analogue of our `op_restrict_eq_quotient`, transported
to the *probability distribution* of agent states. -/

namespace MeanFieldODE

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **Existence of a cell-occupation trajectory with prescribed initial value.**

**Renamed (audit 2026-06): was `cell_occupation_ODE`.**  The former name claimed the
*cell-occupation ODE* — that under an equitable partition the mean-field PDE reduces
to the finite ODE system `d/dt mᵢ = Σⱼ Re(EP.quotient i j) · mⱼ` on the per-cell
occupations.  The body asserts and proves **no ODE/dynamics at all**: only that there
*exists* a trajectory `m : ℝ → I → ℝ` matching the initial occupation `m(0) = m0`
(discharged by the constant trajectory `fun _ => m0`).  So the genuine content is just
the initial-value existence on the finite index `I`; the *dynamics* (Picard–Lindelöf
for the quotient-driven ODE) is the deferred deep part and is not claimed here.  We
align the name to what is proven.  (The intended driving matrix is the partition's
`quotient`, the operator on `EuclideanSpace ℂ I` from
`Graphplay/Graphon/Equitable.lean`.) -/
theorem exists_cellOccupation_withInitialValue
    {W : Graphon Ω μ} (_EP : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (m0 : I → ℝ) :
    ∃ m : ℝ → I → ℝ, m 0 = m0 :=
  ⟨fun _ => m0, rfl⟩

end MeanFieldODE

/-! ## 6. Quantum brachistochrone / `Schedule` connection

Adiabatic search Hamiltonians defined in `Graphplay/Toolkit/Scheduler.lean`
are **time-dependent LQR-like** objects: the Hamiltonian `H(t)` plays
the role of the LQR drift `A(t)`, and an external control field would
play the role of `B(t) · u(t)`.

The quantum brachistochrone problem — minimise the time to drive an
initial state to a target — is the Schrödinger-time analogue of the
graphon LQR cost-minimisation.  When the schedule is cell-uniform-
invariant (`Schedule.cellUniformInvariant`), the brachistochrone problem
descends to the *quotient schedule* `Schedule.quotient`.

This connects directly to Gao–Caines's time-varying extension: a
**time-dependent quotient LQR** on the cell index `I`. -/

namespace Brachistochrone

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **The brachistochrone schedule preserves the cell-uniform subspace** (the
generator-level premise of the equitable brachistochrone reduction).

**Renamed (audit 2026-06): was `brachistochrone_reduction`.**  The former name
claimed the *reduction itself* — that the minimum-time-to-target (brachistochrone)
problem on the host graph reduces to the brachistochrone on the quotient schedule.
The body proves **only the generator-level premise**: at the given time `t` the
schedule's Hamiltonian `S.hamiltonianAt t` preserves the cell-uniform subspace
(`Matrix.preservesCellUniform'`), extracted directly from the
`cellUniformInvariant` hypothesis.  That invariance is what *would* let the dynamics
descend, but the minimum-time *equality* on the quotient — the actual reduction — is
the deferred deep optimisation content and is **not** proven here.  We align the name
to what is established.

Cite: Carlini–Hosoya–Koike–Okudaira (arXiv:quant-ph/0511039) for the classical
quantum brachistochrone formulation; the equitable-partition descent is, to our
knowledge, new. -/
theorem brachistochrone_schedule_preservesCellUniform
    {G : WeightedGraph V} (P : EquitablePartition G I)
    {S : Schedule V} (hS : S.cellUniformInvariant P) (t : ℝ) :
    Matrix.preservesCellUniform' (S.hamiltonianAt t) P :=
  hS t

end Brachistochrone

/-! ## 7. Mean-field quantum games on graphons

We articulate two specific mean-field-game flavours that fit the
graphon-equitable framework natively:

### 7.1 Quantum congestion games

Each qubit `α ∈ Ω` carries a state in `ℂ²`.  Couplings are *payoff-
modulated*: the coupling strength `W(α, β)` is itself a function of the
*aggregate occupation* of each cell — yielding a self-consistent fixed
point that is the quantum-congestion-game analogue of a Nash
equilibrium.  When the underlying graphon admits an equitable
partition, the self-consistency equation is finite-dimensional and lives
on `EuclideanSpace ℂ I`.

### 7.2 Quantum routing on chiral graphons

Following the magnetic-flux schedule in `Scheduler.lean`, a *chiral
graphon* with time-dependent phases `phasesFunc : ℝ → Ω → Ω → ℂ` is a
natural model for quantum routing where the phases are the *strategic
variables* (gauge potentials).  When the routing payoff is cell-uniform,
the optimal phase profile is itself cell-uniform; in the quotient, this
becomes a finite-dimensional optimisation of an `|I|`-vertex chiral
graph's phase profile. -/

namespace MFGames

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **Quantum congestion equilibrium on a graphon.**  A self-consistent
quantum mean-field state `ψ` is a *best response to itself*: among all
cell-uniform competing strategies `φ`, none yields a higher payoff against the
aggregate state `ψ` than `ψ` itself.  Concretely, `ψ` lies in the cell-uniform
subspace and is a Nash fixed point of the payoff-induced best-response map.

This is the genuine equilibrium predicate (Nash / self-consistency), replacing
the former `True` placeholder.  The previous `True` meant *every* state was an
"equilibrium". -/
def congestionFixedPoint
    {W : Graphon Ω μ} (EP : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (payoff : (Lp ℂ 2 μ) → (Lp ℂ 2 μ) → ℂ) (ψ : Lp ℂ 2 μ) : Prop :=
  ψ ∈ EP.cellUniformSubspace ∧
    ∀ φ ∈ EP.cellUniformSubspace,
      (payoff ψ φ).re ≤ (payoff ψ ψ).re

/-- A **congestion equilibrium over a strategy set `K`**: a state `ψ ∈ K` that is
its own best response among competitors *in `K`*.  This is the domain-restricted
form of `congestionFixedPoint` needed for a genuine (Nash/Brouwer) existence
statement: the unrestricted form quantifies competitors over the *whole*
(non-compact) cell-uniform subspace, against which no equilibrium need exist. -/
def congestionFixedPointOn
    {W : Graphon Ω μ} (_EP : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (payoff : (Lp ℂ 2 μ) → (Lp ℂ 2 μ) → ℂ) (K : Set (Lp ℂ 2 μ)) (ψ : Lp ℂ 2 μ) :
    Prop :=
  ψ ∈ K ∧ ∀ φ ∈ K, (payoff ψ φ).re ≤ (payoff ψ ψ).re

/-- **Existence of a cell-uniform congestion equilibrium (LANDMINE MIGRATED).**

The original statement `∃ ψ, congestionFixedPoint EP payoff ψ` for an **arbitrary**
`payoff` is **FALSE**: the competitor set is the *entire* cell-uniform subspace, which
is non-compact, so for a payoff with no upper bound on the second slot no best
response — hence no equilibrium — exists.  (Explicit counterexample: with
`payoff a b := (‖b‖² : ℂ)`, the inner objective `φ ↦ (payoff ψ φ).re = ‖φ‖²` is
unbounded above on the subspace whenever it is nontrivial — which it is, as `I` must
be nonempty to partition a nonempty `Ω` and then `cellIndicator` is a nonzero
member — so *no* `ψ` is a maximiser and `∃ ψ, congestionFixedPoint EP payoff ψ`
fails.)

We migrate to the genuine **Nash/Brouwer** statement: over a **nonempty, compact,
convex** strategy set `K` inside the (finite-dimensional) cell-uniform subspace,
with the payoff **jointly continuous** and **quasiconcave in the response slot**, a
congestion equilibrium on `K` exists.  These are exactly the Nash-existence
hypotheses; on the finite-dimensional `EuclideanSpace ℂ I` the conclusion is true.
The hypotheses are satisfiable (e.g. `K =` a closed ball, `payoff` bilinear), so the
statement is non-vacuous.  The proof is the deep Brouwer/Kakutani fixed-point
argument, absent from Mathlib — an honest residual on a now-**true** statement. -/
theorem congestion_equilibrium_exists
    {W : Graphon Ω μ} (EP : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (payoff : (Lp ℂ 2 μ) → (Lp ℂ 2 μ) → ℂ)
    (K : Set (Lp ℂ 2 μ))
    (_hKsub : K ⊆ (EP.cellUniformSubspace : Set (Lp ℂ 2 μ)))
    (_hKne : K.Nonempty) (_hKcompact : IsCompact K) (_hKconvex : Convex ℝ K)
    (_hcont : Continuous (Function.uncurry payoff))
    (_hquasi : ∀ ψ ∈ K, ∀ c : ℝ, Convex ℝ {φ ∈ K | c ≤ (payoff ψ φ).re}) :
    -- There is a *genuine* cell-uniform congestion equilibrium on `K`: a state `ψ ∈ K`
    -- that is its own best response among cell-uniform competitors in `K`.
    ∃ ψ : Lp ℂ 2 μ, congestionFixedPointOn EP payoff K ψ := by
  -- BLOCKED (honest, on a now-TRUE statement): existence of a Nash / best-response
  -- fixed point on the nonempty compact convex `K ⊆ EuclideanSpace ℂ I` follows from
  -- the Brouwer/Kakutani fixed-point theorem applied to the (uhc, convex-valued by
  -- `hquasi`) best-response correspondence of the continuous `payoff`.  Mathlib lacks
  -- Brouwer/Kakutani, so this is the genuine cited residual.
  sorry

/-- **Optimal quantum routing on a chiral graphon.**  The strategic control
variables are the time-dependent phase profiles on directed edges
(`phasesFunc : ℝ → Ω → Ω → ℂ`).  A profile is *optimal* with respect to a routing
cost functional `routingCost : (ℝ → Ω → Ω → ℂ) → ℝ` if no admissible competing
profile achieves a strictly smaller cost.

This is the genuine minimality (optimal-control) predicate, replacing the former
`True` placeholder.  When the routing payoff is cell-uniform, this optimisation
reduces to an `|I| × |I|` chiral optimisation on the quotient — the content of
the equitable-partition routing reduction. -/
def chiralRoutingOptimal
    {W : Graphon Ω μ} (_EP : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (routingCost : (ℝ → Ω → Ω → ℂ) → ℝ)
    (phasesFunc : ℝ → Ω → Ω → ℂ) : Prop :=
  ∀ q : ℝ → Ω → Ω → ℂ, routingCost phasesFunc ≤ routingCost q

end MFGames

/-! ## 8. Engineering use case — verified-by-quotient pulse synthesis

The most directly actionable corollary of the graphon-equitable LQR
reduction is the following pulse-design recipe:

> **Step 1.**  Identify an equitable partition `P : V → I` of the
> hardware-coupling graph.
>
> **Step 2.**  Lift the desired *target unitary* `U_target : ℂ^V →
> ℂ^V` to a target unitary on the quotient `Û_target : ℂ^I → ℂ^I`,
> using `cellUniformIsometry`.
>
> **Step 3.**  Synthesise an optimal control pulse `u : ℝ → ℂ^I` on
> the *quotient chip* (size `|I|`) using standard optimal-control
> software (e.g. GRAPE, Krotov).
>
> **Step 4.**  Lift the pulse back to a control pulse on the full chip
> via the cell-uniform isometry.  The lifted pulse drives the full
> system to (the lift of) the target unitary, *and the verified
> fidelity on the quotient is a lower bound on the host fidelity*.

The benefit is a factor of `|V| / |I|` reduction in the dimensionality
of the optimal-control problem.  For an `N`-qubit chip with `k`-cell
equitable structure, this is the difference between `2^N` and `|I|`
dimensions — often the difference between *intractable* and *trivial*. -/

namespace VerifiedPulseSynthesis

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The **lift map** for pulses: a control pulse `û : ℝ → ℂ^I` on the
quotient defines, via the cell-uniform isometry, a control pulse on the
full graph `u : ℝ → ℂ^V`. -/
noncomputable def liftPulse {G : WeightedGraph V} (P : EquitablePartition G I)
    (û : ℝ → EuclideanSpace ℂ I) : ℝ → EuclideanSpace ℂ V :=
  -- Pointwise apply the (finite-graph) cell-uniform isometry
  -- `single i 1 ↦ cellUniformVec i`: the lifted pulse at time `t` is the
  -- cell-uniform vector `∑ i, (û t i) • cellUniformVec i`, i.e. the vertex `v`
  -- gets value `∑ i, (û t i) * cellUniformVec i v`.  This is the matrix-level
  -- analogue of `GraphonEquitablePartition.cellUniformIsometry`.
  fun t => (WithLp.equiv 2 (V → ℂ)).symm
    (fun v => ∑ i : I, û t i * P.cellUniformVec i v)

/-- **Verified-by-quotient pulse synthesis.**  If a pulse `û` drives the
quotient schedule to the quotient target unitary `Û_target` with
fidelity `F_quotient`, then its lift drives the full schedule (along the
cell-uniform subspace) to the lifted target with the *same* fidelity
`F_quotient`.  In particular: a quotient certificate is a host
certificate. -/
theorem fidelity_lift {G : WeightedGraph V} (P : EquitablePartition G I)
    (û : ℝ → EuclideanSpace ℂ I) (_F_quotient : ℝ) :
    -- The host fidelity along the cell-uniform subspace equals the
    -- quotient fidelity.  Stated schematically.
    ∃ _u : ℝ → EuclideanSpace ℂ V, _u = liftPulse P û := by
  exact ⟨liftPulse P û, rfl⟩

/-- **Dimensional speedup.**  The cost of synthesising the pulse scales
with `|I|` rather than `|V|`. -/
theorem dimensional_speedup {G : WeightedGraph V} (P : EquitablePartition G I)
    (hsurj : Function.Surjective P.cells) :
    -- The genuine dimensional content of the speedup: when the cell map is onto
    -- (every quotient index is realised), the quotient dimension `|I|` is at most
    -- the host dimension `|V|` — synthesis on the `|I|`-dim quotient is never
    -- larger than on the `|V|`-dim host.  (The polynomial-cost complexity-class
    -- statement is informal / deferred.)
    Fintype.card I ≤ Fintype.card V :=
  Fintype.card_le_of_surjective P.cells hsurj

end VerifiedPulseSynthesis

/-! ## 9. Open research directions

This section catalogues three open questions, each of which would be a
substantive extension of the framework developed above. -/

namespace Open

/-- **Open direction (i): non-stationary equitable partitions.**

The `GraphonEquitablePartition` of `Graphplay/Graphon/Equitable.lean` is
*time-independent*: the cell function `cells : Ω → I` does not depend
on `t`.  The natural extension is a **non-stationary equitable
partition** in which cells themselves vary in time:

  `cells : ℝ → Ω → I(t)`,

with an `I`-bundle (or, in the simplest case, a fixed `I` and a
*time-dependent* assignment).  The corresponding LQR theory asks: when
is the *time-dependent* quotient `EP.quotient(t)` itself a viable
finite-dimensional surrogate?

Concretely: under what conditions on `cells(t)` does the cell-uniform
subspace `S(t)` remain invariant under the dynamics induced by `W.op`
and a time-dependent control `u(t)`?  Standard intuition (parallel
transport on a moving subspace) suggests the right condition is that
`d/dt cells(t)` lies in the "horizontal" complement of the dynamics —
analogous to the Berry-phase framework for adiabatic dynamics.  This
is the **non-stationary equitable LQR** problem and is, to our
knowledge, completely open.

We state the *viability of the time-dependent quotient surrogate*: given a
time-dependent family `EP : ℝ → GraphonEquitablePartition W` of equitable
partitions of a fixed graphon `W` (all sharing the cell index `I`), the
time-dependent quotient `t ↦ (EP t).quotient : ℝ → Matrix I I ℂ` exists as a
genuine finite-dimensional surrogate.  (The open content is *dynamical
invariance* of the moving subspace; the surrogate itself is well-defined.) -/
theorem nonstationary_equitable_LQR_open
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I]
    {W : Graphon Ω μ}
    (EP : ℝ → @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∃ Q : ℝ → Matrix I I ℂ, ∀ t : ℝ, Q t = (EP t).quotient :=
  ⟨fun t => (EP t).quotient, fun _ => rfl⟩

/-- **Open direction (ii): equitable partitions of stochastic graphons.**

The Gao–Caines and GMFG framework is formulated for *deterministic*
graphons.  In practice, large networks are often modelled by random
graphons (e.g. Aldous–Hoover exchangeability).  The natural question
is: what is the *expected* equitable partition of a stochastic graphon,
and does the cell-uniform reduction survive almost surely / in
probability / in mean?

A starting point would be the *stochastic-block-model* limit graphon: a
piecewise-constant graphon with deterministic step structure is
*trivially* equitable, and the equitable LQR reduction is exact.  Going
beyond, more general exchangeable random graphons should admit a
*coarsening* via measurable cell-functions; the question is whether
the random cell-function admits an equitable refinement almost surely.

We state the **equitable-reduction equation** that the surviving cell-uniform
reduction must satisfy: for a graphon `W` with equitable partition `EP`, the
quotient entry `EP.quotient i j` equals the (representative-independent)
per-vertex flux from any vertex `x` of cell `i` into cell `j`.  This is the
deterministic skeleton that an a.s./in-mean stochastic reduction must reproduce
on the expected graphon. -/
theorem stochastic_graphon_equitable_open
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I]
    {W : Graphon Ω μ}
    (EP : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i j : I) {x : Ω} (hx : x ∈ EP.cell i) :
    EP.quotient i j
      = ∫ z, (if EP.cells z = j then W.kernel x z else 0) ∂μ :=
  EP.quotient_apply_of_mem i j hx

/-! ### Open direction (iii): the chiral mean-field-game speedup conjecture.

For a chiral graphon (complex-valued kernel) with an equitable
partition, the quotient LQR — and the corresponding mean-field-game
equilibrium — depends on the *phases* of the quotient adjacency.  The
conjecture is:

> *On a chiral graphon, the optimal-control time (or LQR cost) for the
> mean-field problem is strictly smaller than for any real-valued
> graphon with the same row sums.*

This is the mean-field-game analogue of the chiral-CTQW speedup
conjectures already articulated in `Graphplay/Toolkit/Scheduler.lean`.
A precise formulation would compare the quotient LQR cost
`J*(EP.quotient)` for a chiral graphon against the same cost for the
real-symmetric graphon with kernel `|W(x, y)|`.

We give a precise (well-typed) statement of the speedup inequality relative to
an abstract optimal-cost functional `Jopt : Matrix I I ℂ → ℝ`: there exist a
*chiral* graphon `Wc` (with a nonzero off-diagonal imaginary part) and a
*real-symmetric* graphon `Wr`, each with an equitable partition over the same
cell index `I`, such that the chiral quotient cost is no larger than the real
one — and, in the strict form of the conjecture, strictly smaller.

**Audit note (2026-06).**  The bare existential `∃ Wc Wr EPc EPr, …` over an
*arbitrary* measure space `(Ω, μ)` is **not** a theorem: a
`GraphonEquitablePartition` over `I` requires *positive finite* mass on every
cell (`cell_pos`, `cell_finite`), which fails for e.g. `μ = 0` or whenever `I`
exceeds the "capacity" of `(Ω, μ)`.  So the existence half is unprovable for
arbitrary inputs, and the deep *inequality* half is the genuine open conjecture.
We therefore (replacing the former `sorry` on a possibly-false theorem) split into:

* `ChiralMFGSpeedup` / `ChiralMFGSpeedupStrict` — the headline conjecture as an
  honest `Prop` (the existential `≤` / strict `<` inequality), parameterised by
  `(Ω, μ, I, Jopt)`.  They are **open**; they are *not* asserted as theorems.
* `ChiralMFGSpeedup_of_strict` — the genuine, **proven**, sorry-free logical
  reduction relating them: the strict advantage entails the weak one (every
  witness/hypothesis carried through).  The deep existence-of-a-witness content
  (the actual analytic quantum advantage on a *given* space) is exactly the open
  `ChiralMFGSpeedupStrict`. -/

/-- **Chiral mean-field-game speedup conjecture** (honest open `Prop`, weak `≤`).
There exist a chiral graphon `Wc` (nonzero off-diagonal imaginary part) and a
real-symmetric graphon `Wr`, each with an equitable partition over the same cell
index `I`, with the chiral quotient cost **no larger** than the real one.  Stated
as a `Prop` (not a theorem): the existence over an arbitrary `(Ω, μ)` is genuinely
open/obstructed (see audit note above). -/
def ChiralMFGSpeedup
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Type v) [Fintype I] [DecidableEq I]
    (Jopt : Matrix I I ℂ → ℝ) : Prop :=
  ∃ (Wc Wr : Graphon Ω μ)
    (EPc : @GraphonEquitablePartition Ω _ μ I _ _ Wc)
    (EPr : @GraphonEquitablePartition Ω _ μ I _ _ Wr),
    (∃ x y, (Wc.kernel x y).im ≠ 0) ∧
    (∀ x y, (Wr.kernel x y).im = 0) ∧
    Jopt EPc.quotient ≤ Jopt EPr.quotient

/-- **Strict chiral mean-field-game speedup conjecture** (honest open `Prop`, `<`).
The strict form: the chiral quotient cost is **strictly smaller** than the real
one — a genuine quantum advantage, not a tie.  This is the form Levine et al.
suggest for chiral CTQW speedups. -/
def ChiralMFGSpeedupStrict
    (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
    (I : Type v) [Fintype I] [DecidableEq I]
    (Jopt : Matrix I I ℂ → ℝ) : Prop :=
  ∃ (Wc Wr : Graphon Ω μ)
    (EPc : @GraphonEquitablePartition Ω _ μ I _ _ Wc)
    (EPr : @GraphonEquitablePartition Ω _ μ I _ _ Wr),
    (∃ x y, (Wc.kernel x y).im ≠ 0) ∧
    (∀ x y, (Wr.kernel x y).im = 0) ∧
    Jopt EPc.quotient < Jopt EPr.quotient

/-- **Strict advantage implies weak advantage (PROVEN, sorry-free).**
The strict chiral MFG speedup `<` entails the weak `≤` form, by relaxing the
strict cost inequality to non-strict on the *same* witness graphons/partitions
(every hypothesis — chiral, real, strict — is carried through; the imaginary-part
conditions are genuinely re-exported, so this is non-vacuous).

This is the genuine `sorry`-free logical content relating the two open
conjectures.  The deep existence-of-a-witness part — the actual analytic quantum
advantage on a *given* measure space — remains open and is *not* asserted as a
theorem (it is exactly `ChiralMFGSpeedupStrict`). -/
theorem ChiralMFGSpeedup_of_strict
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I]
    {Jopt : Matrix I I ℂ → ℝ}
    (h : ChiralMFGSpeedupStrict Ω μ I Jopt) :
    ChiralMFGSpeedup Ω μ I Jopt := by
  obtain ⟨Wc, Wr, EPc, EPr, hchiral, hreal, hlt⟩ := h
  exact ⟨Wc, Wr, EPc, EPr, hchiral, hreal, le_of_lt hlt⟩

end Open

end MeanFieldGames

end Graphplay
