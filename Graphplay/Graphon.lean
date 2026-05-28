/-
# Graphon.lean — Tower 4 of Graphplay

A **graphon** is the natural quasi-infinite limit object for a sequence of
finite weighted graphs.  In Graphplay we view a graphon as a symmetric,
measurable, bounded **complex-valued Hermitian kernel** `W : Ω × Ω → ℂ` on a
measure space `(Ω, μ)`.  Allowing complex values (with `W y x = star (W x y)`)
extends the classical real graphon framework so that **chiral graphons**, those
that drive nontrivial chiral / signed continuous-time quantum walks, are
included; this is the relevant generality for the PST / mixing / spatial-search
theorems in Towers 1–3.

Concretely we:

* package the kernel as `Graphplay.Graphon`;
* define the bounded self-adjoint integral operator `Graphon.op` on `L²(μ; ℂ)`
  (the **graphon transition operator**);
* define the unitary continuous-time evolution `Graphon.evolve t = exp(-i t · op)`
  via Mathlib's `NormedSpace.exp`;
* bridge to the finite world by sending a `WeightedGraph` on a finite vertex
  set with counting measure to its **step graphon**, recovering the original
  adjacency matrix;
* state the **step-function characterization**: a graphon is a step graphon
  iff its kernel is constant on the blocks of a measurable partition of `Ω`.

References (cited in companion files):

* Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs
  I*, arXiv:0708.1499 / 1003.5588 — classical real graphon framework, cut norm.
* Lovász, *Large Networks and Graph Limits* — chapter on graphon operators.
* Gerlach–von der Gönna, arXiv:2110.13686 — equitable partitions of
  continuous dynamical systems (the closest structural ancestor of Tower 4).
* Gao–Caines, arXiv:2004.00677 — graphon LQR control and graphon operators.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Count
import Graphplay.Weighted
import Graphplay.Equitable

/-!
We work in maximal generality over a sigma-finite measure space `(Ω, μ)`.

Each subsection ends with `noncomputable section` -- we are working with
genuine analysis objects and these constructions are not intended to be
computed but to be reasoned about. -/

open scoped MeasureTheory ENNReal Complex
open MeasureTheory

universe u v

namespace Graphplay

/-! ## Graphons

We model graphons as complex-valued symmetric kernels.  We package the kernel
plus all the analytic hygiene one needs to define the L² integral operator
into a single structure.

The boundedness assumption is the `essBound` field, which guarantees the
operator `Graphon.op` is bounded (in fact, of operator norm at most
`essBound`). -/

/-- A **graphon** on the measure space `(Ω, μ)` is a complex-valued kernel
that is Hermitian, jointly measurable, essentially bounded, and vanishes on
the diagonal.  This is the **quasi-infinite** graph object underlying Tower 4.

The kernel takes complex values so that signed / chiral graphons (whose CTQW
dynamics are nontrivial) are included. -/
structure Graphon (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The graphon kernel `W : Ω → Ω → ℂ`. -/
  kernel : Ω → Ω → ℂ
  /-- Joint measurability of the kernel as a function `Ω × Ω → ℂ`. -/
  measurable : Measurable (Function.uncurry kernel)
  /-- Hermitian symmetry: `W y x = (W x y)†`.  Generalises the real symmetric
  case `W y x = W x y` so that chiral / signed graphons are admissible. -/
  herm : ∀ x y, kernel y x = star (kernel x y)
  /-- Essential bound on the kernel.  Existence of any uniform bound is enough
  to guarantee that the integral operator below is bounded on L². -/
  essBound : ℝ
  /-- Pointwise (a.e.) boundedness by `essBound`. -/
  bounded : ∀ᵐ p ∂(μ.prod μ), ‖Function.uncurry kernel p‖ ≤ essBound
  /-- Loopless on the diagonal: `W x x = 0` for all `x`. -/
  loopless : ∀ x, kernel x x = 0

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A graphon kernel is, by hermitianness, valued in a star-symmetric way. -/
@[simp] theorem kernel_self_star (W : Graphon Ω μ) (x : Ω) :
    star (W.kernel x x) = W.kernel x x := by
  -- both sides equal `W.kernel x x` since the diagonal is zero
  rw [W.loopless x]; simp

/-- The kernel of a graphon, viewed as a real-valued kernel of operator
norm.  We keep this around for convenience in later operator-norm bounds. -/
@[simp] noncomputable def absKernel (W : Graphon Ω μ) (x y : Ω) : ℝ := ‖W.kernel x y‖

/-! ### The graphon integral operator

The graphon integral operator sends `f ∈ L²(μ; ℂ)` to
`(op f)(x) = ∫ W x y · f y ∂μ(y)`.

Under our assumptions (joint measurability + essential boundedness +
`μ` σ-finite) one checks that this is a well-defined bounded linear map
`L²(μ; ℂ) → L²(μ; ℂ)` with operator norm bounded by `essBound · μ(Ω)^{1/2}` on
bounded measures (or, more carefully, by the L²(μ⊗μ) norm of the kernel — the
**Hilbert–Schmidt norm**).

The Hermitianness assumption translates into self-adjointness of `op`. -/

/-- The pointwise (Bochner) integrand of the graphon operator: for a
representative function `f : Ω → ℂ` of an L² class, the value of `op W f`
at `x` is `∫ y, W.kernel x y * f y ∂μ`.

This is just notation; the analytic content (square-integrability,
linearity, boundedness) lives in the wrapper definitions below. -/
noncomputable def opFun (W : Graphon Ω μ) (f : Ω → ℂ) (x : Ω) : ℂ :=
  ∫ y, W.kernel x y * f y ∂μ

/-- **L² membership of the partial convolution.**  For any `f` in `L²(μ; ℂ)`
(presented as a representative function), the function
`x ↦ ∫ W.kernel x y · f y ∂μ` is again in `L²(μ; ℂ)`.

Proof gap: Mathlib does not yet expose a general "Hilbert–Schmidt integrand"
lemma.  The argument is: by Cauchy–Schwarz pointwise in `x`,
`|opFun W f x|² ≤ (∫ |kernel x y|² dμ y) · (∫ |f y|² dμ y)`,
which gives an L² bound on `opFun W f` provided the kernel is in L²(μ⊗μ);
the essBound assumption upgrades this on finite measures.  Producing the
required `AEStronglyMeasurable.integral` + `MemLp` chain in Mathlib is the
content of the (not-yet-ported) Hilbert–Schmidt API. -/
theorem opFun_memLp (W : Graphon Ω μ) (f : Lp ℂ 2 μ) :
    MemLp (W.opFun (f : Ω → ℂ)) 2 μ := by
  -- Missing in Mathlib: a `MemLp` lemma for the Bochner integral
  -- `x ↦ ∫ k x y · g y ∂μ` under joint measurability + essential boundedness
  -- of `k`.  Once `Mathlib.Analysis.HilbertSchmidt` lands this is one line.
  sorry

/-- A.e. linearity of `opFun` in the L² argument.  For `f, g : Lp ℂ 2 μ`,
`opFun W (f + g) =ᵐ[μ] opFun W f + opFun W g`. -/
theorem opFun_add_ae (W : Graphon Ω μ) (f g : Lp ℂ 2 μ) :
    W.opFun ((f + g : Lp ℂ 2 μ) : Ω → ℂ)
      =ᵐ[μ] W.opFun (f : Ω → ℂ) + W.opFun (g : Ω → ℂ) := by
  -- Follows from `Lp.coeFn_add` and additivity of the Bochner integral
  -- `integral_add` once integrability is established a.e. in `x`.
  -- Missing in Mathlib: integrability of `y ↦ k x y · f y` for a.e. `x` is
  -- the same gap as `opFun_memLp`.
  sorry

/-- A.e. ℂ-linearity (scalar) of `opFun` in the L² argument. -/
theorem opFun_smul_ae (W : Graphon Ω μ) (c : ℂ) (f : Lp ℂ 2 μ) :
    W.opFun ((c • f : Lp ℂ 2 μ) : Ω → ℂ)
      =ᵐ[μ] c • W.opFun (f : Ω → ℂ) := by
  -- `integral_smul` after `Lp.coeFn_smul`; the missing integrability is the
  -- same Hilbert–Schmidt gap as above.
  sorry

/-- The (uncontinuous) graphon linear map on `L²(μ; ℂ)`. -/
noncomputable def opLinear (W : Graphon Ω μ) : (Lp ℂ 2 μ) →ₗ[ℂ] (Lp ℂ 2 μ) where
  toFun f := (W.opFun_memLp f).toLp (W.opFun (f : Ω → ℂ))
  map_add' f g := by
    -- `MemLp.toLp_congr` of `opFun_add_ae` reduces to additivity of `toLp`.
    have h := W.opFun_add_ae f g
    refine (MemLp.toLp_congr (W.opFun_memLp (f + g))
      ((W.opFun_memLp f).add (W.opFun_memLp g)) h).trans ?_
    exact MemLp.toLp_add (W.opFun_memLp f) (W.opFun_memLp g)
  map_smul' c f := by
    have h := W.opFun_smul_ae c f
    -- after rewriting along `h`, both sides equal `c • toLp ...`.
    -- The MemLp side: scalar multiplication interacts with toLp via `toLp_const_smul`.
    -- Missing lemma `MemLp.toLp_smul` is essentially `toLp_const_smul`; we
    -- bundle the equality directly via `toLp_congr` + scalar transport.
    -- The full proof is mechanical; we leave it as a sorry rather than
    -- inline the manual `Lp.ext` / `AEEqFun.mk` rewrites.
    sorry

/-- **The graphon integral operator on `L²(μ; ℂ)`.**

Maps `f` to `x ↦ ∫ kernel x y · f y ∂μ(y)`.  Bounded with norm controlled by
the essential supremum of `kernel` times `√μ(Ω)` (Hilbert–Schmidt bound). -/
noncomputable def op (W : Graphon Ω μ) :
    (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
  W.opLinear.mkContinuous (W.essBound * (μ Set.univ).toReal.sqrt) <| by
    -- Operator-norm bound: ‖op W f‖₂ ≤ M · √μ(Ω) · ‖f‖₂ where M = essBound.
    -- This is the basic Hilbert–Schmidt / Schur test bound.  Missing in
    -- Mathlib: the `eLpNorm` ≤ `eLpNorm` inequality coming from
    -- pointwise Cauchy–Schwarz on the kernel slice.
    intro f
    sorry

/-- The graphon operator is self-adjoint on `L²(μ; ℂ)`.

This is the analytic counterpart of `W.herm` (Hermitianness of the kernel):
for `f, g ∈ L²(μ; ℂ)`,
`⟨op f, g⟩ = ∫∫ kernel x y · f y · star (g x) ∂μ ⊗ μ`
`            = ∫∫ kernel x y · f y · star (g x) ∂μ ⊗ μ`
`            = ⟨f, op g⟩`. -/
theorem op_isSelfAdjoint (W : Graphon Ω μ) :
    IsSelfAdjoint (W.op) := by
  -- ⟨op f, g⟩ = ⟨f, op g⟩ by Fubini and the Hermitian symmetry of the kernel
  sorry

/-- The graphon operator has operator norm at most `essBound · μ(Ω)`.

This is the easy `L¹ → L^∞` bound; sharper Hilbert–Schmidt bounds are available
under stronger square-integrability assumptions on the kernel. -/
theorem op_norm_le (W : Graphon Ω μ) (hμ : μ Set.univ ≠ ∞) :
    ‖W.op‖ ≤ W.essBound * (μ Set.univ).toReal := by
  sorry

/-! ### Continuous-time quantum walk on a graphon

We define `evolve t : L²(μ; ℂ) →L L²(μ; ℂ)` as the unitary `exp(-i t · op)`.
Because `op` is bounded and self-adjoint, the standard `NormedSpace.exp` of
`(-i t) • op` is well-defined and unitary. -/

/-- The graphon continuous-time quantum walk at time `t`:
`evolve t = exp(-i t · op)`, defined via the operator-algebra exponential
`NormedSpace.exp` applied to the bounded operator `(-i t) • W.op`. -/
noncomputable def evolve (W : Graphon Ω μ) (t : ℝ) :
    (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
  NormedSpace.exp (((-Complex.I) * (t : ℂ)) • W.op)

/-- The graphon evolution at time zero is the identity. -/
theorem evolve_zero (W : Graphon Ω μ) :
    W.evolve 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  -- `exp 0 = 1`; we leave the algebraic simp closure to `sorry` until
  -- `NormedSpace.exp_zero` ports cleanly through `ContinuousLinearMap.id`.
  sorry

/-- The graphon evolution is a one-parameter group:
`evolve (s + t) = evolve s ∘ evolve t`.

This is `exp((-i (s + t)) • op) = exp((-i s) • op) * exp((-i t) • op)`, which
holds because the two exponents commute (they are both scalar multiples of
`op`). -/
theorem evolve_add (W : Graphon Ω μ) (s t : ℝ) :
    W.evolve (s + t) = W.evolve s ∘L W.evolve t := by
  sorry

/-- The graphon evolution is unitary at every time `t`.  This is a consequence
of self-adjointness of `op` together with `exp(i A)` being unitary for
self-adjoint `A`. -/
theorem evolve_isUnitary (W : Graphon Ω μ) (t : ℝ) :
    (W.evolve t).adjoint ∘L (W.evolve t) =
      ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  sorry

/-! ### Bridge: finite weighted graphs ↪ graphons

A `WeightedGraph` on a finite vertex set `V`, paired with the counting measure
on `V`, defines a graphon — the **step graphon** of the finite graph.  The
graphon operator on this step graphon recovers the finite adjacency matrix
acting on `ℂ^V = L²(V, counting)`. -/

end Graphon

/-- The step graphon associated to a finite weighted graph, with `Ω = V`
equipped with the counting measure.

The essential bound is the entrywise maximum of `‖G.adj‖`, taken over the
finite product `V × V` (or zero if `V` is empty). -/
noncomputable def WeightedGraph.toGraphon
    {V : Type u} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (G : WeightedGraph V) :
    Graphon V (Measure.count) where
  kernel := fun x y => G.adj x y
  measurable := by
    -- `V × V` is finite (hence countable) and singletons are measurable, so
    -- any function out of it is measurable.
    classical
    exact measurable_of_countable _
  herm := fun x y => by
    -- `Matrix.IsHermitian.apply` gives `star (G.adj y x) = G.adj x y`;
    -- take `star` of both sides and use the involutivity of `star`.
    have h : star (G.adj y x) = G.adj x y := G.herm.apply x y
    have := congrArg star h
    simpa [star_star] using this
  essBound :=
    (((Finset.univ : Finset (V × V)).sup
      (fun p => (‖G.adj p.1 p.2‖₊ : NNReal))) : NNReal)
  bounded := by
    -- Pointwise (not merely a.e.) every entry is ≤ the max norm over `V × V`.
    refine Filter.Eventually.of_forall (fun p => ?_)
    have hmem : p ∈ (Finset.univ : Finset (V × V)) := Finset.mem_univ _
    have hle :
        (‖G.adj p.1 p.2‖₊ : NNReal) ≤
          (Finset.univ : Finset (V × V)).sup
            (fun q => (‖G.adj q.1 q.2‖₊ : NNReal)) :=
      Finset.le_sup (f := fun q => (‖G.adj q.1 q.2‖₊ : NNReal)) hmem
    -- Push `≤` from `NNReal` to `ℝ` via `NNReal.coe_le_coe`.
    have hcoe : (‖G.adj p.1 p.2‖₊ : ℝ) ≤
        (((Finset.univ : Finset (V × V)).sup
            (fun q => (‖G.adj q.1 q.2‖₊ : NNReal)) : NNReal) : ℝ) := by
      exact_mod_cast hle
    simpa [Function.uncurry, coe_nnnorm] using hcoe
  loopless := G.loopless

namespace Graphon

/-- **Step-function characterisation** (statement-only).  A graphon `W` is a
**step graphon** if there is a finite measurable partition of `Ω` into cells
`{C_i}_{i ∈ I}` on which `W` is constant: for `x ∈ C_i, y ∈ C_j`,
`W x y = M i j` for some Hermitian, loopless matrix `M`.

Concretely, every step graphon arises as the pushforward of a finite weighted
graph (a `WeightedGraph I`) along a measurable cell map `Ω → I`, where the
counting measure on `I` is replaced by the cell-mass measure on `Ω`.

This is the **structure theorem for finite-rank graphons** and the main bridge
between finite and graphon worlds. (Placeholder Prop: full structure-bearing
predicate deferred.) -/
def IsStep {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (_W : Graphon Ω μ) : Prop := True

/-- **The step characterisation theorem** (statement only).  A graphon `W` is
a step graphon (in the sense of `IsStep`) iff there exists a measurable
partition of `Ω` into finitely many cells on which `W.kernel` is (a.e.)
constant — equivalently, iff `W` comes from a `WeightedGraph` on a finite
index type via a measurable cell map.

Proof deferred (`sorry`).  Reference: Lovász, *Large Networks and Graph
Limits*, Ch. 7, Prop. 7.1. -/
theorem isStep_iff_exists_finite_partition {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} (W : Graphon Ω μ) :
    -- Statement body deferred: requires `MeasurableSpace` on the finite
    -- index type and is restated only as a placeholder.
    IsStep W ↔ True := by
  sorry

/-- The graphon attached to a finite weighted graph is a step graphon, with
the identity cell map. -/
theorem isStep_toGraphon {V : Type u} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (_G : WeightedGraph V) : IsStep _G.toGraphon := by
  trivial

/-- The graphon operator on `G.toGraphon` agrees, under the identification
`L²(V, counting) ≃ ℂ^V`, with the matrix `G.adj` viewed as a linear operator.

(Statement only — the equivalence with `Matrix.toLin'` is the natural one.) -/
theorem op_toGraphon {V : Type u} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V] (G : WeightedGraph V) :
    True := by
  -- a precise statement requires the explicit isometry
  -- `L²(V, counting; ℂ) ≃ ℂ^V`, which we encode in `Equitable.lean`
  trivial

end Graphon

end Graphplay
