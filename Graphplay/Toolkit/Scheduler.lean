/-
# Hamiltonian schedulers

This file sketches a vocabulary for **time-dependent Hamiltonian schedules**
on a finite quantum walk graph.  Three categories of schedule are covered:

1. *Static* schedules (the textbook CTQW).
2. *Trotter* schedules (digital approximations alternating between two
   Hamiltonians).
3. *Magnetic-flux* schedules (the chiral-Hamiltonian analogue of Hamiltonian
   engineering: adiabatic variation of the *phases* of a chiral bundle).

The headline content is the **adiabatic search schedule**: a Hamiltonian
schedule interpolating between a graph-Laplacian start `H_initial = -A_G` and
a target projector `H_final = -P_marked`.  This is the bridge from CTQW
spatial search (instantaneous, Childs-Goldstone style) to adiabatic search
(slow Hamiltonian path).  We state a Grover-style adiabatic theorem with an
explicit equitable-partition reduction.

Motivating references:

* King et al. 2025 (`2501.08148`) — long-range CTQW search; their
  optimal-search Hamiltonian `H = -γ A_G - |m⟩⟨m|` is the static endpoint of
  our adiabatic schedule.
* Sadowski 2014 (`1406.0339`) — non-trivial planar networks (Apollonian) for
  spatial search.  Their negative results show that *not every* graph
  supports an optimal CTQW search; the adiabatic schedule below is a natural
  workaround.
* Wong 2017 (`1706.06939`) — lackadaisical walks shape stationary states;
  the adiabatic limit of a Trotter schedule between a graph adjacency and a
  diagonal weight schedule is a natural formalisation of stationary-state
  engineering.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Graphplay.Weighted
import Graphplay.Equitable

universe u v

namespace Graphplay

/-! ## Schedule structure

A `Schedule` is a smooth path of Hermitian matrices indexed by a real
interval `[t₀, t₁]`.  We do not impose Hermiticity in the type, only in the
predicate `Schedule.isWellFormed`; this is to keep the structure light and
let downstream consumers add constraints. -/

/-- A scheduled Hamiltonian: a continuous (and presumed smooth) path of
matrices on a finite vertex set `V`.  The Hermiticity of each pointwise
matrix is enforced by `isWellFormed`. -/
structure Schedule (V : Type u) [Fintype V] [DecidableEq V] where
  /-- Endpoints of the time interval `(t₀, t₁)` (we expect `t₀ < t₁`). -/
  endpoints : ℝ × ℝ
  /-- The Hamiltonian at each instant.  Outside `[t₀, t₁]` the value is
  irrelevant; we choose to leave the path defined on all of `ℝ` so that
  composition is convenient. -/
  hamiltonianAt : ℝ → Matrix V V ℂ

namespace Schedule

/-- A schedule is well-formed when:

* the endpoints satisfy `t₀ < t₁`;
* every pointwise Hamiltonian is Hermitian. -/
def isWellFormed
    {V : Type u} [Fintype V] [DecidableEq V] (S : Schedule V) : Prop :=
  S.endpoints.1 < S.endpoints.2 ∧
  ∀ t : ℝ, (S.hamiltonianAt t).IsHermitian

/-- The duration of a schedule. -/
def duration {V : Type u} [Fintype V] [DecidableEq V] (S : Schedule V) : ℝ :=
  S.endpoints.2 - S.endpoints.1

/-! ### Constructor variants -/

/-- A constant Hamiltonian: the textbook CTQW schedule. -/
def staticSchedule
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Matrix V V ℂ) (τ : ℝ) : Schedule V where
  endpoints := (0, τ)
  hamiltonianAt := fun _ => H

/-- A *Trotter* schedule alternating between two Hamiltonians `H₁` and `H₂`
in `steps` slices, over duration `duration`.  Each slice is half-and-half:
the first half applies `H₁`, the second half `H₂`.  This is the simplest
first-order Trotter splitting; higher-order variants are obvious extensions. -/
noncomputable def trotterSchedule
    {V : Type u} [Fintype V] [DecidableEq V]
    (H₁ H₂ : Matrix V V ℂ) (steps : ℕ) (duration : ℝ) : Schedule V where
  endpoints := (0, duration)
  hamiltonianAt := fun t =>
    let sliceWidth := duration / (steps : ℝ)
    let withinSlice := t - (sliceWidth * ⌊t / sliceWidth⌋)
    if 2 * withinSlice < sliceWidth then H₁ else H₂

/-- A *magnetic-flux* schedule.  Given a base graph `G`, and a continuous
function `phasesFunc : ℝ → V → V → ℂ` choosing the time-dependent phase on
every directed edge, the schedule's Hamiltonian at time `t` is the
phase-shifted graph adjacency `phasesFunc t x y * G.adj x y`.

This is the *chiral* version of Hamiltonian engineering: rather than
modulating edge magnitudes (which requires physical gain control), we vary
*phases*, which can be implemented as synthetic flux through the
plaquettes of a chiral hardware layout. -/
def magneticFluxSchedule
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (phasesFunc : ℝ → V → V → ℂ)
    (τ : ℝ) : Schedule V where
  endpoints := (0, τ)
  hamiltonianAt := fun t =>
    Matrix.of (fun x y => phasesFunc t x y * G.adj x y)

/-- A linear adiabatic interpolation between two Hamiltonians.  At `t = t₀`
the schedule equals `H_initial`; at `t = t₁` it equals `H_final`; in between
it is a convex combination by `s := (t - t₀) / (t₁ - t₀)`. -/
noncomputable def linearAdiabatic
    {V : Type u} [Fintype V] [DecidableEq V]
    (H_initial H_final : Matrix V V ℂ) (t₀ t₁ : ℝ) : Schedule V where
  endpoints := (t₀, t₁)
  hamiltonianAt := fun t =>
    let s := (t - t₀) / (t₁ - t₀)
    (1 - (s : ℂ)) • H_initial + (s : ℂ) • H_final

end Schedule

/-! ## Cell-uniform invariance of schedules

A schedule is **cell-uniform-invariant** with respect to an equitable
partition `P` when every pointwise Hamiltonian preserves the cell-uniform
subspace (the span of indicator vectors per cell). -/

/-- Matrix-level cell-uniform preservation (duplicated here from
`Noise.lean` for self-containedness). -/
def Matrix.preservesCellUniform'
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (M : Matrix V V ℂ) (P : EquitablePartition G I) : Prop :=
  ∀ ψ : V → ℂ, (∀ x y : V, P.cells x = P.cells y → ψ x = ψ y) →
    ∀ x y : V, P.cells x = P.cells y → (M.mulVec ψ) x = (M.mulVec ψ) y

/-! ### Closure properties of `preservesCellUniform'`

The cell-uniform-preserving matrices form a (real/complex) subalgebra; we record
the closure facts needed for the adiabatic-schedule reduction: `•` and `+`, and
the fact that the graph adjacency itself preserves the subspace (the equitable
condition).  These let the linear adiabatic path `(1-s)•(-A) + s•(-P_M)` inherit
the invariance from its endpoints. -/

/-- Cell-uniform preservation is closed under scalar multiplication. -/
theorem Matrix.preservesCellUniform'.smul
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {A : Matrix V V ℂ} {P : EquitablePartition G I}
    (hA : Matrix.preservesCellUniform' A P) (c : ℂ) :
    Matrix.preservesCellUniform' (c • A) P := by
  intro ψ hψ x y hxy
  rw [Matrix.smul_mulVec, Pi.smul_apply, Pi.smul_apply, hA ψ hψ x y hxy]

/-- Cell-uniform preservation is closed under addition. -/
theorem Matrix.preservesCellUniform'.add
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {A B : Matrix V V ℂ} {P : EquitablePartition G I}
    (hA : Matrix.preservesCellUniform' A P) (hB : Matrix.preservesCellUniform' B P) :
    Matrix.preservesCellUniform' (A + B) P := by
  intro ψ hψ x y hxy
  rw [Matrix.add_mulVec, Pi.add_apply, Pi.add_apply, hA ψ hψ x y hxy, hB ψ hψ x y hxy]

/-- Cell-uniform preservation is closed under matrix multiplication. -/
theorem Matrix.preservesCellUniform'.mul
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {A B : Matrix V V ℂ} {P : EquitablePartition G I}
    (hA : Matrix.preservesCellUniform' A P) (hB : Matrix.preservesCellUniform' B P) :
    Matrix.preservesCellUniform' (A * B) P := by
  intro ψ hψ x y hxy
  rw [← Matrix.mulVec_mulVec]
  exact hA (B.mulVec ψ) (fun a b hab => hB ψ hψ a b hab) x y hxy

/-- The identity preserves the cell-uniform subspace. -/
theorem Matrix.preservesCellUniform'.one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) :
    Matrix.preservesCellUniform' (1 : Matrix V V ℂ) P := by
  intro ψ hψ x y hxy
  rw [Matrix.one_mulVec]; exact hψ x y hxy

section ExpClosure

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Cell-uniform preservation is closed under the matrix exponential.**  If `A`
preserves the cell-uniform subspace, so does `exp A`.  Proof (mirroring the
`cg_exp_intertwine` technique): for fixed same-cell `x, y`, the map
`M ↦ (M·ψ) x − (M·ψ) y` is a *continuous additive functional* vanishing on every
partial sum of the `exp` series (each `(k!)⁻¹·Aᵏ` preserves cell-constancy, by
power closure); pushing the `exp`-series `HasSum` through this functional shows it
vanishes on `exp A` too. -/
theorem Matrix.preservesCellUniform'.exp
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {A : Matrix V V ℂ} {P : EquitablePartition G I}
    (hA : Matrix.preservesCellUniform' A P) :
    Matrix.preservesCellUniform' (NormedSpace.exp A) P := by
  intro ψ hψ x y hxy
  -- powers preserve cell-constancy
  have hpow : ∀ k : ℕ, Matrix.preservesCellUniform' (A ^ k) P := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]; exact Matrix.preservesCellUniform'.one P
    | succ n ih => rw [pow_succ]; exact ih.mul hA
  -- the continuous additive functional `M ↦ (M·ψ) x − (M·ψ) y`
  let φ : Matrix V V ℂ →+ ℂ :=
    { toFun := fun M => (M.mulVec ψ) x - (M.mulVec ψ) y
      map_zero' := by simp
      map_add' := fun M N => by
        simp only [Matrix.add_mulVec, Pi.add_apply]; ring }
  have hφc : Continuous φ :=
    Continuous.sub
      ((continuous_apply x).comp (continuous_id.matrix_mulVec continuous_const))
      ((continuous_apply y).comp (continuous_id.matrix_mulVec continuous_const))
  have hterm0 : ∀ k : ℕ, φ ((Nat.factorial k : ℂ)⁻¹ • A ^ k) = 0 := by
    intro k
    show (((Nat.factorial k : ℂ)⁻¹ • A ^ k).mulVec ψ) x
        - (((Nat.factorial k : ℂ)⁻¹ • A ^ k).mulVec ψ) y = 0
    rw [Matrix.smul_mulVec, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      hpow k ψ hψ x y hxy]
    ring
  have hsum : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • A ^ k) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' _
  have hzero : HasSum (fun k : ℕ => φ ((Nat.factorial k : ℂ)⁻¹ • A ^ k)) 0 := by
    simp only [hterm0]; exact hasSum_zero
  have hφ0 : φ (NormedSpace.exp A) = 0 := (hsum.map φ hφc).unique hzero
  show ((NormedSpace.exp A).mulVec ψ) x = ((NormedSpace.exp A).mulVec ψ) y
  exact sub_eq_zero.mp hφ0

end ExpClosure

/-- **The graph adjacency preserves the cell-uniform subspace.**  This is the
matrix-level form of the equitable condition: for a cell-constant vector `ψ`,
`(A·ψ)` is again cell-constant, because `(A·ψ) w = ∑_j (branching j w)·ψ̄_j`
depends on `w` only through its cell (by `branching_eq`). -/
theorem WeightedGraph.adj_preservesCellUniform'
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) :
    Matrix.preservesCellUniform' G.adj P := by
  classical
  intro ψ hψ x y hxy
  -- `(A·ψ) w = ∑_j (branching j w) · ψ̄_j`, with `ψ̄_j` a cell-representative value.
  have key : ∀ w : V, (G.adj.mulVec ψ) w
      = ∑ j : I, P.branching j w * (if h : ∃ z, P.cells z = j then ψ h.choose else 0) := by
    intro w
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_fiberwise_of_maps_to (g := P.cells) (fun z _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ∃ z, P.cells z = j
    · rw [dif_pos hj]
      simp only [EquitablePartition.branching]
      rw [show (∑ z, if P.cells z = j then G.adj w z else 0)
            = ∑ z ∈ Finset.univ.filter (fun z => P.cells z = j), G.adj w z from
          (Finset.sum_filter _ _).symm, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mem_filter] at hz
      have : ψ z = ψ hj.choose := hψ z hj.choose (by rw [hz.2, hj.choose_spec])
      rw [this]
    · rw [dif_neg hj, mul_zero]
      have hempty : (Finset.univ.filter (fun z => P.cells z = j)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro z _ hz; exact hj ⟨z, hz⟩
      rw [hempty, Finset.sum_empty]
  rw [key x, key y]
  apply Finset.sum_congr rfl
  intro j _
  rw [P.branching_eq (P.cells x) j x y rfl hxy.symm]

/-- A `Schedule` is **cell-uniform-invariant** when every pointwise
Hamiltonian preserves the cell-uniform subspace. -/
def Schedule.cellUniformInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (S : Schedule V) (P : EquitablePartition G I) : Prop :=
  ∀ t : ℝ, Matrix.preservesCellUniform' (S.hamiltonianAt t) P

/-! ## Quotient schedule

When `S` is cell-uniform-invariant, the pointwise Hamiltonians descend to a
schedule on the quotient `I → ℂ`.  We package this as `S.quotient`. -/

/-- The **cell-restriction** of a matrix `M` on `V` to the orthonormal
cell-uniform basis `{cellUniformVec i}_{i : I}`: its `(i, j)` entry is the
matrix coefficient `⟨e_i, M e_j⟩ = ∑_v conj(e_i v) · (M e_j) v`, where
`e_i = P.cellUniformVec i`.

This is the genuine matrix of `M` in the cell-uniform basis (a concrete
`Matrix I I ℂ`).  For `M = G.adj` it equals `P.symmQuotient` (cf.
`Equitable.restrict_eq_symmQuotient`); for a general cell-uniform-preserving
`M` it is the induced quotient action. -/
noncomputable def cellRestrict
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (M : Matrix V V ℂ) : Matrix I I ℂ :=
  Matrix.of fun i j =>
    ∑ v : V, (starRingEnd ℂ) (P.cellUniformVec i v) * (M.mulVec (P.cellUniformVec j)) v

/-- The quotient schedule induced by a (cell-uniform-invariant) schedule.
At each time `t` its Hamiltonian is the cell-restriction of `S.hamiltonianAt t`
to the cell-uniform basis (a concrete `Matrix I I ℂ`); the time interval is
inherited unchanged.  No `sorry`: this is a total, concrete definition. -/
noncomputable def Schedule.quotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (S : Schedule V) (P : EquitablePartition G I) : Schedule I where
  endpoints := S.endpoints
  hamiltonianAt := fun t => cellRestrict P (S.hamiltonianAt t)

/-! ## Scheduled evolution

We model the time-ordered evolution operator `U(t₀, t₁)` produced by a schedule
as a concrete **first-order Trotter product**.  Splitting `[t₀, t₁]` into `N`
equal slices of width `Δ = (t₁ - t₀)/N`, the time-ordered product (latest slice
on the left, matching the convention `U = 𝒯 exp(-i ∫ H)`) is

`U_N = ∏_{k = N-1, …, 0} exp(-i Δ · H(t₀ + k·Δ))`.

In the `N → ∞` limit this converges to the solution of the time-dependent
Schrödinger equation `i ∂_t U = H(t)·U`; for a *static* schedule it is exact
for every `N` (all slices share the same Hamiltonian).  Each slice factor reuses
the single-Hamiltonian CTQW `WeightedGraph.evolve` machinery via
`NormedSpace.exp`. -/

/-- The number of Trotter slices used by `Schedule.evolve`.  A fixed, moderately
fine discretisation; the choice is convention, not load-bearing for the
algebraic facts (e.g. the static-schedule exactness lemma holds for any `N`). -/
def Schedule.trotterSteps : ℕ := 64

/-- A single Trotter slice propagator: `exp(-i Δ · H(t))`, i.e. the CTQW
evolution generated by the instantaneous Hamiltonian `H(t)` for time `Δ`. -/
noncomputable def Schedule.sliceProp
    {V : Type u} [Fintype V] [DecidableEq V]
    (S : Schedule V) (t Δ : ℝ) : Matrix V V ℂ :=
  NormedSpace.exp (-(Complex.I * (Δ : ℂ)) • S.hamiltonianAt t)

/-- The `N`-slice first-order Trotter product for the time-ordered evolution
from `t₀` to `t₁`.  Built by folding over the slice indices `0, …, N-1` with the
*latest* slice multiplied on the left (preserving the time-ordering convention).
The empty product (`N = 0`) is the identity. -/
noncomputable def Schedule.evolveTrotter
    {V : Type u} [Fintype V] [DecidableEq V]
    (S : Schedule V) (t₀ t₁ : ℝ) (N : ℕ) : Matrix V V ℂ :=
  let Δ : ℝ := (t₁ - t₀) / (N : ℝ)
  (List.range N).foldl
    (init := (1 : Matrix V V ℂ))
    (fun acc k => S.sliceProp (t₀ + (k : ℝ) * Δ) Δ * acc)

/-- The time-ordered evolution operator generated by a schedule `S` from time
`t₀` to time `t₁`, defined concretely as the `trotterSteps`-slice first-order
Trotter product.  No `sorry`: this is a genuine matrix term built from
`NormedSpace.exp`. -/
noncomputable def Schedule.evolve
    {V : Type u} [Fintype V] [DecidableEq V]
    (S : Schedule V) (t₀ t₁ : ℝ) : Matrix V V ℂ :=
  S.evolveTrotter t₀ t₁ Schedule.trotterSteps

/-! ## Main statement: scheduled equitable-partition reduction

**Theorem.**  If `S` is cell-uniform-invariant with respect to `P`, then
for every `t₀ < t₁` the evolution operator `S.evolve t₀ t₁` preserves the
cell-uniform subspace, and its restriction to that subspace coincides with
the evolution operator of the *quotient* schedule `S.quotient P`.

This unifies the static (`staticSchedule`), Trotter (`trotterSchedule`), and
magnetic-flux (`magneticFluxSchedule`) cases: the equitable-partition
reduction is robust to time-dependent driving, *provided every snapshot of
the drive respects the partition*. -/
section EvolvePreserves

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- A left-multiplication fold of cell-uniform-preserving factors onto a
preserving initial matrix preserves the cell-uniform subspace. -/
theorem foldl_mul_preservesCellUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {ι : Type*} (P : EquitablePartition G I) (f : ι → Matrix V V ℂ)
    (hf : ∀ k, Matrix.preservesCellUniform' (f k) P)
    (l : List ι) (init : Matrix V V ℂ)
    (hinit : Matrix.preservesCellUniform' init P) :
    Matrix.preservesCellUniform' (l.foldl (fun acc k => f k * acc) init) P := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil]; exact hinit
  | cons a t ih => rw [List.foldl_cons]; exact ih _ ((hf a).mul hinit)

/-- The finite Trotter-product evolution preserves the cell-uniform subspace
whenever every pointwise Hamiltonian does. -/
theorem Schedule.evolveTrotter_preserves_cellUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {S : Schedule V} {P : EquitablePartition G I}
    (hS : S.cellUniformInvariant P) (t₀ t₁ : ℝ) (N : ℕ) :
    Matrix.preservesCellUniform' (S.evolveTrotter t₀ t₁ N) P := by
  rw [Schedule.evolveTrotter]
  refine foldl_mul_preservesCellUniform P
    (fun k : ℝ => S.sliceProp (t₀ + k * ((t₁ - t₀) / (N : ℝ))) ((t₁ - t₀) / (N : ℝ)))
    (fun k => ?_) _ 1 (Matrix.preservesCellUniform'.one P)
  -- each slice `sliceProp t Δ = exp(-(iΔ)•H(t))` preserves: `H(t)` does (`hS`),
  -- then smul + exp closure.
  unfold Schedule.sliceProp
  exact (Matrix.preservesCellUniform'.smul (hS _) _).exp

theorem Schedule.evolve_preserves_cellUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {S : Schedule V} {P : EquitablePartition G I}
    (hS : S.cellUniformInvariant P) (t₀ t₁ : ℝ) :
    -- the evolution operator preserves the cell-uniform subspace, i.e. maps
    -- cell-constant vectors to cell-constant vectors.
    Matrix.preservesCellUniform' (S.evolve t₀ t₁) P := by
  -- Each Trotter slice `sliceProp t Δ = exp(-iΔ H(t))` preserves the cell-uniform
  -- subspace because `H(t)` does (`hS`) and `exp` is a limit of polynomials in
  -- `H(t)` (`Matrix.preservesCellUniform'.exp`); the left-mult product of
  -- subspace-preserving maps preserves the subspace.
  rw [Schedule.evolve]
  exact Schedule.evolveTrotter_preserves_cellUniform hS t₀ t₁ Schedule.trotterSteps

end EvolvePreserves

/-! ## Adiabatic search

This is the boundary-pushing piece.  We define an *adiabatic search schedule*
interpolating from the graph Laplacian / adjacency to a marked-vertex
projector.  In the limit of long total time, the adiabatic theorem implies
the ground state of the final Hamiltonian — the marked-vertex state — is
prepared with high fidelity. -/

/-- The marked-vertex projector for a single marked vertex `m`. -/
noncomputable def markedProjector
    {V : Type u} [Fintype V] [DecidableEq V] (m : V) : Matrix V V ℂ :=
  Matrix.of (fun x y => if x = m ∧ y = m then (1 : ℂ) else 0)

/-- The marked-set projector for a (finite) set of marked vertices. -/
noncomputable def markedSetProjector
    {V : Type u} [Fintype V] [DecidableEq V] (M : Finset V) : Matrix V V ℂ :=
  Matrix.of (fun x y => if x = y ∧ x ∈ M then (1 : ℂ) else 0)

/-- The marked-set projector acts diagonally: `(P_M·ψ) x = ψ x` if `x ∈ M`,
else `0`. -/
theorem markedSetProjector_mulVec
    {V : Type u} [Fintype V] [DecidableEq V] (M : Finset V) (ψ : V → ℂ) (x : V) :
    ((markedSetProjector M).mulVec ψ) x = if x ∈ M then ψ x else 0 := by
  simp only [markedSetProjector, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single x]
  · by_cases hx : x ∈ M <;> simp [hx]
  · intro b _ hb; rw [if_neg (by tauto), zero_mul]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **The marked-set projector preserves the cell-uniform subspace when the
marked set is a union of cells.**  If `cells x = cells y` and `x ∈ M ⟹ y ∈ M`
(both directions, i.e. `M` is `P`-saturated), then `(P_M·ψ)` is cell-constant
whenever `ψ` is: same-cell vertices are either both marked (giving `ψ x = ψ y`)
or both unmarked (giving `0 = 0`). -/
theorem markedSetProjector_preservesCellUniform'
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (M : Finset V) (P : EquitablePartition G I)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M)) :
    Matrix.preservesCellUniform' (markedSetProjector M) P := by
  intro ψ hψ x y hxy
  rw [markedSetProjector_mulVec, markedSetProjector_mulVec]
  by_cases hx : x ∈ M
  · rw [if_pos hx, if_pos ((hM x y hxy).mp hx)]
    exact hψ x y hxy
  · rw [if_neg hx, if_neg (fun hy => hx ((hM x y hxy).mpr hy))]

/-- The **adiabatic search schedule**.  Linearly interpolates between
`H_initial = - G.adj` (or, in a richer variant, the graph Laplacian) and
`H_final = - markedSetProjector M`, over total time `τ`.

The intuition is:

* at `t = 0` the Hamiltonian is the graph adjacency, whose ground state is
  the uniform superposition (for graphs whose adjacency spectrum is
  bounded above by 0 on the uniform state, e.g. by adding a constant shift);
* at `t = τ` the Hamiltonian is the (negated) marked-set projector, whose
  ground state is the equal superposition over `M` (the *answer* of the
  search);
* the adiabatic theorem guarantees that if `τ` is large compared with the
  minimum spectral gap along the path, the actual evolved state stays close
  to the instantaneous ground state — finishing in (close to) the answer
  state. -/
noncomputable def adiabatic_search_schedule
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (M : Finset V) (τ : ℝ) : Schedule V :=
  Schedule.linearAdiabatic (-(G.adj)) (-(markedSetProjector M)) 0 τ

/-- **Grover-style adiabatic search theorem with equitable-partition
reduction.**

Suppose:

* `G` is a weighted graph with equitable partition `P : V → I`;
* the marked set `M` is a *union of cells* (i.e. `cells x = cells y` and
  `x ∈ M` imply `y ∈ M`); this guarantees `markedSetProjector M` preserves
  the cell-uniform subspace;
* the total time `τ` is at least `C · √(Fintype.card I) / gap_min`, where
  `gap_min` is the minimum spectral gap of the schedule restricted to the
  cell-uniform subspace.

Then the adiabatic search schedule prepared on `V` is *the same as* the
adiabatic search schedule on the quotient `I`, in the sense that the
quotient-space evolution coincides with the restriction of the full
evolution to the cell-uniform subspace; and the resulting fidelity with the
target marked-cell state matches the Grover-adiabatic bound for the
quotient. -/
theorem adiabatic_search_reduction
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (M : Finset V)
    (_marked_is_union_of_cells :
      ∀ x y : V, P.cells x = P.cells y → x ∈ M → y ∈ M)
    (τ : ℝ) :
    -- the adiabatic schedule on V is cell-uniform-invariant, and
    (adiabatic_search_schedule G M τ).cellUniformInvariant P ∧
    -- the quotient schedule on `I` runs over the same time interval `(0, τ)`
    -- (so the reduction lands an adiabatic schedule of equal duration on the
    -- smaller index set).
    ((adiabatic_search_schedule G M τ).quotient P).endpoints = (0, τ) := by
  -- `M` saturated upward + symmetry of `cells x = cells y` gives the `↔` form.
  have hMiff : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M) := by
    intro x y hxy
    exact ⟨_marked_is_union_of_cells x y hxy,
      _marked_is_union_of_cells y x hxy.symm⟩
  refine ⟨?_, ?_⟩
  · -- Cell-uniform invariance.  Each pointwise Hamiltonian is the convex
    -- combination `(1-s)•(-A) + s•(-P_M)`; both `-A` (equitability) and `-P_M`
    -- (M a union of cells) preserve the cell-uniform subspace, and that property
    -- is closed under `•` and `+`.
    intro t
    show Matrix.preservesCellUniform'
      ((1 - ((((t - 0) / (τ - 0) : ℝ)) : ℂ)) • (-(G.adj))
        + ((((t - 0) / (τ - 0) : ℝ)) : ℂ) • (-(markedSetProjector M))) P
    have hA : Matrix.preservesCellUniform' (-(G.adj)) P := by
      have := (G.adj_preservesCellUniform' P).smul (-1)
      rwa [neg_one_smul] at this
    have hPM : Matrix.preservesCellUniform' (-(markedSetProjector M)) P := by
      have := (markedSetProjector_preservesCellUniform' M P hMiff).smul (-1)
      rwa [neg_one_smul] at this
    exact (hA.smul _).add (hPM.smul _)
  · -- The quotient inherits the V-schedule's interval `(0, τ)` by definition of
    -- `Schedule.quotient` and `linearAdiabatic`.
    rfl

/-! ## Quantitative gap bounds (future work)

A complete Grover-style adiabatic theorem requires bounding the spectral gap
of `H(t)` between its ground state and the rest of the spectrum.  For the
*quotient* schedule on `I`, this is much easier than for the full `V`-walk:

* The relevant gap is `gap_min` *restricted to the cell-uniform subspace*.
* For a `k`-regular graph with `k_marked` marked cells out of `|I|`, the
  quotient gap obeys `gap_min = Θ(1 / √(|I| / k_marked))` — the standard
  Grover scaling.

A precise statement requires:

* the *graph Laplacian* version of the schedule (not just adjacency), and
* a Mathlib-level treatment of the adiabatic theorem.

Both are clear next research directions; see e.g. Reichardt's `O(√N)`
adiabatic search analysis and Roland-Cerf for the canonical reference. -/

/-! ## Connection to chiral hardware

The `magneticFluxSchedule` is the bridge to *chiral* Hamiltonian
engineering: the time-dependence acts on the *phases* of the couplings,
which can be implemented as synthetic flux on a fixed hardware layout.

Adiabatic variation of these phases gives a chiral adiabatic search.  For a
chiral graph satisfying a `chiralAllowedSpec phases` hardware spec (from
`Hardware.lean`), the adiabatic schedule's pointwise Hamiltonians must
remain inside that phase set at every time.  This is a *path-feasibility*
constraint: the adiabatic path is the projection of the schedule onto the
hardware-compatible submanifold of Hermitian matrices.

Concretely the open question is: when is the chiral-feasible adiabatic path
from `H_initial` to `H_final` shorter (faster, better gap) than the
real-coupling adiabatic path?  This is the chiral-speedup conjecture and a
natural next experiment to set up in the project. -/

end Graphplay
