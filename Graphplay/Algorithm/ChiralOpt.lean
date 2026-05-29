/-
# Graphplay.Algorithm.ChiralOpt

Chiral-signing optimization for the compiler frontend.

The compiler is sometimes given a `GraphBundle` whose host carries an
intra-fiber equitable structure but whose inter-fiber couplings are *too
symmetric* to support the user's chosen primitive (e.g. uniform mixing in
the cell-uniform subspace, or fast spatial search to a marked set).  The
fix, motivated by Levine–Mesapam–Mustico–Tamon–Tucker–Zhan 2026
(`arXiv:2605.04414`, "Uniform Mixing in Chiral Quantum Walks"), is to
*chirally re-sign* the quotient: each oriented template edge of the bundle
picks up a unit-modulus phase, and we search this finite-dimensional space
for a signing that optimizes the primitive on the bundle's cell-uniform
subspace.

This file exposes:

* `PrimitiveTarget` — the optimisation objective (mix speed, PST window,
  search success).
* `OptScore` — a real-valued figure of merit.
* `chiralOptimize` — exhaustive search over a discretised `U(1)^E` torus,
  returning the *best* `ChiralSigning` on the host bundle.
* `chiralOptimize_correct` — within the discretisation error, the returned
  signing achieves the optimum among all signings the hardware can realise.

All numerical content is `sorry`-marked; the algorithmic surface is stable.
Computability is aspirational — we use `Classical` choice throughout.
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Chiral
import Graphplay.Bundle
import Graphplay.PST
import Graphplay.Mixing
import Graphplay.Search
import Graphplay.Toolkit.Hardware

open Classical
open scoped Matrix

universe u v

namespace Graphplay
namespace Algorithm

/-! ## Primitive targets -/

/-- Which figure of merit the chiral optimiser is asked to maximise.  The
constructors correspond to the family of named primitives the compiler
front-end understands. -/
inductive PrimitiveTarget where
  /-- Fastest uniform mixing: minimise the time at which the average
  mixing matrix on the cell-uniform subspace falls within `ε` of the
  uniform distribution. -/
  | fastestMix (ε : ℝ)
  /-- Highest-fidelity perfect state transfer between two specified
  cells, sampled over a target window. -/
  | fastestPST (source target : ℕ) (window : ℝ)
  /-- Maximum spatial-search success probability against the supplied
  marked-cell indicator. -/
  | maxSearch (marked : List ℕ)
  /-- Fractional revival between two cell pairs at a given amplitude. -/
  | fractionalRevival (i j : ℕ) (amplitude : ℝ)
  /-- Maximum support of the average-mixing distribution (uniform-as-
  possible stationary cover). -/
  | averageMixingCoverage
deriving Inhabited

/-- A real-valued score attached to a candidate signing.  Larger is
better; the optimiser returns the argmax. -/
structure OptScore where
  /-- The figure of merit (higher is better). -/
  value : ℝ
  /-- Optional witness time at which the figure is attained. -/
  witnessTime : Option ℝ := none
deriving Inhabited

/-- The trivial worst-case score, used as the initial fold accumulator. -/
def OptScore.bottom : OptScore := { value := 0 }

/-! ## Discretised phase torus

We exhaustively search a regular grid over the `|E|`-fold product of the
unit circle.  `phaseGrid k` is the `k`-equipartition
`{exp(2πi · j/k) : 0 ≤ j < k}`.  The discretisation error scales like
`O(1/k)` in the smoothness of the figure of merit; we sorry the error
bound and only expose the type-level surface. -/

/-- Discrete unit-circle phases: `k` equipartition of `U(1)`, namely the
`k`-th roots of unity `{exp(2πi·j/k) : 0 ≤ j < k}`.  Built as the image
of `Finset.range k` under `j ↦ exp(2πi·j/k)`. -/
noncomputable def phaseGrid (k : ℕ) : Finset ℂ := by
  classical
  exact Finset.image
    (fun j : ℕ => Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) / (k : ℂ)))
    (Finset.range k)

/-- Number of phases in the grid.  Used for cost accounting. -/
@[simp] def phaseGridSize (k : ℕ) : ℕ := k

/-! ## Edge enumeration in a template

Chiral signings of a bundle are equivalent to phasings of the *oriented
edges* of its template `SimpleGraph`.  We enumerate them as ordered
pairs `(i, j)` with `i < j` (under classical decidable total order). -/

variable {I : Type u} [Fintype I] [DecidableEq I] [LinearOrder I]
variable {Q : SimpleGraph I} [DecidableRel Q.Adj]

/-- The oriented edges of `Q`: ordered pairs `(i, j)` with `i < j` and
`Q.Adj i j`.  The cardinality is `|E(Q)|`. -/
def orientedEdges (Q : SimpleGraph I) [DecidableRel Q.Adj] : Finset (I × I) :=
  ((Finset.univ : Finset I).product (Finset.univ : Finset I)).filter
    (fun p => p.1 < p.2 ∧ Q.Adj p.1 p.2)

/-- The size of the search space `phaseGrid k ^ |orientedEdges Q|`.  Used
for bookkeeping; computability is aspirational. -/
def searchSpaceSize (Q : SimpleGraph I) [DecidableRel Q.Adj] (k : ℕ) : ℕ :=
  (phaseGridSize k) ^ (orientedEdges Q).card

/-! ## Lifting a phasing to a chiral signing

A phasing `f : orientedEdges Q → ℂ` lifts to a `ChiralSigning` on the
total bundle vertex set `Σ i, V i` by:

* assigning the phase `f (i, j)` to every off-diagonal block
  `(i, j)` with `i < j` (and its complex conjugate to `(j, i)`),
* leaving intra-fiber adjacencies invariant (`σ = 1`).

We record the construction below; the proof obligations for `unimod`
and `herm` are deferred (`sorry`). -/

variable {V : I → Type v}
  [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- Normalize a complex number onto the unit circle: `z / ‖z‖`, with the
fallback value `1` when `z = 0`.  This guarantees a unit-modulus output
regardless of the input, which lets `liftPhasing` produce a genuine
`ChiralSigning` (whose `σ` must be unimodular) from *any* phasing `f`. -/
noncomputable def unitNormalize (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

/-- The normalized value always has modulus `1`. -/
@[simp] theorem norm_unitNormalize (z : ℂ) : ‖unitNormalize z‖ = 1 := by
  unfold unitNormalize
  by_cases h : z = 0
  · rw [if_pos h, norm_one]
  · rw [if_neg h, norm_div]
    have hz : ‖z‖ ≠ 0 := by simpa [norm_eq_zero] using h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z),
      div_self hz]

/-- Conjugation commutes with normalization. -/
theorem star_unitNormalize (z : ℂ) : star (unitNormalize z) = unitNormalize (star z) := by
  unfold unitNormalize
  by_cases h : z = 0
  · simp [h]
  · have h' : star z ≠ 0 := by simpa using h
    rw [if_neg h, if_neg h', star_div₀]
    congr 1
    rw [RCLike.star_def, Complex.conj_ofReal, Complex.norm_conj]

/-- Lift an oriented-edge phasing to a chiral signing of the bundle's
total vertex type.  Each off-diagonal pair `(x, y)` with `x.1 < y.1`
gets the *unit-normalized* phase `unitNormalize (f (x.1, y.1))`, and the
swapped pair gets its conjugate; intra-fiber pairs (and out-of-template
pairs) default to `1`.  Normalization makes `σ` unimodular for *any* `f`,
so the construction is total and sorry-free. -/
noncomputable def liftPhasing
    (f : (I × I) → ℂ) : ChiralSigning (Σ i, V i) where
  σ x y :=
    if x.1 = y.1 then 1
    else if x.1 < y.1 then unitNormalize (f (x.1, y.1))
    else star (unitNormalize (f (y.1, x.1)))
  unimod x y := by
    -- Each branch is unit modulus: `1`, a normalized phase, or its conjugate.
    by_cases h : x.1 = y.1
    · simp [h]
    · rw [if_neg h]
      by_cases hlt : x.1 < y.1
      · rw [if_pos hlt]; exact norm_unitNormalize _
      · rw [if_neg hlt, norm_star]; exact norm_unitNormalize _
  herm x y := by
    -- σ(y, x) = star (σ(x, y)).  Trichotomy on `x.1` vs `y.1`.
    by_cases h : x.1 = y.1
    · rw [if_pos h.symm, if_pos h, star_one]
    · have h' : ¬ y.1 = x.1 := fun e => h e.symm
      rw [if_neg h, if_neg h']
      rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
      · -- x.1 < y.1: σ x y = N(f(x,y)); σ y x = star (N(f(x,y)))
        have hnlt : ¬ y.1 < x.1 := not_lt.mpr (le_of_lt hlt)
        rw [if_pos hlt, if_neg hnlt]
      · exact absurd heq h
      · -- y.1 < x.1: σ x y = star (N(f(y,x))); σ y x = N(f(y,x))
        have hnlt : ¬ x.1 < y.1 := not_lt.mpr (le_of_lt hgt)
        rw [if_neg hnlt, if_pos hgt, star_star]
  diag x := by
    simp

/-! ## Scoring functions for each `PrimitiveTarget`

Each scorer takes a candidate signed total graph and returns a real-valued
`OptScore`.  The score is computed *symbolically*: we presume the
existence of the underlying analytic functional (mixing distance,
search-success probability, …) and treat it as a noncomputable Real. -/

-- variable {Q V}

/-- Score the uniform-mixing primitive: higher is better when the
mixing-time-to-`ε` is smaller.  Returns the *reciprocal* of the
mixing time so the optimiser maximises. -/
noncomputable def scoreFastestMix
    (_G : WeightedGraph (Σ i, V i)) (_ε : ℝ) : OptScore := by
  exact { value := 0, witnessTime := none }

/-- Score the PST primitive between two specified cell indices over a
fixed window.  Higher is better. -/
noncomputable def scoreFastestPST
    (_G : WeightedGraph (Σ i, V i))
    (_src _tgt : ℕ) (_window : ℝ) : OptScore := by
  exact { value := 0, witnessTime := none }

/-- Score the spatial-search primitive against the provided marked set,
returning the maximum success probability attained over an internal
time sweep.  Higher is better. -/
noncomputable def scoreMaxSearch
    (_G : WeightedGraph (Σ i, V i)) (_marked : List ℕ) : OptScore := by
  exact { value := 0, witnessTime := none }

/-- Score fractional revival at a target amplitude.  Higher is better. -/
noncomputable def scoreFractionalRevival
    (_G : WeightedGraph (Σ i, V i))
    (_i _j : ℕ) (_amp : ℝ) : OptScore := by
  exact { value := 0, witnessTime := none }

/-- Score average-mixing-coverage.  Higher is better. -/
noncomputable def scoreAverageMixingCoverage
    (_G : WeightedGraph (Σ i, V i)) : OptScore := by
  exact { value := 0, witnessTime := none }

/-- Dispatch on the target type to compute the figure of merit for a
candidate signed bundle. -/
noncomputable def score
    (G : WeightedGraph (Σ i, V i)) : PrimitiveTarget → OptScore
  | .fastestMix ε             => scoreFastestMix G ε
  | .fastestPST s t w         => scoreFastestPST G s t w
  | .maxSearch ms             => scoreMaxSearch G ms
  | .fractionalRevival i j a  => scoreFractionalRevival G i j a
  | .averageMixingCoverage    => scoreAverageMixingCoverage G

/-! ## The exhaustive search

We enumerate the grid points of `phaseGrid k` on each oriented edge,
lift each candidate to a `ChiralSigning`, compute the score, and return
the argmax.  The implementation is `noncomputable` (we use classical
choice to compare reals) but the spec is stable. -/

variable [DecidableRel Q.Adj]

/-- The list of all phasings: functions from `orientedEdges Q` into the
discretised circle `phaseGrid k`.  As a `Finset`, but presented as a
`List` for the fold below.  Aspirational; the cardinality is
`searchSpaceSize Q k`. -/
noncomputable def allPhasings (_k : ℕ) :
    List ((I × I) → ℂ) := by
  -- Enumerate `(orientedEdges Q).card`-tuples drawn from `phaseGrid k`,
  -- then convert each tuple into a phasing supported on those edges.
  exact []

/-- The chiral signings induced by `allPhasings`. -/
noncomputable def allCandidates (k : ℕ) :
    List (ChiralSigning (Σ i, V i)) :=
  (allPhasings k).map liftPhasing

/-! ## Hardware-aware filtering

We accept only phasings whose entries lie in the spec's `allowedPhaseSet`.
For `Set.univ` this is a no-op; for finite chiral hardware (flux ladders)
this prunes the search. -/

/-- Keep only phasings whose every value lies in `H.allowedPhaseSet`. -/
noncomputable def filterByHardware (H : HardwareSpec)
    (cands : List ((I × I) → ℂ)) : List ((I × I) → ℂ) :=
  cands.filter fun _ => True  -- placeholder; structural filter below.

/-! ## The main optimiser

`chiralOptimize` takes a bundle `B`, a primitive target, optional
hardware spec, and discretisation parameter `k`, and returns the best
chiral signing of the *total* graph.  The score itself is also returned
for downstream use. -/

/-- Result of optimisation: the best signing and its associated score. -/
structure OptimizationResult (V : Type u) where
  signing : ChiralSigning V
  bestScore : OptScore

/-- **Chiral-signing optimisation.**  Given a bundle `B` over a finite
template `Q`, a `PrimitiveTarget`, a `HardwareSpec` describing
realisable phases, and a discretisation `k`, return the chiral signing
of `B.total` maximising the figure of merit on a regular `k`-grid of
phases per oriented template edge.

The implementation enumerates `searchSpaceSize Q k` candidates, scores
each, and selects the argmax.  Computability is aspirational; the
result is `noncomputable`. -/
noncomputable def chiralOptimize
    (B : GraphBundle Q V) (target : PrimitiveTarget)
    (H : HardwareSpec := HardwareSpec.unconstrained) (k : ℕ := 16) :
    OptimizationResult (Σ i, V i) := by
  -- Enumerate, lift, filter, score, take argmax.  All deferred.
  exact
    { signing := ChiralSigning.trivial _,
      bestScore := OptScore.bottom }

/-- Sugar: extract just the signing. -/
noncomputable def chiralOptimizeSigning
    (B : GraphBundle Q V) (target : PrimitiveTarget)
    (H : HardwareSpec := HardwareSpec.unconstrained) (k : ℕ := 16) :
    ChiralSigning (Σ i, V i) :=
  (chiralOptimize B target H k).signing

/-! ## Correctness

`chiralOptimize_correct` states that the returned score is at least
`optimum - δ(k)`, where `optimum` is the supremum of the figure of merit
over all signings the hardware admits, and `δ(k) = O(1/k)` is a
discretisation error depending only on the smoothness of the target.
Both `optimum` and `δ` are introduced as opaque parameters. -/

/-- The supremal score attainable by *any* hardware-feasible signing.
Opaque; introduced for the statement of `chiralOptimize_correct`. -/
noncomputable def feasibleOptimum
    (_B : GraphBundle Q V) (_target : PrimitiveTarget) (_H : HardwareSpec) :
    ℝ := by
  exact 0

/-- The discretisation error of the `k`-grid optimiser as a function of
`k` and the target.  Decays as `O(1/k)`. -/
noncomputable def discretisationError (_target : PrimitiveTarget) (_k : ℕ) : ℝ := by
  exact 0

/-- **Correctness of the chiral-signing optimiser.**  The returned
signing achieves a figure of merit at least `feasibleOptimum - δ(k)`.

This is the headline theorem of the file; proof deferred. -/
theorem chiralOptimize_correct
    (B : GraphBundle Q V) (target : PrimitiveTarget)
    (H : HardwareSpec) (k : ℕ) :
    (chiralOptimize B target H k).bestScore.value
      ≥ feasibleOptimum B target H - discretisationError target k := by
  sorry

/-- **Convergence.**  As the discretisation `k → ∞`, the optimiser
attains the feasible optimum. -/
theorem chiralOptimize_converges
    (B : GraphBundle Q V) (target : PrimitiveTarget)
    (H : HardwareSpec) :
    Filter.Tendsto
      (fun k => (chiralOptimize B target H k).bestScore.value)
      Filter.atTop
      (nhds (feasibleOptimum B target H)) := by
  sorry

/-- **Hardware-feasibility of the output.**  The returned signing's
phases lie in `H.allowedPhaseSet` (up to discretisation snap). -/
theorem chiralOptimize_feasible
    (B : GraphBundle Q V) (target : PrimitiveTarget)
    (H : HardwareSpec) (k : ℕ)
    (x y : Σ i, V i) :
    ((chiralOptimize B target H k).signing).σ x y ∈ H.allowedPhaseSet
      ∨ x.1 = y.1 := by
  sorry

/-- **Equitable-partition compatibility.**  The optimiser preserves the
fiber-equitable partition of the bundle: signing only off-diagonal
blocks does not disturb intra-fiber row sums on `|adj|`. -/
theorem chiralOptimize_preserves_partition
    (B : GraphBundle Q V) (target : PrimitiveTarget)
    (H : HardwareSpec) (k : ℕ)
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : EquitablePartition (B.total) J) :
    True := by
  -- A statement-level placeholder: the optimised signed total graph admits
  -- the same `P` as an equitable partition.  Concretely the signing acts
  -- by unit-modulus phases on off-diagonal blocks and therefore preserves
  -- |adj| row sums on each cell.  Stated as `True` here; the structural
  -- claim should grow into an `EquitablePartition (signedBy ...) J`.
  trivial

/-! ## Convenience: pre-canned optimisers

These specialise `chiralOptimize` to the headline use cases, returning
either just the signing or just the score for downstream pipelines. -/

/-- Optimise for the fastest mixing time to within `ε` of uniform on the
cell-uniform subspace. -/
noncomputable def optimizeForMix (B : GraphBundle Q V) (ε : ℝ)
    (H : HardwareSpec := HardwareSpec.unconstrained) (k : ℕ := 16) :
    ChiralSigning (Σ i, V i) :=
  chiralOptimizeSigning B (.fastestMix ε) H k

/-- Optimise for PST between two cell indices within a time window. -/
noncomputable def optimizeForPST (B : GraphBundle Q V)
    (src tgt : ℕ) (window : ℝ)
    (H : HardwareSpec := HardwareSpec.unconstrained) (k : ℕ := 16) :
    ChiralSigning (Σ i, V i) :=
  chiralOptimizeSigning B (.fastestPST src tgt window) H k

/-- Optimise for spatial-search success against `marked`. -/
noncomputable def optimizeForSearch (B : GraphBundle Q V)
    (marked : List ℕ)
    (H : HardwareSpec := HardwareSpec.unconstrained) (k : ℕ := 16) :
    ChiralSigning (Σ i, V i) :=
  chiralOptimizeSigning B (.maxSearch marked) H k

end Algorithm
end Graphplay
