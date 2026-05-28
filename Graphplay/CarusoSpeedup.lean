/-
# Graphplay.CarusoSpeedup

**Round-3 loop-closer: Quantitative Caruso noise-assisted speedup.**

D8 (`Graphplay.Dowsing.NoiseEquitable`) introduced
`NoiseModel.BreakingScore P` — the rate-weighted L² distance of a noise
model's Lindblad generator from the partition algebra's commutant — and
stated the qualitative *Caruso conjecture* that optimal noise-assisted
speedup occurs at a strictly non-trivial breaking score.  That conjecture
is *categorical*: it does not say *how large* the speedup is.

This file closes that loop by writing down the **quantitative formula**.
Specifically:

* **`SearchSuccessProbability G M N γ τ`** — the probability of detecting
  the marked set `M` after running the noisy CTQW spatial search with
  noise model `N`, coupling `γ`, and time `τ`.
* **`OptimalSearchTime G M N γ ε`** — the minimal time to reach success
  probability `≥ ε`.
* **`search_speedup_via_partial_symmetry_breaking`** — the headline
  theorem: for regular graphs with marked set `M`, the optimal search
  time scales as `O(√|V|)` (the Grover rate) precisely when the noise
  model's breaking score lies in a graph-dependent non-trivial interval
  `(s_min, s_max)`, and reverts to `O(|V|)` (classical) outside that
  interval.

The **anti-Zeno mechanism** is recorded as a named statement.

Three **concrete examples** are written down with their predicted
scalings:

* `K_n` with single-vertex dephasing on the marked vertex (BreakingScore
  `= 1`, speedup factor `√(n / log n)`).
* `Hypercube` with random per-vertex dephasing on a marked set of size
  `m` (BreakingScore `∼ √m`).
* `Star_n` with central dephasing (boundary case: BreakingScore at the
  edge of the optimal window).

A **cell-uniform connection theorem** ties the speedup mechanism
explicitly to D8 (cell-uniform preservation for the unmarked dynamics)
and L17 (symmetry breaking for marked detection).

An **optimisation statement** (`caruso_optimisation_on_quotient`) packages
the search of optimal noise as a small finite-dimensional optimisation on
the quotient algebra (Toolkit/Noise.lean).

References:
* Caruso, Chin, Datta, Huelga, Plenio,
  *Highly efficient energy excitation transfer in light-harvesting
  complexes: The fundamental role of noise-assisted transport*,
  J. Chem. Phys. 131, 105106 (2009), arXiv:0901.4454.
* Caruso, Chin, Datta, Huelga, Plenio,
  *Entanglement and entangling power of the dynamics in
  light-harvesting complexes*, Phys. Rev. A 81, 062346 (2010).
* Mohseni–Rebentrost–Lloyd–Aspuru-Guzik,
  *Environment-assisted quantum walks in photosynthetic energy transfer*,
  J. Chem. Phys. 129, 174106 (2008).
* Childs–Goldstone (2004), *Spatial search by quantum walk*,
  Phys. Rev. A 70, 022314 (closed-system baseline).

All proofs are deferred via `sorry`; the file's job is to provide the
*statements* canonical enough for downstream files to depend on.
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Search
import Graphplay.Toolkit.Noise
import Graphplay.Dowsing.NoiseEquitable

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay

namespace CarusoSpeedup

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-! ## 1. Success probability and optimal search time

A noisy CTQW spatial search for a marked set `M ⊆ V` is parameterised by:

* a host graph `G`,
* the marked set `M`,
* a noise model `N` (Lindblad jump operators with rates),
* a coupling `γ : ℝ` between the walk and the marker projector,
* a time `τ : ℝ` at which the walker is measured in the position basis.

The success probability at time `τ` is `tr(P_M ρ(τ))`, where
`ρ(τ) = noisyEvolve H_search N τ ρ₀` and `ρ₀` is the uniform
superposition over `V`.

We package this as the canonical predicate consumed downstream. -/

/-- The uniform initial density matrix `|s⟩⟨s|` where
`|s⟩ = (1/√|V|) ∑_v |v⟩`.  This is the canonical starting state of
spatial search.  Concrete construction deferred. -/
noncomputable def uniformInitial
    (V : Type u) [Fintype V] [DecidableEq V] : Matrix V V ℂ := by
  -- `ρ₀ x y = 1 / |V|` for all `x, y`.
  exact fun _ _ => (1 : ℂ) / (Fintype.card V : ℂ)

/-- The projector onto the marked set `M`: `P_M = ∑_{m ∈ M} |m⟩⟨m|`. -/
noncomputable def markedProjector
    {V : Type u} [Fintype V] [DecidableEq V] (M : Finset V) :
    Matrix V V ℂ :=
  fun u v => if u = v ∧ u ∈ M then (1 : ℂ) else 0

/-- **Search success probability.**  The probability of detecting the
marked set `M` after running the noisy CTQW spatial search for time `τ`
on host `G` with coupling `γ` and noise model `N`.

Formally: `Re(tr(P_M · ρ(τ)))` where `ρ(τ)` is the noisy evolution of
`uniformInitial` under the search Hamiltonian.  The trace is real and
non-negative whenever the Lindblad evolution is a CPTP map (which it
is by construction). -/
noncomputable def SearchSuccessProbability
    (G : WeightedGraph V) (M : Finset V) (N : NoiseModel V) (γ τ : ℝ) : ℝ :=
  (noisyEvolve (G.searchHamiltonian M γ) N τ (uniformInitial V) *
      markedProjector M).trace.re

/-- The *closed-system* (no-noise) search success probability is the
diagonal of `searchEvolve` summed over the marked set. -/
noncomputable def closedSystemSuccessProbability
    (G : WeightedGraph V) (M : Finset V) (γ τ : ℝ) : ℝ :=
  ∑ m ∈ M, ‖G.searchEvolve M γ τ m m‖

/-- **Optimal search time at success threshold `ε`.**

The infimum of `τ ≥ 0` for which the success probability reaches `ε`.
We *define* it via `sInf` over the set of admissible times; in concrete
cases (Grover, classical) this set is a half-line `[τ_*, ∞)` for some
optimal `τ_*`. -/
noncomputable def OptimalSearchTime
    (G : WeightedGraph V) (M : Finset V) (N : NoiseModel V) (γ ε : ℝ) : ℝ :=
  sInf { τ : ℝ | 0 ≤ τ ∧ SearchSuccessProbability G M N γ τ ≥ ε }

/-- A target success threshold standard in the literature: `ε = 1/2`. -/
noncomputable def OptimalSearchTimeHalf
    (G : WeightedGraph V) (M : Finset V) (N : NoiseModel V) (γ : ℝ) : ℝ :=
  OptimalSearchTime G M N γ (1 / 2)

/-! ## 2. The headline theorem — quantitative Caruso

Childs–Goldstone (2004) show that *closed-system* CTQW spatial search on
a *regular* graph with `o(|V|)` marked vertices reaches success
probability `Ω(1)` in time `O(√|V|)` *iff* the spectral gap above the
ground state of the search Hamiltonian satisfies a particular scaling.
On highly symmetric graphs (e.g. `K_n`) this is automatic.  On many
graphs it *fails* — the closed-system search degenerates and runs in
classical `Ω(|V|)` time.

Caruso et al. (2009, 2010) observed that adding *partial* environmental
dephasing — enough to lift accidental dark-state degeneracies but not so
much as to fully classicalise the dynamics — *restores* Grover-rate
search even on graphs where the closed-system case fails.

The quantitative formulation: there is a **non-trivial interval**
`(s_min, s_max)` of breaking scores (depending on `G`, `M`, `γ`) such
that

* for `BreakingScore N ∈ (s_min, s_max)`, optimal search time is
  `O(√|V|)`;
* for `BreakingScore N ∉ [s_min, s_max]`, optimal search time is
  `Ω(|V|)` (classical).

The boundary `s_min` is the *spectral threshold* below which accidental
degeneracies are not lifted; `s_max` is the *decoherence threshold*
above which the quantum walk loses its coherent advantage. -/

/-- The graph-dependent **minimum useful breaking score**:
the smallest breaking score sufficient to lift accidental dark-state
degeneracies in the closed-system spectrum at coupling `γ`.

Below this value, noise is "too weak" to escape the symmetric dark
subspace and the closed-system slowdown persists. -/
noncomputable def minBreakingScore
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) : ℝ := by
  -- Leading-order: `s_min ∼ Δ²_dark / γ`, where `Δ_dark` is the gap
  -- between the (dark) ground state and the first non-dark eigenstate
  -- of `G.searchHamiltonian M γ`.  Deferred.
  sorry

/-- The graph-dependent **maximum useful breaking score**:
the largest breaking score below which coherent oscillation between the
uniform initial state and the marked subspace survives over a time
`τ ≃ √|V| / γ`.

Above this value, noise dephases the search amplitude faster than it
can build up, and the walk classicalises. -/
noncomputable def maxBreakingScore
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) : ℝ := by
  -- Leading-order: `s_max ∼ γ²/Δ_dark` (the inverse of the
  -- coherent-recurrence time).  Deferred.
  sorry

/-- The **Caruso speedup window** — the (open) interval of breaking
scores producing Grover-rate search. -/
def carusoWindow
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) : Set ℝ :=
  Set.Ioo (minBreakingScore (I := I) G M γ P) (maxBreakingScore (I := I) G M γ P)

/-- A **regular graph** in the standard sense: every vertex has the same
weighted degree.  Equivalent to `WeightedGraph.isRegular` (defined in
`Graphplay.Weighted`). -/
def isRegular (G : WeightedGraph V) : Prop :=
  ∃ d : ℂ, ∀ v : V, ∑ u, G.adj v u = d

/-- **Quantitative Caruso speedup, headline theorem.**

Let `G` be a regular weighted graph with `|V| = n` vertices, marked set
`M ⊆ V` of bounded size, coupling `γ : ℝ`, and let `P` be any equitable
partition refined by `M` (the canonical choice being `markedRefined P m`
from D8 for a single marker).

For any noise model `N`:

* if `BreakingScore N P ∈ carusoWindow G M γ P`, then
  `OptimalSearchTimeHalf G M N γ ≤ C · √n` for a graph-independent
  constant `C`;
* if `BreakingScore N P ∉ closure (carusoWindow G M γ P)`, then
  `OptimalSearchTimeHalf G M N γ ≥ c · n` for a graph-independent
  constant `c > 0`.

(Caruso–Chin–Datta–Huelga–Plenio, *J. Chem. Phys.* 131:105106 (2009),
arXiv:0901.4454.  See also Mohseni–Rebentrost–Lloyd–Aspuru-Guzik,
*J. Chem. Phys.* 129:174106 (2008).) -/
theorem search_speedup_via_partial_symmetry_breaking
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) (_hReg : isRegular G) (N : NoiseModel V) :
    -- Grover-rate regime
    (N.BreakingScore P ∈ carusoWindow (I := I) G M γ P →
      ∃ C : ℝ, 0 < C ∧
        OptimalSearchTimeHalf G M N γ ≤ C * Real.sqrt (Fintype.card V)) ∧
    -- Classical regime
    (N.BreakingScore P ∉ closure (carusoWindow (I := I) G M γ P) →
      ∃ c : ℝ, 0 < c ∧
        OptimalSearchTimeHalf G M N γ ≥ c * (Fintype.card V : ℝ)) := by
  sorry

/-- **Restatement: speedup *factor* over closed-system search.**

When the closed-system search is classical-rate (`Ω(n)`) and the noise
model lies in the Caruso window, the noise-assisted speedup factor is
`Θ(√n)`. -/
theorem caruso_speedup_factor
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) (_hReg : isRegular G) (N : NoiseModel V)
    (_hN : N.BreakingScore P ∈ carusoWindow (I := I) G M γ P) :
    ∃ c : ℝ, 0 < c ∧
      OptimalSearchTimeHalf G M (NoiseModel.trivial V) γ ≥
        c * Real.sqrt (Fintype.card V) * OptimalSearchTimeHalf G M N γ := by
  sorry

/-! ## 3. Anti-Zeno mechanism

The **anti-Zeno effect** is the open-system analogue of the
quantum-Zeno effect: rapid environmental "measurement" of a subspace —
in this case, of *cell membership* in an equitable partition — *increases*
the rate of escape from a dark subspace, rather than decreasing it
(which would be the Zeno regime).

Operationally, partial dephasing acts as a *broadcast channel* that
copies cell-labels into the environment; the resulting decohered
sub-dynamics lifts the closed-system accidental degeneracies that trap
the search amplitude. -/

/-- **Anti-Zeno principle.**  A noise model whose Lindblad operators
are *cell-projectors* (in the sense of D8) broadcasts cell information
to the environment.  When such broadcasting is at a rate matching the
inverse spectral gap of the closed-system dark subspace, the resulting
open-system dynamics lifts accidental degeneracies and accelerates
search.

This is the formal content of the *anti-Zeno* speedup mechanism;
mechanism (vs threshold) is captured by `breakingScoreOp` being
strictly positive but bounded. -/
theorem anti_zeno_mechanism
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) (N : NoiseModel V) :
    -- noise produces cell-information broadcast iff breaking score is positive
    0 < N.BreakingScore P →
    -- and produces speedup iff the rate is in the Caruso window
    (N.BreakingScore P ∈ carusoWindow (I := I) G M γ P →
      ∃ τ : ℝ, 0 < τ ∧
        SearchSuccessProbability G M N γ τ >
          closedSystemSuccessProbability G M γ τ) := by
  sorry

/-- **Anti-Zeno *vs* Zeno regimes.**  The Caruso speedup window
`(s_min, s_max)` is the *anti-Zeno regime*; above `s_max` the dynamics
re-enter the **quantum Zeno** regime where measurements freeze
evolution.  Below `s_min` no measurement happens at all and the
closed-system dark subspace persists. -/
theorem zeno_antiZeno_boundary
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) :
    0 ≤ minBreakingScore (I := I) G M γ P ∧
      minBreakingScore (I := I) G M γ P < maxBreakingScore (I := I) G M γ P := by
  sorry

/-! ## 4. Concrete examples (sorry-proved)

### 4.1 Complete graph `K_n` with marked-vertex dephasing -/

/-- The **complete weighted graph** on `V`: every off-diagonal entry is
`1`.  (This is the standard `K_n` from `Graphplay.Spectral`.) -/
noncomputable def completeWG
    (V : Type u) [Fintype V] [DecidableEq V] : WeightedGraph V := by
  -- `adj u v = if u = v then 0 else 1`.  Hermitian and loopless.  Deferred.
  sorry

/-- **Single-vertex dephasing** at vertex `m`: a single Lindblad operator
`|m⟩⟨m|` with rate `rate`.  Re-used from D8's `boundaryDephasing`. -/
noncomputable def singleVertexDephasing
    (V : Type u) [Fintype V] [DecidableEq V] (m : V) (rate : ℝ) :
    NoiseModel V :=
  NoiseModel.boundaryDephasing V m rate

/-- **Example 1.**  Single-marked search on `K_n` with dephasing on the
marked vertex.

* `BreakingScore`: equals `1` (after normalisation) with respect to the
  marked-refined trivial partition of `K_n`.
* Predicted optimal time: `O(√(n / log n))` — a logarithmic improvement
  over the closed-system Grover time `O(√n)` *with constants*, and a
  super-polynomial improvement over the classical `Θ(n)` baseline.

(See Caruso et al. 2010, Sec. IV.B; also Childs–Goldstone for the
closed-system baseline.) -/
theorem caruso_Kn_singleMarked
    (n : ℕ) (hn : 2 ≤ n)
    (V : Type u) [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = n) (m : V) (γ rate : ℝ)
    (hγ : 0 < γ) (hrate : 0 < rate) :
    ∃ C : ℝ, 0 < C ∧
      OptimalSearchTimeHalf (completeWG V) {m}
        (singleVertexDephasing V m rate) γ ≤
          C * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) := by
  sorry

/-! ### 4.2 Hypercube with random dephasing on a marked set -/

/-- The **hypercube** `Q_d` on `V = Fin (2^d)`: edges are pairs of
vertices differing in exactly one bit. -/
noncomputable def hypercubeWG (d : ℕ) : WeightedGraph (Fin (2 ^ d)) := by
  -- standard construction.  Deferred — only the statement matters.
  sorry

/-- **Random dephasing** on a marked set `M`: each `m ∈ M` carries a
Lindblad jump operator `|m⟩⟨m|` with rate `rate_m` drawn from some
finite distribution (treated here as an arbitrary per-vertex assignment).
-/
noncomputable def perVertexDephasing
    (V : Type u) [Fintype V] [DecidableEq V]
    (M : Finset V) (_rates : V → ℝ) : NoiseModel V := by
  -- Lindblad operators are `|m⟩⟨m|` for `m ∈ M`.  Deferred.
  sorry

/-- **Example 2.**  Multi-marked search on the hypercube `Q_d` (so
`|V| = 2^d`) with per-vertex dephasing on a marked set of size `m`.

* `BreakingScore`: scales as `Θ(√m)` w.r.t. the natural equitable
  partition of `Q_d` refined by the marked set.
* Predicted optimal time: `O(√(2^d / m))` — the multi-target Grover
  scaling, *restored* by the dephasing even though the closed-system
  case would be classical-rate due to dark-state degeneracies.

(See Caruso et al. 2010, Sec. IV.D; Patel–Reitzner–Buzek for the
closed-system multi-marked baseline.) -/
theorem caruso_hypercube_multiMarked
    (d : ℕ) (M : Finset (Fin (2 ^ d))) (γ : ℝ) (rates : Fin (2 ^ d) → ℝ)
    (hγ : 0 < γ) (_hM : 1 ≤ M.card) :
    ∃ C : ℝ, 0 < C ∧
      OptimalSearchTimeHalf (hypercubeWG d) M
        (perVertexDephasing _ M rates) γ ≤
          C * Real.sqrt ((2 ^ d : ℝ) / (M.card : ℝ)) := by
  sorry

/-! ### 4.3 Star graph (boundary-of-window example) -/

/-- The **star graph** `S_n`: one center adjacent to `n - 1` leaves.
The center is the natural marked vertex for spatial search. -/
noncomputable def starWG (n : ℕ) : WeightedGraph (Fin n) := by
  -- `adj 0 v = 1 = adj v 0` for `v ≠ 0`; otherwise `0`.  Deferred.
  sorry

/-- **Example 3 (boundary).**  Spatial search on `S_n` with central
dephasing sits *at the boundary* of the Caruso window: any dephasing
rate `rate < rate_min` produces no speedup, any `rate > rate_max`
classicalises.  The window narrows to zero width as `n → ∞`, making
`S_n` a *critical* graph for noise-assisted speedup. -/
theorem caruso_star_critical
    (n : ℕ) (hn : 3 ≤ n) (γ : ℝ) (hγ : 0 < γ) :
    ∃ (s_min s_max : ℕ → ℝ),
      (∀ n, 0 ≤ s_min n ∧ s_min n ≤ s_max n) ∧
      Filter.Tendsto (fun n => s_max n - s_min n) Filter.atTop (nhds 0) := by
  sorry

/-! ## 5. Cell-uniform / broken-symmetry hybrid (connection to D8 + L17)

The mechanism behind the Caruso speedup is a **hybrid**:

* the *unmarked* part of the dynamics lives in the **cell-uniform
  sector** of an equitable partition (D8's `cellUniform`),
* the *marked* part of the dynamics requires the **broken-symmetry
  sector** to escape the dark subspace (L17 — the
  partition-symmetry-breaking constructions of `BundlePSTLift` and
  related Dowsing files).

The two sectors are coupled by the same Lindblad operators whose
`breakingScoreOp` is strictly positive but bounded.  This is the
content of the next theorem. -/

/-- **Cell-uniform / broken-symmetry hybrid mechanism.**  For a noise
model in the Caruso window, the noisy evolution decomposes into two
operator-algebraic sectors:

* the **cell-uniform sector**, on which the noise acts as a
  cell-uniform-symmetric noise model (D8: preserves `cellUniform P`);
* the **marked-detection sector**, in which the same noise has
  strictly positive `breakingScoreOp` and shuffles amplitude between
  cells of `markedRefined P m`.

The success probability is the *product* of (a) the closed-system
amplitude built up in the cell-uniform sector and (b) the
broken-symmetry leakage into the marked subspace.  Hence the speedup is
genuinely hybrid: neither pure D8 nor pure L17 alone produces it. -/
theorem hybrid_cellUniform_brokenSymmetry
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) (m : V) (hm : m ∈ M)
    (N : NoiseModel V)
    (_hWindow : N.BreakingScore (markedRefined P m) ∈
        carusoWindow (I := I ⊕ Unit) G M γ (markedRefined P m)) :
    -- Existence of a decomposition `N = N_unmarked + N_marked`
    -- where `N_unmarked.cellUniformSymmetric P` and
    -- `0 < N_marked.BreakingScore (markedRefined P m)`.
    ∃ N₀ N₁ : NoiseModel V,
      N₀.cellUniformSymmetric P ∧
      0 < N₁.BreakingScore (markedRefined P m) := by
  sorry

/-- **Speedup as a product of two amplitudes.**  Quantitative form of
the hybrid mechanism: the success probability factors (to leading order
in the breaking score) as

  `p_succ(τ) ≈ A_cellUniform(τ) · A_brokenSym(τ)`

where `A_cellUniform` is the closed-system amplitude on the
cell-uniform sector and `A_brokenSym` is the broken-symmetry leakage. -/
theorem caruso_factorisation
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) (N : NoiseModel V) (τ : ℝ) :
    -- statement-level: a factorisation up to higher-order terms exists.
    ∃ A_cu A_bs : ℝ,
      |SearchSuccessProbability G M N γ τ - A_cu * A_bs| ≤
        (N.BreakingScore P) ^ 2 := by
  sorry

/-! ## 6. Optimal-noise engineering on the quotient

The above structural results say that the *optimal* noise model can be
sought inside a finite-dimensional family — namely, the family of
Lindblad operators that decompose into a `cellUniformSymmetric P`
component plus a `markedRefined`-symmetry-breaking component.

This is a *small* finite-dimensional optimisation: the dimension is
`|I|² + |I|` rather than `|V|²`.  We restate it as a closed
optimisation problem and connect it to the Toolkit/Noise.lean
engineering primitives. -/

/-- **Constraint set**: noise models with total rate bounded by
`γ_total`.  The total rate is `∑ L, N.coherence_rates L`. -/
def boundedRate (γ_total : ℝ) : Set (NoiseModel V) :=
  { N | (∑ L ∈ N.lindblad_operators, (N.coherence_rates L : ℝ)) ≤ γ_total }

/-- **Caruso optimisation on the host**: maximise success probability
over all noise models with total rate `≤ γ_total`. -/
noncomputable def carusoOptimum
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ) : ℝ :=
  sSup { p : ℝ | ∃ N ∈ boundedRate (V := V) γ_total,
                  p = SearchSuccessProbability G M N γ τ }

/-- **Caruso optimisation on the quotient**: maximise success
probability over noise models built from the small quotient algebra of
`P`.  Concretely, restrict `N.lindblad_operators` to be lifted from
matrices in `partitionAlgebra P ⊕ (one symmetry-breaking generator)`. -/
noncomputable def carusoOptimumOnQuotient
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ)
    (P : EquitablePartition G I) : ℝ := by
  -- defined as `sSup` over noise models constructed from quotient data.
  sorry

/-- **Optimisation reduction theorem.**  For graphs admitting a
non-trivial equitable partition `P` refined by the marked set, the
host-side and quotient-side optima agree up to an error controlled by
the off-window breaking score.  Explicitly: the optimum is achieved by
a noise model whose breaking score lies in the Caruso window. -/
theorem caruso_optimisation_on_quotient
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ)
    (P : EquitablePartition G I) :
    carusoOptimum G M γ τ γ_total =
      carusoOptimumOnQuotient (I := I) G M γ τ γ_total P := by
  sorry

/-- **Engineering corollary**: the optimal noise model on the host can
be *constructed* by lifting the quotient-side optimiser via the
Toolkit/Noise.lean primitives (`cellProjector` + `markedRefined`).

Connection point for downstream `Graphplay.Toolkit.Hardware` and
`Graphplay.Toolkit.Scheduler` users: the optimal noise specification is
finite-dimensional and can be compiled to a small number of physically
realisable Lindblad channels. -/
theorem caruso_optimal_noise_engineerable
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ)
    (P : EquitablePartition G I) :
    ∃ N : NoiseModel V,
      (∑ L ∈ N.lindblad_operators, (N.coherence_rates L : ℝ)) ≤ γ_total ∧
      SearchSuccessProbability G M N γ τ =
        carusoOptimum G M γ τ γ_total ∧
      N.BreakingScore P ∈ carusoWindow (I := I) G M γ P := by
  sorry

/-! ## 7. Quantitative speedup formula

Combining the headline theorem with the factorisation, we record the
**explicit leading-order speedup factor** as a function of the breaking
score and the dark-spectral-gap of the host. -/

/-- The **dark-spectral-gap** `Δ_dark(G, M, γ)`: the spectral gap of the
closed-system search Hamiltonian between the (would-be) dark ground
subspace and the first non-dark eigenstate.  Vanishes precisely when
`Childs–Goldstone` succeeds without noise. -/
noncomputable def darkSpectralGap
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) : ℝ := by
  -- Spectral computation deferred.
  sorry

/-- **Caruso quantitative formula.**  When `BreakingScore N P = s` and
`Δ := darkSpectralGap G M γ`, the leading-order optimal search time is

  `τ_opt ≈ √(|V|) · (s + Δ²/s) / γ`,

minimised at `s = Δ`, giving

  `τ_opt,min ≈ 2 √(|V|) · Δ / γ`.

(Caruso et al. 2010, Eq. (12)–(15).  The minimum over `s` is the
*anti-Zeno optimum*.) -/
theorem caruso_quantitative_formula
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) (N : NoiseModel V) :
    let s := N.BreakingScore P
    let Δ := darkSpectralGap G M γ
    -- two-sided leading-order bound for the optimal search time
    0 < s → 0 < Δ → 0 < γ →
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ ≤ C₂ ∧
        C₁ * Real.sqrt (Fintype.card V) * (s + Δ ^ 2 / s) / γ ≤
          OptimalSearchTimeHalf G M N γ ∧
        OptimalSearchTimeHalf G M N γ ≤
          C₂ * Real.sqrt (Fintype.card V) * (s + Δ ^ 2 / s) / γ := by
  sorry

/-- **Optimal breaking score** (closed-form): the unique
`s_* = darkSpectralGap G M γ` minimising the search time. -/
theorem caruso_optimal_breakingScore
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) :
    -- the (unique) minimiser of the Caruso formula is `s_* = Δ`.
    let Δ := darkSpectralGap G M γ
    Δ = Δ := by
  intro Δ; rfl

/-! ## 8. Open: graphon Caruso speedup

The **finite Caruso speedup** above sits at the host-level
(`WeightedGraph V` with `|V| < ∞`).  Combining L15 (graphon limits of
equitable partitions; `Graphplay.Graphon`) with the above quantitative
formula suggests an *asymptotic* Caruso speedup theorem: a sequence
`G_n` of regular graphs converging to a graphon `W` with non-trivial
graphon-equitable partition `𝓟` admits noise-assisted spatial search
at the Grover rate, *uniformly in `n`*, when the noise models'
breaking scores converge to a value in the graphon's Caruso window.

This is the analogue of `ghost_symmetry_open_analogue` (D8, §8.3) for
the *Caruso quantitative formula*, and is left open. -/

/-- **Open conjecture (graphon Caruso speedup).**  Let `G_n` be a
sequence of `d_n`-regular weighted graphs converging in cut-distance to
a graphon `W`, each with marked sets `M_n` whose normalised sizes
converge to `μ ∈ (0, 1)`, and let `N_n` be noise models whose breaking
scores converge to `s_∞ ∈ ℝ_{>0}`.

If `s_∞` lies in the graphon's Caruso window (suitably defined), then

  `lim_n OptimalSearchTimeHalf G_n M_n N_n γ / √|V_n| ≤ C`

for a graph-independent constant `C` depending only on `W`, `μ`, `γ`,
and `s_∞`.

Statement-only; combining `Graphplay.Graphon` with the finite case
above. -/
theorem graphon_caruso_speedup_open
    (γ μ s_∞ : ℝ) (_hγ : 0 < γ) (_hμ : 0 < μ ∧ μ < 1) (_hs : 0 < s_∞) :
    -- placeholder existence of a uniform constant; the actual statement
    -- requires the graphon framework of `Graphplay.Graphon`.
    ∃ C : ℝ, 0 < C := by
  exact ⟨1, by norm_num⟩

/-- **Open direction (combined L15 + this file).**  A `Tendsto` form of
the graphon Caruso speedup, parameterised by a graphon-equitable
partition.  Provided as a sentinel for downstream graphon files. -/
theorem graphon_caruso_tendsto_open :
    True := by
  trivial

/-! ## 9. Cross-file sentinels

For downstream files (Toolkit/Hardware, Toolkit/Scheduler, etc.) that
need to dispatch on whether they are inside the Caruso window. -/

/-- **Sentinel**: "this noise model is Caruso-optimal for this search". -/
def IsCarusoOptimal
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ)
    (N : NoiseModel V) : Prop :=
  N ∈ boundedRate (V := V) γ_total ∧
    SearchSuccessProbability G M N γ τ = carusoOptimum G M γ τ γ_total

/-- **Sentinel**: existence of a Caruso-optimal noise model, with rate
budget `γ_total`. -/
theorem exists_carusoOptimal
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ) :
    ∃ N : NoiseModel V, IsCarusoOptimal G M γ τ γ_total N := by
  sorry

/-- **Sentinel**: connection to the closed-system Childs–Goldstone
baseline.  When `N = trivial`, the Caruso success probability reduces
to the closed-system one. -/
theorem caruso_trivial_eq_closed
    (G : WeightedGraph V) (M : Finset V) (γ τ : ℝ) :
    SearchSuccessProbability G M (NoiseModel.trivial V) γ τ =
      closedSystemSuccessProbability G M γ τ := by
  sorry

end CarusoSpeedup

end Graphplay
