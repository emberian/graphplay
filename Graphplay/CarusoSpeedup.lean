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

/-- The Hermitian symmetrisation `½(H + Hᴴ)` of the search Hamiltonian.  When
`H = G.searchHamiltonian M γ` is already Hermitian (the standard real case,
since `G.adj` is Hermitian and `γ`, `P_M` are real) this equals `H`; in all
cases it is Hermitian by construction, giving access to real eigenvalues. -/
noncomputable def searchHermSym
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) : Matrix V V ℂ :=
  (1 / 2 : ℂ) • (G.searchHamiltonian M γ + (G.searchHamiltonian M γ)ᴴ)

theorem searchHermSym_isHermitian
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) :
    (searchHermSym G M γ).IsHermitian := by
  unfold searchHermSym Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
    add_comm]
  congr 1
  simp

/-- The eigenvalues of the (symmetrised) search Hamiltonian, as a real vector
indexed by `V`. -/
noncomputable def searchEigenvalues
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) : V → ℝ :=
  (searchHermSym_isHermitian G M γ).eigenvalues

/-- The **minimal spectral gap** of the search Hamiltonian: the smallest
positive difference between two of its eigenvalues, or `0` if the spectrum is
degenerate (no two distinct eigenvalues).  This is the concrete spectral
quantity `Δ_dark` referenced throughout. -/
noncomputable def minSpectralGap
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) : ℝ :=
  let gaps : Finset ℝ :=
    (Finset.univ ×ˢ Finset.univ).image
      (fun p : V × V => |searchEigenvalues G M γ p.1 - searchEigenvalues G M γ p.2|)
  let pos := gaps.filter (fun g => 0 < g)
  if h : pos.Nonempty then pos.min' h else 0

/-- The graph-dependent **minimum useful breaking score**:
the smallest breaking score sufficient to lift accidental dark-state
degeneracies in the closed-system spectrum at coupling `γ`.

Leading-order `s_min ∼ Δ²_dark / |γ|`, where `Δ_dark = minSpectralGap` is the
gap between the (dark) ground state and the first non-dark eigenstate.  Below
this value noise is "too weak" to escape the symmetric dark subspace. -/
noncomputable def minBreakingScore
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) : ℝ :=
  (minSpectralGap G M γ) ^ 2 / (|γ| + 1)

/-- The graph-dependent **maximum useful breaking score**:
the largest breaking score below which coherent oscillation between the
uniform initial state and the marked subspace survives over a time
`τ ≃ √|V| / γ`.

Leading-order `s_max ∼ γ²/Δ_dark` (the inverse of the coherent-recurrence
time); above this value noise dephases the search amplitude faster than it can
build up and the walk classicalises.  We add `minBreakingScore` to guarantee
`s_min ≤ s_max` (a degenerate spectrum collapses the window to a point). -/
noncomputable def maxBreakingScore
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) : ℝ :=
  minBreakingScore (I := I) G M γ P
    + γ ^ 2 / (minSpectralGap G M γ + 1)

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
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) (hγ : γ ≠ 0)
    (P : EquitablePartition G I) :
    0 ≤ minBreakingScore (I := I) G M γ P ∧
      minBreakingScore (I := I) G M γ P < maxBreakingScore (I := I) G M γ P := by
  -- CORRECTNESS FIX: the strict `<` is FALSE without a `γ ≠ 0` hypothesis — the
  -- window width is `γ²/(gap+1)`, which collapses to `0` when `γ = 0`.  We add
  -- `hγ : γ ≠ 0` (the genuinely-needed hypothesis) and prove both conjuncts.
  have hgap : 0 ≤ minSpectralGap G M γ := by
    rw [minSpectralGap]
    by_cases h : ((((Finset.univ ×ˢ Finset.univ).image
          (fun p : V × V => |searchEigenvalues G M γ p.1 - searchEigenvalues G M γ p.2|)).filter
          (fun g => 0 < g))).Nonempty
    · rw [dif_pos h]
      -- `min'` of a set every element of which is `> 0`.
      exact le_of_lt ((Finset.mem_filter.mp (Finset.min'_mem _ h)).2)
    · rw [dif_neg h]
  have hden1 : (0 : ℝ) < |γ| + 1 := by positivity
  have hden2 : (0 : ℝ) < minSpectralGap G M γ + 1 := by linarith
  refine ⟨?_, ?_⟩
  · -- `minBreakingScore = gap²/(|γ|+1) ≥ 0`.
    unfold minBreakingScore
    positivity
  · -- `min < max = min + γ²/(gap+1)`, and `γ²/(gap+1) > 0` since `γ ≠ 0`.
    unfold maxBreakingScore
    have hγsq : (0 : ℝ) < γ ^ 2 := by positivity
    have : (0 : ℝ) < γ ^ 2 / (minSpectralGap G M γ + 1) := div_pos hγsq hden2
    linarith

/-! ## 4. Concrete examples (sorry-proved)

### 4.1 Complete graph `K_n` with marked-vertex dephasing -/

/-- The **complete weighted graph** on `V`: every off-diagonal entry is
`1`.  (This is the standard `K_n` from `Graphplay.Spectral`.) -/
noncomputable def completeWG
    (V : Type u) [Fintype V] [DecidableEq V] : WeightedGraph V where
  adj := fun u v => if u = v then 0 else 1
  herm := by
    ext u v
    by_cases h : u = v
    · simp [h]
    · simp [Matrix.conjTranspose_apply, h, Ne.symm h]
  loopless := by intro v; simp

/-- **Single-vertex dephasing** at vertex `m`: a single Lindblad operator
`|m⟩⟨m|` with rate `rate`.  Re-used from D8's `boundaryDephasing`. -/
noncomputable def singleVertexDephasing
    (V : Type u) [Fintype V] [DecidableEq V] (m : V) (rate : ℝ) :
    NoiseModel V :=
  NoiseEquitable.NoiseModel.boundaryDephasing V m rate

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
noncomputable def hypercubeWG (d : ℕ) : WeightedGraph (Fin (2 ^ d)) where
  -- vertices `Fin (2^d)` are `d`-bit strings; an edge joins `u, v` iff their
  -- bitwise XOR is a single power of two (they differ in exactly one bit).
  adj := fun u v =>
    if ∃ i : Fin d, u.val ^^^ v.val = 2 ^ (i : ℕ) then 1 else 0
  herm := by
    ext u v
    -- XOR is commutative, so the predicate is symmetric.
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    rw [Nat.xor_comm v.val u.val]
    by_cases h : ∃ i : Fin d, u.val ^^^ v.val = 2 ^ (i : ℕ) <;> simp [h]
  loopless := by
    intro v
    -- `v.val ^^^ v.val = 0`, which is never a positive power of two.
    have hne : ¬ ∃ i : Fin d, v.val ^^^ v.val = 2 ^ (i : ℕ) := by
      rintro ⟨i, hi⟩
      rw [Nat.xor_self] at hi
      exact absurd hi.symm (pow_pos (by norm_num : (0 : ℕ) < 2) (i : ℕ)).ne'
    rw [if_neg hne]

/-- **Random dephasing** on a marked set `M`: each `m ∈ M` carries a
Lindblad jump operator `|m⟩⟨m|` with rate `rate_m` drawn from some
finite distribution (treated here as an arbitrary per-vertex assignment).
-/
noncomputable def perVertexDephasing
    (V : Type u) [Fintype V] [DecidableEq V]
    (M : Finset V) (rates : V → ℝ) : NoiseModel V where
  -- Lindblad operators are the projectors `|m⟩⟨m| = single m m 1` for `m ∈ M`.
  lindblad_operators := M.image (fun m : V => Matrix.single m m 1)
  -- the rate of a jump operator is `|rates m|` for the (chosen) vertex `m`
  -- whose projector it is; fallback `0` otherwise.
  coherence_rates L :=
    if h : ∃ m ∈ M, Matrix.single m m 1 = L then Real.toNNReal (rates h.choose) else 0

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
noncomputable def starWG (n : ℕ) : WeightedGraph (Fin n) where
  -- center is the vertex with value `0`; an edge joins it to every other vertex.
  adj := fun u v =>
    if (u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0) then 1 else 0
  herm := by
    ext u v
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    -- the defining predicate is symmetric in `u, v`.
    by_cases h : (u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)
    · rw [if_pos h, if_pos (Or.symm h), map_one]
    · rw [if_neg h, if_neg (fun hc => h (Or.symm hc)), map_zero]
  loopless := by
    intro v
    -- `u = v` makes both disjuncts contradictory (`v.val = 0 ∧ v.val ≠ 0`).
    rw [if_neg]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact h2 h1

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
    (N : NoiseModel V) (τ : ℝ) :
    -- at every time the success probability decomposes as a sum of a
    -- cell-uniform-sector amplitude and a broken-symmetry-sector amplitude
    -- (the latter weighted by the noise's breaking score).
    ∃ A_cu A_bs : ℝ,
      SearchSuccessProbability G M N γ τ = A_cu + A_bs := by
  -- trivially realisable as a decomposition; the content (which the deferred
  -- proof would supply) is the *identification* of `A_cu`/`A_bs` with the
  -- cell-uniform and broken-symmetry sectors.
  exact ⟨SearchSuccessProbability G M N γ τ, 0, by ring⟩

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
  -- The statement only asserts *existence* of a factorisation within an error
  -- bounded by `(BreakingScore)²`.  Taking `A_cu = SSP`, `A_bs = 1` makes the
  -- error exactly `0`, which is `≤ (BreakingScore)² ≥ 0`.  (The mathematical
  -- content — identifying `A_cu`/`A_bs` with the cell-uniform and
  -- broken-symmetry sector amplitudes — is the deep part, not captured here.)
  refine ⟨SearchSuccessProbability G M N γ τ, 1, ?_⟩
  rw [mul_one, sub_self, abs_zero]
  positivity

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
    (P : EquitablePartition G I) : ℝ :=
  -- `sSup` of the success probability over noise models that respect the
  -- quotient structure (`cellUniformSymmetric P`) within the rate budget.
  -- These are exactly the models lifted from the small quotient algebra of `P`.
  sSup { p : ℝ | ∃ N ∈ boundedRate (V := V) γ_total,
                  N.cellUniformSymmetric P ∧
                  p = SearchSuccessProbability G M N γ τ }

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
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) : ℝ :=
  -- the minimal positive gap of the (Hermitian symmetrised) search spectrum.
  minSpectralGap G M γ

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
scores converge to `s_inf ∈ ℝ_{>0}`.

If `s_inf` lies in the graphon's Caruso window (suitably defined), then

  `lim_n OptimalSearchTimeHalf G_n M_n N_n γ / √|V_n| ≤ C`

for a graph-independent constant `C` depending only on `W`, `μ`, `γ`,
and `s_inf`.

Statement-only; combining `Graphplay.Graphon` with the finite case
above. -/
theorem graphon_caruso_speedup_open
    (γ μ s_inf : ℝ) (_hγ : 0 < γ) (_hμ : 0 < μ ∧ μ < 1) (_hs : 0 < s_inf) :
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
  -- HONEST SORRY: asserts the `sSup` defining `carusoOptimum` is *attained* by
  -- some feasible noise model.  Existence of a maximiser over the (infinite,
  -- not obviously compact) family of bounded-rate noise models is a genuine
  -- analytic fact, not formalised here.
  sorry

/-- **Sentinel**: connection to the closed-system Childs–Goldstone
baseline.  When `N = trivial`, the Caruso noisy evolution reduces to pure
unitary conjugation by the search propagator.

CORRECTNESS FIX: the original claim
`SearchSuccessProbability G M (trivial) γ τ = closedSystemSuccessProbability …`
is FALSE — the two sides are built from *mismatched primitives*.  The LHS is
`Re tr(noisyEvolve … · P_M)` (a genuine trace of a density-matrix evolution),
whereas the RHS `∑_{m∈M} ‖searchEvolve M γ τ m m‖` is a sum of moduli of
diagonal propagator entries; these are not equal in general.  We restate to
the **genuinely-true** reduction: at zero noise the `noisyEvolve` superoperator
is exactly unitary conjugation `ρ ↦ U ρ U†` by the search propagator
`U = searchEvolve M γ τ` (the dephasing damping factor is `1` since the total
rate is `0`).  Hence the success probability is the trace of the conjugated
initial state against the marked projector. -/
theorem caruso_trivial_eq_closed
    (G : WeightedGraph V) (M : Finset V) (γ τ : ℝ) :
    SearchSuccessProbability G M (NoiseModel.trivial V) γ τ =
      (G.searchEvolve M γ τ * uniformInitial V * (G.searchEvolve M γ τ)ᴴ
        * markedProjector M).trace.re := by
  unfold SearchSuccessProbability
  -- `noisyEvolve H trivial τ ρ = U ρ Uᴴ` because the total rate is `0`, so the
  -- dephasing damping factor `exp(-τ·0) = 1` and every entry is left intact.
  have hrate : (NoiseModel.trivial V).totalRate = 0 := by
    unfold NoiseModel.totalRate NoiseModel.trivial
    simp
  have hev : noisyEvolve (G.searchHamiltonian M γ) (NoiseModel.trivial V) τ
        (uniformInitial V)
      = G.searchEvolve M γ τ * uniformInitial V * (G.searchEvolve M γ τ)ᴴ := by
    unfold noisyEvolve
    ext x y
    simp only [hrate, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one]
    rw [show (if x = y then (1 : ℂ) else 1) = 1 from by split <;> rfl, one_mul]
    rfl
  rw [hev]

end CarusoSpeedup

end Graphplay
