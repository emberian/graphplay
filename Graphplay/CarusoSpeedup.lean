/-
# Graphplay.CarusoSpeedup

**Round-3 loop-closer: Quantitative Caruso noise-assisted speedup.**

────────────────────────────────────────────────────────────────────────
⚠ **TOY-MODEL DISCLAIMER (read before citing anything in this file).**

This file is a **scalar-dephasing toy model**, *not* a formalisation of the
Caruso–Chin–Datta–Huelga–Plenio (CDHHP) open-system result.  Specifically:

* **The evolution `noisyEvolve` (imported from `Graphplay/Toolkit/Noise.lean`) is
  NOT a Lindblad generator.**  It is the *unitary conjugation `ρ ↦ U ρ U†`
  followed by a single scalar off-diagonal damping factor `exp(-t·γ_total)`* — a
  uniform-dephasing-in-the-vertex-basis channel.  The genuine CDHHP dynamics is a
  GKLS/Lindblad master equation with per-site jump operators; that semigroup is
  **not** what runs here.  Consequences proved here (e.g. that the success
  probability is a Born probability in `[0,1]`) are facts about *this toy
  channel*.

* **The breaking-score thresholds `toyMinBreakingScore`, `toyMaxBreakingScore`
  and the interval `toyCarusoWindow` are INVENTED scalar surrogates**, not CDHHP
  quantities.  Their formulas (`gap²/(|γ|+1)`, `+ γ²/(gap+1)`) are placeholder
  closed forms chosen only to be non-negative with a non-degenerate window; they
  carry *no* claim to reproduce the CDHHP optimal-dephasing rate.  (The input
  `NoiseModel.BreakingScore P` from D8 — the rate-weighted L² distance to the
  partition commutant — is a real definition; only the *threshold formulas*
  built from it here are toy.)

* **The headline scaling theorems are conditional theorems,
  each derived from a named, cited, no-instance `Prop`-valued interface
  (`CarusoSpeedupDichotomy`, `CarusoAntiZeno`, `CarusoKnScaling`,
  `CarusoHypercubeScaling`, `CarusoQuantitativeFormula`, `CarusoOptimumAttained`),
  with the constants hoisted to graph-independent universals** (so they are not
  trivially closeable per-instance).  They claim the *√n vs n* dichotomy as a
  cited CDHHP/Childs–Goldstone target, conditioned on this toy window — they do
  **not** assert it is derived from a Lindblad analysis, and **no instance** of
  any interface is provided.

In short: the inequalities are real and the probabilities are genuine, but the
*physics names* (`Caruso`, `breaking score window`, `anti-Zeno`) sit on a
scalar-dephasing surrogate that obeys a √n-type bound, **not** on the CDHHP
open-system master equation.  Do not cite this file as a proof of the
Caruso–Chin–Datta–Huelga–Plenio theorem.
────────────────────────────────────────────────────────────────────────

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
  ⚠ NOTE: this 2010 paper is about *entanglement / entangling power*, **not**
  search-time scaling.  It does **not** contain the `√n·(s+Δ²/s)/γ` formula used in
  this file — that shape is the file's own ansatz (see
  `CarusoQuantitativeFormula`).  Do not cite "Caruso 2010 Eq. (12)–(15)" as the
  source of any time-scaling result here.
* Mohseni–Rebentrost–Lloyd–Aspuru-Guzik,
  *Environment-assisted quantum walks in photosynthetic energy transfer*,
  J. Chem. Phys. 129, 174106 (2008).
* Childs–Goldstone (2004), *Spatial search by quantum walk*,
  Phys. Rev. A 70, 022314 (closed-system baseline).

The analytic hygiene (Born-probability bounds, Hermiticity, the `sSup`/`sInf`
monotonicity and ε-approximation results) is proven outright; the external
CDHHP/Childs–Goldstone scaling claims are conditional theorems off the named
interfaces above.
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Search
import Graphplay.Toolkit.Noise
import Graphplay.Dowsing.NoiseEquitable

open scoped Matrix BigOperators ComplexOrder
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

/-! ### Physical bounds on the search success probability

The success probability `SearchSuccessProbability` is — like any Born-rule
detection probability — a genuine probability: it lies in `[0, 1]`.  We prove
this from first principles for the concrete `noisyEvolve` model:

* the search Hamiltonian is **Hermitian** (`searchHamiltonian_isHermitian`),
  so the coherent propagator `U = exp(-iτH)` is unitary;
* the uniform initial state `ρ₀` is **positive semidefinite** of unit trace
  (`uniformInitial_posSemidef`);
* the dephasing damping factor is `1` on the diagonal, so the diagonal of the
  evolved state equals the diagonal of the unitary conjugation `U ρ₀ Uᴴ`,
  which is positive semidefinite — hence its diagonal entries are non-negative
  and sum to `tr(U ρ₀ Uᴴ) = tr ρ₀ = 1`.

These two bounds (`SearchSuccessProbability_nonneg`, `SearchSuccessProbability_le_one`)
are exactly the analytic hygiene needed to run `sSup`/`sInf` arguments on the
Caruso optimisation problem (boundedness of the feasible objective set). -/

/-- The search Hamiltonian `H = -γ A - P_M` is Hermitian: `-γ A` is Hermitian
(`A = G.adj` is Hermitian, `γ` real) and the marked-vertex term is a real
diagonal projector. -/
theorem searchHamiltonian_isHermitian
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) :
    (G.searchHamiltonian M γ).IsHermitian := by
  ext u v
  show star (G.searchHamiltonian M γ v u) = G.searchHamiltonian M γ u v
  unfold WeightedGraph.searchHamiltonian
  rw [star_sub, star_mul']
  congr 1
  · congr 1
    · rw [Complex.star_def, map_neg, Complex.conj_ofReal]
    · have := congrFun (congrFun G.herm u) v
      simpa [Matrix.conjTranspose_apply] using this
  · by_cases h : u = v
    · subst h; simp
    · rw [if_neg (fun hc => h hc.1.symm), if_neg (fun hc => h hc.1)]; simp

/-- For Hermitian `H`, the propagator `U = exp(-iτH)` is unitary: `Uᴴ U = 1`.
(`Uᴴ = exp((-iτH)ᴴ) = exp(iτH) = exp(-(-iτH))`, and `exp(-A) exp(A) = 1`.) -/
theorem exp_negiH_unitary (H : Matrix V V ℂ) (hH : H.IsHermitian) (τ : ℝ) :
    (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H))ᴴ *
      (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H)) = 1 := by
  set A : Matrix V V ℂ := -(Complex.I * (τ : ℂ)) • H with hA
  have hAH : Aᴴ = -A := by
    have hAH' : Aᴴ = (Complex.I * (τ : ℂ)) • H := by
      rw [hA, Matrix.conjTranspose_smul, hH.eq,
        show star (-(Complex.I * (τ : ℂ))) = (Complex.I * (τ : ℂ)) by
          rw [star_neg, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]; ring]
    rw [hAH', hA, neg_smul, neg_neg]
  rw [← Matrix.exp_conjTranspose, hAH,
    ← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
    NormedSpace.exp_zero]

/-- The uniform initial state `ρ₀ x y = 1/|V|` is positive semidefinite.
It equals `vecMulVec a (star a)` for the constant vector `a = 1/√|V|`. -/
theorem uniformInitial_posSemidef (V : Type u) [Fintype V] [DecidableEq V] :
    (uniformInitial V).PosSemidef := by
  have h : uniformInitial V
      = Matrix.vecMulVec (fun (_ : V) => (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ))
          (star (fun (_ : V) => (((Real.sqrt (Fintype.card V))⁻¹ : ℝ) : ℂ))) := by
    ext x y
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    show (uniformInitial V) x y = _
    unfold uniformInitial
    rw [← Complex.ofReal_mul, ← Real.sqrt_inv, Real.mul_self_sqrt (by positivity), one_div,
      ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [h]; exact Matrix.posSemidef_vecMulVec_self_star _

/-- The trace of `A · P_M` is the sum of the marked diagonal entries:
`tr(A · markedProjector M) = ∑_{m ∈ M} A m m`. -/
theorem trace_mul_markedProjector (A : Matrix V V ℂ) (M : Finset V) :
    (A * markedProjector M).trace = ∑ m ∈ M, A m m := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, markedProjector]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ M)]
  rw [show (∑ x ∈ Finset.univ.filter (· ∉ M),
      ∑ y, A x y * (if y = x ∧ y ∈ M then 1 else 0)) = 0 from ?_]
  · rw [add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_eq_single x]
    · rw [if_pos ⟨rfl, hx⟩, mul_one]
    · intro y _ hyx; rw [if_neg (fun h => hyx h.1), mul_zero]
    · intro h; exact absurd (Finset.mem_univ x) h
  · refine Finset.sum_eq_zero (fun x hx => ?_)
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [Finset.mem_filter] at hx
    by_cases hy : y = x ∧ y ∈ M
    · exact absurd (hy.1 ▸ hy.2) hx.2
    · rw [if_neg hy, mul_zero]

/-- **The search success probability is non-negative.**  The diagonal of the
evolved state equals the diagonal of the PSD matrix `U ρ₀ Uᴴ`, whose entries
are non-negative reals; the success probability is a finite sub-sum of them. -/
theorem SearchSuccessProbability_nonneg (G : WeightedGraph V) (M : Finset V)
    (N : NoiseModel V) (γ τ : ℝ) :
    0 ≤ SearchSuccessProbability G M N γ τ := by
  unfold SearchSuccessProbability
  set H := G.searchHamiltonian M γ with hH
  set U : Matrix V V ℂ := NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H) with hU
  set E := noisyEvolve H N τ (uniformInitial V) with hE
  have hdiag : ∀ m : V, E m m = (U * uniformInitial V * Uᴴ) m m := by
    intro m; rw [hE]; unfold noisyEvolve; simp only [if_true, one_mul, ← hU]
  have hB : (U * uniformInitial V * Uᴴ).PosSemidef :=
    (uniformInitial_posSemidef V).mul_mul_conjTranspose_same U
  rw [trace_mul_markedProjector, Finset.sum_congr rfl (fun m _ => hdiag m), Complex.re_sum]
  exact Finset.sum_nonneg (fun m _ => (RCLike.nonneg_iff.mp (hB.diag_nonneg (i := m))).1)

/-- **The search success probability is at most `1`.**  It equals
`∑_{m ∈ M} (U ρ₀ Uᴴ) m m` with `U ρ₀ Uᴴ` PSD of trace `1`; a sub-sum of the
non-negative diagonal of a unit-trace PSD matrix is `≤ 1`. -/
theorem SearchSuccessProbability_le_one (G : WeightedGraph V) (M : Finset V)
    (N : NoiseModel V) (γ τ : ℝ) :
    SearchSuccessProbability G M N γ τ ≤ 1 := by
  unfold SearchSuccessProbability
  set H := G.searchHamiltonian M γ with hH
  set U : Matrix V V ℂ := NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H) with hU
  set E := noisyEvolve H N τ (uniformInitial V) with hE
  have hdiag : ∀ m : V, E m m = (U * uniformInitial V * Uᴴ) m m := by
    intro m; rw [hE]; unfold noisyEvolve; simp only [if_true, one_mul, ← hU]
  have hB : (U * uniformInitial V * Uᴴ).PosSemidef :=
    (uniformInitial_posSemidef V).mul_mul_conjTranspose_same U
  rw [trace_mul_markedProjector, Finset.sum_congr rfl (fun m _ => hdiag m), Complex.re_sum]
  have hnn : ∀ m : V, 0 ≤ (U * uniformInitial V * Uᴴ) m m := fun m => hB.diag_nonneg
  have hsub : (∑ m ∈ M, ((U * uniformInitial V * Uᴴ) m m).re)
      ≤ ∑ m : V, ((U * uniformInitial V * Uᴴ) m m).re := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
    intro i _ _; exact (RCLike.nonneg_iff.mp (hnn i)).1
  refine hsub.trans ?_
  have htr : (∑ m : V, ((U * uniformInitial V * Uᴴ) m m).re)
      = (U * uniformInitial V * Uᴴ).trace.re := by
    rw [Matrix.trace, Complex.re_sum]; rfl
  rw [htr]
  have hUU : Uᴴ * U = 1 := exp_negiH_unitary H (searchHamiltonian_isHermitian G M γ) τ
  have htrB : (U * uniformInitial V * Uᴴ).trace = (uniformInitial V).trace := by
    rw [Matrix.trace_mul_comm (U * uniformInitial V) Uᴴ, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  rw [htrB, Matrix.trace]
  simp only [Matrix.diag_apply, uniformInitial]
  rw [Complex.re_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_cases hcard : Fintype.card V = 0
  · simp [hcard]
  · have hcre : ((1 : ℂ) / (Fintype.card V)).re = 1 / (Fintype.card V) := by
      rw [Complex.div_re]; simp [Complex.normSq_natCast]
    rw [hcre, mul_one_div, div_self]; exact_mod_cast hcard

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
above which the quantum walk loses its coherent advantage.

⚠ The two paragraphs above are the **physical CDHHP narrative** that motivates
this file; they are *not* what the named interfaces below prove.  The actual
`s_min`, `s_max` here are the **invented** `toyMinBreakingScore` /
`toyMaxBreakingScore` closed forms (see their notes), and `noisyEvolve` is uniform
vertex-basis dephasing, not a Lindblad generator — so the interfaces are bare
**toy `√n`-vs-`n` bounds keyed off an invented window**, not the Caruso noise-
assisted / restored-by-dephasing theorem. -/

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

/-- **TOY surrogate** for the graph-dependent *minimum useful breaking score* —
the smallest breaking score that should suffice to lift accidental dark-state
degeneracies in the closed-system spectrum at coupling `γ`.

⚠ This is an **invented scalar closed form** `gap²/(|γ|+1)`, NOT the CDHHP
threshold.  It is chosen only to be non-negative and to sit below
`toyMaxBreakingScore`; it carries no claim to reproduce the physical
optimal-dephasing onset.  (Renamed from `minBreakingScore`, audit 2026-06, to
flag the toy-model status — see the file banner.)

The intended physical reading was `s_min ∼ Δ²_dark / |γ|`, with `Δ_dark =
minSpectralGap` the gap between the (dark) ground state and the first non-dark
eigenstate; below `s_min` noise is "too weak" to escape the symmetric dark
subspace. -/
noncomputable def toyMinBreakingScore
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) : ℝ :=
  (minSpectralGap G M γ) ^ 2 / (|γ| + 1)

/-- **TOY surrogate** for the graph-dependent *maximum useful breaking score* —
the largest breaking score below which coherent oscillation between the uniform
initial state and the marked subspace should survive over a time `τ ≃ √|V| / γ`.

⚠ Like `toyMinBreakingScore`, this is an **invented scalar closed form**
(`toyMinBreakingScore + γ²/(gap+1)`), NOT the CDHHP decoherence threshold.  The
added `γ²/(gap+1)` term exists only to guarantee a strictly-positive window width
when `γ ≠ 0` (a degenerate spectrum collapses the window to a point).  (Renamed
from `maxBreakingScore`, audit 2026-06.)

The intended physical reading was `s_max ∼ γ²/Δ_dark` (the inverse coherent-
recurrence time); above it noise dephases the search amplitude faster than it
builds up and the walk classicalises. -/
noncomputable def toyMaxBreakingScore
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) : ℝ :=
  toyMinBreakingScore (I := I) G M γ P
    + γ ^ 2 / (minSpectralGap G M γ + 1)

/-- **TOY surrogate** for the *Caruso speedup window* — the (open) interval of
breaking scores that should produce Grover-rate search.

⚠ Built from the two **invented** thresholds `toyMinBreakingScore`,
`toyMaxBreakingScore` (see their notes and the file banner): it is a placeholder
interval, NOT the physical CDHHP window.  (Renamed from `carusoWindow`, audit
2026-06.) -/
def toyCarusoWindow
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) : Set ℝ :=
  Set.Ioo (toyMinBreakingScore (I := I) G M γ P) (toyMaxBreakingScore (I := I) G M γ P)

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

* if `BreakingScore N P ∈ toyCarusoWindow G M γ P`, then
  `OptimalSearchTimeHalf G M N γ ≤ C · √n` for a graph-independent
  constant `C`;
* if `BreakingScore N P ∉ closure (toyCarusoWindow G M γ P)`, then
  `OptimalSearchTimeHalf G M N γ ≥ c · n` for a graph-independent
  constant `c > 0`.

(Caruso–Chin–Datta–Huelga–Plenio, *J. Chem. Phys.* 131:105106 (2009),
arXiv:0901.4454.  See also Mohseni–Rebentrost–Lloyd–Aspuru-Guzik,
*J. Chem. Phys.* 129:174106 (2008).)

The quantifier structure is load-bearing:

* A per-instance Grover clause (`∃ C > 0` inside the instance quantifiers)
  carries no `O(√|V|)` content: `OptimalSearchTimeHalf ≥ 0` is a fixed finite
  real and `√|V| > 0` whenever `|V| ≥ 1`, so
  `C = (OptimalSearchTimeHalf + 1)/√|V|` satisfies the clause on every instance.

* A per-instance classical clause without the positivity hypothesis is false:
  `OptimalSearchTimeHalf = 0` whenever the feasible set `{τ ≥ 0 | SSP ≥ 1/2}`
  is empty (success never reaches `1/2`) — which `BreakingScore ∉
  closure(window)` does *not* prevent — and then `c·|V| ≤ 0` is unsatisfiable
  for `c > 0` when `|V| ≥ 1`.

The Childs–Goldstone/Caruso content is that the rate constants `C` (Grover)
and `c` (classical) are *graph-independent universal* constants.  They are
therefore quantified **outside** all instance data, and the classical lower
bound additionally requires `0 < OptimalSearchTimeHalf` (the search runs,
excluding the empty-feasible degeneracy).  This is exactly the cited scaling.

**TOY external, NOT CDHHP.**  This is a **scalar-dephasing
toy**: the conditioning interval `toyCarusoWindow` is an *invented* closed form
(`gap²/(|γ|+1)`, `+ γ²/(gap+1)`), not the CDHHP optimal-dephasing rate, and the
`noisyEvolve` channel is uniform vertex-basis dephasing, not a Lindblad
generator.  So the named field is **not** the Caruso noise-assisted / restored-
by-dephasing theorem; it is a bare conditional `√n` (Grover) vs `n` (classical)
dichotomy keyed off the toy window.  Following the `CNOOptimalSearch` /
`LovaszSDPDuality` pattern it is named as the `Prop`-valued field
`CarusoSpeedupDichotomy.dichotomy` and the theorem below is conditional on it.
No instance is provided.  ⚠ Stated on the file's invented
scalar surrogate `toyCarusoWindow` (see banner). -/
class CarusoSpeedupDichotomy.{uV, uI} : Prop where
  /-- TOY √n-vs-n dichotomy (scalar-dephasing toy, NOT CDHHP): graph-independent
  universal Grover/classical constants `C, c` across the invented toy window. -/
  dichotomy :
    ∃ (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ {V : Type uV} [Fintype V] [DecidableEq V] {I : Type uI} [Fintype I] [DecidableEq I]
        (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
        (P : EquitablePartition G I) (_hReg : isRegular G) (N : NoiseModel V),
        (N.BreakingScore P ∈ toyCarusoWindow (I := I) G M γ P →
          OptimalSearchTimeHalf G M N γ ≤ C * Real.sqrt (Fintype.card V)) ∧
        (N.BreakingScore P ∉ closure (toyCarusoWindow (I := I) G M γ P) →
          0 < OptimalSearchTimeHalf G M N γ →
          OptimalSearchTimeHalf G M N γ ≥ c * (Fintype.card V : ℝ))

/-- **Quantitative Caruso speedup (cited, conditional).**  Discharged from the
named external interface `[CarusoSpeedupDichotomy]`. -/
theorem search_speedup_via_partial_symmetry_breaking [h : CarusoSpeedupDichotomy.{u, v}] :
    ∃ (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {I : Type v} [Fintype I] [DecidableEq I]
        (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
        (P : EquitablePartition G I) (_hReg : isRegular G) (N : NoiseModel V),
        -- Grover-rate regime: universal constant `C`
        (N.BreakingScore P ∈ toyCarusoWindow (I := I) G M γ P →
          OptimalSearchTimeHalf G M N γ ≤ C * Real.sqrt (Fintype.card V)) ∧
        -- Classical regime: universal constant `c`, for searches with positive optimal time
        (N.BreakingScore P ∉ closure (toyCarusoWindow (I := I) G M γ P) →
          0 < OptimalSearchTimeHalf G M N γ →
          OptimalSearchTimeHalf G M N γ ≥ c * (Fintype.card V : ℝ)) :=
  h.dichotomy

/-- **Speedup *factor* over closed-system search.**

When the closed-system search is classical-rate (`Ω(n)`) and the noise
model lies in the Caruso window (Grover-rate, `O(√n)`), the noise-assisted
speedup factor is `Θ(√n)`.

The `√|V|` factor is the **composition** of the two regime bounds from
`search_speedup_via_partial_symmetry_breaking`:

* the closed system is **classical-rate**: `c_cl · |V| ≤ T(trivial)` for some
  `c_cl > 0` (the trivial model sits outside the window);
* the noisy search is **Grover-rate**: `T(N) ≤ C_g · √|V|` for some `C_g > 0` (the
  window payoff).

Taking these two regime bounds as explicit hypotheses (with their constants
`c_cl, C_g`), the speedup factor `c = c_cl / C_g` follows from
`√|V| · √|V| = |V|`.  The deep content lives in the regime bounds (the headline
theorem); the factor is their elementary consequence.

A per-instance form `∃ c > 0, T(trivial) ≥ c·√|V|·T(N)` would be wrong in both
directions: if `T(trivial) = 0` (empty feasible set) while `T(N) > 0` and
`|V| ≥ 1`, then `0 ≥ c·√|V|·(positive)` is unsatisfiable for `c > 0`; otherwise
a per-instance `c` discharges the single inequality trivially. -/
theorem caruso_speedup_factor
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) (_hReg : isRegular G) (N : NoiseModel V)
    (_hN : N.BreakingScore P ∈ toyCarusoWindow (I := I) G M γ P)
    (c_cl C_g : ℝ) (hc_cl : 0 < c_cl) (hC_g : 0 < C_g)
    -- closed-system search is classical-rate `Ω(|V|)`
    (hclassical : c_cl * (Fintype.card V : ℝ) ≤
      OptimalSearchTimeHalf G M (NoiseModel.trivial V) γ)
    -- noisy search is Grover-rate `O(√|V|)`
    (hgrover : OptimalSearchTimeHalf G M N γ ≤ C_g * Real.sqrt (Fintype.card V)) :
    OptimalSearchTimeHalf G M (NoiseModel.trivial V) γ ≥
      (c_cl / C_g) * Real.sqrt (Fintype.card V) * OptimalSearchTimeHalf G M N γ := by
  -- Let `r := √|V| ≥ 0`, `T0 := T(trivial)`, `TN := T(N)`.
  set r : ℝ := Real.sqrt (Fintype.card V) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- `(c_cl/C_g)·r·TN ≤ (c_cl/C_g)·r·(C_g·r) = c_cl·r² = c_cl·|V| ≤ T0`.
  have hcoef : 0 ≤ (c_cl / C_g) * r := mul_nonneg (by positivity) hr0
  have hstep : (c_cl / C_g) * r * OptimalSearchTimeHalf G M N γ
      ≤ (c_cl / C_g) * r * (C_g * r) :=
    mul_le_mul_of_nonneg_left hgrover hcoef
  have hsq : (c_cl / C_g) * r * (C_g * r) = c_cl * (r * r) := by
    rw [show (c_cl / C_g) * r * (C_g * r) = (c_cl / C_g * C_g) * (r * r) by ring,
      div_mul_cancel₀ c_cl (ne_of_gt hC_g)]
  have hrr : r * r = (Fintype.card V : ℝ) := by
    rw [hr, Real.mul_self_sqrt (by positivity)]
  rw [hsq, hrr] at hstep
  -- chain: `(c_cl/C_g)·r·TN ≤ c_cl·|V| ≤ T0`.
  exact le_trans hstep hclassical

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
strictly positive but bounded.

Both sides of the `>` are the *same* `Re tr(noisyEvolve · P_M)` primitive: the
closed-system baseline is `SearchSuccessProbability G M (NoiseModel.trivial V)
γ τ`, the zero-noise (unitary-conjugation) model, **not**
`closedSystemSuccessProbability G M γ τ` (= `∑ ‖searchEvolve_mm‖`), which is a
different primitive (cf. `caruso_trivial_eq_closed`).  So `∃τ` constrains two
values living in the same `[0,1]` Born scale.

**External, cited.**  Named as the `Prop`-valued field `CarusoAntiZeno.antiZeno`
(CDHHP/Childs–Goldstone); the theorem is conditional on it.  No instance is
provided.  ⚠ Stated on the file's invented scalar surrogate `toyCarusoWindow`
(see banner). -/
class CarusoAntiZeno.{uV, uI} : Prop where
  /-- CDHHP anti-Zeno mechanism: positive in-window breaking score strictly
  improves the success probability over the closed-system (zero-noise) search at
  some `τ > 0` — both sides the same `Re tr(· P_M)` Born probability. -/
  antiZeno :
    ∀ {V : Type uV} [Fintype V] [DecidableEq V] {I : Type uI} [Fintype I] [DecidableEq I]
      (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
      (P : EquitablePartition G I) (N : NoiseModel V),
      0 < N.BreakingScore P →
      (N.BreakingScore P ∈ toyCarusoWindow (I := I) G M γ P →
        ∃ τ : ℝ, 0 < τ ∧
          SearchSuccessProbability G M N γ τ >
            SearchSuccessProbability G M (NoiseModel.trivial V) γ τ)

/-- **Anti-Zeno mechanism (cited, conditional).**  Discharged from the named
external interface `[CarusoAntiZeno]`. -/
theorem anti_zeno_mechanism [h : CarusoAntiZeno.{u, v}]
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (P : EquitablePartition G I) (N : NoiseModel V) :
    -- noise produces cell-information broadcast iff breaking score is positive
    0 < N.BreakingScore P →
    -- and produces speedup iff the rate is in the Caruso window: the noisy success
    -- probability strictly exceeds the closed-system (zero-noise) one — same `Re tr`
    -- Born primitive on both sides
    (N.BreakingScore P ∈ toyCarusoWindow (I := I) G M γ P →
      ∃ τ : ℝ, 0 < τ ∧
        SearchSuccessProbability G M N γ τ >
          SearchSuccessProbability G M (NoiseModel.trivial V) γ τ) :=
  h.antiZeno G M γ P N

/-- **Anti-Zeno *vs* Zeno regimes.**  The Caruso speedup window
`(s_min, s_max)` is the *anti-Zeno regime*; above `s_max` the dynamics
re-enter the **quantum Zeno** regime where measurements freeze
evolution.  Below `s_min` no measurement happens at all and the
closed-system dark subspace persists. -/
theorem zeno_antiZeno_boundary
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) (hγ : γ ≠ 0)
    (P : EquitablePartition G I) :
    0 ≤ toyMinBreakingScore (I := I) G M γ P ∧
      toyMinBreakingScore (I := I) G M γ P < toyMaxBreakingScore (I := I) G M γ P := by
  -- The hypothesis `hγ : γ ≠ 0` is necessary for the strict `<`: the window
  -- width is `γ²/(gap+1)`, which collapses to `0` when `γ = 0`.
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
  · -- `toyMinBreakingScore = gap²/(|γ|+1) ≥ 0`.
    unfold toyMinBreakingScore
    positivity
  · -- `min < max = min + γ²/(gap+1)`, and `γ²/(gap+1) > 0` since `γ ≠ 0`.
    unfold toyMaxBreakingScore
    have hγsq : (0 : ℝ) < γ ^ 2 := by positivity
    have : (0 : ℝ) < γ ^ 2 / (minSpectralGap G M γ + 1) := div_pos hγsq hden2
    linarith

/-! ## 4. Concrete examples (TOY √n bounds, conditional on named externals)

These are **bare toy `√n`-type bounds**, not Caruso noise-assisted / restoration
results: the dephasing models used (`singleVertexDephasing`, `perVertexDephasing`)
are *diagonal* and have `BreakingScore = 0`, so they break no symmetry.
Each bound is a theorem conditional on a named, no-instance external; the
analytic hygiene around it is proven outright.

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
`|m⟩⟨m|` with rate `rate`.  Re-used from D8's `boundaryDephasing`.

⚠ NOTE: `|m⟩⟨m| = single m m 1` is **diagonal**, so by D8's
`boundaryDephasing_breakingScore` its `BreakingScore` on the marked-refined
partition is **`0`** — it carries *no* off-block (symmetry-breaking) Frobenius
mass.  Consequently this model does **not** drive the "noise-assisted /
restored-by-dephasing" mechanism; the `√n` bound below is a bare toy bound, not a
restoration result. -/
noncomputable def singleVertexDephasing
    (V : Type u) [Fintype V] [DecidableEq V] (m : V) (rate : ℝ) :
    NoiseModel V :=
  NoiseEquitable.NoiseModel.boundaryDephasing V m rate

/-- **Example 1 (TOY).**  Single-marked search on `K_n` with dephasing on the
marked vertex — a bare `√n` toy bound, **not** a Caruso restoration result.

* Optimal time: `O(√n)` — the Grover rate (which the *closed* system already
  achieves on `K_n`; the dephasing does not destroy it).

(Childs–Goldstone (2004) for the closed-system `K_n` Grover baseline.)

Three remarks on the statement's shape:

* **Not noise-assisted.**  `singleVertexDephasing` is the *diagonal* projector
  `|m⟩⟨m|`, whose `BreakingScore` is `0` (`boundaryDephasing_breakingScore`).
  So this example exhibits **no** symmetry-breaking and cannot be a
  "restoration by dephasing" instance; on `K_n` the closed system is *already*
  Grover-rate, so there is nothing to restore.  It is a bare toy `O(√n)` bound
  (Caruso Sec. IV.B is about restoration on graphs where the closed search
  fails — not `K_n`).

* **`O(√n)` is sharp; no sub-Grover rate is possible.**  Spatial search for a
  *single* marked vertex on the complete graph `K_n` is *unstructured* search
  of `n` items (all vertices are symmetric), so it is subject to the
  Bennett–Bernstein–Brassard–Vazirani `Ω(√n)` query/time lower bound.  Since
  `√(n/log n) = o(√n)`, a uniform bound `T(n) ≤ C·√(n/log n)` would force
  `T(n) = o(√n)`, violating the `Ω(√n)` bound — no such `C` exists.
  Open-system dephasing cannot beat Grover: it destroys coherence, it does
  not add query structure.

* **Uniform constant.**  With `C` quantified inside a fixed-`n` theorem,
  `C = (T+1)/√n` discharges `T ≤ C·√n` trivially; `C` is therefore a single
  constant uniform over **all** `n`.

**TOY external (scalar-dephasing toy, NOT CDHHP).**  The uniform `O(√n)` bound is
named as the `Prop`-valued field `CarusoKnScaling.bound` (Childs–Goldstone
baseline for the `K_n` Grover rate); the theorem is conditional on it.  No
instance is provided. -/
class CarusoKnScaling.{uV} : Prop where
  /-- `K_n` single-marked dephasing keeps the Grover `O(√n)` rate (uniform `C`). -/
  bound :
    ∀ (γ : ℝ), 0 < γ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 2 ≤ n →
          ∀ (V : Type uV) [Fintype V] [DecidableEq V], Fintype.card V = n →
            ∀ (m : V) (rate : ℝ), 0 < rate →
              OptimalSearchTimeHalf (completeWG V) {m}
                (singleVertexDephasing V m rate) γ ≤ C * Real.sqrt (n : ℝ)

/-- **Example 1, `K_n` toy `O(√n)` bound (conditional).**  Discharged from the
toy external `[CarusoKnScaling]`.  (Toy bound, not a Caruso restoration
result — the diagonal marked-vertex dephasing has `BreakingScore = 0`.) -/
theorem caruso_Kn_singleMarked [h : CarusoKnScaling.{u}] (γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n →
        ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = n →
          ∀ (m : V) (rate : ℝ), 0 < rate →
            OptimalSearchTimeHalf (completeWG V) {m}
              (singleVertexDephasing V m rate) γ ≤
                C * Real.sqrt (n : ℝ) :=
  h.bound γ hγ

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

⚠ NOTE: every jump operator `|m⟩⟨m| = single m m 1` is **diagonal**, so
this whole model has zero off-block Frobenius mass and (by D8's
`boundaryDephasing_breakingScore` applied per-projector) `BreakingScore = 0`.  It
is therefore **not** a symmetry-breaking model and does **not** drive
restoration; the `√(2^d/|M|)` bound below is a bare toy bound. -/
noncomputable def perVertexDephasing
    (V : Type u) [Fintype V] [DecidableEq V]
    (M : Finset V) (rates : V → ℝ) : NoiseModel V where
  -- Lindblad operators are the projectors `|m⟩⟨m| = single m m 1` for `m ∈ M`.
  lindblad_operators := M.image (fun m : V => Matrix.single m m 1)
  -- the rate of a jump operator is `|rates m|` for the (chosen) vertex `m`
  -- whose projector it is; fallback `0` otherwise.
  coherence_rates L :=
    if h : ∃ m ∈ M, Matrix.single m m 1 = L then Real.toNNReal (rates h.choose) else 0

/-- **Example 2 (TOY).**  Multi-marked search on the hypercube `Q_d` (so
`|V| = 2^d`) with per-vertex dephasing on a marked set of size `m` — a bare
`√(2^d/m)` toy bound, **not** a Caruso restoration result.

* Predicted optimal time: `O(√(2^d / m))` — the multi-target Grover scaling.

(Patel–Reitzner–Buzek for the closed-system multi-marked hypercube baseline.)

Two remarks on the statement's shape:

* **Not noise-assisted.**  `perVertexDephasing` is built from *diagonal*
  projectors `|m⟩⟨m|`, so its `BreakingScore` is `0` (no off-block mass; cf.
  `boundaryDephasing_breakingScore`): this model breaks no symmetry and
  restores nothing.  It is a bare toy `O(√(2^d/m))` bound with only the
  closed-system multi-marked baseline citation.

* **Uniform constant.**  As in `caruso_Kn_singleMarked`: for a fixed `d` (and
  fixed `M`, `rates`) the base `√(2^d/|M|)` is a fixed positive real
  (`|M| ≥ 1`, `2^d ≥ 1`) and the optimal time is a fixed finite real, so a
  per-instance `C` would discharge `T ≤ C·√(2^d/|M|)` trivially.  `C` is
  therefore a single constant uniform over **all** `d` (and the per-`d` data
  `M`, `rates`).

**TOY external (scalar-dephasing toy, NOT CDHHP).**  The uniform `O(√(2^d/|M|))`
bound is named as the `Prop`-valued field `CarusoHypercubeScaling.bound`
(Patel–Reitzner–Buzek multi-marked hypercube baseline); the theorem is `#print
axioms`-clean and conditional on it.  No instance is provided. -/
class CarusoHypercubeScaling : Prop where
  /-- TOY hypercube multi-marked `O(√(2^d/|M|))` bound (uniform `C`) — bare toy
  `√n`-type bound, NOT the Caruso restored-by-dephasing result (the diagonal
  per-vertex dephasing here has `BreakingScore = 0`). -/
  bound :
    ∀ (γ : ℝ), 0 < γ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (d : ℕ) (M : Finset (Fin (2 ^ d))) (rates : Fin (2 ^ d) → ℝ), 1 ≤ M.card →
          OptimalSearchTimeHalf (hypercubeWG d) M
            (perVertexDephasing _ M rates) γ ≤
              C * Real.sqrt ((2 ^ d : ℝ) / (M.card : ℝ))

/-- **Example 2, hypercube multi-marked toy `O(√(2^d/|M|))` bound (conditional).**
Discharged from the toy external `[CarusoHypercubeScaling]`.  (Toy bound, not a
Caruso restoration result — the diagonal per-vertex dephasing has
`BreakingScore = 0`.) -/
theorem caruso_hypercube_multiMarked [h : CarusoHypercubeScaling] (γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (M : Finset (Fin (2 ^ d))) (rates : Fin (2 ^ d) → ℝ), 1 ≤ M.card →
        OptimalSearchTimeHalf (hypercubeWG d) M
          (perVertexDephasing _ M rates) γ ≤
            C * Real.sqrt ((2 ^ d : ℝ) / (M.card : ℝ)) :=
  h.bound γ hγ

/-! ## 5. Optimal-noise engineering on the quotient

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

/-- **Optimisation reduction theorem (one-sided).**

Only the inequality `carusoOptimumOnQuotient ≤ carusoOptimum` holds: the
quotient-side optimum ranges over the strictly smaller family of
*cell-uniform-symmetric* noise models, so it cannot exceed the host-side
optimum.  The reverse inequality (hence the equality) fails for exactly the
reason that makes the Caruso effect interesting — in the noise-assisted regime
a *symmetry-breaking* model (outside the quotient family) strictly outperforms
every cell-symmetric one, so equality would assert that the optimal noise is
always cell-symmetric, the negation of the headline phenomenon.

The inequality is the bound a downstream optimiser needs: the small
finite-dimensional quotient search gives a *lower* bound on the achievable
success probability, certified `≤` the true host optimum.

The proof is `sSup` monotonicity: the quotient-feasible objective set is a
subset of the host-feasible set, the host objective is bounded above by `1`
(`SearchSuccessProbability_le_one`), and every objective value is `≥ 0`
(`SearchSuccessProbability_nonneg`) so the host supremum is `≥ 0`. -/
theorem carusoOptimumOnQuotient_le_carusoOptimum
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ)
    (P : EquitablePartition G I) :
    carusoOptimumOnQuotient (I := I) G M γ τ γ_total P ≤
      carusoOptimum G M γ τ γ_total := by
  unfold carusoOptimumOnQuotient carusoOptimum
  set Sq : Set ℝ := { p : ℝ | ∃ N ∈ boundedRate (V := V) γ_total,
      N.cellUniformSymmetric P ∧ p = SearchSuccessProbability G M N γ τ } with hSq
  set Sh : Set ℝ := { p : ℝ | ∃ N ∈ boundedRate (V := V) γ_total,
      p = SearchSuccessProbability G M N γ τ } with hSh
  -- the host objective set is bounded above by `1`.
  have hbdd : BddAbove Sh := by
    refine ⟨1, ?_⟩
    rintro p ⟨N, _, rfl⟩
    exact SearchSuccessProbability_le_one G M N γ τ
  -- the quotient objective set is a subset of the host objective set.
  have hsub : Sq ⊆ Sh := by
    rintro p ⟨N, hN, _, rfl⟩
    exact ⟨N, hN, rfl⟩
  -- the host supremum is `≥ 0` (every objective value is `≥ 0`).
  have hSh_nonneg : 0 ≤ sSup Sh := by
    refine Real.sSup_nonneg ?_
    rintro p ⟨N, _, rfl⟩
    exact SearchSuccessProbability_nonneg G M N γ τ
  by_cases hne : Sq.Nonempty
  · exact csSup_le_csSup hbdd hne hsub
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    exact hSh_nonneg

/-- **Optimisation reduction theorem (legacy name, one-sided).**

The quotient-restricted optimum lower-bounds the host optimum
(`carusoOptimumOnQuotient_le_carusoOptimum`).  See that theorem's docstring
for why the corresponding *equality* is false (it would contradict the
noise-assisted speedup itself). -/
theorem caruso_optimisation_on_quotient
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ)
    (P : EquitablePartition G I) :
    carusoOptimumOnQuotient (I := I) G M γ τ γ_total P ≤
      carusoOptimum G M γ τ γ_total :=
  carusoOptimumOnQuotient_le_carusoOptimum G M γ τ γ_total P

/-- The **trivial (zero) noise model is feasible** for any non-negative rate
budget: its total rate is `0 ≤ γ_total`. -/
theorem trivial_mem_boundedRate {γ_total : ℝ} (hγ : 0 ≤ γ_total) :
    (NoiseModel.trivial V) ∈ boundedRate (V := V) γ_total := by
  show (∑ L ∈ (NoiseModel.trivial V).lindblad_operators,
      ((NoiseModel.trivial V).coherence_rates L : ℝ)) ≤ γ_total
  rw [show (NoiseModel.trivial V).lindblad_operators = ∅ from rfl, Finset.sum_empty]
  exact hγ

/-- **Engineering corollary (ε-approximation form).**

For any tolerance `ε > 0` and non-negative rate budget, there is a *concrete
feasible* noise model whose success probability comes within `ε` of the host
optimum (and never exceeds it).  This is exactly what a finite-dimensional
optimiser delivers — feasible models approaching the supremum — and is proved
from the `sSup` characterisation (`exists_lt_of_lt_csSup`), using feasibility
of the trivial model to guarantee a non-empty feasible objective set.

The ε is not removable without further input:

* the supremum `carusoOptimum` need not be *attained* — the feasible family of
  bounded-rate noise models is not compact (cf. `exists_carusoOptimal`), so
  there may be no maximiser;
* requiring a (would-be) optimiser's breaking score to lie in the *open*
  Caruso window is exactly the noise-assisted-speedup claim, the *content* of
  the cited Caruso theorem, not a free corollary. -/
theorem caruso_optimal_noise_engineerable
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ) (hγ : 0 ≤ γ_total)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : NoiseModel V,
      (∑ L ∈ N.lindblad_operators, (N.coherence_rates L : ℝ)) ≤ γ_total ∧
      carusoOptimum G M γ τ γ_total - ε < SearchSuccessProbability G M N γ τ ∧
      SearchSuccessProbability G M N γ τ ≤ carusoOptimum G M γ τ γ_total := by
  set S : Set ℝ := { p : ℝ | ∃ N ∈ boundedRate (V := V) γ_total,
      p = SearchSuccessProbability G M N γ τ } with hS
  -- `S` is nonempty (the trivial model is feasible) and bounded above by `1`.
  have hne : S.Nonempty :=
    ⟨_, NoiseModel.trivial V, trivial_mem_boundedRate hγ, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨1, ?_⟩; rintro p ⟨N, _, rfl⟩; exact SearchSuccessProbability_le_one G M N γ τ
  -- pick a feasible value within `ε` of the supremum.
  obtain ⟨p, ⟨N, hN, rfl⟩, hp⟩ :=
    exists_lt_of_lt_csSup hne (show carusoOptimum G M γ τ γ_total - ε < sSup S by
      have : carusoOptimum G M γ τ γ_total = sSup S := rfl
      rw [this]; linarith)
  refine ⟨N, hN, ?_, ?_⟩
  · exact hp
  · exact le_csSup hbdd ⟨N, hN, rfl⟩

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

⚠ The `√n·(s + Δ²/s)/γ` shape is **this file's own ansatz**, *motivated by* the
Caruso et al. noise-assisted-transport picture — it is **not** taken from a
published equation.  (Do not cite "Caruso et al. 2010, Eq. (12)–(15)": that
paper [Phys. Rev. A 81, 062346 (2010)] is about *entanglement and entangling
power*, not search-time scaling, and has no such formula.)  The minimum over
`s` is the *anti-Zeno optimum*; its AM-GM minimisation is proven below in
`caruso_optimal_breakingScore`.

The quantifier structure and hypotheses are load-bearing:

* **Universal constants.**  The Caruso content is that `C₁, C₂` are
  *graph-independent universal* constants.  With the constants quantified
  *inside* the per-instance theorem one may take
  `C₁ = C₂ = OptimalSearchTimeHalf / (√|V|·(s+Δ²/s)/γ)`, collapsing both
  bounds to a trivial equality; they are therefore hoisted out of all
  instance data.

* **`0 < OptimalSearchTimeHalf` is necessary for the lower bound.**
  `OptimalSearchTimeHalf = sInf {τ ≥ 0 | SSP ≥ 1/2}` is `0` whenever the
  feasible set is empty (the noisy search never reaches success `1/2`) *or*
  contains `0` (instant success) — and `0 < s, 0 < Δ, 0 < γ` do not prevent
  this (e.g. a noise model so strong it destroys all coherence gives
  `sInf ∅ = 0`).  When `|V| ≥ 1` the factor `√|V| · (s + Δ²/s) / γ` is
  strictly positive, so `C₁ · (positive) ≤ 0` is unsatisfiable for `C₁ > 0`.

* **The window hypothesis is necessary for the upper bound.**  The scaling
  `τ_opt ≈ √|V|·(s+Δ²/s)/γ` is the *Grover-rate* formula and holds **only
  inside the window**.  Outside it (classical regime) the search runs in
  `Θ(|V|)` time, so `T/(√|V|·(s+Δ²/s)/γ) = Θ(√|V|) → ∞` and no universal
  upper constant `C₂` can exist.

**TOY external, motivated by Caruso (NOT a cited equation).**  Named as the
`Prop`-valued field `CarusoQuantitativeFormula.formula`; the theorem below is
conditional on this field.  No instance is provided.  ⚠ Stated on the file's
invented scalar surrogate `toyCarusoWindow` (see banner). -/
class CarusoQuantitativeFormula.{uV, uI} : Prop where
  /-- TOY `√n·(s+Δ²/s)/γ` optimal-time scaling ansatz (motivated by Caruso, not a
  cited equation): universal constants `C₁ ≤ C₂`, in the toy window, for a
  search with positive optimal time. -/
  formula :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ ≤ C₂ ∧
      ∀ {V : Type uV} [Fintype V] [DecidableEq V] {I : Type uI} [Fintype I] [DecidableEq I]
        (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
        (P : EquitablePartition G I) (N : NoiseModel V),
        N.BreakingScore P ∈ toyCarusoWindow (I := I) G M γ P →
        0 < N.BreakingScore P → 0 < darkSpectralGap G M γ → 0 < γ →
        0 < OptimalSearchTimeHalf G M N γ →
          C₁ * Real.sqrt (Fintype.card V)
              * (N.BreakingScore P + darkSpectralGap G M γ ^ 2 / N.BreakingScore P) / γ ≤
            OptimalSearchTimeHalf G M N γ ∧
          OptimalSearchTimeHalf G M N γ ≤
            C₂ * Real.sqrt (Fintype.card V)
              * (N.BreakingScore P + darkSpectralGap G M γ ^ 2 / N.BreakingScore P) / γ

/-- **Caruso quantitative formula (toy ansatz, conditional).**  Discharged from
the named toy external interface `[CarusoQuantitativeFormula]`.  (The
`√n·(s+Δ²/s)/γ` shape is this file's ansatz motivated by Caruso, not a cited
equation.) -/
theorem caruso_quantitative_formula [h : CarusoQuantitativeFormula.{u, v}] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ ≤ C₂ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {I : Type v} [Fintype I] [DecidableEq I]
        (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
        (P : EquitablePartition G I) (N : NoiseModel V),
        N.BreakingScore P ∈ toyCarusoWindow (I := I) G M γ P →
        0 < N.BreakingScore P → 0 < darkSpectralGap G M γ → 0 < γ →
        0 < OptimalSearchTimeHalf G M N γ →
          C₁ * Real.sqrt (Fintype.card V)
              * (N.BreakingScore P + darkSpectralGap G M γ ^ 2 / N.BreakingScore P) / γ ≤
            OptimalSearchTimeHalf G M N γ ∧
          OptimalSearchTimeHalf G M N γ ≤
            C₂ * Real.sqrt (Fintype.card V)
              * (N.BreakingScore P + darkSpectralGap G M γ ^ 2 / N.BreakingScore P) / γ :=
  h.formula

/-- **Optimal breaking score** (closed-form minimisation): the leading-order
Caruso time shape `f(s) = s + Δ²/s` (the bracket of `caruso_quantitative_formula`,
with `Δ := darkSpectralGap G M γ`) is *minimised* over breaking scores `s > 0`
at the **unique** minimiser `s_* = Δ`, where it takes the value `2Δ`.

Concretely, for `Δ > 0` we prove:
 * lower bound / optimality: `∀ s > 0, 2·Δ ≤ s + Δ²/s` (so `f(Δ) = 2Δ` is the min);
 * uniqueness: any `s > 0` attaining the minimum `s + Δ²/s = 2Δ` equals `Δ`.

This is the anti-Zeno AM-GM optimum: `s + Δ²/s ≥ 2√(s·Δ²/s) = 2Δ`, with equality
iff `s = Δ`.  It is a self-contained AM-GM fact about the file's own
`f(s) = s + Δ²/s` ansatz (motivated by the Caruso anti-Zeno picture); it does
*not* depend on any external interface or published equation. -/
theorem caruso_optimal_breakingScore
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ)
    (hΔ : 0 < darkSpectralGap G M γ) :
    let Δ := darkSpectralGap G M γ
    -- value at the minimiser is `2Δ`
    (Δ + Δ ^ 2 / Δ = 2 * Δ) ∧
    -- optimality: `2Δ` lower-bounds `f(s)` for every positive breaking score
    (∀ s : ℝ, 0 < s → 2 * Δ ≤ s + Δ ^ 2 / s) ∧
    -- uniqueness of the minimiser
    (∀ s : ℝ, 0 < s → s + Δ ^ 2 / s = 2 * Δ → s = Δ) := by
  intro Δ
  have hΔ' : (0 : ℝ) < Δ := hΔ
  refine ⟨?_, ?_, ?_⟩
  · -- `Δ + Δ²/Δ = Δ + Δ = 2Δ`
    rw [sq, mul_div_assoc, div_self (ne_of_gt hΔ'), mul_one]; ring
  · -- optimality from `(s - Δ)² ≥ 0`: `s + Δ²/s - 2Δ = (s - Δ)²/s ≥ 0`
    intro s hs
    have hid : s + Δ ^ 2 / s - 2 * Δ = (s - Δ) ^ 2 / s := by
      field_simp; ring
    have hnn : 0 ≤ (s - Δ) ^ 2 / s := div_nonneg (sq_nonneg _) hs.le
    rw [← hid] at hnn
    linarith
  · -- uniqueness: `s + Δ²/s = 2Δ` ⇒ `(s - Δ)² = 0` ⇒ `s = Δ`
    intro s hs heq
    have hsne : s ≠ 0 := ne_of_gt hs
    have hkey : s ^ 2 + Δ ^ 2 = 2 * Δ * s := by
      have := heq
      field_simp at this
      nlinarith [this]
    nlinarith [sq_nonneg (s - Δ), hkey]

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

-- **Graphon Caruso speedup — intentionally NOT stated as a theorem.**
-- The intended (unproven, open) statement is: for a sequence `G_n` of `d_n`-regular
-- weighted graphs converging in cut-distance to a graphon `W`, with marked sets
-- `M_n` of normalised size `→ μ ∈ (0,1)` and noise models `N_n` of breaking score
-- `→ s_inf > 0` lying in the graphon's (toy) Caruso window,
--   `lim_n OptimalSearchTimeHalf G_n M_n N_n γ / √|V_n| ≤ C(W, μ, γ, s_inf)`.
-- Stating it faithfully requires the graphon framework of `Graphplay.Graphon` and is
-- left open.

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
budget `γ_total`.

The hypothesis `0 ≤ γ_total` is necessary: `IsCarusoOptimal` requires the
witness `N` to satisfy `N ∈ boundedRate γ_total`, i.e. `totalRate N ≤ γ_total`,
and `totalRate N` is a sum of non-negative coherence rates, hence `≥ 0`.  For
`γ_total < 0` the feasible set is empty and `∃ N, IsCarusoOptimal …` is false.
With `0 ≤ γ_total` the trivial no-jump model is feasible
(`trivial_mem_boundedRate`), so the feasible set is non-empty; the remaining
content is the analytic attainment claim — that the `sSup` defining
`carusoOptimum` is *attained* by some feasible model, a maximiser over the
infinite, not-obviously-compact family of bounded-rate noise models.  (The
ε-approximation form — a feasible model within `ε` of the optimum — is proven
as `caruso_optimal_noise_engineerable`.)

**External (analytic), named.**  The attainment is the `Prop`-valued field
`CarusoOptimumAttained.attained`; the theorem is conditional on it.  No
instance is provided — the maximiser need not exist for a non-compact feasible
family, so this is a real assumption (true in any regime where the
bounded-rate family is compact, e.g. a finite Lindblad-generator basis). -/
class CarusoOptimumAttained.{uV} : Prop where
  /-- The `sSup` defining `carusoOptimum` is attained by some feasible noise
  model, for any non-negative rate budget. -/
  attained :
    ∀ {V : Type uV} [Fintype V] [DecidableEq V]
      (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ), 0 ≤ γ_total →
      ∃ N : NoiseModel V, IsCarusoOptimal G M γ τ γ_total N

/-- **Existence of a Caruso-optimal noise model (cited, conditional).**
Discharged from the named analytic interface `[CarusoOptimumAttained]`. -/
theorem exists_carusoOptimal [h : CarusoOptimumAttained.{u}]
    (G : WeightedGraph V) (M : Finset V) (γ τ γ_total : ℝ) (hγ : 0 ≤ γ_total) :
    ∃ N : NoiseModel V, IsCarusoOptimal G M γ τ γ_total N :=
  h.attained G M γ τ γ_total hγ

/-- **Sentinel**: connection to the closed-system Childs–Goldstone
baseline.  When `N = trivial`, the Caruso noisy evolution reduces to pure
unitary conjugation by the search propagator.

Note the equality
`SearchSuccessProbability G M (trivial) γ τ = closedSystemSuccessProbability …`
does **not** hold — the two sides are built from mismatched primitives.  The LHS
is `Re tr(noisyEvolve … · P_M)` (a trace of a density-matrix evolution),
whereas `closedSystemSuccessProbability` (`∑_{m∈M} ‖searchEvolve M γ τ m m‖`)
is a sum of moduli of diagonal propagator entries; these are not equal in
general.  The reduction that does hold: at zero noise the `noisyEvolve`
superoperator is exactly unitary conjugation `ρ ↦ U ρ U†` by the search propagator
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
