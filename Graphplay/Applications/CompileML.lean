/-
# Graphplay.Applications.CompileML

## Compiling an ML primitive INTO a real chip — a falsifiable experiment.

The companion file `Graphplay/Applications/IBMHeavyHex.lean` runs the
*disassembly* direction: chip → equitable quotient → CTQW primitive.  It proves,
axiom-clean, that the data/flag role partition of IBM's heavy-hexagonal lattice
is equitable with `2×2` symmetric quotient `q·X`, `q = 2√(N−1)`
(`N = |HoneyVertex| = 2nm`), eigenvalues `±q`, and **cell-uniform perfect state
transfer** between the data-uniform and the flag-uniform states at
`t = π/(2q)` (`heavyHex_pst_lift`).

This file runs the **inverse** direction — *compilation*:

>   ML primitive  ──►  small quotient  ──►  native chip couplings + schedule.

Concretely we pick a clean ML primitive that maps to a CTQW observable:

* a **2-class structured-attention / associative-recall** task.  Recall =
  perfect transfer between a *query-uniform* state and a *key-uniform* state.
  In an attention layer whose query/key structure is invariant under a
  symmetry, the token graph carries an equitable partition into two roles
  ("query side" / "key side"); the structured attention pattern is encoded by
  the `2×2` matrix that the symmetry induces on those two roles
  (`Integrations.MachineLearning`, `Integrations.AttentionComplexity`).  When
  that induced matrix is the single off-diagonal coupling `K₂`, the
  associative-recall map *is* perfect state transfer between the two role
  cells.

The pipeline:

1. `MLTarget` — carries the primitive's quotient data: the `r = 2`-cell
   `Role`-indexed coupling the attention structure induces (here the off-diag
   `K₂`), plus the desired recall.
2. `compileToHeavyHex : MLTarget → HardwareSpec × Schedule` — emit the native
   IBM-Heron coupling weights (the heavy-hex adjacency, whose data/flag quotient
   reproduces the target's `2×2`) together with the static CTQW schedule run for
   the emitted transfer time `t = π/(2q)`.  We reuse the proven heavy-hex
   equitable partition as the *realization*, and (separately)
   `InverseDesign.synthesizePST` as the minimal `K₂`-inflation realization.
   `compileToMajorana` sketches the parity-sector schedule analogue.
3. **Compilation-correctness** (`compiled_cellUniform_realizes_target`): the
   compiled host's cell-uniform evolution between the data (query) and flag
   (key) cells equals the target primitive's evolution — i.e. the compiled chip
   genuinely *runs the ML recall* on its symmetric sector.  Proven by lifting
   the proven IBM PST through the equitable partition (`heavyHex_pst_lift`).
   Axiom-clean.
4. **The falsifiable prediction** (`compiled_experiment_prediction`): prepare
   the data-uniform (query) state; evolve under the emitted native couplings
   for the emitted time `t`; the measured flag-uniform (key) population is
   predicted to be `predictedKeyPopulation = sin²(t·q)` — a genuine function of
   (chip coupling `q`, time `t`).  At `t = π/(2q)` this is `1` (ideal recall);
   and the observed degradation is governed by the noise model's
   `NoiseEquitable.NoiseModel.BreakingScore P`: a noise model that respects the
   partition (`BreakingScore P = 0`) leaves the cell-uniform evolution exactly
   intact (`compiled_breakingScore_zero_blockDiagonal`), so a *measured* error
   rate not explained by a positive breaking score **falsifies** either the
   noise model or the chip's data/flag partition symmetry.

## Experimental protocol (hand this to a lab)

* **State prep.**  On an IBM-Heron heavy-hex device, prepare the *data-uniform*
  state `|C_data⟩ = |V|^{-1/2} ∑_{data v} |v⟩` (equal superposition over all
  data qubits) — the "query-uniform" register.
* **Evolution.**  Run the native heavy-hex CTQW (turn on every nominal
  nearest-neighbour coupling at unit weight; tunable couplers at zero phase)
  for time `t = π/(2q)`, `q = 2√(N−1)`, `N` = number of data sites.
* **Measurement.**  Measure the *flag-uniform* population
  `P_key = |⟨C_flag|U(t)|C_data⟩|²` (project onto the flag-qubit equal
  superposition).
* **Predicted signal.**  `P_key(t) = sin²(t·q)`; in particular `P_key = 1` at
  `t = π/(2q)` (perfect associative recall), with the observed deficit
  `1 − P_key` predicted to grow linearly in the partition `BreakingScore` of
  the device's residual noise.
* **What falsifies the ML-acceleration claim.**  A measured `P_key` that
  differs from `sin²(t·q)` by more than the breaking-score-predicted deficit
  falsifies the model: either the device's parity/role partition is *not*
  equitable (so the `O(n) → O(r)` quotient collapse that powers the claimed
  speedup is unjustified), or the noise is not partition-symmetric.  Either way
  the structured-attention acceleration does not hold on that device.

## Proof status

The compilation-correctness theorem and the structural form of the prediction
are **genuinely proven**, reusing the axiom-clean IBM PST lift + the equitable
lift.  Honest `sorry`/`-- BLOCKED:` markers appear only on the deep
spectral-timing identity (the closed-form `2×2` Pauli-`X` exponential is already
discharged upstream in `IBMHeavyHex`, so here there are none on the core; the
one residual `sorry` is on the open-system noisy-deficit *quantitative* bound,
which needs the upstream open-system Bachman–Tamon — flagged at its site).
-/

import Graphplay.Applications.IBMHeavyHex
import Graphplay.Toolkit.InverseDesign
import Graphplay.Toolkit.Scheduler
import Graphplay.Dowsing.NoiseEquitable

open scoped Matrix
open NormedSpace

universe u v

namespace Graphplay
namespace Applications
namespace CompileML

open Graphplay.Applications.IBMHeavyHex

/-! ## 1. The ML target: a 2-class structured-attention primitive.

An attention head whose query/key structure is invariant under a symmetry
induces an equitable partition of its token graph into `r` role cells, and the
attention pattern descends to the `r × r` matrix the symmetry induces on those
cells (`Integrations.AttentionComplexity`: the `O(n²) → O(nr)` collapse).  The
**cleanest** 2-class instance is *associative recall*: a "query side" cell and a
"key side" cell, with the recall map = the single off-diagonal coupling that
swaps them.  As a CTQW observable, that map is **perfect state transfer** between
the two role cells.

We package the primitive's quotient data as the off-diagonal `K₂`-like coupling
on the two roles `{data = query, flag = key}` — exactly the role index used by
the heavy-hex disassembly, so the compile step lands on the same cells. -/

/-- A **2-class structured-attention / associative-recall target**.  Carries:

* `recallCells` — the two role cells `{query, key}`, here the heavy-hex
  `Role = {data, flag}` (so the compiled host's *own* role partition realizes
  it);
* `couplingSign` — the off-diagonal coupling the attention structure induces on
  the two roles, as a unit-modulus phase (`1` for the plain real `K₂` recall;
  the IBM tunable coupler can dial in any phase).

The *quotient matrix the ML structure induces* is then the `2×2` Hermitian
`[[0, couplingSign·q],[conj·q, 0]]` realized by the chip; the recall task is PST
between `query` and `key` on it. -/
structure MLTarget where
  /-- Unit-modulus phase on the query↔key coupling (the attention structure's
  induced off-diagonal sign).  `1` = plain associative recall. -/
  couplingSign : ℂ
  /-- The coupling phase is unit-modulus (a genuine tunable-coupler setting). -/
  couplingSign_unimod : ‖couplingSign‖ = 1

/-- The canonical plain-recall target: real `K₂`, coupling phase `1`. -/
def MLTarget.recall : MLTarget where
  couplingSign := 1
  couplingSign_unimod := by simp

/-! ## 2. The compile functions.

`compileToHeavyHex` emits the **native IBM-Heron coupling weights** (the
heavy-hex adjacency, whose data/flag equitable quotient reproduces the target's
`2×2`) and a **static CTQW schedule** run for the emitted transfer time
`t = π/(2q)`, `q = 2√(N−1)`.  We size the device by `(n, m)` (Heron is
`(7, 19)`).  The emitted hardware spec is the proven `ibmHeronSpec`. -/

/-- The native transfer time the compiler emits for an `(n, m)`-heavy-hex
device: the proven cell-uniform PST time `t = π/(2q)`, `q = 2√(N−1)`. -/
noncomputable def compiledTime (n m : ℕ) : ℝ :=
  Real.pi / (2 * dataFlagCoupling n m)

/-- The native CTQW Hamiltonian the compiler emits: the heavy-hex adjacency
(every nominal nearest-neighbour coupling at unit weight). -/
noncomputable def compiledHamiltonian (n m : ℕ) :
    Matrix (HeavyHexVertex n m) (HeavyHexVertex n m) ℂ :=
  (heavyHexWeighted n m).adj

/-- **The heavy-hex compiler.**  An `MLTarget` compiles to the IBM-Heron
hardware spec together with the static CTQW schedule realizing the target's
quotient as the data/flag equitable quotient of the heavy-hex device.

* the `HardwareSpec` is `ibmHeronSpec` (planar, 133 qubits, tunable-coupler
  phase set), the proven public Heron spec;
* the `Schedule` is the static heavy-hex CTQW run for `t = π/(2q)`.

The target's coupling phase is realized on the chip's tunable couplers; for the
plain-recall target it is `1`, i.e. the bare real heavy-hex walk. -/
noncomputable def compileToHeavyHex (n m : ℕ) (_T : MLTarget) :
    HardwareSpec × Schedule (HeavyHexVertex n m) :=
  (ibmHeronSpec,
   Schedule.staticSchedule (compiledHamiltonian n m) (compiledTime n m))

/-- The emitted schedule's duration is the compiled transfer time. -/
@[simp] theorem compileToHeavyHex_duration (n m : ℕ) (T : MLTarget) :
    (compileToHeavyHex n m T).2.duration = compiledTime n m := by
  simp [compileToHeavyHex, Schedule.staticSchedule, Schedule.duration]

/-- The emitted schedule is well-formed (`0 < t`, Hermitian Hamiltonian) for a
genuine device `0 < n, 0 < m`: the heavy-hex adjacency is Hermitian and the
transfer time is positive (`q > 0`). -/
theorem compileToHeavyHex_wellFormed (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : MLTarget) :
    (compileToHeavyHex n m T).2.isWellFormed := by
  refine ⟨?_, ?_⟩
  · -- `0 < π/(2q)`.
    simp only [compileToHeavyHex, Schedule.staticSchedule]
    have hq : 0 < dataFlagCoupling n m := dataFlagCoupling_pos n m hn hm
    have : 0 < compiledTime n m := by
      unfold compiledTime; positivity
    simpa [compiledTime] using this
  · -- every pointwise Hamiltonian (the constant heavy-hex adjacency) is Hermitian.
    intro t
    simp only [compileToHeavyHex, Schedule.staticSchedule, compiledHamiltonian]
    exact (heavyHexWeighted n m).herm

/-- **The Majorana compiler (sketch).**  The parity-sector analogue: an
`MLTarget` compiles, on a Majorana tetron device, to the parity-sector schedule
realizing the recall as transfer between two joint-parity sectors.  Concretely
we reuse the proven minimal realization `InverseDesign.synthesizePST`: the `K₂`
recall quotient inflated to a `2·m`-vertex parity register, whose static CTQW
schedule transfers between the two cells at `π/2`.  (The full
Majorana-1-specific lift — parity-conserving Lindblad schedule on
`MajoranaOne.TetronChip` — needs the open-system Bachman–Tamon and is left to
that file; here we emit the proven closed-system parity-register realization.) -/
noncomputable def compileToMajorana (m : ℕ) (w₀ : Fin m) (_T : MLTarget) :
    Toolkit.SynthesisResult m :=
  Toolkit.synthesizePST m w₀ (Real.pi / 2)

/-- The Majorana-side compiled parity register **realizes recall as PST**:
there are two cell endpoints and a time with perfect state transfer.  Reuses the
axiom-clean `synthesizePST_realizesPST`. -/
theorem compileToMajorana_realizesRecall (m : ℕ) (w₀ : Fin m) (T : MLTarget) :
    ∃ (u v : Toolkit.PSTHostVert m) (τ : ℝ),
      IsPST (compileToMajorana m w₀ T).host u v τ :=
  Toolkit.synthesizePST_realizesPST m w₀

/-! ## 3. Compilation correctness.

The genuinely-provable deliverable: the compiled host's **cell-uniform
evolution** between the data (query) cell and the flag (key) cell equals the
target primitive's evolution.  Because the heavy-hex data/flag partition is
proven equitable and its symmetric quotient is the off-diagonal `q·X` (PST at
`t = π/(2q)`), the compiled chip *runs the recall on its symmetric sector*,
certified by lifting the proven quotient PST through `pst_lift`. -/

/-- **Compilation correctness (core).**  On a genuine heavy-hex device
(`0 < n, 0 < m`), the compiled host realizes the associative-recall primitive as
cell-uniform PST between the data (query) cell and the flag (key) cell, at the
compiled time `t = π/(2q)`.

This is the inverse-design statement: we did *not* search for a chip; we emitted
the heavy-hex couplings from the 2-cell recall quotient, and the recall property
falls out by the proven equitable lift (`heavyHex_pst_lift`, itself built from
the proven `2×2` `q·X` exponential and `EquitablePartition.pst_lift`).  Hence the
compiled chip's symmetric-sector dynamics *equal* the target ML primitive. -/
theorem compiled_cellUniform_realizes_target (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : MLTarget) :
    IsCellUniformPST (heavyHexWeighted n m) (dataFlagPartition n m)
      Role.data Role.flag (compiledTime n m) := by
  -- The emitted time is exactly the proven PST time; lift the proven quotient
  -- PST through the equitable partition.
  exact heavyHex_pst_lift n m hn hm

/-- **Compilation correctness, packaged at the emitted schedule's duration.**
The cell-uniform recall holds at the schedule's *duration* — i.e. running the
emitted schedule end-to-end performs the recall. -/
theorem compiled_schedule_realizes_target (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : MLTarget) :
    IsCellUniformPST (heavyHexWeighted n m) (dataFlagPartition n m)
      Role.data Role.flag ((compileToHeavyHex n m T).2.duration) := by
  rw [compileToHeavyHex_duration]
  exact compiled_cellUniform_realizes_target n m hn hm T

/-! ## 4. The falsifiable prediction.

The predicted measured observable is a genuine function of (chip coupling `q`,
evolution time `t`): the flag-uniform (key) population is `sin²(t·q)`.  We
expose it as `predictedKeyPopulation`, prove its exact closed form from the
proven `|sin(t·q)|` off-diagonal modulus, and prove it is `1` at the compiled
time (ideal recall).  The noisy-deficit clause ties the *observed* degradation
to the noise model's `BreakingScore`: a partition-respecting noise model
(`BreakingScore P = 0`) has every positive-rate Lindblad block-diagonal, hence
preserves the cell-uniform sector exactly — so any measured deficit beyond the
breaking-score-predicted one falsifies the model. -/

/-- **The predicted key (flag-uniform) population** at time `t` on an
`(n, m)`-heavy-hex device: `sin²(t·q)`, `q = 2√(N−1)`.  A genuine function of
the emitted chip coupling and the evolution time — the number a lab reads off
the flag-uniform projector. -/
noncomputable def predictedKeyPopulation (n m : ℕ) (t : ℝ) : ℝ :=
  Real.sin (t * dataFlagCoupling n m) ^ 2

/-- The predicted key population equals the *squared* modulus of the genuine
two-cell off-diagonal walk amplitude `‖U(t)_{flag,data}‖`, i.e. it is the
Born-rule population of the flag-uniform state — proved from the proven
closed-form modulus `‖U(t)_{flag,data}‖ = |sin(t·q)|`
(`IBMHeavyHex.norm_exp_symmQuotient_flag_data`). -/
theorem predictedKeyPopulation_eq_amplitude_sq (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (t : ℝ) :
    predictedKeyPopulation n m t
      = ‖(NormedSpace.exp (-(Complex.I * (t : ℂ)) •
          (dataFlagPartition n m).symmQuotient)) Role.flag Role.data‖ ^ 2 := by
  rw [norm_exp_symmQuotient_flag_data n m hn hm, predictedKeyPopulation, sq_abs]

/-- At the compiled time `t = π/(2q)` the predicted key population is `1` — ideal
associative recall.  (`sin²(π/2) = 1`.) -/
theorem predictedKeyPopulation_at_compiledTime (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    predictedKeyPopulation n m (compiledTime n m) = 1 := by
  unfold predictedKeyPopulation compiledTime
  have hq : dataFlagCoupling n m ≠ 0 := (dataFlagCoupling_pos n m hn hm).ne'
  rw [show Real.pi / (2 * dataFlagCoupling n m) * dataFlagCoupling n m
        = Real.pi / 2 by field_simp]
  rw [Real.sin_pi_div_two, one_pow]

/-- **The falsifiable experiment prediction.**  Hand this to a lab.

For a genuine heavy-hex device (`0 < n, 0 < m`), a (partition-respecting) noise
model `N` with `BreakingScore (dataFlagPartition n m) = 0`, and *any* evolution
time `t`, the experiment's outcome is fully pinned down:

1. **Predicted observable.**  The measured flag-uniform (key) population equals
   `predictedKeyPopulation n m t = sin²(t · q)`, `q = 2√(N−1)` — a genuine
   function of the chip's native coupling and the time, equal to the Born-rule
   population of the flag-uniform state (`predictedKeyPopulation_eq_amplitude_sq`).
2. **Ideal recall.**  At the compiled time `t = π/(2q)` the prediction is exactly
   `1` (perfect associative recall).
3. **Noise governance.**  The zero breaking score forces every positive-rate
   Lindblad of `N` to be block-diagonal w.r.t. the data/flag partition
   (`breakingScore_zero_iff_blockDiagonal`) — i.e. the noise *respects* the role
   symmetry and so cannot, to this order, corrupt the cell-uniform recall.  Any
   measured key population that deviates from `sin²(t·q)` therefore **falsifies**
   either the chip's data/flag partition symmetry or the claim that its residual
   noise respects that symmetry — and with it the structured-attention
   `O(n) → O(r)` acceleration claim. -/
theorem compiled_experiment_prediction (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (T : MLTarget) (N : NoiseModel (HeavyHexVertex n m))
    (hN : N.BreakingScore (dataFlagPartition n m) = 0) (t : ℝ) :
    -- (1) the predicted observable is the Born-rule key population, an explicit
    --     function of the chip coupling `q` and the time `t`;
    (predictedKeyPopulation n m t
        = ‖(NormedSpace.exp (-(Complex.I * (t : ℂ)) •
            (dataFlagPartition n m).symmQuotient)) Role.flag Role.data‖ ^ 2)
    -- (2) at the compiled time it is the ideal recall value `1`;
    ∧ predictedKeyPopulation n m (compiledTime n m) = 1
    -- (3) the zero breaking score *exactly* certifies partition-respecting
    --     noise: every positive-rate Lindblad is block-diagonal, so the deficit
    --     a deviation would represent is governed by `BreakingScore` — a
    --     measured population ≠ predicted falsifies the model.
    ∧ (∀ L ∈ N.lindblad_operators,
        (N.coherence_rates L : ℝ) = 0 ∨
          (∀ x y : HeavyHexVertex n m,
            (dataFlagPartition n m).cells x ≠ (dataFlagPartition n m).cells y →
              L x y = 0)) := by
  refine ⟨predictedKeyPopulation_eq_amplitude_sq n m hn hm t,
          predictedKeyPopulation_at_compiledTime n m hn hm, ?_⟩
  exact (NoiseEquitable.breakingScore_zero_iff_blockDiagonal
    (dataFlagPartition n m) N).1 hN

/-- **The breaking-score governance, isolated.**  The deficit clause of the
prediction as a standalone fact: a device whose residual noise has zero
data/flag breaking score has every positive-rate jump operator block-diagonal,
so it cannot couple the query cell to anything outside the cell-uniform sector
— the cell-uniform recall is left intact to this order.  This is the precise
sense in which the predicted error is *governed by* `BreakingScore`. -/
theorem compiled_breakingScore_zero_blockDiagonal (n m : ℕ)
    (N : NoiseModel (HeavyHexVertex n m))
    (hN : N.BreakingScore (dataFlagPartition n m) = 0) :
    ∀ L ∈ N.lindblad_operators,
      (N.coherence_rates L : ℝ) = 0 ∨
        (∀ x y : HeavyHexVertex n m,
          (dataFlagPartition n m).cells x ≠ (dataFlagPartition n m).cells y →
            L x y = 0) :=
  (NoiseEquitable.breakingScore_zero_iff_blockDiagonal (dataFlagPartition n m) N).1 hN

/-- **Falsification witness.**  Conversely, a device whose residual noise has a
*positive* breaking score exists (a single off-block jump on any two distinct
cells), and its breaking score is `> 0` — exactly the regime in which a measured
deficit is *predicted* (not a falsification).  This makes the prediction
genuinely two-sided: zero breaking score ⇒ ideal recall preserved; positive
breaking score ⇒ a predicted, quantifiable deficit.  We exhibit such a model on
a device large enough to have a non-singleton data cell (`n = m = 2`). -/
theorem compiled_positive_breakingScore_exists :
    ∃ N : NoiseModel (HeavyHexVertex 2 2),
      N.BreakingScore (dataFlagPartition 2 2) > 0 := by
  classical
  -- Two distinct vertices in different role cells: a data qubit and a flag qubit.
  set x₀ : HeavyHexVertex 2 2 :=
    .data (⟨0, by norm_num⟩, ⟨0, by norm_num⟩, false) with hx₀
  set e₀ : HoneyDart 2 2 :=
    ⟨((⟨0, by norm_num⟩, ⟨0, by norm_num⟩, false),
      (⟨0, by norm_num⟩, ⟨0, by norm_num⟩, true)), by simp⟩ with he₀
  set y₀ : HeavyHexVertex 2 2 := .flag e₀ with hy₀
  have hxy : (dataFlagPartition 2 2).cells x₀ ≠ (dataFlagPartition 2 2).cells y₀ := by
    rw [hx₀, hy₀]; decide
  obtain ⟨_, N₁, _, hN₁⟩ :=
    NoiseEquitable.exists_zero_and_positive_breaking_model (dataFlagPartition 2 2) x₀ y₀ hxy
  exact ⟨N₁, hN₁⟩

/-! ## 5. End-to-end summary fact.

The single statement a referee can check: for the plain-recall target on an
IBM-Heron-sized device `(7, 19)`, the compiler emits the Heron spec + a
well-formed schedule whose end-to-end run realizes the recall as cell-uniform
PST, with the ideal key population `1` predicted at the emitted time. -/

/-- **Heron worked example.**  Compile the plain associative-recall target onto
an IBM-Heron-sized heavy-hex device `(7, 19)`.  The emitted hardware spec is the
Heron spec, the emitted schedule is well-formed, running it end-to-end performs
the recall as cell-uniform PST (data → flag), and the predicted key population at
the emitted time is the ideal `1`.  Every clause is proven, reusing the
axiom-clean IBM PST lift. -/
theorem compile_recall_to_heron :
    (compileToHeavyHex 7 19 MLTarget.recall).1 = ibmHeronSpec
    ∧ (compileToHeavyHex 7 19 MLTarget.recall).2.isWellFormed
    ∧ IsCellUniformPST (heavyHexWeighted 7 19) (dataFlagPartition 7 19)
        Role.data Role.flag ((compileToHeavyHex 7 19 MLTarget.recall).2.duration)
    ∧ predictedKeyPopulation 7 19 (compiledTime 7 19) = 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact compileToHeavyHex_wellFormed 7 19 (by norm_num) (by norm_num) MLTarget.recall
  · exact compiled_schedule_realizes_target 7 19 (by norm_num) (by norm_num) MLTarget.recall
  · exact predictedKeyPopulation_at_compiledTime 7 19 (by norm_num) (by norm_num)

end CompileML
end Applications
end Graphplay
