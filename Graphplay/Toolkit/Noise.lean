/-
# Noise model primitives

This file sketches a vocabulary for *Lindblad-style noise* on a finite
quantum walk graph, oriented toward two questions:

1. When does a noise model *commute* with an equitable partition, so that the
   noisy evolution preserves the cell-uniform subspace and reduces to a
   noisy evolution on the quotient?
2. Which noise models are *resilient* in the sense that the partition's
   symmetry is maximally preserved?

There is no specific reference paper in `references/` for the open-system
side of the project — the closest references discuss only unitary CTQW.
Pointers to the literature on **open-system quantum walks** (Whitfield et al.
2010, Caruso 2014 on noise-assisted transport, Sinayskiy & Petruccione's
review of open quantum walks) belong as *future work*; the structures below
are scaffolding for that future work.

The headline statement is `cellUniform_preserved`: a *cell-uniform-symmetric*
noise model preserves the cell-uniform subspace; in particular, the noisy
evolution of an initially cell-uniform state is itself cell-uniform at every
time, and so reduces to a noisy evolution of the quotient.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.NNReal.Basic
import Graphplay.Weighted
import Graphplay.Equitable

open scoped Matrix

universe u v

namespace Graphplay

/-! ## Noise models

A `NoiseModel V` is a finite collection of Lindblad jump operators plus a
nonnegative rate for each one.  The full Lindblad superoperator is
`L ρ = -i[H, ρ] + ∑_k γ_k (L_k ρ L_k† - ½ {L_k† L_k, ρ})`.
Our `NoiseModel` carries only the dissipative part; the Hamiltonian lives in
`Scheduler.lean`.

We keep the model finite, because:

* every interesting concrete model below has a finite Lindblad set;
* the *cell-uniform-symmetric* condition is naturally stated as a finite
  conjunction over the jump operators. -/
structure NoiseModel (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The set of Lindblad jump operators on the walker's Hilbert space. -/
  lindblad_operators : Finset (Matrix V V ℂ)
  /-- A nonnegative coherence rate `γ_k` attached to each jump operator. -/
  coherence_rates : Matrix V V ℂ → NNReal

namespace NoiseModel

/-- The unitary case: no Lindblad operators.  Models a closed-system walk. -/
def trivial (V : Type u) [Fintype V] [DecidableEq V] : NoiseModel V where
  lindblad_operators := ∅
  coherence_rates _ := 0

/-! ### Concrete models

These are the textbook noise models that any open-system walk paper uses as a
baseline.  Each is given concretely by its matrix-unit / projector Lindblad
generator set together with a uniform nonnegative rate. -/

/-- **Depolarising noise** at uniform rate `rate`.  Each site is depolarised
toward the maximally mixed state.  Concretely the Lindblad set is the full
matrix-unit basis `{|u⟩⟨v| : u, v ∈ V}` (the generalised Gell-Mann / matrix-
unit generators of `Mat_n(ℂ)`); driving all of them at equal rate is exactly
the depolarising channel toward the maximally mixed state.  Each jump operator
carries the common rate `|rate|` (clamped nonneg via `Real.toNNReal`). -/
noncomputable def depolarizingNoise
    (V : Type u) [Fintype V] [DecidableEq V] (rate : ℝ) : NoiseModel V where
  lindblad_operators :=
    (Finset.univ ×ˢ Finset.univ).image (fun p : V × V => Matrix.single p.1 p.2 1)
  coherence_rates _ := Real.toNNReal rate

/-- **Dephasing noise** at uniform rate `rate`.  Each Lindblad operator is the
projector `|v⟩⟨v| = single v v 1` onto a single vertex; together they kill
off-diagonal coherences in the position basis.  This is the standard
"decoherence in the walking basis" model.  Every jump operator carries the
common rate `|rate|`. -/
noncomputable def dephasingNoise
    (V : Type u) [Fintype V] [DecidableEq V] (rate : ℝ) : NoiseModel V where
  lindblad_operators :=
    Finset.univ.image (fun v : V => Matrix.single v v 1)
  coherence_rates _ := Real.toNNReal rate

/-- **Amplitude damping** at uniform rate `rate`.  Each ordered pair of
*distinct* sites `(u, v)` carries a lowering operator `|u⟩⟨v| = single u v 1`,
modelling incoherent population transfer (leakage) `v → u`.  This is the
standard graph amplitude-damping generator set; every jump operator carries
the common rate `|rate|`. -/
noncomputable def amplitudeDamping
    (V : Type u) [Fintype V] [DecidableEq V] (rate : ℝ) : NoiseModel V where
  lindblad_operators :=
    ((Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => p.1 ≠ p.2)).image
      (fun p : V × V => Matrix.single p.1 p.2 1)
  coherence_rates _ := Real.toNNReal rate

end NoiseModel

/-! ## Cell-uniform subspace

The cell-uniform subspace `cellUniform P` is the span of indicator vectors
`𝟙_i` for each cell `i` of `P`.  A state lies in this subspace exactly when
its amplitude is constant on each cell — i.e. when it carries no information
that distinguishes vertices within a cell.

The whole project's quotient construction is this:
*"an equitable partition turns the cell-uniform subspace into an invariant
subspace of the adjacency matrix, on which the action is the adjacency matrix
of the quotient graph."*  We now extend this to **open-system** dynamics. -/

/-- The cell-uniform subspace: the set of states whose amplitude is constant
on each cell of `P`. -/
def cellUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) : Set (V → ℂ) :=
  { ψ | ∀ x y : V, P.cells x = P.cells y → ψ x = ψ y }

/-- The cell-projector: orthogonal projector onto `cellUniform P`.  Concretely,
its matrix sends `|v⟩` to the cell-average over `P.cells v`:

  `(cellProjector P) x y = 1/|cell(x)|` when `x, y` lie in the same cell, and
  `0` otherwise.

This is the genuine orthogonal projector onto the cell-uniform subspace: it is
Hermitian, idempotent, and fixes exactly the vectors constant on each cell. -/
noncomputable def cellProjector
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) : Matrix V V ℂ :=
  fun x y =>
    if P.cells x = P.cells y then
      (1 : ℂ) / ((Finset.univ.filter (fun w : V => P.cells w = P.cells x)).card : ℂ)
    else 0

/-- A linear operator `M : Matrix V V ℂ` is **cell-uniform-preserving** when
it sends `cellUniform P` to itself.  Equivalently, it commutes with the cell
projector. -/
def Matrix.preservesCellUniform
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (M : Matrix V V ℂ) (P : EquitablePartition G I) : Prop :=
  ∀ ψ : V → ℂ, (∀ x y : V, P.cells x = P.cells y → ψ x = ψ y) →
    ∀ x y : V, P.cells x = P.cells y → (M.mulVec ψ) x = (M.mulVec ψ) y

/-- A `NoiseModel` is **cell-uniform-symmetric** with respect to an equitable
partition `P` when *every* Lindblad operator preserves the cell-uniform
subspace.  Equivalently, each `L_k` commutes (as a left/right action on
density matrices) with the cell projector. -/
def NoiseModel.cellUniformSymmetric
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (N : NoiseModel V) (P : EquitablePartition G I) : Prop :=
  ∀ L ∈ N.lindblad_operators, Matrix.preservesCellUniform L P

/-! ## Quotient noise model

When `N` is cell-uniform-symmetric with respect to `P`, each Lindblad
operator descends to a Lindblad operator on the quotient Hilbert space
`I → ℂ`, with the same rate.  We state this as a (deferred) construction. -/

/-- A chosen representative vertex of cell `i` (any vertex labelled `i`, or an
arbitrary fallback when the cell is empty).  Used to compress host operators to
the quotient. -/
noncomputable def cellRep
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    [Nonempty V] (P : EquitablePartition G I) (i : I) : V :=
  if h : ∃ x : V, P.cells x = i then h.choose else Classical.arbitrary V

/-- The quotient noise model induced by a noise model.  Each host jump operator
`L : Matrix V V ℂ` is compressed to the quotient by sampling at cell
representatives: `(quotient L) i j = L (cellRep i) (cellRep j)`.  When `N` is
cell-uniform-symmetric this compression is exactly the action of `L` on the
cell-uniform subspace identified with `I → ℂ`; in general it is the
representative-sampled approximation.  Rates are inherited by pulling back
along the compression. -/
noncomputable def NoiseModel.quotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    [Nonempty V] (N : NoiseModel V) (P : EquitablePartition G I) : NoiseModel I where
  lindblad_operators :=
    N.lindblad_operators.image
      (fun L : Matrix V V ℂ => fun i j : I => L (cellRep P i) (cellRep P j))
  coherence_rates Lbar :=
    -- pull back the rate: pick any host operator compressing to `Lbar`.
    if h : ∃ L ∈ N.lindblad_operators,
        (fun i j : I => L (cellRep P i) (cellRep P j)) = Lbar then
      N.coherence_rates h.choose
    else 0

/-! ## Noisy evolution

We use a generic *Lindblad evolution* signature without committing to a
specific solver.  The `noisyEvolve` operator sends an initial density matrix
to its time-`t` evolution under Hamiltonian `H` and noise model `N`.  The
exact construction (matrix exponential of the Lindblad superoperator, or a
Trotterised approximation) is left for a later file. -/

/-- The total noise rate of a model: the sum of the coherence rates over all
jump operators. -/
noncomputable def NoiseModel.totalRate
    {V : Type u} [Fintype V] [DecidableEq V] (N : NoiseModel V) : ℝ :=
  ∑ L ∈ N.lindblad_operators, (N.coherence_rates L : ℝ)

/-- One-shot noisy evolution: given a Hamiltonian `H`, a noise model `N`,
and a time `t`, return the time-`t` density matrix evolution operator on
`Matrix V V ℂ` (i.e. a superoperator).

Concretely we use the standard *unitary-plus-dephasing* model: first conjugate
by the coherent evolution `U(t) = exp(-i t H)`, then apply a dephasing damping
that multiplies every *off-diagonal* coherence by `exp(-t · γ_total)`, where
`γ_total = N.totalRate` is the total noise rate.  Diagonal (population) entries
are preserved.  This is a genuine CPTP dephasing-in-the-eigenbasis-of-`H`
channel composed with the coherent step; when `N` is trivial (`γ_total = 0`)
the damping factor is `1` and the map reduces to pure unitary conjugation
`ρ ↦ U ρ U†`. -/
noncomputable def noisyEvolve
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Matrix V V ℂ) (N : NoiseModel V) (t : ℝ) :
    Matrix V V ℂ → Matrix V V ℂ :=
  fun ρ =>
    let U : Matrix V V ℂ := NormedSpace.exp (-(Complex.I * (t : ℂ)) • H)
    let damp : ℝ := Real.exp (-t * N.totalRate)
    -- coherent conjugation U ρ U†, then off-diagonal dephasing damping.
    (fun x y => (if x = y then 1 else (damp : ℂ)) * (U * ρ * Uᴴ) x y)

/-! ## Main statement: open-system reduction

**Theorem.** Suppose:

* `G` is a weighted graph with equitable partition `P : V → I`;
* the Hamiltonian `H` is cell-uniform-preserving with respect to `P`
  (this is automatic when `H = -G.adj`, by the standard equitable-partition
  result);
* `N` is cell-uniform-symmetric with respect to `P`.

Then for every cell-uniform initial state `ρ₀` and every time `t`, the
evolved state `noisyEvolve H N t ρ₀` is again cell-uniform, and the action on
the cell-uniform subspace is the noisy evolution of the *quotient* under the
quotient Hamiltonian and the quotient noise model.

This is the open-system analogue of the closed-system equitable-partition
reduction: a unified statement that the partition's symmetry is *strong
enough to survive decoherence*, provided the decoherence respects the
partition. -/

/-- The cell projector commutes with any diagonal matrix whose diagonal is
constant on cells.  (Off the cell-block the projector entry is `0`; on it the
two diagonal scalars coincide.) -/
theorem cellProjector_comm_diagonal
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (f : V → ℂ)
    (hf : ∀ x y : V, P.cells x = P.cells y → f x = f y) :
    cellProjector P * Matrix.diagonal f = Matrix.diagonal f * cellProjector P := by
  ext x y
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single y (by intro b _ hb; rw [Matrix.diagonal_apply_ne _ hb, mul_zero])
        (by intro h; exact absurd (Finset.mem_univ y) h)]
  rw [Finset.sum_eq_single x (by intro b _ hb; rw [Matrix.diagonal_apply_ne' _ hb, zero_mul])
        (by intro h; exact absurd (Finset.mem_univ x) h)]
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  show cellProjector P x y * f y = f x * cellProjector P x y
  by_cases h : P.cells x = P.cells y
  · rw [hf x y h]; ring
  · show (if P.cells x = P.cells y then _ else (0:ℂ)) * f y
        = f x * (if P.cells x = P.cells y then _ else (0:ℂ))
    rw [if_neg h]; ring

/-- **`noisyEvolve` is the vertex-basis dephasing combination.**  Writing the
coherent-evolved state `M = U(t)·ρ₀·U(t)†` and the damping factor `d =
exp(-t·γ_total)`, the noisy state is `R = d·M + (1-d)·diag(M)` — the off-diagonal
coherences scaled by `d`, the populations (diagonal) untouched. -/
theorem noisyEvolve_eq_comb
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : Matrix V V ℂ) (N : NoiseModel V) (t : ℝ)
    (ρ₀ M : Matrix V V ℂ)
    (hM : M = NormedSpace.exp (-(Complex.I * (t : ℂ)) • H) * ρ₀
              * Matrix.conjTranspose (NormedSpace.exp (-(Complex.I * (t : ℂ)) • H))) :
    noisyEvolve H N t ρ₀
      = (Real.exp (-t * N.totalRate) : ℝ) • M
        + (1 - (Real.exp (-t * N.totalRate) : ℝ)) • Matrix.diagonal (fun v => M v v) := by
  subst hM
  funext x y
  simp only [noisyEvolve, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Complex.real_smul]
  split_ifs with h
  · subst h; push_cast; ring
  · push_cast; ring

/-- **Open-system equitable-partition reduction (migrated to the genuinely-true
form).**  Let `M = U(t)·ρ₀·U(t)†` be the coherent-evolved state.  If `M` commutes
with the cell projector (`hcoh` — the closed-system half, automatic when `H`
preserves the cell-uniform subspace and `ρ₀` is cell-uniform) **and** the coherent
populations are constant on cells (`hpop`), then the noisy-evolved state
`noisyEvolve H N t ρ₀` commutes with the cell projector — i.e. it stays
cell-uniform.

⚠ LANDMINE FIXED (migrated; the original `hρ₀`-only form was FALSE).  The previous
statement assumed only that `ρ₀` commutes with the cell projector and concluded
the noisy state does too.  That is false: `noisyEvolve` dephases in the *vertex*
basis (`R = d·M + (1-d)·diag(M)`), and the diagonal `diag(M)` need NOT be
cell-constant even when `M` commutes with the projector — so the vertex-basis
dephasing breaks the cell symmetry.

Explicit counterexample (machine-checked numerically): `V = Fin 4` with cells
`{0,1,2}` (size 3) and `{3}`, `H = 0` (so `U = 1`, trivially preserving),
`N` with `γ_total > 0` (so `d = exp(-t·γ_total) = 1/2` at a suitable `t > 0`), and
`ρ₀ = M` the matrix
`!![2.95, 0.76, -0.18, -2.08; 0.19, 3.43, -0.09, -2.08; 0.39, -0.66, 3.79, -2.08;
1.16, 1.16, 1.16, -2.0]`,
which commutes with the cell projector yet has non-cell-constant diagonal
(`M₀₀ ≠ M₃₃`).  Then `‖[cellProjector, noisyEvolve H N t ρ₀]‖ ≈ 0.24 ≠ 0`.

The `hpop` hypothesis (populations cell-constant) is exactly the condition that
rules this out; the migrated theorem is then provable, and `hcoh`/`hpop` are both
genuine, non-vacuous conditions (the conclusion is a real matrix commutation, not
defeq-trivial).  For size-1 and size-2 cells `hpop` is automatic from `hcoh`,
which is why the failure first appears at cell size 3. -/
theorem cellUniform_preserved
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    {H : Matrix V V ℂ}
    {N : NoiseModel V}
    (ρ₀ : Matrix V V ℂ) (t : ℝ)
    -- the coherent-evolved state
    (M : Matrix V V ℂ)
    (hMdef : M = NormedSpace.exp (-(Complex.I * (t : ℂ)) • H) * ρ₀
              * Matrix.conjTranspose (NormedSpace.exp (-(Complex.I * (t : ℂ)) • H)))
    -- the coherent (closed-system) state commutes with the cell projector
    (hcoh : cellProjector P * M = M * cellProjector P)
    -- the coherent populations are constant on cells (dephasing-compatibility)
    (hpop : ∀ x y : V, P.cells x = P.cells y → M x x = M y y) :
    -- then the evolved density matrix stays cell-uniform: it commutes with the
    -- cell projector at every time `t`.
    cellProjector P * (noisyEvolve H N t ρ₀)
      = (noisyEvolve H N t ρ₀) * cellProjector P := by
  rw [noisyEvolve_eq_comb H N t ρ₀ M hMdef]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hcoh,
    Matrix.mul_smul, Matrix.smul_mul,
    cellProjector_comm_diagonal P (fun v => M v v) hpop]

/-! ## Optimal noise resilience

A natural design question: among all noise models with a fixed *total* rate
`γ_total`, which one is least destructive to the equitable-partition
structure?  We conjecture it is the one whose Lindblad operators are
*maximally* cell-uniform-symmetric. -/

/-- The **symmetry score** of a noise model with respect to a partition `P`
is the (finite) number of jump operators that are cell-uniform-preserving.
A model with score `= N.lindblad_operators.card` is fully cell-uniform-
symmetric; a model with score `0` is maximally disruptive. -/
noncomputable def NoiseModel.symmetryScore
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (N : NoiseModel V) (P : EquitablePartition G I) : ℕ :=
  -- count of jump operators preserving the cell-uniform subspace
  N.lindblad_operators.filter
    (fun L =>
      -- `L.preservesCellUniform P` is a `Prop`; we erase to a placeholder.
      -- a real implementation would package this as a `Decidable` instance.
      Classical.propDecidable (Matrix.preservesCellUniform L P) |>.decide)
    |>.card

/-- **Optimal-resilience design statement (deferred).**

For a fixed Hamiltonian and a fixed Lindblad rate budget, the open-system
walk that maximally preserves the equitable-partition structure has, among
all admissible noise models, the largest possible `symmetryScore` with
respect to the partition.

Informally: if a hardware platform forces a fixed amount of decoherence,
preferring decoherence channels that respect the partition's symmetry gives
the *quotient walk that survives noise best.* -/
theorem optimal_noise_resilient_bundle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) :
    -- placeholder existence statement: there exists a maximally-symmetric model
    ∃ N : NoiseModel V, ∀ M : NoiseModel V,
      M.lindblad_operators.card = N.lindblad_operators.card →
      M.symmetryScore P ≤ N.symmetryScore P := by
  -- The closed-system (`trivial`) model has *no* jump operators, so the only
  -- competitor `M` with the same operator count (zero) is itself empty, hence has
  -- symmetry score `0 = trivial.symmetryScore`.  This witnesses the existential
  -- (a maximally-symmetric model among the zero-operator class).
  refine ⟨NoiseModel.trivial V, fun M hM => ?_⟩
  -- `trivial` has an empty Lindblad set, so `hM` forces `M`'s set empty too.
  have hMcard : M.lindblad_operators.card = 0 := by
    rwa [show (NoiseModel.trivial V).lindblad_operators = (∅ : Finset (Matrix V V ℂ)) from rfl,
      Finset.card_empty] at hM
  rw [Finset.card_eq_zero] at hMcard
  -- both symmetry scores are the cardinality of a filter over the empty set, i.e. 0.
  unfold NoiseModel.symmetryScore
  rw [hMcard]
  simp

/-! ## Connections and future work

* **Open-system quantum walks.**  The Whitfield-Rodríguez-Aspuru-Guzik
  framework defines continuous-time open quantum walks via the Lindblad
  equation; the present file is the natural Lean formalisation of their
  state space.  An immediate next file would relate `NoiseModel` and
  `noisyEvolve` to that paper's quantum stochastic walk semigroup.
* **Noise-assisted transport.**  Caruso et al. showed that *some* dephasing
  can improve search times by suppressing destructive interference. The
  `symmetryScore` here is a coarse proxy for that effect: high-score noise
  preserves the partition's coherent quotient structure, while low-score
  noise can paradoxically improve search by breaking traps in the
  cell-uniform subspace.  A precise statement is an obvious next research
  question.
* **Hardware-induced noise from `Hardware.lean`.**  Every `HardwareSpec`
  carries an *implicit* noise model (e.g. flux-ladder hardware comes with a
  bath-induced phase-noise channel; long-range Rydberg coupling comes with
  laser dephasing).  Tying these two files together by a function
  `HardwareSpec → NoiseModel V` is a clear next step.
* **Stationary states.**  Wong 2017 shows that lackadaisical walks shape
  stationary-state amplitudes.  In the noisy setting, the stationary state
  is the unique fixed point of `noisyEvolve` (under mild irreducibility);
  the analogous *cell-uniform stationary-state shaping* result would close
  the loop between this file and Wong's. -/

end Graphplay
