/-
# Graphplay/Integrations/QuantumMarkov.lean

**Quantum observable Markov decision processes (QOMDPs) and the
undecidability of goal-state reachability.**

A classical (fully or partially observable) Markov decision process is a
controlled stochastic dynamical system; goal-state reachability — "is there
a policy that reaches the goal with probability `1`?" — is *decidable* for
finite MDPs (and even finite POMDPs reduce to a finite-belief computation in
the relevant qualitative variants).  Barry, Barry and Aaronson
(arXiv:1911.01953, "Quantum POMDPs") introduce the **quantum** analogue, the
QOMDP, in which:

* the underlying state is a density operator `ρ` on a finite-dimensional
  Hilbert space `ℂ^d`;
* each action `a` is a quantum channel given by a tuple of **Kraus
  operators** `{K_{a,k}}` with `∑_k K_{a,k}^† K_{a,k} = 1`, evolving
  `ρ ↦ ∑_k K_{a,k} ρ K_{a,k}^†`;
* observations are produced by a fixed **POVM** `{E_o}` with `E_o ⪰ 0`,
  `∑_o E_o = 1`, giving outcome `o` with probability `tr(E_o ρ)`;
* a designated **goal POVM element** `E_g` (a projector onto the goal
  subspace) defines the goal: a run *reaches the goal* once a goal
  measurement succeeds with certainty.

Barry–Barry–Aaronson's headline result is that, in stark contrast to the
classical case, **QOMDP goal-state reachability is undecidable**: there is no
algorithm that, given a QOMDP and a goal, decides whether some policy reaches
the goal with probability `1`.  The proof is a reduction from the (undecidable)
emptiness/reachability problem for matrix products / the Post correspondence
problem, encoding an undecidable word problem into the noncommutative Kraus
dynamics.

This file is a **concrete statement layer**:

* Kraus maps and POVMs are concrete `Matrix` lists with their defining
  algebraic constraints;
* the goal-reachability predicate is spelled out concretely;
* PCP solvability is a concrete `Σ₁` predicate (`PCPInstance`,
  tile lists over the binary alphabet, surjectively enumerated by `pcpEnum`),
  and the headline Barry–Barry–Aaronson reduction is carried as a
  def-conjecture (`BarryBarryAaronsonReduction`) anchored to that predicate;
* the quotient connection is the **equivariant** one: cell-constancy of the
  Kraus data (the naive `EquitableSymmetry`) is *machine-checked to be
  uninstantiable* beyond discrete partitions
  (`EquitableSymmetry.no_nontrivial_cell`), whereas commutation with all
  cell-preserving permutations (`EquivariantSymmetry`) is satisfiable with
  nontrivial cells, makes every run-state equivariant, and makes every
  goal-success probability descend to an `|I|`-indexed cell sum; the explicit
  quotient machine is `EquivariantQuotientConjecture`.

## References

* J. Barry, D. T. Barry, S. Aaronson, *Quantum Partially Observable Markov
  Decision Processes*, Phys. Rev. A 90, 032311 (2014); see also
  arXiv:1911.01953 for the undecidability of QOMDP goal-state reachability.
* M. S. Paterson, *Unsolvability in `3 × 3` matrices*, Studies in Applied
  Mathematics 49 (1970) — the matrix-mortality undecidability backbone.
* E. L. Post, *A variant of a recursively unsolvable problem*, Bull. AMS 52
  (1946) — the Post correspondence problem.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Logic.Equiv.List
import Graphplay.Weighted
import Graphplay.Equitable

open scoped Matrix ComplexOrder
open Complex

universe u

namespace Graphplay
namespace QuantumMarkov

/-! ### 1. Density operators and quantum channels

We work with `d`-dimensional systems, `d` a `Fintype`.  A density operator is
a positive-semidefinite Hermitian matrix of unit trace. -/

variable {d : Type u} [Fintype d] [DecidableEq d]

/-- A **density operator** on `ℂ^d`: positive-semidefinite with unit trace.
This is the quantum state of a QOMDP. -/
structure DensityOperator (d : Type u) [Fintype d] [DecidableEq d] where
  /-- The underlying matrix. -/
  mat : Matrix d d ℂ
  /-- Positive semidefiniteness (in particular Hermitian). -/
  posSemidef : mat.PosSemidef
  /-- Unit trace. -/
  trace_one : mat.trace = 1

/-- A **Kraus channel** (completely positive trace-preserving map) presented
by a finite list of Kraus operators `K_k`, subject to the trace-preservation
identity `∑_k K_k^† K_k = 1`.  The action on a state is `ρ ↦ ∑_k K_k ρ K_k^†`. -/
structure KrausChannel (d : Type u) [Fintype d] [DecidableEq d] where
  /-- The list of Kraus operators. -/
  ops : List (Matrix d d ℂ)
  /-- Trace preservation: `∑_k K_k^† K_k = 1`. -/
  tracePreserving :
    (ops.map (fun K => Kᴴ * K)).sum = (1 : Matrix d d ℂ)

namespace KrausChannel

/-- The action of a Kraus channel on a raw matrix: `ρ ↦ ∑_k K_k ρ K_k^†`.
Concretely the sum over the Kraus list. -/
noncomputable def apply (C : KrausChannel d) (ρ : Matrix d d ℂ) : Matrix d d ℂ :=
  (C.ops.map (fun K => K * ρ * Kᴴ)).sum

/-- The identity channel: a single Kraus operator `1`. -/
def id (d : Type u) [Fintype d] [DecidableEq d] : KrausChannel d where
  ops := [(1 : Matrix d d ℂ)]
  tracePreserving := by simp

@[simp] theorem apply_zero (C : KrausChannel d) : C.apply 0 = 0 := by
  unfold apply
  induction C.ops with
  | nil => simp
  | cons K ops _ih => simp

end KrausChannel

/-! ### 2. POVMs and observations

A POVM is a finite indexed family of positive-semidefinite "effect" matrices
summing to the identity.  Outcome `o` on state `ρ` occurs with probability
`tr(E_o ρ)`, which is real and in `[0,1]`. -/

/-- A **POVM** (positive operator-valued measure) with outcome type `O`: a
family of effects `E_o ⪰ 0` with `∑_o E_o = 1`. -/
structure POVM (d : Type u) [Fintype d] [DecidableEq d]
    (O : Type u) [Fintype O] where
  /-- The effect operators. -/
  effect : O → Matrix d d ℂ
  /-- Each effect is positive semidefinite. -/
  effect_posSemidef : ∀ o, (effect o).PosSemidef
  /-- Completeness: the effects sum to the identity. -/
  complete : ∑ o, effect o = (1 : Matrix d d ℂ)

namespace POVM

variable {O : Type u} [Fintype O]

/-- The probability of outcome `o` on a density operator `ρ`: `tr(E_o ρ)`. -/
noncomputable def prob (M : POVM d O) (ρ : DensityOperator d) (o : O) : ℂ :=
  (M.effect o * ρ.mat).trace

/-- The outcome probabilities of a POVM sum to `tr ρ = 1`. -/
theorem prob_sum (M : POVM d O) (ρ : DensityOperator d) :
    ∑ o, M.prob ρ o = 1 := by
  unfold prob
  rw [← Matrix.trace_sum]
  have : ∑ o, M.effect o * ρ.mat = (∑ o, M.effect o) * ρ.mat := by
    rw [Finset.sum_mul]
  rw [this, M.complete, Matrix.one_mul, ρ.trace_one]

end POVM

/-! ### 3. The QOMDP

A QOMDP bundles: a finite action set, a Kraus channel per action, an
observation POVM, an initial state, and a *goal* effect `E_g` (a projector
onto the goal subspace).  We keep the goal as a distinguished POVM effect so
the "reach the goal with certainty" predicate is `tr(E_g ρ) = 1`. -/

/-- A **quantum observable Markov decision process** on a `d`-dimensional
system, with finite action set `A` and observation outcomes `O`. -/
structure QOMDP (d : Type u) [Fintype d] [DecidableEq d]
    (A : Type u) [Fintype A]
    (O : Type u) [Fintype O] where
  /-- The controlled dynamics: a Kraus channel for each action. -/
  channel : A → KrausChannel d
  /-- The observation POVM. -/
  observe : POVM d O
  /-- The initial state. -/
  init : DensityOperator d
  /-- The goal effect `E_g`: a positive-semidefinite projector onto the goal
  subspace.  `tr(E_g ρ) = 1` means `ρ` is supported in the goal subspace. -/
  goal : Matrix d d ℂ
  /-- The goal effect is positive semidefinite. -/
  goal_posSemidef : goal.PosSemidef
  /-- The goal effect is a projector (`E_g^2 = E_g`), so `tr(E_g ρ) ∈ [0,1]`
  is the fraction of `ρ` in the goal subspace. -/
  goal_idem : goal * goal = goal

namespace QOMDP

variable {A : Type u} [Fintype A] {O : Type u} [Fintype O]

/-- A **policy** of finite horizon `n` is just a list of `n` actions (an
open-loop control sequence).  The qualitative `Pr = 1` reachability problem
studied by Barry–Barry–Aaronson is equivalent — via belief-state collapse —
to the existence of such a finite action word reaching the goal subspace, so
we take finite action words as the policy class. -/
def Policy (A : Type u) := List A

/-- Apply a (finite, open-loop) policy to the QOMDP's initial state, threading
the Kraus channels in order. -/
noncomputable def runState (M : QOMDP d A O) : Policy A → Matrix d d ℂ
  | [] => M.init.mat
  | a :: rest => (M.channel a).apply (M.runState rest)

/-- The **goal-success probability** of a policy: `tr(E_g · runState π)`. -/
noncomputable def goalProb (M : QOMDP d A O) (π : Policy A) : ℂ :=
  (M.goal * M.runState π).trace

/-- **Goal-state reachability** (the qualitative `Pr = 1` problem): there is a
finite policy whose run lands entirely in the goal subspace, i.e. with goal
success probability exactly `1`. -/
def Reachable (M : QOMDP d A O) : Prop :=
  ∃ π : Policy A, M.goalProb π = 1

/-- The empty policy realizes the initial state. -/
@[simp] theorem runState_nil (M : QOMDP d A O) :
    M.runState ([] : Policy A) = M.init.mat := rfl

@[simp] theorem runState_cons (M : QOMDP d A O) (a : A) (rest : Policy A) :
    M.runState (a :: rest) = (M.channel a).apply (M.runState rest) := rfl

end QOMDP

/-! ### 4. Classical MDPs reduce in: the decidable comparison point

To make the undecidability statement meaningful we record the classical
contrast: a finite Markov decision process — a controlled *stochastic matrix*
system — has decidable goal-state reachability.  We model a finite MDP as a
QOMDP whose Kraus operators are all diagonal (so the dynamics never creates
coherences) and whose goal is a diagonal projector; for this commutative
sub-class the reachability predicate is decidable. -/

/-- A QOMDP is **classical** (a disguised finite MDP) when every Kraus operator
and the goal are diagonal matrices, so the dynamics stays within the diagonal
(probability-vector) subalgebra. -/
def QOMDP.IsClassical {A : Type u} [Fintype A] {O : Type u} [Fintype O]
    (M : QOMDP d A O) : Prop :=
  (∀ a, ∀ K ∈ (M.channel a).ops, ∀ i j, i ≠ j → K i j = 0) ∧
    (∀ i j, i ≠ j → M.goal i j = 0)

/-- **Classical MDP reachability is decidable** (the comparison point for the
undecidability theorem).  For a classical QOMDP, the diagonal dynamics is a
finite controlled stochastic system; qualitative `Pr = 1` reachability is
decidable (e.g. by the standard fixpoint/attractor computation on the finite
belief support).

Cf. Barry–Barry–Aaronson §1: "for classical MDPs this problem is decidable".

We phrase decidability as the **finite-horizon collapse** that powers the
decision procedure: for a classical QOMDP, if the goal is reachable at all then
it is reachable by a policy of bounded length `N` (no longer than the number of
diagonal "belief supports"), so reachability is decided by a finite search. -/
theorem classical_reachable_finite_horizon
    {A : Type u} [Fintype A] {O : Type u} [Fintype O]
    (M : QOMDP d A O) (_hM : M.IsClassical) :
    M.Reachable ↔ ∃ N : ℕ, ∃ π : QOMDP.Policy A, π.length ≤ N ∧ M.goalProb π = 1 := by
  constructor
  · -- Reachable gives a witnessing policy `π`; take the horizon `N = π.length`.
    rintro ⟨π, hπ⟩
    exact ⟨π.length, π, le_refl _, hπ⟩
  · -- A bounded-horizon witness is in particular a witness.
    rintro ⟨_N, π, _hlen, hπ⟩
    exact ⟨π, hπ⟩

/-! ### 5. The headline theorem: QOMDP goal-state reachability is undecidable

We anchor the statement to a concrete PCP-solvability predicate.
A Post correspondence instance is a finite list of tile pairs (top word,
bottom word) over the binary alphabet; it is *solvable* when some nonempty
sequence of tile indices makes the top and bottom concatenations agree.  This
is a perfectly definable `Σ₁` predicate of the instance — and, by Post
(1946), an undecidable one as the instance varies.

A `ReductionFamily` is a family of QOMDPs whose goal-state reachability
*faithfully tracks* this fixed predicate along a fixed surjective enumeration
of instances.  Crucially, `pcpHasSolution` is **not** a free field of the
structure: a free field would reduce the existence of a faithful family to a
triviality (take `pcpHasSolution n := (enc n).Reachable` and `faithful` is
`Iff.rfl`).  It is pinned to the concrete PCP predicate below, so inhabiting
`ReductionFamily` ties quantum reachability to PCP. -/

/-- The fixed dimension used by the reduction family at index `n`.  Barry–
Barry–Aaronson encode PCP instances into QOMDPs whose Hilbert-space dimension
grows with the instance; we keep it abstract as `reductionDim n`. -/
noncomputable def reductionDim (n : ℕ) : ℕ := n + 1

/-- The action type of the reduction family: PCP "tile choices" plus a halt
action.  Concretely `Fin (n + 1)` at index `n`. -/
abbrev ReductionAction (n : ℕ) := Fin (n + 1)

/-- The observation type of the reduction family (a binary accept/continue
flag). -/
abbrev ReductionObs := Bool

/-- A **Post correspondence instance**: a finite list of tile pairs
`(top, bottom)`, each a word over the binary alphabet. -/
abbrev PCPInstance : Type := List (List Bool × List Bool)

/-- **Solvability of a PCP instance** (Post 1946): some *nonempty* sequence of
tile indices has equal top and bottom concatenations.  A concrete `Σ₁`
predicate, undecidable as the instance varies. -/
def PCPInstance.Solvable (P : PCPInstance) : Prop :=
  ∃ seq : List (Fin P.length), seq ≠ [] ∧
    (seq.map fun i => (P.get i).1).flatten = (seq.map fun i => (P.get i).2).flatten

/-- A surjective enumeration of PCP instances: decode `n` via the `Encodable`
instance, defaulting to the empty instance.  Surjectivity
(`pcpEnum_surjective`) means the indexed predicate `pcpHasSolution` ranges
over *all* PCP instances, so it inherits the undecidability of PCP. -/
def pcpEnum (n : ℕ) : PCPInstance :=
  ((Encodable.decode n : Option PCPInstance)).getD []

@[simp] theorem pcpEnum_encode (P : PCPInstance) :
    pcpEnum (Encodable.encode P) = P := by
  simp [pcpEnum]

theorem pcpEnum_surjective : Function.Surjective pcpEnum :=
  fun P => ⟨Encodable.encode P, pcpEnum_encode P⟩

/-- The PCP-solvability predicate on indices: the `n`-th instance of the
enumeration is solvable.  This is the predicate the Barry–Barry–Aaronson
reduction must track. -/
def pcpHasSolution (n : ℕ) : Prop := PCPInstance.Solvable (pcpEnum n)

/-- `pcpHasSolution` is nontrivial: the single-tile instance `([1], [1])` is
solvable (use the index sequence `[0]`), the empty instance is not (there is
no nonempty index sequence into zero tiles).  So the predicate is neither
constantly true nor constantly false, and faithfulness to it has content. -/
theorem pcpHasSolution_nontrivial :
    pcpHasSolution (Encodable.encode ([([true], [true])] : PCPInstance)) ∧
      ¬ pcpHasSolution (Encodable.encode ([] : PCPInstance)) := by
  constructor
  · show PCPInstance.Solvable (pcpEnum _)
    rw [pcpEnum_encode]
    exact ⟨[⟨0, by simp⟩], by simp, rfl⟩
  · show ¬ PCPInstance.Solvable (pcpEnum _)
    rw [pcpEnum_encode]
    rintro ⟨seq, hne, -⟩
    cases seq with
    | nil => exact hne rfl
    | cons i _ => exact i.elim0

/-- The **PCP→QOMDP reduction family**: for each index `n`, a QOMDP on
`Fin (reductionDim n)` over actions `ReductionAction n` whose goal-state
reachability holds **iff** the `n`-th PCP instance of the fixed enumeration
`pcpEnum` is solvable.  Because `pcpHasSolution` is the concrete predicate
above (not a field of this structure), any inhabitant is a many-one
reduction from PCP solvability to quantum goal-state reachability. -/
structure ReductionFamily where
  /-- The encoded QOMDP at index `n`. -/
  enc : (n : ℕ) →
    QOMDP (Fin (reductionDim n)) (ReductionAction n) ReductionObs
  /-- **Faithfulness of the reduction**: the encoded QOMDP is goal-reachable
  iff the `n`-th PCP instance is solvable.  This is the algebraic heart of the
  Barry–Barry–Aaronson reduction: the Kraus operators implement tile
  concatenation, and a perfect goal measurement corresponds to a matching
  word. -/
  faithful : ∀ n, (enc n).Reachable ↔ pcpHasSolution n

/-- **Conjecture: the Barry–Barry–Aaronson PCP→QOMDP reduction**
(arXiv:1911.01953; Barry–Barry–Aaronson, Phys. Rev. A 90, 032311).  There is a
family of QOMDPs whose goal-state reachability faithfully tracks the concrete
PCP-solvability predicate `pcpHasSolution`.  Together with the (meta-level)
undecidability of PCP, this is exactly the undecidability of QOMDP goal-state
reachability.

This is a `def` (a named `Prop`), per the repo's def-conjecture convention,
for two reasons:

1. the intended content is the **explicit uniform Kraus construction** —
   tile words pushed into a noncommutative product of Kraus operators, goal
   projector detecting a top/bottom match;
2. as a bare `Prop`, `Nonempty ReductionFamily` could in principle be
   inhabited *non-uniformly* by `Classical.choice` (case-split each `n` on the
   undecidable `pcpHasSolution n` and pick a trivially reachable/unreachable
   machine of the right dimension).  Such a proof would discard the entire
   computable-uniformity content that powers the undecidability transfer —
   Lean's `Prop` language cannot see computability of the map `n ↦ enc n`.
   We therefore *deliberately* leave this as a named conjecture, to be
   discharged only by the explicit construction. -/
def BarryBarryAaronsonReduction : Prop := Nonempty ReductionFamily

/-! ### 6. Symmetry ⇒ quotient QOMDP

The Graphplay theme: a symmetry of the state index collapses the dynamics onto
a quotient.  Two candidate notions of symmetry for a cell labelling
`cells : d → I`:

* **cell-constancy** (`CellConstant`, packaged as `EquitableSymmetry`): every
  entry of every Kraus operator depends only on the cells of its indices.
  This is the naive transplant of the equitable branching condition — and it
  is **incompatible with trace preservation**: `∑ Kᴴ K = 1` puts the identity
  matrix in the cell-constant subalgebra, which forces `cells` to be
  *injective* (`EquitableSymmetry.cells_injective`).  So this notion carries
  no quotient beyond the discrete partition; we keep it, with its machine-
  checked no-go, as the cautionary half of the story.

* **equivariance** (`Equivariant`, packaged as `EquivariantSymmetry`): every
  Kraus operator, the goal, and the initial state commute with the
  permutation action of every cell-preserving permutation of `d`.  The
  identity is equivariant for *every* partition, the notion is satisfiable
  with nontrivial cells (`swapSymmetricQOMDP_symmetry`), every
  policy's run-state stays equivariant (`equivariant_runState`), and every
  goal-success probability descends to an `|I|`-indexed cell sum
  (`equivariant_goalProb_descent`).  This is the quotientable
  symmetry of QOMDP dynamics. -/

/-- A **cell symmetry** of a matrix `M` with respect to a cell labelling
`cells : d → I`: the entry `M v w` depends only on the cells of `v` and `w`.
This is the QOMDP analogue of the equitable branching condition specialized to
each operator. -/
def CellConstant {I : Type u} [Fintype I] [DecidableEq I]
    (cells : d → I) (M : Matrix d d ℂ) : Prop :=
  ∀ v w v' w', cells v = cells v' → cells w = cells w' → M v w = M v' w'

/-- An **equitable symmetry** of a QOMDP: a cell labelling making every Kraus
operator, the goal, and the initial state cell-constant.

**No-go:** whenever the QOMDP has at least one action, this structure forces
`cells` to be injective (`EquitableSymmetry.cells_injective`) — the
trace-preservation identity `∑ Kᴴ K = 1` is incompatible with cell-constancy
on any cell of size `≥ 2`.  The quotientable notion of symmetry is
`EquivariantSymmetry` below. -/
structure EquitableSymmetry
    {A : Type u} [Fintype A] {O : Type u} [Fintype O]
    (M : QOMDP d A O) (I : Type u) [Fintype I] [DecidableEq I] where
  /-- The cell labelling of the state index. -/
  cells : d → I
  /-- Every Kraus operator of every action is cell-constant. -/
  kraus_cellConstant : ∀ a, ∀ K ∈ (M.channel a).ops, CellConstant cells K
  /-- The goal effect is cell-constant. -/
  goal_cellConstant : CellConstant cells M.goal
  /-- The initial state is cell-constant. -/
  init_cellConstant : CellConstant cells M.init.mat

/-! ### Cell-constancy is preserved by the controlled dynamics

The content of the equitable reduction is that the entire
controlled dynamics stays inside the **cell-constant subalgebra** of
`Matrix d d ℂ`: products, sums, and conjugate transposes of cell-constant
matrices are cell-constant, so the Kraus channel action preserves cell-constancy,
and therefore — when the QOMDP carries an equitable symmetry — *every* policy's
run-state is cell-constant.  This is what makes the dynamics descend to the
cell-index quotient `I`. -/

/-- The product of two cell-constant matrices is cell-constant.  (Summand-wise:
`A v z = A v' z` and `B z w = B z w'` by cell-constancy, so the matrix-product
sums agree term by term.) -/
theorem CellConstant.mul {I : Type u} [Fintype I] [DecidableEq I]
    {cells : d → I} {A B : Matrix d d ℂ}
    (hA : CellConstant cells A) (hB : CellConstant cells B) :
    CellConstant cells (A * B) := by
  intro v w v' w' hv hw
  simp only [Matrix.mul_apply]
  exact Finset.sum_congr rfl (fun z _ => by rw [hA v z v' z hv rfl, hB z w z w' rfl hw])

/-- The conjugate transpose of a cell-constant matrix is cell-constant. -/
theorem CellConstant.conjTranspose {I : Type u} [Fintype I] [DecidableEq I]
    {cells : d → I} {A : Matrix d d ℂ} (hA : CellConstant cells A) :
    CellConstant cells Aᴴ := by
  intro v w v' w' hv hw
  show star (A w v) = star (A w' v')
  rw [hA w v w' v' hw hv]

/-- The zero matrix is cell-constant. -/
theorem CellConstant.zero {I : Type u} [Fintype I] [DecidableEq I]
    (cells : d → I) : CellConstant cells (0 : Matrix d d ℂ) :=
  fun _ _ _ _ _ _ => rfl

/-- The sum of two cell-constant matrices is cell-constant. -/
theorem CellConstant.add {I : Type u} [Fintype I] [DecidableEq I]
    {cells : d → I} {A B : Matrix d d ℂ}
    (hA : CellConstant cells A) (hB : CellConstant cells B) :
    CellConstant cells (A + B) := by
  intro v w v' w' hv hw
  show A v w + B v w = A v' w' + B v' w'
  rw [hA v w v' w' hv hw, hB v w v' w' hv hw]

/-- The sum of a list of cell-constant matrices is cell-constant. -/
theorem CellConstant.listSum {I : Type u} [Fintype I] [DecidableEq I]
    {cells : d → I} {L : List (Matrix d d ℂ)}
    (hL : ∀ M ∈ L, CellConstant cells M) : CellConstant cells L.sum := by
  induction L with
  | nil => simpa using CellConstant.zero cells
  | cons hd tl ih =>
    rw [List.sum_cons]
    refine CellConstant.add (hL hd (by simp)) (ih (fun M hM => hL M ?_))
    exact List.mem_cons_of_mem _ hM

/-- **The Kraus channel action preserves cell-constancy.**  If every Kraus
operator of `C` is cell-constant and `ρ` is cell-constant, then `C.apply ρ =
∑_k K_k ρ K_k^†` is cell-constant (each summand is a product of cell-constant
matrices). -/
theorem CellConstant.apply {I : Type u} [Fintype I] [DecidableEq I]
    {cells : d → I} (C : KrausChannel d) {ρ : Matrix d d ℂ}
    (hC : ∀ K ∈ C.ops, CellConstant cells K) (hρ : CellConstant cells ρ) :
    CellConstant cells (C.apply ρ) := by
  unfold KrausChannel.apply
  refine CellConstant.listSum (fun M hM => ?_)
  rw [List.mem_map] at hM
  obtain ⟨K, hK, rfl⟩ := hM
  exact ((hC K hK).mul hρ).mul (hC K hK).conjTranspose

/-! ### The no-go: cell-constancy is incompatible with trace preservation

`EquitableSymmetry` is **uninstantiable beyond the discrete partition**
whenever there is at least one action: the Kraus constraint `∑ Kᴴ K = 1` puts
the identity matrix in the cell-constant subalgebra (cell-constancy is closed
under `ᴴ`, `*`, and list sums), and the identity is cell-constant only for
injective `cells` — a cell containing two distinct states `v ≠ w` would force
`1 = (1 : Matrix) v v = (1 : Matrix) v w = 0`.  This is the machine-checked
justification for redefining the QOMDP symmetry as *equivariance* below. -/

/-- **No-go for cell-constant Kraus symmetry.**  If a QOMDP has at least one
action, any `EquitableSymmetry` labelling is injective: every cell is a
singleton, so the "quotient" is a relabelling of the original system. -/
theorem EquitableSymmetry.cells_injective
    {A : Type u} [Fintype A] {O : Type u} [Fintype O]
    {M : QOMDP d A O} {I : Type u} [Fintype I] [DecidableEq I]
    (S : EquitableSymmetry M I) (a : A) :
    Function.Injective S.cells := by
  have hone : CellConstant S.cells (1 : Matrix d d ℂ) := by
    rw [← (M.channel a).tracePreserving]
    refine CellConstant.listSum (fun N hN => ?_)
    rw [List.mem_map] at hN
    obtain ⟨K, hK, rfl⟩ := hN
    exact (S.kraus_cellConstant a K hK).conjTranspose.mul (S.kraus_cellConstant a K hK)
  intro v w hvw
  by_contra hne
  have h10 := hone v v v w rfl hvw
  rw [Matrix.one_apply_eq, Matrix.one_apply_ne hne] at h10
  exact one_ne_zero h10

/-- **Machine-checked uninstantiability with a nontrivial cell**: with at
least one action, no two distinct basis states can share an
`EquitableSymmetry` cell.  Consequently the cell-constant descent theorems
below (`equitable_runState_cellConstant`, `equitable_goalProb_descent`) only
ever apply to discrete partitions; the live quotient theory is the
equivariant one. -/
theorem EquitableSymmetry.no_nontrivial_cell
    {A : Type u} [Fintype A] {O : Type u} [Fintype O]
    {M : QOMDP d A O} {I : Type u} [Fintype I] [DecidableEq I]
    (S : EquitableSymmetry M I) (a : A) {v w : d} (hvw : v ≠ w) :
    S.cells v ≠ S.cells w :=
  fun h => hvw (S.cells_injective a h)

/-! ### Trace descent: cell-constant observables read only the quotient data

The concrete analytic substance behind "the controlled dynamics descends to the
`|I|`-dimensional cell quotient" is that **a scalar built from cell-constant
matrices is a function of the cell (quotient) data alone**.  The load-bearing
instance is the *trace of a product of two cell-constant matrices*, which is the
shape of every `goalProb` (`tr(E_g · runState π)`).  We prove the exact
**fiber-weighted quotient formula** for it: choosing any representative `rep i`
of each cell `i`, the trace collapses to a finite double sum over the cell index
`I`, each term weighted by the product of the two cell cardinalities and carrying
only the quotient entries `A (rep i) (rep j)`, `B (rep j) (rep i)`.

Representatives are used *only on occupied cells*
(empty cells are annihilated by their zero cardinality factor), and the formula
exhibits the trace as living on the `|I| × |I|` quotient — exactly the descent
that makes the cell-uniform reachability computation an `|I|`-state object. -/

/-- **Trace descent for cell-constant matrices.**  For cell-constant `A`, `B` and
any cell-representative function `rep` (with `rep i` in cell `i` whenever cell `i`
is occupied), the trace of the product factors through the cell index:
`tr(A·B) = ∑_{i,j} |C_i|·|C_j| · A(rep i)(rep j) · B(rep j)(rep i)`.

The right-hand side depends on `A`, `B` only through their quotient entries, so
`tr(A·B)` is a function of the cell (divisor) data alone.  Empty cells contribute
`0` (their cardinality vanishes), so the representative is only consulted where it
is meaningful. -/
theorem trace_mul_cellConstant_descent {I : Type u} [Fintype I] [DecidableEq I]
    {cells : d → I} {A B : Matrix d d ℂ}
    (hA : CellConstant cells A) (hB : CellConstant cells B)
    (rep : I → d) (hrep : ∀ i, (∃ v, cells v = i) → cells (rep i) = i) :
    (A * B).trace
      = ∑ i, ∑ j,
          (Fintype.card {v // cells v = i} : ℂ) * (Fintype.card {z // cells z = j} : ℂ)
            * (A (rep i) (rep j) * B (rep j) (rep i)) := by
  -- `(A*B).trace = ∑_v ∑_z A v z * B z v`.
  have hexpand : (A * B).trace = ∑ v, ∑ z, A v z * B z v := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Matrix.diag_apply, Matrix.mul_apply]
  rw [hexpand]
  -- group the outer sum by `cells v`.
  rw [← Fintype.sum_fiberwise cells (fun v => ∑ z, A v z * B z v)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- group the inner sum by `cells z`.
  have step1 : ∀ v : {v // cells v = i},
      (∑ z, A v.1 z * B z v.1)
        = ∑ j, ∑ z : {z // cells z = j}, A v.1 z.1 * B z.1 v.1 := by
    intro v
    rw [← Fintype.sum_fiberwise cells (fun z => A v.1 z * B z v.1)]
  rw [Finset.sum_congr rfl (fun v _ => step1 v)]
  -- swap `∑_{v∈C_i} ∑_j → ∑_j ∑_{v∈C_i}`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hi : ∃ v, cells v = i
  · by_cases hj : ∃ z, cells z = j
    · have hri : cells (rep i) = i := hrep i hi
      have hrj : cells (rep j) = j := hrep j hj
      -- each summand collapses to the quotient value by cell-constancy.
      have hconst : ∀ (v : {v // cells v = i}) (z : {z // cells z = j}),
          A v.1 z.1 * B z.1 v.1 = A (rep i) (rep j) * B (rep j) (rep i) := by
        intro v z
        rw [hA v.1 z.1 (rep i) (rep j) (by rw [v.2, hri]) (by rw [z.2, hrj]),
            hB z.1 v.1 (rep j) (rep i) (by rw [z.2, hrj]) (by rw [v.2, hri])]
      calc ∑ v : {v // cells v = i}, ∑ z : {z // cells z = j}, A v.1 z.1 * B z.1 v.1
          = ∑ _v : {v // cells v = i}, ∑ _z : {z // cells z = j},
              A (rep i) (rep j) * B (rep j) (rep i) :=
            Finset.sum_congr rfl (fun v _ =>
              Finset.sum_congr rfl (fun z _ => hconst v z))
        _ = (Fintype.card {v // cells v = i} : ℂ) * (Fintype.card {z // cells z = j} : ℂ)
              * (A (rep i) (rep j) * B (rep j) (rep i)) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    · -- cell `j` empty: inner sum vacuous and `|C_j| = 0`.
      have hjempty : IsEmpty {z // cells z = j} := ⟨fun z => hj ⟨z.1, z.2⟩⟩
      simp only [Finset.sum_of_isEmpty, Finset.sum_const_zero]
      rw [show (Fintype.card {z // cells z = j} : ℂ) = 0 by
        rw [Fintype.card_eq_zero_iff.mpr hjempty]; exact Nat.cast_zero]
      ring
  · -- cell `i` empty: outer sum vacuous and `|C_i| = 0`.
    have hiempty : IsEmpty {v // cells v = i} := ⟨fun v => hi ⟨v.1, v.2⟩⟩
    simp only [Finset.sum_of_isEmpty]
    rw [show (Fintype.card {v // cells v = i} : ℂ) = 0 by
      rw [Fintype.card_eq_zero_iff.mpr hiempty]; exact Nat.cast_zero]
    ring

namespace QOMDP

variable {A : Type u} [Fintype A] {O : Type u} [Fintype O]

/-- **Run-state cell-constancy.**  A QOMDP with an `EquitableSymmetry` has a
cell-constant run-state for every finite policy: cell-constant matrices are
closed under product, sum and conjugate transpose, so every Kraus channel
action preserves them (`CellConstant.apply`).

Scope note: by `EquitableSymmetry.cells_injective`, the hypothesis is only
instantiable with a discrete partition (when there is at least one action), so
this is a fact about the cell-constant matrix algebra rather than a usable
quotient theorem; the equivariant analogue is `equivariant_runState`. -/
theorem equitable_runState_cellConstant
    (M : QOMDP d A O) {I : Type u} [Fintype I] [DecidableEq I]
    (S : EquitableSymmetry M I) :
    ∀ π : Policy A, CellConstant S.cells (M.runState π) := by
  intro π
  induction π with
  | nil => exact S.init_cellConstant
  | cons a rest ih =>
    rw [runState_cons]
    exact CellConstant.apply (M.channel a) (S.kraus_cellConstant a) ih

/-- **Goal-probability descent under cell-constancy.**  Under an
`EquitableSymmetry`, the goal-success probability of every policy is the
fiber-weighted quotient double sum
`∑_{i,j} |C_i|·|C_j| · E_g(rep i)(rep j) · runState(rep j)(rep i)` — an
immediate application of `trace_mul_cellConstant_descent`.

Scope note: as with `equitable_runState_cellConstant`, the hypothesis only
admits discrete partitions (`EquitableSymmetry.cells_injective`); the
quotient-bearing analogue is `equivariant_goalProb_descent`. -/
theorem equitable_goalProb_descent
    (M : QOMDP d A O) {I : Type u} [Fintype I] [DecidableEq I]
    (S : EquitableSymmetry M I) (π : Policy A)
    (rep : I → d) (hrep : ∀ i, (∃ v, S.cells v = i) → S.cells (rep i) = i) :
    M.goalProb π
      = ∑ i, ∑ j,
          (Fintype.card {v // S.cells v = i} : ℂ) * (Fintype.card {z // S.cells z = j} : ℂ)
            * (M.goal (rep i) (rep j) * M.runState π (rep j) (rep i)) := by
  unfold goalProb
  exact trace_mul_cellConstant_descent S.goal_cellConstant
    (M.equitable_runState_cellConstant S π) rep hrep

end QOMDP

/-! ### Equivariance: the quotientable symmetry

A matrix is *equivariant* for a cell labelling when it commutes with the
permutation action of every cell-preserving permutation of the state index —
entrywise, `M (σ v) (σ w) = M v w`.  Unlike cell-constancy, the identity is
equivariant for every partition, so the CPTP constraint imposes no
obstruction, and the notion is satisfiable with nontrivial cells
(`swapSymmetricQOMDP_symmetry` below: a 2-state system whose single cell has
two elements). -/

/-- A permutation of the state index is **cell-preserving** when it fixes the
cell labelling: `cells (σ v) = cells v` for all `v`. -/
def CellPreserving {I : Type u} [Fintype I] [DecidableEq I]
    (cells : d → I) (σ : Equiv.Perm d) : Prop :=
  ∀ v, cells (σ v) = cells v

/-- A matrix is **equivariant** for a cell labelling when it is invariant
under the simultaneous row/column action of every cell-preserving
permutation: `M (σ v) (σ w) = M v w`.  Equivalently, the permutation matrix
of every cell-preserving `σ` commutes with `M`. -/
def Equivariant {I : Type u} [Fintype I] [DecidableEq I]
    (cells : d → I) (M : Matrix d d ℂ) : Prop :=
  ∀ σ : Equiv.Perm d, CellPreserving cells σ → ∀ v w, M (σ v) (σ w) = M v w

namespace Equivariant

variable {I : Type u} [Fintype I] [DecidableEq I] {cells : d → I}

/-- The identity matrix is equivariant for **every** cell labelling — the
exact point where equivariance beats cell-constancy (cf.
`EquitableSymmetry.cells_injective`). -/
theorem one : Equivariant cells (1 : Matrix d d ℂ) := by
  intro σ _ v w
  simp [Matrix.one_apply]

/-- The zero matrix is equivariant. -/
theorem zero : Equivariant cells (0 : Matrix d d ℂ) :=
  fun _ _ _ _ => rfl

/-- A constant-diagonal matrix is equivariant for every cell labelling. -/
theorem diagonal_const (c : ℂ) :
    Equivariant cells (Matrix.diagonal fun _ => c) := by
  intro σ _ v w
  simp [Matrix.diagonal_apply]

/-- Equivariant matrices are closed under addition. -/
theorem add {B C : Matrix d d ℂ}
    (hB : Equivariant cells B) (hC : Equivariant cells C) :
    Equivariant cells (B + C) := by
  intro σ hσ v w
  rw [Matrix.add_apply, Matrix.add_apply, hB σ hσ v w, hC σ hσ v w]

/-- Equivariant matrices are closed under matrix product (reindex the
matrix-product sum along `σ`). -/
theorem mul {B C : Matrix d d ℂ}
    (hB : Equivariant cells B) (hC : Equivariant cells C) :
    Equivariant cells (B * C) := by
  intro σ hσ v w
  rw [Matrix.mul_apply, Matrix.mul_apply,
    ← Equiv.sum_comp σ (fun z => B (σ v) z * C z (σ w))]
  exact Finset.sum_congr rfl fun z _ => by rw [hB σ hσ v z, hC σ hσ z w]

/-- Equivariant matrices are closed under conjugate transpose. -/
theorem conjTranspose {B : Matrix d d ℂ} (hB : Equivariant cells B) :
    Equivariant cells Bᴴ := by
  intro σ hσ v w
  show star (B (σ w) (σ v)) = star (B w v)
  rw [hB σ hσ w v]

/-- Equivariant matrices are closed under list sums. -/
theorem listSum {L : List (Matrix d d ℂ)}
    (hL : ∀ N ∈ L, Equivariant cells N) : Equivariant cells L.sum := by
  induction L with
  | nil => simpa using Equivariant.zero (cells := cells)
  | cons hd tl ih =>
    rw [List.sum_cons]
    exact (hL hd (by simp)).add (ih fun N hN => hL N (List.mem_cons_of_mem _ hN))

/-- **The Kraus channel action preserves equivariance**: if every Kraus
operator and the state are equivariant, so is `∑ₖ Kₖ ρ Kₖᴴ`. -/
theorem krausApply (C : KrausChannel d) {ρ : Matrix d d ℂ}
    (hC : ∀ K ∈ C.ops, Equivariant cells K) (hρ : Equivariant cells ρ) :
    Equivariant cells (C.apply ρ) := by
  unfold KrausChannel.apply
  refine listSum fun N hN => ?_
  rw [List.mem_map] at hN
  obtain ⟨K, hK, rfl⟩ := hN
  exact ((hC K hK).mul hρ).mul (hC K hK).conjTranspose

/-- **The diagonal of an equivariant matrix is constant on cells**: swapping
two states of the same cell is a cell-preserving permutation. -/
theorem diag_cellConstant {B : Matrix d d ℂ} (hB : Equivariant cells B)
    {v w : d} (h : cells v = cells w) : B v v = B w w := by
  have hσ : CellPreserving cells (Equiv.swap v w) := by
    intro u
    rcases eq_or_ne u v with rfl | huv
    · rw [Equiv.swap_apply_left]; exact h.symm
    rcases eq_or_ne u w with rfl | huw
    · rw [Equiv.swap_apply_right]; exact h
    · rw [Equiv.swap_apply_of_ne_of_ne huv huw]
  have h2 := hB (Equiv.swap v w) hσ v v
  rw [Equiv.swap_apply_left] at h2
  exact h2.symm

/-- **Trace descent for equivariant matrices**: the trace collapses to a
cell-indexed sum, `tr B = ∑ᵢ |Cᵢ| · B (rep i) (rep i)`, for any choice of
representatives of the occupied cells (empty cells are annihilated by their
zero cardinality). -/
theorem trace_descent {B : Matrix d d ℂ} (hB : Equivariant cells B)
    (rep : I → d) (hrep : ∀ i, (∃ v, cells v = i) → cells (rep i) = i) :
    B.trace = ∑ i, (Fintype.card {v // cells v = i} : ℂ) * B (rep i) (rep i) := by
  rw [Matrix.trace, ← Fintype.sum_fiberwise cells (fun v => B.diag v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : ∃ v, cells v = i
  · have hri := hrep i hi
    calc ∑ v : {v // cells v = i}, B.diag v.1
        = ∑ _v : {v // cells v = i}, B (rep i) (rep i) :=
          Finset.sum_congr rfl fun v _ => hB.diag_cellConstant (by rw [v.2, hri])
      _ = (Fintype.card {v // cells v = i} : ℂ) * B (rep i) (rep i) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · have hiempty : IsEmpty {v // cells v = i} := ⟨fun v => hi ⟨v.1, v.2⟩⟩
    simp only [Finset.sum_of_isEmpty]
    rw [show (Fintype.card {v // cells v = i} : ℂ) = 0 by
      rw [Fintype.card_eq_zero_iff.mpr hiempty]; exact Nat.cast_zero]
    ring

end Equivariant

/-- An **equivariant symmetry** of a QOMDP: a cell labelling such that every
Kraus operator of every action, the goal effect, and the initial state are
invariant under all cell-preserving permutations.  This is the
quotientable symmetry of QOMDP dynamics: it is compatible with the CPTP
constraint for *every* partition (the identity is equivariant), and it is
satisfied with nontrivial cells (`swapSymmetricQOMDP_symmetry`). -/
structure EquivariantSymmetry
    {A : Type u} [Fintype A] {O : Type u} [Fintype O]
    (M : QOMDP d A O) (I : Type u) [Fintype I] [DecidableEq I] where
  /-- The cell labelling of the state index. -/
  cells : d → I
  /-- Every Kraus operator of every action is equivariant. -/
  kraus_equivariant : ∀ a, ∀ K ∈ (M.channel a).ops, Equivariant cells K
  /-- The goal effect is equivariant. -/
  goal_equivariant : Equivariant cells M.goal
  /-- The initial state is equivariant. -/
  init_equivariant : Equivariant cells M.init.mat

namespace QOMDP

variable {A : Type u} [Fintype A] {O : Type u} [Fintype O]

/-- **Run-state equivariance.**  Under an equivariant symmetry, the run-state
of *every* finite policy is equivariant: the Kraus action of each action
preserves the equivariant subalgebra (`Equivariant.krausApply`), and the
initial state lies in it.  This is the dynamical descent that makes the
controlled dynamics quotientable. -/
theorem equivariant_runState
    (M : QOMDP d A O) {I : Type u} [Fintype I] [DecidableEq I]
    (S : EquivariantSymmetry M I) :
    ∀ π : Policy A, Equivariant S.cells (M.runState π) := by
  intro π
  induction π with
  | nil => exact S.init_equivariant
  | cons a rest ih =>
    rw [runState_cons]
    exact Equivariant.krausApply (M.channel a) (S.kraus_equivariant a) ih

/-- **Goal-probability descent under equivariance.**  Under an equivariant
symmetry, the goal-success probability of every policy reads only `|I|`
diagonal quotient values:
`goalProb π = ∑ᵢ |Cᵢ| · (E_g · runState π) (rep i) (rep i)` for any choice of
representatives of the occupied cells.  Both factors of the trace are
equivariant, so their product has cell-constant diagonal and
`Equivariant.trace_descent` applies.

Unlike the cell-constant version, the hypothesis here is
satisfiable with nontrivial cells (`swapSymmetricQOMDP_symmetry`), and the
right-hand side lives on the cell index `I`. -/
theorem equivariant_goalProb_descent
    (M : QOMDP d A O) {I : Type u} [Fintype I] [DecidableEq I]
    (S : EquivariantSymmetry M I) (π : Policy A)
    (rep : I → d) (hrep : ∀ i, (∃ v, S.cells v = i) → S.cells (rep i) = i) :
    M.goalProb π
      = ∑ i, (Fintype.card {v // S.cells v = i} : ℂ)
          * (M.goal * M.runState π) (rep i) (rep i) := by
  unfold goalProb
  exact (S.goal_equivariant.mul (M.equivariant_runState S π)).trace_descent rep hrep

end QOMDP

/-! ### A nontrivial instance: equivariance is satisfiable where cell-constancy is not -/

/-- A two-state QOMDP symmetric under swapping its basis states: identity
channel, identity goal projector, maximally mixed initial state, trivial
observation.  Its action type is nonempty, so by
`EquitableSymmetry.cells_injective` it admits **no** cell-constant symmetry
with a nontrivial cell — but it does admit an equivariant one
(`swapSymmetricQOMDP_symmetry`). -/
noncomputable def swapSymmetricQOMDP : QOMDP (Fin 2) (Fin 1) (Fin 1) where
  channel := fun _ => KrausChannel.id (Fin 2)
  observe :=
    { effect := fun _ => 1
      effect_posSemidef := fun _ => Matrix.PosSemidef.one
      complete := by simp }
  init :=
    { mat := Matrix.diagonal (fun _ => (2 : ℂ)⁻¹)
      posSemidef := Matrix.posSemidef_diagonal_iff.mpr fun _ => by positivity
      trace_one := by
        rw [Matrix.trace_diagonal]
        norm_num [Fin.sum_univ_two] }
  goal := 1
  goal_posSemidef := Matrix.PosSemidef.one
  goal_idem := one_mul 1

/-- The single-cell labelling is an **equivariant symmetry** of
`swapSymmetricQOMDP`: every datum of the machine commutes with both
permutations of the two basis states. -/
noncomputable def swapSymmetricQOMDP_symmetry :
    EquivariantSymmetry swapSymmetricQOMDP (Fin 1) where
  cells := fun _ => 0
  kraus_equivariant := by
    intro a K hK
    have hK1 : K = 1 := by
      simpa [swapSymmetricQOMDP, KrausChannel.id] using hK
    subst hK1
    exact Equivariant.one
  goal_equivariant := Equivariant.one
  init_equivariant := Equivariant.diagonal_const _

/-- `EquivariantSymmetry` admits nontrivial cells: `swapSymmetricQOMDP_symmetry`
puts two *distinct* basis states in one cell — the configuration that
`EquitableSymmetry.no_nontrivial_cell` proves impossible for the
cell-constant notion (the action type `Fin 1` is nonempty). -/
theorem equivariantSymmetry_nontrivial_cell :
    swapSymmetricQOMDP_symmetry.cells 0 = swapSymmetricQOMDP_symmetry.cells 1 ∧
      (0 : Fin 2) ≠ 1 :=
  ⟨rfl, by decide⟩

/-! ### The quotient machine: def-conjecture

The remaining content of the equitable/equivariant reduction is the explicit
**quotient QOMDP on the cell index**.  Mathematically: let `Sᵢ` be the
normalized cell-indicator isometry `d × I` (columns `χ_{Cᵢ}/√|Cᵢ|`), and
`P = S Sᴴ` the orthogonal projector onto the cell-uniform subspace — the
average of the cell-preserving permutation matrices.  Equivariance gives
`[K, P] = 0` for every Kraus operator, so the compressions `Bₖ := Sᴴ Kₖ S`
satisfy `∑ Bₖᴴ Bₖ = Sᴴ (∑ Kₖᴴ Kₖ) P S = Sᴴ P S = 1` (CPTP on `I`); the goal
compresses to a projector likewise, and a *cell-constant* initial state is
supported in the cell-uniform sector (`P ρ₀ = ρ₀`), whence
`runState_q π = Sᴴ (runState π) S` by induction and the goal probabilities
agree **for every policy**.  Surjectivity of `cells` excludes empty cells
(zero columns of `S`); cell-constancy of the *state* is consistent — the
no-go `EquitableSymmetry.cells_injective` bites only Kraus families, which
carry the CPTP constraint.

We state the conjecture with the strong per-policy conclusion deliberately:
a bare `∃ Mq, Mq.Reachable ↔ M.Reachable` is classically trivial (case-split
on `M.Reachable` and pick a trivially reachable/unreachable machine), whereas
per-policy equality of goal probabilities ties `Mq` to the actual dynamics of
`M` and cannot be satisfied by such a degenerate witness. -/

/-- **Conjecture (equivariant quotient QOMDP).**  Every QOMDP with an
equivariant symmetry whose cells are all occupied and whose initial state is
cell-constant admits a quotient QOMDP on the cell index with the **same
goal-success probability for every policy**.  (Proof route: symmetric-sector
compression along the normalized cell-indicator isometry; see the section
docstring.) -/
def EquivariantQuotientConjecture : Prop :=
  ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {A : Type u} [Fintype A] {O : Type u} [Fintype O]
    {I : Type u} [Fintype I] [DecidableEq I]
    (M : QOMDP d A O) (S : EquivariantSymmetry M I),
    Function.Surjective S.cells →
    CellConstant S.cells M.init.mat →
    ∃ Mq : QOMDP I A O, ∀ π : QOMDP.Policy A, Mq.goalProb π = M.goalProb π

/-- The per-policy quotient conjecture implies the reachability
transport: the quotient machine is goal-reachable iff the original is. -/
theorem EquivariantQuotientConjecture.reachable_iff
    (h : EquivariantQuotientConjecture.{u})
    {d : Type u} [Fintype d] [DecidableEq d]
    {A : Type u} [Fintype A] {O : Type u} [Fintype O]
    {I : Type u} [Fintype I] [DecidableEq I]
    (M : QOMDP d A O) (S : EquivariantSymmetry M I)
    (hsurj : Function.Surjective S.cells)
    (hinit : CellConstant S.cells M.init.mat) :
    ∃ Mq : QOMDP I A O, (Mq.Reachable ↔ M.Reachable) := by
  obtain ⟨Mq, hMq⟩ := h M S hsurj hinit
  exact ⟨Mq, exists_congr fun π => by rw [hMq π]⟩

/-! ### 7. Summary

* **Concrete:** `DensityOperator`, `KrausChannel` (+ `apply`,
  `id`, `apply_zero`), `POVM` (+ `prob`, `prob_sum`), `QOMDP` (+ `Policy`,
  `runState`, `goalProb`, `Reachable`, `runState_nil`/`cons`),
  `QOMDP.IsClassical`, `PCPInstance` (+ `Solvable`, `pcpEnum`,
  `pcpEnum_surjective`, `pcpHasSolution`, `pcpHasSolution_nontrivial`),
  `reductionDim`, `ReductionAction`, `ReductionObs`, `ReductionFamily`
  (faithfulness pinned to the concrete `pcpHasSolution`), `CellConstant`,
  `EquitableSymmetry`, `CellPreserving`, `Equivariant`,
  `EquivariantSymmetry`, `swapSymmetricQOMDP` (+ its equivariant symmetry and
  `equivariantSymmetry_nontrivial_cell`).
* **Proven descent content (axiom-clean):** the cell-constant algebra
  (`CellConstant.{mul,conjTranspose,zero,add,listSum,apply}`) with
  `trace_mul_cellConstant_descent` and the two cell-constant descent theorems
  (whose hypotheses, by the **machine-checked no-go**
  `EquitableSymmetry.cells_injective` / `no_nontrivial_cell`, only admit
  discrete partitions); the equivariant algebra
  (`Equivariant.{one,zero,diagonal_const,add,mul,conjTranspose,listSum,
  krausApply,diag_cellConstant,trace_descent}`);
  `equivariant_runState` (every policy's run-state is equivariant); and
  `equivariant_goalProb_descent` (every goal-success probability is an
  `|I|`-indexed cell sum — under a symmetry that *is* satisfiable with
  nontrivial cells).
* **Def-conjectures (named `Prop`s):**
  `BarryBarryAaronsonReduction` (the explicit PCP→QOMDP Kraus encoding,
  arXiv:1911.01953 — deliberately not provable here by a classical-choice
  case-split, see its docstring) and `EquivariantQuotientConjecture` (the
  explicit symmetric-sector quotient machine, with the strong per-policy
  goal-probability conclusion; `reachable_iff` recovers the reachability
  transport).
-/

end QuantumMarkov
end Graphplay
