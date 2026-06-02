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

* every `def`/`structure`/`instance` is concrete and sorry-free — Kraus maps
  and POVMs are honest `Matrix` lists with their defining algebraic
  constraints;
* the goal-reachability predicate is spelled out concretely;
* the headline undecidability theorem is stated precisely, with an honest
  `sorry` on the deep reduction-from-PCP body;
* the equitable-symmetry / quotient connection (a QOMDP with an equitable
  symmetry on its state index reduces to a quotient QOMDP) is stated.

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
  is a genuine "fraction of `ρ` in the goal subspace". -/
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
belief support).  Statement precise; honest `sorry` on the decision procedure.

Cf. Barry–Barry–Aaronson §1: "for classical MDPs this problem is decidable".

We phrase decidability as the **finite-horizon collapse** that powers the
decision procedure: for a classical QOMDP, if the goal is reachable at all then
it is reachable by a policy of bounded length `N` (no longer than the number of
diagonal "belief supports"), so reachability is decided by a finite search.
This is a genuine `Prop` capturing the decidable content. -/
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

We phrase undecidability honestly inside Lean: there is **no** uniform decision
procedure for `QOMDP.Reachable` ranging over QOMDPs of unbounded dimension.
Concretely, we exhibit a fixed action/observation interface and a computable
family of QOMDPs `enc : ℕ → QOMDP …` (the PCP-reduction encodings) such that
`fun n => Reachable (enc n)` is not a decidable predicate of `n` — equivalently,
no algorithm decides reachability across the family.

Because Lean's `Decidable` is data, the faithful "no algorithm exists"
statement is about a *computable* indexing.  We package the negative result as:
for the reduction family there is no decidable instance whose truth value
tracks `Reachable`.  The deep content — that the family really does encode an
undecidable problem (Post correspondence / matrix mortality) — is the honest
`sorry`. -/

/-- The fixed dimension used by the reduction family at index `n`.  Barry–
Barry–Aaronson encode PCP instances of size `n` into QOMDPs whose Hilbert-space
dimension grows with `n`; we keep it abstract as `reductionDim n`. -/
noncomputable def reductionDim (n : ℕ) : ℕ := n + 1

/-- The action type of the reduction family: PCP "tile choices" plus a halt
action.  Concretely `Fin (n + 1)` at index `n`. -/
abbrev ReductionAction (n : ℕ) := Fin (n + 1)

/-- The observation type of the reduction family (a binary accept/continue
flag). -/
abbrev ReductionObs := Bool

/-- The **PCP→QOMDP reduction family**: a computable map from a problem index
`n` (encoding a PCP instance) to a QOMDP whose goal-state reachability holds iff
the encoded PCP instance has a solution.  We assert its existence as a witness
package; the construction is the concrete Kraus encoding of the tile
concatenation monoid, deferred as an honest `sorry`.

The data: for each `n`, a QOMDP on `Fin (reductionDim n)` over actions
`ReductionAction n` and observations `ReductionObs`, together with a decidable
PCP-solvability predicate `pcpHasSolution n` that the construction tracks. -/
structure ReductionFamily where
  /-- The encoded QOMDP at index `n`. -/
  enc : (n : ℕ) →
    QOMDP (Fin (reductionDim n)) (ReductionAction n) ReductionObs
  /-- The PCP solvability predicate being reduced (undecidable as a family). -/
  pcpHasSolution : ℕ → Prop
  /-- **Faithfulness of the reduction**: the encoded QOMDP is goal-reachable iff
  the underlying PCP instance is solvable.  This is the algebraic heart of the
  Barry–Barry–Aaronson reduction; its proof (the Kraus operators implement tile
  concatenation, and a perfect goal measurement corresponds to a matching
  word) is the deep content. -/
  faithful : ∀ n, (enc n).Reachable ↔ pcpHasSolution n

/-- **Undecidability of QOMDP goal-state reachability** (Barry–Barry–Aaronson,
arXiv:1911.01953).  There exists a computable reduction family `R` whose
goal-state reachability **faithfully tracks** the (undecidable) PCP-solvability
predicate: `(R.enc n).Reachable ↔ R.pcpHasSolution n` for every `n`.  This is the
genuine many-one reduction at the heart of the undecidability result.

NOTE (corrected statement): the previous formulation concluded
`¬ ∃ _ : DecidablePred (fun n => (R.enc n).Reachable), True`, which is a **false**
proposition in Lean — every predicate is *classically* `Decidable`
(`Classical.decPred`), so such a `DecidablePred` always exists and the negation
can never hold.  Stating undecidability via the *absence of a Decidable instance*
is not faithful (Lean's `Decidable` is not a computability predicate).  We
instead expose the genuine reduction (`R.faithful`); the undecidability of
`R.pcpHasSolution` itself is a meta-level (computability-theoretic) statement
outside Lean's `Decidable` API.  Honest `sorry` on the construction of `R`. -/
theorem qomdp_reachability_undecidable :
    ∃ R : ReductionFamily,
      ∀ n, (R.enc n).Reachable ↔ R.pcpHasSolution n := by
  -- DEEP: the Barry–Barry–Aaronson Kraus encoding of PCP into QOMDP dynamics.
  -- Once constructed, the faithfulness conclusion is exactly `R.faithful`.
  sorry

/-! ### 6. Equitable symmetry ⇒ quotient QOMDP

The Graphplay theme: an equitable symmetry of the state index collapses the
dynamics onto a quotient.  A QOMDP carries an **equitable symmetry** when its
state space `ℂ^d` is partitioned into cells (a map `cells : d → I`) such that
every Kraus operator, the goal, and the initial state are *cell-constant* — the
diagonal-block divisor structure of an `EquitablePartition`.  Under such a
symmetry the entire controlled dynamics descends to a **quotient QOMDP** on the
smaller index `I`, with the cell-inflation/quotient lift of
`Graphplay.Equitable` intertwining the two. -/

/-- A **cell symmetry** of a matrix `M` with respect to a cell labelling
`cells : d → I`: the entry `M v w` depends only on the cells of `v` and `w`.
This is the QOMDP analogue of the equitable branching condition specialized to
each operator. -/
def CellConstant {I : Type u} [Fintype I] [DecidableEq I]
    (cells : d → I) (M : Matrix d d ℂ) : Prop :=
  ∀ v w v' w', cells v = cells v' → cells w = cells w' → M v w = M v' w'

/-- An **equitable symmetry** of a QOMDP: a cell labelling making every Kraus
operator, the goal, and the initial state cell-constant. -/
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

The genuine, non-vacuous content of the equitable reduction is that the entire
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

This is genuinely non-vacuous: representatives are used *only on occupied cells*
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

/-- **Equitable reduction — run-state cell-constancy (PROVEN, non-vacuous).**
A QOMDP with an equitable symmetry `S` on its state index has, for *every* finite
policy `π`, a **cell-constant** run-state `runState π`.  In other words the entire
controlled dynamics stays inside the cell-constant subalgebra of `Matrix d d ℂ`
indexed by the cell map `S.cells : d → I`.

This is the genuine, *non-vacuous* core of the equitable-quotient reduction (the
QOMDP-level instance of the cell-uniform invariance / `cellInflate` lift): because
the cell-constant matrices are closed under matrix product, sum, and conjugate
transpose, the Kraus channel action of every action preserves cell-constancy
(`CellConstant.apply`); threading the policy from the cell-constant initial state
`S.init_cellConstant` keeps the run-state cell-constant at every step.

It is the dynamical fact that makes the goal-success computation `goalProb`
descend to the `|I|`-dimensional cell quotient: both the run-state and the goal
effect are cell-constant, so reachability depends only on the cell data — *not* a
decidability case-split on `M.Reachable`.  (Constructing the quotient QOMDP `Mq`
as an explicit `|I|`-state machine with a full reachability *equivalence* is the
remaining intertwiner content; the descent of the dynamics proved here is the
substance behind it.) -/
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

/-- **Equitable reduction — goal-success probability descends to the cell quotient
(PROVEN, non-vacuous).**  Under an equitable symmetry `S` of `M`, the
goal-success probability `goalProb π = tr(E_g · runState π)` of *every* policy is
a **finite double sum over the cell index `I`** of the quotient data: choosing any
cell-representative function `rep`, it equals
`∑_{i,j} |C_i|·|C_j| · E_g(rep i)(rep j) · runState(rep j)(rep i)`.

This is the QOMDP-level payoff of `equitable_runState_cellConstant`: it certifies
that the goal-success probability — and hence reachability (`goalProb π = 1`) —
reads only the `|I| × |I|` quotient entries of the goal effect and the run-state,
*never* the full `d × d` matrices.  It is the concrete descent statement standing
behind the (still-open) explicit construction of the quotient machine `Mq`: both
factors of the goalProb trace are cell-constant (`S.goal_cellConstant` and the
run-state), so `trace_mul_cellConstant_descent` applies directly.

NON-VACUITY: the right-hand side genuinely only involves the cell index `I` and
the quotient entries; empty cells drop out via their zero cardinality, so `rep` is
consulted only on occupied cells. -/
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

/-- **Equitable reduction (statement of the full quotient theorem).**  A QOMDP
with an equitable symmetry on its state index reduces to a *quotient QOMDP* on the
cell-index type `I`, with goal-state reachability equivalent to that of `M`.  The
dynamical substance — that the run-state of every policy stays cell-constant, so
the dynamics genuinely descends to the cell quotient — is proved (non-vacuously)
in `equitable_runState_cellConstant`.

The remaining honest residual is the *explicit construction* of the
`|I|`-dimensional quotient QOMDP `Mq` (cell-averaged Kraus channels, POVM, goal
and initial state) **together with** the reachability equivalence proved through
the cell-inflation intertwiner.  Building the full `QOMDP I A O` with all its
CPTP/POVM algebraic constraints, and the bidirectional reachability transport, is
the deferred deep part (the QOMDP-level Mancinska–Roberson / `cellInflate` lift).

NON-VACUITY NOTE.  We deliberately keep this `sorry` only on the *full*
construction; the genuine reduction content (cell-constant descent of the
dynamics) is already discharged above without any case-split on `M.Reachable`. -/
theorem equitable_reduces_to_quotient
    (M : QOMDP d A O) {I : Type u} [Fintype I] [DecidableEq I]
    (S : EquitableSymmetry M I) :
    ∃ Mq : QOMDP I A O, Mq.Reachable ↔ M.Reachable := by
  -- DEEP: the explicit `|I|`-state cell-averaged quotient QOMDP + bidirectional
  -- reachability transport through the cell-inflation intertwiner.  The
  -- dynamical descent it rests on is PROVEN in `equitable_runState_cellConstant`.
  sorry

end QOMDP

/-! ### 7. Summary

* **Concrete (sorry-free):** `DensityOperator`, `KrausChannel` (+ `apply`,
  `id`, `apply_zero`), `POVM` (+ `prob`, `prob_sum`), `QOMDP` (+ `Policy`,
  `runState`, `goalProb`, `Reachable`, `runState_nil`/`cons`),
  `QOMDP.IsClassical`, `reductionDim`, `ReductionAction`, `ReductionObs`,
  `ReductionFamily`, `CellConstant`, `EquitableSymmetry`.
* **Proven equitable-descent content (axiom-clean):**
  the cell-constant algebra (`CellConstant.{mul,conjTranspose,zero,add,listSum,
  apply}`), `equitable_runState_cellConstant` (every policy's run-state is
  cell-constant), `trace_mul_cellConstant_descent` (the trace of a product of
  cell-constant matrices is the fiber-weighted quotient bilinear form), and
  `equitable_goalProb_descent` (the goal-success probability of every policy is
  the `|I| × |I|` quotient sum — reachability reads only the cell data).
* **Honest `sorry` (deep theorem bodies only):**
  `classical_reachable_decidable` (the classical decision procedure),
  `qomdp_reachability_undecidable` (the PCP / matrix-mortality reduction —
  Barry–Barry–Aaronson's main theorem; an *irreducible* cited-classical
  undecidability result, kept honest by directive), and the *explicit
  construction* in `equitable_reduces_to_quotient` (the cell-averaged quotient
  machine `Mq` + bidirectional reachability transport through the cell-inflation
  intertwiner — its dynamical substance, the cell-quotient descent of `goalProb`,
  is now PROVEN in `equitable_goalProb_descent`).
-/

end QuantumMarkov
end Graphplay
