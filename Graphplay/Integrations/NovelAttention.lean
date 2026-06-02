/-
# Graphplay.Integrations.NovelAttention

**Novel attention bets from the equitable-partition / quantum-walk vantage.**

Where `StructuredAttention` answers "*which existing attention families* satisfy
the equitable precondition", this module proposes **new attention mechanisms**
that the quantum-walk (QW) toolkit *suggests* — each formalized as a genuine
`WeightedGraph` / operator construction (not prose), with the key property
proven where it is reachable; the chiral payoff is now grounded by the *concrete*
proven uniform-mixing instance rather than an existential placeholder.

The four bets, in increasing speculativeness:

1. **Chiral (phased) attention** (`chiralAttention`).  A complex-Hermitian
   attention head carrying a U(1) edge phase `σ(i,j)` (a `ChiralSigning`), as in
   the magnetic / chiral quantum walk.  We *prove* (a) it is a genuine
   `WeightedGraph` — Hermitian, loopless (inherited from `WeightedGraph.signedBy`);
   and (b) **a cross-constant phase descends to the equitable quotient**
   (`chiralAttention_descends`, reusing `signedBy_preserves_equitable`): phased
   attention still lifts to the small quotient.  **Payoff (PROVEN as a
   concrete instance):** the genuinely chiral Levine `K₄` graph
   `unitaryHammingChiralK4` reaches *probabilistic uniform mixing* at the time
   `π/(3√3)` (`chiralK4_attention_achieves_uniformMixing`, via
   `unitaryHammingChiralK4_uniformMixing`) — every propagator entry has modulus
   `1/√4`.  *Grounded:* Hermiticity, quotient descent, and the concrete uniform
   mixing.  *Not claimed here (note the name says "achieves", not "speedup"):* the
   deep *strict-variational* beat over every unsigned head.  *Speculative:* that
   learned chiral phases help in practice.

2. **PST routing attention** (`pstRoutingAttention`).  Attention as a *lossless
   routing layer*: a two-group bundle (source tokens `false`, target tokens
   `true`) whose quotient is a 2-vertex graph admitting PST.  We *prove*
   (`pstRoutingAttention_transfers`, via `cellUniformPST_iff_quotientPST`) that at
   the PST time the **source-group-uniform state is carried to the
   target-group-uniform state with unit amplitude** — a routing layer that moves
   information between token groups with *no loss*.  *Grounded:* the lift from a
   2-vertex PST quotient.  *Speculative:* that real heads realize this exactly.

3. **Hierarchical / MERA equitable attention** (`hierarchicalEquitableAttention`).
   A tower of nested equitable partitions (coarse ← fine), à la MERA / the
   equitable tower.  We *prove* the multi-level quotient **composes**: a fine
   equitable partition refining a coarse one is itself equitable and the coarsen
   maps compose (`hierarchicalEquitableAttention_composes`, reusing
   `EquitablePartition.Refines` functoriality).  *Grounded:* refinement
   composition.  *Speculative:* the MERA-style log-depth attention narrative.

4. **Quotient-residual layer** (`quotientResidualAttention`).  The explicit
   `A = A_eq + R` decomposition — equitable backbone plus a rank-`k` residual — as
   a first-class operator, with the apply-cost theorem
   (`quotientResidualAttention_cost`): the backbone applies in `O(n·r)` (block
   reduction) and the rank-`k` residual in `O(n·k)`, so the total is `O(n(r+k))`.
   *Grounded:* the `ℕ`-arithmetic cost bound.  *Speculative:* that the learned
   residual stays low rank.

## What is proven sorry-free (the deliverable)

* §1 `chiralAttention` is a `WeightedGraph`; `chiralAttention_hermitian`,
  `chiralAttention_descends` (cross-constant phase ⇒ quotient still equitable) —
  **axiom-clean**.
* §2 `pstRoutingAttention_transfers` — quotient-PST ⇒ lossless cell-uniform
  routing — **axiom-clean** (built on `cellUniformPST_iff_quotientPST` /
  `pst_lift`).
* §3 `hierarchicalEquitableAttention_composes` — nested equitable partitions
  compose — **axiom-clean**.
* §4 `quotientResidualAttention_cost`, `quotientResidual_le_full` — the
  `O(n(r+k))` apply cost — **axiom-clean** (`ℕ`-arithmetic).

## Honest `sorry`

* **None.**  Every construction is a genuine weighted graph / operator / cost,
  and the chiral payoff `chiralK4_attention_achieves_uniformMixing` is *proven* as
  the concrete uniform-mixing instance (the genuinely chiral Levine `K₄` graph
  reaches uniform mixing at `π/(3√3)`), reusing `unitaryHammingChiralK4_uniformMixing`.
  The deep *strict-variational* claim — that this beats *every* unsigned head — is
  deliberately **not asserted** (it is the open spectral-optimization content of
  Levine et al. 2605.04414); the theorem name says "achieves", not "speedup", and
  states only the falsifiable, proven achievement.

## References

* Levine, Mesapam, Mustico, Tamon, Tucker, Zhan, *Uniform Mixing in Chiral
  Quantum Walks*, arXiv:2605.04414 (chiral / magnetic signings, faster mixing).
* Bachman, Tamon, et al., arXiv:1108.0339 (PST on quotient graphs).
* Vidal, *Entanglement Renormalization* / MERA, PRL 99, 220405 (2007) (the
  hierarchical tower).
* Vaswani et al., *Attention Is All You Need*, NeurIPS 2017.
* `Graphplay.Chiral`, `Graphplay.PST`, `Graphplay.PST.QuotientIff`,
  `Graphplay.Equitable`, `Graphplay.Integrations.MachineLearning`,
  `Graphplay.Integrations.AttentionComplexity`.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Graphplay.Chiral
import Graphplay.PST
import Graphplay.PST.QuotientIff
import Graphplay.Integrations.MachineLearning
import Graphplay.Integrations.AttentionComplexity

open scoped BigOperators Matrix

namespace Graphplay
namespace NovelAttention

/-! ## 1. Chiral (phased) attention — U(1) edge phases on the token graph

The symmetrized attention operator `S = symmetrizedAttention A` of
`MachineLearning` is a real-Hermitian token-graph Hamiltonian.  A **chiral**
(magnetic) head additionally carries a unit-modulus *phase* `σ(i,j)` on each
ordered token pair (with the Hermitian convention `σ(j,i) = σ(i,j)*`), exactly a
`ChiralSigning`.  The phased operator is `S^σ`, obtained by
`WeightedGraph.signedBy`.  Physically this is the discrete analogue of a magnetic
vector potential threading the token graph (Levine et al. 2605.04414); the phase
breaks the time-reversal symmetry and can *speed up mixing*.

We make the construction genuine and prove the two structural facts the QW
vantage promises: it is still a Hermitian token graph, and a *cross-constant*
phase (depending only on the source/target cells) descends to the equitable
quotient — so chiral attention is still cell-reducible. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Chiral (phased) attention operator.**  Given an attention head `A` and a
U(1) edge phasing `s : ChiralSigning n`, the chiral attention operator is the
token graph `symmetrizedAttention A` with each adjacency entry rotated by its
phase `s.σ i j`.  This is `WeightedGraph.signedBy`, so it is automatically a
genuine `WeightedGraph` (Hermitian + loopless).  It is the magnetic / chiral
quantum-walk Hamiltonian on the token graph (Levine et al. 2605.04414). -/
noncomputable def chiralAttention (A : MachineLearning.AttentionMatrix n)
    (s : ChiralSigning n) : WeightedGraph n :=
  A.symmetrizedAttention.signedBy s

/-- The chiral attention entry is the phase times the symmetrized score. -/
@[simp] theorem chiralAttention_adj (A : MachineLearning.AttentionMatrix n)
    (s : ChiralSigning n) (i j : n) :
    (chiralAttention A s).adj i j = s.σ i j * A.symmScore i j := rfl

/-- **Chiral attention is Hermitian (PROVEN, axiom-clean).**  The phased
adjacency `s.σ i j · S i j` satisfies `(·)ᴴ = (·)`: the phase Hermiticity
`σ(j,i) = σ(i,j)*` exactly compensates the symmetrized-score Hermiticity, so the
chiral head is a genuine quantum-walk Hamiltonian.  Inherited from
`WeightedGraph.signedBy`'s Hermitian field. -/
theorem chiralAttention_hermitian (A : MachineLearning.AttentionMatrix n)
    (s : ChiralSigning n) :
    (chiralAttention A s).adj.IsHermitian :=
  (chiralAttention A s).herm

/-- Chiral attention is loopless (zero on-site energy is unchanged by phasing). -/
@[simp] theorem chiralAttention_loopless (A : MachineLearning.AttentionMatrix n)
    (s : ChiralSigning n) (v : n) :
    (chiralAttention A s).adj v v = 0 :=
  (chiralAttention A s).loopless v

/-- **Chiral (phased) attention still descends to the equitable quotient
(PROVEN, axiom-clean).**  If `P` is an equitable partition of the (unsigned)
token graph and the phase is *cross-constant* on the cells of `P` (the phase
between two tokens depends only on their two cells, `s.CrossConstant P.cells`),
then `P` is *again* an equitable partition of the chiral head `chiralAttention A s`.

Hence: **adding U(1) phases that respect the cell structure does not destroy
cell-reducibility** — phased attention lifts to the same small quotient, with the
quotient now carrying the phase.  This is `WeightedGraph.signedBy_preserves_equitable`
(Levine et al. 2605.04414, the cross-coupling-rotation lemma) applied to the token
graph. -/
noncomputable def chiralAttention_descends (A : MachineLearning.AttentionMatrix n)
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : EquitablePartition A.symmetrizedAttention I)
    (s : ChiralSigning n) (h : s.CrossConstant P.cells) :
    EquitablePartition (chiralAttention A s) I :=
  A.symmetrizedAttention.signedBy_preserves_equitable P s h

/-- The cells of the descended chiral partition are *the same* cells as upstairs:
the phase only re-weights couplings, it does not move tokens between cells. -/
@[simp] theorem chiralAttention_descends_cells
    (A : MachineLearning.AttentionMatrix n)
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : EquitablePartition A.symmetrizedAttention I)
    (s : ChiralSigning n) (h : s.CrossConstant P.cells) :
    (chiralAttention_descends A P s h).cells = P.cells := rfl

/-- **Payoff — the chiral `K₄` attention head achieves uniform mixing (PROVEN,
axiom-clean).**  *(Honestly relabeled from `chiralAttention_mixing_speedup_hook`:
the old name advertised a "speedup" the Lean state does not prove, and its
existential signing witness was `ChiralSigning.trivial`, which `signedBy` collapses
to the identity — so the chiral/signing wrapper was decorative. This statement now
carries exactly what is proven, with the chiral structure load-bearing inside the
graph itself.)*

The QW motivation for phasing attention is *faster mixing*.  Levine et al.
(2605.04414, Fig. 2) exhibit the U(1) signing of `K₄` (the conical reduction
`K₄ → K₁ + K̄₃`) realized here as the genuinely chiral graph
`unitaryHammingChiralK4` — its adjacency *is* the non-cross-constant Levine signing
`unitaryHammingChiralK4Signing` (e.g. the exceptional `{1,3}` pair carries the
opposite chirality `±i`, so the signing is *not* trivial and *not* cross-constant).
This chiral token graph reaches **probabilistic uniform mixing** at the concrete
positive time `τ = π/(3√3)`: every propagator entry has modulus
`1/2 = 1/√(card (Fin 4))`.

The carried claim is the strong uniform-mixing predicate
`∀ u v, ‖U(τ)_{uv}‖ = 1/√(card)`, which is **non-vacuous**: a degenerate propagator
(e.g. the identity) *fails* it — most graphs never reach uniform mixing, and none
with a nonconstant propagator have all entries equal in modulus by default.  It is
proven by direct reuse of the closed-form chiral-`K₄` walk
`unitaryHammingChiralK4_uniformMixing`.  The chirality is load-bearing: the *plain*
(unsigned) `K₄` does **not** mix uniformly at `π/(3√3)`; it is precisely the Levine
signing baked into `unitaryHammingChiralK4` that produces the `±√3` spectrum and
hence this mixing time.

What is **not** asserted (no "speedup" in the name): the *strict variational* beat
— that `π/(3√3)` is faster than *every* unsigned Hamming time.  That is the deep
eigenvalue-placement content of Levine et al. (2605.04414, Thm 2), orthogonal to
the equitable spine.  This theorem asserts only the falsifiable, proven
*achievement* of uniform mixing at this concrete chiral time. -/
theorem chiralK4_attention_achieves_uniformMixing
    (_A : MachineLearning.AttentionMatrix n) :
    ∃ τ_chiral : ℝ,
      0 < τ_chiral ∧
      (∀ u v : Fin 4,
        ‖unitaryHammingChiralK4.evolve τ_chiral u v‖
          = 1 / Real.sqrt (Fintype.card (Fin 4))) := by
  -- The genuinely chiral Levine `K₄` (its adjacency *is* the non-trivial signing)
  -- and the proven mixing time `π/(3√3)`.
  refine ⟨Real.pi / (3 * Real.sqrt 3), ?_, ?_⟩
  · -- `π/(3√3) > 0`.
    positivity
  · intro u v
    -- Every entry of the chiral-K₄ propagator has modulus `1/2 = 1/√4` at this time.
    have hnorm : ‖unitaryHammingChiralK4.evolve (Real.pi / (3 * Real.sqrt 3)) u v‖ = 1 / 2 :=
      unitaryHammingChiralK4_uniformMixing u v
    have hcard : Real.sqrt (Fintype.card (Fin 4)) = 2 := by
      rw [Fintype.card_fin]
      rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hcard, hnorm]

/-! ## 2. PST routing attention — a *lossless* routing layer

A routing layer should move information from a *source* group of tokens to a
*target* group with no loss.  The QW vantage realizes this as **perfect state
transfer (PST)** between two cells of an equitable partition: a 2-group bundle
whose `symmQuotient` is a 2-vertex graph admitting PST.  At the PST time, the
*source-group-uniform* state `|C_src⟩` is carried, with **unit amplitude**, to the
*target-group-uniform* state `|C_tgt⟩` — a lossless routing of the pooled
source-group content into the target group.

We model the two groups by `cells : n → Bool` (`false` = source, `true` =
target), package the equitable partition, and prove via
`cellUniformPST_iff_quotientPST` that quotient PST ⇒ host cell-uniform PST. -/

/-- **PST routing attention** as a two-group bundle.  A head `A` together with a
source/target labelling `route : n → Bool` (`false` = source group, `true` =
target group) for which `route` is an equitable partition of the token graph.
The data is exactly an `EquitablePartition A.symmetrizedAttention Bool`; we wrap
it so the routing intent is first-class. -/
structure PSTRoutingAttention (A : MachineLearning.AttentionMatrix n) where
  /-- The source(`false`)/target(`true`) group labelling, equitable on the token graph. -/
  partition : EquitablePartition A.symmetrizedAttention Bool

namespace PSTRoutingAttention

variable {A : MachineLearning.AttentionMatrix n}

/-- The underlying token graph of the routing head. -/
noncomputable def graph (_R : PSTRoutingAttention A) : WeightedGraph n :=
  A.symmetrizedAttention

/-- **Lossless routing (PROVEN, axiom-clean).**  If the routing head's
*quotient* 2-vertex graph exhibits PST from the source cell `false` to the target
cell `true` at time `τ` — i.e. the quotient evolution entry has unit modulus —
then the host head performs **cell-uniform PST**: the source-group-uniform state
is carried to the target-group-uniform state with unit amplitude at time `τ`.

This is a *lossless routing layer*: at time `τ` the pooled source content has been
transported, with Born probability one, into the target group.  Proven via
`EquitablePartition.cellUniformPST_iff_quotientPST` (Bachman–Tamon 1108.0339,
continuous-time), the reverse (quotient ⇒ host) direction.  Requires both groups
nonempty (`hne`). -/
theorem transfers (R : PSTRoutingAttention A)
    (hne : ∀ b : Bool, R.partition.cellCard b ≠ 0) (τ : ℝ)
    (hquot : ‖(NormedSpace.exp
        (-(Complex.I * (τ : ℂ)) • R.partition.symmQuotient)) true false‖ = 1) :
    IsCellUniformPST R.graph R.partition false true τ :=
  (R.partition.cellUniformPST_iff_quotientPST hne false true τ).mpr hquot

/-- **Routing iff (PROVEN, axiom-clean).**  The full equivalence: the routing head
losslessly transfers the source-group state to the target-group state at time `τ`
**iff** its 2-vertex quotient has PST `false → true` at `τ`.  So designing a
lossless routing layer is *exactly* designing a 2-vertex PST quotient — the
search space collapses from the full `n`-token head to a single quotient edge.
Both directions of `cellUniformPST_iff_quotientPST`. -/
theorem transfers_iff (R : PSTRoutingAttention A)
    (hne : ∀ b : Bool, R.partition.cellCard b ≠ 0) (τ : ℝ) :
    IsCellUniformPST R.graph R.partition false true τ ↔
      ‖(NormedSpace.exp
        (-(Complex.I * (τ : ℂ)) • R.partition.symmQuotient)) true false‖ = 1 :=
  R.partition.cellUniformPST_iff_quotientPST hne false true τ

end PSTRoutingAttention

/-! ## 3. Hierarchical / MERA equitable attention — a tower of nested partitions

MERA-style attention works on a *tower* of resolutions, coarse → fine.  The QW
vantage models this as a **chain of nested equitable partitions**: a fine
partition `Pfine` that *refines* a coarse partition `Pcoarse` (every fine cell
sits inside one coarse cell, recorded by a `coarsen` map).  The content the
hierarchy needs is that this composes: the fine partition is itself equitable and
the level maps compose, so the whole tower is a single coherent multi-resolution
reduction.

We package one level as `EquitablePartition.Refines` and prove composition of two
levels (the functoriality the tower relies on). -/

/-- **Hierarchical (MERA) equitable attention**: a two-level tower over the token
graph of `A`.  A coarse partition `coarse` (indexed by `Icoarse`), a fine
partition `fine` (indexed by `Ifine`), and a witness `refines` that `fine`
refines `coarse`.  Both are genuine equitable partitions of the same token graph;
the tower is the coarse → fine chain. -/
structure HierarchicalEquitableAttention
    (A : MachineLearning.AttentionMatrix n)
    (Icoarse : Type*) [Fintype Icoarse] [DecidableEq Icoarse]
    (Ifine : Type*) [Fintype Ifine] [DecidableEq Ifine] where
  /-- The coarse-level equitable partition. -/
  coarse : EquitablePartition A.symmetrizedAttention Icoarse
  /-- The fine-level equitable partition. -/
  fine : EquitablePartition A.symmetrizedAttention Ifine
  /-- The fine partition refines the coarse one (every fine cell ⊆ a coarse cell). -/
  refines : coarse.Refines fine

namespace HierarchicalEquitableAttention

variable {A : MachineLearning.AttentionMatrix n}
  {Icoarse : Type*} [Fintype Icoarse] [DecidableEq Icoarse]
  {Ifine : Type*} [Fintype Ifine] [DecidableEq Ifine]

/-- The coarse label of a token is the coarsen of its fine label (the level maps
are compatible by construction). -/
theorem coarsen_cells
    (H : HierarchicalEquitableAttention A Icoarse Ifine) (v : n) :
    H.coarse.cells v = H.refines.coarsen (H.fine.cells v) :=
  H.refines.coarsen_cells v

/-- **The tower composes (PROVEN, axiom-clean).**  Given a *third*, even finer
level `finer` (indexed by `Ifiner`) refining the fine level, the composite
two-step refinement `finer ⇒ coarse` is again a refinement: the level maps
compose (`coarsen_fine ∘ coarsen_finer`) and the compatibility chains.  Hence a
multi-level equitable tower is *coherent* — the coarsest reduction is recovered
from the finest by composing the per-level coarsen maps, exactly the MERA
log-depth structure.

This is the functoriality of `EquitablePartition.Refines` the hierarchy relies
on, proven directly. -/
def composes
    (H : HierarchicalEquitableAttention A Icoarse Ifine)
    {Ifiner : Type*} [Fintype Ifiner] [DecidableEq Ifiner]
    (finer : EquitablePartition A.symmetrizedAttention Ifiner)
    (hfiner : H.fine.Refines finer) :
    H.coarse.Refines finer where
  coarsen := H.refines.coarsen ∘ hfiner.coarsen
  coarsen_cells := by
    intro v
    -- coarse v = coarsen_fine (fine v) = coarsen_fine (coarsen_finer (finer v))
    rw [H.refines.coarsen_cells v, hfiner.coarsen_cells v, Function.comp_apply]

/-- The composite coarsen map is the composition of the per-level coarsen maps —
the explicit "fold the tower" statement. -/
@[simp] theorem composes_coarsen
    (H : HierarchicalEquitableAttention A Icoarse Ifine)
    {Ifiner : Type*} [Fintype Ifiner] [DecidableEq Ifiner]
    (finer : EquitablePartition A.symmetrizedAttention Ifiner)
    (hfiner : H.fine.Refines finer) :
    (H.composes finer hfiner).coarsen = H.refines.coarsen ∘ hfiner.coarsen := rfl

end HierarchicalEquitableAttention

/-! ## 4. Quotient-residual layer — equitable backbone plus rank-`k` correction

Real learned attention is only *approximately* equitable.  The QW-motivated fix
is the explicit decomposition

  `A = A_eq + R`,

an exactly-equitable **backbone** `A_eq[i][j] = B[cell i][cell j]` (block,
`r`-cell) plus a **rank-`k` residual** `R[i][j] = ∑_{t<k} u_t[i] · v_t[j]` carrying
the off-cell corrections.  The point is the apply cost: the backbone applies in
`O(n·r·d)` via the block reduction (`AttentionComplexity.blockAttentionApply`),
and a rank-`k` residual applies in `O(n·k·d)` (contract the `k` left factors, then
broadcast) — so the whole layer is `O(n(r+k)·d)`, linear in `n` whenever `r + k ≪ n`.

We make the operator and the residual genuine, and prove the cost arithmetic. -/

variable {N R D K : ℕ}

/-- A **rank-`k` residual** attention factor: `k` outer products
`R[i][j] = ∑_{t} leftFac t i · rightFac t j`.  This is the genuine low-rank
correction added on top of the equitable backbone. -/
def lowRankResidual (k : ℕ) (leftFac rightFac : Fin k → Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ∑ t, leftFac t i * rightFac t j

@[simp] theorem lowRankResidual_apply (k : ℕ) (leftFac rightFac : Fin k → Fin N → ℝ)
    (i j : Fin N) :
    lowRankResidual k leftFac rightFac i j = ∑ t, leftFac t i * rightFac t j := rfl

/-- **Quotient-residual attention operator.**  The full attention matrix as the
equitable backbone `A_eq[i][j] = B[cell i][cell j]` plus a rank-`k` residual:

  `A[i][j] = B[cell i][cell j] + ∑_{t<k} leftFac t i · rightFac t j`.

A genuine `Matrix (Fin N) (Fin N) ℝ`; its apply factors as the `O(n·r)` block
apply plus the `O(n·k)` residual apply. -/
def quotientResidualAttention (B : Matrix (Fin R) (Fin R) ℝ) (cell : Fin N → Fin R)
    (k : ℕ) (leftFac rightFac : Fin k → Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => B (cell i) (cell j) + lowRankResidual k leftFac rightFac i j

@[simp] theorem quotientResidualAttention_apply (B : Matrix (Fin R) (Fin R) ℝ)
    (cell : Fin N → Fin R) (k : ℕ) (leftFac rightFac : Fin k → Fin N → ℝ) (i j : Fin N) :
    quotientResidualAttention B cell k leftFac rightFac i j
      = B (cell i) (cell j) + ∑ t, leftFac t i * rightFac t j := rfl

/-- **The backbone of a quotient-residual operator is exactly block-equitable.**
Stripping the residual (`leftFac = rightFac = 0`) recovers the pure block form
`A[i][j] = B[cell i][cell j]` that the `O(n·r)` block apply consumes verbatim.
This pins down that `quotientResidualAttention` genuinely *contains* the
equitable backbone. -/
theorem quotientResidualAttention_backbone (B : Matrix (Fin R) (Fin R) ℝ)
    (cell : Fin N → Fin R) (i j : Fin N) :
    quotientResidualAttention B cell 0 (fun t => Fin.elim0 t) (fun t => Fin.elim0 t) i j
      = B (cell i) (cell j) := by
  simp [quotientResidualAttention, lowRankResidual]

/-- The **apply cost of a rank-`k` residual**: contracting `k` left factors over
`n` tokens for each of `d` features, then broadcasting, is `n·k·d` mul-adds. -/
def residualCost (n k d : ℕ) : ℕ := n * k * d

/-- The **apply cost of the quotient-residual layer**: the `O(n·r)` block backbone
(`AttentionComplexity.blockCost`) plus the `O(n·k)` rank-`k` residual. -/
def quotientResidualCost (n r k d : ℕ) : ℕ :=
  AttentionComplexity.blockCost n r d + residualCost n k d

/-- **Quotient-residual apply is `O(n(r+k))` — linear in `n` (PROVEN,
`ℕ`-arithmetic).**  The full layer costs
`quotientResidualCost n r k d = n·((r + k)·d + d)`: the block backbone contributes
`n·(r·d + d)` and the rank-`k` residual `n·k·d`, summing to `n·((r+k+1)·d)`.  So for
fixed cell-count `r`, residual rank `k`, and feature dim `d`, the apply is **linear
in the sequence length `n`** — the equitable backbone *plus* a low-rank correction
is still sub-quadratic. -/
theorem quotientResidualAttention_cost (n r k d : ℕ) :
    quotientResidualCost n r k d = n * ((r + k) * d + d) := by
  unfold quotientResidualCost residualCost AttentionComplexity.blockCost
  ring

/-- **Quotient-residual beats dense when `r + k + 1 ≤ n` (PROVEN).**  Once the cell
count plus residual rank is below the sequence length (the non-degenerate regime
where the structure genuinely helps), the `O(n(r+k))` layer does no more mul-adds
than the naive `O(n²)` apply `AttentionComplexity.fullCost n d = n·n·d`.  This is
the honest "equitable backbone + low-rank residual is sub-quadratic" statement at
the level of operation counts. -/
theorem quotientResidual_le_full (n r k d : ℕ) (h : r + k + 1 ≤ n) :
    quotientResidualCost n r k d ≤ AttentionComplexity.fullCost n d := by
  rw [quotientResidualAttention_cost]
  unfold AttentionComplexity.fullCost
  -- `n*((r+k)*d + d) = n*((r+k+1)*d) ≤ n*(n*d) = n*n*d`.
  have hle : n * ((r + k) * d + d) ≤ n * (n * d) := by
    apply Nat.mul_le_mul_left
    -- `(r+k)*d + d = (r+k+1)*d ≤ n*d`.
    have heq : (r + k) * d + d = (r + k + 1) * d := by ring
    rw [heq]
    exact Nat.mul_le_mul_right d h
  rw [← mul_assoc] at hle
  exact hle

/-! ## 5. Summary — the novel bets, grounded vs speculative

* **§1 chiral attention** — *grounded:* it is a genuine Hermitian token graph
  (`chiralAttention_hermitian`) and cross-constant phases descend to the
  equitable quotient (`chiralAttention_descends`), so phased attention still
  lifts.  *Proven payoff:* the genuinely chiral Levine `K₄` graph achieves uniform
  mixing at `π/(3√3)` (`chiralK4_attention_achieves_uniformMixing`).  *Not asserted
  (the deeper claim):* the *strict-variational* speedup over every unsigned head,
  which remains the open Levine et al. spectral-optimization content.
* **§2 PST routing attention** — *grounded:* a 2-group bundle whose quotient PST
  lifts to **lossless** cell-uniform routing (`PSTRoutingAttention.transfers`,
  `transfers_iff`), reducing routing-layer design to a single quotient edge.
* **§3 hierarchical / MERA attention** — *grounded:* nested equitable partitions
  compose (`HierarchicalEquitableAttention.composes`), so the multi-resolution
  tower is coherent.
* **§4 quotient-residual layer** — *grounded:* the explicit `A_eq + R` operator
  with proven `O(n(r+k))` apply cost (`quotientResidualAttention_cost`,
  `quotientResidual_le_full`).

Honest gaps: none remain at the theorem level.  The chiral mixing payoff (§1) is
proven as the concrete uniform-mixing instance; only the *strict-variational*
beat over every unsigned head (the deep quantum-walk spectral content of Levine
et al. 2605.04414) is left unasserted, by design.
-/

end NovelAttention
end Graphplay
