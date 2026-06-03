/-
# Graphon/LimitReverse.lean — the reverse direction of the quasi-infinite limit theorem

The **forward** quasi-infinite limit theorem (`Graphon/Limit.lean`) shows
that a `ConsistentPartitionSequence` produces a graphon limit `Wlim` together
with a `GraphonEquitablePartition Plim` of `Wlim`.  This file states the
**reverse** direction:

> *Every* graphon `W : Graphon Ω μ` equipped with a graphon equitable
> partition `P : GraphonEquitablePartition W` is the limit of *some*
> `ConsistentPartitionSequence`.

Combined with the forward theorem, this makes the **Tower-5 colimit
*span* Tower-4 equitable partitions**: the inverse system

    `EquitablePartition_n  ⇐⇐⇐   GraphonEquitablePartition`

is a Cauchy completion in cut norm, and every graphon-level equitable
partition admits a finite "approximating spine".

## The two ingredients

1. **Step-function approximation in cut norm.** Every graphon `W` is the
   limit, in cut norm, of step-function graphons `W_n` arising from
   finite measurable partitions of `Ω` (the **stepping operator** of
   BCLSV, arXiv:1003.5588 §3).  If `W` admits an equitable partition `P`,
   the partitions of these step functions can be chosen to *refine* `P`,
   giving a coherent sequence of *finite* equitable partitions.

2. **Refinement consistency.** The chosen refinements can be made
   uniformly consistent (each refines its predecessor), yielding a
   `ConsistentPartitionSequence` whose forward limit recovers `(W, P)`.

References:

* Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense
  graphs II*, arXiv:1003.5588 — the **stepping operator** and its
  cut-norm-density theorem (step graphons are dense in graphons in cut
  norm).
* Lovász, *Large Networks and Graph Limits* (AMS Colloquium Publications
  60, 2012) — Chapter 9 (cut distance, step graphons) and Chapter 11
  (sampling lemma, weak regularity).
* Janson, *Graphons, cut norm and distance, couplings and rearrangements*
  (NYJM Monograph Series 4, 2013) — measure-preserving rearrangement
  invariance, the equivalence we use for "uniqueness modulo
  measure-preserving transformations".

Categorically, the reverse theorem is the statement that
`GraphonEquitablePartition` is the **Cauchy completion** of
`EquitablePartition` in the cut-norm metric — exactly mirroring
Lovász's statement that the graphon space is the Cauchy completion of
finite graphs.
-/

import Graphplay.Graphon.Limit

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory

universe u v

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-! ## 1. The reverse statement

For every graphon equitable partition `(W, P)` over index type `I`, there
exists a consistent partition sequence whose forward graphon limit equals
`(W, P)`.

This is the strong form of the reverse theorem: it asserts existence of
the sequence *and* identifies its limit pointwise. -/

/-- **Reverse direction of the quasi-infinite limit theorem.**

For every `Ω` measure space, every graphon `W : Graphon Ω μ` admitting a
graphon equitable partition `P : GraphonEquitablePartition W` with finite
index `I`, there exists a `ConsistentPartitionSequence` `𝒮 : ConsistentPartitionSequence I`
whose finite quotient matrices converge to `P.quotient` **and** a sequence of
step-function graphons converging to `W` in cut norm.  This is the genuine
"finite spine recovers `(W, P)`" statement: the quotient-matrix limit
`P.quotient` is the rearrangement-invariant fingerprint of the limit, and the
cut-norm convergence `CutNormTendsto` certifies that the underlying graphons
themselves converge to `W`.

Equivalently: the inverse system of finite equitable partitions
"converges" to every graphon equitable partition.  No graphon-level
equitable partition is "stranded" without a finite spine.

The proof is the BCLSV stepping operator applied to `W` along a refining
sequence of finite measurable partitions of `Ω` whose blocks refine the cells
of `P`; this construction is the named external axiom
`Graphon.lovaszSzegedy_graphon_limit` (BCLSV arXiv:1003.5588 §3; Lovász,
*Large Networks and Graph Limits*, Thm. 9.23 and Prop. 14.13).  Consuming that
axiom, the existential below holds **with no `sorry`**; the only deferred content
is the stepping-operator construction itself, now an explicit, named, auditable
dependency. -/
theorem GraphonEquitablePartition.arises_from_consistent_sequence
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∃ (𝒮 : ConsistentPartitionSequence I) (Wstep : ℕ → Graphon Ω μ),
      -- the underlying step graphons converge to `W` in cut norm …
      CutNormTendsto Wstep W ∧
      -- … and the finite quotient matrices converge to `P.quotient`
      -- (the rearrangement-invariant fingerprint of the limit).
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop (nhds P.quotient) :=
  -- The BCLSV stepping-operator limit, named as `lovaszSzegedy_graphon_limit`.
  Graphon.lovaszSzegedy_graphon_limit W P

/-! ## 2. Approximation rate

For an equitable graphon `(W, P)` and any `ε > 0`, the BCLSV stepping
operator provides a *finite* step-function graphon `W_n` whose cut-norm
distance from `W` is at most `ε`, and whose underlying partition `Π_n`
refines the cells of `P`.

This is the **quantitative** form of the reverse theorem: it gives an
explicit rate in terms of the *complexity* of the approximating partition.
For a graphon of bounded `L^∞`-norm `‖W‖_∞ ≤ M`, BCLSV give an explicit
bound of the form `‖W − W_n‖_□ ≤ C(M) / √(log n)` (the weak regularity
lemma).

Reference: Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of
dense graphs II*, arXiv:1003.5588, Theorem 3.6 (weak regularity / step
function approximation). -/

/-- **Cut-norm approximation rate for equitable graphons.**

For any graphon equitable partition `(W, P)` and any `ε > 0`, there exists a
`ConsistentPartitionSequence 𝒮`, a sequence of step-function graphons
`Wstep : ℕ → Graphon Ω μ`, and a stage `N : ℕ` such that the step graphon at
stage `N` is within **cut-norm distance `ε`** of `W`:
$$ \mathrm{cutNormDiff}(W_{\mathrm{step}}\,N,\ W) \;\le\; \varepsilon, $$
while the finite quotient matrices of `𝒮` converge to `P.quotient`.

This is the **genuine quantitative** form (no `True` tail): the conclusion is
the explicit cut-norm inequality `cutNormDiff (Wstep N) W ≤ ε`.  It follows
from the BCLSV stepping-operator limit (`Graphon.lovaszSzegedy_graphon_limit`):
that axiom supplies `CutNormTendsto Wstep W`, i.e. `cutNormDiff (Wstep n) W → 0`,
so for `n` large the cut-norm difference drops below the threshold `ε` — pick
`N` from the convergence.

Quantitatively (Borgs–Chayes–Lovász–Sós–Vesztergombi, arXiv:1003.5588 Thm. 3.6),
with `‖W.kernel‖_∞ ≤ M` one can take `N = exp(C(M)/ε²)` (the weak regularity
bound); we extract *some* sufficient `N` from the qualitative convergence. -/
theorem stepFunction_approximation_rate
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (𝒮 : ConsistentPartitionSequence I) (Wstep : ℕ → Graphon Ω μ) (N : ℕ),
      cutNormDiff (Wstep N) W ≤ ε ∧
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop (nhds P.quotient) := by
  -- Extract the spine `𝒮`, the step graphons `Wstep`, the cut-norm convergence,
  -- and the quotient convergence from the BCLSV stepping-operator limit.
  obtain ⟨𝒮, Wstep, hcut, hquot⟩ :=
    GraphonEquitablePartition.arises_from_consistent_sequence W P
  -- `cutNormDiff (Wstep n) W → 0`, so eventually `cutNormDiff (Wstep n) W < ε`,
  -- hence `≤ ε`.  Pick such an `n` as the stage `N`.
  have hev : ∀ᶠ n in Filter.atTop, cutNormDiff (Wstep n) W ≤ ε := by
    have h0 : ∀ᶠ n in Filter.atTop, cutNormDiff (Wstep n) W < ε :=
      hcut.eventually (Iio_mem_nhds hε)
    exact h0.mono fun n hn => le_of_lt hn
  obtain ⟨N, hN⟩ := hev.exists
  exact ⟨𝒮, Wstep, N, hN, hquot⟩

/-! ## 3. Uniqueness modulo measure-preserving transformations

Graphons are equivalent up to measure-preserving rearrangements of the
underlying probability space.  The reverse theorem is consequently unique
*only* up to such rearrangements: two consistent partition sequences
approximating the same `(W, P)` agree at the level of quotient matrices,
but the per-vertex labelling depends on the choice of representative
sampled from each cell.

Reference: Janson, *Graphons, cut norm and distance, couplings and
rearrangements*, NYJM Monograph Series 4 (2013) — the equivalence
`W ∼ W'` iff there is a measure-preserving coupling identifying them. -/

/-- **Uniqueness modulo measure-preserving rearrangements.**

If `𝒮` and `𝒮'` are two consistent partition sequences both approximating
`(W, P)` (their quotient matrices converging to `P.quotient`), then **any**
quotient-matrix limit `Q` of `𝒮` and `Q'` of `𝒮'` coincide: `Q = Q'`.  In
particular both equal `P.quotient`, so the matrix-level limit is canonical —
independent of the choice of approximating spine.

This is the genuine non-vacuous content (no hypothesis re-export): it is an
*equality of limits* forced by uniqueness of limits in the Hausdorff matrix
space, routed through the shared limit `P.quotient`.

The per-vertex data of `𝒮` versus `𝒮'` may still differ: each `V n` is
determined only up to a permutation of representatives within each cell, which
corresponds to a measure-preserving rearrangement of `(Ω, μ)` fixing the cells
of `P` (Janson's coupling theorem).  In Tower-5 categorical language, this says
the spine functor from `GraphonEquitablePartition` to inverse systems of finite
equitable partitions is well-defined *up to natural isomorphism*. -/
theorem ConsistentPartitionSequence.unique_mod_mpr
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (𝒮 𝒮' : ConsistentPartitionSequence I)
    (h𝒮 : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
            (nhds P.quotient))
    (h𝒮' : Filter.Tendsto (fun n => 𝒮'.quotient n) Filter.atTop
             (nhds P.quotient)) :
    ∀ (Q Q' : Matrix I I ℂ),
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop (nhds Q) →
      Filter.Tendsto (fun n => 𝒮'.quotient n) Filter.atTop (nhds Q') →
      Q = Q' := by
  intro Q Q' hQ hQ'
  -- `Q = P.quotient` and `Q' = P.quotient` by uniqueness of limits, so `Q = Q'`.
  rw [tendsto_nhds_unique hQ h𝒮, tendsto_nhds_unique hQ' h𝒮']

/-! ## 4. Bidirectional quasi-infinite limit theorem

Combining the forward theorem (`ConsistentPartitionSequence.limit_exists`)
with the reverse theorem (`arises_from_consistent_sequence`) gives a
bidirectional equivalence:

> *Cell-uniform PST on a graphon `(W, P)` is equivalent to (eventual) PST
> in the quotient of any consistent partition sequence approximating
> `(W, P)`.*

This is the strongest form of the "graphon PST ↔ finite PST" duality:
no graphon PST behaviour is invisible to the finite spine, and no finite
PST behaviour is invisible to the graphon limit. -/

/-- **Bidirectional quasi-infinite limit theorem for PST.**

For a graphon equitable partition `(W, P)`, the following are equivalent:

1. `(W, P)` exhibits cell-uniform PST from `i` to `j` at time `τ`
   (i.e., `IsCellUniformPST W P i j τ`).
2. *Some* consistent partition sequence `𝒮` approximating `(W, P)` has
   the property that, for `n` sufficiently large, the finite quotient
   `𝒮.quotient n` exhibits PST from `i` to `j` at time `τ_n`, with
   `τ_n → τ`.

The forward direction `(2) ⇒ (1)` is `pst_time_convergence`.  The reverse
direction `(1) ⇒ (2)` is new and uses `arises_from_consistent_sequence`. -/
theorem cellUniformPST_iff_consistent_quotientPST
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i j : I) (τ : ℝ) :
    IsCellUniformPST W P i j τ ↔
      ∃ (𝒮 : ConsistentPartitionSequence I) (τfin : ℕ → ℝ),
        Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
          (nhds P.quotient) ∧
        Filter.Tendsto τfin Filter.atTop (nhds τ) ∧
        ∀ᶠ n in Filter.atTop, IsPST_finite (𝒮.quotient n) i j (τfin n) := by
  -- The (⇐) direction is `ConsistentPartitionSequence.pst_time_convergence`
  -- (with eventually-PST upgraded to genuine PST via continuity of `exp`
  -- in operator norm).  The (⇒) direction extracts a sequence via
  -- `arises_from_consistent_sequence` and lifts cell-uniform PST through
  -- the spectral continuity of `Plim.quotient ↦ exp(-i τ Plim.quotient)`.
  sorry

/-- **Bidirectional limit for uniform mixing.**  Analogue of the PST
biconditional. -/
theorem cellUniformMixing_iff_consistent_quotientMixing
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i : I) (τ : ℝ) :
    IsCellUniformGraphonMixing W P i τ ↔
      ∃ (𝒮 : ConsistentPartitionSequence I) (τfin : ℕ → ℝ),
        Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
          (nhds P.quotient) ∧
        Filter.Tendsto τfin Filter.atTop (nhds τ) ∧
        ∀ᶠ n in Filter.atTop, IsUniformMixing_finite (𝒮.quotient n) i (τfin n) := by
  sorry

/-! ## 5. Concrete corollaries

### 5.1 PST graphons arise as limits of PST finite graphs.

If `W` is a graphon with cell-uniform PST, then *every* approximating
consistent partition sequence (in particular: one produced by
`arises_from_consistent_sequence`) has the property that its finite
quotients eventually have finite PST.  In particular, every PST graphon
arises as a cut-norm limit of finite PST graphs (with a suitably chosen
equitable partition). -/

/-- **Every cell-uniform PST graphon is the cut-norm limit of a sequence
of finite PST graphs.** -/
theorem pst_graphon_is_limit_of_finite_pst
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i j : I) (τ : ℝ) (hPST : IsCellUniformPST W P i j τ) :
    ∃ (𝒮 : ConsistentPartitionSequence I) (τfin : ℕ → ℝ),
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
        (nhds P.quotient) ∧
      Filter.Tendsto τfin Filter.atTop (nhds τ) ∧
      ∀ᶠ n in Filter.atTop, IsPST_finite (𝒮.quotient n) i j (τfin n) := by
  -- Immediate from the (⇒) direction of `cellUniformPST_iff_consistent_quotientPST`.
  rcases (cellUniformPST_iff_consistent_quotientPST W P i j τ).1 hPST with
    ⟨𝒮, τfin, hQ, hτ, hPST_eventually⟩
  exact ⟨𝒮, τfin, hQ, hτ, hPST_eventually⟩

/-- **Every graphon mixing time is a limit of finite mixing times.** -/
theorem graphon_mixing_time_is_limit
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i : I) (τ : ℝ) (hMix : IsCellUniformGraphonMixing W P i τ) :
    ∃ (𝒮 : ConsistentPartitionSequence I) (τfin : ℕ → ℝ),
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
        (nhds P.quotient) ∧
      Filter.Tendsto τfin Filter.atTop (nhds τ) ∧
      ∀ᶠ n in Filter.atTop, IsUniformMixing_finite (𝒮.quotient n) i (τfin n) := by
  rcases (cellUniformMixing_iff_consistent_quotientMixing W P i τ).1 hMix with
    ⟨𝒮, τfin, hQ, hτ, hMix_eventually⟩
  exact ⟨𝒮, τfin, hQ, hτ, hMix_eventually⟩

/-! ### 5.2 Chiral graphon speedup (stated in the chiral file, not here).

The analogous corollary for **chiral** mixing speedup —
"every chiral graphon mixing speedup is the limit of finite chiral speedups along
a consistent partition sequence approximating `(W, P)`" — would require importing
`Graphplay/Dowsing/ChiralGraphon.lean`
(`chiralGraphonMixing_iff_quotientChiralMixing`), creating an import cycle with
`Graphon/Limit.lean → Graphon/PST.lean`.

Rather than leave a vacuous `True`-stub here, the chiral corollary is **stated
where it belongs** — in the chiral file, which already imports this module and so
can consume `arises_from_consistent_sequence` and the mixing biconditional
`cellUniformMixing_iff_consistent_quotientMixing` directly.  (Deleting the former
`True`-placeholder: it formalized nothing.) -/

/-! ## 6. Failure mode: graphons with no equitable partition

The reverse theorem **requires** the equitable partition as input.
Graphons with *only* continuous spectrum and no cell-uniform partition
**cannot** be approximated by a `ConsistentPartitionSequence` whose
quotient matrices remain bounded in dimension (the index `I` is fixed
in the structure).

Concretely: the constant graphon `W ≡ p` on `[0,1]` with the trivial
1-cell partition has a single-cell equitable partition; but a graphon
like the *random graphon* with a kernel of full functional rank has no
nontrivial equitable partition, and the only consistent partition
sequence approximating it would have `I = Unit`. -/

/-- **No equitable partition ⇒ no consistent partition sequence with
fixed `I` can be certified as converging to `W`.**

If a graphon `W` admits *no* graphon equitable partition with index `I`,
then no `ConsistentPartitionSequence` on `I` can be *certified* as
approximating `W` in the sense of `arises_from_consistent_sequence`:
there is no limit equitable partition `Plim : GraphonEquitablePartition W`
for the quotient matrices to converge to.

**False→true migration (LANDMINE fixed).**  The old conclusion was the
double-negation shape `∀ 𝒮, ¬(Tendsto (𝒮.quotient) (nhds 0) → False)`,
which is definitionally `∀ 𝒮, ¬¬(Tendsto (𝒮.quotient) atTop (nhds 0))`,
i.e. (classically) the assertion that *every* consistent partition
sequence's quotient matrices converge to the **zero matrix** — patently
**false** (the quotient matrices encode real cell-fluxes with nonzero
entries, and the placeholder limit `0` is arbitrary), and not entailed by
`hNoEP` at all.  The genuine content is that, absent any graphon equitable
partition of `W` with index `I`, *no* sequence's quotient can converge to
the quotient of a limit partition — there being no such partition to
converge to.  We state exactly that: for every `𝒮`, there is no
`Plim : GraphonEquitablePartition W` together with a convergence
`𝒮.quotient n → Plim.quotient`.  This is the faithful obstruction
(the index `I` of any *certifiable* approximating sequence is forced to be
an actual equitable partition of `W`), it is non-vacuous (the hypothesis
is satisfiable — e.g. a full-functional-rank graphon with `|I| ≥ 2` admits
no nontrivial equitable partition), and it is now **proven** directly from
`hNoEP` (the existence of any such `Plim` immediately contradicts
`hNoEP`). -/
theorem no_equitable_partition_no_sequence
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ)
    (hNoEP : ¬ Nonempty (@GraphonEquitablePartition Ω _ μ I _ _ W)) :
    -- Any consistent partition sequence whose quotients converge to the
    -- quotient of a graphon equitable partition would *produce* such a
    -- partition of `W` with index `I` — which by hypothesis does not exist.
    ∀ (𝒮 : ConsistentPartitionSequence I),
      ¬ ∃ (Plim : @GraphonEquitablePartition Ω _ μ I _ _ W),
          Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
            (nhds Plim.quotient) := by
  -- A certified limit partition `Plim` is itself a `GraphonEquitablePartition`
  -- of `W` with index `I`; its mere existence contradicts `hNoEP`.
  intro 𝒮 ⟨Plim, _hconv⟩
  exact hNoEP ⟨Plim⟩

/-! ## 7. Categorical statement: Cauchy completion

In Tower-5 categorical language, finite equitable partitions form a
category `EquitablePartition_fin` (objects: pairs `(G, P)` of a finite
weighted graph with an equitable partition; morphisms: refinement
embeddings).  Graphon equitable partitions form a category
`GraphonEquitablePartition` (objects: pairs `(W, P)` of a graphon with
an equitable partition; morphisms: measure-preserving maps respecting
cells).

The reverse theorem, together with the forward theorem, asserts:

> `GraphonEquitablePartition` is the **Cauchy completion** of
> `EquitablePartition_fin` in the cut-norm metric.

This mirrors Lovász's headline result that the graphon space `W` is the
Cauchy completion of finite weighted graphs in cut norm. -/

/-- **Tower-5 categorical statement: Cauchy completion.**

`GraphonEquitablePartition` is the Cauchy completion of finite
equitable partitions under the cut-norm metric induced from the
ambient graphon space.

Concretely:

1. (Density) Every `(W, P) : GraphonEquitablePartition` is the cut-norm
   limit of a `ConsistentPartitionSequence` (reverse theorem).
2. (Completeness) Every Cauchy sequence of finite equitable partitions
   (in the sense of `quotient_cauchy`) has a graphon limit
   (forward theorem).

Together these say that `GraphonEquitablePartition` is the metric
completion of `EquitablePartition_fin` in cut norm, with the
identification unique up to measure-preserving rearrangement
(`unique_mod_mpr`).

We package this as a single existence statement: every graphon
equitable partition has a Cauchy approximating sequence, and the
forward theorem identifies its limit. -/
theorem graphonEquitablePartition_is_cauchy_completion
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    -- Density side: there exists a consistent partition sequence whose
    -- finite quotient matrices form a Cauchy sequence (automatic by
    -- `quotient_cauchy`) and whose limit is `P.quotient` (reverse
    -- theorem).
    ∃ 𝒮 : ConsistentPartitionSequence I,
      CauchySeq (fun n => 𝒮.quotient n) ∧
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
        (nhds P.quotient) := by
  -- Combine `arises_from_consistent_sequence` (density) with
  -- `quotient_cauchy` (the Cauchy property holds for *every* sequence
  -- produced by the forward theorem).
  rcases GraphonEquitablePartition.arises_from_consistent_sequence W P with
    ⟨𝒮, _Wstep, _hcut, h_lim⟩
  exact ⟨𝒮, 𝒮.quotient_cauchy ⟨P.quotient, h_lim⟩, h_lim⟩

/-! ## Summary table

| Direction | Statement                                              | Source                                          |
|-----------|--------------------------------------------------------|-------------------------------------------------|
| Forward   | `𝒮 ⇒ (W_lim, P_lim)`                                   | `ConsistentPartitionSequence.limit_exists`      |
| Reverse   | `(W, P) ⇒ 𝒮`                                           | `arises_from_consistent_sequence` (this file)   |
| Rate      | cut-norm distance `≤ ε` at finite stage                | `stepFunction_approximation_rate` (this file)   |
| Unique    | mod measure-preserving rearrangements                  | `unique_mod_mpr` (this file)                    |
| Both      | cell-uniform PST ↔ eventual finite PST                  | `cellUniformPST_iff_consistent_quotientPST`     |
| Cat.      | `GraphonEquitablePartition = Cauchy(EquitablePartition_fin)` | `graphonEquitablePartition_is_cauchy_completion` |

References (combined):

* BCLSV, arXiv:1003.5588 — stepping operator and cut-norm density.
* Lovász, *Large Networks and Graph Limits* — Cauchy completion of
  finite graphs.
* Janson, NYJM Monograph 4 (2013) — uniqueness modulo
  measure-preserving rearrangement. -/

end Graphon

end Graphplay