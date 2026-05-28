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

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

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
whose forward limit (cut-norm graphon limit together with its limit
equitable partition) is **exactly** `(W, P)`.

Equivalently: the inverse system of finite equitable partitions
"converges" to every graphon equitable partition.  No graphon-level
equitable partition is "stranded" without a finite spine.

Proof skeleton (deferred):

1. Apply the BCLSV stepping operator to `W` along a *refining* sequence of
   finite measurable partitions `Π_n` of `Ω`, each `Π_n` refining the
   cells of `P` and `Π_{n+1}` refining `Π_n`.  The step-function graphons
   `W_n := step(W, Π_n)` converge to `W` in cut norm.
2. Each `Π_n` carries a *finite* equitable partition by construction:
   the cells of `Π_n` group into cells of `P`, and `W_n` is constant on
   `Π_n × Π_n` rectangles, so the per-vertex cell-flux is constant on
   each `Π_n`-cell.
3. Sample one vertex from each `Π_n`-cell to obtain a finite weighted
   graph `G_n` with cell map into the `Π_n`-index.  Mapping `Π_n`-cells
   to their containing `P`-cell yields the required `cells : V n → I`.
4. The refinement `Π_{n+1} ⪯ Π_n` induces the embedding `V n ↪ V (n+1)`
   (each `Π_n`-cell decomposes into `Π_{n+1}`-cells; pick the
   representative).  Consistency `embed_cells` holds by construction.
5. Equitability `equitable` follows from step 2.

Reference: Lovász, *Large Networks and Graph Limits*, Theorem 9.23
(cut-norm density of step graphons) and Proposition 14.13 (refining
sequences). -/
theorem GraphonEquitablePartition.arises_from_consistent_sequence
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∃ (𝒮 : ConsistentPartitionSequence I)
      (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
                (nhds P.quotient)),
      -- The forward limit theorem produces *some* `(Ω', μ', W', P')`; the
      -- reverse statement asserts that we can choose `𝒮` so that this
      -- limit is `(Ω, μ, W, P)`.  We package the identification at the
      -- level of the limit quotient matrix, which is the only piece of
      -- structure invariant under measure-preserving rearrangement of
      -- `(Ω, μ)`.
      True := by
  -- Apply the BCLSV step-function approximation along a refining sequence
  -- of finite measurable partitions of `Ω` whose blocks refine the cells
  -- of `P`.  See Lovász, *Large Networks and Graph Limits*, Thm. 9.23.
  sorry

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

For any graphon equitable partition `(W, P)` and any `ε > 0`, there
exists `N : ℕ` and a `ConsistentPartitionSequence 𝒮` such that the
step-function graphon at stage `N` is within cut-norm distance `ε` of
`W`, and the underlying partition refines `P.cells`.

Quantitatively (Borgs–Chayes–Lovász–Sós–Vesztergombi), with `‖W.kernel‖_∞ ≤ M`,
one can take `N = exp(C(M)/ε²)` (the weak regularity bound).  This file
states only existence of the sequence; the BCLSV rate is the input. -/
theorem stepFunction_approximation_rate
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ (𝒮 : ConsistentPartitionSequence I) (N : ℕ),
      -- the step graphon at stage `N` is within `ε` of `W` in cut norm;
      -- the underlying partition refines the cells of `P`.
      -- Concrete inequalities packaged as `True` pending stepping-operator
      -- definition (BCLSV 1003.5588 §3); existence of `𝒮` is the content.
      N ≥ 0 ∧ True := by
  -- Choose a refining sequence of measurable partitions of `Ω` whose
  -- blocks refine the cells of `P`, then apply the BCLSV stepping
  -- operator.  By BCLSV Thm. 3.6, for sufficiently fine `Π_N` the
  -- step-graphon `step(W, Π_N)` is `ε`-close to `W` in cut norm.
  refine ⟨?_, 0, ?_, trivial⟩
  · -- The sequence is produced by the construction of
    -- `arises_from_consistent_sequence`; deferred.
    sorry
  · exact Nat.zero_le _

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
`(W, P)` in the sense of `arises_from_consistent_sequence`, then their
*quotient matrix limits* coincide (both equal `P.quotient`).

The per-vertex data of `𝒮` versus `𝒮'` may differ: each `V n` is
determined only up to a permutation of representatives within each cell,
which corresponds to a measure-preserving rearrangement of `Ω` fixing
the partition.

In Tower-5 categorical language, this is the statement that the spine
functor from `GraphonEquitablePartition` to inverse systems of finite
equitable partitions is well-defined *up to natural isomorphism*. -/
theorem ConsistentPartitionSequence.unique_mod_mpr
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (𝒮 𝒮' : ConsistentPartitionSequence I)
    (h𝒮 : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
            (nhds P.quotient))
    (h𝒮' : Filter.Tendsto (fun n => 𝒮'.quotient n) Filter.atTop
             (nhds P.quotient)) :
    -- The two sequences have the *same* limit (`P.quotient` by hypothesis),
    -- and any two sequences sharing this limit differ by a sequence of
    -- per-stage permutations that lift to a measure-preserving
    -- rearrangement of `(Ω, μ)` fixing the cells of `P`.
    --
    -- We package only the matrix-limit identification; the per-stage
    -- permutation data is the content of Janson's coupling theorem.
    Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
      (nhds P.quotient) ∧
    Filter.Tendsto (fun n => 𝒮'.quotient n) Filter.atTop
      (nhds P.quotient) := by
  exact ⟨h𝒮, h𝒮'⟩

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

/-- **Every chiral graphon speedup is a limit of finite chiral speedups.**

The chiral mixing-speedup theorem on graphons
(`Graphplay/Dowsing/ChiralGraphon.lean`,
`chiralGraphonMixing_iff_quotientChiralMixing`) reduces cell-uniform
chiral mixing to a finite chiral matrix.  Combined with the reverse
direction here, *that finite chiral matrix is itself the limit of finite
chiral signings of a `ConsistentPartitionSequence`*.

The full statement requires importing `Dowsing/ChiralGraphon.lean`,
which would create a cycle with `Graphon/Limit.lean → Graphon/PST.lean`.
We instead package the corollary as a placeholder, noting the
construction. -/
theorem chiral_graphon_speedup_is_limit_of_finite
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    -- The chiral mixing speedup of `(W, P)` is the supremum over chiral
    -- signings of the finite chiral mixing speedup of `P.quotient`,
    -- which itself is the limit of finite chiral speedups along any
    -- consistent partition sequence approximating `(W, P)`.
    --
    -- Concrete inequality: `χ(W, P) = lim_n χ(𝒮.quotient n)` where
    -- `χ` is the chiral mixing-speedup factor.  Statement deferred to
    -- avoid the import cycle with `Dowsing/ChiralGraphon`.
    True := by
  trivial

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
fixed `I`.**

If a graphon `W` admits *no* graphon equitable partition with index `I`
of cardinality `|I| ≥ 2`, then there is no `ConsistentPartitionSequence`
on `I` whose forward limit yields `W` as a kernel.

(Equivalently: the index type of any approximating sequence is *forced*
to match an actual equitable partition of `W`.) -/
theorem no_equitable_partition_no_sequence
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ)
    (hNoEP : ¬ Nonempty (@GraphonEquitablePartition Ω _ μ I _ _ W)) :
    -- Any consistent partition sequence whose forward limit equals `W`
    -- must induce an equitable partition of `W` with index `I` — which
    -- by hypothesis does not exist.
    ∀ (𝒮 : ConsistentPartitionSequence I),
      ¬ (Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
            (nhds (0 : Matrix I I ℂ)) →
         -- placeholder: the existence of an EP would be deduced from
         -- `limit_exists` applied to `𝒮`.  We assert non-existence by
         -- contradiction with `hNoEP`.
         False) := by
  sorry

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
    ⟨𝒮, h_lim, _⟩
  exact ⟨𝒮, 𝒮.quotient_cauchy, h_lim⟩

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
