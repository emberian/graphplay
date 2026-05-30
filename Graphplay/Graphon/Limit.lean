/-
# Graphon/Limit.lean — quasi-infinite limit theorems

This file states the **graphon limit theorem** for sequences of finite
weighted graphs equipped with compatible equitable partitions: such a
sequence has a graphon limit `Wlim`, the equitable partitions also limit to a
graphon equitable partition `Plim`, the quotient matrices converge in operator
norm, and PST / mixing / spatial-search times converge.

This is the quantitative bridge between Tower 4 (graphons) and the finite
spectral graph theory of Towers 1–3.  A concrete consequence is the
**Xie–Tamon "no infinite tail beats optimality"** result: for the family
`G_n = K_n + P_n` (complete graph plus a path of length `n`) with the
distance-from-`K_n` equitable partition, the limit graphon yields the same
PST optimality bound as Xie–Tamon prove for the finite case.

References:

* Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs
  I*, arXiv:0708.1499 (also arXiv:1003.5588 — graphon stepping operator) —
  **cut-norm convergence of graphons** and counting-lemma framework.
* Lovász, *Large Networks and Graph Limits* — the standard reference for
  graphon convergence and cut-norm.
* Gao–Caines, arXiv:2004.00677 — graphon limit of LQR control problems.
* Xie–Tamon, arXiv:2301.07251 — the concrete corollary we obtain.
-/

import Graphplay.Graphon.PST

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory

universe u v

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The cut norm and graphon convergence

The **cut norm** of a graphon `W` is
$$ \|W\|_\square \;=\; \sup_{S, T \subseteq \Omega} \Big|\int_{S \times T} W\,
   d(\mu \otimes \mu)\Big|, $$
the supremum being over measurable subsets.  A sequence `(W_n)` of graphons
converges to `W` *in cut norm* iff `‖W_n − W‖_\square → 0`.

This is the standard convergence of the BCLSV–Lovász theory. -/

/-- The **cut norm** of a graphon kernel difference (real-valued).  Defined
as the sup over measurable rectangles `S × T` of the absolute value of the
integral of `W.kernel` over that rectangle. -/
noncomputable def cutNorm {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W : Graphon Ω μ) : ℝ :=
  ⨆ (S : Set Ω) (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
    ‖∫ x in S, ∫ y in T, W.kernel x y ∂μ ∂μ‖

/-- The **cut norm of a difference of two graphon kernels** (real-valued):
the sup over measurable rectangles `S × T` of the absolute value of the
integral of `W.kernel - Wlim.kernel` over that rectangle.  We work directly
with the pointwise kernel difference rather than constructing a graphon
difference (the structure `Graphon` bundles analytic hygiene fields that need
not survive subtraction, e.g. the diagonal-vanishing condition); only the
kernel matters for the cut norm. -/
noncomputable def cutNormDiff {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W Wlim : Graphon Ω μ) : ℝ :=
  ⨆ (S : Set Ω) (_ : MeasurableSet S) (T : Set Ω) (_ : MeasurableSet T),
    ‖∫ x in S, ∫ y in T, (W.kernel x y - Wlim.kernel x y) ∂μ ∂μ‖

/-- A sequence of graphons on the same measure space converges in cut norm to
`Wlim` iff the cut norm of the (pointwise kernel) difference tends to zero:
$$ \|W_n - W_{\lim}\|_\square \;\longrightarrow\; 0. $$
This is the standard BCLSV–Lovász cut-norm convergence, made concrete via
`cutNormDiff`. -/
def CutNormTendsto {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W : ℕ → Graphon Ω μ) (Wlim : Graphon Ω μ) : Prop :=
  Filter.Tendsto (fun n => cutNormDiff (W n) Wlim) Filter.atTop (nhds 0)

/-! ## Consistent partition sequences

The key combinatorial input for the limit theorem is a sequence of finite
weighted graphs `G_n` with equitable partitions `P_n` that **refine each
other in a uniform way** under embeddings `G_n ↪ G_{n+1}`. -/

/-- A **consistent partition sequence**: a sequence of finite weighted graphs
`G n` on the vertex types `V n`, together with equitable partitions of the
canonical step graphons (with the same fixed index type `I`), and embeddings
`V n ↪ V (n+1)` that map cells `i ∈ I` to cells `i ∈ I`.

The "consistency" condition is that the pullback of the partition `P_{n+1}`
along the embedding equals `P_n`. -/
structure ConsistentPartitionSequence
    (I : Type v) [Fintype I] [DecidableEq I] where
  /-- The vertex type at each stage `n`. -/
  V : ℕ → Type u
  /-- Finiteness, decidability, and measurable-singleton-class at each stage. -/
  finV : ∀ n, Fintype (V n)
  decV : ∀ n, DecidableEq (V n)
  measV : ∀ n, MeasurableSpace (V n)
  msingV : ∀ n, @MeasurableSingletonClass (V n) (measV n)
  /-- The finite weighted graph at stage `n`. -/
  G : ∀ n, @WeightedGraph (V n) (finV n) (decV n)
  /-- The cell-membership map for stage `n`. -/
  cells : ∀ n, V n → I
  /-- Embedding `V n ↪ V (n+1)`. -/
  embed : ∀ n, V n → V (n + 1)
  /-- Embeddings respect the cell maps: `cells (n+1) ∘ embed n = cells n`. -/
  embed_cells : ∀ n (v : V n), cells (n + 1) (embed n v) = cells n v
  /-- The partitions are equitable for the step graphons.  We package this as
  the hypothesis that the relevant uniform-row-sum property holds at each
  stage. -/
  equitable :
    ∀ n (i j : I) (x y : V n),
      cells n x = i → cells n y = i →
      ∑ z : V n, (if cells n z = j then (G n).adj x z else 0)
        = ∑ z : V n, (if cells n z = j then (G n).adj y z else 0)

/-- The **stage-`n` quotient matrix** of a consistent partition sequence,
defined directly as a cell-mass-averaged cell-flux.  This is the finite
analogue of `GraphonEquitablePartition.quotient`:
$$ B^{(n)}_{i j} \;=\; \frac{1}{|C^{(n)}_i|}
   \sum_{x \in C^{(n)}_i}\ \sum_{z \in C^{(n)}_j} (G\,n).\mathrm{adj}\ x\ z. $$
The cell-mass normalisation makes the matrix **total** (well-defined for every
`i`, taken to be `0` on an empty cell) and choice-free; by `𝒮.equitable` the
inner double sum is constant on `C^{(n)}_i`, so for a nonempty cell this average
equals the per-vertex flux out of any representative `x ∈ C^{(n)}_i`. -/
noncomputable def ConsistentPartitionSequence.quotient
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I) (n : ℕ) :
    Matrix I I ℂ :=
  -- route the stage-`n` finiteness / decidability instances explicitly
  letI : Fintype (𝒮.V n) := 𝒮.finV n
  letI : DecidableEq (𝒮.V n) := 𝒮.decV n
  fun i j =>
    (((Finset.univ.filter (fun x : 𝒮.V n => 𝒮.cells n x = i)).card : ℂ))⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x : 𝒮.V n => 𝒮.cells n x = i),
        ∑ z ∈ Finset.univ.filter (fun z : 𝒮.V n => 𝒮.cells n z = j),
          (𝒮.G n).adj x z

/-! ## **The limit theorem (statement only)**

For a consistent partition sequence `𝒮`, the step graphons converge in cut
norm to a limit graphon `Wlim`, the partitions converge to a graphon
equitable partition `Plim : GraphonEquitablePartition Wlim`, and the finite
quotient matrices converge in operator norm to `Plim.quotient`.

Consequently, the PST / mixing / search **times** computed on the finite
quotients converge to the analogous quantities on `Plim.quotient` — and
hence, by the headline graphon-PST theorem, to the cell-uniform graphon
quantities. -/

/-- Existence of a graphon limit and a limit equitable partition for any
consistent partition sequence.

This is the **graphon limit theorem of Graphplay**, the quasi-infinite
counterpart of the BCLSV cut-norm limit construction.  Proof deferred. -/
theorem ConsistentPartitionSequence.limit_exists
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim),
      -- the cell quotient matrices converge to `Plim.quotient` in operator norm
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
        (nhds Plim.quotient) := by
  sorry

/-- A slightly weaker, very useful **convergence-of-quotients** statement:
**The finite quotient matrices `𝒮.quotient n` form a Cauchy sequence in
operator norm.**  This is the "matrix-only" tail of the limit theorem and
is the version actually needed for PST/mixing/search time convergence. -/
theorem ConsistentPartitionSequence.quotient_cauchy
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I) :
    CauchySeq (fun n => 𝒮.quotient n) := by
  sorry

/-- **PST-time convergence.**  If `𝒮.quotient n` exhibits PST from cell `i`
to cell `j` at time `τ_n` for every `n`, and `τ_n → τlim`, then the graphon
limit `(Wlim, Plim)` exhibits cell-uniform PST from cell `i` to cell `j` at
time `τlim`.

Conversely, cell-uniform PST on `(Wlim, Plim)` is the limit of finite PST on
the `𝒮.quotient n`. -/
theorem ConsistentPartitionSequence.pst_time_convergence
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (i j : I) (τ : ℕ → ℝ) (τlim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds τlim))
    (h_pst : ∀ n, IsPST_finite (𝒮.quotient n) i j (τ n)) :
    IsCellUniformPST Wlim Plim i j τlim := by
  -- Honest gap: needs joint continuity of `(H, t) ↦ exp(-i t · H)` entrywise to
  -- pass modulus-one to the limit, AND a bridge from the raw `𝒮.quotient`/`Plim.quotient`
  -- (in the hypotheses) to the spectrum-sharing `Plim.symmQuotient` (in the conclusion,
  -- via `cellUniformPST_iff_quotientPST`); the two matrices differ unless cell masses coincide.
  sorry

/-- **Mixing-time convergence.**  Analogous statement for uniform mixing. -/
theorem ConsistentPartitionSequence.mixing_time_convergence
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (i : I) (τ : ℕ → ℝ) (τlim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds τlim))
    (h_mix : ∀ n, IsUniformMixing_finite (𝒮.quotient n) i (τ n)) :
    IsCellUniformGraphonMixing Wlim Plim i τlim := by
  -- Honest gap: as in `pst_time_convergence` — joint `exp`-continuity plus the raw
  -- `quotient` vs `symmQuotient` bridge (`cellUniformGraphonMixing_iff_quotientMixing`).
  sorry

/-- **Search-time convergence.**  Spatial-search success times computed on
finite quotients converge to the graphon-level cell-uniform search-success
time. -/
theorem ConsistentPartitionSequence.search_time_convergence
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (γ : ℝ) (w : I) (τ : ℕ → ℝ) (τlim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds τlim)) :
    IsCellUniformSearchSuccess Wlim Plim γ w τlim := by
  -- the conclusion `IsCellUniformSearchSuccess` is now the concrete modulus-one
  -- amplitude condition (no longer `True`).  By `cellUniformSearch_iff_quotientSearch`
  -- it is the finite-search success on `Plim.symmQuotient`, which is the
  -- operator-norm limit (`h_lim`) of the finite searches on `𝒮.quotient n` via
  -- joint continuity of `exp(-iτ · finiteSearchHamiltonian H γ w)` in `(H, τ)`.
  -- Honest gap (depends on the `exp`/search lift).
  sorry

/-! ## Concrete corollary: Xie–Tamon (arXiv:2301.07251)

The Xie–Tamon paper *No infinite tail beats optimality* (2023) considers the
graph family `G_n = K_n + path-n` (a complete graph `K_n` joined by an edge to
a path of `n` vertices), with the equitable partition `P_n` given by distance
from `K_n`.  They prove that the PST time on `G_n` is bounded below by a
universal constant for all `n`, *no matter how long the tail*.

This is the special case `𝒮 = (G_n, P_n)` of our limit theorem.  The graphon
limit `Wlim` is concretely the **half-line graphon**:

* `Ω = {0} ∪ (0, ∞)` with the disjoint union measure (Dirac at `0` plus
  Lebesgue on `(0, ∞)`);
* the kernel is `1` on the `(0,0)` cell (the limit of `K_n`), `1` between `0`
  and any `x ∈ (0,1]` (the limit of the joining edge), `1` between
  consecutive segments of the tail, and `0` elsewhere.

The Xie–Tamon optimality bound is then exactly the inequality
`‖exp(-i τ Plim.quotient)‖ ≥ c > 0` for all `τ`, where `Plim.quotient` is the
**infinite tridiagonal matrix** that is the limit of the path quotient
matrices.

We package this as the following corollary. -/

/-- **Xie–Tamon as a corollary of the limit theorem.**  There is a consistent
partition sequence (concretely `G_n = K_n + P_n` with `P_n =
distance-from-K_n`) and a graphon limit `(Wlim, Plim)` of it for which PST
between two **distinct** cells `i ≠ j` is impossible at *every* time `τ` —
recovering the Xie–Tamon "no infinite tail beats optimality" result.

The statement is now genuine (no `True`): it asserts the existence of the
sequence, its limit, two distinct cells, and the all-time PST-impossibility
`∀ τ, ¬ IsCellUniformPST Wlim Plim i j τ`.  The explicit `K_n + path-n`
construction and the impossibility proof (via the continuous tail sector of
`Graphon/Spectrum.lean`) are deferred as an honest `sorry`. -/
theorem xie_tamon_no_infinite_tail
    (I : Type v) [Fintype I] [DecidableEq I] [Nontrivial I] :
    ∃ (𝒮 : ConsistentPartitionSequence I)
      (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsFiniteMeasure μ)
      (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
      (i j : I), i ≠ j ∧ (∀ τ : ℝ, ¬ IsCellUniformPST Wlim Plim i j τ) := by
  -- the precise witness is the explicit `K_n + path-n` consistent partition
  -- sequence; its graphon limit has a continuous tail sector
  -- (`Graphon/Spectrum.lean`, `HasContinuousTailSector`) that obstructs
  -- cell-uniform PST.  Construction + impossibility proof deferred.
  sorry

end Graphon

end Graphplay
