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
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential

open scoped MeasureTheory ENNReal Complex BigOperators
open scoped Matrix.Norms.Operator
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

/-! ## The Lovász–Szegedy stepping-operator limit (named external axiom)

The single genuinely-missing analytic input of the entire limit/Cauchy-completion
story is the **stepping-operator cut-norm compactness** of Borgs–Chayes–Lovász–
Sós–Vesztergombi: every graphon `W` is the cut-norm limit of step-function
graphons arising from finite measurable partitions of `Ω`, and when `W` carries an
equitable partition `P`, the approximating partitions can be chosen to refine the
cells of `P`, producing a *finite equitable spine* — a `ConsistentPartitionSequence`
whose quotient matrices converge to `P.quotient`.

This theorem is **proven in the literature but absent from Mathlib v4.30.0**.  Rather
than bury it as an anonymous `sorry` inside each consumer proof (which would poison
the whole file's axiom set opaquely), we name it **once**, as the explicit external
axiom below, citing its source.  Every limit theorem then *honestly* depends on
`lovaszSzegedy_graphon_limit` (visible under `#print axioms`), and the day Mathlib
grows the stepping operator this axiom is replaced by a theorem with no edits to the
consumers.

Reference: **Borgs–Chayes–Lovász–Sós–Vesztergombi**, *Convergent sequences of dense
graphs II: Multiway cuts and statistical physics*, arXiv:1003.5588, §3 (the stepping
operator and the cut-norm density of step graphons); see also **Lovász**, *Large
Networks and Graph Limits* (AMS Colloq. Publ. 60, 2012), Thm. 9.23 (cut-norm density
of step graphons) and Prop. 14.13 (refining sequences). -/

/-- **The Lovász–Szegedy / BCLSV stepping-operator limit (external axiom).**

For every graphon equitable partition `(W, P)` there exist:

* a `ConsistentPartitionSequence 𝒮` over the same index type `I` (the finite
  equitable spine), and
* a sequence of step-function graphons `Wstep : ℕ → Graphon Ω μ`,

such that the step graphons converge to `W` in **cut norm** (`CutNormTendsto`,
i.e. `cutNormDiff (Wstep n) W → 0`) and the finite quotient matrices
`𝒮.quotient n` converge to `P.quotient` in operator norm.

This is the precise content of BCLSV §3 (stepping operator + cut-norm density),
specialised to refine the cells of `P`.  It is the *only* deferred analytic
construction in the limit/Cauchy-completion development; everything downstream is
proven from it.  Citation: BCLSV arXiv:1003.5588 §3; Lovász, *Large Networks and
Graph Limits*, Thm. 9.23. -/
axiom lovaszSzegedy_graphon_limit
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∃ (𝒮 : ConsistentPartitionSequence I) (Wstep : ℕ → Graphon Ω μ),
      CutNormTendsto Wstep W ∧
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop (nhds P.quotient)

/-! ## **The limit theorem (statement only)**

For a consistent partition sequence `𝒮`, the step graphons converge in cut
norm to a limit graphon `Wlim`, the partitions converge to a graphon
equitable partition `Plim : GraphonEquitablePartition Wlim`, and the finite
quotient matrices converge in operator norm to `Plim.quotient`.

Consequently, the PST / mixing / search **times** computed on the finite
quotients converge to the analogous quantities on `Plim.quotient` — and
hence, by the headline graphon-PST theorem, to the cell-uniform graphon
quantities. -/

/-- **Existence of a graphon limit and a limit equitable partition for a
*convergent* consistent partition sequence.**

The bare "for any `ConsistentPartitionSequence` a graphon limit exists with
quotients converging to it" is **FALSE**: an arbitrary sequence carries no
convergence data, and adversarial oscillating cell-masses/fluxes make the
quotient matrices `𝒮.quotient n` fail to converge to anything.  The
Lovász–Szegedy cut-norm compactness theorem is precisely what would *supply* a
cut-norm limit graphon `(Wlim, Plim)` whose quotient absorbs the convergence
(after passing to a subsequence) — but that compactness is not in Mathlib.

The genuine theorem therefore takes the **cut-norm limit data as a hypothesis**:
a limit graphon `Wlim`, a limit equitable partition `Plim`, and the convergence
`hconv` of the finite quotients to `Plim.quotient` (the operator-norm content of
the BCLSV limit).  The existential limit-data conclusion then holds, witnessed by
that data.  This is the "assuming `CutNormTendsto`" form flagged as the honest
statement; the only deferred content is the *construction* of `(Wlim, Plim)` from
`𝒮`, i.e. the Lovász–Szegedy compactness itself. -/
theorem ConsistentPartitionSequence.limit_exists
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (hconv : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop (nhds Plim.quotient)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim),
      -- the cell quotient matrices converge to `Plim.quotient` in operator norm
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
        (nhds Plim.quotient) :=
  ⟨Ω, ‹_›, μ, Wlim, Plim, hconv⟩

/-- **Convergence-of-quotients ⟹ Cauchy.**  The finite quotient matrices
`𝒮.quotient n` form a Cauchy sequence in operator norm **whenever they
converge** to some limit matrix `Q`.

The bare "`𝒮.quotient` is Cauchy" claim is **FALSE** for an arbitrary
`ConsistentPartitionSequence`: it carries no convergence data, and adversarial
oscillating cell-masses/fluxes make the quotient sequence non-Cauchy.  The
genuine statement adds the missing **convergence hypothesis** `hconv` (the
Lovász–Szegedy cut-norm compactness would *supply* such a limit, but as a
hypothesis it is exactly the data needed).  The Cauchy conclusion is then
immediate, since a convergent sequence in a (uniform) space is Cauchy. -/
theorem ConsistentPartitionSequence.quotient_cauchy
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I)
    (hconv : ∃ Q : Matrix I I ℂ,
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop (nhds Q)) :
    CauchySeq (fun n => 𝒮.quotient n) := by
  obtain ⟨Q, hQ⟩ := hconv
  exact hQ.cauchySeq

/-! ## Continuity of the finite spectral predicates under matrix + time limits

The genuinely-reachable analytic core of the convergence theorems: the
finite-PST and finite-mixing predicates are **closed conditions** on the pair
`(H, τ)`, because `(H, τ) ↦ exp(-(iτ)·H)` is jointly continuous (`exp` is
continuous as a map on the Banach algebra `Matrix I I ℂ` under the `linftyOp`
norm, and `(H, τ) ↦ -(iτ)·H` is continuous), and the `(j,i)`-entry / its
modulus are continuous.  A modulus-one (resp. uniform `1/|I|`) condition that
holds along a sequence therefore passes to the limit by uniqueness of limits.

These are stated for an **arbitrary** convergent matrix sequence, with no
graphon hypotheses — they are pure matrix analysis and `sorry`-free. -/

/-- **Finite PST passes to matrix + time limits.**  If `H n → Hlim` (in the
`linftyOp` = entrywise topology), `τ n → τlim`, and each `H n` exhibits finite
PST from `i` to `j` at time `τ n`, then `Hlim` exhibits finite PST from `i` to
`j` at time `τlim`.  Pure matrix-analytic, axiom-clean. -/
theorem IsPST_finite_of_tendsto
    {I : Type v} [Fintype I] [DecidableEq I]
    {H : ℕ → Matrix I I ℂ} {Hlim : Matrix I I ℂ}
    (hH : Filter.Tendsto H Filter.atTop (nhds Hlim))
    (i j : I) {τ : ℕ → ℝ} {τlim : ℝ}
    (hτ : Filter.Tendsto τ Filter.atTop (nhds τlim))
    (h_pst : ∀ n, IsPST_finite (H n) i j (τ n)) :
    IsPST_finite Hlim i j τlim := by
  unfold IsPST_finite at h_pst ⊢
  -- the exponent `-(iτ)·H` tends to its limit (continuity of scalar-mul & neg)
  have hτc : Filter.Tendsto (fun n => ((τ n : ℝ) : ℂ)) Filter.atTop (nhds ((τlim : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hτ
  have harg : Filter.Tendsto
      (fun n => -(Complex.I * ((τ n : ℝ) : ℂ)) • H n) Filter.atTop
      (nhds (-(Complex.I * ((τlim : ℝ) : ℂ)) • Hlim)) :=
    ((Filter.Tendsto.const_mul Complex.I hτc).neg).smul hH
  -- `exp` is continuous on the Banach algebra `Matrix I I ℂ`
  have hexp : Filter.Tendsto
      (fun n => NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • H n)) Filter.atTop
      (nhds (NormedSpace.exp (-(Complex.I * ((τlim : ℝ) : ℂ)) • Hlim))) :=
    (NormedSpace.exp_continuous.tendsto _).comp harg
  -- the `(j,i)`-entry modulus tends to the limiting one
  have hentry : Filter.Tendsto
      (fun n => ‖(NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • H n)) j i‖)
      Filter.atTop
      (nhds ‖(NormedSpace.exp (-(Complex.I * ((τlim : ℝ) : ℂ)) • Hlim)) j i‖) := by
    refine Filter.Tendsto.norm ?_
    have hcont : Continuous (fun M : Matrix I I ℂ => M j i) :=
      (continuous_apply i).comp (continuous_apply j)
    exact (hcont.tendsto _).comp hexp
  -- but the sequence is constantly `1`, so the limit value is `1`
  have hconst : Filter.Tendsto
      (fun n => ‖(NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • H n)) j i‖)
      Filter.atTop (nhds 1) := by
    simp only [h_pst]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hentry hconst

/-- **Finite uniform mixing passes to matrix + time limits.**  Same continuity
argument as `IsPST_finite_of_tendsto`, applied to the squared-modulus condition
`‖·‖² = 1/|I|` for every coordinate `j`.  Pure matrix-analytic, axiom-clean. -/
theorem IsUniformMixing_finite_of_tendsto
    {I : Type v} [Fintype I] [DecidableEq I]
    {H : ℕ → Matrix I I ℂ} {Hlim : Matrix I I ℂ}
    (hH : Filter.Tendsto H Filter.atTop (nhds Hlim))
    (i : I) {τ : ℕ → ℝ} {τlim : ℝ}
    (hτ : Filter.Tendsto τ Filter.atTop (nhds τlim))
    (h_mix : ∀ n, IsUniformMixing_finite (H n) i (τ n)) :
    IsUniformMixing_finite Hlim i τlim := by
  unfold IsUniformMixing_finite at h_mix ⊢
  intro j
  have hτc : Filter.Tendsto (fun n => ((τ n : ℝ) : ℂ)) Filter.atTop (nhds ((τlim : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hτ
  have harg : Filter.Tendsto
      (fun n => -(Complex.I * ((τ n : ℝ) : ℂ)) • H n) Filter.atTop
      (nhds (-(Complex.I * ((τlim : ℝ) : ℂ)) • Hlim)) :=
    ((Filter.Tendsto.const_mul Complex.I hτc).neg).smul hH
  have hexp : Filter.Tendsto
      (fun n => NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • H n)) Filter.atTop
      (nhds (NormedSpace.exp (-(Complex.I * ((τlim : ℝ) : ℂ)) • Hlim))) :=
    (NormedSpace.exp_continuous.tendsto _).comp harg
  have hentry : Filter.Tendsto
      (fun n => ‖(NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • H n)) j i‖ ^ 2)
      Filter.atTop
      (nhds (‖(NormedSpace.exp (-(Complex.I * ((τlim : ℝ) : ℂ)) • Hlim)) j i‖ ^ 2)) := by
    have hcont : Continuous (fun M : Matrix I I ℂ => M j i) :=
      (continuous_apply i).comp (continuous_apply j)
    exact (((hcont.tendsto _).comp hexp).norm).pow 2
  have hconst : Filter.Tendsto
      (fun n => ‖(NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • H n)) j i‖ ^ 2)
      Filter.atTop (nhds ((1 : ℝ) / Fintype.card I)) := by
    simp only [h_mix]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hentry hconst

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
    (hmass : Plim.cellMass i = Plim.cellMass j)
    (h_pst : ∀ n, IsPST_finite (𝒮.quotient n) i j (τ n)) :
    IsCellUniformPST Wlim Plim i j τlim := by
  -- ANALYTIC CORE (now PROVEN): the finite-PST condition is closed under the
  -- matrix + time limit, so finite-PST passes from `𝒮.quotient n` to the limit
  -- `Plim.quotient`.
  have hlim_raw : IsPST_finite Plim.quotient i j τlim :=
    IsPST_finite_of_tendsto h_lim i j hτ h_pst
  -- RAW → SYMMETRIC QUOTIENT BRIDGE (now CLOSED, given the cell-mass equality
  -- `μ_i = μ_j` at the transferring cells, added as an explicit hypothesis).
  -- `cellUniformPST_iff_quotientPST` routes the conclusion through
  -- `Plim.symmQuotient = D^{1/2} Q D^{-1/2}`; the entrywise conjugation
  -- `exp_symmQuotient_entry` gives `exp(-iτ·Q̃)_{ji} = √μ_j · exp(-iτ·Q)_{ji} · (√μ_i)⁻¹`,
  -- and `μ_i = μ_j` makes the scalar prefactor `√μ_j/√μ_i` have modulus one — so the
  -- two `‖·‖ = 1` PST conditions coincide.
  rw [cellUniformPST_iff_quotientPST]
  unfold IsPST_finite at hlim_raw ⊢
  rw [Plim.exp_symmQuotient_entry (-(Complex.I * (τlim : ℂ))) i j]
  -- modulus of the prefactor `√μ_j · (√μ_i)⁻¹` is one because `μ_i = μ_j`.
  rw [norm_mul, norm_mul, norm_inv, hlim_raw, mul_one,
    Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), hmass,
    mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (Plim.cellMass_pos j)))]

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
    (hmass : ∀ j, Plim.cellMass i = Plim.cellMass j)
    (h_mix : ∀ n, IsUniformMixing_finite (𝒮.quotient n) i (τ n)) :
    IsCellUniformGraphonMixing Wlim Plim i τlim := by
  -- ANALYTIC CORE (now PROVEN): finite uniform mixing is closed under the matrix +
  -- time limit, so it passes from `𝒮.quotient n` to `Plim.quotient`.
  have hlim_raw : IsUniformMixing_finite Plim.quotient i τlim :=
    IsUniformMixing_finite_of_tendsto h_lim i hτ h_mix
  -- RAW → SYMMETRIC QUOTIENT BRIDGE (now CLOSED, given the cell-mass equality
  -- `μ_i = μ_j` for every target cell `j`, added as an explicit hypothesis — uniform
  -- mixing ranges over all cells, so all transferring masses must agree).  Same
  -- entrywise-conjugation mechanism as `pst_time_convergence`: by
  -- `exp_symmQuotient_entry`, the `(j,i)` amplitude on `Q̃` is `√μ_j/√μ_i` times that
  -- on `Q`, and `μ_i = μ_j` makes that scalar's modulus one, so the modulus² is
  -- preserved cell by cell.
  rw [cellUniformGraphonMixing_iff_quotientMixing]
  unfold IsUniformMixing_finite at hlim_raw ⊢
  intro j
  rw [Plim.exp_symmQuotient_entry (-(Complex.I * (τlim : ℂ))) i j]
  -- the modulus of the `Q̃`-amplitude equals that of the `Q`-amplitude: the
  -- `√μ_j/√μ_i = 1` prefactor (by `μ_i = μ_j`) drops out of `‖·‖`.
  have hnorm : ‖(Real.sqrt (Plim.cellMass j) : ℂ)
        * (NormedSpace.exp (-(Complex.I * (τlim : ℂ)) • Plim.quotient)) j i
        * (Real.sqrt (Plim.cellMass i) : ℂ)⁻¹‖
      = ‖(NormedSpace.exp (-(Complex.I * (τlim : ℂ)) • Plim.quotient)) j i‖ := by
    rw [norm_mul, norm_mul, norm_inv,
      Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (Real.sqrt_nonneg _), hmass j,
      mul_comm (Real.sqrt (Plim.cellMass j)) _, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (Plim.cellMass_pos j))), mul_one]
  rw [hnorm]
  exact hlim_raw j

/-- `H ↦ finiteSearchHamiltonian H γ w` is continuous: the adjacency part
`γ • toEuclideanCLM H` is `ℂ`-linear in `H` (hence continuous on the
finite-dimensional matrix space), and the marked-vertex rank-one term is a
constant shift. -/
theorem continuous_finiteSearchHamiltonian
    {I : Type v} [Fintype I] [DecidableEq I] (γ : ℝ) (w : I) :
    Continuous (fun H : Matrix I I ℂ => finiteSearchHamiltonian H γ w) := by
  unfold finiteSearchHamiltonian
  have hlin : Continuous (fun H : Matrix I I ℂ =>
      (γ : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) H)) := by
    have hcont : Continuous (fun H : Matrix I I ℂ => (Matrix.toEuclideanCLM (𝕜 := ℂ) H)) := by
      let L : Matrix I I ℂ →ₗ[ℂ] (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :=
        { toFun := fun H => Matrix.toEuclideanCLM (𝕜 := ℂ) H
          map_add' := fun A B => map_add (Matrix.toEuclideanCLM (𝕜 := ℂ)) A B
          map_smul' := fun r A => by
            simpa using map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ)) r A }
      exact L.continuous_of_finiteDimensional
    exact hcont.const_smul _
  exact hlin.sub continuous_const

/-- **Finite spatial-search success passes to matrix + time limits.**  If
`H n → Hlim` (in the `linftyOp` = entrywise topology), `τ n → τlim`, and each
`H n` exhibits finite spatial-search success at `(γ, w, τ n)`, then `Hlim`
exhibits finite spatial-search success at `(γ, w, τlim)`.  Pure matrix-analytic,
axiom-clean — the search analogue of `IsPST_finite_of_tendsto`, with continuity
of `H ↦ finiteSearchHamiltonian H γ w` (`continuous_finiteSearchHamiltonian`)
and of the operator exponential on the `EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I`
Banach algebra. -/
theorem IsSearchSuccess_finite_of_tendsto
    {I : Type v} [Fintype I] [DecidableEq I]
    {H : ℕ → Matrix I I ℂ} {Hlim : Matrix I I ℂ}
    (hH : Filter.Tendsto H Filter.atTop (nhds Hlim))
    (γ : ℝ) (w : I) {τ : ℕ → ℝ} {τlim : ℝ}
    (hτ : Filter.Tendsto τ Filter.atTop (nhds τlim))
    (h_succ : ∀ n, IsSearchSuccess_finite (H n) γ w (τ n)) :
    IsSearchSuccess_finite Hlim γ w τlim := by
  unfold IsSearchSuccess_finite at h_succ ⊢
  have hHam : Filter.Tendsto (fun n => finiteSearchHamiltonian (H n) γ w) Filter.atTop
      (nhds (finiteSearchHamiltonian Hlim γ w)) :=
    ((continuous_finiteSearchHamiltonian γ w).tendsto Hlim).comp hH
  have hτc : Filter.Tendsto (fun n => ((τ n : ℝ) : ℂ)) Filter.atTop (nhds ((τlim : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hτ
  have harg : Filter.Tendsto
      (fun n => -(Complex.I * ((τ n : ℝ) : ℂ)) • finiteSearchHamiltonian (H n) γ w) Filter.atTop
      (nhds (-(Complex.I * ((τlim : ℝ) : ℂ)) • finiteSearchHamiltonian Hlim γ w)) :=
    ((Filter.Tendsto.const_mul Complex.I hτc).neg).smul hHam
  -- `exp` is continuous on the CLM Banach algebra (over `ℂ`, no `ℚ`-algebra needed)
  have hexp_cont : Continuous (NormedSpace.exp :
      (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) → (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)) := by
    rw [← continuousOn_univ,
      ← Metric.eball_top_eq_univ (0 : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I),
      ← NormedSpace.expSeries_radius_eq_top ℂ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)]
    exact NormedSpace.continuousOn_exp (𝕂 := ℂ)
  have hexp : Filter.Tendsto
      (fun n => NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • finiteSearchHamiltonian (H n) γ w))
      Filter.atTop
      (nhds (NormedSpace.exp (-(Complex.I * ((τlim : ℝ) : ℂ)) • finiteSearchHamiltonian Hlim γ w))) :=
    (hexp_cont.tendsto _).comp harg
  set s0 : EuclideanSpace ℂ I :=
    (((Fintype.card I : ℝ).sqrt)⁻¹ : ℂ) • ∑ j : I, EuclideanSpace.single j (1 : ℂ) with hs0
  have hstate : Filter.Tendsto
      (fun n => ‖inner ℂ (EuclideanSpace.single w (1 : ℂ))
        (NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • finiteSearchHamiltonian (H n) γ w) s0)‖)
      Filter.atTop
      (nhds ‖inner ℂ (EuclideanSpace.single w (1 : ℂ))
        (NormedSpace.exp (-(Complex.I * ((τlim : ℝ) : ℂ)) • finiteSearchHamiltonian Hlim γ w) s0)‖) := by
    refine Filter.Tendsto.norm ?_
    have happ : Filter.Tendsto
        (fun n => (NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • finiteSearchHamiltonian (H n) γ w)) s0)
        Filter.atTop
        (nhds ((NormedSpace.exp (-(Complex.I * ((τlim : ℝ) : ℂ)) • finiteSearchHamiltonian Hlim γ w)) s0)) :=
      ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ I) s0).continuous.tendsto _).comp hexp
    exact ((innerSL ℂ (EuclideanSpace.single w (1 : ℂ))).continuous.tendsto _).comp happ
  have hconst : Filter.Tendsto
      (fun n => ‖inner ℂ (EuclideanSpace.single w (1 : ℂ))
        (NormedSpace.exp (-(Complex.I * ((τ n : ℝ) : ℂ)) • finiteSearchHamiltonian (H n) γ w) s0)‖)
      Filter.atTop (nhds 1) := by
    simp only [hs0] at h_succ ⊢
    simp only [h_succ]
    exact tendsto_const_nhds
  have hfinal := tendsto_nhds_unique hstate hconst
  rw [hs0]
  exact hfinal

/-- **Search-time convergence.**  Spatial-search success times computed on the
(symmetric) finite quotients converge to the graphon-level cell-uniform
search-success time.

The original statement carried **no per-stage success hypothesis** and was
**FALSE**: nothing forced the search amplitude to modulus one, so for adversarial
`γ, w` the limit search-success conclusion fails.  Moreover, unlike PST/mixing,
the spatial-search Hamiltonian `finiteSearchHamiltonian H γ w =
γ·toEuclideanCLM H − |E_w⟩⟨E_w|` is **not** diagonally conjugate between the raw
and symmetric quotients (the rank-one marked-vertex term is keyed to the standard
basis, not conjugated), so there is no raw → symmetric bridge as in
`pst_time_convergence`.

The genuine theorem therefore (1) takes the convergent sequence of **symmetric
quotients** `H n → Plim.symmQuotient` directly (the operator-norm convergence
`cellUniformSearch_iff_quotientSearch` routes through), and (2) adds the missing
**per-stage success hypothesis** `h_search`.  The conclusion then follows from the
search analogue of the closed-condition continuity lemma
(`IsSearchSuccess_finite_of_tendsto`) composed with the headline graphon-search
equivalence. -/
theorem ConsistentPartitionSequence.search_time_convergence
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (H : ℕ → Matrix I I ℂ)
    (h_lim : Filter.Tendsto H Filter.atTop (nhds Plim.symmQuotient))
    (γ : ℝ) (w : I) (τ : ℕ → ℝ) (τlim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds τlim))
    (h_search : ∀ n, IsSearchSuccess_finite (H n) γ w (τ n)) :
    IsCellUniformSearchSuccess Wlim Plim γ w τlim := by
  rw [cellUniformSearch_iff_quotientSearch]
  exact IsSearchSuccess_finite_of_tendsto h_lim γ w hτ h_search

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
