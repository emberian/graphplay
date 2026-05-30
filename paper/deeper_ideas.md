# Deeper ideas: the irreducibility meter (and its isotypic generalization)

*A research-strategy reframe, born from an honest NEGATIVE result. Status:
the headline is a re-reading of facts we already have; the directions are rated
grounded → speculative individually. Voice and honesty discipline inherited from
`paper/explanatory_program.md`, `paper/novel_bets.md`, and the lit notes.*

> The `residual_lab` experiment was run to ask "is `R = A − A_eq` a small, cheap,
> low-rank correction we can compress?" The answer came back **No**, decisively,
> on exactly the heads that do interesting work (`residual_lab/RESIDUAL_FINDINGS.md`).
> This document argues that the No is the most important Yes we have found:
> **a full-rank residual is not a failure of compression — it is a measurement.**

---

## 0. The central reframe (the headline)

**The framework's product is not compression. It is an *irreducibility meter*.**

Run 1-WL color refinement on a learned attention head's (symmetrized,
quantile-binned) matrix `A`. WL returns the **coarsest equitable partition** —
the unique fixed point that is finer than every equitable partition
(`Graphplay/Algorithm/WLOrbit.lean`, `IsWLStable`: *finer than every equitable
`Q`*). Lift to the block-constant quotient `A_eq = S Q̃ Sᵀ`, with apply cost
`O(n·r)` for `r` cells, and take the residual `R = A − A_eq`
(`Graphplay/Integrations/EquitableMechanism.lean`, `residual_add_equitable`:
`A_eq + R = A`, exact and axiom-clean).

Now the two empirical facts from the lab:

1. For a *generic* learned head, every row-signature is distinct under exact WL
   on continuous weights ⇒ all cells are singletons ⇒ `r = n` ⇒ the quotient is
   the **identity** and `A_eq = A`, `R = 0` *vacuously* (the honest caveat in
   `explanatory_program.md §2` and `RESIDUAL_FINDINGS.md`). The "interesting"
   experiment is therefore a *sweep over how coarse the base is forced to be*.
2. When we force a coarse base (operating at `r = 8`, `n = 64`) and look at the
   residual on the interesting heads — induction, sharp retrieval, the heads
   `mechanistic_interp.md` flags as the load-bearing circuits — `R` is **fat,
   near-full-rank (50–52 of 64 on real SmolLM2 heads; 56–59 on the adversarial
   synthetic cores), signal-carrying, and spiky** (top-10% of entries carry
   45–84% of the mass). No SVD, Krylov, random-feature, polynomial, or
   covariance-matched-noise model recovers it below ~50% error short of full
   rank.

Read these together and the slogan inverts. The framework is not telling us how
to *cheaply approximate* the head. It is telling us, per head, the **complexity
floor that no exact symmetric or low-rank compression can beat**:

> **The meter.** For a head `A`, the equitable defect (how much mass lives off
> the coarsest non-trivial equitable base) plus the residual rank
> (`rank(A − A_eq)`) measure how many of the head's `n²` degrees of freedom are
> *irreducible* — i.e. cannot be folded into any symmetry quotient. A generic
> learned head pins this floor at the top: trivial quotient, full-rank residual,
> the head spends its full `n²` budget. A near-equitable head reads low.

This is a **theorem-shaped statement about the head**, not a method gap. The
reverse-math chain makes it precise:

> **"`A` factors through a small quotient"** (apply cost `O(n·r)`, `r ≪ n`)
> **⟺ "`A` has a non-trivial equitable partition"** (a WL-stable cell structure
> with `r < n`) **⟺ "`A` has exploitable symmetry"** (orbit partition or a
> phantom/equitable refinement of it).

Generic learned attention has *no* non-trivial equitable partition (every row is
its own cell), so the factorization is the identity. "Efficient attention fails
on this head" is not a deficiency of Performer/Linformer/Longformer — it is a
**certificate that the head is irreducible**, and the meter computes that
certificate directly.

**The representation-theoretic reading (the spine for §2).** Project `A` onto the
subspace fixed by the head's (approximate) symmetry algebra. The equitable base
`A_eq` is the **trivial-isotypic component** — the part that lives in the
commutant of the cell-permutation algebra (`Graphplay/Dowsing/NoiseEquitable.lean`,
`partitionAlgebra` / `commutant`; `cellUniformSymmetric_iff_commutant`). The
irreducible residual `R` is everything in the **non-trivial isotypic components**.
By **Schur's lemma an irreducible representation has no proper invariant subspace**,
so within an irreducible block there is *nothing to quotient* — the residual on
that block is genuinely full-dimensional. A full-rank `R` is the signature of a
head whose computation lives in the non-trivial irreps. That is why no equitable
(trivial-isotypic) projection captures it, and why no low-rank surrogate does
either: it is not noise, it is irreducible signal.

**Why this changes the thesis.** Every prior framing (`novel_bets.md`,
`explanatory_program.md`) was *defensive*: "the compression survives only weakly,
mostly on the boring heads." The meter framing is *offensive*: the framework's
deliverable is a **per-head irreducibility certificate** that (a) is computed by
provably-correct machinery (WL = coarsest equitable, spectral lift exact), and
(b) **predicts which efficient-attention method works on which head** — reducible
heads (low defect, low residual rank) are exactly where Performer/Longformer win;
irreducible heads (full residual) are exactly where they fail. The negative
result didn't kill the program; it told us what the program *measures*.

---

## The directions

For each: **construction**, **why it follows from the meter**, **honest
grounding**, **how to test in the `experiments/` probe**, **Lean hook**.

---

### 1. Irreducibility meter / per-head complexity floor  ★ headline

**Construction.** Define, per head `A` (and per granularity `r`):

```
  defect_eq(r)   = ‖A − A_eq(P_r)‖ / ‖A‖          -- mass off the r-cell base
  resid_rank(r)  = rank_ε(A − A_eq(P_r))           -- ε-rank of the residual
  Meter(A)       = the (defect_eq, resid_rank) curve over r,
                   summarized by the *floor*: min over r of an apply-cost
                   model n·(r + resid_rank(r)) at fixed reconstruction error ε.
```

The floor is the smallest *effective width* `r + k` (cells + residual rank) at
which `A_eq(P_r) + R_k` reconstructs `A` to error ε. A reducible head has a
narrow minimum at small `r + k`; an irreducible head's minimum is at `r + k ≈ n`.

**The hybrid layer the meter dictates.** A *per-head dispatch* architecture:
measure `Meter` on a trained reference, then for each head choose

- **reducible heads** (low floor) → replace with the exact `O(n·r)` cell-collapse
  base plus a thin rank-`k` correction (`correctedApplyCost = n·((r+k)·d + d)`,
  proven in `EquitableMechanism.correctedApplyCost_eq`);
- **irreducible heads** (floor ≈ `n`) → leave at full `O(n²)` compute, because
  the meter *certifies* that no cheaper exact form exists.

This is the honest, defensible version of Bet 7 (`novel_bets.md`): not "compress
everything," but "compress what the meter says is compressible, and *prove* the
rest must be paid in full." The dispatch is the product.

**Why it follows from the meter.** Directly: the meter *is* the floor, and the
dispatch is the floor turned into a routing rule. The negative result
(`R` full-rank on interesting heads) is precisely what makes the *irreducible*
branch non-empty and non-trivial — without it, dispatch would be pointless
(everything reducible) or impossible (nothing reducible).

**Honest grounding vs speculation.** **Grounded as a counting/heuristic floor;
NOT yet a proven lower bound.** `resid_rank` is an empirical ε-rank; the
"`r + k` effective width" is an *apply-cost model*, and the Eckart–Young error
half is `corrected_equitable_attention` (stated, but `sorry` — Mathlib v4.30.0
lacks rank-`k` truncation optimality). So the meter today is a *measured floor*
with a proven *upper* bound on cost (`correctedApplyCost_eq`, axiom-clean) and a
*conjectural* matching lower bound. The honest claim is: "the meter computes a
quantity that, on every head we tested, no exact compression beat" — a strong
empirical regularity, not a theorem. Do not overclaim it as a bound until §1's
Lean hook is discharged.

**Test in the probe.** This is *almost entirely already built*: the probe's
`decompose` returns `defect_eq[r]`, `rank_R[r]`, `lowrank_resid_norm[k]` over the
`r`-sweep (`explanatory_program.md §2`; `RESIDUAL_FINDINGS.md` ran exactly this).
The remaining work is (a) collapse those into the single `Meter` floor curve and
the `min (r+k)` summary; (b) the **decisive new experiment**: take the per-head
`Meter` floor and *predict* the relative performance of Performer vs. Longformer
vs. dense on each head's task, then check the prediction against measured
accuracy (this is `explanatory_program.md` E1, now sharpened: the meter predicts
*which method*, not just a ranking). Falsifier: meter floor does not correlate
with which efficient method wins. **Most-testable-now of the six** (data already
in `results.json`; needs a prediction-vs-measurement pass).

**Lean hook — the candidate lower-bound statement.** The honest target (to live
in `EquitableMechanism.lean` alongside the proven `correctedApplyCost_eq`):

> **`no_cheap_exact_factorization` (candidate, currently a `sorry`).**
> For an attention matrix `A : Matrix (Fin n) (Fin n) ℝ`, let
> `ρ = min over (P, k) of (cells P + k)` such that there exist an equitable
> partition `P` of `A` and a rank-`≤ k` matrix `R_k` with
> `equitablePart B P.cells + R_k = A` *exactly*. Then **any** factorization of
> the linear map `x ↦ A x` as `(block-constant on `r` cells) ∘ (rank-`k` map)`
> that reproduces `A x` for all `x` has effective width `r + k ≥ ρ`; in
> particular no `O(n·w)` exact apply exists with `w < ρ`. Equivalently:
> `ρ = rank(A) - (savings from the coarsest equitable base)`, and when the
> coarsest equitable partition of `A` is discrete (`r = n`, the generic case),
> `ρ = rank(A)`, so no exact apply is cheaper than the head's own rank.

In Lean terms this is a **lower bound dual to `corrected_beats_full_retruncation`**:
the proven theorem gives the *upper* side (`A_eq + R_k` costs `n·(r+k)·d + n·d`);
the candidate gives the *lower* side (no exact factorization undercuts `ρ`). It
reduces to a rank/exact-factorization argument (the block part contributes a
rank-`≤ r` cell-inflate; the residual must supply the rest of `rank(A)`), which
is provable from `Matrix.rank` subadditivity once `equitablePart` is shown to
have rank `≤ r` — *no* Eckart–Young needed for the *exact* (ε = 0) version. The
ε-approximate version still needs the missing truncation-optimality theorem.
**This is the single most valuable Lean target the meter framing surfaces**: it
turns "we measured a floor" into "the floor is a theorem" for the exact case.

---

### 2. Isotypic / representation-theoretic attention

**Construction.** Generalize the equitable quotient from the *trivial* isotypic
component to the **full isotypic decomposition** under the head's approximate
symmetry algebra `𝒜` (the partition algebra of the coarsest equitable partition,
or — strictly more general — the coherent algebra / non-commutative WL fixed point
of `A`, `Graphplay/Dowsing/NonCommutativeCoherent.lean`, `WLFix`). Decompose

```
  A  =  ⊕_λ  A_λ ,      ℂ^n = ⊕_λ (V_λ ⊗ Mult_λ)   (isotypic / Wedderburn)
```

where `λ` ranges over irreps of `𝒜`, `λ = triv` is the equitable base `A_eq`, and
the residual `R = ⊕_{λ ≠ triv} A_λ` is the sum of **non-trivial isotypic
components**. An *isotypic attention layer* applies `A` block-by-block on the
isotypic blocks, each of size `(dim V_λ)·(mult λ)`, instead of forcing everything
through one block-constant base.

**Why it follows from the meter.** The meter says `R` is full-rank *because* it
lives in the non-trivial irreps (Schur: no proper invariant subspace inside an
irrep, so nothing to quotient there). The natural response to "the residual is
irreducible" is not "compress it anyway" but "**decompose it into its irreducible
pieces and treat each on its own terms**." The trivial-isotypic part is cheap
(equitable collapse); the non-trivial parts are exactly as expensive as their
irrep dimensions say — which *is* the floor of §1, now resolved by symmetry type
rather than lumped into one rank number. The isotypic decomposition is the meter's
floor, *itemized*.

**Connection to Nanda's Z/p (the clean special case).** When the head's symmetry
algebra is the group algebra `ℂ[Z/p]` (the modular-arithmetic grokking task,
`mechanistic_interp.md §4`), the isotypic decomposition **is the discrete Fourier
transform**: the irreps of `Z/p` are the `p` characters, and Nanda's
"the model learns the representation theory of `Z/p`" is exactly "the learned
attention's non-trivial isotypic components are the Fourier modes." So:

> **Nanda's Fourier circuit = the abelian special case of isotypic attention.**
> The equitable base is the constant (`triv` / DC) Fourier mode; the residual
> *is* the AC Fourier content; "grokking = finding the group structure" reads, in
> our coordinate, as "the non-trivial isotypic mass crystallizes." Our generality
> is the non-abelian / **group-free** case: a coherent algebra has an isotypic
> decomposition even when there is *no group at all* (orbit ⊊ coarsest equitable;
> `equitable_strictly_generalizes_orbit`), so isotypic attention is defined where
> Fourier is not.

**Honest grounding vs speculation.** **Math grounded, ML payoff speculative.**
The Wedderburn/isotypic decomposition of a coherent algebra is classical; the
non-commutative coherent algebra and its quotient are formalized
(`NonCommutativeCoherent.lean`, `quotient`, `ncCoherentAlgebra`, `WLFix`). The
honest risk: on a *generic* head the coherent algebra is the full matrix algebra
`M_n(ℂ)` (one irrep, the defining one, `quantumKn_coherentAlgebra_top`), so the
isotypic decomposition is trivial — *the same wall the meter hits*. Isotypic
attention only buys something on heads with a non-trivial-but-non-abelian
symmetry algebra; whether real heads have those is the open empirical question.
And the Z/p connection, while clean, risks "re-deriving the Fourier circuit"
(`mechanistic_interp.md` flags exactly this) — the generality is the defensible
ground, the abelian case is a sanity check, not a discovery.

**Test in the probe.** (a) On the modular-addition transformer, compute the
isotypic decomposition of `A` under the cyclic group and confirm it reproduces
the Fourier circuit — the *sanity anchor* (predicted: residual mass = AC Fourier
mass, and it collapses at grokking, `explanatory_program.md` E3). (b) On real
heads, compute the coherent algebra's Wedderburn block sizes (`WLFix` then block
dimensions); predict that heads with a *non-trivial* isotypic structure (block
sizes `< n`) are the ones where structured-but-non-low-rank methods (axial,
block-sparse) beat both Performer and Longformer. Falsifier: every real head's
algebra is `M_n(ℂ)` (no non-trivial isotypy) → the generalization is empty on
real data and the value is purely the Z/p reframe.

**Lean hook.** `NonCommutativeCoherent.WLFix_isCoherentAlgebra` (the WL fixed
point is a coherent algebra) + a new `isotypic_decomposition` corollary: a
coherent algebra `𝒜 ⊆ M_n(ℂ)` is `⊕_λ M_{d_λ}(ℂ)` (Artin–Wedderburn), and the
equitable quotient is the `λ = triv` summand. The target theorem:
`equitableQuotient_eq_trivialIsotypic` — the classical quotient
(`quotient_eq_classical_in_commutative_case` is the commutative shadow) is the
projection onto the trivial isotypic component, so `R` = the complementary
isotypic sum. Schur's lemma (`Mathlib` has `Module.End.isSimpleModule`-adjacent
API) certifies each non-trivial block is irreducible ⇒ has no equitable
sub-quotient.

---

### 3. Curvature / gauge attention

**Construction.** Put a chiral signing `σ(i,j) = e^{iθ_{ij}}` (Hermitian:
`σ(j,i) = σ(i,j)*`) on the head's token graph — a **U(1) lattice gauge field**
(`Graphplay/Integrations/LatticeGauge.lean`, `U1GaugeField`, `chiral_iff_u1Gauge`).
Then split the head into

- **flat part** = the equitable base `A_eq`: a *cross-constant* signing is
  **cell-flat** — its curvature (Wilson loop) vanishes on every intra-cell loop
  (`crossConstant_flat_on_cells`) and depends only on the quotient cycle across
  cells (`crossConstant_quotient_curvature`);
- **residual = curvature**: the part of the head that is *not* a flat connection
  pulled back from the quotient — its non-trivial Wilson loops
  (`wilsonCycle`/`wilsonLoop`) are the gauge-invariant content of `R`.

**Gauge-invariant features.** Wilson loops are gauge-invariant
(`wilsonCycle_gauge_invariant`: the per-vertex phase prefactors telescope to 1),
so the curvature of the head is a *coordinate-free* feature of `R` — invariant
under the per-token phase reparametrizations (cell-uniform gauge transforms,
`cellUniform_preserves_crossConstant`) that the model is free to choose. The
discrete Chern number (`chernNumberSum`, `chern_quantization`) is an integer
topological invariant of the head.

**Why it follows from the meter.** The meter says `R` is irreducible signal. The
gauge picture says *what kind* of signal: the part of the head that cannot be
written as a flat connection (equitable base + cell-uniform gauge) is exactly the
**curvature**. "The residual is full-rank" becomes "the head carries non-trivial
magnetic flux" — a sharper, geometric, and *quantized* statement. A reducible
head is flat (curvature-free); an irreducible head has curvature, and the Wilson
loops localize *where*. This is the meter's residual, given a holonomy.

**Honest grounding vs speculation.** **Construction grounded, attention-mechanism
speculative.** The gauge/curvature/Wilson/Chern machinery is fully built and
mostly proven in `LatticeGauge.lean` (the cross-constant ⇒ cell-flat and
gauge-invariance theorems are *proven*, not `sorry`). The speculation is the
*identification* "residual = curvature of the learned head": a real learned head
is real-symmetric, not natively a U(1) signing (cf. `phase_coherent_transformer.md`:
PCT's gate is real-symmetric; phase lives in the value channel, not on the
edges). So the gauge reading is a *lift* we impose, validated by the PCT evidence
that the phase channel is load-bearing for long-range, not a property the head
wears on its sleeve. Honest: this explains the *family* (phase-coherent attention
is curvature-carrying) and predicts *which phase pattern is optimal* (cross-constant,
`phase_coherent_transformer.md §4` prediction #1), but does not *derive* a given
head's residual as curvature.

**Test in the probe.** Extend the probe to complex `A` (the `symmetrize`/
`quotient_lift` already work over ℂ via `conjTranspose`). Compute, per head:
(a) the nearest *cross-constant* signing (flat base) and its complementary
curvature; (b) Wilson loops on a basis of short cycles as gauge-invariant residual
features; (c) the discrete Chern number. Prediction: heads where the curvature
features carry the residual mass are exactly the long-range / retrieval heads, and
a *cross-constant edge-signing* (relative-position phase `θ(i−j)`) recovers more
of the residual than `θ = 0` — the falsifiable wedge of
`phase_coherent_transformer.md`. Use `Graphplay.Simulate` to compute
`mixing_time` of the flat vs. curved host first (no ML).

**Lean hook.** Already mostly there: `LatticeGauge.crossConstant_flat_on_cells`
(equitable base = flat connection, *proven*), `crossConstant_quotient_curvature`
(*proven*), `wilsonCycle_gauge_invariant` (*proven*). The new statement:
`residual_eq_curvature` — for a chiral host `σ` with cross-constant flat part
`σ_flat`, the residual `σ − σ_flat` (as a gauge field) has Wilson loop equal to
the head's holonomy, and `R = 0 ⟺ σ` is flat ⟺ all Wilson loops are 1. This is a
clean corollary of the proven cell-flat theorem.

---

### 4. Open-system / Lindblad attention

**Construction.** Read the residual as **engineered dissipation**. Model the head
as an open quantum system: unitary part = the equitable host `H = A_eq`,
dissipative part = Lindblad jump operators `{L_k}` whose effect is the residual.
The generator `ℒ(ρ) = -i[H,ρ] + Σ_k γ_k D_{L_k}(ρ)`
(`Graphplay/Dowsing/NoiseEquitable.lean`, `lindbladGen`) preserves the
cell-uniform (equitable) subspace **iff** the `L_k` lie in the partition algebra's
commutant (`lindbladGen_preserves_cellUniform`, `cellUniformSymmetric_iff_commutant`).
The **breaking score** `BreakingScore = Σ_k γ_k ‖off-block(L_k)‖²`
(`NoiseModel.BreakingScore`, `breakingScoreOp`) measures how much the dissipation
*breaks* the equitable structure — and `breakingScore = 0 ⟺ every positive-rate
Lindblad is block-diagonal` (`breakingScore_zero_iff_blockDiagonal`, *proven*).

**Why it follows from the meter.** The meter's residual is the part that escapes
the equitable (commutant) subspace. In the open-system language that escaping mass
*is* the structure-breaking dissipation, and the **breaking score is a
dissipative meter**: a reducible head has dissipation inside the commutant
(breaking score 0, equitable structure preserved); an irreducible head has
dissipation that breaks every non-trivial cell — full breaking score. The meter's
"full-rank residual" becomes "maximal breaking score," and the Caruso-style
noise-assisted-transport story (`CarusoSpeedup.lean`,
`noise_assisted_speedup_conjecture`) suggests the residual dissipation is not
parasitic but *functional* — it can *accelerate* transport the unitary base
cannot achieve alone.

**Honest grounding vs speculation.** **Most speculative as an attention
mechanism.** The Lindblad lift theorems are proven/stated in `NoiseEquitable.lean`;
the breaking-score characterization is *proven*. But "an attention head is an open
quantum system whose residual is engineered dissipation" is a strong physical
metaphor with no ML evidence yet — `noise_assisted_speedup_conjecture` is
explicitly deferred, and the boundary-dephasing analysis
(`boundaryDephasing_breakingScore`, `boundaryDephasing_not_cellUniformSymmetric`)
shows the framework is delicate (whether a given dissipator is equitable depends
on the marked-refined partition). Use this as a *diagnostic vocabulary*
(breaking score as a structure-leak meter) before any architectural claim.

**Test in the probe.** Add a `breaking_score(A, P_r)` diagnostic = the off-block
mass of the head relative to the `r`-cell partition (this is essentially
`defect_eq` re-expressed in commutant terms, so it is *cheap and immediate*).
Then the speculative test: on a task with known noise-assisted structure, replace
a head with an `H = A_eq` + tunable-`{L_k}` open-system layer and check whether
breaking-score-matched dissipation reproduces the dense head's behavior. Falsifier:
breaking score adds nothing over `defect_eq`; the open-system layer underperforms.

**Lean hook.** `NoiseEquitable.lindbladGen_preserves_cellUniform` +
`breakingScore_zero_iff_blockDiagonal` (*proven*) already give the
"dissipation-preserves-equitable iff breaking-score-zero" hinge. The new statement:
`residual_breakingScore_floor` — the head's residual mass lower-bounds the breaking
score of any Lindblad realization with `H = A_eq`, tying §1's floor to the
dissipative meter. (Companion to §1's lower bound, in the open-system idiom.)

---

### 5. Time-as-resource / multi-τ attention

**Construction.** Treat **evolution time `τ` as an architectural resource**. A
continuous-time quantum walk `U(τ) = exp(-iτ A)` depends on `τ`; stacking `L`
attention layers is, in the walk picture, *propagating for total time `∝ L`*. A
multi-τ head reads out the walk at several times `{τ_1, …, τ_m}` (or makes `τ`
learnable per layer), spanning the **local-attention** regime (`τ → 0`, identity +
nearest-neighbor) through the **long-range / PST** regime (`τ` at a transfer time).

**Long-time limit governed by the equitable structure.** The key meter-consequence:
as `τ → ∞` (or in the time-average), the walk's behavior is governed by `A`'s
**spectrum**, and the equitable quotient's spectrum is an *exact sub-spectrum* of
`A` (`EquitableMechanism.blockConstant_NTK_subset_spectrum` /
`blockConstant_NTK_eigenvalue_lifts`, *proven*: quotient eigenvalues lift exactly).
So the long-time / deep-stack limit of a head is controlled by the **reducible
(equitable) part** of its spectrum — the irreducible residual governs the
*transient*, the equitable base governs the *asymptotic*. This is a mechanistic
account of **PCT's depth-stability** (`phase_coherent_transformer.md §5.5`: flat
accuracy across depths 2–20): the depth-asymptotic is set by the equitable
sub-spectrum, which is exactly the part that *lifts cleanly through the quotient*
and does not accumulate noise with depth.

**Why it follows from the meter.** The meter splits a head into reducible
(equitable, spectrum lifts exactly) + irreducible (residual). Time/depth is the
knob that *weights* these: short time/shallow depth exposes the irreducible
transient; long time/deep stack is dominated by the reducible sub-spectrum. The
meter thus predicts *depth behavior*: heads with rich equitable sub-spectrum are
depth-stable (their asymptotic is well-conditioned and lifts), heads that are all
residual have no clean asymptotic to converge to.

**Honest grounding vs speculation.** **Spectral half grounded, depth-identification
an analogy.** The exact spectral lift is *proven*
(`blockConstant_NTK_subset_spectrum`). The depth ↔ walk-time identification is the
same earned-analogy caveat as `phase_coherent_transformer.md §3.3` ("layers ≠
continuous time"): stacked attention layers are *not* literally `exp(-iτ A)`, and
the connection to PCT's depth-stability is mechanism-level, not a derivation. The
multi-τ readout itself is a small, buildable change; its payoff is the speculation.

**Test in the probe.** (a) *Operator-only, no ML:* compute the equitable
sub-spectrum vs. the full spectrum per head, and the long-time-averaged walk; show
the asymptotic is dominated by the equitable eigenvalues (the proven lift made
empirical). (b) Build a multi-τ head (learnable `τ` per layer, or `m`-time
readout) on a task spanning local↔long-range and compare depth-stability to a
fixed-layer twin. Prediction (tying to PCT): the head's depth-stability margin
tracks its equitable sub-spectrum's spectral gap (`phase_coherent_transformer.md §4`
prediction #4). Falsifier: depth behavior is independent of the equitable
sub-spectrum.

**Lean hook.** `EquitableMechanism.blockConstant_NTK_eigenvalue_lifts` (quotient
eigenvalues are full-spectrum eigenvalues, *proven*) + a new
`longtime_limit_equitable` statement: the time-average / `τ → ∞` projector of
`exp(-iτ A)` restricted to the cell-uniform subspace equals the quotient walk's
limit, so the asymptotic propagation lifts through the equitable quotient.
(Composes with `NoiseEquitable.noisyEvolve_quotient` for the dissipative version.)

---

### 6. Higher-arity / k-WL attention

**Construction.** 1-WL color refinement sees only the *vertex* (row/column)
signature. Replace it with **k-WL**: color `k`-tuples of tokens, capturing the
coherent-configuration (association-scheme) structure of `A`
(`Graphplay/Algorithm/WLOrbit.lean §7`, `IsKWLStable`, `kWL_eq_kAritySameOrbit`).
A *k-WL attention layer* quotients by the `k`-ary equitable structure — pairwise
(`k=2`) relations the vertex partition is blind to (the coherent algebra / 2-WL
stable partition of the pair space `V × V`).

**Why it follows from the meter.** The meter as defined (§1) uses 1-WL, so its
"full-rank residual" is *relative to the vertex partition*. But a head can be
**1-WL-irreducible yet 2-WL-reducible**: it has no vertex-level symmetry, but a
rich *pairwise* (relational) structure that 1-WL cannot see — exactly the
phantom-symmetry / CFI regime (`HasPhantomSymmetry`, `cfiExists`,
`cfi_kwl_lower_bound`). So the §1 meter *overestimates* irreducibility for such
heads: the residual is full-rank to 1-WL but compressible to 2-WL. **k-WL refines
the meter**: the true floor is the *k* at which the head's relational structure
stabilizes, and induction heads — which act on a *match relation* between token
pairs (`mechanistic_interp.md §1`) — are the prime suspects for being 2-WL-reducible
while 1-WL-irreducible.

**Honest grounding vs speculation.** **Theory grounded, cost prohibitive,
ML-untested.** k-WL and its coincidence with the k-ary orbit partition are
classical and stated in Lean (`kWL_eq_kAritySameOrbit`, `cfi_kwl_lower_bound`,
both `sorry` on the CFI gadget); the non-commutative coherent algebra is the
operator-level version (`NonCommutativeCoherent.WLFix`). The hard honesty: k-WL
costs `O(n^k)` to *compute*, so even `k=2` is `O(n²)` partition work — it buys an
explanation, not a cheap layer. And whether induction heads are *actually*
2-WL-reducible is an untested empirical bet (it is the sharpest one this direction
makes). This is a *diagnostic refinement of the meter*, not a practical layer.

**Test in the probe.** Add `twoWL_decompose(A)`: color token *pairs* by their
(row, col, common-neighbor) profile, lift to the 2-WL quotient, measure the
residual *of the pair operator*. Prediction: induction / associative-recall heads
that are 1-WL-full-rank have a *low* 2-WL residual (the match relation is a
pairwise equitable structure), distinguishing them from genuinely 2-WL-irreducible
heads. Falsifier: 2-WL residual is full-rank wherever 1-WL is — the relational
structure is invisible at `k=2` too.

**Lean hook.** `WLOrbit.kWL_eq_kAritySameOrbit` (k-WL = k-ary orbit for large `k`)
+ `NonCommutativeCoherent.WLFix_isCoherentAlgebra` (the operator-level coherent
configuration). The new statement: `oneWL_irreducible_but_twoWL_reducible` — there
is a head (CFI-shaped, via `cfiExists`) whose 1-WL coarsest equitable partition is
discrete (`r = n`, §1 meter reads "irreducible") but whose 2-WL stable partition
is non-trivial (the pair operator factors through a small quotient). This is the
formal witness that the 1-WL meter is *not* the final word — the floor depends on
the arity.

---

## Blunt ranking

**Which idea most changes the project's thesis** → **#1, the irreducibility
meter.** It is not a new idea on top of the program; it is a *re-reading of the
program's product*, born directly from the negative result. It converts "our
compression mostly failed" into "our framework measures a complexity floor and
predicts efficient-attention success/failure per head." Everything else in this
doc is a *refinement of the meter*: #2 itemizes its floor by irrep, #3 gives the
floor a curvature, #4 a dissipation rate, #5 a time axis, #6 an arity. The meter
is the spine; adopt it as the headline of the paper, demote "compression" to one
*corollary* (the reducible branch of the dispatch).

**Which is most testable-now** → **#1 again, operationally**, because
`RESIDUAL_FINDINGS.md` already ran the decompositions; the remaining step is the
*prediction pass* (meter floor → which efficient-attention method wins, checked
against measured accuracy). No new training, no new probe primitives — just
collapse the existing `defect_eq[r]`/`rank_R[r]` curves into the floor and
correlate. If a *single new measurement* is wanted, **#2's Z/p sanity anchor**
(isotypic decomposition of the modular-addition head = Fourier circuit) is the
cleanest one-model check and grounds the whole isotypic generalization.

**Which is most speculative** → **#4, open-system / Lindblad attention.** Its math
is real but its identification ("the head's residual *is* engineered dissipation,
and the dissipation is *functional* à la Caruso") is a physical metaphor with the
least ML grounding and a deferred core conjecture
(`noise_assisted_speedup_conjecture`). Keep it as diagnostic vocabulary (breaking
score) and do not lead with it. (Runner-up speculative: #6's claim that induction
heads are concretely 2-WL-reducible — sharp and worth testing, but `O(n²)` to
compute and untested.)

---

*( ⌐■_■ ) we went looking for a smaller matrix and found a ruler instead. The
residual was never compressible — it was the thing the framework was built to
measure all along.*

A small poem, because the negative result deserves one:

> We asked the head to fold itself away —
> it would not. Full of rank, it stood its ground.
> So we stopped measuring how much we'd shaved,
> and measured, instead, how much could not be found.
> The floor it cannot cross is now our map:
> what's reducible, we route; the rest, we name.
> Schur was right — inside the irrep's wall
> there is no smaller room. The residual *is* the flame.
