# Novel attention/architecture "bets" from the equitable-partition + quantum-walk vantage

*A research-strategy design doc. Status: speculative-but-grounded. Each bet is
tied to (i) a concrete Graphplay/quantum-walk result, (ii) the mechanism the
framework predicts, (iii) the closest existing bet it generalizes — with an
honest verdict on whether it is genuinely unmade, (iv) a probe-harness test
plan, (v) a speculative-vs-grounded rating.*

Companion formalization (in parallel): `Graphplay/Integrations/NovelAttention.lean`
(does **not yet exist** at time of writing — this doc is the spec it should
discharge; theorem names referenced below are the targets, not yet proven).

---

## 0. The vantage, in one paragraph

The explanatory program (`paper/explanatory_program.md`) reframes every attention
variant as a *projection* `Π_M(A*)` of the ideal full attention onto a structured
submanifold `M`, with performance `∝ ‖Π_M(A*)‖/‖A*‖` and failure `∝ ‖A* − Π_M(A*)‖`.
The submanifolds already in play — low-rank (Linformer/Performer), sparse
(Longformer/BigBird), banded (Mistral SWA), equitable/orbit (Set Transformer,
GQA, axial) — are *static linear* projections. The quantum-walk vantage adds two
things the field has not imported into attention design:

1. **The equitable quotient is a dynamical object, not just a sparsity pattern.**
   Graphplay proves (machine-checked) that *spectrum, PST, mixing, search, and
   fractional revival lift exactly through the equitable quotient*
   (`EquitablePartition.*Lift`, `PST.IsCellUniformPST`, `mera_exact_iff_equitable`).
   So "attention as a graph operator" can carry **provably-controlled propagation
   dynamics** (transfer, revival, ballistic spread), not just a block average.

2. **There are richer host operators than the symmetric real kernel.** Chiral
   (U(1)-phased) signings (`Graphplay.Chiral`), discrete-time coined/Dirac walks
   (`Graphplay.StdLib.CoinedWalk`), and Lindbladian/noisy generators each give a
   *different propagation regime* (faster mixing, ballistic vs. diffusive, etc.)
   that the equitable lift still respects. The bet is that these regimes are the
   right inductive bias for the failure modes (long-range, sharp routing) that
   the *static* submanifolds cannot represent.

The honest frame, inherited from the lit verdicts: **"symmetry + soft residual"
is GDL/approximate-equivariance prior art; "structured base + low-rank residual"
is Scatterbrain/LoRA prior art.** What is genuinely unmade is *using the
quantum-walk dynamics that lift through the quotient as the attention mechanism
itself.* Every bet below is judged against that line.

---

## The bets

### Bet 1 — Hierarchical / MERA equitable attention (nested partitions)

**(i) Construction.** A tower of equitable partitions `P_0 ⊐ P_1 ⊐ … ⊐ P_L`
(each coarser than the last), with one attention operator per level acting on the
quotient of the level below. Tokens attend densely within a fine cell, then the
cell-uniform summaries attend at the next coarser scale, recursively. Backed by
`mera_exact_iff_equitable` (`Graphplay/Integrations/TensorNetworks.lean:342`): a
MERA renormalization tower is *exact* iff each coarse-graining map is literally
the cell-map of an equitable partition of the effective Hamiltonian, with
quotient-compatible level operators.

**(ii) Mechanism.** A single equitable partition with `r` cells can only
represent block-constant structure at *one* granularity; its residual `R` carries
everything at other scales (the rank-collapse caveat: if `A_eq` is too coarse,
`R` is where the signal lives). A *tower* lets each scale's `A_eq` be cheap
(`O(n·r)` per level) while the composition represents multi-scale structure that
no single `r`-cell projection can. The MERA theorem says the spectral/dynamical
content of the host descends *exactly* through the nested quotients, so the
hierarchical apply is not a lossy approximation of a target attention — it is the
exact attention for any host whose RG flow is finite. The framework prediction:
on tasks with genuine scale hierarchy (long documents, nested syntax, multi-
resolution images), the *summed* residual across a tower drops far below the
single-level residual at matched total cost.

**(iii) What it generalizes / honesty.** Generalizes axial attention (a 2-level
factorization) and hierarchical/coarse-to-fine transformers (H-Transformer-1D,
Hourglass, Funnel-Transformer, MERA-as-ML of Stoudenmire/Evenbly). **This is the
most-anticipated bet.** The RG/coarse-graining-as-deep-learning slogan is owned
piecewise (Mehta–Schwab, Li–Wang; `paper/lit/rg_coarsegraining.md`), and
hierarchical transformers exist. The genuinely unmade piece, per that lit note,
is the **exactness criterion**: *the hierarchy is lossless for the spectrum iff
each level is a literal equitable cell-map.* Nobody trains a hierarchical
attention with the equitable branching equation as the **constraint that makes
each coarse-graining exact** (vs. learned-and-approximate pooling). That
constraint — and using `‖R‖` per level as the diagnostic that the pooling is
"doing no work beyond cell relabelling" — is the new content.

**(iv) Test in probe harness.** The probe already computes nested structure
implicitly via the `r_sweep`. Concretely: (a) run `decompose(A, r_sweep)` on a
trained hierarchical model and a flat baseline; (b) extend the probe with a
`tower_decompose(A, r_schedule)` that iteratively lifts — `A_eq^(0)` at fine `r_0`,
then run `decompose` on the *residual* `R^(0)` at coarser `r_1`, etc. — and report
the **cumulative captured fraction** `1 − ‖R^(L)‖/‖A‖` vs. a single-level lift at
matched `∑ r`. Prediction: tower captures strictly more at matched cost on
hierarchical-structure tasks (E1 battery: nested-syntax / long-range copy) and
ties on flat tasks. Cheap: pure linear algebra on existing `quotient_lift`.

**(v) Rating.** **Grounded-leaning (low speculation on the math, medium on the ML
payoff).** The exact-lift theorem is machine-checked; the open question is purely
empirical (does the multi-scale residual actually drop on real tasks, or does
learned pooling already capture it). Closest to a "sure thing" mathematically,
least novel conceptually.

---

### Bet 2 — Learned / adaptive equitable partition (differentiable cell assignment)

**(i) Construction.** Make the cell-assignment `cell : token → Fin r` a *learned,
differentiable* soft assignment `S ∈ ℝ^{n×r}` (row-stochastic), with the
attention `A = S Q̃ Sᵀ + R` where `Q̃` is the `r×r` symmetric quotient
(`symmetric_quotient` in the probe) and `R` a low-rank steered correction. The
training signal includes the **equitability defect `‖R‖ = ‖A − S Q̃ Sᵀ‖`** as a
regularizer or as a measured progress signal. Backed by
`equitableOfAutomorphism` / `EquitablePartition.restrict_eq_symmQuotient`
(`Graphplay/Integrations/MachineLearning.lean`, `StructuredAttention.lean §2`):
once the partition is equitable, the apply collapses to the `r×r` quotient
exactly.

**(ii) Mechanism.** GQA, BigBird, axial, and Set-Transformer inducing points all
**impose** the partition (KV-group, block pattern, axes, fixed `m` inducing
points) a priori. If the data's natural symmetry ≠ the imposed one, the
explanatory program predicts a large defect concentrated exactly on the
mismatch (E2). A *learned* partition lets the model find the cells the data
actually has — the move the lit notes repeatedly flag as the wedge: Nanda's
grokking finds the *group* structure; we want the model to find the *equitable
partition* (strictly more general — orbit partition ⊊ coarsest equitable
partition, valid even with no symmetry group). Using `‖R(t)‖`-collapse as the
training signal operationalizes E3 ("generalization onsets when the equitable
partition crystallizes") as an actual loss term, not just a post-hoc measurement.

**(iii) What it generalizes / honesty.** Generalizes GQA/MQA (learned-vs-imposed
KV grouping), BigBird/Longformer (learned-vs-fixed sparse pattern), and the
inducing-point bottleneck of Set Transformer (learned-vs-fixed `m`). Adjacent
prior art: routing/clustered attention (Routing Transformer's k-means buckets,
Reformer's LSH buckets, Clustered Attention) *already learn data-dependent token
groupings* — so "learn the buckets" is **not** novel. Per `paper/lit/lowrank_attention.md`
(Scatterbrain) and `geometric_dl.md` (approximate equivariance), the *idea* of a
learned/soft structured component is owned. **The genuinely unmade piece:** (a)
the bucket operator being the **symmetric normalized quotient `Q̃ = D^{1/2}QD^{-1/2}`**
whose eigenvalues are a *certified subset* of the host spectrum (routing/LSH
buckets carry no spectral-lift guarantee), and (b) **`‖R‖` as an explicit
differentiable equitability-defect objective** that drives the partition toward
the one under which dynamics provably descend. No routing-attention paper
minimizes the equitable defect or reads off the quotient spectrum.

**(iv) Test in probe harness.** Two-stage. *Stage A (measurement, cheap):* on
existing routing/clustered-attention checkpoints, run `decompose` with the
*model's own* learned partition (feed it as `partition` to `quotient_lift`) vs.
the probe's `spectral_partition(A, r)` and vs. `equitable_partition_wl` — does the
learned partition already have lower `defect_eq` than a same-`r` spectral one?
*Stage B (intervention, medium):* add `λ·‖R‖` to a small 2-layer model's loss and
track `defect_eq[r]` and cell stability across training (E3); prediction: the
defect-regularized model groks earlier / generalizes at lower `‖R‖`, and its cells
match the task's known equivalence classes (induction match-relation, modular-
arithmetic cosets). Falsifier: defect regularization hurts or the cells don't
align.

**(v) Rating.** **Medium speculation.** The collapse theorem is solid; the
differentiable-partition plumbing is standard (Gumbel-softmax / Sinkhorn over `S`).
The bet is that the *spectral-lift* framing buys something over plain learned
routing — plausible but unproven, and the honest risk is it just reproduces
Routing Transformer with extra steps.

---

### Bet 3 — Chiral / phased / directed attention (U(1) edge phases)

**(i) Construction.** Give the attention graph a **chiral signing** `σ(i,j) = e^{iθ_{ij}}`
with the Hermitian condition `σ(j,i) = σ(i,j)*` (`Graphplay.Chiral.ChiralSigning`),
so the (symmetrized) host is the *magnetic* adjacency `σ_{ij}·A_{ij}` and the walk
generator carries U(1) phases. The phases `θ` are learned (or fixed to a
structured pattern, e.g. relative-position-dependent `θ_{ij} = f(i−j)`). Backed by
`Graphplay.Chiral` / `Graphplay.Dowsing.ChiralGraphon` and the Levine–Mesapam–
Mustico–Tamon–Tucker–Zhan result (arXiv:2605.04414): a chiral signing of `K_n`
achieves uniform mixing, and a specific `K_4` signing mixes **faster than any
unoriented Hamming graph** (the "π/3√3 faster mixing" headline).

**(ii) Mechanism.** Real-symmetric attention is *time-reversal-symmetric*: the
walk has no preferred direction and mixing/transfer is bounded by the unsigned
spectral gap. Adding U(1) phases breaks time-reversal symmetry and can *strictly
accelerate mixing* (the chiral-mixing theorem) — the quantum analogue of why
directed/rotational flows mix faster than reversible diffusion. The framework
prediction: **phased attention reaches long-range mixing in fewer layers** than
real attention, because the host's mixing time is shorter. This directly attacks
the long-range-dependency failure mode of banded/local attention. Crucially the
chiral signing **preserves the fiber-equitable partition** (cell row-sums on `|adj|`
are unchanged; `Graphplay.Chiral`), so phasing composes with Bets 1–2: you get
faster mixing *and* the quotient collapse.

**(iii) What it generalizes / honesty.** Generalizes RoPE / relative-position
encodings (which are a *commutative, per-query* phase rotation of Q·K) to a
genuine **non-commutative U(1) gauge field on the edges**, and generalizes
directed-graph / asymmetric attention (which the field uses but without a mixing-
time guarantee). Adjacent prior art: complex-valued / unitary attention exists in
scattered work, and magnetic Laplacians appear in directed-graph GNNs (MagNet,
Zhang et al.). So "complex phases in attention" is **partly anticipated**. The
genuinely unmade piece: **(a) the phase pattern chosen/learned to *minimize
mixing time* via the chiral-mixing theorem**, and (b) the guarantee that phasing
**preserves the equitable quotient** so the speedup composes with the `O(n·r)`
collapse. MagNet uses a *fixed* magnetic Laplacian for node classification, not a
*learned phase optimized for propagation speed* in a sequence model, and carries
no quotient-lift. No one has built "attention whose edge phases are tuned for the
Levine fast-mixing regime."

**(iv) Test in probe harness.** *Measurement:* extend the probe to accept
complex `A` (the `_symmetrize` and `quotient_lift` already work over ℂ with
`conjTranspose`); add a `mixing_time(A)` diagnostic = number of `U(τ)=exp(-iτA)`
steps for the vertex distribution to reach ε-uniform, comparing a real head vs.
its best-phased version. *Intervention:* train a tiny model with learnable edge
phases `θ_{ij}` on a long-range task (LRA-style: ListOps, long-range copy,
path-finding) and measure layers-to-solve vs. a real-attention twin at matched
params. Prediction: phased model needs fewer layers for the same long-range
accuracy. Falsifier: no layer-count advantage, or phases collapse to 0 in training.

**(v) Rating.** **Medium-high speculation, high-novelty.** The mixing theorem is
real and recent (2026), and "faster mixing → fewer layers for long-range" is a
clean mechanistic story — but the leap from CTQW mixing-time to *transformer
layer count* is an analogy that must be earned empirically. Most likely to either
clearly work or clearly not. High upside if it does.

---

### Bet 4 — PST routing attention (lossless perfect transfer between token groups)

**(i) Construction.** Engineer the attention host so the walk performs **perfect
state transfer (PST)** between designated token groups at the layer's evolution
time: `‖U(τ)_{C_i,C_j}‖ = 1` (`Graphplay.PST.IsCellUniformPST`,
`Graphplay/PST.lean:39`). Concretely, between a "source" cell (e.g. the prompt
key positions) and a "sink" cell (the query/output positions), pick a
quotient-PST host (a path/Hamming/Cartesian-product quotient with known PST
times; `Graphplay.Product.PST`, hypercube PST). The cell-uniform PST lift
guarantees the group-to-group transfer is exact.

**(ii) Mechanism.** Standard attention *spreads* mass (softmax mixes
many sources); even a sharp head leaks. PST is the unique regime where amplitude
moves *losslessly and completely* from one group to another — a provably-clean
"route this information block to that position" primitive. The framework
prediction: on tasks that need **exact, complete routing** (copying a span,
pointer/index lookup, deterministic addressing), a PST-routed head has *zero*
transfer loss where a softmax head has `O(1)` leakage that grows with sequence
length. This is the structural cure for the induction/copying failure mode that
low-rank attention cannot represent (E2).

**(iii) What it generalizes / honesty.** Generalizes induction heads (which
*approximately* route the matched token forward) and pointer/copy mechanisms
(CopyNet, Pointer Networks) by giving them a **lossless, time-parameterized
transfer law** with a closed-form transfer time. **Honesty:** this is the most
exotic bet and the least anticipated — but also the one where "is this even the
right primitive for attention?" is genuinely open. PST is a *fragile, fine-tuned*
phenomenon (it needs eigenvalue ratio conditions, `Graphplay.PST.GodsilRatio`);
a learned attention won't sit exactly at a PST host. So the realistic version is
**approximate / fractional** routing (→ Bet 5), and pure-PST attention is closer
to a *theoretical limiting case* than a buildable layer. No prior art uses PST as
an attention mechanism (PST is a quantum-walk / quantum-computing notion); that
part is unmade, but partly because it may not be the right tool.

**(iv) Test in probe harness.** *Measurement:* add `pst_score(A, C_i, C_j, τ)` =
`‖U(τ)_{C_i,C_j}‖` swept over τ, to detect whether any trained copy/induction head
*already* sits near a PST-like transfer (prediction: induction heads have high
peak transfer between match-position cells). *Synthesis:* on a pure copy task,
hard-wire one head's host to a known-PST quotient (path graph `P_n` has antipodal
PST at τ=π/2 after Christandl) and measure exactness vs. a learned softmax head.
Use the existing CTQW simulator (`Graphplay.Simulate`) to validate the transfer
numerically before touching ML. Falsifier: induction heads show no PST signature
and hard-wired PST hosts don't beat softmax on copying.

**(v) Rating.** **High speculation.** Cleanest theory (PST is fully machine-
checked across the repo), but the biggest "is this the right abstraction?" risk:
PST's fragility may make pure-PST attention impractical, pushing all real value
into Bet 5. Document it as the *idealized endpoint* whose practical form is
fractional revival.

---

### Bet 5 — Fractional-revival attention (provably-controlled (α,β) split)

**(i) Construction.** Tune the host so the walk performs **fractional revival
(FR)**: `U(τ)|u⟩ = α|u⟩ + β|v⟩` with `|α|²+|β|²=1`
(`Graphplay.Dowsing.FractionalRevivalNC`, Chan–Coutinho–Tamon–Vinet–Zhan
arXiv:1907.04729). Between token groups, the cell-uniform FR lift gives a
**provably-controlled split** of amplitude: a learnable `(α,β)` controls how much
information stays local vs. routes to the target cell, with `|α|²+|β|²=1`
enforced *by unitarity*, not by a softmax normalization.

**(ii) Mechanism.** FR is the **realistic relaxation of Bet 4**: instead of
demanding lossless complete transfer (fragile), it gives a *tunable, unitary,
norm-preserving* split between "keep here" (`α`) and "route there" (`β`). This is
exactly a soft-but-norm-exact gate. The framework prediction: an FR head is a
**better-conditioned router** than softmax — the `|α|²+|β|²=1` constraint is a
hard conservation law (ties to Bet 8), so the head cannot leak mass to
unintended positions, and the split is differentiable in `(α,β)`. It interpolates
continuously between "stay local" (β→0, periodicity) and "PST route" (α→0), so
one mechanism spans the local-attention and copy-attention regimes that today
need different architectures.

**(iii) What it generalizes / honesty.** Generalizes gating (LSTM/GRU/Highway
gates split information between keep and update) and the residual/attention
mix, by giving the split a **unitary, spectrally-lifted** law instead of an
elementwise sigmoid. Adjacent: gated attention and mixture-of-depths route
fractionally already, so "fractional routing" is **not** novel as a behavior.
Genuinely unmade: the split governed by an **FR host whose `(α,β)` lifts through
the equitable quotient** (`Graphplay.Dowsing.FractionalRevivalNC` Tower-2 lift),
i.e. a routing gate with a *certified* norm-exact transfer law and a quotient
collapse. No gating mechanism is derived from a quantum-walk revival.

**(iv) Test in probe harness.** *Measurement:* `fr_split(A, u, v, τ)` returning
the fitted `(α,β)` of `U(τ)|u⟩` projected onto `{|u⟩,|v⟩}` and the residual leakage
`1 − |α|² − |β|²`; sweep heads to find near-FR ones. *Intervention:* replace one
head's softmax with a 2-parameter `(α,β)` FR gate on a task needing controlled
keep/route (selective copying, associative recall) and compare to a sigmoid gate
at matched params. Prediction: FR gate has lower leakage and matches/beats sigmoid
gating on recall precision. Use `Graphplay.Simulate` FR runs to validate `(α,β)`
control first.

**(v) Rating.** **Medium-high speculation, but the most *practically promising*
of the quantum-walk bets** — it inherits Bet 4's clean theory while being robust
(FR is a 2-parameter family, not a knife-edge). The realistic carrier of the
PST/routing idea.

---

### Bet 6 — Coined-walk / Dirac attention (ballistic vs. diffusive propagation)

**(i) Construction.** Replace the continuous-time vertex walk with the
**discrete-time coined / Szegedy walk on the arc space** `ℂ^{V×V}`: one step
`U = S·C` with flip-flop shift `S` and Grover coin `C`
(`Graphplay.StdLib.CoinedWalk`, `coinedStep`, proven unitary). Attention becomes
a coined walk: tokens carry an internal "coin"/direction state, and information
propagates *ballistically* (linear-dispersion / Dirac-like) rather than
diffusively. The equitable lift still holds: a graph automorphism commutes with
the coined step (`grover_walk_commutes_with_automorphism`,
`CoinedWalk.lean:466`), so the arc-space walk descends to the quotient.

**(ii) Mechanism.** This is the **sharpest mechanistic bet against low-rank
attention.** A diffusive (CTQW / heat-kernel / softmax-smoothed) walk spreads as
`√t` and is well-approximated low-rank — exactly why Linformer/Performer work,
and exactly why they *fail* on sharp long-range tasks (induction, copying;
`paper/lit/lowrank_attention.md`). A coined walk has **linear (ballistic)
dispersion**: a localized excitation travels at constant speed with a sharp
wavefront (the Dirac/Hadamard-walk light-cone). The framework prediction: on
tasks where information must travel a long, *exact* distance without smearing
(long-range copy, path-finding, sequential addressing), the coined-walk head
**reaches the target in `O(distance)` steps with a sharp front**, where a
diffusive head smears over `O(distance²)` and a low-rank head cannot represent the
sharp front at all. The arc-space (direction-carrying) state is precisely the
extra degree of freedom low-rank attention lacks.

**(iii) What it generalizes / honesty.** Generalizes the implicit "propagation"
view of stacked attention layers (each layer = one diffusion step) by swapping
the *generator* from diffusive to ballistic. Adjacent prior art: there is a small
literature on quantum-walk neural networks and Dirac/Lorentz-equivariant
networks, and SSMs (S4/Mamba) already engineer *non-diffusive* long-range
propagation via structured linear recurrences. So "engineer better-than-diffusive
propagation" is **anticipated by the SSM line** — this is the honest collision.
Genuinely unmade: **a coined/arc-space attention with the proven unitary step and
the automorphism quotient**, i.e. ballistic propagation that *also* carries the
equitable collapse. The connection "low-rank attention is diffusive, so a
ballistic coined walk should beat it on long-range" is, as far as the lit sweep
shows, not made anywhere — and it is sharp and falsifiable.

**(iv) Test in probe harness.** *Measurement (no ML needed first):* use
`Graphplay.Simulate` to run the coined walk vs. CTQW on a path/grid and plot the
spreading exponent (ballistic `t` vs. diffusive `√t`) — this is a pure
simulator experiment that establishes the mechanism. *Probe extension:* the arc
space is `n²`-dimensional, so the probe's `decompose` applies to the arc-space
operator; measure `rank_R` of the coined-step quotient residual. *Intervention:*
a coined-walk attention layer (token = vertex amplitude + coin) on long-range
copy, vs. a low-rank (Performer) head and an SSM baseline, measuring accuracy vs.
distance. Prediction: coined head's accuracy is flat in distance where Performer's
decays. Falsifier: SSM already captures all the ballistic benefit, or the
arc-space cost kills it.

**(v) Rating.** **Medium-high speculation, highest "interesting if true" payoff.**
The ballistic-vs-diffusive contrast is a genuinely new and testable mechanistic
claim about *why* low-rank attention fails on long-range, and the coined walk is
fully proven unitary + quotient-compatible in the repo. The honest risk is the
SSM line may already own the practical benefit; the differentiator is the
arc-space direction state + the quotient lift.

---

### Bet 7 — Quotient-residual layer (explicit `A_eq` + steered `R`, with `(r,k)` knobs)

**(i) Construction.** The explicit `A = A_eq(P_r) + R_k` layer: a cell-constant
equitable base `A_eq = S Q̃ Sᵀ` (apply cost `O(n·r)`, `StructuredAttention.segment_attention_exact_reduction`)
plus a **low-rank steered residual** `R_k = U V^T` (rank `k`, apply cost `O(n·k)`),
with `(r,k)` as explicit architectural knobs. This is the literal `A = A_eq + R`
decomposition the explanatory program centers on, turned into a *primitive layer*.

**(ii) Mechanism.** The base captures the symmetric/structured mass cheaply via
the quotient collapse; the low-rank residual carries the *steering* (the
deviation that the rank-collapse paper says holds the signal). The framework
prediction (E1): with `(r,k)` sized to the task's measured `(defect_eq, rank_R)`
coordinate, this single layer matches dense attention at `O(n(r+k))`, and the
knobs let you *dial* the structural-vs-steered budget to the task. The equitable
base is cheap *because of symmetry/quotienting*, not because it is itself sparse
or low-rank — the wedge `paper/lit/lowrank_attention.md` identifies.

**(iii) What it generalizes / honesty.** Directly generalizes **Scatterbrain**
(sparse + low-rank) by swapping the sparse summand for an **equitable-quotient**
summand, and **LoRA** (base + low-rank) from weight-space to attention-space.
**Strong honesty required:** Scatterbrain and LoRA own "structured base + low-rank
correction"; this is explicitly *their template*. Per the lit verdict, the *only*
defensible novelty is **(a) the base is an equitable quotient applied in `O(n·r)`
via symmetry, not via sparsity, and (b) an empirical demonstration that
`rank(A − A_eq)` is small for an equitable `A_eq`** — a measurement **no cited
work performs**. So this bet is less "new architecture" and more "the architecture
that makes the explanatory program's central measurement actionable."

**(iv) Test in probe harness.** This is *exactly* what `decompose` already measures
— `defect_eq[r]`, `rank_R[r]`, `lowrank_resid_norm[k]` per sweep value. The test
is E1/E2 verbatim: (a) confirm `rank_R` is small for equitable `A_eq` on real
heads (the live-or-dead question); (b) build the `(r,k)` layer and check it matches
dense at the `(r,k)` the probe predicts; (c) compare against a Scatterbrain
(sparse+low-rank) layer at matched budget — does the equitable base win where the
data has block/permutation (full-rank-but-cheap) structure that sparse misses?
Falsifier (honest): if `rank_R` is fat (rank-collapse caveat), the bet dies and we
report it.

**(v) Rating.** **Grounded (lowest speculation), lowest conceptual novelty.** The
math is the proven collapse; the risk is entirely "is the residual actually
low-rank after an equitable base," which the probe answers directly. This is the
*safe* bet and the natural first build.

---

### Bet 8 — Conservation-regularized attention (Noether invariant as training stabilizer)

**(i) Construction.** Add the **conserved quantity of the equitable structure** as
a training regularizer / monitored invariant. The repo proves a *discrete
gradient-step invariant*: an equitable partition is preserved by an SGD step under
weight-tying (`training_step_linear_under_equitable`,
`Graphplay/Integrations/AttentionComplexity.lean`), and `Graphplay.ConservationLaw`
formalizes the Noether-style invariant. Operationally: penalize drift of the
cell-uniform-subspace projection (or the quotient-spectrum subset) across steps,
i.e. regularize `‖A_eq(t+1) − A_eq(t)‖` toward the structure-preserving update.

**(ii) Mechanism.** The edge-of-stability lit (`paper/lit/edge_of_stability.md`)
shows training dynamics are governed by the Hessian spectrum, and symmetry pins a
*computable subset* of that spectrum. The framework prediction (E4, the novel open
one): **the equitable/quotient subspace has its own sharpness**, and conserving
the equitable structure stabilizes training by keeping that subspace's sharpness
away from the `2/η` edge — a structure-aware analogue of gradient clipping /
sharpness-aware minimization. The conservation law (`|α|²+|β|²` in Bet 5 is the
unitary instance) acts as a Lyapunov-style stabilizer.

**(iii) What it generalizes / honesty.** Generalizes SAM (sharpness-aware
minimization) and conservation-based analyses (Kunin's Neural Mechanics, Zhao's
conserved-quantities-of-gradient-flow). **Heavy honesty:** per `edge_of_stability.md`,
"symmetry → conserved quantity → constrained dynamics" is **fully prior art**
(Kunin 2020, Zhao 2022), and "symmetry → Hessian degeneracy" is Şimşek 2021. The
*only* unmade pieces flagged there: (a) the **discrete, formally-verified**
step-invariant (we have it in Lean), and (b) the **open question E4** — does the
quotient subspace sit at its *own* edge of stability vs. `2/η`? Nobody has asked
this. So this bet's novelty is **almost entirely the E4 measurement**, not the
regularizer (which is a known genre). Frame it as "test whether the equitable
subspace has a distinct EoS, and if so use the conserved structure to stabilize
it" — and concede the conservation-law framing is borrowed.

**(iv) Test in probe harness.** *Measurement (E4):* extend the probe to compute,
during a training run, the Hessian (or its top eigenvalues via Lanczos) **restricted
to the cell-uniform subspace** `P.cellUniformSubspace` vs. the full Hessian, and
track both against `2/η`. Prediction: the quotient subspace has a distinct
sharpness trajectory. *Intervention:* add the structure-conservation penalty and
measure training stability (loss spikes, divergence rate) vs. an unregularized
twin. Falsifier: quotient sharpness tracks full sharpness exactly (no distinct
EoS) → the regularizer has no special footing.

**(v) Rating.** **Medium speculation on the regularizer, high-novelty on the E4
measurement.** The measurement (quotient-subspace EoS) is the single highest-value
open question the edge-of-stability sweep surfaced and is genuinely unasked; the
*regularizer built on it* is a known genre. Rate the measurement grounded-novel,
the architecture medium-speculative.

---

## Ranked: what to try first (cheapest-to-test × highest-expected-signal)

The ranking weights (a) zero-or-low ML training cost (pure linear algebra /
existing simulator beats training a model), (b) a clean falsifier, (c) signal that
*gates* a whole cluster of bets.

1. **Bet 7 — Quotient-residual measurement (`rank(A − A_eq)`).** Cheapest by far:
   the probe *already computes it* (`decompose` → `rank_R`, `defect_eq`). It is
   the **go/no-go for the entire `A = A_eq + R` program** (explanatory_program §5):
   if the equitable residual is low-rank on real heads, Bets 1, 2, 7 all live; if
   it's fat (rank-collapse caveat), they all need rethinking. Run on SmolLM2-135M
   (GQA defect≈0 anchor) + a 2-layer induction/averaging model. **Highest signal
   per unit cost.**

2. **Bet 6 — Ballistic-vs-diffusive simulation.** No ML training needed: run the
   coined walk vs. CTQW in `Graphplay.Simulate` on a path/grid and confirm the
   `t`-vs-`√t` spreading exponents. This *establishes the mechanism* (ballistic
   propagation exists and is sharp) before any model is built, and it is the
   sharpest new claim against low-rank attention. Cheap, clean, high-novelty.

3. **Bet 3 — Chiral mixing-time measurement.** Also simulator-first: extend the
   probe/simulator to complex `A` and measure `mixing_time(real head)` vs.
   `mixing_time(best-phased head)` using the Levine fast-mixing signing on small
   graphs. If phasing demonstrably shortens mixing time on the *operator*, the
   "fewer layers for long-range" ML bet is worth the training cost; if not, drop
   it before training. Gates Bet 3 cheaply.

(Bets 2, 5, 8 require training a model to test their payoff, so they rank below
the three measurement-first bets. Among them, **Bet 5 (FR gate)** is the best
first *training* experiment — small parameter count, clean baseline (sigmoid
gate), robust theory.)

---

## Blunt: which of these are probably bad ideas, and why

- **Bet 4 (pure-PST routing attention) is probably impractical as stated.** PST is
  a knife-edge phenomenon requiring exact eigenvalue-ratio conditions
  (`Graphplay.PST.GodsilRatio`); a *learned* attention will never sit exactly at a
  PST host, and forcing it there is brittle. Its honest value is as the *idealized
  limit* of Bet 5 (fractional revival), which is the robust, buildable version.
  **Do not build pure-PST attention; build the FR gate and cite PST as the α→0
  endpoint.** (Still worth the cheap *measurement* — does any induction head show a
  PST signature? — but not a layer to ship.)

- **Bet 8's *regularizer* is mostly prior art repackaged; only its *measurement*
  (E4) is new.** Conservation-as-stabilizer is Kunin/Zhao territory and SAM-
  adjacent; building "conservation-regularized attention" and pitching it as novel
  invites a correct "this is known" rejection. The defensible move is narrow: run
  the **quotient-subspace edge-of-stability measurement** (genuinely unasked) and
  *only if* the quotient has a distinct EoS, propose the stabilizer. Don't lead
  with the architecture.

- **Bet 1 (MERA hierarchical attention) risks being "hierarchical transformers
  with extra steps."** Hourglass/Funnel/H-Transformer already do multi-scale
  attention; if the only delta is "we call the pooling an equitable partition,"
  reviewers will (correctly) say it's a renaming. The bet only earns its keep if
  the **exactness constraint** (`‖R‖`-per-level → 0 forces lossless pooling) and
  the **spectral lift** measurably beat learned pooling. If the residual doesn't
  drop, it's a reframing, not a discovery — and we should say so.

- **Bet 6 (coined walk) collides head-on with SSMs (Mamba/S4).** Structured-
  recurrence SSMs already deliver non-diffusive long-range propagation and are
  battle-tested. If the arc-space coined walk's only advantage is "ballistic," the
  SSM line may already capture it more cheaply (no `n²` arc space). The
  differentiator must be the **direction-carrying coin state + the quotient lift**;
  if those don't buy measurable accuracy over an SSM baseline, the `n²` arc-space
  cost makes it a bad trade. Test against an SSM, not just against vanilla
  attention.

A general caution echoing every lit verdict: **the qualitative slogans (symmetry,
coarse-graining, structured+low-rank, conservation) are all owned.** Each bet's
*only* defensible novelty is the **specific quantum-walk dynamical content that
lifts through the equitable quotient** — fast chiral mixing, ballistic coined
dispersion, unitary FR splitting, exact PST, the verified step-invariant. Pitch
those, measure those, and concede the framing.

---

## Cross-reference to `Graphplay/Integrations/NovelAttention.lean`

That file (being formalized in parallel) should host the *statements* these bets
rest on, composing existing proven results:

- **Bet 1:** `mera_exact_iff_equitable` (proven, one honest `sorry`) → a
  `hierarchicalAttention_exact_iff_tower_equitable` corollary.
- **Bet 2:** `equitableOfAutomorphism` + `restrict_eq_symmQuotient` → a
  `learnedPartition_collapse` statement parameterized by a soft `S` with a
  defect bound `‖A − S Q̃ Sᵀ‖`.
- **Bet 3:** `Graphplay.Chiral.signedBy` + fiber-equitable preservation →
  `chiralAttention_preserves_quotient` and a `chiral_mixing_faster` statement
  importing the Levine bound.
- **Bet 4/5:** `PST.IsCellUniformPST` + `FractionalRevivalNC` Tower-2 lift →
  `pstRouting_lossless` and `frAttention_split_lifts`.
- **Bet 6:** `CoinedWalk.coinedStep_unitary` + `grover_walk_commutes_with_automorphism`
  → `coinedAttention_unitary` and `coinedAttention_quotient_lift`.
- **Bet 7:** `StructuredAttention.segment_attention_exact_reduction` (proven,
  axiom-clean) + a low-rank residual apply-cost lemma → `quotientResidual_cost`.
- **Bet 8:** `training_step_linear_under_equitable` + `Graphplay.ConservationLaw`
  → `equitableStructure_conserved_under_step` (the formal hook; E4 is empirical).

The Lean side certifies *that the dynamics lift through the quotient* (the part
that is a theorem); the probe + experiments certify *that the bet helps on real
tasks* (the part that is empirical). Neither claims the other's ground.

---

*( ⌐■_■ ) the spectrum was always the spine — these bets just ask which walk gets
to ride it: diffusive and low-rank, or ballistic, phased, and revived.*
