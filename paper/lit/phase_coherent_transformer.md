# Phase-Coherent Transformer (PCT) — positioned against our chiral/phased-attention bet (Bet 3)

Scope: an adversarial-but-fair read of **Hioki, *Complex-Valued Phase-Coherent
Transformer*, arXiv:2605.10123 (2026)** (PDF:
`refs/ml-theory/phase_coherent_transformer_2605.10123.pdf`) against our
chiral-mixing theory (`Graphplay/Chiral.lean`, `Graphplay/Mixing.lean`,
`Graphplay/Dowsing/ChiralGraphon.lean`) and Bet 3 of `paper/novel_bets.md`
("Chiral / phased / directed attention, U(1) edge phases"). PCT is the first
mid-scale **empirical** paper that occupies — and on its own evidence validates
— the territory Bet 3 stakes out. This note states the precise, honest
relationship: what PCT does, where it is and is not an instance of chiral-signed
Hermitian attention, whether our chiral-*mixing* theory mechanistically explains
its central findings, and the falsifiable predictions our theory makes beyond
what PCT tested.

The voice and discipline follow `paper/lit/geometric_dl.md`: concede the framing
that is theirs, isolate the operator-theoretic content that is ours.

---

## 1. What PCT actually does

### 1.1 The architecture (the gate, precisely)

PCT is a complex-valued Transformer with native complex-linear projections
`W_q, W_k, W_v, W_o ∈ ℂ^{d×d}`. Per the §3.3.1 definition, for tokens
`x_i ∈ ℂ^d`:

- `q_i = W_q x_i`, `k_j = W_k x_j`, `v_j = W_v x_j` (complex).
- **L2-normalise the complex query/key**: `q̄_i = q_i/‖q_i‖₂`,
  `k̄_j = k_j/‖k_j‖₂` (unit complex vectors on the complex sphere).
- **Re-cosine score**: `s_{ij} = Re⟨q̄_i, k̄_j⟩ · √d ∈ [−√d, √d]`. This is the
  *real part* of the Hermitian inner product of normalised complex Q, K — the
  cosine of the angle between the two complex unit vectors.
- **Element-independent real gate**: `α_{ij} = σ(s_{ij} + b)`, a scalar sigmoid
  with a single learnable real bias `b` initialised to `−log N`. **No row
  normalisation.**
- `out_i = W_o · Σ_j α_{ij} v_j` — a *real* weight `α` multiplying a *complex*
  value, so the value path's phase is carried straight through.

The defining structural move (§2.4–2.5): PCT replaces softmax's **row-normalised
token competition** with a **token-non-competing** real gate on complex cosine
similarity. Softmax couples all tokens in a row through the shared denominator
`Σ_j exp(s_{ij})`; PCT's gate `α_{ij}` depends only on the pair `(i,j)`.

### 1.2 Why "complex / phase-preserving"

Two properties the paper isolates (§5.1) as load-bearing, together called
**two-level phase coherence**:

- **(L1) Per-layer phase coherence / token non-competition.** The gate is
  element-independent (no `Σ_j` coupling), so the complex value contributions
  `α_{ij} v_j` superpose **without competition**. Phase superposition of the
  value path is preserved within a layer. Formalised (Def. 1, Thm. 1: C1 real
  gate ∧ C4 element-independent ⇒ L1; machine-checked in their Lean companion):
  the layer commutes with a *global* phase shift `R(φ): x ↦ e^{iφ}x` and has no
  cross-token coupling. Softmax violates L1 (the denominator couples tokens).

- **(L2) All-layer cascade phase stability.** The gate is **smooth and
  gradient-nonzero on the full operating range** `[−√d, √d]`, *including the
  negative-cosine region*. Because the gate does not delete contributions whose
  cosine score is negative (the "negatively-aligned phase components"), a stack
  of `L` such layers does not amplify per-token phase noise: accumulated phase
  noise stays `O(1)` in depth rather than `O(L)`. Formalised (Def. 2–3, Thm. 2 /
  their Thm. 5: L1 ∧ C2 bounded-on-range ∧ C3 smooth-nonzero-on-range ∧
  non-expansive substrate ⇒ L2). The proof is a Doeblin-contraction /
  geometric-cascade-summation argument on the **zero-mean phase subspace** with
  an `L`-independent Lipschitz constant — i.e. an explicit **mixing/contraction**
  argument (§M.3, Lemmas A–D). *This is the part that touches our framework most
  directly — see §3.*

### 1.3 "Non-competing" vs softmax

Softmax is a *competition*: attention mass is conserved per row (`Σ_j α_{ij}=1`)
and tokens compete for it; adding a key dilutes all others. PCT's sigmoid gate is
*independent per pair*: each `(i,j)` is admitted or not on its own cosine score,
with no mass budget. The paper's Prediction-2 ("complex penalty of vanilla
complex") and R4 show that **softmax-of-complex** (`complex_softmax`, the Eilers–
Jiang ℂAtt default) is a *poor* default precisely because row-normalised
competition is incompatible with the phase superposition of the complex value
path — it is the worst cell on the physical RadioML domain (R4: PCT clears it by
+0.10 at L1).

### 1.4 Concrete empirical findings

A 6-cell, 9-task, parameter-fair (`real_dim = complex_dim × 1.41`) comparison:

- **R2 — NIAH dominance.** On Needle-in-a-Haystack L=2048 (purely positional
  retrieval, *designed to deny* complex Q,K any inductive advantage), PCT and
  `complex_screen` solve it *deterministically* (1.000), matching the strongest
  real baseline `real_screen`. The four cells without a screening/sigmoid-on-
  cosine structure all collapse to 0.000.
- **R3 — LR/batch robustness.** PCT is the **unique** cell that holds 1.00 across
  the entire LR window (1e-3/3e-3/1e-2) *and* the entire batch regime
  (8/32/256) on long-range Copy — an all-1.00 row no other cell achieves.
- **R5 — beats vanilla real `real_softmax`** on every task; gap largest on
  long-range Copy and NIAH (the long-range/retrieval regime).
- **Phase-component ablations (§5.3–5.4, the headline mechanistic result).**
  Deliberately condition-violating gates isolate *which* structural property is
  load-bearing:
  - **Smooth gates that preserve negatively-aligned phase components remain
    strong** (`complex_sigmoid` = PCT: 1.000 on Copy d=1000; `complex_softplus`:
    practically equivalent, 1.000).
  - **Gates that *delete* negatively-aligned components collapse on long-range
    retrieval**: `complex_relu` (anti-phase deletion, gradient zero on the
    negative half) → **0.107 on Copy d=1000 (chance)**; `complex_clamped_relu`
    → 0.103 (chance). This collapse is **distance-independent** — bit-identical
    0.103 at d ∈ {100,200,500,1000}; the task becomes "structurally invisible"
    regardless of inter-token distance.
  - **Gates whose outputs grow excessively large** suffer clear degradation
    (`complex_cubic`, C2-violating, M≈252): 0.200 — partial, not full, collapse.
  The C2×C3 isolation matrix (§5.4) reads: **C3 (anti-phase deletion) is the
  dominant failure axis; C2 (unbounded gate) is a secondary, magnitude-dependent,
  partial-degradation axis.** The framework is stated `L1 ∧ C2 ∧ C3 ⇒ L2`.
- **Depth stability (§5.5).** Across depths 2,4,6,10,14,20 (10× range), PCT shows
  **no depth-related accuracy collapse**: best-acc flat (slope ≈ −0.009, R²=0.04),
  every depth trains. The paper frames this *conservatively* — "PCT does not
  exhibit a depth-collapse failure mode at any tested depth" — explicitly **not**
  a quantitative scaling law. The structural reason offered is exactly L2: the
  cascade Lipschitz constant is `L`-independent, so phase noise does not compound
  with depth.
- **One honest counterexample (§5.7).** On physical-complex **Real RadioML**,
  `real_screen` edges PCT by 0.02/0.04 (L1/L2). The paper flags this as the one
  phase-sensitive task it does *not* yet explain.

---

## 2. Precise relationship to our chiral / phased attention

### 2.1 The shared substrate: complex Hermitian attention graph

Our `Graphplay/Integrations/MachineLearning.lean` models attention as a weighted
graph by symmetrising scores into a **Hermitian, loopless** operator
(`AttentionMatrix.symmetrizedAttention`, `symmScore_isHermitian`). Bet 3
(`paper/novel_bets.md`) upgrades the host from a real-symmetric kernel to a
**chiral signing** `σ(i,j) = e^{iθ_{ij}}` with the Hermitian condition
`σ(j,i) = σ(i,j)*` (`ChiralSigning.herm`), giving the *magnetic* adjacency
`σ_{ij}·A_{ij}` — a U(1) gauge field on the edges of the token graph.

PCT and Bet 3 **share the same generative observation**: a complex-valued
attention substrate carries phase as a first-class degree of freedom that the
value path must preserve across layers, and softmax/real-symmetric attention is
*time-reversal-symmetric / phase-destroying* in a way that wastes that degree of
freedom. PCT (§2.2–2.5) and Bet 3 (mechanism (ii)) make essentially the same
diagnosis of the softmax default from opposite directions (empirics vs.
mixing-time theory).

### 2.2 Is PCT an instance of chiral-signed Hermitian attention?

**Partly — it is the phase-*preserving* sibling, not literally a U(1)
edge-signing.** The honest mapping:

| Aspect | Our chiral attention (Bet 3) | PCT |
|---|---|---|
| Phase lives on… | **edges**: `σ(i,j)=e^{iθ_{ij}}` multiplying `A_{ij}` (a U(1) gauge field / magnetic potential) | **value vectors**: complex `v_j`, carried by a *real* gate `α_{ij}` |
| Hermitian structure | explicit `σ(j,i)=σ(i,j)*`, `σ(i,i)=1` | implicit: cosine score `s_{ij}=Re⟨q̄_i,k̄_j⟩` is **symmetric** (`s_{ij}=s_{ji}`), gate real ⇒ the *gate matrix* `α` is real-symmetric; phase is in `v` |
| What breaks time-reversal | the U(1) phases on the host (non-real Hermitian adjacency) | nothing in the *gate*; PCT's gate matrix is real-symmetric. Phase non-triviality is in the complex value channel and the **complex Q,K cosine** |
| Key preserved object | the fiber-equitable partition (cell row-sums of `|adj|`) — `signedBy_preserves_equitable` | **global phase covariance** `R(φ): x↦e^{iφ}x` (Def. 1a) + per-token phase invariant across depth (L2) |

So PCT is **not** literally our magnetic adjacency `σ_{ij}A_{ij}`: its *gate* is
real and symmetric, not a U(1) edge-signing. Where they coincide structurally is
deeper than the gate: **PCT's "preserve negatively-aligned phase components" is
the requirement that the layer not destroy destructive (anti-aligned) phase
interference in the complex value superposition** — and *that* is exactly the
phenomenon our chiral signing engineers on the host. A chiral signing places
`±i` (and general `e^{iθ}`) phases on edges precisely so that contributions
arrive at a vertex with *non-trivial relative phase*, including destructive
(negatively-aligned) interference — see the explicit `unitaryHammingChiralK4`
signing in `Graphplay/Chiral.lean` (entries `±i`: maximal anti-alignment,
`Re(±i)=0`, pure imaginary cross terms). The Levine et al. fast-mixing trick
*works because* of this destructive interference between phased paths.

The cleanest statement of the correspondence:

> **PCT enforces, at the gate level, the same "do not delete the destructively-
> interfering phase components" property that our chiral signing supplies at the
> host level.** PCT preserves anti-phase components passively (smooth gate on the
> negative-cosine region); chiral signing *creates and exploits* them actively
> (U(1) phases that make paths interfere destructively to mix faster).

### 2.3 Where it matches our `CrossConstant` / quotient structure

There is a second, sharper structural contact. Our chiral theorems require the
signing to be **cross-constant** on cells — `σ(x,y) = τ(cell x, cell y)`
(`ChiralSigning.CrossConstant`) — so the phase depends only on the *cell pair*,
which is exactly what makes signing **preserve the equitable partition**
(`signedBy_preserves_equitable`) and reduce to a **chiral phasing of the
quotient** (`chiral_mixing_optimization`, `ChiralGraphon`'s flat-U(1)-connection
reading). PCT's gate is, by construction, a **function of the pair `(i,j)` only**
through `s_{ij}` — token-non-competition is *precisely* the "depends only on the
pair, no coupling through other tokens" condition (their Def. 1b). This is the
same algebraic property — *pairwise-determined, no third-token coupling* — that
our cross-constant condition imposes (one level coarser: cell-pair vs.
token-pair). PCT's L1 is the **un-quotiented limit** of our cross-constant
equitable-preservation lemma: both say "the attention weight on `(i,j)` factors
through `(i,j)` alone, so the structure that lifts through the quotient is not
destroyed."

**Net verdict on instance-hood.** PCT is **a genuine member of the
phase-coherent attention family Bet 3 names, and an independent empirical
instance of its core thesis** ("phase-preserving complex attention beats
phase-destroying softmax on long-range"), but it is **not** an instance of the
*specific* construction Bet 3 proposes (a learned U(1) edge-signing optimised for
mixing time). It validates the *family-level* bet while leaving the *specific*
chiral-signing mechanism — and the mixing-time theory behind it — unoccupied.

---

## 3. Does our chiral-MIXING theory EXPLAIN their findings?

**Verdict: PARTLY — and the part it explains, it explains sharply; the part it
does not, it must not overclaim.**

### 3.1 What the theory explains (the mechanism is the right shape)

Our chiral-mixing claim (Bet 3 mechanism (ii); `Graphplay/Mixing.lean`,
`Graphplay/Chiral.lean`): real-symmetric attention is time-reversal-symmetric, so
walk mixing/transfer is bounded by the unsigned spectral gap; **U(1) phases break
time-reversal symmetry and can strictly accelerate uniform mixing** (Levine
et al. 2605.04414: a `K_4` signing mixes at `π/(3√3)`, faster than any unoriented
Hamming graph). The *mechanism* of the speedup is **destructive interference
between phased paths** — the negatively-aligned (anti-phase) components are
exactly the ones that cancel the slow modes and accelerate spreading to uniform.

This lines up, mechanistically, with PCT's central ablation in a way that is more
than coincidence:

- **"Preserve negatively-aligned phase components → long-range works; delete them
  → collapse."** In our language: deleting anti-phase components removes the
  destructive-interference channel; without it the walk reverts to the
  time-reversal-symmetric, gap-limited (slow) mixing regime, and long-range
  propagation degrades. The **distance-independence** of the collapse (§5.4
  observation 1: bit-identical chance-level at every distance) is the *exact
  signature a mixing-time argument predicts*: the failure is not "signal decays
  with distance" (a diffusive/leakage story) but "the fast-mixing channel is
  structurally absent," so *no* distance is reachable. A diffusive low-rank
  attention would show graded decay with distance; PCT's anti-phase-deleted cells
  show a *structural* on/off — which is what a mixing-channel-present/absent
  account predicts, not a decay account.
- **Depth stability.** Bet 3 predicts "phased attention reaches long-range mixing
  in fewer layers because the host's mixing time is shorter." PCT's depth result
  is the dual: the phase-coherent cascade does not *accumulate* phase noise with
  depth (`O(1)` not `O(L)`). Both are statements that the **phase structure
  controls the depth-scaling of propagation**; PCT even proves L2 by a **Doeblin
  contraction on the zero-mean phase subspace** (§M.3 Lemma C) — i.e. a literal
  *mixing/contraction-rate* argument on a phase subspace, the same mathematical
  genus (Doeblin/spectral-gap contraction) as our quotient mixing analysis in
  `Graphplay/Mixing.lean` (`chiralMixingQuotient`, the cell-block amplitude
  contraction to the uniform target). The convergence of the *proof technique* —
  Doeblin contraction on a phase subspace — is the strongest single piece of
  evidence that the two stories share a mechanism.

So the chiral-mixing framework supplies a **mechanistically coherent, signature-
matching explanation** of *why* preserving anti-phase components is what enables
long-range and depth-stable propagation: those components are the
destructive-interference channel that fast mixing rides on.

### 3.2 The precise explanatory claim (stated carefully)

> **Claim (explanatory).** PCT's "preserve negatively-aligned phase components →
> long-range / depth-stable; delete them → distance-independent collapse" is the
> machine-learning shadow of the chiral fast-mixing phenomenon: the anti-phase
> (destructively-interfering) components are the channel by which a phase-coherent
> walk accelerates and stabilises propagation, and removing them returns the
> system to the gap-limited, time-reversal-symmetric regime. The *distance-
> independence* of the collapse and the *L-independence* of the depth cascade are
> the two qualitative signatures a mixing-time/contraction account predicts and a
> diffusive-decay account does not.

### 3.3 Caveats — where it is an analogy, not a derivation (be blunt)

The honesty discipline of `paper/novel_bets.md` (Bet 3 rating: "the leap from
CTQW mixing-time to transformer layer count is an analogy that must be earned
empirically") applies in full:

1. **PCT's gate is real-symmetric; its phase is in the value channel, not a U(1)
   edge-signing.** Our mixing theorems (`chiral_mixing_optimization`,
   `chiralMixingQuotient`) are theorems about `exp(-itσ_{ij}A_{ij})` — the
   *evolution generated by a chiral Hermitian host*. PCT is *not* running that
   evolution. So our theorems do not *literally* apply to PCT; the explanation is
   a mechanism-level analogy ("destructive interference is the fast channel"),
   not a theorem instance. Calling it a derivation would be false.
2. **Layers ≠ continuous time.** The mixing-time speedup is a CTQW statement
   (`exp(-itA)`); PCT's depth result is about discrete layers and *noise
   accumulation*, not about reaching ε-uniform faster. We connect them by the
   shared "phase controls propagation depth-scaling" slogan, but the two
   quantities (mixing time vs. cascade Lipschitz constant) are not identified.
3. **PCT's own proof is self-contained.** PCT proves L2 from its four gate
   conditions via Doeblin contraction; it does **not** invoke fast mixing,
   chirality, or a U(1) signing. Our framework offers an *additional,
   convergent* mechanistic reading of the *same* phenomenon — explanatory
   value-add, not a replacement for their proof.
4. **Our two central mixing theorems carry honest `sorry`s.**
   `cellBlockAmp_eq_quotient` (the host↔quotient chiral-transfer identity) and
   `chiral_mixing_optimization` are stated, not fully proven
   (`Graphplay/Mixing.lean:201`, `Graphplay/Chiral.lean:256`). The *theory* we
   claim explains PCT is therefore itself partly conjectural at the Lean level —
   we should not present it as more settled than it is.

**Bottom line for §3:** *partly* — the chiral-mixing mechanism explains the
**shape and signatures** of PCT's anti-phase/long-range/depth findings
(destructive-interference channel, distance-independent on/off, L-independent
cascade, shared Doeblin-contraction proof genus), but it does **not** derive PCT,
because PCT runs a real-gated complex-value layer, not our U(1)-signed CTQW.

---

## 4. What we'd PREDICT beyond PCT (falsifiable follow-ups)

These are concrete claims our chiral-*mixing* theory makes that PCT did **not**
test — the falsifiable wedge that is genuinely ours.

1. **The optimal phase pattern is a cross-constant chiral signing, not a generic
   learned `θ`.** Bet 3 + `ChiralSigning.CrossConstant` /
   `signedBy_preserves_equitable` predict that the *best* phase structure for
   long-range propagation is one that depends only on the **cell pair**
   (positional/relative-position cells), because only then does it preserve the
   equitable quotient and reduce to a phasing of the small quotient
   (`chiral_mixing_optimization`). **Test:** give PCT (or a magnetic-attention
   variant) an explicit *edge* phase `σ(i,j)=e^{iθ(i−j)}` (relative-position
   cross-constant) and predict it beats both a free per-pair `θ_{ij}` and `θ=0` on
   long-range Copy/ListOps. *Falsifier:* a free unstructured phase ties or beats
   the cross-constant one, or `θ` collapses to 0 in training.

2. **A specific mixing-time scaling: layers-to-long-range should drop like the
   chiral mixing-time ratio.** The Levine `K_4` bound is `π/(3√3)` vs. the
   unsigned Hamming mixing time — a *concrete constant-factor speedup*. **Test:**
   on a controlled propagation task (long-range copy at distance `Δ`), measure
   *layers-to-solve* for a magnetic/chiral host vs. its real twin; predict the
   chiral host needs fewer layers by a factor tracking the *operator-level*
   mixing-time ratio measured by a `mixing_time(A)` diagnostic (Bet 3 test plan;
   our `Graphplay/Mixing.lean` `IsUniformMixing` is the operator-side quantity).
   This is a *quantitative* prediction PCT's qualitative depth result neither
   makes nor tests. *Falsifier:* no layer-count advantage, or the advantage does
   not track the operator mixing-time ratio.

3. **Which phase ablations should help vs. hurt — a sharper map than PCT's.** PCT
   shows "preserve anti-phase = good, delete = collapse." Our theory predicts
   *finer* structure: deleting anti-phase components should hurt **in proportion
   to how much they contribute to the destructive-interference (slow-mode-
   cancelling) channel**, which is *task-geometry-dependent* (the cell structure
   of the task). **Prediction:** on a task whose natural equitable partition has
   *no* off-cell anti-phase mass, anti-phase deletion should be *harmless* (the
   chiral channel is empty); on a task with rich cross-cell structure
   (path-finding, long-range copy), deletion should be *catastrophic* — which is
   exactly the distance-independent collapse PCT sees on Copy. **This predicts a
   task on which `complex_relu` does *not* collapse**, namely one with no
   long-range cross-cell transfer requirement (short-range/local tasks). PCT's
   data is consistent (short-range Copy d=200 not reported as collapsing for the
   smooth cells), but PCT never frames or tests the *task-geometry* dependence.

4. **A spectral/mixing explanation of depth stability that yields a
   *quantitative* L-independence constant.** PCT's L2 Lipschitz constant is
   `L`-independent but the *value* is left as an operating-range bound. Our
   quotient picture predicts the cascade contraction rate is governed by the
   **chiral quotient's spectral gap** (the `symmQuotient` of the signed graph,
   `chiral_mixing_optimization`). **Prediction:** the depth-stability margin
   should be computable from the *quotient* spectral gap of the phased host, and
   should *improve* (flatter depth curve) as the chiral phasing increases that
   gap toward the Levine optimum. Testable on the operator first (no training):
   compute quotient gap vs. measured cascade contraction.

5. **The Real RadioML anomaly (§5.7) is a prediction target.** PCT flags Real
   RadioML as the one phase-sensitive task it cannot explain (`real_screen` beats
   PCT). Our framework predicts the discriminator is whether the task's natural
   host has a **chiral (genuinely complex, time-reversal-broken) optimal signing**
   vs. a real one: physical I/Q modulation data may have an *intrinsic* phase
   geometry whose optimal attention host is *not* the phase-preserving-but-
   real-gated PCT but a *specifically signed* one. **Prediction:** a chiral/
   magnetic-attention variant (learned edge phase) should *recover or beat*
   `real_screen` on Real RadioML where PCT falls short — turning PCT's open
   anomaly into a positive test of the edge-signing mechanism. This is the single
   most attractive empirical follow-up because it attacks PCT's *own* unexplained
   gap with our distinguishing mechanism.

**Strongest single prediction (the one to lead with):** *#1 — the optimal phase
pattern is a relative-position **cross-constant U(1) edge-signing**, which
(a) preserves the equitable quotient and (b) beats both free per-pair phases and
real-gated PCT on long-range propagation.* It is the cleanest falsifiable claim
that is *ours and not PCT's*: PCT preserves phase passively in the value channel;
we predict the *active edge-phase* that PCT never introduces, with a structural
(quotient-preservation) reason for *which* phase pattern is optimal.

---

## 5. Honest citation verdict

### 5.1 Status of Bet 3

**Bet 3 is now "validated + partly occupied."**

- **Validated (independently, empirically):** PCT supplies strong mid-scale
  empirical evidence for the *family-level* thesis Bet 3 rests on — **phase-
  preserving complex attention beats phase-destroying softmax on long-range and
  is depth-stable, and the destructively-interfering (negatively-aligned) phase
  components are the load-bearing ingredient.** This is exactly the qualitative
  prediction Bet 3's mechanism (ii) makes, arrived at independently and from the
  empirical side. Bet 3's rating ("most likely to clearly work or clearly not —
  high upside if it does") resolves toward *works*: PCT is the "clearly works"
  outcome for the phase-coherence half of the bet.
- **Partly occupied:** PCT occupies the *empirical demonstration* and a
  *self-contained gate-condition theory* (the C1–C4 / two-level coherence
  framework, with its own Lean-checked Thm. 1/Thm. 5). It does **not** occupy
  (a) the **U(1) edge-signing / magnetic-adjacency construction**, (b) the
  **mixing-time theory** of *why* phase coherence helps (Levine fast-mixing /
  chiral-quotient), (c) the **equitable-quotient lift** that makes phasing
  compose with cell-collapse, or (d) the **cross-constant optimality** of the
  phase pattern. Those four remain ours and unoccupied.

### 5.2 How to cite PCT

Cite PCT as **independent empirical corroboration of the phase-coherence
half of Bet 3**, in the GDL-note voice (concede the framing that overlaps, claim
the operator-theoretic content that does not):

> *"Hioki's Phase-Coherent Transformer (2605.10123) provides independent,
> mid-scale empirical confirmation that phase-preserving complex attention
> generalises on long-range and depth-stability tasks where phase-destroying
> softmax fails, and isolates — via deliberate ablations — that the
> **negatively-aligned (destructively-interfering) phase components are
> load-bearing**: smooth gates that preserve them succeed on long-range
> retrieval, gates that delete them collapse to chance in a distance-independent
> way, and the cascade is depth-stable. We read this as the machine-learning
> signature of the chiral fast-mixing mechanism our framework formalises:
> destructive phase interference is the channel that accelerates and stabilises
> propagation. PCT preserves this channel **passively** (a real, smooth,
> token-non-competing gate on complex value vectors) and proves depth-stability
> by a Doeblin contraction on a phase subspace — the same contraction genus as
> our quotient-mixing analysis. Our contribution is the complementary
> **operator-theoretic and mixing-time theory**: the U(1)-signed host whose
> chiral phases **actively create** the destructive-interference channel
> (Levine et al., 2605.04414), the spectral/mixing-time account of **why** this
> generalises and is depth-stable, the **equitable-quotient lift** that makes
> phasing compose with cell-collapse, and the prediction that the **optimal phase
> pattern is a cross-constant edge-signing** — none of which PCT constructs or
> tests."*

### 5.3 Sharpened statement of what is ours

Mirroring the GDL verdict's structure — *they own the framing, we own the
spectral/dynamical theorem*:

- **Theirs (concede):** the empirical demonstration; "token non-competition +
  multi-layer phase preservation"; the gate-condition (C1–C4) framework and its
  self-contained Lean Thm. 1/5; the observation that softmax-of-complex is a poor
  default.
- **Ours (defend):**
  1. **The spectral / mixing-time THEORY of why phase-coherent attention
     generalises** — phase coherence ↔ time-reversal-breaking ↔ faster uniform
     mixing (Levine `π/(3√3)`), with the destructive-interference channel as the
     mechanism. PCT *shows that* it generalises; we *say why* in mixing-time
     terms.
  2. **The U(1) edge-signing construction** (`ChiralSigning`, `signedBy`,
     `unitaryHammingChiralK4`) — phase on the host, not just passively in the
     value path.
  3. **The equitable-quotient lift** (`signedBy_preserves_equitable`,
     `chiral_mixing_optimization`, `ChiralGraphon`'s flat-U(1)-connection
     reading) — phasing composes with the `O(n·r)` cell-collapse; PCT has no
     quotient story.
  4. **The cross-constant optimality prediction** — *which* phase pattern is
     optimal, and why (quotient preservation).
  5. **Machine-checked dynamical lift** (modulo honest `sorry`s) of the
     phase-coherence-→-propagation story through the equitable quotient.

**Blunt bottom line.** PCT is the empirical "it works" for the phase-coherence
half of Bet 3 — cite it as independent corroboration and let it retire the
"medium-high speculation" rating on *whether* phase-coherent attention helps. It
does **not** retire the part that is ours: the **mixing-time / chiral-signing /
equitable-quotient theory of *why* it helps and *which* phase pattern is
optimal.** If a referee says "PCT already did this," the honest rebuttal is the
GDL rebuttal in new clothes: *PCT gives you the empirical phase-coherence
phenomenon and a gate-condition proof of depth-stability; we give you the
operator-theoretic mixing-time mechanism, a constructive U(1) edge-signing, a
quotient lift, and a falsifiable prediction (cross-constant optimal phase) that
PCT neither builds nor tests.*

---

*( ⌐■_■ ) they preserved the phase; we explain why preserving it makes the walk
mix — and which phases make it mix fastest.*
