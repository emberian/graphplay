# PCT × Graphplay: the complex-Hermitian extension and a phase-coherent chiral attention design

Scope: a *design + theory* study (not a literature note) of how Graphplay's
chiral / complex-Hermitian framework can extend toward — and plausibly improve
on — the **Phase-Coherent Transformer** (PCT; Hioki, arXiv:2605.10123,
`refs/ml-theory/phase_coherent_transformer_2605.10123.pdf`). It complements the
first-pass adversarial read in `paper/lit/phase_coherent_transformer.md`; where
that note positions PCT against Bet 3, this note goes *into the machine*: the
exact gate, the C1–C4 conditions, the Appendix-M Doeblin proof, and then states
the **complex-Hermitian generalisation our results need**, a **concrete chiral
phase-coherent attention design** that is our analogue of PCT, and the
**falsifiable simulator experiment** that separates them.

The single load-bearing discovery of the deeper read: **PCT throws away exactly
the object our framework is built on.** PCT's gate keeps `Re⟨q̄,k̄⟩` (the real,
*symmetric* part of the Hermitian Q,K inner product) and discards
`Im⟨q̄,k̄⟩` (the *antisymmetric* part) from the gate — yet the antisymmetric
part reappears, uncontrolled, as `η_{ij} = −Im⟨q̄_i,k̄_j⟩` inside PCT's own
Appendix-M Doeblin Jacobian (Lemma B). That `η` *is* an (infinitesimal) U(1)
edge-signing — a chiral phase on the token graph. PCT carries it passively and
never optimises it; our framework is the theory of putting it *actively on the
edges and choosing it optimally*.

---

## 1. PCT's complex mechanism, precisely

### 1.1 The gate (§3.3.1, exact)

For tokens `x_i ∈ ℂ^d`, complex-linear `W_q,W_k,W_v,W_o ∈ ℂ^{d×d}`, learnable
**real** bias `b`:

```
q_i = W_q x_i,  k_j = W_k x_j,  v_j = W_v x_j           (complex)
q̄_i = q_i/‖q_i‖₂,  k̄_j = k_j/‖k_j‖₂                    (complex unit vectors)
s_{ij} = Re⟨q̄_i, k̄_j⟩ · √d  ∈ [−√d, √d]               (REAL cosine score)
α_{ij} = σ(s_{ij} + b),   b init = −log N               (REAL scalar gate, no row-norm)
out_i  = W_o · Σ_j α_{ij} v_j                           (REAL weight × COMPLEX value)
```

RoPE is applied to Q,K of every layer (A2.1) — so PCT *already has relative
position phase*, but only inside `q̄,k̄`, passed through to `s` via the real
part. Pre-norm RMSNorm; ModReLU FFN; ReLU² real-side FFN.

The phase lives in **two** places and is *spent* in neither: (i) the complex
value vectors `v_j`, carried by a real `α` straight through `W_o` ("real-weight ×
complex-value"); (ii) the discarded imaginary part `Im⟨q̄,k̄⟩` of the score. The
gate itself is **real and symmetric** (`s_{ij}=s_{ji}`).

### 1.2 What makes it "phase-coherent" — two levels

- **L1 (per-layer / token non-competition).** Def. 1: the layer commutes with a
  *global* phase shift `R(φ): x↦e^{iφ}x`, and each `α_{ij}` depends only on the
  pair `(i,j)` — no coupling through other tokens (no softmax denominator
  `Σ_k exp s_{ik}`). **Theorem 1: C1 ∧ C4 ⇒ L1**, proven by complex-linear
  conjugate cancellation (the cosine is rotation-invariant; the value sum is
  complex-linear so the global `e^{iφ}` factors out). Machine-checked in their
  Lean, no `sorry`. Softmax violates L1 (the denominator couples tokens).

- **L2 (all-layer cascade phase stability).** Def. 2–3: stacking `L` layers does
  not amplify *per-token* phase noise — the cascade Lipschitz constant on the
  zero-mean phase subspace is **`L`-independent**, so accumulated phase noise is
  `O(1)` not `O(L)`. **Theorem 2: L1 ∧ C2 ∧ C3 ∧ (non-expansive substrate) ⇒ L2.**

### 1.3 The C1–C4 conditions (§5.2), in operating-range form

- **C1** — gate output is real, `α∈ℝ`.
- **C2** — gate is *bounded on the operating range*, `|f|≤M` for `s∈[−√d,√d]`.
- **C3** — gate is *smooth, gradient-nonzero on the operating range* (in
  particular on the **negative-cosine / anti-phase** region).
- **C4** — gate is element-independent (the pairwise / no-third-token property).

"Operating-range vs strict-on-ℝ" is load-bearing: L2-normalisation confines `s`
to `[−√d,√d]`, so a gate that is unbounded on ℝ (softplus) but bounded on the
range still passes C2. This is why the framework is `L1 ∧ C2 ∧ C3 ⇒ L2` and not
a strict-on-ℝ condition.

### 1.4 The Appendix-M proof — and the chiral object hiding in it

Theorem 2's proof (M.3) is the part that touches us. The per-token perturbation
`ε∈ℝ^N` splits into a **global mode** `φ̄·1` (passes exactly through L1, Lemma A)
and a **zero-mean residual** `δ⊥1`. On `δ`, a single layer acts to first order
by a Jacobian `J_l` built from:

- the **row-stochasticised gate** `P_{ij} = α_{ij}/Σ_k α_{ik}` (Lemma B), and
- **`η_{ij} = −Im⟨q̄_i, k̄_j⟩`** — the imaginary part of the Hermitian Q,K inner
  product (Lemma B).

Then a **Doeblin contraction** (Lemma C, via Levin–Peres–Wilmer Thm 4.9): under
"attention diffuseness" (`α_{ij} ≥ µ·π_j`, a positive distribution, holding at
init by the `b=−log N` bias), `P_l` satisfies a Doeblin condition with constant
`µ_D>0`, so `‖J_l|_{δ⊥1}‖ ≤ 1−µ_D < 1`. The depth-`L` Lipschitz is then a
**geometric series** `Σ_l (1−µ_D)^l ≤ 1/µ_D`, `L`-independent. C3 enters because
the linearisation needs gate differentiability *through* the negative region;
C2 enters because an unbounded gate blows up the geometric series' constant.
**Lean-checked as `theorem5` under an explicit premise bundle `Theorem5Premises`**
(Lemmas B, D and the Doeblin/Mathlib step are *assumed* in the bundle, not
proven from scratch; `#print axioms` is clean).

**The discovery.** `η_{ij} = −Im⟨q̄_i,k̄_j⟩` is *antisymmetric* (`η_{ij}=−η_{ji}`,
since `⟨q̄_j,k̄_i⟩ = conj⟨k̄_i,q̄_j⟩`); it is precisely the off-diagonal phase a
Hermitian operator carries. It is an **infinitesimal U(1) edge-signing on the
token graph** — `σ(i,j) ≈ e^{iη_{ij}}`. PCT *has* this chiral object, lets it
ride passively in the Jacobian, and **never optimises it**. Our framework is the
theory of `η`: put it actively on the edges, make it cross-constant, choose it
for fastest mixing.

### 1.5 What the ablations prove (§5.3–5.4) — which phase components are load-bearing

The 2×2 (C2 × C3) isolation on Copy d=1000 (N=3):

| | C2 ✓ | C2 ✗ (M≈252) |
|---|---|---|
| **C3 ✓** | sigmoid 1.000 · softplus 1.000 | cubic **0.200** |
| **C3 ✗** | clamped_relu **0.103** | relu **0.107** |

- **C3 is the dominant failure axis.** Gates that *delete the
  negatively-aligned (anti-phase, negative-cosine) components* — relu,
  clamped_relu — collapse to **chance** (0.103/0.107) on long-range retrieval.
  Gates that *preserve* them (sigmoid, softplus) succeed (1.000).
- **The C3 collapse is distance-independent.** clamped_relu returns
  **bit-identical 0.103 at d ∈ {100,200,500,1000}** — it "never starts learning";
  the task is "structurally invisible" regardless of inter-token distance. On
  structured-multilabel (multi-pitch) the same cell sits exactly at the trivial
  baseline 0.812 with std 0 across seeds.
- **C2 is a secondary, magnitude-dependent axis.** cubic (C3 ✓, M≈252) drops to
  0.200 — partial, not full, collapse; "somewhere between M=4 and M=252 lies a
  transition." Distance-independent too (bit-identical 0.200 across d).
- **complex_softmax fails by a *separate* mechanism** (violates L1/C4, not C3):
  long-range dilution from token competition; worst cell on physical RadioML L1.

**Plain statement of the headline ablation:** *the negatively-aligned phase
components — the ones that interfere destructively in the complex value
superposition — are load-bearing for long-range and depth-stable propagation.*
Delete them → distance-independent on/off collapse; keep them → it works.

### 1.6 The empirical results that matter for us

- **NIAH L=2048 (positional retrieval, designed to deny complex Q,K any
  advantage):** PCT, complex_screen, real_screen all solve it 1.000; the four
  cells lacking a sigmoid/screen-on-cosine structure collapse to 0.000.
- **Long-range Copy d=2000:** only PCT/complex_screen/real_screen ≥ 0.53; vanilla
  real/complex softmax at chance (~0.10/0.08).
- **R3 LR/batch robustness:** PCT is the *unique* all-1.00 row across LR ∈
  {1e-3,3e-3,1e-2} and batch ∈ {8,32,256}.
- **Depth 2–20 (10×):** *no depth-related accuracy collapse*; slope −0.009,
  R²=0.04 — explicitly framed as **qualitative, not a scaling law**. The
  structural reason offered is exactly L2's `L`-independent Lipschitz constant.
- **The one honest counterexample (§5.7):** on physical **Real RadioML**,
  `real_screen` beats PCT by 0.02/0.04 (L1/L2). PCT flags this as the one
  phase-sensitive task it does *not* explain — the most important pending
  validation by their own admission.

---

## 2. Why the COMPLEX case is vital for us — and exactly which results need it

Graphplay's chiral mixing speedup *is already* complex-Hermitian; the obstruction
is that the rest of our attention apparatus is **real-only**, so it cannot
formally touch a PCT-style (phased / RoPE) attention host. Three precise gaps.

### 2.1 The host is real; the chiral lift is the only complex thing — and PCT's host is *natively* phased

`MachineLearning.AttentionMatrix.score : Matrix n n ℝ` (real), symmetrised to
`symmScore : Matrix n n ℂ` whose entries are **real numbers cast to ℂ**
(`symmScore_isHermitian`, `symmScore_diag` — real-symmetric, zero diagonal). The
*only* place a genuine phase enters our pipeline is
`chiralAttention A s = (symmetrizedAttention A).signedBy s`
(`NovelAttention.lean §1`): the chiral signing `s.σ(i,j)=e^{iθ_{ij}}` multiplies
the real host. This is good — but PCT's host is **already complex-Hermitian
before any signing**: `Re⟨q̄,k̄⟩ + i·Im⟨q̄,k̄⟩` with RoPE phase baked into `q̄,k̄`.
So to talk about PCT-style attention at all, our host must be allowed to be a
**genuine complex-Hermitian kernel `H = Re-part + i·Im-part`** (a magnetic
adjacency), not "real host + bolt-on signing." `chiralAttention` already produces
such an `H`; what is missing is the rest of the toolkit operating on it.

### 2.2 Eckart–Young / corrected-attention is real-only — the central blocking gap

`EquitableMechanism.lean`: `equitablePart`, `residual`, `residual_add_equitable`,
`correctedApplyCost`, and the **Eckart–Young residual-truncation optimality**
(`corrected_equitable_attention`, `diag_eckartYoung_optimal`) are **all stated on
`Matrix (Fin n) (Fin n) ℝ`** — real-valued. The `A = A_eq + R` decomposition and
the proven "`A_eq` + rank-`k` residual is `O(n(r+k))` and Frobenius-optimal" hold
**only for a real host.** A phased / RoPE attention host is complex-Hermitian, so
**none of the corrected-attention results currently apply to PCT-style
attention.** This is the single most important complex generalisation we need
(see §2.5). Concretely we need:

- `equitablePart`, `residual` over `Matrix (Fin n) (Fin n) ℂ` with the block `B`
  Hermitian;
- `residual_add_equitable` is type-generic and ports immediately;
- the Eckart–Young half needs the **Hermitian** SVD / spectral truncation
  (`Matrix.IsHermitian.spectral_theorem`, which the file already uses for the
  *diagonal* real case) generalised so the optimal rank-`k` residual is the
  top-`k` eigenspace of the *Hermitian* residual `R = H − H_eq`. Eckart–Young
  holds verbatim for the Frobenius norm over ℂ (unitary invariance), so this is a
  mechanical-but-real lift, not a new theorem.

### 2.3 The chiral mixing speedup is complex-Hermitian — but it must be wired to a phased *host*

`Chiral.lean` / `Mixing.lean` are *already* complex: `ChiralSigning.σ : V→V→ℂ`,
`signedBy`, `ChiralMixingSigning` (Hermitian signed adjacency),
`cellBlockAmp_eq_quotient` (the host↔quotient identity, **proven sorry-free**),
`chiralMixingQuotient`. The speedup *statement*
(`chiralAttention_mixing_speedup_hook`, `chiral_mixing_optimization`) carries the
honest `sorry` (the Levine `π/(3√3)` spectral content). What is missing is **not**
complexity — it is the *connection* of this machinery to a host that is itself
phased (RoPE). Right now `chiralAttention` signs a *real* host. To model PCT we
need the signing to compose with a host that already carries the RoPE phase, i.e.
`H = (RoPE-phased complex-Hermitian kernel)`, then `H.signedBy s` adds the *extra,
optimised* chiral edge phase. The intertwining `cellBlockAmp_eq_quotient` is
host-agnostic (it only needs Hermitian + `ReducesToQuotient`), so it ports —
the work is constructing the RoPE-phased host as a `WeightedGraph V` / Hermitian
adjacency.

### 2.4 The equitable lift needs a complex-Hermitian host

`signedBy_preserves_equitable` (`Chiral.lean`) and `chiralAttention_descends`
(`NovelAttention.lean`) — *cross-constant phase preserves the equitable
partition* — are **already complex** and **proven sorry-free**. Good. But the
*partition itself* (`EquitablePartition`) is currently defined relative to a
host whose adjacency we feed from the **real** `symmScore`. For PCT the partition
must be equitable for the **complex-Hermitian RoPE host** (cell row-sums of a
complex kernel). `EquitablePartition` is type-generic over the weighted graph's
field, so the definitions port; what must be re-checked is that a relative-
position (RoPE) host is genuinely equitable for the position-cell partition —
which is exactly the cross-constant condition `σ(i,j)=τ(cell i,cell j)` for
`cell = position-mod` (the band/Toeplitz structure of relative position). **This
is provable and is the structural heart of the design in §3.**

### 2.5 Summary table — which results need the complex-Hermitian generalisation

| Result | Current type | PCT needs | Status of lift |
|---|---|---|---|
| Eckart–Young corrected attention (`corrected_equitable_attention`, `diag_eckartYoung_optimal`, `equitablePart`, `residual`) | **ℝ only** | complex-Hermitian `H=H_eq+R`, top-`k` *Hermitian* eigentruncation | **the central gap** — mechanical lift via Hermitian spectral theorem; EY holds over ℂ |
| chiral mixing speedup (`chiralAttention_mixing_speedup_hook`, `chiral_mixing_optimization`) | complex, `sorry` | same, wired to a *phased* host | complex already; needs RoPE-host construction + the Levine spectral content |
| host↔quotient identity (`cellBlockAmp_eq_quotient`) | complex, **proven** | host-agnostic | ports — needs only Hermitian + `ReducesToQuotient` |
| equitable lift (`signedBy_preserves_equitable`, `chiralAttention_descends`) | complex, **proven** | partition equitable for complex-Hermitian RoPE host | ports; needs RoPE-host-is-equitable lemma |
| symmetrized host (`symmScore`, `symmetrizedAttention`) | real-cast-to-ℂ | genuine complex-Hermitian kernel | needs a `complexHost` constructor carrying `Re + i·Im` |

**The single most important complex-case extension:** *generalise the
Eckart–Young / corrected-attention `A=A_eq+R` apparatus from `Matrix _ _ ℝ` to a
complex-Hermitian host with top-`k` Hermitian eigentruncation.* Until that lands,
**none** of our `O(n(r+k))` cost/optimality results formally reach PCT-style
(phased/RoPE) attention, and the chiral framework cannot claim PCT's host as an
instance. Everything else (the mixing speedup wiring, the equitable lift) is
downstream of having a genuine complex-Hermitian host object to operate on.

---

## 3. The Graphplay phase-coherent attention design

### 3.1 The design: active-edge-phase chiral attention

PCT puts phase **passively in the value channel** (`out = W_o Σ_j α_{ij} v_j`,
real `α`, complex `v`) and discards `Im⟨q̄,k̄⟩` from the gate. Our design puts the
phase **actively on the edges of the token graph** as an *optimised* U(1)
signing, and keeps it in the operator that generates propagation.

**Chiral phase-coherent attention (CPCA).** Take a PCT-style head and instead of
the real gate `α_{ij}` on a real score, form the **complex-Hermitian propagation
host**

```
H_{ij} = α_{ij} · σ(i,j) · ‖·‖   with   σ(i,j) = e^{iθ(cell i, cell j)}     (i≠j),
H_{ii} = 0,   H_{ji} = conj(H_{ij})            (Hermitian, loopless)
```

where:

1. `α_{ij} = σ_gate(Re⟨q̄_i,k̄_j⟩+b)` is PCT's *real, smooth, C1–C4-satisfying*
   magnitude gate (we **keep** PCT's L1/L2 guarantees on the magnitude);
2. `θ(·,·)` is a **cross-constant** U(1) edge phase — `θ` depends only on the
   *cell pair* (positional/relative-position cells), i.e. a flat U(1) connection
   on the cell-partition graph (`ChiralSigning.CrossConstant`,
   `ChiralGraphon`'s U(1)-gauge reading);
3. propagation is the CTQW / layer-iterate of `H` (the magnetic adjacency), so
   the phase is *in the generator* `exp(−itH)`, not merely in `v`.

This is *exactly* `chiralAttention A s` (`NovelAttention.lean §1`) with `A` the
PCT magnitude gate and `s` the cross-constant signing — already a proven
`WeightedGraph` (`chiralAttention_hermitian`) that **descends to the equitable
quotient** (`chiralAttention_descends`). The only new content is *choosing `θ`
for fastest mixing* and *wiring it to a RoPE host*.

### 3.2 Three structural reasons it could beat PCT

- **(R1) Active beats passive on long-range.** PCT preserves the anti-phase
  (destructively-interfering) components *passively* (a smooth gate that doesn't
  delete them). A cross-constant chiral signing *creates and maximises* them: the
  Levine K₄ signing places `±i` phases (`Re(±i)=0`, pure anti-alignment;
  `unitaryHammingChiralK4` in `Chiral.lean`) so paths interfere destructively and
  the walk mixes at `π/(3√3)`, **strictly faster than any unsigned host**. If
  long-range performance tracks host mixing time, *the fastest-mixing host wins*,
  and PCT's host (real-symmetric gate, time-reversal-symmetric, gap-limited) is
  **not** the fastest. PCT keeps the chiral channel open; we make it optimal.

- **(R2) `η` should be on the edges, optimised — not in the Jacobian,
  uncontrolled.** PCT's own Doeblin Jacobian (M.3 Lemma B) contains
  `η_{ij}=−Im⟨q̄_i,k̄_j⟩` — an *uncontrolled* chiral phase that happens to ride in
  the contraction. Our design makes `η` a *first-class, learned, cross-constant
  edge phase* that the equitable lift preserves. The Doeblin contraction is the
  *same proof genus* either way (Lemma C ≈ `chiralMixingQuotient`'s cell-block
  amplitude contraction), but a chosen `η` controls the contraction rate via the
  **quotient spectral gap**, which a free `η` does not.

- **(R3) Cross-constant `θ` preserves the `O(n·r)` quotient.** Because `θ` is
  cell-pair-constant, `chiralAttention_descends` guarantees the phased host still
  lifts to the small quotient, so the `O(n(r+k))` apply cost survives the phasing
  (pending the §2.2 complex Eckart–Young lift). PCT has *no* quotient story —
  every head is `O(n²)`. A learned generic per-pair `θ_{ij}` would also have no
  quotient; **cross-constant is the sweet spot** that is both expressive (it is
  the relative-position band structure) and cheap.

### 3.3 The concrete, falsifiable design claim

> **Claim (CPCA).** For long-range propagation tasks (Copy d≥2000, NIAH L=2048,
> ListOps L=1024), an active cross-constant U(1) edge-signing `θ(cell i,cell j)`
> on the PCT magnitude gate — a *relative-position* signing `θ = θ(i−j)` — gives
> a host whose **continuous-time mixing time is strictly smaller** than (a) the
> unsigned/real PCT host and (b) a free per-pair `θ_{ij}`, and this advantage
> **tracks the operator-level mixing-time ratio**. The cross-constant signing
> also (c) preserves the equitable quotient (so stays `O(n(r+k))`), which the
> free signing does not.

Falsifiers, any one of which sinks it: (a) the cross-constant chiral host's
measured mixing time is **not** below the unsigned host's; (b) a free `θ_{ij}`
mixes as fast or faster (then "cross-constant optimality" is wrong); (c) on a
trained run the learned `θ` collapses to 0 / a global constant (then the active
edge phase buys nothing over PCT's passive scheme).

### 3.4 The simulator experiment that tests it (operator-first, no training)

The cleanest test is **operator-level**, in the simulator, decoupled from
training noise — exactly the regime where Graphplay has proven machinery
(`Mixing.lean`: `IsUniformMixing`, `IsCellUniformMixingOf`, `mixing`, `evolve`).

**Experiment CPCA-MIX.**

1. **Build three hosts on a structured-attention token graph** (e.g. a
   relative-position / band Toeplitz host `H_band` standing in for a RoPE
   attention pattern, n ∈ {64,256,1024} tokens, cells = position bands):
   - `H_0` = unsigned real-Hermitian host (PCT-analogue host: `signedBy trivial`);
   - `H_χ` = `H_0.signedBy s_cc`, `s_cc` a **cross-constant** signing
     `σ(i,j)=e^{iθ(cell i,cell j)}`, `θ` swept toward the Levine-optimal
     conical-reduction pattern (and including the explicit
     `unitaryHammingChiralK4` block on the cell quotient);
   - `H_free` = `H_0.signedBy s_free`, `s_free` a generic per-pair phase
     (control for "active *and* cross-constant" vs "active but unstructured").
2. **Measure CTQW mixing time** for each: the smallest `t` with
   `max_{u,v} |M(t)_{uv} − 1/n| ≤ ε` (use `WeightedGraph.mixing`,
   `IsUniformMixing` from `Mixing.lean`; for the quotient use
   `IsCellUniformMixingOf` on `cellBlockAmp`). Report `τ_χ`, `τ_0`, `τ_free`.
3. **Predicted outcome:** `τ_χ < τ_0` (chiral beats unsigned — the Levine
   speedup; the `K₄→K₁+K₃` block should give a clean `π/(3√3)` ratio on the
   matching quotient) and `τ_χ ≤ τ_free` *with* `H_χ` preserving the equitable
   quotient (verify via `chiralAttention_descends` / `signedPartition`) while
   `H_free` does not.
4. **Then, and only then, train.** Drop `H_χ` (cross-constant relative-position
   chiral phase) into a PCT cell as the propagation host and rerun Copy
   d=2000/5000, NIAH L=2048, ListOps L=1024 vs vanilla PCT. Predict
   *layers-to-solve* drops by a factor tracking `τ_0/τ_χ` measured in step 2.

The simulator pieces needed: a `complexHost`/`bandHost` constructor (a Hermitian
`WeightedGraph` from a relative-position kernel — `Simulate.lean` /
`Toolkit/InverseDesign.lean` are the natural homes), then `mixing` /
`IsUniformMixing` give `τ` directly. `cellBlockAmp_eq_quotient` (proven) lets us
read the quotient mixing time off the small `I×I` quotient instead of the full
`n×n` host — the `O(n·r)` win in the *measurement* itself.

---

## 4. Can we extend toward / improve on PCT? — honest assessment

**Verdict: MAYBE — leaning yes on long-range mixing, no on trained depth
stability, with one clean shot at PCT's own open anomaly.**

### 4.1 Where we can EXPLAIN PCT with a theorem (the mixing speedup)

PCT's headline ablation — *preserve anti-phase components → long-range works;
delete them → distance-independent collapse* — is the ML shadow of the chiral
fast-mixing mechanism. The anti-phase (negatively-aligned) components **are** the
destructive-interference channel that fast mixing rides on; deleting them returns
the walk to the time-reversal-symmetric, gap-limited regime. Two signatures
*only* a mixing account predicts and PCT confirms:

- **distance-independent on/off collapse** (clamped_relu bit-identical 0.103 at
  every d) — a *mixing-channel-present/absent* signature, not a diffusive-decay
  one (decay would be graded in distance);
- **`L`-independent depth cascade** — PCT proves it by Doeblin contraction on the
  zero-mean phase subspace (M.3 Lemma C), the **same proof genus** as our
  `chiralMixingQuotient` cell-block amplitude contraction. This convergence of
  *proof technique* (Doeblin on a phase subspace) is the strongest single piece
  of evidence the two stories share a mechanism.

This is an *explanation*, not a derivation: PCT runs a real-gated complex-value
layer, not our `exp(−itH^σ)` CTQW; our theorems do not literally instantiate on
PCT (and our two central mixing theorems —
`cellBlockAmp_eq_quotient` is proven, but `chiral_mixing_optimization` /
`chiralAttention_mixing_speedup_hook` carry honest `sorry`s). Stated as a
derivation it would be false; stated as a convergent mechanism it is sharp.

### 4.2 Where we PREDICT beyond PCT (the active-edge-phase, the optimal signing)

1. **Cross-constant edge-phase optimality.** The optimal phase pattern is a
   relative-position **cross-constant** U(1) edge-signing (preserves the
   equitable quotient, reduces to a quotient phasing), beating both a free
   per-pair `θ_{ij}` and PCT's `θ=0`. PCT never introduces an *edge* phase at all
   — it keeps phase in `v`. This is the cleanest *ours-not-PCT* claim. (§3.3,
   tested by CPCA-MIX §3.4.)
2. **Quantitative mixing-time scaling of layers-to-long-range.** PCT's depth
   result is *qualitative* ("no collapse"). We predict layers-to-solve drops by
   the operator mixing-time ratio `τ_0/τ_χ` — a *number*, testable on the
   operator before any training.
3. **Task-geometry dependence of anti-phase deletion.** PCT shows "delete →
   collapse" globally. We predict the collapse magnitude tracks how much
   anti-phase mass the task's equitable partition carries off-cell: on a
   *short-range / no-cross-cell* task, anti-phase deletion should be **harmless**
   (chiral channel empty). PCT's data is consistent but never frames this — a
   sharper, falsifiable refinement.
4. **The Real RadioML anomaly (§5.7) as a positive test.** PCT *cannot* explain
   why `real_screen` beats PCT on physical I/Q data. We predict the discriminator
   is whether the task's optimal host is *genuinely chiral* (time-reversal-broken,
   complex eigenstructure) — physical I/Q modulation has intrinsic phase geometry
   whose optimal attention host may be a *specifically signed* one, not PCT's
   real-gated host. **Prediction: a learned cross-constant chiral host recovers or
   beats `real_screen` on Real RadioML where PCT falls short** — turning PCT's
   own open anomaly into a positive test of the edge-signing mechanism. This is
   the single most attractive empirical follow-up: it attacks PCT's *own*
   unexplained gap with our distinguishing mechanism.

### 4.3 Where PCT is genuinely ahead (concede)

- **Trained depth stability 2–20.** PCT has *run* it: no collapse, with a
  machine-checked (premise-bundled) `L`-independent Lipschitz constant. Our
  `L`-independence claim is an *operator-quotient-gap* prediction
  (`chiral_mixing_optimization`, still `sorry`) — unproven and untrained.
- **The full trained mid-scale empirical suite** (9 tasks, 6 cells, parameter-
  fair, LR/batch robustness). We have *zero* trained results; everything we have
  is operator-level Lean + the simulator.
- **The C1–C4 gate-condition framework with its own Lean Thm 1 / Thm 5.** A
  self-contained, machine-checked theory of *which gates* preserve coherence. We
  do not have an analogous trained-gate theory.
- **The honest no-overclaim discipline** (depth result framed as qualitative, not
  a scaling law) — a standard worth matching.

### 4.4 Concrete next experiments (in order)

1. **CPCA-MIX (§3.4), operator-only** — measure `τ_χ` vs `τ_0` vs `τ_free` on a
   band/RoPE host in the simulator. Cheapest, no training; directly tests the
   core mixing claim and the cross-constant-optimality claim. *Falsifiable today.*
2. **Land the complex Eckart–Young lift (§2.2/§2.5)** — port `equitablePart`,
   `residual`, `corrected_equitable_attention` to complex-Hermitian `H` via the
   Hermitian spectral theorem; this is the formal bridge that lets *any* of our
   cost/optimality results reach PCT-style attention. Discharges the central gap.
3. **Construct the RoPE/relative-position host as a Hermitian `WeightedGraph`** and
   prove it is equitable for the position-band partition (the cross-constant
   condition for `θ=θ(i−j)`); this wires `chiralAttention_descends` to a *real*
   PCT host.
4. **Trained CPCA vs PCT** on Copy d=5000 / NIAH / ListOps, predicting
   layers-to-solve ∝ `τ_0/τ_χ` from step 1.
5. **Real RadioML rematch** — learned cross-constant chiral host vs `real_screen`,
   to convert PCT's open anomaly into a positive test (§4.2.4).

---

*( ⌐■_■ ) PCT kept the destructively-interfering phase alive in the value channel
and threw `Im⟨q̄,k̄⟩` out of the gate — but it reappears, uncontrolled, in their
own Doeblin Jacobian as η. That η is a U(1) edge-signing. Our move: put it on the
edges, make it cross-constant, choose it for fastest mixing — and measure τ_χ <
τ_0 in the simulator before we ever train.*
