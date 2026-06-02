# Walk-Operator Post-Hoc Distillation / Grafting — Findings

**Experiment:** Take a *trained* small transformer, fit structured-walk operators
(a dictionary of CTQW / classical-walk atoms: heat / shift / circulant / chiral /
Chebyshev / Bessel / coined / two-horn / power-law / learned-Hamiltonian) to its
attention heads, then **graft** the walk operators back in — replacing the
softmax(QKᵀ) mixing pattern of a chosen set of heads with the cheap walk
operator — and measure **how much function survives** as a function of *how many
heads are replaced* and *which head type*.

This is the **post-hoc distillation / grafting** probe that the atlas↔walkformer
reconciliation pointed at as the one adoption path *not* ruled out. It tests the
**expressivity / compression** claim directly, **decoupled from training
dynamics** (unlike the from-scratch walkformer, which was falsified — see
`WALKFORMER_PROBE_FINDINGS.md` / memory `restrans-suite-is-junk`).

- **Model (teacher):** `EleutherAI/pythia-70m` (GPTNeoX, 6 layers × 8 heads = 48
  heads, RoPE). Frozen. Chosen because it is small, real, pretrained, and uses a
  clean GPTNeoX attention we can surgically graft per-head.
- **Walk dictionary:** the `WalkKernel` v2 atom set (10 atoms) from
  `resonance/resonance/kernels.py` — each atom a Toeplitz (function-of-offset)
  walk operator with Lean-formalized semantics. Causal-softmax of the kernel's
  per-offset bias *is* the grafted attention matrix.
- **Hardware:** persvati ROCm (AMD Radeon, `HSA_OVERRIDE_GFX_VERSION=11.0.0`).
- **Code:** `~/restrans/resonance/walkformer_graft/` on persvati —
  `g1_kernel_fit.py` (fit, static), `graft.py` + `g2_graft_distill.py`
  (layer-level graft+distill), `g3_head_sweep.py` (per-head fraction sweep,
  written for this task). `common.py` shared utils.

---

## A-PRIORI PREDICTIONS (stated before running)

These come directly from the framework's own theorem
(`EquitableMechanism.lean`: generic learned attention has a discrete 1-WL
partition ⇒ rank floor ⇒ *no nontrivial exact walk compression*) and the
circuit-atlas head taxonomy:

- **P1 (positional heads graft cleanly).** Heads that are banded / translation-
  equivariant (high `toep_cos`, local or fixed-offset structure — the thermal
  path-CTQW / log(A)-banded heads) **ARE walks**, so a walk operator should fit
  them tightly (low reconstruction residual) and, when grafted, the model's
  function should largely survive.
- **P2 (content / induction heads degrade badly).** Content / induction / sink
  heads are **irreducible** (1-WL floor): a Toeplitz walk operator structurally
  cannot represent them. Grafting them should degrade function badly even after
  distillation.
- **P3 (a survival cliff).** Function survival should be **high when only the
  positional fraction is replaced** and **fall off** once content/induction
  heads start being replaced.

---

## STAGE 1 — Static walk-fit to every head (g1)  ✅ DONE

We run the teacher on 64 wikitext-103 sequences (len 64), average attention per
head to get its *characteristic* map, then fit a fresh walk kernel's attention to
each head map by direct Adam optimization of the kernel params alone (no model,
no content path) minimizing KL + 0.1·Frobenius. We report the walk relative-
Frobenius residual vs. the **Toeplitz oracle** (the best-possible translation-
equivariant attention — the information-theoretic ceiling any walk basis could
reach). Heads split by `toep_cos` (cosine of the head to its own Toeplitz
projection) at 0.85.

| head class | n | walk relFro | oracle relFro (ceiling) | walk KL |
|---|---|---|---|---|
| **positional** (toep_cos ≥ 0.85) | **28** | **0.185** | 0.210 | 0.054 |
| **content** (toep_cos < 0.85)    | **20** | **0.796** | 0.867 | 1.037 |

**Result: P1 + P2 confirmed at the static-fit level, sharply.**
- Positional heads reconstruct to **walk 0.185 vs. ceiling 0.210** — the walk
  basis reaches within **2.5 percentage points of the Toeplitz ceiling**; they
  are genuinely walk-shaped.
- Content heads sit at **walk 0.796**, and crucially the **oracle itself is
  0.867** — even the *best possible* Toeplitz attention fails on them. The
  failure is **not** a weak basis; these heads are intrinsically
  non-translation-equivariant (content routing / attention sinks). This is the
  irreducibility floor, measured.

**Independent validation (layer anatomy, recovered from scratch).** The
`toep_cos` meter — which has no layer information — places positional heads in
the early layers and content heads in the late layers, matching known pythia
anatomy:

```
positional heads per layer: {L0: 8, L1: 8, L2: 7, L3: 2, L5: 3}   (23/28 in L0–2)
content    heads per layer: {L2: 1, L3: 6, L4: 8, L5: 5}           (19/20 in L3–5)
```

Full per-head table (ranked positional→content) is at the end of this file.

---

## STAGE 2 — Behavioral graft + distill, by LAYER (g2)  ✅ DONE

Now the real behavioral test: replace the attention *mixing pattern* of whole
layers with walk-kernel attention (keep the teacher's V and output dense),
distill **only** the walk params (per-head kernel + temperature) to match the
frozen teacher's next-token logits (KL + 0.5·CE) on wikitext (192 train / 64 eval
sequences, len 128, 300 steps). Early layers (L0–2) ≈ positional proxy; late
layers (L3–5) ≈ content proxy.

`recovered_fraction = (ppl_untrained − ppl_distilled) / (ppl_untrained − ppl_teacher)`,
clipped to ≤ 1. `residual_ratio = ppl_distilled / ppl_teacher`. **Teacher
ppl = 123.3.**

| graft (mode `pos`) | ppl untrained → distilled | recovered | residual ×teacher |
|---|---|---|---|
| **early L0–2 (positional-ish)** | 646.0 → **295.7** | **0.670** | 2.40× |
| **late  L3–5 (content-ish)**    | 321.5 → **247.8** | **0.372** | 2.01× |
| all L0–5                         | 872.1 → **486.3** | 0.515     | 3.94× |

**Result: P1/P2/P3 directionally confirmed; magnitude is sobering.**
- Early/positional-layer grafts recover **~1.8× more** of the lost perplexity
  (0.670) than late/content-layer grafts (0.372) — the predicted gradient by
  head type is real.
- BUT pure positional walk attention is **not free**: even the best (early) graft
  lands at **2.4× teacher perplexity**. Walk operators carry the positional
  *shape* but lose a large amount of the function the full QK machinery provides.
  Reported plainly — this is a compression-with-loss story, not lossless.

**`pos+lowrank` control — does a rank-4 content channel rescue the content
layers?** Same graft, but each grafted head also gets a learnable rank-4 content
logit correction (q'k'ᵀ, started OFF at exp(−4)) added to the walk bias before
softmax. **Teacher ppl = 123.3.**

| graft (mode `pos+lowrank`) | ppl untrained → distilled | recovered | residual ×teacher | trainable params |
|---|---|---|---|---|
| early L0–2 | 646.3 → **148.5** | **0.952** | 1.204× | 100,032 |
| late  L3–5 | 321.4 → **145.6** | **0.888** | 1.181× | 100,032 |
| all L0–5   | 872.3 → **179.3** | **0.925** | 1.454× | 200,064 |

**Result: nuance for P2 — a small content channel closes most of the gap, even
for content layers.** With rank-4 content added, late/content layers recover
**0.888** (residual 1.18×) — nearly as well as positional layers (0.952). So the
"irreducible" content fraction of pythia-70m's late heads is **largely
recoverable at rank 4**. This is consistent with the framework's measured
"content is *low-rank* but not equitable" finding (generator S=QKᵀ is low-rank);
the irreducibility theorem is about *exact* compression, and here we measure
*approximate* recovery where rank-4 suffices to within ~18% perplexity.

**⚠ Honest caveat (load-bearing for interpretation):** in `pos+lowrank` the
trainable params are **~100 K**, of which the walk kernels are only ~2.5 K — the
rest is the rank-4 content channel (2 × hidden 512 × 8 heads × rank 4 × 3
layers). So in this mode **the content channel, not the walk basis, does most of
the heavy lifting**, which is exactly why it rescues content layers. The clean
expressivity test of *the walk basis alone* is therefore the `pos` mode above
(content QK fully discarded, only ~2.5 K walk params) and the per-head sweep
(Stage 3) — those are the numbers that isolate "what walk operators can do."
`pos+lowrank` is the upper bound of "walk shape + a cheap learned content
correction," and it says that bound is high (residual 1.2–1.5×).

---

## STAGE 3 — Per-head fraction sweep (g3): the survival curve  ✅ DONE

This is the precise version of the task. We graft **individual heads** (not whole
layers): non-grafted heads run the exact teacher path (RoPE + softmax(QKᵀ) + V);
grafted heads use **pure walk-kernel attention** on the teacher V (content QK
*fully discarded* for that head — no rank-4 channel here, ~63 walk params/head).
Only the grafted heads' walk params are distilled to the frozen teacher (300
steps). We sweep the **fraction of heads replaced** under three orderings of the
g1 `toep_cos` ranking:
- **`pos_first`** — most-positional heads first (high `toep_cos`).
- **`content_first`** — most-content heads first (low `toep_cos`).
- **`random`** — shuffled control.

**Teacher ppl = 123.3.** Two metrics, and *the distinction between them is the
whole story*:
- `recovered_fraction` = (ppl_untrained − ppl_distilled)/(ppl_untrained −
  ppl_teacher) — **how much of the function the graft destroyed does the walk
  basis claw back** = how *walk-expressible* those specific heads are.
- `residual_ratio` = ppl_distilled / ppl_teacher — absolute distance from teacher.

### recovered_fraction — the head-type discriminator (HIGHER = more walk-expressible)

| frac | k heads | **pos_first** | **content_first** | random |
|---|---|---|---|---|
| 0.042 | 2  | **0.926** | **0.437** | 0.690 |
| 0.083 | 4  | **0.907** | **0.234** | 0.628 |
| 0.167 | 8  | **0.823** | **0.172** | 0.605 |
| 0.250 | 12 | **0.750** | **0.225** | 0.610 |
| 0.375 | 18 | **0.720** | **0.220** | 0.591 |
| 0.500 | 24 | **0.691** | **0.231** | 0.604 |
| 0.667 | 32 | 0.686 | 0.366 | 0.683 |
| 0.833 | 40 | 0.650 | 0.447 | 0.632 |
| 1.000 | 48 | 0.511 | 0.516 | 0.513 |

**This is the decisive result. P1, P2, P3 confirmed.** Grafting the most-
positional heads, the walk basis recovers **75–93%** of the function it
displaced. Grafting the most-content heads, it recovers only **17–44%** — a
**3–4× gap** in walk-expressibility, exactly the predicted positional/content
split. `random` sits cleanly between the two everywhere (mixed head types). At
f = 1.0 all three converge (0.51, identical head set) — sanity check passes.
`mean_toep_cos` of the grafted set runs 0.999→0.77 for pos_first and 0.37→0.77
for content_first, confirming the orderings select the intended head types.

### residual_ratio (ppl_distilled / teacher) — absolute survival (LOWER = better)

| frac | **pos_first** | **content_first** | random |
|---|---|---|---|
| 0.042 | 1.026 | 1.020 | 1.035 |
| 0.083 | 1.056 | 1.129 | 1.052 |
| 0.167 | 1.171 | 1.194 | 1.150 |
| 0.250 | 1.452 | 1.216 | 1.307 |
| 0.375 | 1.937 | 1.798 | 1.605 |
| 0.500 | 2.358 | 2.060 | 2.017 |
| 0.667 | 2.606 | 2.432 | 2.391 |
| 0.833 | 3.045 | 3.291 | 2.795 |
| 1.000 | 3.969 | 3.940 | 3.957 |

**⚠ The honest subtlety (must be stated, it complicates the naive "cliff"
story).** The *absolute* perplexity does **not** show a clean positional/content
cliff — at low fraction all three orderings sit near 1.0–1.2× teacher, and at
high fraction they converge to ~4×. Counterintuitively, `content_first` is
sometimes *lower* (better) residual than `pos_first` at matched fraction.

The reason is diagnostic, not a contradiction: **content heads, when grafted
*before distillation*, barely perturb the model** (they are diffuse / high-
entropy / sink heads, and an untrained walk kernel's near-uniform output already
approximates that average of V) — so the absolute damage from grafting them is
small. **Positional heads cause large perturbation** (they do precise local /
offset routing) — but the walk basis then *recovers most of it*. So:
- on **content** heads: small damage, but walk fixes little of it (recovered 0.2) → **irreducible, just cheap to begin with**;
- on **positional** heads: large damage, walk fixes most of it (recovered 0.7–0.9) → **reducible to a walk**.

The head-type signal therefore lives in **recovered_fraction, not in raw
residual_ratio**. Anyone citing this experiment as "positional heads survive
grafting, content heads fall off a perplexity cliff" would be **overstating** —
the truth is "positional-head *function* is walk-recoverable; content-head
function is not, but content heads were carrying little isolated marginal
perplexity in the first place." Reported plainly.

---

## HEADLINE NUMBERS

- **Static walk-fit (g1):** positional heads **0.185** relFro vs Toeplitz ceiling
  **0.210** (walk basis ≈ ceiling); content heads **0.796** vs ceiling **0.867**
  (even the *best* Toeplitz fails — genuinely irreducible). Sharp bimodal split,
  28 positional / 20 content, layer anatomy recovered from scratch.
- **Per-head behavioral survival (g3), the headline:** walk-grafting the most-
  positional heads recovers **0.93 → 0.75 → 0.69** of their displaced function
  (2→12→24 heads); the most-content heads recover only **0.44 → 0.23 → 0.23** —
  a **3–4× walk-expressibility gap by head type**, with `random` cleanly between.
- **Layer graft, pure walk (g2 `pos`):** positional layers recover **0.670** of
  lost ppl (residual 2.40×); content layers **0.372** (residual 2.01×).
- **Layer graft + rank-4 content (g2 `pos+lowrank`):** **0.95 / 0.89 / 0.93**
  recovery (residual 1.18–1.45×) — but the ~100 K content-channel params, not the
  ~2.5 K walk params, drive that; it bounds "walk shape + cheap content fix," not
  walk alone.

### Verdict on the predictions

| prediction | held? | evidence |
|---|---|---|
| **P1** positional heads graft cleanly | **YES** | static fit 0.185≈ceiling; behavioral recovery 0.69–0.93 (pos_first) |
| **P2** content/induction heads degrade / irreducible | **YES** | static fit 0.80 (ceiling itself 0.87); behavioral recovery only 0.17–0.44 (content_first) |
| **P3** survival high for positional, falls for content | **YES, in the right metric** | clean 3–4× `recovered_fraction` gap pos vs content; **but NOT a raw-perplexity cliff** (content heads carry little isolated ppl) — see Stage 3 subtlety |

**Bottom line.** The post-hoc grafting probe **confirms the framework's core
claim and is consistent with both prior results** (the descriptive atlas
*succeeded*; the generative from-scratch walkformer *failed*): a trained model's
**positional heads ARE walks** — replace them with ~63-param walk operators and
distillation recovers 70–90% of their function — while its **content/induction
heads are irreducible** to walks (recover ~20%), exactly as the 1-WL rank-floor
theorem predicts. This is the honest "compress the structured fraction" story:
walk operators are a faithful, ultra-cheap substitute for the positional
fraction of attention and a poor one for the content fraction. It is **not** a
universal attention compressor (pure-walk all-heads graft lands at ~4× teacher
perplexity), and the apparent rank-4 "rescue" of content layers is the content
channel, not the walk basis, doing the work. No cherry-picking: the raw-
perplexity view does not show a clean cliff, and we say so.

---

## Reproduction

All code + outputs live in `~/restrans/resonance/walkformer_graft/` on **persvati**
(not a git repo there — left in place). Env: `~/restrans/.venv`,
`export HSA_OVERRIDE_GFX_VERSION=11.0.0` (gfx1150 iGPU), wikitext-103-raw +
pythia-70m cached under `~/.cache/huggingface`.

```bash
# Stage 1 — static walk-fit per head  -> outputs/g1_persvati.json
python g1_kernel_fit.py --model EleutherAI/pythia-70m --device cuda \
    --n_batches 64 --seq_len 64 --steps 400 --out outputs/g1_persvati.json
# Stage 2 — layer graft+distill (pure walk, then +rank-4 content)
python g2_graft_distill.py --device cuda --mode pos        --out outputs/g2_pos.json
python g2_graft_distill.py --device cuda --mode pos+lowrank --lowrank 4 --out outputs/g2_lowrank.json
# Stage 3 — per-head fraction sweep (THE survival curve) -> outputs/g3_head_sweep.json
python g3_head_sweep.py --device cuda --steps 300 \
    --fractions 0.0417,0.0833,0.1667,0.25,0.375,0.5,0.667,0.833,1.0 \
    --orders pos_first,content_first,random --out outputs/g3_head_sweep.json
python analyze_g3.py outputs/g3_head_sweep.json     # prints the tables in this file
```

Runner that produced these numbers: `run_full.sh` (log: `outputs/run_full.log`).
Teacher ppl reproduced at **123.32** across all three runs (deterministic seed 0).
Distillation: KL(student‖teacher logits, T=2) + 0.5·CE, Adam, 300 steps, 192
train / 64 eval packed wikitext sequences of length 128, batch 8.

**Method notes / limitations.** (1) Single model, single scale (pythia-70m, 48
heads) — the head-type *gap* is robust here but absolute magnitudes are scale-
and model-specific; a 160m/410m replication would strengthen it. (2) g1 fits the
*batch-averaged characteristic* attention map (positional component survives
averaging, content spikes wash out) — this is the right target for a position-
only kernel but means g1 slightly *flatters* the walk fit vs. per-example
attention. (3) g3's grafted heads discard RoPE+content entirely (≈63 walk params
+ 1 temp per head), the strict pure-walk expressivity test; non-grafted heads run
the exact teacher path. (4) `recovered_fraction` normalizes by the per-ordering
untrained gap, so cross-ordering comparison must use it *together with* absolute
ppl (both reported) — see the Stage-3 subtlety. (5) 300 distill steps plateaued
(g2 KL flat by ~150); more steps did not materially change the layer numbers.

---

## Appendix — per-head static fit (g1), ranked positional → content

```
  L.H  toepC walkRF  oraRF local  sink   ent       dom
  2.1  1.000  0.033  0.033  0.95  0.04  0.25    chiral
  0.1  0.998  0.062  0.066  0.82  0.04  0.54    chiral
  1.3  0.997  0.068  0.079  0.58  0.04  0.73    chiral
  1.1  0.996  0.090  0.090  0.80  0.03  0.60    chiral
  1.5  0.990  0.140  0.146  0.57  0.04  0.80    chiral
  1.0  0.988  0.138  0.162  0.45  0.05  0.89    chiral
  0.4  0.988  0.149  0.156  0.58  0.04  0.77    chiral
  1.6  0.987  0.149  0.168  0.49  0.03  0.86    chiral
  1.2  0.986  0.172  0.174  0.64  0.07  0.75      heat
  2.7  0.985  0.160  0.171  0.60  0.08  0.66    chiral
  0.7  0.985  0.172  0.179  0.55  0.06  0.81    chiral
  1.7  0.984  0.171  0.185  0.49  0.06  0.87    chiral
  0.3  0.983  0.148  0.193  0.42  0.02  0.82  learnedH
  0.5  0.982  0.183  0.193  0.50  0.04  0.84    chiral
  5.7  0.982  0.191  0.191  0.89  0.04  0.45    chiral
  2.3  0.980  0.193  0.204  0.49  0.05  0.86    chiral
  0.2  0.979  0.134  0.218  0.27  0.05  0.97      cheb
  2.4  0.977  0.210  0.214  0.67  0.05  0.65    chiral
  3.4  0.977  0.215  0.217  0.64  0.11  0.70    chiral
  5.2  0.972  0.236  0.236  0.73  0.10  0.56      heat
  5.1  0.972  0.233  0.235  0.58  0.05  0.65    chiral
  0.6  0.970  0.171  0.250  0.27  0.07  0.97      cheb
  1.4  0.970  0.143  0.255  0.23  0.08  0.99      cheb
  0.0  0.968  0.199  0.255  0.29  0.08  0.94      cheb
  2.5  0.959  0.207  0.299  0.25  0.09  0.98      cheb
  2.0  0.952  0.280  0.308  0.32  0.10  0.90      cheb
  2.2  0.872  0.444  0.493  0.23  0.16  0.92      cheb   <- last positional (toep_cos>=0.85)
  3.2  0.852  0.477  0.525  0.25  0.14  0.92      cheb
  4.0  0.738  0.649  0.676  0.24  0.27  0.84    chiral
  3.7  0.626  0.770  0.783  0.28  0.36  0.75  learnedH
  4.5  0.624  0.736  0.781  0.14  0.37  0.76 circulant
  5.0  0.623  0.779  0.789  0.47  0.42  0.55    chiral
  4.6  0.584  0.765  0.814  0.18  0.35  0.76  learnedH
  2.6  0.578  0.782  0.845  0.20  0.32  0.81  learnedH
  3.3  0.517  0.788  0.858  0.14  0.43  0.76      cheb
  4.3  0.488  0.807  0.873  0.10  0.50  0.62      cheb
  5.4  0.485  0.861  0.878  0.30  0.50  0.56      cheb
  5.5  0.468  0.872  0.887  0.26  0.52  0.59  learnedH
  5.6  0.456  0.850  0.892  0.14  0.49  0.62  learnedH
  5.3  0.446  0.888  0.901  0.30  0.48  0.56  learnedH
  4.2  0.426  0.825  0.904  0.09  0.60  0.53      cheb
  4.4  0.418  0.802  0.909  0.07  0.67  0.46      cheb
  4.7  0.398  0.835  0.918  0.09  0.68  0.44      cheb
  4.1  0.395  0.873  0.919  0.15  0.64  0.51  learnedH
  3.0  0.385  0.860  0.923  0.11  0.67  0.48      cheb
  3.6  0.378  0.796  0.926  0.07  0.78  0.33      cheb
  3.5  0.375  0.778  0.927  0.07  0.76  0.35      cheb
  3.1  0.356  0.613  0.935  0.06  0.87  0.20      cheb   <- most content (highest sink_frac 0.87)
```

(`toepC`=toep_cos, `walkRF`=walk relFro fit, `oraRF`=Toeplitz oracle relFro
ceiling, `local`=mass on |i−j|≤2, `sink`=mass on token 0, `ent`=normalized row
entropy, `dom`=dominant fitted atom.)
