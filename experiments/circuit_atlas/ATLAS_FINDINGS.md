# Circuit Atlas — classifying every attention head of a production LLM by its dominant structured-walk atom

*ML-experiments lab report, 2026-05-30. Honest. We take the walk-basis circuit
DIAGNOSTIC — validated in `experiments/walk_basis/` on the labeled toy
`attn-only-2l` — and scale it to a REAL production LLM. For every (layer, head) we
extract the attention pattern, encode the BOS attention-sink first, sparse-code the
residual against the named structured-walk dictionary, and assign each head a
CIRCUIT-TYPE label = its dominant named atom. The output is a CIRCUIT ATLAS: a
layer×head map of what kind of routing primitive each head implements.*

## Model actually used

**`HuggingFaceTB/SmolLM3-3B`** — the first-choice model loaded and ran fine on CPU
(fp32, eager attention, `output_attentions=True`). No fallback needed.

* 36 layers × 16 attention heads = **576 heads** classified.
* GQA: 4 KV-heads, group size 4 (each KV-head shared by 4 query heads). HF
  `output_attentions` materializes all 16 query-head patterns, so every (L,H) is a
  genuine query-head pattern; KV-group boundaries are drawn as white separators on
  the atlas (heads within a group share K/V but learn distinct query projections,
  and indeed do not collapse to identical types).
* **No BOS token** (`tokenizer.bos_token_id is None`) — SmolLM3 does not prepend
  BOS. The "sink" is therefore an attention sink on **column 0 = the first real
  token**, the well-documented Llama/SmolLM register-token behaviour. The
  `bos-sink` atom captures it regardless (it is just "every row → fixed column 0").

### Compute limits (honest)

CPU only. Two forward passes total: a 6-sequence repeated-random-token batch
(period 40, T=80) to activate induction heads, and a 3-prompt natural-text batch
(T=96). Attention averaged within each batch. This is a *few-shot* atlas — the
broad structure is robust, but per-head labels on borderline heads would move with
more prompts. We did not sweep prompts or seeds; the qualitative atlas is the
deliverable, not a tight per-head confidence interval.

## Reproduce

```bash
cd experiments && source .venv/bin/activate
python circuit_atlas/atlas.py          # -> circuit_atlas/results.json
python circuit_atlas/make_figures.py   # -> circuit_atlas/figures/*.png
```

## Headline figure

`figures/atlas_heatmap.png` — the 36×16 layer×head grid, each cell colored by
circuit type. Companions: `figures/type_distribution.png` (overall counts + the
per-layer stacked composition), `figures/residual_heatmap.png` (per-head OMP error
floor = irreducibility), `figures/score_maps.png` (raw induction / prev-token /
sink scores).

---

## THE HEADLINE

**The walk-basis diagnostic produces a genuinely interpretable, sensible circuit
atlas of a 3B production LLM — and it independently rediscovers the textbook
transformer head taxonomy in the textbook places.** Without ever being told layer
indices or head roles, sparse-coding each head against the named walk dictionary
recovers:

* an **attention-sink phase transition** between layer 1 and layer 2,
* a **prev-token / positional early phase**,
* a **mid-to-late induction band**, and
* a **content / output final layer**,

each landing exactly where mechanistic-interpretability work on Llama-family models
says it should. The diagnostic is **real at scale.**

## Circuit-type distribution (576 heads)

| circuit type | atom | count | fraction |
|---|---|---:|---:|
| **sink** | `bos-sink` (col-0 attention sink) | 300 | **52%** |
| **positional** | `path-diffusion` / `uniform` / `identity` | 170 | **30%** |
| **content / irreducible** | (no structured atom fits) | 65 | **11%** |
| **induction** | `induction-shift` (content-dependent period offset) | 31 | **5%** |
| **prev-token** | `shift-1` | 10 | **2%** |

So **89% of heads get a clean named walk-atom circuit label; only 11% are
content/irreducible.** (That 89% is the "what is the dominant atom" number; how
*tight* the reconstruction is varies — see the residual section.)

---

## SANITY CHECKS — does the diagnostic produce something real?

All four canonical phenomena are detected, in the expected layers:

### 1. Attention sinks — detected, and the sink PHASE TRANSITION is visible

* **Layers 0–1: ZERO sink heads** (mean col-0 mass ≈ 0.04–0.05). The sink does not
  exist yet.
* **Layer 2 onward: the sink switches on hard** — mean col-0 mass jumps to **0.72**
  and stays 0.5–0.9 for the rest of the network; 300/576 heads are sink-dominated.
* This abrupt L1→L2 onset is exactly the documented Llama/Mistral/SmolLM "attention
  sink forms after the first block" behaviour. The diagnostic finds it with no
  hand-holding — it is the single most visible feature of the atlas (the grey flood
  from row 2 down).

### 2. Induction heads — detected, in the classic MIDDLE-TO-LATE layers

* 31 induction heads, in layers **{7, 12, 13, 15, 18, 19, 22, 23, 26, 27, 28, 31,
  35}** — clustered in the mid-to-late network, with a dense band at **L18–L31**.
  Induction heads being a mid-network phenomenon (after a prev-token head in an
  earlier layer has run) is the textbook two-layer induction-circuit story; the
  atlas reproduces it (prev-token heads in L1–L16, induction heads peaking
  L22–L31).
* Per-head induction scores are strong and real: top heads reach **0.93** (L23H9),
  0.78, 0.76 attention onto the induction target — these are unambiguous induction
  heads, not noise.

### 3. Positional / shift heads — cluster EARLY, as predicted

* **Layers 0–1 are almost entirely positional** (25/32 of those head-slots) and
  carry **no sink at all** — early layers do local/positional mixing before the
  sink and the higher-order circuits form. The positional class is dominated by
  `path-diffusion` (the thermal local-decay walk) and `uniform` atoms, exactly the
  smooth-local shapes the validated diagnostic maps to "positional".
* **prev-token (`shift-1`) heads** appear in layers {1, 5, 6, 8, 10, 12, 16, 22} —
  early-to-mid, upstream of the induction band, with the strongest one (L1H13, prev
  score 0.69) in layer 1. Prev-token-before-induction is the canonical ordering.

### 4. Final layer goes CONTENT

* **Layer 35: 15/16 content, sink collapses to 0.04.** The last layer abandons
  structural routing and does input-specific output computation — sensible and
  consistent with "late layers are task/content heads".

**Verdict on sanity: the atlas matches known LLM phenomenology on every axis —
sink onset, induction band, early positional, content final layer. The diagnostic
is producing something real, not an artifact.**

---

## HONEST verdict — clean label vs content/irreducible

There are two honest numbers, and the gap between them IS the finding (same split
as the validated toy-model report):

| bar | fraction of heads |
|---|---|
| gets a **clean named circuit-type label** (dominant atom identified, not content) | **89%** (511/576) |
| label backed by a **tight reconstruction** (OMP error floor ≤ 0.10) | **32%** (182/576) |
| label backed by a **loose reconstruction** (floor ≤ 0.25) | **78%** (450/576) |
| **content / irreducible** (no structured atom fits at all) | **11%** (65/576) |

**Reading.** The diagnostic is an excellent *qualitative classifier* and a *partial
quantitative compressor* — exactly as the walk-basis report predicted, now confirmed
at 3B scale:

* **Sink heads are clean** — 300 of them, mean error floor **0.09**. A sink head
  really is ≈ one constant `bos-sink` atom plus small noise. This is the bulk of the
  32% tight-fit heads.
* **prev-token heads are clean** — `shift-1` + sink, floors 0.09–0.22.
* **positional heads are loosely clean** — `path-diffusion`/`uniform` capture the
  *shape* (local, decaying, or prefix-average) but leave a diffuse residual; most
  land in the 0.10–0.25 band, not below 0.10.
* **induction heads are the validated "RIGHT ATOM, LARGE RESIDUAL" case** — every
  one of the 31 selects `induction-shift` as its dominant non-sink walk (the atom
  identity is correct and diagnostic), but the mean error floor is **0.37** (range
  0.18–0.61). The batch-mean induction pattern is a blurred delta plus a genuine
  diffuse cloud, so the reconstruction is loose even though the *label* is right.
  **We deliberately label these "induction" on atom identity, not on reconstruction
  error** — this is the load-bearing pitfall from the toy-model report (the named
  atom is diagnostic even when the fit is not), applied honestly at scale. With a
  strict floor≤0.30 gate these heads fall into "content"; that is why a naive gate
  *under*-counts induction (we found 14 induction heads under the strict gate vs 31
  with the atom-identity rule, and the strongest induction head of all, L23H9 at
  ind-score 0.93, has a floor of ~0.5 — pure-error gating would have thrown the best
  induction head into the content bin).
* **The 11% content bin is genuinely irreducible** — mean floor **0.42**, no
  structured walk gets close. This is the same fat-residual / full-rank-attention
  signal seen in the toy model: a real fraction of heads do dense, content-specific
  routing that no low-dimensional structured walk represents. We do not hide it.

So: **does the walk-basis diagnostic produce an interpretable, sensible atlas of a
production model? YES — 89% of heads receive a sensible named circuit type and the
atlas reproduces known structure in the right layers. Is it a tight compressor?
Only for ~a third (the sinks + prev-token heads); positional and induction heads
get the right label but carry a diffuse residual; 11% are honestly irreducible.**

---

## The single most striking thing in the atlas

**The attention-sink phase transition between layer 1 and layer 2 is the loudest,
cleanest feature — the diagnostic discovers it from scratch.** Layers 0–1 carry
*zero* sink mass (mean col-0 attention ≈ 0.04) and are wall-to-wall positional;
then at layer 2 the col-0 sink turns on across the board (mean ≈ 0.72) and stays on
for 33 layers until it switches *off* again in the final layer 35 (≈ 0.04, which
flips to all-content). On the heatmap this is unmistakable: two green/yellow rows on
top, a grey ocean of sinks in the middle with a red induction band running through
the late layers, and one yellow content row at the bottom. A sparse-coding
diagnostic built and validated on a 2-layer toy model, pointed at a 3-billion-
parameter model it had never seen, drew the textbook anatomy of a transformer.

---

## Pitfalls handled (carried over from the validated toy-model run)

1. **The BOS / col-0 attention sink dominates everything.** 52% of heads are
   sink-dominated (up to 0.89 mass). The `bos-sink` atom is encoded first; without
   it OMP burns its whole budget on the sink and every head looks irreducible. Note
   SmolLM3 has *no* BOS token — the sink is on the first real token (col 0), and the
   atom captures it identically.
2. **The induction offset is content-dependent, not a fixed small shift.** On a
   period-40 repeated sequence the induction target sits at offset `period−1`, not
   any `shift-k`. We add the dedicated `induction-shift` atom at the known period;
   it is correctly selected by all 31 induction heads. Without it the induction
   structure is invisible to the dictionary.
3. **Batch-averaging blurs the induction delta → large residual.** We label
   induction heads on *atom identity* (induction-shift is their dominant walk) plus
   a real induction score (≥0.15), NOT on reconstruction error, precisely because
   the mean pattern is a blurred delta. Gating on error alone mislabels the
   strongest induction heads as "content".
4. **GQA pattern sharing.** KV-heads are shared 4:1, but query projections differ;
   heads within a KV-group do not collapse to one type. We mark group boundaries on
   the atlas rather than dedup, so the map shows real per-query-head structure.

---

*( ⌐■_■ ) we handed a three-billion-parameter model the same little dictionary of
walks and asked every one of its 576 heads what it does. Five hundred of them said
"I look at the first token." A hundred and seventy said "I diffuse over what's
near." Thirty-one pointed back across the sequence to the token after the last time
they saw this one — the induction reflex — and ten just said "the one before."
Sixty-five kept their own counsel. And when we drew the answers on a grid, the grid
was a transformer: positional at the top, a sea of sinks, a band of induction in
the deep layers, content at the very end. The dictionary names the circuit. At
scale, it draws the map.*
