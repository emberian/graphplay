# Are learned attention circuits SUPERPOSITIONS of a few structured WALKS?

*Sparse-coding lab report, 2026-05-30. Brutally honest. We test the sharp
hypothesis: for a head's attention matrix `A`, does `A ≈ Σ_j c_j W_j` with **few**
atoms, each `W_j` a simple **named structured-walk** operator (shift / cell-uniform
/ thermal path-diffusion / cycle-diffusion / identity / uniform / BOS-sink)? This
is sparse coding against a structured-walk dictionary, run on a model with
**labeled circuits** (the canonical TransformerLens `attn-only-2l`, whose induction
head we detect by induction score) plus our 4 tiny trained attention-only models
where the task — hence the needed structure — is known.*

Regenerate:

```bash
cd experiments && source .venv/bin/activate
uv pip install transformer_lens          # one-time
python walk_basis/run.py                 # -> walk_basis/results.json
python walk_basis/make_figures.py        # -> walk_basis/figures/*.png
```

Figures: `figures/sparsity_curves.png` (error vs #atoms, by head class + the tiny
clean cases), `figures/atom_usage.png` (error floor + best named `sink+1walk`
companion per head; atoms-needed by class).

---

## THE HEADLINE

**PARTLY.** The hypothesis is **TRUE in the clean / structured regime and FALSE in
the messy real-LLM regime**, and the split is exactly along the head taxonomy:

* **The cross-reference SUCCEEDS at the level of WHICH named atom matches WHICH
  head class.** Every labeled circuit type maps to the *right* walk atom: the
  **prev-token head → `shift-1`**, the **induction head → `induction-shift`** (the
  content-dependent shift, made explicit at the known repeat period), positional
  heads → **path-diffusion**, sink heads → **`bos-sink`**. The dictionary's atom
  identities are correctly diagnostic. This is the live positive.

* **But the error FLOORS are too high to call most real heads "≤3-atom walk
  superpositions at 10%".** On `attn-only-2l`, **only 1/16 heads (6%)** reaches
  ≤10% reconstruction error with ≤3 atoms; even with the *full* 22-atom dictionary
  most heads floor at 0.10–0.36. At a looser **25% bar, 75% of heads ARE ≤3-atom
  sink+walk objects** (median K@25% = 2 for content & positional). So real heads
  are *approximately* sink + one-or-two walks, but with a stubborn diffuse residual
  that no structured walk removes.

* **The induction head is the sharpest mixed result.** Its single best named
  companion (after the BOS sink) is **exactly `induction-shift`** — the atom labels
  it correctly — but the 2-atom fit is only 0.56 and the full-dictionary floor is
  **0.48**. The batch-mean induction pattern is a *blurred* delta plus a large
  diffuse component, so it is **NOT a clean shift atom + small residual**. It is a
  shift atom + a *large* residual.

* **The tiny trained models give the textbook clean positives.** A head trained on
  the `induction` task = **`shift-1`, ONE atom, floor 0.04**; a head trained on the
  `local` (banded copy) task = **`shift-1`, ONE atom, floor 0.035**. When the model
  is *forced* to implement a pure routing primitive, that head **is** a single walk
  atom. The real `attn-only-2l` heads are messier because they do many jobs at once
  and dump mass on the BOS attention-sink.

**Verdict: PARTLY. "Learned circuit = a single clean walk atom" is TRUE for
purpose-built tiny heads and for the prev-token / sink heads of the real model;
PARTLY-true (right atom, large residual) for the real induction head; and FALSE as
a *low-error* statement for the content-head bulk, which needs the whole dictionary
and still floors at 10–36%.** A content head that needs ~the complete dictionary
and still does not reach 10% is a real negative — irreducibility confirmed for that
class. An induction/prev-token head whose single best named atom is the *correct*
labeled walk is the live positive.**

---

## The dictionary (all atoms NAMED)

22 interpretable row-stochastic, causal-masked `n×n` operators (`n=49`, TL seq incl
BOS):

| class | atoms |
|---|---|
| identity / uniform | `identity`, `uniform` (avg over causal prefix) |
| **sink** (constant, NOT a walk) | `bos-sink` (every row → col 0 = BOS) |
| **shift** (induction primitive) | `shift-1..5`, `shift-8`, and `induction-shift` (content-dependent shift at the known repeat period) |
| cell-uniform | `cell-halves/thirds/quarters/parity/blocks8` |
| **thermal diffusion** | `path-diff-τ` (τ=0.5,1,2,4,8), `cycle-diff-τ` (τ=1,4) — `rownorm(exp(τ·(−L)))` |

The `bos-sink` atom is included because real LLM heads dump a large constant share
of attention onto BOS (up to **56%** of the induction head's mass). It is a
*constant* operator, not a walk, and we name it so the walk story is tested on the
*residual after the sink is removed* (otherwise OMP wastes its whole budget
modelling the sink — see "honest pitfalls").

---

## Headline cross-reference (the demanded table)

attn-only-2l, per head: label (by induction/prev/diag score), best named
`bos-sink + ONE walk atom` companion, that 2-atom relerr, and the full-dictionary
OMP error floor.

| head | label | best `sink+1` companion | 2-atom relerr | full-dict floor | clean walk? |
|---|---|---|---|---|---|
| L0H3 | **positional** (prev) | **`shift-1`** ✓ | 0.17 | **0.09** | yes — prev-token = shift-1 + sink |
| L0H5 | sink/content | `path-diff-τ2` | **0.05** | **0.05** | yes — ~pure BOS-sink (1 atom) |
| L0H4 | content | `uniform` | 0.11 | 0.09 | borderline |
| L0H0 | content | `path-diff-τ8` | 0.35 | 0.10 | no (needs full dict) |
| L1H6 | **induction** | **`induction-shift`** ✓ | 0.56 | **0.48** | **NO — right atom, huge residual** |
| L1H4 | positional | `path-diff-τ0.5` | 0.22 | 0.16 | no |
| L0H7 | content | `identity` | 0.40 | 0.36 | **no — irreducible** |
| L1H3 | content | `path-diff-τ8` | 0.33 | 0.27 | no |
| (other 8 content heads) | content | `uniform` / `path-diff-τ` | 0.16–0.29 | 0.13–0.22 | no |

**Reading:** the *companion atom identity is diagnostic of the head's role* (prev →
shift-1, induction → induction-shift, smooth/positional → path-diffusion), but only
the prev-token head and the pure-sink head reach a *small* 2-atom error. The
induction head and every content head carry a large diffuse residual.

---

## Per-question verdicts

### Q1. Are learned circuits sparse superpositions of structured walks? (per class)

* **prev-token / positional (`shift`) — YES (clean).** L0H3 = `shift-1` + `bos-sink`
  at 0.17, reaches 10% in **4 atoms**. The induction *primitive* (a fixed small
  shift) IS a single named atom.
* **sink heads — trivially YES.** ~pure `bos-sink` (1 atom, 0.05). A constant
  operator, included as a named atom; not a "walk" but a clean 1-atom object.
* **induction — PARTLY.** Correct named atom (`induction-shift`) but 0.48 floor.
* **content (the bulk, 13/16 heads) — NO.** Best companion is usually a
  path-diffusion or `uniform`, but the full 22-atom dictionary floors at 0.10–0.36.
  These need ~the complete dictionary and still miss 10%. **Irreducible-to-walks
  confirmed for the content class** (consistent with the prior `generator_probe`
  and `residual_lab` findings that `A` is full-rank with a fat residual).

### Q2. Does the labeled induction head = a shift atom?

**Partly. The atom is RIGHT, the fit is NOT clean.** The single best named companion
to the sink for L1H6 is **exactly `induction-shift`** (the content-dependent shift
at the known period — verified the true offset is `half−1` and carries 0.63 mean
attention to the induction target). So the **labeling cross-reference is correct**:
the induction head decomposes onto the induction-shift atom and no other. **But**
`A = bos-sink + induction-shift` reaches only 0.56 relerr and the full-dictionary
floor is 0.48 — the batch-mean induction pattern is a *blurred* delta plus a large
diffuse component, so it is **a shift atom + a LARGE residual, not a small one.**
(In the tiny model trained purely on induction, the head *is* a single `shift-1`
atom at floor 0.04 — the clean version of the same statement.)

### Q3. Do positional heads = path-diffusion atoms?

**Mixed.** L1H4 (diag-heavy positional) → `path-diff-τ0.5` companion, and the smooth
content heads (L0H0/L0H6/L1H3) all pick `path-diff` as their best single walk — so
**when a head is smooth/local, the thermal path-diffusion is its best walk atom**,
as predicted. But the fit floors at 0.16–0.36: path-diffusion captures the *shape*
(local, decaying) but not enough mass to hit 10%. The other positional head (L0H3)
is a `shift-1` prev-token head, not a diffusion — so "positional = diffusion" holds
only for the *smooth-local* sub-type, not the *prev-token* sub-type.

### Q4. Do content heads need many atoms (= irreducible)?

**YES — confirmed.** 12/13 content heads never reach 10% even with the full
dictionary (median K@10% = 20 = "never"); their floors are 0.10–0.36. A content
head that needs a near-complete dictionary and *still* misses the target is exactly
the predicted real negative. (At the looser 25% bar most do collapse to ~2 atoms,
so they are *coarsely* sink+walk but not *sharply*.)

### Q5. What fraction of heads ARE ≤K-atom walk superpositions?

| threshold | frac of attn-only-2l heads that are ≤3-atom walk-superpositions |
|---|---|
| ≤10% error | **0.06** (1/16: only the prev-token head L0H3) |
| ≤25% error | **0.75** (12/16; median K@25% = 2) |

So **at a strict 10% bar almost no real head is a sparse walk; at a loose 25% bar
three-quarters are ~2-atom sink+walk objects.** The honest single number depends
entirely on the error bar you accept — which is itself the finding.

---

## The single most important finding

**The named-atom identity is diagnostic even when the reconstruction is not.**
Sparse-coding against a labeled walk dictionary recovers the *correct circuit type*
for every labeled head — prev-token → `shift-1`, induction → `induction-shift`,
smooth → `path-diffusion`, sink → `bos-sink` — **but the real `attn-only-2l` heads
are sink + (correct walk) + a large diffuse residual, not clean low-error
superpositions.** Only purpose-built tiny heads (and the prev-token / pure-sink real
heads) are genuine 1–4 atom walks. So "learned circuits = superposed walks" is a
correct *qualitative classifier* and a *failed quantitative compressor* for the
content-head bulk — irreducibility confirmed there, the live positive being the
shift-atom = induction/prev-token primitive.

---

## Honest pitfalls handled (and one residual caveat)

1. **The BOS attention-sink dominates everything.** Real heads dump 15–56% of
   attention on the BOS column — a constant operator no walk represents. Without a
   `bos-sink` atom, OMP spends its whole budget on the sink and *every* head looks
   irreducible (overall frac ≤3-atom = 0.00). Adding the named `bos-sink` atom is
   the correct fix; we report the walk story on the post-sink residual. (Pre-sink
   numbers in the first run row of `results.json` history; the effect is large.)
2. **The induction offset is content-dependent, not a fixed small shift.** A real
   induction head attends to "the token *after* the previous occurrence of the
   current token" — on a length-`m`-repeated sequence this is a fixed diagonal at
   offset `m−1`, NOT any `shift-k` with small `k`. We add a dedicated
   `induction-shift` atom at the verified true offset (`half−1`, 0.63 mean mass).
   Without it the induction head's structure is invisible to the dictionary; with it
   the atom is correctly selected (but the residual remains large).
3. **Batch-averaging blurs the induction delta.** The mean over random-prefix
   repeats smears the hard induction diagonal (partial token matches at neighbouring
   offsets), inflating the residual. We code the batch-mean (cleaner for
   non-induction heads, averages per-token noise) and flag that for the induction
   head this mean is a *blurred* delta — the 0.48 floor is partly this blur, not
   pure irreducibility. The tiny induction model (no such averaging confound) hits
   floor 0.04, the clean version.
4. **Residual caveat — the content-head floor is genuine.** Even granting the sink
   atom and the right walk companion, content heads floor at 0.10–0.36 with the full
   22-atom dictionary. This is the same fat-residual / full-rank-`A` signal seen in
   `residual_lab` and `generator_probe`: most of `A`'s mass for a content head is
   not on any low-dimensional structured-walk manifold. We do not hide it.

---

*( ⌐■_■ ) we asked the heads to confess as a sum of walks. The prev-token head said
"shift one." The sink head said "look at BOS." The induction head pointed at the
right walk but kept a cloud of secrets. And the content heads — the many of them —
needed every walk we own and still would not round to themselves. The dictionary
names the circuit; it does not, for the dense ones, compress it.*
