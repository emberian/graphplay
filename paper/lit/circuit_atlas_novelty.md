# Circuit Atlas — Novelty Scan

**Construction under scrutiny.** A fixed, hand-named *dictionary* of canonical structured "walk"
operators — shift-k (prev-token), induction-shift, cell-uniform/averaging, path/cycle-diffusion
(CTQW / heat-kernel style), BOS/attention-sink atom — against which each attention head's pattern
matrix `A` is **sparse-coded** (OMP/LASSO). The *dominant named atom* is taken as the head's
circuit-type label. Run on SmolLM3-3B (all 576 heads, no training, no labels), it recovers known
transformer anatomy: sink phase transition ~L2, induction band mid-late, positional/prev-token
early, content heads late.

**Scope of the claim being checked.** NOT the phenomena (all known — see below). The method:
*fixed-walk-operator dictionary + sparse-coding-as-circuit-classifier, used as a diagnostic basis
that reproduces layer anatomy.*

---

## VERDICT (blunt)

**PARTLY-NOVEL.**

- The **individual ingredients are all prior art**: (a) named canonical attention templates exist
  and are matched to heads (TransformerLens `head_detector`); (b) classifying/embedding heads by
  their pattern is done (Attention Motifs); (c) sparse coding of attention internals for interp is
  done (Attention-Output SAEs, sparse attention decomposition). The recovered anatomy
  (sink@L2, induction band, prev-token early, content late) is textbook.
- The **specific combination is, as far as this scan found, not previously published**: a
  *single fixed over-complete dictionary of analytically-defined operators* (shifts + **diffusion /
  CTQW / heat-kernel atoms** + sink) used with **OMP/LASSO sparse coding** to assign each head a
  *dominant-atom circuit label*, validated by recovering the full layer profile across an entire
  modern LLM. No single prior work does the whole pipeline.
- The genuinely distinctive bit is the **walk/diffusion/heat-kernel atoms as interpretability
  basis functions** — nobody in the interp literature appears to use CTQW/graph-diffusion operators
  as a dictionary for *classifying* heads. (Diffusion/heat-kernel attention papers exist, but they
  *replace softmax in the architecture*, not interpret a trained model's heads.)

So: the *frame* ("a structured-operator dictionary is a diagnostic basis for circuit type") is a
fresh and clean recombination, but it is incremental over `head_detector` (which already does fixed
canonical-template matching for prev-token/dup/induction) and Attention Motifs (which already
systematically categorizes heads by pattern and finds layer structure). Don't oversell it as a new
*discovery*; sell it as a new *lens / unifying method*.

**Single closest prior work:** TransformerLens `head_detector`
(Nanda et al., jbloomaus.github.io/TransformerLens/.../head_detector.html) — it already does
fixed-template matching of head pattern matrices against canonical detection patterns
(`previous_token_head`, `duplicate_token_head`, `induction_head`) with an element-wise "mul" score
("how big a fraction of this head's attention lands on these query-key pairs"). Your method is
literally a generalization of this: bigger dictionary (adds diffusion/CTQW + sink atoms), continuous
sparse-coding (OMP/LASSO) instead of one-template-at-a-time scoring, and a dominant-atom label. This
is the work a reviewer will hit you with first; cite it as the direct ancestor.

---

## Closest prior art, per angle

### 1. Head taxonomy / function categorization
- **Zheng et al., "Attention Heads of Large Language Models: A Survey," arXiv 2409.03752**
  (+ Cell *Patterns* 2025; IAAR-Shanghai/Awesome-Attention-Heads). The canonical taxonomy of head
  *functions*. This is the reference set of "circuit types" you are predicting. It is a
  *survey/taxonomy*, not a single-basis classifier — so it establishes the target labels, not the
  method. Cite as: "the function taxonomy we recover against."

### 2. Clustering / categorizing heads BY PATTERN  — **(this is competitor #2)**
- **"Motifs in Attention Patterns of Large Language Models"** (attention-motifs.github.io;
  OpenReview ND2WsCwlDQ). Explicitly: "little work addressing ways to systematically analyze or
  categorize attention heads using the patterns they produce" → they build an **embedding of
  attention patterns**, embed heads in it, and analyze structure. This is the closest work on
  *systematic, pattern-based head categorization across a model.* KEY DIFFERENCE: their embedding is
  **learned / data-driven (a latent space)**, NOT a fixed hand-named operator dictionary, and the
  axes are not analytically interpretable named atoms. Your contribution vs. theirs: the basis is
  *fixed, named, and analytic* (each axis already means "prev-token" / "diffusion-on-a-path" /
  "sink"), so you get a label for free without post-hoc cluster naming. State this difference
  explicitly — it is your main delta over Motifs.
- (PDF couldn't be machine-read in this scan; the abstract/site text above is the load-bearing
  evidence. Worth a careful human read of their method section before posting, to confirm they don't
  also use a fixed dictionary.)

### 3. Fixed canonical-template matching of heads  — **(competitor #1, the direct ancestor)**
- **TransformerLens `head_detector`** (Nanda et al.). Fixed 0/1 detection patterns for
  prev-token / duplicate / induction; "mul" score = fraction of head attention on the template's
  query-key pairs. This already IS "fit a head to a fixed named canonical operator and score it."
  Your generalizations over it: (i) richer dictionary incl. **diffusion/CTQW + sink**; (ii)
  **sparse coding (OMP/LASSO)** over the whole dictionary rather than per-template scoring;
  (iii) **dominant-atom labeling + whole-model layer-profile recovery**. Honest framing: "we
  generalize TransformerLens head-detection from a few hard templates to an over-complete
  structured-operator dictionary with sparse coding."

### 4. Dictionary learning / sparse coding of attention
- **Kissane et al., "Interpreting Attention Layer Outputs with Sparse Autoencoders," arXiv
  2406.17759** (+ LessWrong "Attention Output SAEs"). Sparse decomposition for attention interp —
  BUT on attention *output activations*, with a **learned** dictionary, to find *features*, not on
  the *pattern matrix A* with a *fixed* dictionary to find *circuit type*. Different object
  (outputs vs. pattern), different dictionary (learned vs. fixed/named), different goal
  (features vs. head-type label). Good to cite as the "sparse-coding-in-interp" lineage you depart
  from.
- **"Sparse Attention Decomposition Applied to Circuit Tracing," arXiv 2410.00340** — sparse
  encoding via attention-head *singular vectors* for circuit tracing. Closer in spirit (sparse +
  circuits) but the basis is the head's own SVD, not a fixed shared operator dictionary.
- "Learning Dictionary for Visual Attention" (NeurIPS 2023, Dic-Attn) and "From Attention to Atoms:
  Spectral Dictionary Learning" (2505.00033) — both *build architectures* with learned dictionaries;
  not interpretation of a trained model's heads. Not real competitors, but name-collision risk
  ("dictionary" + "atoms" + "attention"); distinguish yourself in one sentence.

### 5. Phenomena you recover (ALL KNOWN — credit, don't claim)
- **Attention sink:** Xiao et al., "Efficient Streaming Language Models with Attention Sinks"
  (StreamingLLM), arXiv 2309.17453 — sink on initial tokens. Phase-transition / emergence-at-a-layer
  framing is established. CREDIT, do not claim discovery.
- **Induction heads & prev-token heads:** Elhage et al. "A Mathematical Framework for Transformer
  Circuits" (transformer-circuits.pub 2021); Olsson et al. "In-context Learning and Induction
  Heads" (transformer-circuits.pub 2022). CREDIT.
- **Layer anatomy (positional early → content late):** folklore + the survey (2409.03752) +
  "Decoupling Positional and Symbolic Attention Behavior," 2511.11579. CREDIT.

### 6. Quantum-walk / heat-kernel operators as an interpretability basis — **(your distinctive bit)**
- **No prior interpretability work found** that uses CTQW / quantum-walk / graph-heat-kernel
  operators as a *diagnostic basis to classify trained attention heads.* This scan's most
  novelty-positive result.
- Adjacent-but-different (architectural, not interpretive): "Diffusion Attention: Replacing Softmax
  with Heat Kernel Dynamics" (SSRN 5953096 / JDCurry repo); MeshFormer HDMSA (CVPR 2023);
  "Quantum-Enhanced Attention Mechanism in NLP," 2501.15630. These put diffusion/quantum effects
  *into the model*; you use those operators to *read out* an existing model. Different use entirely
  — cite to preempt "isn't this just heat-kernel attention?" and clarify the distinction.
- Mild conceptual cousin: "Symmetric/skew decomposition of QK as associative memory" (2605.27476)
  and "Sink vs. diagonal patterns" (2605.08453) — analytic decompositions of attention matrices,
  but not a named-operator dictionary nor a classifier.

---

## Recommended HONEST framing for a public post

**Lead with the method, not the phenomena.** The phenomena (sink@L2, induction band, prev-token
early) are known and you must say so up front — the post's credibility depends on crediting Elhage,
Olsson, Xiao, and the head survey explicitly and early.

**Claim this (defensible):**
> *We define a fixed, analytic dictionary of canonical "walk" operators — shifts, diffusion/CTQW
> heat-kernels, and a sink atom — and sparse-code every attention head against it. The
> dominant atom gives each head an interpretable circuit-type label with no training and no
> probing, and across all 576 heads of SmolLM3-3B this single fixed basis reproduces the known
> layer anatomy. It generalizes TransformerLens head-detection from a few hard templates to a
> structured-operator basis, and is the first to use graph-diffusion / quantum-walk operators as
> an interpretability dictionary.*

**One-sentence version that IS defensible:**
> *A fixed dictionary of analytic walk/diffusion operators, sparse-coded against each attention
> head, acts as a training-free diagnostic basis that labels head circuit-type and recovers the
> known transformer layer anatomy across an entire 3B model — generalizing canonical-template head
> detection to an over-complete structured-operator basis.*

**Do NOT claim:**
- discovery of sinks / induction / prev-token / layer anatomy (all prior; credit them);
- that you're the first to classify heads by their pattern (Motifs; head_detector);
- that you're the first to sparse-code attention for interp (Attention SAEs);
- tight reconstruction / compression — you already hold the honest caveat that this is a
  **classifier (dominant-atom identity), not a faithful reconstructor/compressor.** Keep that caveat
  visible; it also defends you against "your dictionary doesn't actually fit A well" pushback.

**Credit prominently:** Elhage et al. (math framework), Olsson et al. (induction heads),
Xiao et al. (attention sinks / StreamingLLM), Zheng et al. survey (head taxonomy),
TransformerLens `head_detector` (direct methodological ancestor), Attention Motifs (closest
pattern-categorization peer), Kissane et al. Attention SAEs (sparse-coding-for-interp lineage).

**Mandatory caveats to bake in (so it reads as honest, not hype):**
1. It's a classifier, not a reconstructor (you hold this already).
2. Heads are polysemantic — Kissane et al. estimate ≥90% of GPT-2-small heads are polysemantic, so a
   single dominant atom is a *summary*, not the whole story.
3. Pattern-matching ≠ causal role — "MHC Interp" (LessWrong) shows ablation/path-patching can
   disagree with pattern-based prev-token labels. Validating dominant-atom labels against ablation
   would materially strengthen the claim; flag it as future work or do a spot-check.

**Net:** a clean, honest "new lens" post — not a "we discovered X" post. The walk/diffusion atoms
are your real signature; lean on them.

---

*Sources via Kagi search (May 2026). Closest two competitors — TransformerLens `head_detector`
and "Motifs in Attention Patterns" — should be read in full by a human before the post goes out;
the Motifs PDF could not be machine-parsed in this scan and its method section deserves a direct
confirmation that it uses a learned (not fixed/named) basis.*
