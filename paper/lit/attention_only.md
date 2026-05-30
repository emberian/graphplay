# Attention-Only Networks: A Clean Testbed for the Equitable-Partition / Quotient / Irreducibility Framework

*Literature scout, 2026-05-30. Purpose: identify attention-only (no-MLP / attention-dominant) architectures where the attention operator IS the whole computation, so our equitable-partition / quotient / spectral irreducibility-meter analysis applies to the entire model with no MLP confound.*

## Why attention-only models are the cleanest testbed for us

In a standard transformer block the residual stream is updated by `x <- x + Attn(x)` and then `x <- x + MLP(x)`. Our framework analyses the **attention operator** — the token-mixing map `A(x) = softmax(QK^T/√d) V` (or a linear-attention surrogate) — as a (data-dependent, row-stochastic) operator on the token graph, and asks: what is its equitable partition, what is the quotient, and does the residual coordinate (the irreducibility-meter readout) predict performance/failure?

The MLP is a confound for exactly this reason: it is a per-token nonlinear map that does *not* mix tokens, so it is invisible to a token-graph / equitable-partition lens but contributes most of the FLOPs and a large share of the model's computation. In an **attention-only network the MLP is removed entirely**, so:

- the attention operators are the *entire* computation (modulo embedding, unembedding, LayerNorm, skip connections);
- our quotient/equitable-partition statement is a statement about the whole model, not a fragment;
- the explanatory experiment — "does the residual coordinate / spectral irreducibility readout predict the model's behavior?" — is uncontaminated;
- this is *exactly* why mechanistic-interpretability circuit work (Elhage et al.; Olsson et al.) uses attention-only models: with no MLP, the QK and OV circuits are fully readable from the weights.

## Architectures and results found

### A. The mech-interp / circuits lineage (small, open, fully analyzable — our primary targets)

1. **Elhage, Nanda, Olsson et al., "A Mathematical Framework for Transformer Circuits" (Anthropic, 2021).**
   `refs/ml-theory/elhage2021_mathematical_framework_transformer_circuits.pdf` (= `anthropic2021_..._.pdf`, duplicate).
   The foundational attention-only analysis. They deliberately study **zero-, one-, and two-layer attention-only transformers (no MLP)** to isolate mechanism. Key structure that maps onto our framework:
   - Each head factors into a **QK circuit** (computes the attention pattern = the data-dependent token-mixing operator — *this is literally our operator on the token graph*) and an **OV circuit** (how an attended token writes to the residual stream).
   - 0-layer = bigram statistics; 1-layer = ensemble of bigram + **skip-trigram** ("A … B C") models; 2-layer = **induction heads** via Q/K/V-**composition** ("virtual attention heads").
   - The QK circuit is exactly the object whose row-stochastic structure / equitable partition we want to characterize; composition = products of operators across layers = the quotient/structure we should be able to read spectrally.
   **Why clean for us:** no MLP, weights small enough to compute the operator and its equitable partition in closed form. This is the canonical reference to cite for "the attention operators are the whole model."

2. **Olsson, Elhage, Nanda et al., "In-context Learning and Induction Heads" (Anthropic, 2022).** arXiv:2209.11895.
   `refs/ml-theory/olsson2022_induction_heads_icl.pdf` (= `induction_heads_2022.pdf`, dup).
   Shows induction heads (the 2-layer attention-only mechanism) are the engine of in-context learning, with a phase-change signature. ICL = a structured token-mixing pattern (attend to the token *after* the previous copy of the current token). This pattern has a very specific, near-permutation/shift structure — a sharp test case for whether our equitable-partition/quotient readout detects it.

3. **"Which Attention Heads Matter for In-Context Learning?" (2025).** arXiv:2502.14010.
   `refs/ml-theory/which_attention_heads_icl_2025.pdf` (= `which_attention_heads_matter_icl_2025.pdf`, dup).
   Distinguishes induction heads vs. function-vector heads; gives a head-level importance ranking. Useful as a *ground-truth* labeling of "which operators carry the computation," against which our irreducibility-meter / residual-coordinate predictor can be validated.

4. **Supporting circuit case studies (already in repo):** `attention_heads_survey_2024.pdf` (taxonomy of head roles), `ioi_path_patching_2211.00593.pdf` (IOI circuit), `acdc_2304.14997.pdf`, `attribution_patching_2310.10348.pdf`, `activation_patching_bestpractices_2404.15255.pdf`. These give the standard causal-ablation toolkit we can compare our spectral predictor against. The classic 4-layer attention-only "docstring circuit" (Heimersheim & Janiak, LessWrong 2022) is another fully-worked attention-only example to reproduce.

### B. Attention-only as a *competitive* architecture (the "surprisingly good" recent results)

5. **Wang, Lu, ... "Attention-Only Transformers via Unrolled Subspace Denoising" (ICML 2025).** arXiv:2506.03790.
   `refs/ml-theory/attention_only_unrolled_subspace_denoising_2025.pdf`.
   The strongest recent "attention-only actually works" result. Architecture = **only self-attention operators + skip connections, MLP removed entirely (AoT)**. They derive attention as *iterative denoising toward a mixture of low-dimensional subspaces*, and report performance **close to GPT-2 and CRATE** on vision and language. Crucially for us: they avoid rank collapse not with an MLP but through the **subspace-denoising structure of the attention operator itself** — i.e. the operator is engineered to have a specific invariant-subspace / spectral structure. This is a direct, mathematically-principled instance of the very thing our spectral/equitable lens characterizes; their "low-dimensional subspaces" are candidate quotient blocks.

6. **"Attention-Only Transformers and Implementing MLPs with Attention Heads" (2023).** arXiv:2309.08593.
   `refs/ml-theory/mlps_with_attention_heads_2023.pdf` (= `attention_only_implementing_mlps.pdf`, dup).
   Proves attention heads (with a masked/extra "memory" token construction) can *implement* an MLP — i.e. attention-only is universal in a precise sense. Important for honesty: "attention-only" is not a weaker model class in expressivity terms; the MLP confound is about *typical learned* behavior, not a capability ceiling. Relevant when we claim our analysis covers "the whole computation."

### C. The honest caveat literature (rank collapse — itself a target for our lens)

7. **Dong, Cordonnier, Loukas, "Attention is Not All You Need: Pure Attention Loses Rank Doubly Exponentially with Depth" (ICML 2021).** arXiv:2103.03404.
   `refs/ml-theory/dong2021_pure_attention_rank_collapse.pdf` (= `rank_collapse_2103.03404.pdf`, dup).
   **The key caveat.** Without skip connections AND without MLPs, the output of a pure deep self-attention stack converges *doubly-exponentially* to a rank-1 matrix (all tokens collapse to the same vector). They show skip connections and MLPs are precisely the two forces that counteract this. So a *naive* deep attention-only stack degenerates.

8. **"Why Attention Fails: The Degeneration of Transformers into MLPs in In-Context Learning" (2025).** arXiv:2509.20942.
   `refs/ml-theory/why_attention_fails_degeneration_2025.pdf` (dup). Complementary failure mode.

9. **"The Importance of Feedforward Networks in Transformer Models" (2025).** arXiv:2505.06633.
   `refs/ml-theory/importance_of_ffn_2025.pdf`. The counter-case for why MLPs matter; sets the bar our attention-only story must clear.

Related already-in-repo: `transformer_vs_mlpmixer_expressivity_gap.pdf`, `toy_models_superposition_2022.pdf`.

### Why the rank-collapse caveat is a feature, not a bug, for us

Rank collapse (Dong et al.) is **the cleanest possible phenomenon for a spectral/equitable lens**: it is literally a statement about the spectrum of a product of row-stochastic attention operators collapsing onto the all-ones (rank-1) eigenvector. An equitable partition / quotient analysis predicts exactly this — the trivial equitable partition (one block = "all tokens equivalent") is the fixed point, and the *gap to that fixed point* is what the irreducibility-meter should measure. The two known antidotes — **skip connections** and **MLPs** — are exactly the terms that break the row-stochasticity / push mass off the rank-1 mode. So:

- our framework should *predict the rate* of collapse from the operator spectrum (doubly-exponential = repeated squaring of a contraction toward the Perron eigenvector);
- the residual coordinate / irreducibility readout should *anticipate* degeneration before task accuracy drops;
- AoT (paper #5) is the constructive flip side: it engineers the operator's invariant-subspace structure to keep the partition non-trivial — a concrete "our quotient stays non-degenerate" success case to characterize.

This turns the caveat into a quantitative prediction the framework can be evaluated on.

## Recommended first experiments (concrete)

**Primary testbed — small attention-only mech-interp models (run our probe here first):**
- A **2-layer attention-only transformer** in the Elhage/Olsson sense, trained on a small corpus (or use TransformerLens / `redwoodresearch/Easy-Transformer` pretrained `attn-only-2l`). These are tiny (≈ a few M params), fully open, and the QK operator can be extracted per layer/head and turned directly into our token-graph operator. Run: (a) compute the attention operator on held-out sequences, (b) compute its equitable partition / quotient, (c) test whether the residual-coordinate / irreducibility readout flags induction-head behavior and predicts ICL accuracy. Ground truth for "which operators matter" comes from paper #3 and the path-patching toolkit (#4).
- Stretch within the same family: the **4-layer attention-only docstring circuit** model — a slightly richer fully-attention-only model with a known circuit to check our readout against.

**Secondary testbed — competitive attention-only at scale:**
- **AoT (paper #5, arXiv:2506.03790)** if code is released (CRATE/AoT line from the Ma/Yu group typically open-sources). Here the experiment is the *constructive* one: verify that the engineered low-dim-subspace structure shows up as a stable non-trivial quotient in our analysis, and that depth-wise the operator's spectral gap behaves as their denoising-rate theory predicts (contrast with naive pure-attention rank collapse, paper #7).

**Validation against the caveat:**
- Take a pure attention-only stack *without* skip connections, increase depth, and confirm our irreducibility-meter tracks the doubly-exponential collapse predicted by Dong et al. (#7) — a falsifiable quantitative test of the framework on a phenomenon with a known closed-form rate.

Start with the **2-layer attention-only TransformerLens model**: smallest, fully open, weights → operator is trivial, and it has a crisp, well-documented target behavior (induction / ICL) with independent ground-truth labels.

## Files downloaded this session (refs/ml-theory/)
- `dong2021_pure_attention_rank_collapse.pdf` — arXiv:2103.03404 (the caveat) [1.6 MB]
- `mlps_with_attention_heads_2023.pdf` — arXiv:2309.08593 (attention-only universality) [188 KB]
- `olsson2022_induction_heads_icl.pdf` — arXiv:2209.11895 (induction heads / ICL) [10 MB]
- `which_attention_heads_icl_2025.pdf` — arXiv:2502.14010 [1.4 MB]
- `importance_of_ffn_2025.pdf` — arXiv:2505.06633 (why MLPs matter) [283 KB]
- `why_attention_fails_degeneration_2025.pdf` — arXiv:2509.20942 [1.8 MB]
- `attention_only_unrolled_subspace_denoising_2025.pdf` — arXiv:2506.03790 (AoT, competitive attention-only) [3.6 MB]
- `elhage2021_mathematical_framework_transformer_circuits.pdf` — Anthropic 2021 framework [4.8 MB]

(Several were de-duplicated against pre-existing copies already in the folder, e.g. `rank_collapse_2103.03404.pdf`, `anthropic2021_..._.pdf`, `induction_heads_2022.pdf`, `attention_only_implementing_mlps.pdf`, `which_attention_heads_matter_icl_2025.pdf` — same papers, harmless duplicates.)
