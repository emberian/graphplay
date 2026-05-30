# Equivariant / Structured-Attention Targets for the Equitable-Partition Attention Reduction

**Scope.** Graphplay's `Graphplay/Integrations/AttentionComplexity.lean` proves an **exact**
`O(n²·d) → O(n·r·d)` collapse of self-attention whenever the score matrix is *cell-constant*:
`A[i][j] = B[cell i][cell j]`, where `cell : Fin n → Fin r` is an equitable partition of the
token graph. The collapse is *exact* and *correct* (proven, sorry-free:
`blockAttentionApply_eq_fullAttentionApply`), and both forward and backward stay linear in `n`
under a *maintained* (by-construction equivariant) cell structure
(`training_step_linear_under_equitable`). The companion bridge
`Graphplay/Integrations/MachineLearning.lean` supplies the symmetry→equitable direction
(`equitableOfAutomorphism`, `multiHead_restrict_eq_symmQuotient`).

This document maps real-world architectures onto **which of four reduction axes** the
Graphplay machinery fires on:

| axis | what is cell-constant | `cell` map | `r` = | where in Lean |
|---|---|---|---|---|
| **token-cell** | `A[i][j]` constant on token-orbit pairs (vertex partition of the token graph) | tokens → orbit | #orbits | `equitableOfAutomorphism`, `blockAttentionApply` |
| **banded / Toeplitz** | `A[i][j]` depends only on `i−j` (shift-equivariance), banded if windowed | tokens → relative-offset class | #distinct offsets (= window width `w`) | translation-invariance case of `equitableOfAttention` |
| **head-GQA** | heads tied within a group; pooled head operator quotients to the group rep | heads → KV-group | #KV groups | `MultiHeadAttention`, `multiHead_restrict_eq_symmQuotient` |
| **positional-equivariant** | `A[i][j]` constant on group-orbit cells of a geometric/group action (SE(3), Lie G, S_n, lattice) | tokens/points → group-orbit cell | #orbit types | `equitableOfAutomorphism` (orbit partition is equitable) |

---

## Architecture → reduction table

| architecture | paper / url | Graphplay reduction | exact or approx | equitable **by design**? |
|---|---|---|---|---|
| **Set Transformer (ISAB/PMA)** | Lee et al. 2019, arXiv:1810.00825; code github.com/juho-lee/set_transformer | token-cell (full S_n permutation-equivariance); inducing points already are an explicit `r`-cell bottleneck | **exact** | **YES** — permutation-equivariant by construction; the `m` inducing points literally *are* the `r` cells |
| **LieTransformer** | Hutchinson et al. 2021, arXiv:2012.10885; code github.com/oxcsml/lie-transformer | positional-equivariant (attention constant on Lie-group orbits / lifted cosets) | **exact** | **YES** — equivariant to an arbitrary Lie group G by construction |
| **SE(3)-Transformer** | Fuchs et al. 2020, arXiv:2006.10503; code lucidrains/se3-transformer-pytorch, NVIDIA SE3Transformer | positional-equivariant (SO(3)/SE(3)-equivariant attention via spherical-harmonic kernels) | **exact** (within each degree-ℓ irrep block) | **YES** — roto-translation-equivariant by construction; the irrep block structure *is* a cell decomposition |
| **E(n)-GNN (EGNN)** | Satorras et al. 2021, arXiv:2102.09844; code vgsatorras/egnn, lucidrains/egnn-pytorch | token-cell + positional (message weights constant on E(n)-orbit cells; graph automorphism → equitable) | **exact** for the equivariant message aggregation | **YES** — E(n)-equivariant by construction (note: it is attention-free message passing; the reduction targets the aggregation, not a softmax) |
| **Group-Equivariant Stand-Alone Self-Attention (GSA-Nets)** | Romero & Cordonnier 2021, arXiv:2010.00977 | positional-equivariant (attention tied across a discrete group acting on the spatial grid) | **exact** | **YES** — p4 / p4m group-equivariant by construction |
| **Axial Attention** | Ho et al. 2019, arXiv:1912.12180; code lucidrains/axial-attention | banded/token-cell *factorization* (rows & columns are independent axes → block/cell structure along each axis) | **exact** as a factorization; cell-constancy only if the per-axis pattern is itself tied | partial — axis factorization is structural, not symmetry-tied; equitable only if combined with a tied per-axis pattern |
| **Grouped-Query Attention (GQA)** | Ainslie et al. 2023, arXiv:2305.13245 | **head-GQA** (multiple query heads share one KV head → heads tied within a group) | **exact** on the head axis (KV is literally shared = tied params) | **YES on the head axis** — KV-sharing is exact weight-tying; this is the cleanest head-axis instance |
| **Multi-Query Attention (MQA)** | Shazeer 2019 (degenerate GQA, all heads one KV group) | head-GQA with `r = 1` KV group | **exact** | **YES** — single shared KV |
| **Mistral 7B (SWA + GQA)** | Jiang et al. 2023, arXiv:2310.06825; open weights (Apache-2.0) | banded (sliding-window = banded-Toeplitz mask, window `w=4096`) **+** head-GQA | banded mask is **exact-sparse** but only **approximately** cell-constant (learned scores vary within the band); GQA part is exact | banded: **NO** (sparse, not tied — different reduction); GQA: **YES** |
| **Longformer** | Beltagy et al. 2020, arXiv:2004.05150 | banded (sliding window) + global tokens | sparse-banded; **NOT** cell-constant (learned) | **NO** — sparse, not equivariant; ε-equitable at best |
| **BigBird** | Zaheer et al. 2020, arXiv:2007.14062 | banded (window) + random + global; block-sparse | sparse-block; **NOT** cell-constant | **NO** — sparse, not equivariant |

---

## The three strongest EXACT-domain targets

These are genuinely **equivariant-by-construction**, so the cell-constancy hypothesis
`A[i][j] = B[cell i][cell j]` holds *exactly* and is *preserved across gradient steps by
construction* — exactly the regime `training_step_linear_under_equitable` is written for.

1. **Set Transformer (ISAB)** — the canonical token-cell target. Full S_n permutation
   equivariance means the score matrix is constant on token-orbit pairs; the inducing-point
   bottleneck is *already* a hand-built `r`-cell reduction, so our quotient is its exact
   theoretical shadow. Best clean match for the `blockAttentionApply` correctness theorem.

2. **LieTransformer** — the canonical positional-equivariant target. Attention is provably
   constant on Lie-group orbits (lifted-coset construction), so `cell` = orbit map and `r` =
   number of orbit types. Equivariance is structural for *any* Lie group G, giving a
   parameterized family of exact instances.

3. **SE(3)-Transformer / EGNN** — the geometric-deep-learning workhorses. SE(3)/E(n)
   equivariance forces the attention (resp. message) weights to be constant on roto-translation
   orbit cells and block-diagonal across irreps. EGNN in particular is small, widely
   reproduced, and trivially runnable on QM9 (see below). The reduction targets the equivariant
   aggregation step.

**Plus the cleanest head-axis instance:** **GQA / MQA**. KV-sharing is *literal exact
weight-tying* on the head axis — no approximation — and it is in essentially every modern
open-weight LLM. This is the head-GQA reduction in its purest form and the easiest place to
*measure a zero equitability defect on the head axis* in a real production model.

---

## Experiment shortlist (small, open, runnable — measure the equitability defect)

The "equitability defect" = how far a learned score matrix `A` is from its best cell-constant
approximation `B[cell i][cell j]` (Frobenius residual `‖A − Π_cell A‖`). Exact-domain models
should show defect ≈ 0; sparse models show large defect (confirming they need a *different*
reduction). Pick a mix of one exact-equivariant and one production-GQA model.

1. **EGNN on QM9** — *strongest exact-domain runnable.* Tiny (~few-M params), trains on a
   laptop, reference code `github.com/vgsatorras/egnn` (`main_qm9.py`) plus the minimal
   `lucidrains/egnn-pytorch`. Weights are quick to reproduce (no pretrained checkpoint needed;
   training is cheap) or use the BU DS595 Colab `qm9_egnn.ipynb`. **Measure:** the message-weight
   defect should be ~0 by construction → validates the exact-collapse claim empirically.

2. **Set Transformer (juho-lee reference)** — *exact token-cell.* `github.com/juho-lee/set_transformer`,
   tiny toy tasks (amortized clustering, max-regression) train in minutes. **Measure:** the ISAB
   attention is permutation-equivariant; confirm the induced `r`-cell partition matches our
   `equitableOfAutomorphism` orbit partition.

3. **SmolLM2-135M** — *smallest mainstream open-weight LLM with GQA.* `HuggingFace
   HuggingFaceTB/SmolLM2-135M` (safetensors, Apache-2.0, 135M params — loads on CPU). Uses
   grouped-query attention. **Measure:** the **head-GQA defect is exactly 0** (KV is shared →
   tied by construction) — a clean real-model demonstration that the head-axis reduction is
   exact in deployed models; and separately measure the (large) *token-axis* defect to show the
   token reduction does **not** fire on a generic learned LM.

4. **Mistral-7B-v0.1** (if a 7B fits) — *banded + GQA in one production model.* Apache-2.0,
   `arXiv:2310.06825`. Lets you measure two axes at once: GQA head-defect ≈ 0 (exact), and the
   sliding-window band defect > 0 (sparse, not tied) — a direct side-by-side of "exact reduction"
   vs "merely sparse." Heavier to run; use only if the 135M and EGNN experiments need a
   large-scale confirmation.

**Recommended single best model to run first:** **EGNN on QM9** — smallest, cheapest, and
genuinely equivariant-by-construction, so it directly exercises the *exact* domain the Lean
theorems certify. If you want a *language* model specifically, **SmolLM2-135M** for the exact
head-axis (GQA) demonstration.

---

## Honest note: equivariant-by-construction (exact domain) vs. merely sparse (different reduction)

- **EXACT domain (cell-constant by construction):** Set Transformer, LieTransformer,
  SE(3)-Transformer, EGNN, GSA-Nets, and the **head axis** of GQA/MQA. For these the score
  (or message) matrix is *forced* by a symmetry to be constant on orbit cells, so
  `A[i][j] = B[cell i][cell j]` holds exactly and is preserved under training **by construction**
  (the update is on the small tied `B`, then `A` is re-derived — exactly the persistence argument
  in the `training_step_linear_under_equitable` docstring). This is where the `O(n²)→O(n·r)`
  collapse is a *theorem*, not an approximation.

- **NOT exact — merely sparse (needs a different / approximate reduction):** Longformer, BigBird,
  and the **sliding-window (token) axis** of Mistral. These impose a *sparsity mask* (banded +
  global + random), **not** a weight-tying symmetry. The mask makes attention `O(n·w)` for window
  `w`, but the surviving entries are **freely learned** — `A[i][j]` is *not* cell-constant within
  the band. Our exact collapse does **not** fire here; the right tool is the **ε-equitable
  partition** theory flagged as the open frontier in `AttentionComplexity.lean`'s "Honest scope"
  (an ε-cell-constant `A` quotients with controlled error). Banded-Toeplitz becomes exact only in
  the *shift-equivariant* limit (scores a pure function of `i−j`), which learned LMs only
  approximate.

- **Subtlety — Axial attention:** the row/column factorization is a *structural* `O(n√n)` win
  that is orthogonal to ours; it becomes equitable only if the per-axis pattern is *itself*
  symmetry-tied. Count it as a factorization that *composes with*, rather than *is*, our
  reduction.

- **Subtlety — EGNN is attention-free:** it is message-passing, not softmax attention. The
  reduction applies to its equivariant *aggregation* (which is a weighted sum over E(n)-orbit
  cells), so it is the cleanest *runnable* exact target even though it is not literally a
  transformer head.

( ◕‿◕ ) the clean story: **symmetry-tied → exact theorem; sparsity-masked → ε-approximate.**
