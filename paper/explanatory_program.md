# The equitable spectrum as a common coordinate for the attention zoo

*A program for experiments demonstrating the explanatory power of the
equitable-partition lens on the performance & failure modes of attention
variants. Status: design + falsifiable predictions. Honest about prior art.*

## 0. The reframe

Stop thinking "we compress attention." Think: **the equitable-partition
spectrum is a coordinate system, and every attention variant is a different
*structural bet* expressed in it.** Each mechanism projects the "ideal" full
attention `A*` for a task onto a structured submanifold; its accuracy is how
much of `A*` lives in that submanifold, and its *failure mode* is the residual
it cannot represent. Because all the bets live in *one* coordinate, the
framework can (a) place every variant, (b) place every task, and (c) **predict
the match** — which is the explanatory claim.

This is falsifiable: the match-metric must actually predict the measured
performance ranking. If it doesn't, the lens is decorative.

## 1. The attention zoo as structural bets (one coordinate)

For a task, let `A*` be the attention of a *trained full-attention reference*.
Decompose it: nearest equitable partition `P_r` (r cells), `A_eq = `its
quotient lift, residual `R = A* − A_eq`, with rank/sparsity spectra of each.

| Variant | Structural bet (the submanifold) | Coordinate that predicts it | Known failure mode |
|---|---|---|---|
| Full (dense) | none (r = n, exact, O(n²)) | — | cost only |
| Linear (Performer, Linformer) | `A*` is global **low-rank k** | `rank_ε(A*)` | sharp/high-rank tasks (induction, copying) |
| Sparse (Longformer, BigBird) | `A*` lives on a **fixed pattern** | off-pattern mass of `A*` | important edges off-pattern |
| Local / sliding-window (Mistral) | `A*` is **banded / circulant** (translation-equitable) | banded residual `‖A* − band_w‖` | long-range dependencies |
| Structured / equitable (Set Transformer, GQA, axial) | `A*` is **equitable with r cells** (a symmetry) | defect `‖A* − A_eq(P_r)‖` | data symmetry ≠ imposed symmetry |

The unifying statement: each variant = a projection `Π_M(A*)` onto a structured
manifold `M` (low-rank / sparse / banded / equitable). **Performance ∝
`‖Π_M(A*)‖ / ‖A*‖`; failure ∝ `‖A* − Π_M(A*)‖` and *where* that residual is
concentrated.** Our specific contribution is the *equitable* manifold (strictly
more general than the group-orbit manifold) and the *verified* spectral
consequences of projecting onto it.

## 2. The instrument (the probe)

Given any attention matrix `A` (n×n, per head, per layer):
1. **Equitable decomposition**: compute the nearest equitable partition at a
   sweep of cell-counts r (color-refinement / spectral clustering on the
   symmetrized `A`), giving `A_eq(r)` and `R(r) = A − A_eq(r)`.
2. **Residual spectrum**: singular values of `R(r)` — *is the leftover
   low-rank?* (the live-or-dead question for the steered-correction idea).
3. **Spectral subset**: which eigenvalues of `A` survive into `Q̃(P_r)`
   (the verified lift's content, measured).
4. **Submanifold residuals**: also project onto low-rank-k, sparse-pattern,
   banded-w — to place *every* variant's bet in the same coordinate.
Outputs: per (layer, head, r) a vector `(defect_eq, rank(R), off-pattern mass,
banded residual, surviving-spectrum fraction)`.

## 3. Falsifiable experiments

**E1 — Match predicts performance (the headline).** Battery of small tasks with
*known, distinct* structural character: induction/copying (needs sharp/sparse),
associative recall, averaging/bag-of-words (low-rank suffices), local/translation
(banded), set/permutation (equitable), modular arithmetic (group=equitable).
For each task: train a full reference, measure `A*`'s coordinate (§2); for each
variant compute its submanifold residual; **predict the performance ranking**
from the residuals; compare to *measured* benchmark performance. Explanatory
power = the residual-match predicts the ranking across tasks.

**E2 — Failure-mode localization.** For a variant known to fail on a task (e.g.
linear attention on induction), show the residual it cannot represent is
*concentrated exactly on the failure instances* (e.g. the induction edges) — the
residual *is* the mechanistic explanation of the failure, not a correlate.

**E3 — Training dynamics / generalization.** Track `‖R(t)‖` and cell-stability
across training. Prediction: generalization onsets when the equitable partition
*crystallizes* (`‖R‖` drops, cells stabilize). On grokking tasks (modular
arithmetic) the equitable partition should coincide with the group structure at
the grokking transition — connecting to Nanda's Fourier circuits but in a
group-free, operator-algebraic progress measure `‖R(t)‖`.

**E4 — Equitable-quotient sharpness (the novel open one).** Does the *cell-uniform
subspace* have its own edge-of-stability? Measure the Hessian restricted to the
quotient subspace vs the full Hessian during training. If the quotient has
distinct sharpness dynamics vs `2/η`, that is a framework-specific, previously
un-asked prediction (surfaced by the EoS sweep).

## 4. Honest risks (design experiments that can falsify us)

- **Rank-collapse caveat** (Dong et al. 2103.03404): attention cores tend toward
  rank-1 with the signal in the *deviation* carried by skips. If `A_eq` is too
  coarse, `R` carries everything and isn't low-rank — the steered-correction and
  the "small residual" story both die. E1/§2 must report `rank(R)` honestly; a
  fat residual *falsifies* the compressibility claim, and we report it.
- **The match-metric might not predict.** If residual-mass does not track
  measured performance, the lens is descriptive-only. E1 is built to catch this.
- **Most qualitative pieces are prior art** (GDL, Scatterbrain, Nanda,
  Şimşek, O'Clery–Barahona). The contribution is the *common verified
  coordinate* + the *measured predictions* + the *equitable-⊋-group* generality
  — NOT the slogan "symmetry matters." Frame accordingly.

## 5. First experiment to run

Build the probe (§2) and run **E2-minimal** on one trained small model
(SmolLM2-135M for GQA defect≡0 as a sanity anchor; a 2-layer attention-only
transformer trained on induction + averaging for the contrast). Deliverable: a
single figure — residual-vs-r and `rank(R)` per layer for each task — that shows
the residual is small/low-rank where the variant succeeds and concentrated where
it fails. That figure is the go/no-go for the whole explanatory program.
