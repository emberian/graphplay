# Low-Rank / Intrinsic-Dimension / Structured Attention — Literature Sweep

Scope: evidence bearing on our hypothesis that a learned attention matrix factors as
**A = A_eq + R**, where A_eq is a structured/equitable base (apply-cost O(n·r)) and R is a
**low-rank or sparse residual** ("steered correction"). The question is adversarial: (1) is the
post-base residual *empirically* low-rank, and (2) has anyone already built "structured base +
low-rank correction"?

PDFs downloaded to `/Users/ember/dev/graphplay/refs/ml-theory/` (all verified real PDF, >50 KB):

| file | arXiv | role |
|---|---|---|
| `linformer_2006.04768.pdf` | 2006.04768 | self-attention is low-rank (spectrum evidence) |
| `scatterbrain_2110.15343.pdf` | 2110.15343 | **closest prior art**: sparse + low-rank decomposition of attention |
| `intrinsic_dim_2012.13255.pdf` | 2012.13255 | intrinsic dimensionality of fine-tuning |
| `lora_2106.09685.pdf` | 2106.09685 | low-rank *update* to a frozen base |
| `rank_collapse_2103.03404.pdf` | 2103.03404 | pure attention → rank-1; residual/skip is what saves it |
| `performer_2009.14794.pdf` | 2009.14794 | low-rank (kernel-feature) attention, the φ(Q)φ(K)ᵀ machinery |

---

## Per-paper claims and honest relation to A = A_eq + R

### 1. Linformer — *Self-Attention with Linear Complexity* (Wang et al., 2006.04768)
**Claim.** The softmax attention (row-stochastic) matrix **P is approximately low-rank**, shown
both empirically (normalized cumulative singular-value spectrum has a clear long tail across every
layer/head/task; higher layers are *more* skewed/lower-rank) and theoretically (Thm 1: a
Johnson–Lindenstrauss-style argument gives a rank-`O(d/ε²)`, sequence-length-independent
approximation to P). Linformer exploits this by projecting K,V down to `k` dimensions, yielding O(n)
attention.
**Relation to us.** This is the single strongest *direct* support that attention has low-rank
structure — but note the rank it finds is the rank of the *whole* attention matrix, not of a
residual after subtracting a structured base. It supports "A is well-approximated by rank `r`"; it
does **not** test "A − A_eq is low-rank." If anything it is a competing hypothesis: maybe A itself
is just low-rank and no equitable base is needed. **Adversarial note:** our pitch only beats plain
Linformer if A_eq captures structure that a global rank-`r` factor misses (e.g. block/permutation
structure that is full-rank but cheap to apply).

### 2. Scatterbrain — *Unifying Sparse and Low-rank Attention* (Chen, Dao, et al., 2110.15343) — CLOSEST PRIOR ART
**Claim.** Attention should be approximated as **sparse + low-rank**, A ≈ S + φ(Q)φ(K)ᵀ, explicitly
inspired by **Robust PCA** (the classical L+S decomposition). They show sparse vs. low-rank each win
in different *softmax-temperature/entropy* regimes (low-entropy → sparse; high-entropy → low-rank),
and that the *combination* strictly beats either, with up to 95% error reduction in the mid-entropy
regime. Unbiased estimator, provable error bound. Drop-in: 98% attention-memory cut at 1% accuracy
loss on T2T-ViT.
**Relation to us.** This is the paper that most directly *already does* "structured component +
low-rank correction" — and we must be honest that **the decomposition idea is not novel in itself.**
The crucial difference: Scatterbrain's structured component is a **sparse (LSH-bucketed)** matrix S,
chosen by data-dependent hashing; ours is an **equitable/graph-symmetric base A_eq** chosen by the
*partition structure of the problem*, with apply-cost O(n·r) by quotienting rather than by sparsity.
So the live, defensible novelty is **not** "decompose into base + low-rank" (taken) but specifically
**"the base is an equitable quotient that is cheap to apply because of symmetry, not because it is
sparse or itself low-rank."** Robust-PCA = sparse+low-rank; ours = (equitable/quotient) + low-rank,
which is a genuinely different choice of the "structured" summand. Treat Scatterbrain as the
benchmark to beat and to cite as the template for the L+R math.

### 3. Aghajanyan et al. — *Intrinsic Dimensionality Explains LM Fine-Tuning* (2012.13255)
**Claim.** The *change* induced by fine-tuning lives in a tiny subspace: ~200 randomly-projected
parameters reach 90% of full RoBERTa-MRPC performance. Pre-training implicitly *minimizes* intrinsic
dimension; larger models have lower intrinsic dimension.
**Relation to us.** Supports the "**correction is low-dimensional**" half of our story, but for the
*weight delta during adaptation*, not for the attention matrix at inference. It is the conceptual
parent of LoRA and an indirect prior for "a structured pretrained base + low-dimensional steering."
Good motivation, not direct evidence about attention residual rank.

### 4. Hu et al. — *LoRA: Low-Rank Adaptation* (2106.09685)
**Claim.** Freeze pretrained W₀; learn ΔW = B·A with rank `r ≪ d`. Works because the adaptation
delta is empirically low-rank (operationalizing Aghajanyan). So W = W₀ + (low-rank).
**Relation to us.** This is **literally "structured base + low-rank correction," but in weight space,
not attention-matrix space.** W₀ = frozen base (our A_eq analogue), BA = low-rank residual (our R).
The strongest existing instance of our *template*. Honest gap: LoRA's base is an arbitrary trained
matrix, not a *structurally-cheap-to-apply* equitable base, and the decomposition is of weights, not
of the n×n attention map whose O(n²) cost we are attacking. Our contribution would be transporting
the LoRA template onto the *attention map* with a *symmetry-structured* base.

### 5. Dong et al. — *Pure Attention Loses Rank Doubly Exponentially with Depth* (2103.03404)
**Claim.** Self-attention *without* skip connections / MLPs collapses doubly-exponentially fast to a
**rank-1 matrix** with identical rows. Skip connections and MLPs are precisely what arrest this
collapse; they give a path-decomposition where the residual paths carry the surviving rank.
**Relation to us.** Double-edged. (a) Supports that the attention operator alone is *driven toward*
low rank — consistent with "A_eq (the rank-1-ish smooth base) + R." (b) Warning: if the attention
core wants to be rank-1, then the *interesting* information is exactly in the residual carried by
skips, i.e. R is where the signal lives and may **not** be small/low-rank — it might be full-rank but
*structured*. This is the most adversarial paper for a naive "R is tiny" claim: it suggests the
useful part is the deviation from a structured (rank-1) base, which is the *opposite* of "the base
does the work and R is a small correction." Reconciles with us only if A_eq is taken richer than
rank-1 (a genuine equitable quotient), so that R is the small leftover.

### 6. Choromanski et al. — *Rethinking Attention with Performers* (2009.14794)
**Claim.** Approximate softmax attention by a **low-rank kernel feature map** φ: A ≈ φ(Q)φ(K)ᵀ
(FAVOR+), giving unbiased softmax estimation in O(n). The low-rank summand machinery Scatterbrain
reuses.
**Relation to us.** Provides the concrete O(n·r) apply mechanism for the *low-rank* summand R, and is
evidence that a low-rank kernel factor alone is often *insufficient* on structured/hierarchical tasks
(per LRA and Scatterbrain) — which is exactly why a non-trivial structured base A_eq could add value
on top of a Performer-style R.

---

## EVIDENCE VERDICT

**Is the "steered correction" idea (A = A_eq + low-rank R) alive?** — *Qualified yes.*

1. **Attention is low-rank-ish at the whole-matrix level: well-established** (Linformer spectrum +
   JL theorem; Performer; the rank-collapse paper even says the *core* wants to be rank-1). So a
   low-rank summand is firmly justified by the literature.

2. **Low-rank *correction to a fixed base* is established in weight space** (LoRA, intrinsic-dim) and
   in *attention* space the L+S ("structured + low-rank") decomposition is established
   (Scatterbrain via Robust PCA). So the *shape* of our hypothesis is corroborated, not speculative.

3. **The specific empirical claim "the residual after an *equitable/structured* base is low-rank" is
   NOT directly tested anywhere I found.** Closest is Scatterbrain, whose structured summand is
   *sparse (LSH)*, not equitable-quotient. Nobody measured rank(A − A_eq) for an equitable A_eq.
   That measurement is the open, ownable empirical question and the natural first experiment.

4. **Adversarial caveat (must address):** the rank-collapse result warns that the part of attention
   carrying real signal is the *deviation* from a smooth/rank-1 base. If A_eq is too coarse, R is
   where everything lives and is *not* small — the decomposition buys nothing. Our claim therefore
   survives only if A_eq is rich enough (a real equitable quotient capturing the problem's symmetry)
   that R is genuinely a low-rank/sparse leftover. The hypothesis is **falsifiable**: compute
   rank(A − A_eq) on real heads and check it is small relative to rank(A).

**Closest prior art doing "structured base + low-rank correction":**
- **Scatterbrain (2110.15343)** — attention = (sparse structured) + (low-rank), Robust-PCA-style.
  Same template, different structured summand (sparse vs. equitable). *This is the one to beat.*
- **LoRA (2106.09685)** — weight = (frozen base) + (low-rank). Same template, weight space not
  attention space.

**Bottom line for the paper:** Do **not** claim novelty for "decompose attention into base + low-rank
residual" — Scatterbrain and LoRA own that. Claim novelty for **(i) the base being an *equitable
quotient* applied in O(n·r) via symmetry/quotienting rather than via sparsity or its own low rank,
and (ii) an empirical demonstration that rank(A − A_eq) is small for equitable A_eq** — a measurement
no cited work performs. Pair any such claim with the rank-collapse caveat to stay honest.
