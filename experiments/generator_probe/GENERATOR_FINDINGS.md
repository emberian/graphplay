# Probing the SCORE GENERATOR `S = QKᵀ`, not `A`

*Brutally-honest lab report. The previous work (`residual_lab/RESIDUAL_FINDINGS.md`,
`paper/deeper_ideas.md`) established that the attention matrix `A` is full-rank and
its equitable residual is fat — a NEGATIVE for the "A is structured" story. This
lab re-asks the question on the **generator** `S = QKᵀ` (rank ≤ d by construction),
because `A = rownorm(exp(S/√d))` is the thermal exponential of `S`. The mis-measure
hypothesis: structure might live in `S` where the framework can see it, even when
`A` looks irreducible. We test specifically for structure **beyond low-rank**
(equitable / coherent / circulant / sparse-log / butterfly), since "generator is
low-rank" is already known (it is why linear attention works).*

All numbers regenerate with:

```bash
cd experiments && source .venv/bin/activate && cd generator_probe
python run_tiny.py        # 4 trained tiny attention-only models -> tiny_results.json
python run_smollm.py      # SmolLM2-135M, 12 heads across 3 layers -> smollm_results.json
python run_followups.py   # forced-equitable + 270-head banded-log -> followup_results.json
python make_figures.py    # figures/01_*.png, figures/02_*.png
```

Models: the four `graphplay_probe` tiny attention-only transformers (Q,K tapped via
forward hooks in `extract_qk.py`, so `S = qkᵀ/√d` is exact) and **SmolLM2-135M**
(30 layers, 9 query heads, 3 KV heads, d_head=64, RoPE applied to q,k before
forming S; seq_len n=64 so `rank(S) ≤ 64` is a genuine reduction).

---

## THE HEADLINE

**No.** The generator is **low-rank and otherwise unstructured.** The structure the
framework looks for — a nontrivial *equitable* partition, a small *coherent/color*
algebra, a *circulant/Toeplitz* form — is **absent from `S` just as it is from `A`**,
and where `S` *does* compress, it compresses by **plain low-rank, which is the known
story**, not by any equitable / association-scheme structure. The single partial
positive is the **matrix-log**: `log(A)` is strongly banded ("sparse Hamiltonian")
for a real **~28% minority of heads** (the local/positional ones), bimodal across the
population. Butterfly is a weak partial: `A` admits a *better* (but still far-from-
exact) butterfly product than `S`.

So: **"generator low-rank" — YES (known). "generator equitable/structured beyond
low-rank" — NO.** This is an honest partial-negative for the equitable framework
applied to attention, with one localized sparse-Hamiltonian pocket worth keeping.

---

## Per-probe verdict

### Probe 1 — Generator rank (KNOWN baseline). **Confirmed.**
On SmolLM2 (n=64, d_head=64): `rank_ε(S) = 18–37`, always `≤ d_head`, while
`rank_ε(A) = 10–64` (near-full on the rich heads). The generator carries the same
information in `≤ d` directions; `A` spends it across up to `n`. This is the
established "generator is low-rank ⇒ linear attention" fact, reproduced as a sanity
anchor. (On the tiny models n≈d so this is not yet a reduction; SmolLM2 is the clean
demonstration.) **Verdict: YES, baseline, nothing new.** *(fig 01, panel 1.)*

### Probe 2 — Generator EQUITABLE structure (THE NEW QUESTION). **NO.**
Two ways of asking, both negative:

* **Exact 1-WL equitable partition** (the framework's instrument) on `S`, `(S+Sᵀ)/2`,
  and `A`: **all give `r = n` cells (every vertex its own colour), defect = 0
  vacuously**, on *every* head of both the tiny models and SmolLM2. The generator has
  **no nontrivial exact equitable partition** — exactly the generic continuous-weight
  fate that already killed it for `A`. `defect_eq(S)` and `defect_eq(A)` are
  *identical* (both vacuous). The generator hides nothing here.

* **Forced-coarse equitable** (`r ∈ {2,4,8,16}` spectral cells, the `residual_lab`
  protocol). Here `defect_eq(S) < defect_eq(A)` looks like a win (e.g. r=8:
  `0.45` vs `0.87`) — but this is a **mirage controlled by rank**. The fair baseline
  is `S`'s own rank-`r` SVD residual, and **equitable does WORSE than plain low-rank
  on `S`** at every `r`:

  | r | equitable(S) | low-rank(S) | equitable(A) | low-rank(A) |
  |---|---|---|---|---|
  | 2 | 0.639 | **0.362** | 0.953 | 0.552 |
  | 4 | 0.532 | **0.266** | 0.919 | 0.474 |
  | 8 | 0.447 | **0.192** | 0.872 | 0.373 |
  | 16 | 0.415 | **0.134** | 0.808 | 0.257 |

  `S` is more compressible than `A` *only because `S` is low-rank* — and once you
  give plain low-rank the same DOF, low-rank wins. The equitable quotient adds
  **nothing beyond rank** on the generator. **Verdict: NO — generator is not
  equitable-beyond-low-rank. The framework's quotient does not see new structure in
  `S`.** *(fig 01, panel 2.)*

### Probe 3 — Coherent algebra / color count. **NO, and inverted.**
A full-rank-but-small-algebra matrix (association scheme / circulant) has a *small
entry alphabet*. We count distinct entry "colors" and distinct row-multiset profiles:

* SmolLM2: `S` has **471–740 distinct colors** of 4096 entries; **A has only
  151–237.** `S` has *more* colors than `A`, not fewer. Distinct row profiles of `S`
  = `n` (every row distinct). The generator's algebra is *bigger* than `A`'s — the
  softmax + row-normalization actually *quantizes/compresses* the entry alphabet.
* Toeplitz/circulant defect: `S` is **0.38–0.92** from Toeplitz (no diagonal
  structure), generally *further* than `A` (which is mildly Toeplitz, 0.21–0.31, on
  the positional heads because softmax concentrates on `|i−j|`).

So the generator is **not** circulant-like, Toeplitz-like, or association-scheme-like.
It is a generic low-rank matrix with a rich entry alphabet. **Verdict: NO.**
*(fig 01, panel 3.)*

### Probe 4 — Matrix-log of `A` (sparse Hamiltonian?). **PARTLY — the one live signal.**
Real principal `log(A)` (after a strictly-positive row-stochastic regularization;
we flag and discard heads where `‖exp(log A) − A‖` or imaginary mass exceeds 5%,
leaving 226 of 270 SmolLM2 heads reliable). Bandedness of `log(A)`:

* **Bimodal.** `band-w1` mass: median **0.01**, mean **0.24**, max **0.90**, and
  **28% of heads carry >50% of their log-mass in the tridiagonal band**. A real
  minority of heads — the local / positional / induction-adjacent ones, concentrated
  in early and late layers (e.g. L0H2 band1=0.89, L29 heads 0.70–0.83) — have a
  genuinely **banded (sparse, near-tridiagonal) generating Hamiltonian**: `A` is
  full-rank but is `exp` of a sparse operator.
* The majority of heads have a dense, near-full-rank `log(A)` (band mass ≈ 0).

**Verdict: PARTLY YES.** "Dense full-rank `A` = thermal evolution of a *sparse*
Hamiltonian" is **true for ~1/4 of heads, false for the rest.** This is the most
interesting positive in the lab and the one worth a follow-up (it localizes the
"sparse-Hamiltonian attention" idea to a specific, identifiable head population).
*(fig 02, panel A.)* Honest caveat: `log(A)` is not the QKᵀ generator — it is the
*propagator* generator one would read off if `A` were a one-step quantum/stochastic
evolution; the banded-log heads are exactly those whose `A` looks like a short-range
transfer operator.

### Probe 5 — Butterfly / Monarch product factorization. **PARTLY / weak.**
Gradient-fit of `M ≈ B_L … B_1` (depth-`L` product of 2×2 butterfly factors,
O(n log n) params) on SmolLM2 last-layer head:

* `A` reaches **0.21** relative error at full depth `log₂n = 6`; `S` only **0.43**.
* Neither reaches ~0, so **neither is an exact butterfly** — a true butterfly fits at
  error ≈ 0. But `A` consistently admits a *better* sub-quadratic product than `S`
  (the softmax appears to push `A` toward a more hierarchical/multiscale form).
* On the tiny models the only clean butterfly fit is `averaging`'s generator
  (`S` err **0.14**) — because that task needs near-uniform attention, whose `S` is
  smooth and low-frequency; the sharp tasks (induction/recall/local) do **not**
  butterfly-fit (`S` err 0.41–0.56).

**Verdict: PARTLY.** `A` has a *partial* sub-quadratic product factorization (better
than the generator's), but not an exact one; the generator does not butterfly-fit
except on intrinsically smooth (low-rank-ish) heads. *(fig 02, panel B.)*

---

## Distinguishing the known from the new (the brief's demand)

| claim | status | evidence |
|---|---|---|
| **generator low-rank** | **KNOWN, confirmed** | rank(S) ≤ d ≪ rank(A) on SmolLM2 (Probe 1) |
| **generator equitable** | **NEW claim — FALSE** | exact 1-WL: r=n vacuous (= A); forced-r: equitable loses to S's own low-rank (Probe 2) |
| **generator coherent/circulant** | **NEW claim — FALSE** | S has *more* colors than A, far from Toeplitz/circulant (Probe 3) |
| **log(A) sparse Hamiltonian** | **NEW claim — PARTLY TRUE** | banded log for ~28% of heads, bimodal (Probe 4) |
| **A butterfly product** | **NEW claim — PARTLY** | A fits to 0.21 (better than S's 0.43), not exact (Probe 5) |

The honest reading: **the generator's only compressibility is its known low-rankness.**
Re-measuring on `S` instead of `A` does **not** rescue the equitable/coherent program
— the structure is genuinely absent, not merely hidden by the softmax. The softmax,
if anything, *adds* mild structure to `A` (fewer colors, mild Toeplitz, better
butterfly) rather than destroying structure that `S` had. The framework's "structured
generator" bet, in its equitable/coherent form, is a **partial-negative**; its
sparse-Hamiltonian form survives on a localized head minority.

---

## Is dense attention the thermal evolution of a structured Hamiltonian?

For **most heads: no** — the generator `S` is low-rank but otherwise generic
(no equitable, coherent, circulant, or Toeplitz structure), and `log(A)` is dense.
For a **real ~28% minority** (local/positional heads): **yes in the sparse-Hamiltonian
sense** — `A` is full-rank but is `exp` of a banded (near-tridiagonal) operator. The
equitable/coherent-algebra lens the project is built on does **not** fire on the
generator any more than on `A`; the live wedge is the *sparse-log* (banded-Hamiltonian)
characterization of the positional head population, not the equitable quotient.

---

## Honest risks / limits
1. **Tiny models are n≈d**, so Probe 1's reduction is only meaningful on SmolLM2;
   the tiny models serve as exact-`S` controls and they agree with SmolLM2 on every
   qualitative verdict.
2. **`log(A)` ≠ `S`.** The sparse-Hamiltonian positive is about the *propagator*
   generator (`log A`), not the *score* generator (`QKᵀ`). The two coincide only if
   `A` were literally `exp` of `S`, which it is not (softmax row-normalizes). We report
   both and do not conflate them.
3. **Butterfly fit is gradient-descent**, so its errors are *upper bounds*; a better
   optimizer could lower them. The S-vs-A *ordering* (A fits better) is the robust
   claim, not the absolute values.
4. **One text batch, 64 tokens.** The banded-log fraction (28%) is a point estimate on
   one prompt; the qualitative bimodality is robust but the exact fraction is not.

## Figures
- `figures/01_rank_equitable_color.png` — Probes 1 (rank baseline), 2 (equitable loses
  to low-rank on S), 3 (S has more colors than A).
- `figures/02_log_butterfly.png` — Probe 4 (bimodal banded-log, 28% banded) and Probe 5
  (A butterfly-fits better than S, neither exact).

---

*( ⌐■_■ ) we looked under the softmax for the hidden symmetry and found only its
rank. The generator keeps its one secret — it is low — and tells no other. But a
quarter of the heads wear a tridiagonal heart, and those we can still name.*
