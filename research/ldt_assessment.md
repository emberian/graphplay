# Lattice Deduction Transformers (LDT) — adversarial graphplay-connection assessment

**Paper:** *Lattice Deduction Transformers*, Liam Davis (Amherst), Leopold Haller (Axiom / axiommath.ai), Alberto Alfarano (Axiom), Mark Santolucito (Barnard / Columbia). arXiv:2605.08605 v1, 9 May 2026. Code: github.com/lcrh/lattice-deduction-transformers (single-commit reconstruction; sole committer `Leopold Haller <leo@axiommath.ai>`).
**Status:** research scoping memo (adversarial). Default posture: skeptical. Audience: Ember (+ possibly Tino Tamon). Precision over enthusiasm.
**Date:** 2026-06-01. Source read: full PDF (14 pp incl. Appendix A) + the actual training/solver/model code.

---

## 0. TL;DR verdict (read this first)

LDT is a **genuine, clean, textbook abstract-interpretation construction** wrapped around a tiny looped transformer. The abstraction is not hand-wavy: the paper states the **Galois connection `C ⇄ A` verbatim** (powerset of solution strings ⇄ product-of-per-cell candidate-sets), defines `α(S')(i) = {s(i) : s ∈ S'}` and `γ(a) = {s : ∀i. s(i) ∈ a(i)}`, gives the **best abstract transformer** `dedₚ(a) = α(γ(a) ∩ ‖p‖)`, and characterizes solving as **greatest-fixpoint Kleene iteration of a monotone *reductive* deduction operator** (a lower closure operator) descending from ⊤ toward ⊥. The transformer's only job is to *learn* `dedₚ`; the lattice projection, conflict (= ⊥ reached), and branching are symbolic and live in `dpll_step`/`solve`, outside the net.

The graphplay connection is **real at the level of "both are complete lattices with Galois connections and Kleene fixpoints,"** but the three specific bridges resolve as:

- **(i) Sound abstraction ↔ our quotient/certificate — REAL-BUT-NOT-(YET)-USABLE.** Both are complete lattices + Galois-flavored adjunctions, and LDT *wants* a machine-checked soundness account it does not have. BUT our objects are a **different kind of lattice** (partition/refinement lattice; the lift `cellInflate`/`restrict` is a *linear-algebra* subspace isometry, an **exactness** statement — "the small quotient computes the *same* answer") whereas LDT's is an **information/over-approximation lattice** where the whole point is *inexactness* (`α∘γ` strictly loses cell-correlations; see their Fig. 5). graphplay has **no `GaloisConnection`/`GaloisInsertion` instance proven** — the order-theoretic adjunction it would need to *be* the soundness account is exactly the piece that's missing. So the contribution is structurally available but is **new Lean work, not a wiring of existing assets.**
- **(ii) Looped convergence ↔ spectral gap — SUPERFICIAL (and falsified by the paper's own mechanism).** LDT's iteration count is governed by **strict descent / well-foundedness** ("the lattice is finite and each step strictly decreases the alive-candidate count", §4.2) and by problem hardness + how well-trained `dedₚ` is (Fig. 3a). It is Kleene iteration of a **monotone map on a discrete lattice**, with **no linear operator and no eigenvalues** in the loop. The `k* ≈ log ε / log|λ₂/λ₁|` prediction is a *spectral-mixing* law for a contraction; it does **not** model gfp-iteration of a closure operator. The honest analogy is "number of forward passes ≈ fixpoint-iteration depth = longest deduction chain length," which is a **combinatorial/Cousot height** quantity, not a spectral one.
- **(iii) Deduction step ↔ WL refinement / constraint propagation — REAL-AND-USABLE (as positioning), REAL-BUT-NOT-USABLE (as a literal identity).** LDT's per-step candidate elimination **is** unit-propagation / arc-consistency narrowing, and the *paper itself* frames solving as gfp of a reductive operator — the *exact dual species* of WL, which graphplay proves is the **lfp of a monotone refining operator** (`wlRefine_stable`, `wlRefine_coarsestEquitable`). The k-WL ↔ k-consistency ↔ Sherali–Adams analogy is real. The literal identity fails (WL refines a *partition of vertices*; LDT narrows a *candidate-set per position* — different carriers, opposite fixpoint direction, downward-vs-upward).

**Decision: CONTRIBUTE — a *narrow, honest* verified-soundness Lean note, NOT a fold-in, NOT the spectral experiment.** The single sharpest move is in §3.

**Authorship/ember angle (§4):** the LDT authors are the **PL/abstract-interpretation-meets-SAT community** (Haller co-authored the foundational *Abstract Conflict Driven Learning*, POPL 2013, ref [28]; Davis works on the Stålmarck saturation prover, ref [27]; Santolucito = PL). **ember is NOT an author or code contributor** — no "ember"/"arlynx"/"lunar.town"/"cmr://" string anywhere in the repo, paper, or git metadata. The `lcrh` org = Leopold C.R. Haller's initials, not ember. The "cmr://ember" repost is a *social-graph* signal only; treat as "ember is adjacent to this scene," not "ember is in this artifact."

---

## 1. ELABORATION — the precise mechanics

### 1.1 The abstract domain (the lattice)

**Concrete domain** `C = ℘(S)`, where `S = {1..k} → V` is the set of fixed-length solution strings over vocabulary `V` (digits 1–9 for Sudoku, the 5 cell-types for maze). `C` ordered by ⊆, meet ∩, join ∪, ⊤ = all of `S`, ⊥ = ∅.

**Abstract domain** `A = {1..k} → ℘(V)` — **a product, over the `k` positions/cells, of the per-cell candidate powerset.** Order is **pointwise inclusion**: `a ⊑ b ⟺ ∀i. a(i) ⊆ b(i)`. Meet/join pointwise: `(a⊓b)(i) = a(i)∩b(i)`, `(a⊔b)(i) = a(i)∪b(i)`. ⊤ = every cell holds the full vocab `V`; ⊥ = (identified with) any `a` with an **empty cell** `a(i) = ∅`. Precision ordering: **lower = more informative**; deduction *descends*. The paper names this the **grid powerset lattice**.

**In code** (`sudoku_extreme.py`, `dpll.py`): `state : [B, S, C]` of binary alive-bits. `x` (puzzle input) is ⊤: blanks = all-ones (sum=9), givens = singletons. A solution `y` is one-hot per cell (a minimal SAT element). UNSAT target = all-zeros (`y_bot`, the explicit ⊥). The lattice is literally a multi-hot tensor; meet = bitwise AND, join = bitwise OR.

> **Key honest caveat the paper flags itself (App. A.1):** abstracting to `A` *loses all inter-cell correlation* — `α∘γ` adds back grids that satisfy the per-cell candidate sets but were not in the original set (their Fig. 5 worked example). This **inexactness is the defining feature** of an over-approximation domain. Contrast graphplay's quotient, whose entire content is *exactness* on the symmetric sector.

### 1.2 The Galois connection (stated verbatim, App. A.1)

```
              α
        C  ⇄  A           α(S')(c) = { g(c) : g ∈ S' }   (per-cell projection; lower adjoint)
              γ           γ(a)     = { g ∈ G : ∀c. g(c) ∈ a(c) }   (upper adjoint)
```
with the two round-trip laws printed explicitly:
```
S ⊆ γ(α(S))            (abstraction is sound: round trip over-approximates)
α(γ(a)) ⊑ a            (re-abstraction refines / strips unwitnessed structure)
```
This is the **standard over-approximation soundness**, *not* `α∘γ = id` (which would be a Galois *insertion*; they do not claim it — and Fig. 5 shows it fails). γ is monotone (`a ⊑ b ⟹ γ(a) ⊆ γ(b)`).

### 1.3 The per-forward-pass projection = the deduction / abstraction step

The **best abstract transformer** for instance `p` (App. A.2, and §4 Methodology, displayed equation):
```
dedₚ(a) = α( γ(a) ∩ ‖p‖ )
```
where `‖p‖ ⊆ S` is the (unknown, sample-only) solution set of instance `p`. "Refines `a` to keep only candidates that survive in at least one valid solution." `dedₚ` is a **lower closure operator**: monotone, **reductive** (`dedₚ(a) ⊑ a`), idempotent. *Naked singles / hidden singles are weaker sound under-approximations of this operator.* **The transformer is trained to approximate `dedₚ`** — at inference the model's per-cell sigmoids, thresholded at `θ_elim`, perform the narrowing (`masked_fill(probs < θ, 0)` in `dpll_step`). One forward pass = one application of (a learned, sound-by-training) abstract deduction step.

### 1.4 The recurrence / what makes it converge

**Two nested loops** (this is the thing the social thread blurs):
- **Inner:** the looped transformer (`PowersetModel`, `n_loops=16`): a 4-layer stack unrolled 16× with input re-injection and a LayerNorm'd outer residual (`h = LayerNorm(h + backbone(h+h0))`). Per-iteration logits are mean-pooled (or last). This is the *Sotaku/Universal-Transformer/TRM*-style recurrent backbone — it computes **one** `dedₚ`-approximation per Solve-step.
- **Outer (Algorithm 1 `Solve`):** `repeat { (x', conflict, solved) ← step(x); x ← x' } until conflict or solved`. **`step` projects the discrete lattice state forward** (deduce → narrow), re-encodes it as the transformer's input next round, and (if undetermined) **branches**.

**Convergence is gfp Kleene iteration of `dedₚ` from ⊤** (App. A.2, verbatim): *"Solving a Sudoku amounts to computing the greatest fixed point of an abstract deduction function `dedₚ` in the grid powerset lattice, starting from ⊤ and descending until no further candidates can be removed."* **Termination guarantee (§4.2): well-foundedness** — "the lattice is finite and each step strictly decreases the alive-candidate count." Cousot–Cousot fixpoint-transfer is invoked: `α(gfp f) ⊑ gfp f^♯` (App. A.2). **No contraction constant, no spectral rate.** If the gfp is a singleton-per-cell → solved; if multi-candidate cells remain → **search (branch) is invoked**, which is the completeness-restoring layer on top of the (sound but incomplete) deduction.

### 1.5 Conflict detection + backtracking

⊥ has a **dual representation** (§4.1): (a) *implicit* — any cell with empty candidate set IS ⊥ in the lattice (`empty_cell` test in `dpll_step`); (b) *explicit* — a learned **CLS-token sigmoid** trained to fire on any unsatisfiable state (`conflict_head`, threshold `θ_CLS`). A step that reaches either → **conflict → reset the chain to the puzzle's original** (`solve.py`: `new_state[idx] = original[idx]`) = backtrack. The CLS head is on the **completeness** side (a missed conflict stalls search); elimination is on the **soundness** side (a wrong elimination is unrecoverable). They are deliberately split across the soundness/completeness trade-off (Loss design, §4.2).

### 1.6 The on-policy lattice-target supervision (the `α` operator)

Per training step (`train.py`):
- **BCE target = `state ⊓ α(surviving)`** = `state * orig_y` where `orig_y = _alpha_surviving(state, solutions)`. `_alpha_surviving` takes the K ground-truth solutions still **consistent** with the current `state` and ORs them per (cell, channel) — this is **literally `α({y ∈ Y : y consistent with x})`**, the abstraction of the surviving solution set (Alg. 2 line 8: `ŷ ← x ⊓ α({y ∈ Y | y consistent with x})`).
- **Conflict target** = `gt_conflict` = "∃ cell with no state-bit consistent with `α`" = γ(state)∩surviving = ∅ = UNSAT.
- **Softmax CE** = the GT digit, but **skipped at multi-alive `α` cells** (branching cells with ≥2 legitimate survivors) — avoids forcing an arbitrary argmax.
- **On-policy:** a **pool/replay buffer** of partial lattice states; each step advances `state` by running the model's *own* `dpll_step`, so the training distribution of `state` = the model's actual search trajectory (§4.2: "lattice states evolve under the model's own forward pass"). Solved / truly-conflicted entries are discarded and backfilled → an emergent **curriculum over lattice depths**.
- **`K`** is the multi-solution sample budget: K=1 (Sudoku/Snowflake, unique solution) recovers ordinary single-target SFT; K=512 (Maze, millions of shortest paths sampled from the all-shortest-paths DAG) sharpens `α` toward the true `α(‖p‖)`. **Fig. 4b: solve-rate rises and inference-search drops with K, saturating fast** (most benefit by a handful of samples). Training-step count is K-independent; K≈512 is ~2% slower/step.

### 1.7 Results (Table 1–3)

Sudoku-Extreme: **LDT 800K → 100% accuracy / empirically sound, 15 min on 1×B200** (Sotaku 800K/2.7M-train → 98.9 in 2h40m; TRM 5M → 87.4; HRM 27M → 55; GRAM/frontier-LLMs → 0). Inference cost drops ×10 in median forwards as train budget grows (Fig. 3a). Snowflake (hex, variable-size) 800K → 100. Maze-Hard 30×30: 1.8M → 99.3 (K=1) / **99.9 (K=512)**. "Empirically sound" = returns correct answer or abstains; the few Maze misses emit valid-but-suboptimal paths (not unsound).

---

## 2. THE THREE BRIDGES — adversarial verdicts with evidence

### (i) Sound abstraction ↔ our quotient/certificate — **REAL-BUT-NOT-(YET)-USABLE**

**What's genuinely shared.** Both LDT-`A` and graphplay's partition order are **complete lattices**. Both come with an adjoint pair. LDT *explicitly lacks* a machine-checked soundness artifact and the authors are exactly the people who'd value one (§4). graphplay has the verified coalgebra/bisimulation certificate (Tower-8 `equitable_isBisim`, `dist_*` genuine-successor coalgebra, `stepInv_preserved` safety) and the dregg2-shadow `Disclosure`-style information ladder *modelled abstractly* (Tower-8 §"Relationship to dregg2"). On paper this looks like a match made for a "verified soundness of lattice-deduction" paper.

**Why it is NOT a drop-in (the adversarial core).** Three structural mismatches:

1. **Different lattice *kind*.** LDT's `A` is an **information / over-approximation** lattice: the operator is *reductive* (`ded(a) ⊑ a`), the Galois connection is **lossy** (`α∘γ ≠ id`; Fig. 5), and *soundness = over-approximation* ("never derives a false fact"). graphplay's `cellInflate`/`restrict_eq_symmQuotient` is the **opposite**: an **exactness** theorem — the `r×r` symmetric quotient computes the *same* spectrum/evolution as the `n×n` original on the cell-uniform subspace (an isometry of *subspaces*, a linear-algebra adjoint `Q̃ = D^{1/2} Q D^{-1/2}`), *not* an order-theoretic Galois connection. "Both called lattice" is true; "the same usable object" is false. The quotient is a *no-loss symmetry reduction*; LDT's abstraction is a *deliberate-loss approximation*. These are dual stories (exact reduction vs sound approximation), which is *interesting positioning* but means the graphplay lemmas don't *transfer* as soundness lemmas for LDT.

2. **graphplay has no `GaloisConnection` instance.** Grep confirms: every "adjoint" in graphplay is **operator self-adjointness** (Hermitian), none is Mathlib `GaloisConnection`/`GaloisInsertion`. The `Refines` structure (`Equitable.lean:463`, `WLRefinement.lean:189`) is an *order* (`coarsen : I'→I`, monotone color-count) but is **not packaged as the adjunction** `α ⊣ γ` that an LDT-soundness account needs. So "wire our verified Galois machinery to Tower-8" overstates: **the Galois machinery for *this* lattice does not yet exist in the repo.** It would be *new* (very doable) Lean work: define `A`, prove `α ⊣ γ`, prove `dedₚ = α∘(·∩‖p‖)∘γ` is a sound (over-approximating) reductive closure, and prove the Kleene-gfp-transfer. That is a real, self-contained, *publishable-as-a-note* deliverable — but it is **building the bridge, not crossing an existing one.**

3. **The certificate that *does* port is the conflict/backtracking safety invariant, not the quotient.** Tower-8's `stepInv_preserved` / `dist_cell_confinement` (a predicate preserved along an entire run) is the *right shape* to certify LDT's "soundness is preserved along the Solve loop" — i.e. *if every single `step` is a sound narrowing (`ded(a) ⊑ a` and `γ(ded a) ⊇ ‖p‖∩γ(a)`), then no reachable Solve-state ever excludes a true solution.* THAT is the genuinely reusable graphplay asset (an inductive run-invariant over a transition coalgebra). It is **not** about equitable partitions at all; it's about the abstract `TransitionCoalg` interface.

**Verdict: REAL-BUT-NOT-USABLE as-is; becomes REAL-AND-USABLE after one focused Lean module** (define the powerset abstract domain + Galois connection + sound-closure + run-invariant, reusing Tower-8's `TransitionCoalg`/`stepInv_preserved` as the *only* imported asset). The equitable quotient itself is a **red herring** here — wrong lattice kind.

### (ii) Looped convergence ↔ spectral gap — **SUPERFICIAL**

**The prediction.** graphplay's ML thread: "iterating attention = a walk; loops-to-convergence `k* ≈ log ε / log|λ₂/λ₁|` from the equitable-quotient spectral gap." This is a **linear-operator mixing law**: a power-iteration / Markov chain contracts to its top eigenvector at rate set by the second eigenvalue.

**Why it does not apply to LDT (paper's own words).** LDT's outer loop is **gfp Kleene iteration of a monotone reductive operator on a finite discrete lattice** (App. A.2). Termination is **well-foundedness**: "the lattice is finite and each step strictly decreases the alive-candidate count" (§4.2). There is **no linear operator iterated**, hence **no `λ₂`** to form a ratio. The relevant convergence quantity is the **Cousot fixpoint-iteration height** = the **longest sound deduction chain** before reaching the gfp (or before a branch is forced) — a *combinatorial lattice-height / constraint-graph-diameter* quantity, **not** a spectral gap. Empirically (Fig. 3a, 3b): forward-pass count is set by **(a) problem hardness** (bimodal: a "pure-deduction, no-search" mode vs a "needs-branching" mode) and **(b) training budget** (more training → the learned `dedₚ` is closer to the best transformer → fewer steps and less branching). Neither is `log ε / log|λ₂/λ₁|`.

**Could a spectral story be smuggled in?** Only by changing the object: if one *relaxed* the lattice to a continuous `[0,1]`-valued candidate field and modeled the *learned* `dedₚ` as a (nonlinear) smoothing operator, one could ask for a local contraction rate near the fixpoint. But (1) that is **not LDT** (its operator is a hard threshold + discrete branch), (2) the relevant operator is the *learned net*, whose Jacobian has nothing to do with the *graph* `λ₂` of the equitable quotient, and (3) the paper's termination proof explicitly does not need or use it. **Forcing the spectral-gap law here would be manufacturing a connection that isn't structurally present** — exactly what the brief warns against.

**Falsifiable-experiment status.** The brief proposed: "is K governed by a contraction/spectral-gap, testably matching k*?" The honest answer from the paper is **the experiment's hypothesis is already contradicted by the mechanism** — running it on persvati would measure forward-passes-vs-hardness (which LDT *already reports*, Fig. 3) and find **no `λ₂` dependence**, because there is no iterated linear operator. *Running it would most likely falsify the prediction, not confirm it.* (One could still run a *negative-result* probe — "does deduction-chain length, not spectral gap, predict LDT depth?" — but that confirms the abstract-interpretation height story, which is bridge (iii)/(i), not (ii).)

**Verdict: SUPERFICIAL.** The two "loops" are loops in different categories (discrete lattice gfp-iteration vs linear-operator power-iteration). Do **not** spend persvati GPU on the spectral-gap experiment for LDT; it is set up to fail for the right reasons.

### (iii) Deduction step ↔ WL refinement / constraint propagation — **REAL (positioning) / NOT-USABLE (literal identity)**

**What's genuinely true and sharp.** LDT's deterministic candidate-elimination **is** constraint propagation / arc-consistency: `dedₚ(a) = α(γ(a) ∩ ‖p‖)` keeps exactly the locally-consistent candidates; *naked/hidden singles = the standard propagation rules* (App. A.2, paper says so). The paper frames solving as **gfp of a monotone reductive operator**. graphplay proves **WL/color-refinement is the Kleene fixpoint of a monotone *refining* operator** on the partition lattice: `wlStep` monotone (`wlStep_isRefinement`), color-count monotone non-decreasing (`wlColorCount_mono`), **stabilizes in ≤|V| rounds** (`wlRefine_stable`) to the **coarsest equitable partition** = canonical fixpoint (`wlRefine_coarsestEquitable`). The k-WL ↔ k-consistency ↔ Sherali–Adams hierarchy is a real, well-known correspondence (Atserias–Maneva; Grohe). So **"LDT-deduction and WL are both Kleene-fixpoint constraint-propagation on a complete lattice"** is a *correct and non-trivial* unifying statement.

**Why the literal identity fails (the adversarial cut).**
- **Different carrier.** WL refines a **partition of the vertex set** (the object is "which vertices are indistinguishable"). LDT narrows a **candidate-set per solution-position** (the object is "which digits are still possible at cell i"). These are not the same lattice; a WL color is not an LDT candidate-cell.
- **Opposite fixpoint direction.** WL is a **least** fixpoint of a **refining (information-increasing upward in the refinement order)** operator started from the trivial coloring; LDT is a **greatest** fixpoint of a **reductive (candidate-removing, descending in the precision order)** operator started from ⊤. They are **dual** Kleene iterations. (This duality is itself a *nice* observation — but it means one cannot reuse a WL lemma *as* an LDT lemma.)
- **graphplay's WL is on a *fixed graph*; LDT's `dedₚ` is instance-parameterized by `‖p‖`** (the unknown solution set). LDT's "constraints" are the puzzle rules + the sampled solutions; WL's "constraint" is the adjacency. Bridging would require viewing the Sudoku constraint graph's *consistency closure* as a refinement — possible in principle (constraint propagation = a closure on the constraint hypergraph) but **not** the equitable-partition closure graphplay proves.

**The genuinely usable nugget.** The defensible, *shippable* claim is the **abstract-interpretation framing of both**: *"deterministic candidate elimination (LDT) and color refinement (WL) are instances of Kleene-fixpoint iteration of a monotone operator on a complete lattice with a Galois connection; graphplay supplies a machine-checked lfp instance (WL→coarsest equitable), LDT supplies a gfp instance (deduction→solution closure)."* That is **positioning/dual-instance framing**, which is worth a paragraph in a paper, **not** a transferred proof.

**Verdict: REAL-AND-USABLE as positioning/dual-Kleene framing; REAL-BUT-NOT-USABLE as a literal "LDT step = our coarsening" identity** (wrong carrier, opposite direction, instance-parameterized vs fixed-graph).

---

## 3. DECISION + SINGLE SHARPEST NEXT STEP

### Decision: **CONTRIBUTE (narrow, honest) — not FOLD-IN, not NOT-WORTH-IT.**

- **Not FOLD-IN.** LDT is *not* "a concrete instance of our certificate framework." Our framework is built on the *equitable-partition / exact-quotient* lattice; LDT lives on the *over-approximation* lattice. Claiming LDT folds into graphplay would be the manufactured connection the brief forbids. (The honest relationship is **dual**: exact symmetry-reduction vs sound approximation; lfp-refinement vs gfp-narrowing.)
- **Not NOT-WORTH-IT.** The abstract-interpretation core is *exactly* graphplay's native idiom (Galois connections, monotone fixpoints, coalgebraic run-invariants), and graphplay already has the one *reusable* asset: **Tower-8's `TransitionCoalg` + `stepInv_preserved`** — a verified "safety invariant preserved along an entire run." LDT has **no formal soundness artifact** and is authored by people (Haller: *Abstract Conflict Driven Learning*; Santolucito: PL) who would *credit* one.
- **CONTRIBUTE = a self-contained Lean module + short note:** *"A machine-checked soundness skeleton for learned lattice-deduction."* It defines the grid-powerset abstract domain `A`, proves the **Galois connection `α ⊣ γ`** (the paper's App. A maps line-for-line to Mathlib `GaloisConnection`), proves `dedₚ = α ∘ (·∩‖p‖) ∘ γ` is a **sound reductive closure** (`ded a ⊑ a` ∧ `γ(ded a) ⊇ ‖p‖ ∩ γ a` — "never excludes a true solution"), and **instantiates Tower-8's `stepInv_preserved`** to prove the **run-level soundness invariant**: *along any Solve trajectory whose every step is a sound narrowing, no reachable lattice-state ever excludes a true solution; hence a non-⊥ terminal that is a singleton-per-cell IS a solution.* This is precisely the property LDT *asserts empirically* ("returns a correct answer or abstains") and **never proves**. It reuses the *one* graphplay asset that genuinely fits (the coalgebraic run-invariant), and is honest that the equitable *quotient* is not the relevant object.

### THE SINGLE SHARPEST CONCRETE NEXT STEP

**Write `Graphplay/Integrations/LatticeDeduction.lean`: the ~1-page Lean theorem `soundDeduction_run_preserves_solutions`.** Concretely:
1. `abstract domain A := pos → Finset V` with the pointwise `⊑`; prove `instCompleteLattice`.
2. `def γ (a) := {s | ∀ i, s i ∈ a i}`; `def α (S) i := S.image (· i)`; prove `GaloisConnection α γ` (the paper's two round-trip laws — both are short).
3. `def soundNarrow (f : A → A) := ∀ a, f a ⊑ a ∧ ‖p‖ ∩ γ a ⊆ γ (f a)` (sound = reductive + never-drops-a-true-solution).
4. Instantiate `Tower8.TransitionCoalg` with carrier `A`, `step` = the (abstract) narrow-or-branch, and apply **`stepInv_preserved`** with `Good a := ‖p‖ ∩ γ ⊤ ⊆ γ a` to get: *every reachable Solve-state keeps every true solution alive* ⟹ a singleton terminal is correct.
5. **One short note** (or a section appended to the bisim memo / a fresh `research/` doc) stating the **dual-Kleene positioning** (LDT gfp-narrowing ⟂ graphplay lfp-WL-refinement; both Galois+Kleene), and explicitly **retracting the spectral-gap bridge** for LDT.

This is **falsifiable, finite, and high-credibility** (it is a *proof*, the currency this community respects per the Tino "precision as credibility" rule), it imports **exactly one** graphplay asset (so it cannot be accused of force-fitting the quotient), and it hands the LDT authors the artifact they're missing. If it type-checks, it is a clean outreach hook to Haller/Santolucito; if `α ⊣ γ` or the run-invariant resists, that *itself* is the honest finding that the connection is thinner than it looks.

**Do NOT:** (a) run the spectral-gap/`k*` persvati experiment for LDT — its mechanism (well-founded discrete descent) has no `λ₂` (bridge ii is set up to falsify); (b) claim LDT folds into the equitable-quotient framework — wrong lattice kind; (c) claim the existing `cellInflate`/`restrict` lemmas certify LDT — those are *exactness*, LDT needs *over-approximation soundness*.

---

## 4. Community / authorship / ember angle

- **Authors & scene.** Davis (Amherst undergrad email; Stålmarck-procedure optimizations, ref [27]), **Leopold Haller (Axiom, axiommath.ai)** — co-author of **D'Silva–Haller–Kroening, *Abstract Conflict Driven Learning*, POPL 2013** (ref [28]), the paper that recast CDCL conflict-analysis as abstract interpretation: **LDT is the neural sequel to his own thesis line.** Alfarano (Axiom). **Santolucito (Barnard/Columbia) = programming-languages / formal-methods.** This is the **PL ∩ SAT ∩ abstract-interpretation** community — the same intellectual neighborhood as graphplay's certificate program, and a community that values *machine-checked soundness* (so a Lean note lands well).
- **`axiommathai` / `lcrh`.** `axiommath.ai` is Haller's affiliation ("Axiom"); the GitHub org `lcrh` = his initials (Leopold C. R. Haller). These are *Haller*, not ember.
- **Is ember connected?** **Not in the artifact.** Exhaustive grep of the repo (code, `pyproject.toml`, `uv.lock`, README, git log/shortlog) and the paper finds **zero** occurrences of `ember`, `arlynx`, `lunar.town`, or `cmr://`. The single git author is Haller. **The "cmr://ember" repost in the social thread is a community-graph signal only** — it places ember *adjacent* to this AI-for-reasoning / abstract-interpretation scene (plausibly via the catgrad / formal-methods overlap), but ember is **not** an author or contributor here. Treat the connection as *social proximity worth leveraging for outreach*, not *prior involvement*.
- **Outreach read.** The strongest, most honest pitch to this group is **not** "graphplay subsumes LDT" (false) but **"here is the machine-checked soundness skeleton your empirical-soundness claim is missing, built on a verified coalgebraic run-invariant, and here is the clean lfp/gfp duality between your deduction and Weisfeiler–Leman."** That is true, narrow, and exactly the currency (precision/proof) this community trades in.

---

## 5. One-paragraph honest summary

LDT is a *bona fide* abstract-interpretation construction (explicit Galois connection `α(S')(i)={s(i):s∈S'}` ⊣ `γ(a)={s:∀i s(i)∈a(i)}`; best transformer `dedₚ=α∘(·∩‖p‖)∘γ`; gfp-Kleene descent from ⊤ with well-founded termination; learned per-step narrowing; CLS/empty-cell conflict→reset backtracking; on-policy `α(surviving)` supervision over a replay pool). Its lattice is an **over-approximation / information** lattice — the *dual species* of graphplay's **exact equitable-quotient** lattice. The real, usable connection is **not** the quotient (wrong lattice kind) and **not** the spectral gap (no iterated linear operator → bridge (ii) is superficial and self-falsifying), but the **abstract-interpretation idiom itself**: a short Lean note proving **run-level soundness of learned lattice-deduction**, built on the *one* graphplay asset that fits — **Tower-8's verified `stepInv_preserved` run-invariant** — plus the **lfp(WL)/gfp(deduction) Kleene duality** as honest positioning. That note is the single sharpest next move; the persvati spectral experiment is not.
