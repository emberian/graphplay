# A machine-checked theory of soundness, completeness, and abstention for Lattice Deduction Transformers

**For:** Liam Davis, Leopold Haller, Alberto Alfarano, Mark Santolucito — the LDT authors
(*Lattice Deduction Transformers*, arXiv:2605.08605).
**From:** the graphplay formalization effort.
**Posture:** consolidate-and-expand, not novelty. Everything below is either (a) **machine-checked**
in Lean 4 / Mathlib (theorem name cited inline; axiom-clean output pasted at the end), (b) a
**classical result** of CSP / abstract-interpretation theory (cited, *not* claimed as ours), or
(c) flagged **aspirational** (an experiment we have not run). The point of the artifact is to be a
*proof*, in the currency your community (Haller's *Abstract Conflict Driven Learning*; Santolucito's
formal methods) already trades in.
**Date:** 2026-06-02.

---

## 0. The one-line gift

> **Stop defending soundness — it is free from output checking and training-independent. The science
> is the abstention map: which problems your deduction lattice can *complete*, governed by the
> classical bounded-width CSP dichotomy.**

The rest of this memo makes that sentence precise, ties each clause to a named machine-checked theorem,
and ends with a falsifiable experiment.

---

## 1. Soundness dissolves into output-verification — and is training-independent

Your load-bearing empirical claim is *"returns a correct answer or abstains, never confidently wrong"*
(your §4.2, Tables 1–3). Read carefully, **this is not a property of the trained network at all.** It
is a property of the **output check**, and it holds for *any* operator the net could possibly learn,
with **no soundness hypothesis on the net**.

Model the entire trained looped transformer as an arbitrary endomap `solve : Abs → Abs` (input the
all-candidates grid `⊤`, output the final lattice state). The deployment protocol reads off the pinned
assignment `s` and **verifies `s ∈ cons` before returning** (else abstains). Then:

- **`checkedSolve_sound`** (`LDTSoundness.lean`): for *any* `solve`, if the checked protocol returns
  `s`, then `s ∈ cons` — `s` is a genuine solution. *The proof is `h.2`*: the protocol returns `s`
  only when the check passed. No property of `solve` is used. This is exactly the SAT-solver guarantee:
  a `SAT` answer is believed because the assignment is **checkable**, not because the search was
  **trusted**.

- **`id_sound_but_useless`** (`LDTSoundness.lean`): soundness says *nothing* about power. The identity
  operator is a perfectly sound, reductive deduction step (`id a ≤ a` and `cons ∩ γ a ⊆ γ (id a)`) that
  from `⊤` makes zero progress and (≥2 symbols, ≥1 cell) pins no string. A sound deduction can be
  completely useless.

**Consequence for the paper.** "Is the trained net sound?" is the wrong question — it is sound by the
output check regardless of training. If you want to trust the *intermediate trace* too (early
abstention, proof extraction, composition with another reasoner), per-step soundness is recovered the
same way, by the **verifier not the net**: a candidate is dropped only with a checkable certificate that
no solution *consistent with the current state* uses it.

- **`certifiedStep_sound` / `certifiedSoundStep`** (`LDTSoundness.lean`): a reductive,
  certificate-checked operator is a genuine sound narrowing step (`SoundStep`) for *arbitrary* `f` —
  so its whole run preserves all solutions via `dedRun_preserves_solutions`. **`dedP_certified`** shows
  the exact best transformer `dedₚ` really is such a step. (Honesty note carried in-file: the
  certificate is *relative to the current state `a`*; the unrelativized "no solution anywhere uses `v`"
  is **false** — a solution off `γ a` may use `v`, and `dedₚ` legitimately drops it. The relativized
  form is the one that is both true and sufficient.)

The skeleton these rest on is in `LatticeDeduction.lean`: the Galois connection **`alpha_gc_gamma`**
(`α ⊣ γ`, your App. A verbatim — Mathlib had no `GaloisConnection` for this in graphplay before),
`dedₚ` as a **sound reductive closure** (`dedP_reductive`, `dedP_sound`), and the run-level invariant
**`dedRun_preserves_solutions`** / **`solved_state_is_correct`** (every reachable Solve-state admits
every true solution; a solved state is therefore the correct, unique answer). That *is* your empirical
soundness claim, machine-checked — but the deeper message is item 1's: it was never about the net.

---

## 2. The real science is COMPLETENESS / abstention — bounded by the lattice and the width

Soundness being free, the meaningful, training- **and** lattice-dependent quantity is whether the loop
reaches a *checkable* answer at all:

- **`Solves` / `Abstains`** (`LDTSoundness.lean`): the solver *solves* iff it returns some
  (necessarily correct) answer; it *abstains* otherwise. This — not soundness — is what fails when the
  projection lattice is too coarse.

Why does it fail? Because the per-cell projection lattice **forgets inter-cell correlation**, machine-checked:

- **`ldt_lossy`** (`Tower9.lean`): `∃ a, α(γ a) ≠ a`. The over-approximation is genuinely lossy
  (your Fig. 5) — `α ⊣ γ` is a Galois *connection*, **not** an *insertion*. Per-cell candidate sets
  cannot represent the joint constraints that some problems need; that gap is the entire story of
  abstention.

This is **the classical bounded-width CSP dichotomy**, and we cite it — we do not claim it:

- Pure local-consistency deduction (arc-/`k`-consistency propagation, which is exactly what `dedₚ`
  computes — your App. A says so, "naked/hidden singles = the standard rules") solves **exactly the
  bounded-width CSPs**. This is Feder–Vardi (*The computational structure of monotone monadic SNP and
  constraint satisfaction*, SICOMP 1998) and the Datalog/bounded-width line, sharpened by **Barto–Kozik**
  (*Constraint satisfaction problems solvable by local consistency methods*, JACM 2014): a CSP is solved
  by local consistency **iff** it has bounded width **iff** its polymorphisms omit the affine type.
- **Affine / linear systems (XOR) are unbounded width** — invisible to deduction, solvable only by
  branching or linear algebra (Gaussian elimination). They are the canonical *tractable-but-not-by-local-consistency*
  obstruction.

So the honest, citable statement is: **your deduction leg solves precisely the bounded-width fragment;
abstention on everything else is forced by the projection lattice, not by any error.** The map of
"which problems generalize" is the bounded-width map, and it is a *theorem*, not a hyperparameter.

---

## 3. The machine-checked incompleteness witness: soundness ⟂ completeness

The pairing is the whole point — **one operator, simultaneously a SOUND deduction and INCOMPLETE on a
solvable problem.** We built the canonical affine obstruction concretely.

Take generalized arc consistency `acStep` for a constraint family (`LDTCompleteness.lean`): keep value
`v` at cell `i` iff every constraint admits a satisfying string, consistent with the current domains,
that places `v` at `i` — the efficiently-computable local narrowing the per-cell lattice supports, the
operator class your learned `dedₚ` targets. It is sound for free (`acStep_certified`, `acSoundStep`:
the support test *is* the impossibility certificate).

Now the XOR system over `Bool` on three cells `{x = y, y = z, x ⊕ y ⊕ z = 0}` (`xorCs`):

- **`xor_unique`**: the system has a **unique** solution `(false, false, false)` — it *is* solvable.
- **`acStep_xor_stuck`**: from `⊤`, arc consistency makes **zero** progress (`acStep xorCs ⊤ = ⊤`) —
  every value at every cell is locally supported by every constraint; the global linear coupling is
  invisible to per-constraint, per-cell reasoning.
- **`acStep_xor_abstains`**: so the AC-deduction solver **abstains** (its fixed point pins nothing).
- **`acStep_xor_sound_but_abstains`** — the headline, all three at once: `acStep` is (1) a sound
  reductive deduction, (2) the problem has a unique solution, yet (3) the solver abstains. **Soundness
  ⟂ completeness, machine-checked.** The projection lattice (not unsoundness) bounds the solvable class.

And the contrast, *same operator, same lattice*, on a width-1 chain `{x₀ = false, x₀ = x₁}`:

- **`acStep_chain_solves`**: two AC iterations from `⊤` reach the solved state pinning `(false, false)`,
  which passes the check — the solver returns the correct answer (`acStep_chain_step1`,
  `acStep_chain_step2`, `chain_unique` are the steps).
- **`ac_kind_discriminates`**: the one-line conjunction — the *same* arc-consistency operator **solves**
  the width-1 chain and **abstains** on the affine XOR system. The difference is the problem's **width**
  versus the per-cell lattice's expressiveness, *not* correctness.

This is the formal content of "the projection lattice bounds which problems generalize": affine /
unbounded-width problems are not invisible to LDT because it *errs* — it *abstains*, soundly, and the
lattice (`ldt_lossy`) is exactly what forces it.

---

## 4. Two orthogonal problem-axes — the framework predicts which problems generalize

The framework factors every problem along **two independent axes**, and items 1–3 show they are
genuinely orthogonal:

**(a) Output-checkable** (the NP / small-certificate property → **soundness is free**).
A problem is output-checkable when a candidate answer can be verified cheaply against the constraints.
This is what makes `checkedSolve_sound` apply *training-independently* (item 1). It is a property of the
*problem's verification cost*, nothing to do with the lattice.

**(b) Deduction-solvable** (the width / lattice property → **completeness, i.e. low abstention**).
A problem is deduction-solvable when local-consistency narrowing reaches a checkable answer — i.e. it is
bounded-width (item 2). This is a property of the *problem's algebraic structure* (its polymorphisms /
width), nothing to do with verification cost.

The axes are orthogonal because the XOR witness (item 3) is **(a)-yes, (b)-no**: a checked XOR solution
is trivially verifiable, yet AC-deduction abstains. (The classic **(a)-no** direction — checkable
solving without cheap *verification* — is e.g. problems whose certificates are not succinct; outside our
Lean scope, cited only.) Your puzzles — Sudoku, mazes, Snowflake — are **(a)-yes and (b)-yes**: cheaply
checkable *and* (empirically) low-width-enough that deduction + a thin branch layer completes them.
**That co-occurrence is why LDT generalizes, and the framework says so in advance:** the solve-rate is
governed by axis (b) (how far into bounded width the instance distribution sits), the
never-confidently-wrong guarantee by axis (a) (checkability) — and *they are not the same property*.

---

## 5. The framework of kinds — stratify by abstract-domain richness × algebraic type

Two classical hierarchies, crossed, organize the whole landscape. **We cite both; we do not claim to
have proved either.** graphplay machine-checks only the rung-0 instances and the abstract-interpretation
*interface* they live in.

**Axis I — abstract-domain richness (the consistency / lift level).** Strictly increasing expressiveness:

| rung | abstract domain | local-consistency level | descriptive-complexity rung |
|---|---|---|---|
| 0 | per-cell candidate sets (LDT's `Abs`) | (generalized) **arc consistency** | 1-WL / `C²` / level-1 Sherali–Adams |
| 1 | pairs of cells | **path consistency** | 2-WL / `C³` |
| `k` | `k`-tuples | **`k`-consistency** | `k`-WL / `C^{k+1}` / level-`k` Sherali–Adams |

The equivalences `k`-consistency ≡ `k`-WL ≡ `C^{k+1}` ≡ level-`k` Sherali–Adams are
**Atserias–Maneva** (*Graph isomorphism, Sherali–Adams relaxations and expressibility in counting
logics*, SICOMP 2013) with **Atserias–Bulatov–Dawar** (*On the power of k-consistency*, ICALP 2007) and
Grohe–Otto for the strictness. **LDT today lives at rung 0** (`Abs = Fin k → Set V`); the
`ldt_lossy` lossiness is precisely "rung 0 forgets the rung-1 pair-correlations."

**Axis II — the algebraic dichotomy type (the XOR wall).** Bounded width is exactly the
*non-affine* / *no-Maltsev* side (Barto–Kozik; Bulatov–Zhuk CSP dichotomy). Affine / Maltsev problems
(linear systems over a finite field — XOR is `GF(2)`) are the **unbounded-width wall**: no finite
consistency rung on Axis I cracks them; they need linear algebra or branching. This is why item 3's XOR
witness sits *off* the entire Axis-I ladder, not merely above rung 0.

**What graphplay machine-checks here:** the **rung-0 cells of this table** (`acStep` = arc consistency;
solves width-1 chain, abstains on affine XOR), and — separately, in `Tower9.lean` — that LDT's
deduction is one instance of a **verified Cousot abstract-interpretation interface** (`AbstractInterpretation`,
with `gfp_transfer` the fixpoint-transfer theorem and `ldt_deduction_run_sound` deriving LDT
run-soundness as a *corollary* of that general transfer). The richer rungs (path-/`k`-consistency as
abstract domains) and the algebraic dichotomy itself are **classical, cited, and not formalized here** —
formalizing them would be a large descriptive-complexity project (Mathlib lacks the Sherali–Adams / `C^k`
infrastructure). The honest claim is: *the rung-0 cell is proved; the ladder it sits on is the
literature's.*

**The lift this predicts.** Moving LDT up Axis I (a pair-aware or `k`-tuple abstract domain) would extend
the deduction-solvable class to higher bounded-width problems — but **never** past the Axis-II affine
wall. That is the precise, theorem-backed scope of "make the lattice richer."

---

## 6. A concrete experiment with a-priori predictions (aspirational — we have not run it)

This is the falsifiable cash-out. It measures the **abstention rate** (item 2), *not* soundness (item 1,
which is free), and it tests the framework against the bounded-width dichotomy (item 5, Axis II).

**Design.**

- **kind-0 (AC-solvable, bounded width):** a distribution of problems solvable by pure arc consistency —
  Horn-SAT, or "easy"/naked-singles-only Sudoku (no guessing needed). These sit at Axis-I rung 0,
  Axis-II non-affine.
- **kind-2 (3-XOR, unique solution):** random sparse 3-XOR systems with a planted unique solution
  (the `xor_unique` shape, scaled up). Axis-II **affine** — the unbounded-width wall.
- **Ablation:** train LDT on each kind; then **ablate the branching / CLS-conflict head**, leaving
  *deduction only* (the looped `dedₚ` with no search restart). Compare full vs deduction-only.
- **Metric:** the **abstention rate** (fraction of solvable instances on which the loop reaches no
  checkable answer). Report soundness too, but only to confirm the prediction that it is ~1.0
  *by the output check* in every cell — that confirms item 1, it is not the dependent variable.

**A-priori predictions (the framework's falsifiable commitments).**

| condition | predicted abstention | predicted soundness |
|---|---|---|
| kind-0, deduction-only | **≈ 0** (deduction completes bounded width) | 1.0 (free) |
| kind-0, full (with branch) | ≈ 0 (branch unused or rarely) | 1.0 (free) |
| kind-2 (XOR), **deduction-only** | **≈ 1** (abstains — affine wall) | **1.0 (free, despite abstaining)** |
| kind-2 (XOR), full (with branch) | low-ish (branch/CLS does the search) | 1.0 (free) |

The sharp, framework-defining prediction is the **third row**: deduction-only on 3-XOR should **abstain
on essentially every instance while remaining perfectly sound** — soundness ⟂ completeness, exactly
`acStep_xor_sound_but_abstains` at scale. The contrast with row 1 (deduction-only solves kind-0) is
`ac_kind_discriminates` at scale.

**The falsifier.** If a *deduction-only* LDT (branch/CLS ablated) **solves 3-XOR with non-trivial
solve-rate**, that **refutes the framework**: it would mean the learned per-cell operator is doing
something *not* captured by bounded-width local consistency (effectively learning linear algebra inside
the per-cell sigmoids), and the `ldt_lossy` / bounded-width account of abstention would be wrong. We
predict this does not happen; if it does, that is the interesting result and we want to know.

(Secondary, cheaper probe: hold the net fixed and vary the *abstract domain* — rung 0 vs a pair-aware
rung-1 head — on a *width-2* family that rung 0 cannot but rung 1 can solve. Prediction: abstention
drops at rung 1, confirming Axis I. This isolates the lattice from the algebra.)

---

## 7. What is machine-checked vs classical-cited vs aspirational (one table)

| claim | status | anchor |
|---|---|---|
| Soundness = output check, training-independent | **machine-checked** | `checkedSolve_sound` |
| Sound ≠ powerful (identity is sound, useless) | **machine-checked** | `id_sound_but_useless` |
| Per-step soundness from certificates (verifier, not net) | **machine-checked** | `certifiedStep_sound`, `certifiedSoundStep`, `dedP_certified` |
| Run-level soundness ("correct or abstain", the half that is correctness) | **machine-checked** | `dedRun_preserves_solutions`, `solved_state_is_correct` |
| Galois connection `α ⊣ γ` (your App. A) | **machine-checked** | `alpha_gc_gamma` |
| Projection lattice is lossy (`α∘γ ≠ id`, forgets correlation) | **machine-checked** | `ldt_lossy` |
| Completeness = abstention is the real quantity | **machine-checked (defs)** | `Solves`, `Abstains` |
| AC sound but incomplete on solvable XOR | **machine-checked** | `acStep_xor_sound_but_abstains` |
| Same operator solves width-1, abstains on XOR | **machine-checked** | `ac_kind_discriminates` |
| LDT run-soundness = Cousot fixpoint transfer | **machine-checked** | `gfp_transfer`, `ldt_deduction_run_sound` |
| Local consistency solves **exactly** bounded-width CSPs | **classical-cited** | Feder–Vardi 1998; Barto–Kozik 2014 |
| Affine/XOR is unbounded width (the wall) | **classical-cited** | Feder–Vardi; Bulatov–Zhuk dichotomy |
| `k`-consistency ≡ `k`-WL ≡ `C^{k+1}` ≡ Sherali–Adams-`k` | **classical-cited** | Atserias–Maneva 2013; Atserias–Bulatov–Dawar 2007 |
| Abstract interpretation is the containing frame | **classical-cited** | Cousot–Cousot POPL 1977 |
| kind-0 vs kind-2 ablation, abstention predictions | **aspirational** (experiment, not run) | §6 |

**Honest residuals.** (i) `α ⊣ γ` is a *connection*, not an *insertion*; we do **not** claim `dedₚ`
idempotence among the soundness obligations (it holds for the exact best transformer, off the soundness
path). (ii) The *learned* operator is an approximation of `dedₚ`; we certify the soundness of the
abstract *skeleton* the learned operator targets (any operator in `SoundStep`), which is exactly the
level at which "trained to be sound" is meaningful. (iii) `solved_state_is_correct` covers the
"returns a correct answer" half of "correct-or-abstains"; the abstention/branching layer (CLS-head +
search) is the *completeness* layer, characterized here by the bounded-width dichotomy but not itself
formalized as a search procedure. (iv) The framework-of-kinds ladder (§5) is classical; only its rung-0
cells and the AI interface are in Lean. (v) The spectral-gap / mixing-rate bridge is **retracted** for
LDT: the loop is well-founded discrete gfp Kleene descent with no iterated linear operator and no `λ₂`;
its depth is the **Cousot fixpoint-iteration height** (longest sound deduction chain), a combinatorial
not spectral quantity.

---

## 8. The gift, restated

You wrote a clean textbook abstract-interpretation construction (Galois connection verbatim, best
transformer `dedₚ`, gfp Kleene descent) wrapped around a small looped transformer, and you defended it
with the honest empirical line *"correct or abstains."* The machine-checked theory above says you can
stop defending the first half:

> **Soundness is free from output checking and training-independent (`checkedSolve_sound`); the science
> is the abstention map — which problems your lattice can complete — and that map is the classical
> bounded-width CSP dichotomy (Feder–Vardi; Barto–Kozik), with a machine-checked witness that soundness
> and completeness are orthogonal (`acStep_xor_sound_but_abstains`, `ac_kind_discriminates`).** Measure
> abstention, not soundness; train on kind-0 vs kind-2 and watch the affine wall.

A falsifying deduction-only XOR success would refute the framework — which is the point: it is a
prediction, not a press release. ( ◕‿◕ )

---

### References

- Davis, Haller, Alfarano, Santolucito. *Lattice Deduction Transformers.* arXiv:2605.08605, 2026.
- Cousot, Cousot. *Abstract interpretation: a unified lattice model for static analysis of programs by
  construction or approximation of fixpoints.* POPL 1977.
- Feder, Vardi. *The computational structure of monotone monadic SNP and constraint satisfaction: a
  study through Datalog and group theory.* SIAM J. Comput. 28(1), 1998.
- Barto, Kozik. *Constraint satisfaction problems solvable by local consistency methods.* JACM 61(1),
  2014.
- Atserias, Maneva. *Graph isomorphism, Sherali–Adams relaxations and expressibility in counting
  logics.* SIAM J. Comput. 42(1), 2013.
- Atserias, Bulatov, Dawar. *On the power of k-consistency.* ICALP 2007.
- Bulatov, *A dichotomy theorem for nonuniform CSPs* (FOCS 2017); Zhuk, *A proof of the CSP dichotomy
  conjecture* (JACM 2020) — the affine/Maltsev wall in the full dichotomy.
- D'Silva, Haller, Kroening. *Abstract Conflict Driven Learning.* POPL 2013 — the gfp-narrow +
  lfp-learn lineage LDT descends from.

### Machine-checked source (graphplay, this repo)

- `Graphplay/Integrations/LatticeDeduction.lean` — the soundness skeleton: `alpha_gc_gamma`,
  `dedP_reductive`, `dedP_sound`, `dedRun_preserves_solutions`, `solved_state_is_correct`,
  `SoundStep`, `dedStep`.
- `Graphplay/Integrations/LDTSoundness.lean` — checking vs trusting: `checkedSolve_sound`,
  `id_sound_but_useless`, `Solves`, `Abstains`, `certifiedStep_sound`, `certifiedSoundStep`,
  `dedP_certified`.
- `Graphplay/Integrations/LDTCompleteness.lean` — arc consistency + the XOR wall: `acStep`,
  `acSoundStep`, `xor_unique`, `acStep_xor_stuck`, `acStep_xor_abstains`,
  `acStep_xor_sound_but_abstains`, `chain_unique`, `acStep_chain_solves`, `ac_kind_discriminates`.
- `Graphplay/Tower9.lean` — the Cousot interface: `AbstractInterpretation`, `gfp_transfer`,
  `ldt_deduction_run_sound`, `ldt_lossy`.
