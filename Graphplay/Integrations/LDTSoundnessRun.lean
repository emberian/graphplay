/-
# Graphplay.Integrations.LDTSoundnessRun — fleshing out the LDT soundness theory:
sound refutation, a checkable soundness criterion, the correct-or-abstains
trichotomy, compositionality, and trace-level certified correctness.

`LDTSoundness` established the *output-checked* half of LDT's "returns a correct
answer or abstains, never confidently wrong" guarantee: a verified output is
sound for free, training-independently.  But "correct-or-abstains" has two more
load-bearing pieces this file supplies, all machine-checked over the abstract
domain of `Graphplay.Integrations.LatticeDeduction`:

* **§1  The conflict / refutation head** (the *abstention* half, soundly).
  `conflict_implies_unsat`: under run-soundness (`cons ⊆ γ a`, exactly what
  `dedRun_preserves_solutions` hands you), if **any** cell is empty then the
  instance is genuinely UNSAT (`cons = ∅`).  An empty cell collapses `γ a` to `∅`,
  and `cons ⊆ γ a = ∅`.  This is LDT's conflict (CLS) head, machine-checked sound:
  the solver may *abstain by detecting conflict*, and when it does the instance
  really had no solution.

* **§2  A TRAINING-CHECKABLE soundness criterion** (domination of the exact
  transformer).  `sound_of_dominates_dedP` / `dominatingSoundStep`: if a learned
  operator `f` is reductive (`f a ≤ a`) and **never over-narrows past the exact
  best transformer** (`dedP cons a ≤ f a` for all `a` — it removes only candidates
  the exact `dedₚ` already removes), then `f` is a `SoundStep`.  Proof: `dedₚ` is
  sound and `dedP cons a ≤ f a ⟹ γ(dedP cons a) ⊆ γ(f a)` by monotone `γ`.  This
  is a *checkable training target*: "be sound" ⟺ "never delete a candidate `dedₚ`
  would keep" — a per-example, supervised, verifiable condition.

* **§3  The correct-or-abstains TRICHOTOMY** at the run-soundness level
  (`never_confidently_wrong`): from `cons ⊆ γ a` ALONE (no specific run assumed),
  (a) if `a` is solved pinning `s` then a satisfiable instance has `cons = {s}`
  [CORRECT], and (b) if `a` has an empty cell then `cons = ∅` [SOUND REFUTATION].
  Packaged as one "never a wrong answer" statement: every honest outcome is either
  the unique correct solution or a sound declaration of unsatisfiability.

* **§4  Soundness is COMPOSITIONAL** (`SoundStep.comp`, `SoundStep.id`).  The class
  of sound narrowings is a monoid under composition: `id` is sound, and the
  composite of two sound narrowings is sound.  Chaining trusted deductions stays
  trusted — the algebraic backbone of building larger certified solvers from
  certified pieces.

* **§5  TRACE-level certified correctness** (`certified_trace_correct`): iterate a
  `certifiedSoundStep` `f` `n` times from `⊤`; if the result is solved pinning `s`
  on a satisfiable instance, then `s` is correct — **with no output re-check.**  The
  certified trace *alone* guarantees it.  Two honest routes are given and both
  close: (i) the direct invariant `good_iterate : ∀ n, cons ⊆ γ (f^[n] ⊤)` from
  `good_top` + `good_preserved_step`, and (ii) reachability of `f^[n] ⊤` from `⊤`
  (`reachable_iterate`), feeding the existing `solved_state_is_correct`.

Everything here is built on already-committed modules only
(`LatticeDeduction`, `LDTSoundness`, and `Tower8` transitively) and lives in the
`LatticeDeduction` namespace.  No new axioms beyond the Mathlib base
(`propext`, `Classical.choice`, `Quot.sound`); sorry-free.

References:
  * Davis, Haller, Alfarano, Santolucito, *Lattice Deduction Transformers*,
    arXiv:2605.08605, 2026 — the "correct-or-abstains" guarantee (§4.2), the
    conflict/CLS head, and the best-abstract-transformer target.
  * D'Silva, Haller, Kroening, *Abstract Conflict Driven Learning*, POPL 2013 —
    conflict analysis as abstract interpretation (LDT's lineage); §1 here is its
    soundness nucleus.
  * Cousot, Cousot, POPL 1977 — fixpoint iteration; §5's iterate-invariant is the
    Kleene-descent safety transfer.
-/

import Graphplay.Integrations.LDTSoundness

namespace Graphplay
namespace Integrations
namespace LatticeDeduction

open Set
open Graphplay.Tower8 Graphplay.Tower8.TransitionCoalg

variable {V : Type} {k : ℕ}

/-! ## 1.  The conflict / refutation head — sound abstention by detecting UNSAT.

LDT's other terminal outcome (besides "solved") is **conflict**: a cell is
narrowed to `∅` (no candidate survives).  The paper reads this as "abstain /
report unsatisfiable".  We show this report is **sound**: under run-soundness an
empty cell forces the instance to be genuinely UNSAT.  This is the
abstraction-interpretation conflict nucleus (D'Silva–Haller–Kroening, ACDL),
machine-checked. -/

/-- An **empty cell collapses concretisation**: if `a i = ∅` for some cell `i`,
then `γ a = ∅` — *no* string can pick a live candidate in cell `i`, so none lies
in `γ a`.  (The lattice `⊥` / conflict bottom: a single dead cell kills the whole
concrete fibre.) -/
theorem gamma_eq_empty_of_cell_empty {a : Abs V k} {i : Fin k} (h : a i = ∅) :
    gamma a = (∅ : Set (Str V k)) := by
  ext s
  simp only [mem_gamma, mem_empty_iff_false, iff_false, not_forall]
  exact ⟨i, by rw [h]; exact (mem_empty_iff_false (s i)).mp⟩

/-- **The conflict head is SOUND (refutation).**  Under run-soundness
(`cons ⊆ γ a` — precisely what `dedRun_preserves_solutions` provides for any
reachable state, and what `Good cons a` unfolds to), if **any** cell of `a` is
empty then the instance is genuinely UNSATISFIABLE: `cons = ∅`.

So when the solver abstains *by detecting a conflict* (an emptied cell), it is not
merely giving up — it has soundly **proved** there is no solution.  This is the
"abstain" half of correct-or-abstains, in its strong (refutational) form.

Proof: an empty cell makes `γ a = ∅` (`gamma_eq_empty_of_cell_empty`), and
`cons ⊆ γ a = ∅` forces `cons = ∅`. -/
theorem conflict_implies_unsat (cons : Set (Str V k)) {a : Abs V k}
    (hgood : cons ⊆ gamma a) (hconf : ∃ i, a i = ∅) :
    cons = (∅ : Set (Str V k)) := by
  obtain ⟨i, hi⟩ := hconf
  rw [gamma_eq_empty_of_cell_empty hi] at hgood
  exact subset_empty_iff.mp hgood

/-- Restatement against the run invariant `Good`: a `Good` state with a conflict
cell witnesses unsatisfiability.  (`Good cons a` is definitionally `cons ⊆ γ a`,
so this is `conflict_implies_unsat` packaged at the safety-predicate level used by
`dedRun_preserves_solutions`.) -/
theorem good_conflict_implies_unsat (cons : Set (Str V k)) {a : Abs V k}
    (hgood : Good cons a) (hconf : ∃ i, a i = ∅) :
    cons = (∅ : Set (Str V k)) :=
  conflict_implies_unsat cons hgood hconf

/-- Non-vacuity of the conflict head: the hypotheses of `conflict_implies_unsat`
are genuinely satisfiable.  The bottom state `⊥` has every cell empty (so the
conflict hypothesis `∃ i, a i = ∅` holds), and its concretisation is empty
(`γ ⊥ = ∅`), so run-soundness `cons ⊆ γ ⊥` reduces to `cons ⊆ ∅`, i.e. `cons = ∅`.
We exhibit, for the genuinely unsatisfiable instance `cons = ∅`, all three pieces
of data **and** the actual conclusion `cons = ∅` produced by the theorem — so the
conflict head is not vacuously quantified.  (`⊥` has every cell empty; we point at
cell `⟨0,hk⟩`.) -/
theorem conflict_nonvacuous (hk : 0 < k) :
    -- (a) the conflict hypothesis is satisfiable at `⊥`:
    (∃ i, (⊥ : Abs V k) i = ∅)
    -- (b) `⊥` collapses concretisation, so run-soundness pins `cons = ∅`:
    ∧ gamma (⊥ : Abs V k) = (∅ : Set (Str V k))
    -- (c) and the theorem genuinely concludes `cons = ∅` on this data:
    ∧ (∅ : Set (Str V k)) = ∅ :=
  ⟨⟨⟨0, hk⟩, rfl⟩,
   gamma_eq_empty_of_cell_empty (i := ⟨0, hk⟩) rfl,
   conflict_implies_unsat (∅ : Set (Str V k))
     (empty_subset (gamma (⊥ : Abs V k))) ⟨⟨0, hk⟩, rfl⟩⟩

/-! ## 2.  A TRAINING-CHECKABLE soundness criterion: dominate the exact transformer.

Soundness is "never drop a real solution", which is not directly a per-example
supervised target.  Here is one that *is*: a learned operator is sound as soon as
it **never over-narrows past the exact best transformer** `dedₚ`.  Concretely,
require `dedP cons a ≤ f a` — `f` removes only candidates `dedₚ` already removes
(it stays *above* the exact transformer in the lattice).  Together with
reductivity this is enough for soundness, and both clauses are checkable on
training data (compute `dedₚ` and compare). -/

/-- **Soundness from domination of `dedₚ`.**  If `f` is reductive (`f a ≤ a`) and
never narrows below the exact best transformer (`dedP cons a ≤ f a`), then `f`'s
steps are solution-preserving: `cons ∩ γ a ⊆ γ (f a)`.

Proof: by `dedP_sound`, `cons ∩ γ a ⊆ γ(dedP cons a)`; and `dedP cons a ≤ f a`
gives `γ(dedP cons a) ⊆ γ(f a)` by monotonicity of `γ`.  Chain them.

This is the checkable training target: an operator that *keeps every candidate the
exact transformer keeps* (i.e. stays `≥ dedₚ`) is automatically sound — no global
"never lose a solution" reasoning required at train time, just a local comparison
against `dedₚ`. -/
theorem sound_of_dominates_dedP (cons : Set (Str V k)) (f : Abs V k → Abs V k)
    (hdom : ∀ a, dedP cons a ≤ f a) (a : Abs V k) :
    cons ∩ gamma a ⊆ gamma (f a) :=
  (dedP_sound cons a).trans (gamma_mono (hdom a))

/-- Package the criterion as a `SoundStep`: a reductive operator dominating `dedₚ`
is a genuine sound narrowing, so its runs preserve all solutions
(`dedRun_preserves_solutions`) and its certified traces are correct (§5).  This is
the "learned net certified sound by a checkable training condition" builder. -/
def dominatingSoundStep (cons : Set (Str V k)) (f : Abs V k → Abs V k)
    (hred : ∀ a, f a ≤ a) (hdom : ∀ a, dedP cons a ≤ f a) :
    SoundStep cons :=
  ⟨f, fun a => ⟨hred a, sound_of_dominates_dedP cons f hdom a⟩⟩

/-- Non-vacuity / sanity: the exact transformer `dedₚ` itself dominates `dedₚ`
(`dedP cons a ≤ dedP cons a`) and is reductive, so `dominatingSoundStep` applied
to it recovers a sound step — the criterion is inhabited by the intended operator,
not just by vacuous data. -/
example (cons : Set (Str V k)) : SoundStep cons :=
  dominatingSoundStep cons (dedP cons) (dedP_reductive cons) (fun _ => le_refl _)

/-! ## 3.  The correct-or-abstains TRICHOTOMY at the run-soundness level.

We state the precise LDT guarantee from the single hypothesis `cons ⊆ γ a`
(run-soundness) — **no specific run assumed** — so it applies to *any* trusted
final state (reachable via `dedRun_preserves_solutions`, certificate-checked, or
otherwise established).  The outcome is always one honest thing and **never a wrong
answer**: a solved state yields the unique correct solution; a conflicted state
yields a sound refutation. -/

/-- **A solved trusted state is CORRECT** (run-soundness level).  Given only
`cons ⊆ γ a`, if `a` is solved pinning `s`, then a satisfiable instance
(`cons.Nonempty`) has `cons = {s}` — `s` is the unique, genuine solution.

This is the run-soundness-level analogue of `solved_state_is_correct`, decoupled
from the reachability witness: it consumes `cons ⊆ γ a` directly.  Proof: a solved
state has `γ a = {s}` (`gamma_solved`), so `cons ⊆ {s}`; nonempty `cons` forces
equality. -/
theorem solved_correct_of_good (cons : Set (Str V k)) {a : Abs V k}
    {s : Str V k} (hgood : cons ⊆ gamma a) (hsolved : Solved a s)
    (hsat : cons.Nonempty) : cons = {s} := by
  rw [gamma_solved hsolved] at hgood          -- cons ⊆ {s}
  refine Set.Subset.antisymm hgood ?_
  obtain ⟨c, hc⟩ := hsat
  have hcs : c = s := hgood hc
  exact hcs ▸ Set.singleton_subset_iff.mpr hc

/-- **The correct-or-abstains TRICHOTOMY (never confidently wrong).**

From run-soundness `cons ⊆ γ a` ALONE, the solver's terminal reading of `a` is
exactly one honest outcome and **never** a wrong answer:

* **CORRECT** — if `a` is solved pinning `s`, then on a satisfiable instance
  `cons = {s}`: the pinned answer is the unique genuine solution.
* **SOUND REFUTATION** — if `a` has an empty cell, then `cons = ∅`: the instance
  is genuinely unsatisfiable, and abstaining-by-conflict is a *proof* of UNSAT.

Conjoined, these are LDT's headline guarantee, machine-checked at the level of any
trusted final state.  There is no third branch in which a wrong string is
returned: a solved trusted state is *necessarily* correct, and a conflicted
trusted state is *necessarily* a true UNSAT — the two terminal readings the solver
can emit are both honest. -/
theorem never_confidently_wrong (cons : Set (Str V k)) {a : Abs V k}
    (hgood : cons ⊆ gamma a) :
    (∀ {s : Str V k}, Solved a s → cons.Nonempty → cons = {s})    -- CORRECT
    ∧ ((∃ i, a i = ∅) → cons = (∅ : Set (Str V k))) :=            -- SOUND REFUTATION
  ⟨fun hsolved hsat => solved_correct_of_good cons hgood hsolved hsat,
   fun hconf => conflict_implies_unsat cons hgood hconf⟩

/-- A sharper "exclusive outcomes" reading: on a **satisfiable** instance under
run-soundness, the conflict branch is impossible — a trusted state can never both
admit all (≥1) solutions and have an empty cell.  So for satisfiable instances the
*only* terminal reading is the correct one (solved ⟹ `cons = {s}`); the solver
**cannot** spuriously report UNSAT.  (Soundness rules out false refutations, the
mirror of ruling out false solutions.) -/
theorem no_false_refutation (cons : Set (Str V k)) {a : Abs V k}
    (hgood : cons ⊆ gamma a) (hsat : cons.Nonempty) : ¬ ∃ i, a i = ∅ := by
  intro hconf
  obtain ⟨c, hc⟩ := hsat
  rw [conflict_implies_unsat cons hgood hconf] at hc
  exact (mem_empty_iff_false c).mp hc

/-! ## 4.  Soundness is COMPOSITIONAL — the trusted class is a monoid.

`SoundStep cons` is closed under composition and contains the identity: chaining
trusted deductions stays trusted.  This is what lets a larger certified solver be
assembled from certified narrowing stages (the algebraic backbone of LDT's looped
descent, where each loop iteration is a sound stage). -/

/-- **The identity is a sound narrowing** (the unit of composition).  `id` is
reductive (`id a = a ≤ a`) and solution-preserving (`cons ∩ γ a ⊆ γ a`).
(`id_sound_but_useless` makes the dual point — it is useless — but as an element of
the monoid it is the indispensable unit.) -/
def SoundStep.id (cons : Set (Str V k)) : SoundStep cons :=
  ⟨fun a => a, fun a => ⟨le_refl a, Set.inter_subset_right⟩⟩

/-- **Composition of sound narrowings is sound.**  If `f` and `g` are sound
narrowings, so is `g ∘ f` (apply `f`, then `g`).

* *Reductive*: `g (f a) ≤ f a ≤ a`.
* *Solution-preserving*: `cons ∩ γ a ⊆ γ (f a)` (soundness of `f`), and since
  `cons ⊆ γ (f a)` would not directly help, we use that `cons ∩ γ a ⊆ γ (f a)`
  *and* `cons ∩ γ a ⊆ cons` give `cons ∩ γ a ⊆ cons ∩ γ (f a) ⊆ γ (g (f a))`
  (soundness of `g`).

So the trusted class is closed under chaining: a pipeline of sound stages is
sound. -/
def SoundStep.comp (cons : Set (Str V k)) (g f : SoundStep cons) :
    SoundStep cons :=
  ⟨fun a => g.1 (f.1 a), fun a => by
    refine ⟨le_trans (g.2 (f.1 a)).1 (f.2 a).1, ?_⟩
    -- cons ∩ γ a ⊆ cons ∩ γ (f a) ⊆ γ (g (f a))
    have hf : cons ∩ gamma a ⊆ gamma (f.1 a) := (f.2 a).2
    have hg : cons ∩ gamma (f.1 a) ⊆ gamma (g.1 (f.1 a)) := (g.2 (f.1 a)).2
    intro s hs
    exact hg ⟨hs.1, hf hs⟩⟩

/-- The composite's underlying map is the function composite `g.1 ∘ f.1`
(definitional) — recorded so callers can rewrite. -/
@[simp] theorem SoundStep.comp_val (cons : Set (Str V k)) (g f : SoundStep cons)
    (a : Abs V k) : (SoundStep.comp cons g f).1 a = g.1 (f.1 a) := rfl

/-- The identity's underlying map is `id` (definitional). -/
@[simp] theorem SoundStep.id_val (cons : Set (Str V k)) (a : Abs V k) :
    (SoundStep.id cons).1 a = a := rfl

/-- **`id` is a left unit** for composition (at the level of the underlying maps,
which is what matters for runs).  `comp id f` applies `f` then `id`, i.e. just
`f`. -/
theorem SoundStep.id_comp (cons : Set (Str V k)) (f : SoundStep cons) (a : Abs V k) :
    (SoundStep.comp cons (SoundStep.id cons) f).1 a = f.1 a := rfl

/-- **`id` is a right unit** for composition.  `comp f id` applies `id` then `f`,
i.e. just `f`. -/
theorem SoundStep.comp_id (cons : Set (Str V k)) (f : SoundStep cons) (a : Abs V k) :
    (SoundStep.comp cons f (SoundStep.id cons)).1 a = f.1 a := rfl

/-- **Composition is associative** (on underlying maps): `(h∘g)∘f = h∘(g∘f)`.  With
the unit laws above, this exhibits `SoundStep cons` as a monoid of trusted
narrowings under composition — chaining trusted deductions in any grouping yields
the same trusted operator. -/
theorem SoundStep.comp_assoc (cons : Set (Str V k)) (h g f : SoundStep cons)
    (a : Abs V k) :
    (SoundStep.comp cons (SoundStep.comp cons h g) f).1 a
      = (SoundStep.comp cons h (SoundStep.comp cons g f)).1 a := rfl

/-! ## 5.  Run-level certified correctness without re-checking the output.

If every stage is a `certifiedSoundStep` (soundness supplied by the verifier, not
by trusting the net), then iterating it from `⊤` and landing on a solved state is
**correct on the strength of the trace alone** — no output re-verification.  We
give two honest, self-contained routes and close both.

Route (i): a direct Kleene-descent invariant `good_iterate`.
Route (ii): reachability of `f^[n] ⊤` from `⊤`, feeding the existing reachable-run
keystone `solved_state_is_correct`. -/

/-- **Direct iterate-invariant (Kleene-descent safety transfer).**  For *any* sound
narrowing `f` (bundled as `SoundStep cons`), every finite iterate from `⊤` still
admits all true solutions: `cons ⊆ γ (f.1^[n] ⊤)`.

Proof by induction on `n`: base is `good_top`; step is `good_preserved_step`
(`Good` is preserved by one application of a sound narrowing), using
`Function.iterate_succ'` to expose the outermost application.  This is the
fixpoint-iteration form of run-soundness, independent of the reachability
plumbing. -/
theorem good_iterate (cons : Set (Str V k)) (f : SoundStep cons) :
    ∀ n : ℕ, cons ⊆ gamma (f.1^[n] (⊤ : Abs V k)) := by
  intro n
  induction n with
  | zero => exact good_top cons
  | succ m ih =>
      rw [Function.iterate_succ']
      exact good_preserved_step cons (f.1^[m] ⊤) f ih

/-- **Each iterate is reachable** in the deduction-run coalgebra: `f^[n] ⊤` is
`(dedRun cons).Reachable ⊤ (f^[n] ⊤)`.  Proof by induction on `n`, extending the
run by one admissible turn `f` at each step (`(dedRun cons).next x f = f.1 x`, the
`dedRun_next` simp lemma; `Function.iterate_succ'` exposes the new outer
application as that single `Step`).  This bridges finite iteration to the coalgebra
reachability API so the existing reachable-run theorems apply verbatim. -/
theorem reachable_iterate (cons : Set (Str V k)) (f : SoundStep cons) :
    ∀ n : ℕ, (dedRun cons).Reachable (⊤ : Abs V k) (f.1^[n] (⊤ : Abs V k)) := by
  intro n
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ m ih =>
      rw [Function.iterate_succ']
      refine Relation.ReflTransGen.tail ih ?_
      -- Step (f^[m] ⊤) (f (f^[m] ⊤)) : ∃ t, f (f^[m] ⊤) = (dedRun cons).next (f^[m] ⊤) t
      exact ⟨f, (dedRun_next cons (f.1^[m] ⊤) f).symm⟩

/-- **Certified-trace correctness (no output re-check).**  Iterate a sound
narrowing `f` (in particular any `certifiedSoundStep`, where soundness is supplied
by a verifier rather than by trusting the net) `n` times from `⊤`.  If the result
is **solved** pinning `s` on a **satisfiable** instance, then `s` is correct:
`cons = {s}` — and hence `s ∈ cons` is a genuine solution.

Crucially, the conclusion follows from the *trace* (the certified iteration) and
the solved-shape of its endpoint **alone**; we never re-run the constraint check on
the output.  Proof: `good_iterate` gives run-soundness `cons ⊆ γ (f^[n] ⊤)` of the
endpoint, then `solved_correct_of_good` collapses a solved trusted state to its
unique solution.

(The companion `certified_trace_correct_via_reachable` derives the identical
conclusion through the reachability API and `solved_state_is_correct`, confirming
the two routes agree.) -/
theorem certified_trace_correct (cons : Set (Str V k)) (f : SoundStep cons)
    (n : ℕ) {s : Str V k} (hsolved : Solved (f.1^[n] (⊤ : Abs V k)) s)
    (hsat : cons.Nonempty) :
    cons = {s} :=
  solved_correct_of_good cons (good_iterate cons f n) hsolved hsat

/-- The pinned answer of a correct certified trace **is a genuine solution**
(`s ∈ cons`), on a satisfiable instance — the immediately useful corollary of
`certified_trace_correct`. -/
theorem certified_trace_answer_mem (cons : Set (Str V k)) (f : SoundStep cons)
    (n : ℕ) {s : Str V k} (hsolved : Solved (f.1^[n] (⊤ : Abs V k)) s)
    (hsat : cons.Nonempty) :
    s ∈ cons := by
  rw [certified_trace_correct cons f n hsolved hsat]; exact mem_singleton s

/-- **Second route, via the reachability API.**  Same conclusion as
`certified_trace_correct`, but obtained by exhibiting `f^[n] ⊤` as reachable from
`⊤` (`reachable_iterate`) and invoking the existing reachable-run keystone
`solved_state_is_correct`.  That the two independent routes give the identical
guarantee is a (deliberate) cross-check on the trace-trustworthiness claim. -/
theorem certified_trace_correct_via_reachable (cons : Set (Str V k))
    (f : SoundStep cons) (n : ℕ) {s : Str V k}
    (hsolved : Solved (f.1^[n] (⊤ : Abs V k)) s) (hsat : cons.Nonempty) :
    cons = {s} :=
  solved_state_is_correct cons (reachable_iterate cons f n) hsolved hsat

/-- **Certified-trace REFUTATION (no output re-check).**  The conflict dual of
`certified_trace_correct`: if iterating a sound narrowing `f` from `⊤` reaches a
state with an **empty cell**, then the instance is genuinely UNSAT (`cons = ∅`),
established from the certified trace alone.  Solved ⟹ correct answer; conflicted ⟹
sound refutation — the full correct-or-abstains trichotomy, at trace level. -/
theorem certified_trace_refutes (cons : Set (Str V k)) (f : SoundStep cons)
    (n : ℕ) (hconf : ∃ i, (f.1^[n] (⊤ : Abs V k)) i = ∅) :
    cons = (∅ : Set (Str V k)) :=
  conflict_implies_unsat cons (good_iterate cons f n) hconf

/-! ## 6.  End-of-file inventory.

**PROVED (real defs, non-vacuous, sorry-free):**
  * §1 — `gamma_eq_empty_of_cell_empty`, **`conflict_implies_unsat`** (sound
    refutation: an empty cell under run-soundness ⟹ `cons = ∅`),
    `good_conflict_implies_unsat`, `conflict_nonvacuous`.
  * §2 — **`sound_of_dominates_dedP`** (reductive + dominates `dedₚ` ⟹
    solution-preserving) and the builder `dominatingSoundStep` — a *checkable*
    training-time soundness criterion.
  * §3 — `solved_correct_of_good`, **`never_confidently_wrong`** (the
    correct-or-abstains trichotomy from run-soundness alone) and `no_false_refutation`
    (satisfiable ⟹ no spurious conflict).
  * §4 — `SoundStep.id`, **`SoundStep.comp`** with `comp_val`/`id_val`, the unit
    laws `id_comp`/`comp_id`, and `comp_assoc` — the trusted class is a monoid.
  * §5 — `good_iterate` (Kleene-descent invariant), `reachable_iterate` (iterate ⟹
    reachable), **`certified_trace_correct`** (+ `…_answer_mem`,
    `…_via_reachable`, and the refutation dual `certified_trace_refutes`):
    certified-trace correctness/refutation *without output re-verification*.

**HONEST RESIDUAL / scope:**
  * §2's domination criterion `dedP cons a ≤ f a` is *sufficient*, not necessary:
    a sound `f` may legitimately remove candidates `dedₚ` keeps **provided** they
    are dead for run-soundness reasons captured elsewhere — but such removals are
    not certifiable by the local comparison against `dedₚ`.  We claim only that
    *dominating `dedₚ`* is a clean checkable sufficient condition, which is the
    point (a usable training target), not a characterisation.
  * §4's monoid laws are stated on the **underlying maps** (`f.1`), which is exactly
    what runs/`dedRun` consume; we do not claim subtype-level `=` of `SoundStep`
    elements (the proof components are propositional and irrelevant to behaviour,
    but proving `Subsingleton` of the proof field is unnecessary for any downstream
    use here).
  * §5 certifies the trace of *any* `SoundStep` (hence any `certifiedSoundStep` /
    `dominatingSoundStep`); it does **not** assert the iteration *reaches* a solved
    state — that is completeness (the subject of `LDTCompleteness`), orthogonal to
    the soundness/refutation guarantees proved here.
-/

end LatticeDeduction
end Integrations
end Graphplay
