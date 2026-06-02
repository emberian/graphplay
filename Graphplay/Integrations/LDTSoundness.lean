/-
# Graphplay.Integrations.LDTSoundness — soundness of a *trained* lattice-deduction
solver: checking vs. trusting.

The load-bearing empirical claim of Lattice Deduction Transformers (LDT,
arXiv:2605.08605) — "returns a correct answer or abstains, never confidently
wrong" — is, properly understood, **not a property of the trained network at
all.**  It is a property of **output verification**, and it holds for *any*
operator the network could possibly learn, soundly and **training-independently**.
This is the genuine content of the "SAT-solver guarantee": a SAT solver's `SAT`
answer is believed because the assignment is *checkable*, not because the search
was *trusted*.

This file formalizes the decomposition over the LDT abstract domain of
`Graphplay.Integrations.LatticeDeduction`:

* **`checkedSolve_sound`** — for an *arbitrary* solver `solve : Abs → Abs` (in
  particular any trained network, with **no** soundness hypothesis), the protocol
  "run `solve` from `⊤`, read off the pinned assignment, RETURN it only if it
  satisfies the constraints, else ABSTAIN" never returns a wrong answer.  Training
  cannot break this; soundness is the output check.

* **`id_sound_but_useless`** — soundness says *nothing* about power: the identity
  is a perfectly sound, reductive deduction that solves nothing.  So "is the
  deduction sound?" is the wrong question.

* **`Solves` / `Abstains`** — the *real* quantity is COMPLETENESS (does it reach a
  checkable answer?).  This, not soundness, is what the projection-lattice
  expressiveness (`Tower9.ldt_lossy`, `α∘γ ≠ id`) and the problem's width bound —
  the honest home of the "which problems generalize" question.

* **`certifiedStep_sound` / `certifiedSoundStep`** — if you want to trust the
  *intermediate* trace (early abstention, proof extraction, composition), per-step
  soundness is recovered by **certificate-checked** ("proof-carrying") deduction: a
  candidate is removed only with a checkable witness that no solution *consistent
  with the current state* uses it.  Such a step is in `SoundStep` regardless of how
  it was produced — the *verifier*, not the trained net, guarantees soundness — so
  `dedRun_preserves_solutions` lifts it to whole-run soundness.  `dedP_certified`
  shows the exact best transformer really is such a step.

The upshot for the LDT authors: **soundness is free from checking and
training-independent; the science is COMPLETENESS (abstention vs. lattice
expressiveness / problem width), not soundness.**
-/

import Graphplay.Integrations.LatticeDeduction

namespace Graphplay
namespace Integrations
namespace LatticeDeduction

open Set

variable {V : Type} {k : ℕ}

/-! ## 1.  Output-checked soundness — training-independent.

We model the *whole trained looped network* as an arbitrary endomap
`solve : Abs → Abs` (input the all-candidates grid `⊤`, output its final state).
The deployment protocol reads off the pinned assignment and **verifies it against
the constraints before returning.** -/

/-- The **output-checked protocol returns `s`**: the solver's final state `solve ⊤`
pins the string `s` (every cell a singleton) **and** `s` passes the constraint
check `s ∈ cons`.  Otherwise the protocol abstains. -/
def CheckedReturns (cons : Set (Str V k)) (solve : Abs V k → Abs V k)
    (s : Str V k) : Prop :=
  Solved (solve ⊤) s ∧ s ∈ cons

/-- **Soundness is training-independent (the SAT-solver guarantee).**  For *any*
solver `solve` — in particular any trained network, with **no** soundness
hypothesis whatsoever — if the output-checked protocol returns `s`, then `s` is a
genuine solution (`s ∈ cons`).

The proof is `h.2`: the protocol returns `s` *only when* `s ∈ cons`.  That
triviality is the whole point — soundness comes from the cheap output check, not
from trusting (or having trained) the net.  No property of `solve` is used. -/
theorem checkedSolve_sound (cons : Set (Str V k)) (solve : Abs V k → Abs V k)
    {s : Str V k} (h : CheckedReturns cons solve s) : s ∈ cons :=
  h.2

/-- Non-vacuity: the checked protocol *can* return — a solver that lands on the
solved state for `cons = {s₀}` returns `s₀`.  (So `checkedSolve_sound` is not
vacuously quantified.) -/
theorem checkedReturns_nonvacuous (s₀ : Str V k) :
    CheckedReturns ({s₀} : Set (Str V k)) (fun _ i => {s₀ i}) s₀ :=
  ⟨fun _ => rfl, rfl⟩

/-! ## 2.  Soundness ≠ power.  The identity is a sound, useless deduction. -/

/-- **Soundness does not imply power.**  The identity operator is a sound,
reductive deduction step — it never drops a real solution — yet from `⊤` it makes
no progress (`id ⊤ = ⊤`), and (≥2 symbols, ≥1 cell) `⊤` pins *nothing*.  A sound
deduction can be completely useless: "is it sound?" is the wrong question;
"does it reach a checkable answer?" (completeness) is the right one. -/
theorem id_sound_but_useless (cons : Set (Str V k)) :
    -- `id` is a sound narrowing step (reductive AND solution-preserving):
    (∀ a : Abs V k, id a ≤ a ∧ cons ∩ gamma a ⊆ gamma (id a))
    ∧ -- ... yet from ⊤ it stays at ⊤,
    (id (⊤ : Abs V k) = ⊤)
    ∧ -- ... which (≥2 symbols, ≥1 cell) pins no string.
    (0 < k → Nontrivial V → ¬ ∃ s, Solved (⊤ : Abs V k) s) := by
  refine ⟨fun a => ⟨le_refl a, ?_⟩, rfl, ?_⟩
  · show cons ∩ gamma a ⊆ gamma a
    exact Set.inter_subset_right
  · rintro hk ⟨x, y, hxy⟩ ⟨s, hs⟩
    have h0 := hs ⟨0, hk⟩
    rw [Pi.top_apply, Set.top_eq_univ] at h0      -- h0 : univ = {s ⟨0,hk⟩}
    have hx : x ∈ ({s ⟨0, hk⟩} : Set V) := h0 ▸ Set.mem_univ x
    have hy : y ∈ ({s ⟨0, hk⟩} : Set V) := h0 ▸ Set.mem_univ y
    rw [Set.mem_singleton_iff] at hx hy
    exact hxy (hx.trans hy.symm)

/-! ## 3.  The real quantity: completeness / abstention.

Soundness being free, the meaningful, training- and lattice-dependent property is
whether the solver reaches a *checkable* answer at all. -/

/-- The solver **solves** the instance: it returns some (necessarily correct, by
`checkedSolve_sound`) answer. -/
def Solves (cons : Set (Str V k)) (solve : Abs V k → Abs V k) : Prop :=
  ∃ s, CheckedReturns cons solve s

/-- The solver **abstains**: it reaches no checkable answer.  This — not
soundness — is what fails when the projection lattice is too coarse for the
problem (cf. `Tower9.ldt_lossy`: per-cell candidate sets cannot represent the
inter-cell correlations higher-width problems need). -/
def Abstains (cons : Set (Str V k)) (solve : Abs V k → Abs V k) : Prop :=
  ¬ Solves cons solve

/-- Every solved-and-returned answer is genuinely correct (the returned string is
a real solution).  Restates `checkedSolve_sound` at the `Solves` level: if the
solver solves, its answer is sound. -/
theorem solves_returns_correct (cons : Set (Str V k))
    (solve : Abs V k → Abs V k) {s : Str V k}
    (h : CheckedReturns cons solve s) : s ∈ cons :=
  checkedSolve_sound cons solve h

/-! ## 4.  Trusting the *trace*: certificate-checked (proof-carrying) deduction.

If you want soundness of the *intermediate* states (not just the final output) —
for early abstention, extracting a proof, or composing LDT with another reasoner —
you need per-step soundness.  It is recovered, again training-independently, by
**certificates relative to the current state**: remove a candidate `v` from cell
`i` only with a checkable witness that *no solution consistent with the current
abstract state `a`* places `v` at `i`. -/

/-- **A certificate-checked removal is solution-preserving.**  If every candidate
`f` removes from a cell (`v ∈ a i`, `v ∉ f a i`) is certified impossible *relative
to the current state* — no solution consistent with `a` places `v` at `i`
(`∀ s ∈ cons, s ∈ γ a → s i ≠ v`) — then `f` drops no solution consistent with
`a`: `cons ∩ γ a ⊆ γ (f a)`.  The certificate, checked by a verifier, does the
work; `f` (the trained net) is arbitrary. -/
theorem certifiedStep_sound (cons : Set (Str V k)) (f : Abs V k → Abs V k)
    (hcert : ∀ a i (v : V), v ∈ a i → v ∉ f a i → ∀ s ∈ cons, s ∈ gamma a → s i ≠ v)
    (a : Abs V k) : cons ∩ gamma a ⊆ gamma (f a) := by
  rintro s ⟨hcons, hga⟩ i
  by_contra hnot
  exact hcert a i (s i) (hga i) hnot s hcons hga rfl

/-- A reductive, certificate-checked operator is a genuine `SoundStep` — so any
run built from it preserves all solutions via `dedRun_preserves_solutions`
(§5 of `LatticeDeduction`).  **Soundness is supplied by the verifier, not by
trusting the trained net.** -/
def certifiedSoundStep (cons : Set (Str V k)) (f : Abs V k → Abs V k)
    (hred : ∀ a, f a ≤ a)
    (hcert : ∀ a i (v : V), v ∈ a i → v ∉ f a i → ∀ s ∈ cons, s ∈ gamma a → s i ≠ v) :
    SoundStep cons :=
  ⟨f, fun a => ⟨hred a, certifiedStep_sound cons f hcert a⟩⟩

/-- **The exact best transformer `dedₚ` is certificate-checked.**  Every candidate
`dedₚ` removes is genuinely placed by no solution consistent with the current
state — so the certified-step notion is inhabited by the intended operator, not
just stubs.  (NB: the certificate is *relative to `a`*; the *unrelativised*
"no solution anywhere places `v` at `i`" is FALSE — a solution off `γ a` may use
`v`, and `dedₚ` legitimately drops it.  Honesty matters: the relativised form is
the one that is both true and sufficient for run-soundness.) -/
theorem dedP_certified (cons : Set (Str V k)) (a : Abs V k) (i : Fin k) (v : V)
    (hgone : v ∉ dedP cons a i) : ∀ s ∈ cons, s ∈ gamma a → s i ≠ v := by
  intro s hcons hga hsi
  apply hgone
  show v ∈ alpha (gamma a ∩ cons) i
  rw [mem_alpha]
  exact ⟨s, ⟨hga, hcons⟩, hsi⟩

end LatticeDeduction
end Integrations
end Graphplay
