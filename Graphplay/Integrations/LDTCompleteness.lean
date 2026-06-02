/-
# Graphplay.Integrations.LDTCompleteness — the *completeness* side: which problems
the per-cell projection lattice can actually solve by deduction.

`LDTSoundness` showed soundness is free (output verification / certificates) and
training-independent.  The *real* quantity is **completeness**: does the deduction
loop reach a checkable answer, or abstain?  This file builds the honest theory of
that, on a concrete deduction operator:

* **`acStep`** — *generalized arc consistency* for a constraint family `Cs` on the
  LDT per-cell domain: keep a candidate iff every constraint has a satisfying
  string, consistent with the current domains, that uses it.  This is exactly the
  efficiently-computable local deduction the per-cell projection lattice supports
  (the level LDT's learned `dedₚ` targets).

* **`acStep` is SOUND for free** (`acSoundStep`) — it is a `certifiedSoundStep`
  (the support test *is* the impossibility certificate), so by `LDTSoundness` its
  runs preserve all solutions.  No training, no trust.

* **The incompleteness witness** (`acStep_xor_sound_but_abstains`) — a tiny XOR /
  affine system over `Bool` with a **unique** solution, on which `acStep` is
  **stuck at `⊤`** (makes no progress) and therefore the AC-deduction solver
  **ABSTAINS** — despite the problem being solvable.  This is the formal content of
  "the projection lattice bounds which problems generalize" (AiDevCraft): affine /
  unbounded-width problems are **not** invisible to LDT because it errs — it
  *abstains*, soundly.  The lattice (`Tower9.ldt_lossy`: per-cell sets forget
  inter-cell correlation) is exactly what forces it.

The pairing is the whole point: **one operator that is simultaneously a *sound*
deduction (free) and *incomplete* on affine problems (lattice-forced).**
Soundness ⟂ completeness, machine-checked.
-/

import Graphplay.Integrations.LDTSoundness

namespace Graphplay
namespace Integrations
namespace LatticeDeduction

open Set

variable {V : Type} {k : ℕ}

/-! ## 1.  Generalized arc consistency on the per-cell domain. -/

/-- **Generalized arc consistency** for a constraint family `Cs`.  Keep value `v`
at cell `i` iff `v` is a current candidate (`v ∈ a i`) AND **every** constraint
`C ∈ Cs` admits a satisfying string consistent with the current domains that
places `v` at `i`.  This is the efficiently-computable local narrowing the per-cell
lattice supports — the operator class LDT's learned `dedₚ` targets. -/
def acStep (Cs : Set (Set (Str V k))) (a : Abs V k) : Abs V k :=
  fun i => {v | v ∈ a i ∧ ∀ C ∈ Cs, ∃ t ∈ C, (∀ j, t j ∈ a j) ∧ t i = v}

/-- The solution set of the constraint family: strings satisfying every
constraint, `⋂ Cs`. -/
def famCons (Cs : Set (Set (Str V k))) : Set (Str V k) := {s | ∀ C ∈ Cs, s ∈ C}

/-- `acStep` is **reductive** — it only ever removes candidates. -/
theorem acStep_reductive (Cs : Set (Set (Str V k))) (a : Abs V k) :
    acStep Cs a ≤ a := by
  intro i v hv; exact hv.1

/-- **`acStep` is certificate-checked, hence sound for free.**  Every candidate it
removes is genuinely unsupported by some constraint relative to the current state —
the support test *is* the impossibility certificate — so it never drops a real
solution consistent with the state.  (The proof: a solution `s` consistent with
`a` supports `s i` in *every* constraint via the witness `t := s`.) -/
theorem acStep_certified (Cs : Set (Set (Str V k))) :
    ∀ (a : Abs V k) (i : Fin k) (v : V), v ∈ a i → v ∉ acStep Cs a i →
      ∀ s ∈ famCons Cs, s ∈ gamma a → s i ≠ v := by
  intro a i v hv hgone s hs hsa hsi
  exact hgone ⟨hv, fun C hC => ⟨s, hs C hC, hsa, hsi⟩⟩

/-- `acStep Cs` is a genuine `SoundStep` for the family's solution set — so any run
built from it preserves all solutions (via `dedRun_preserves_solutions`).
**Soundness from the verifier, not the trained net.** -/
def acSoundStep (Cs : Set (Set (Str V k))) : SoundStep (famCons Cs) :=
  certifiedSoundStep (famCons Cs) (acStep Cs) (acStep_reductive Cs) (acStep_certified Cs)

/-! ## 2.  The incompleteness witness — an affine system AC cannot crack.

A connected XOR system over `Bool` on three cells, with a **unique** solution
`(false,false,false)`, on which arc consistency makes **zero** progress.  This is
the canonical "tractable but not by local consistency" obstruction (Feder–Vardi;
the affine / Maltsev type of the algebraic dichotomy). -/

/-- `x = y`. -/
def xC1 : Set (Str Bool 3) := {t | t 0 = t 1}
/-- `y = z`. -/
def xC2 : Set (Str Bool 3) := {t | t 1 = t 2}
/-- `x ⊕ y ⊕ z = 0` (even parity). -/
def xC3 : Set (Str Bool 3) := {t | xor (xor (t 0) (t 1)) (t 2) = false}

/-- The XOR constraint family `{x=y, y=z, x⊕y⊕z=0}`. -/
def xorCs : Set (Set (Str Bool 3)) := {xC1, xC2, xC3}

/-- **The system has a unique solution** `(false,false,false)`:
`x=y=z` and even parity force all-false.  So it *is* solvable. -/
theorem xor_unique : famCons xorCs = {fun _ => false} := by
  ext t
  simp only [famCons, xorCs, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, xC1, xC2, xC3, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    -- t 0 = t 1 = t 2 =: b, and b ⊕ b ⊕ b = b = false.
    have h02 : t 0 = t 2 := h1.trans h2
    rw [← h1, ← h02] at h3
    have key : ∀ b : Bool, xor (xor b b) b = b := by decide
    rw [key] at h3                         -- h3 : t 0 = false
    have ht1 : t 1 = false := by rw [← h1]; exact h3
    have ht2 : t 2 = false := by rw [← h02]; exact h3
    funext i; fin_cases i
    · exact h3
    · exact ht1
    · exact ht2
  · rintro rfl
    refine ⟨rfl, rfl, ?_⟩
    decide

/-- **Arc consistency is stuck at `⊤`** on the XOR system: from the all-candidates
grid it makes no progress at all (`acStep xorCs ⊤ = ⊤`).  Every value at every cell
is locally supported by every constraint — the global linear coupling is invisible
to per-constraint, per-cell reasoning. -/
theorem acStep_xor_stuck : acStep xorCs (⊤ : Abs Bool 3) = ⊤ := by
  funext i
  ext v
  simp only [acStep, xorCs, xC1, xC2, xC3, Set.top_eq_univ, Pi.top_apply,
    Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, forall_const]
  fin_cases i <;> cases v <;> refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The AC-deduction solver abstains** on the XOR system: its fixed point from
`⊤` is `⊤`, which pins no assignment, so the output-checked protocol returns
nothing.  (Modelled with the solver `solve := acStep xorCs`, whose value at `⊤` is
`⊤` by `acStep_xor_stuck`.) -/
theorem acStep_xor_abstains : Abstains (famCons xorCs) (acStep xorCs) := by
  rintro ⟨s, hsolved, -⟩
  rw [show acStep xorCs (⊤ : Abs Bool 3) = ⊤ from acStep_xor_stuck] at hsolved
  exact (id_sound_but_useless (famCons xorCs)).2.2 (by norm_num) inferInstance ⟨s, hsolved⟩

/-- **The headline: a sound deduction, lattice-forced to abstain.**  On the XOR
system, `acStep` is (1) a sound, reductive deduction, (2) the problem has a unique
solution — yet (3) the AC solver abstains.  Soundness ⟂ completeness, and the
projection lattice (not unsoundness) is what bounds the solvable class. -/
theorem acStep_xor_sound_but_abstains :
    (∀ a, acStep xorCs a ≤ a)                       -- sound (reductive) deduction
    ∧ (famCons xorCs = {fun _ => false})            -- the problem IS solvable (unique sol.)
    ∧ Abstains (famCons xorCs) (acStep xorCs) :=    -- yet AC-deduction abstains
  ⟨acStep_reductive xorCs, xor_unique, acStep_xor_abstains⟩

end LatticeDeduction
end Integrations
end Graphplay
