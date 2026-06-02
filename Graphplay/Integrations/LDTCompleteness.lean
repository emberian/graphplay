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

/-! ## 3.  The contrast: arc consistency DOES solve bounded-width problems.

The *same* operator, on a "chain" (`x₀ = false`, `x₀ = x₁`) — a width-1 / kind-0
problem — propagates to the solution in two steps.  So the projection lattice
genuinely **discriminates** kind-0 (solved) from kind-2 affine (abstained): the
obstruction is the problem's *width*, not the deduction.  The honest stratification
behind the "framework of kinds." -/

/-- `x₀ = false` (unary). -/
def cU0 : Set (Str Bool 2) := {t | t 0 = false}
/-- `x₀ = x₁`. -/
def cE01 : Set (Str Bool 2) := {t | t 0 = t 1}
/-- The chain family `{x₀ = false, x₀ = x₁}`. -/
def chainCs : Set (Set (Str Bool 2)) := {cU0, cE01}

/-- The chain has the unique solution `(false, false)`. -/
theorem chain_unique : famCons chainCs = {fun _ => false} := by
  ext t
  simp only [famCons, chainCs, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, cU0, cE01, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, h01⟩
    have h1 : t 1 = false := by rw [← h01]; exact h0
    funext i; fin_cases i
    · exact h0
    · exact h1
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- **Step 1:** one AC step from `⊤` narrows cell 0 to `{false}` (the unary
constraint fires); cell 1 is still unconstrained. -/
theorem acStep_chain_step1 :
    acStep chainCs (⊤ : Abs Bool 2)
      = (fun i => if i = 0 then ({false} : Set Bool) else Set.univ) := by
  funext i; ext v
  simp only [acStep, chainCs, cU0, cE01, Set.top_eq_univ, Pi.top_apply,
    Set.mem_setOf_eq, Set.mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, forall_const]
  fin_cases i <;> cases v <;> simp <;> decide

/-- **Step 2:** the second AC step propagates `x₀ = false` along `x₀ = x₁` to pin
cell 1 — reaching the fully solved state `(false, false)`. -/
theorem acStep_chain_step2 :
    acStep chainCs (fun i => if i = 0 then ({false} : Set Bool) else Set.univ)
      = (fun _ => {false}) := by
  funext i; ext v
  simp only [acStep, chainCs, cU0, cE01, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  fin_cases i <;> cases v <;> simp <;> decide

/-- **Arc consistency solves the chain.**  Two iterations from `⊤` reach the solved
state pinning `(false,false)`, which passes the constraint check — so the
AC-deduction solver returns the (correct) answer.  Contrast `acStep_xor_abstains`:
same operator, same lattice, *solvable* problem — the difference is width. -/
theorem acStep_chain_solves :
    Solves (famCons chainCs) (fun a => acStep chainCs (acStep chainCs a)) := by
  refine ⟨fun _ => false, ?_, ?_⟩
  · show Solved (acStep chainCs (acStep chainCs ⊤)) (fun _ => false)
    rw [acStep_chain_step1, acStep_chain_step2]
    intro _; rfl
  · rw [chain_unique]; rfl

/-- **The lattice is the discriminator (the framework of kinds, in miniature).**
One arc-consistency operator: it **solves** the width-1 chain but **abstains** on
the affine XOR system.  Both soundly; the difference is the problem's width versus
the per-cell lattice's expressiveness — *not* correctness. -/
theorem ac_kind_discriminates :
    Solves (famCons chainCs) (fun a => acStep chainCs (acStep chainCs a))
    ∧ Abstains (famCons xorCs) (acStep xorCs) :=
  ⟨acStep_chain_solves, acStep_xor_abstains⟩

end LatticeDeduction
end Integrations
end Graphplay
