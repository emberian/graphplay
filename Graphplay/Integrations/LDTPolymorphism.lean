/-
# Graphplay.Integrations.LDTPolymorphism — the algebraic signature of the kinds.

The bounded-width CSP dichotomy is stated in terms of **polymorphisms**: an
operation `f : Vⁿ → V` is a polymorphism of a constraint family when, applied
coordinate-wise to `n` satisfying assignments of a constraint, it yields another
satisfying assignment.  The Feder–Vardi / Barto–Kozik theorem is: a CSP is solved
by local consistency (= has bounded width) **iff** its polymorphisms omit the
**affine** type — equivalently, iff it has a near-unanimity / WNU-style
polymorphism on the non-affine side.

We do **not** need (or formalize) the full dichotomy — that is the large
tame-congruence-theory build.  But the *signature* of our kind-discriminator
(`LDTCompleteness.ac_kind_discriminates`) is finitary and cheap, so we formalize
it directly here (Boolean, by `decide`):

* the **chain** (AC-solvable, `acStep_chain_solves`) carries a **semilattice**
  polymorphism (`∧`) — `chain_semilattice`;
* the **XOR** system (AC-abstains, `acStep_xor_abstains`) carries the **affine /
  Maltsev** polymorphism `x⊕y⊕z` (`xor_affine`) and has **no majority**
  polymorphism (`xor_no_majority`) — the exact algebraic signature of the
  unbounded-width / affine wall.

So the kind discriminator is not a coincidence of two hand-picked instances: it is
the polymorphism algebra, the object the dichotomy classifies, computed in Lean.
-/

import Graphplay.Integrations.LDTCompleteness

namespace Graphplay
namespace Integrations
namespace LatticeDeduction

open Set

variable {V : Type} {k : ℕ}

/-- An `n`-ary operation `f : Vⁿ → V` is a **polymorphism** of the constraint
family `cs` when, applied coordinate-wise to any `n` strings satisfying a
constraint `C ∈ cs`, the result still satisfies `C`.  The polymorphism algebra of
`cs` is what the CSP dichotomy classifies: bounded width (= local-consistency
solvable) iff the polymorphisms omit the affine type. -/
def IsPolymorphism (cs : Set (Set (Str V k))) (n : ℕ) (f : (Fin n → V) → V) : Prop :=
  ∀ C ∈ cs, ∀ rows : Fin n → Str V k, (∀ a, rows a ∈ C) →
    (fun cell => f (fun a => rows a cell)) ∈ C

/-- The **affine / Maltsev** operation over `GF(2)`: `x ⊕ y ⊕ z`.  A Maltsev
polymorphism (`m(x,x,y)=y`, `m(x,y,y)=x`) is the signature of an *affine* CSP — the
unbounded-width side of the dichotomy. -/
def boolAffine : (Fin 3 → Bool) → Bool := fun v => xor (xor (v 0) (v 1)) (v 2)

/-- The Boolean **majority** operation (the unique majority on `Bool`).  A majority
(near-unanimity) polymorphism is a *sufficient* condition for bounded width
(2-decomposability); affine CSPs provably lack one. -/
def boolMaj : (Fin 3 → Bool) → Bool :=
  fun v => (v 0 && v 1) || (v 1 && v 2) || (v 0 && v 2)

/-- The **semilattice** (meet / `∧`) operation.  A semilattice polymorphism forces
arc-consistency solvability (the Horn / set-function tractable class). -/
def boolMeet : (Fin 2 → Bool) → Bool := fun v => v 0 && v 1

/-- **The chain is a semilattice CSP.**  `∧` is a polymorphism of the chain family
`{x₀ = false, x₀ = x₁}` — the algebraic reason `acStep_chain_solves`: a semilattice
polymorphism ⟹ solvable by arc consistency. -/
theorem chain_semilattice : IsPolymorphism chainCs 2 boolMeet := by
  intro C hC
  simp only [chainCs, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with rfl | rfl <;>
    (simp only [cU0, cE01, boolMeet, Set.mem_setOf_eq]; decide)

/-- **XOR is affine.**  The Maltsev operation `x ⊕ y ⊕ z` is a polymorphism of the
XOR family — the algebraic signature of the unbounded-width / affine wall that
makes `acStep_xor_abstains` inevitable, not incidental. -/
theorem xor_affine : IsPolymorphism xorCs 3 boolAffine := by
  intro C hC rows hrows
  simp only [xorCs, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with rfl | rfl | rfl
  · simp only [xC1, Set.mem_setOf_eq, boolAffine] at hrows ⊢
    rw [hrows 0, hrows 1, hrows 2]
  · simp only [xC2, Set.mem_setOf_eq, boolAffine] at hrows ⊢
    rw [hrows 0, hrows 1, hrows 2]
  · simp only [xC3, Set.mem_setOf_eq, boolAffine] at hrows ⊢
    have h0 := hrows 0; have h1 := hrows 1; have h2 := hrows 2
    revert h0 h1 h2
    cases rows 0 0 <;> cases rows 0 1 <;> cases rows 0 2 <;>
      cases rows 1 0 <;> cases rows 1 1 <;> cases rows 1 2 <;>
      cases rows 2 0 <;> cases rows 2 1 <;> cases rows 2 2 <;> decide

/-- **XOR has no majority polymorphism.**  The (unique, on `Bool`) majority
operation is NOT a polymorphism of the XOR family.  Since a near-unanimity /
majority polymorphism would force bounded width, its *absence* — together with the
affine `xor_affine` — is the formal obstruction: XOR sits on the affine side of the
dichotomy, off the entire local-consistency ladder. -/
theorem xor_no_majority : ¬ IsPolymorphism xorCs 3 boolMaj := by
  intro h
  -- witness: three even-parity rows whose majority is odd-parity, breaking xC3.
  have key := h xC3 (by simp [xorCs])
    ![![false, false, false], ![true, true, false], ![true, false, true]]
    (by simp only [xC3, Set.mem_setOf_eq]; decide)
  simp only [xC3, boolMaj, Set.mem_setOf_eq] at key
  revert key
  decide

/-! ### The defining identities — making the algebraic *labels* rigorous.

The kind-names ("affine / Maltsev", "semilattice", "majority") are not decoration:
each is a finite equational signature, and our concrete operations satisfy exactly
the right one (by `decide` on `Bool`). -/

/-- `boolAffine` is a **Maltsev operation**: `m(x,x,y) = y` and `m(x,y,y) = x`.
A Maltsev polymorphism is the algebraic signature of an *affine* CSP (the
unbounded-width side); `xor_affine` exhibits one for XOR. -/
theorem boolAffine_maltsev :
    (∀ x y, boolAffine ![x, x, y] = y) ∧ (∀ x y, boolAffine ![x, y, y] = x) := by
  constructor <;> intro x y <;> cases x <;> cases y <;> decide

/-- `boolMeet` is a **semilattice operation**: idempotent, commutative, associative.
A semilattice polymorphism forces arc-consistency solvability; `chain_semilattice`
exhibits one for the chain. -/
theorem boolMeet_semilattice :
    (∀ x, boolMeet ![x, x] = x)
    ∧ (∀ x y, boolMeet ![x, y] = boolMeet ![y, x])
    ∧ (∀ x y z, boolMeet ![boolMeet ![x, y], z] = boolMeet ![x, boolMeet ![y, z]]) := by
  refine ⟨fun x => ?_, fun x y => ?_, fun x y z => ?_⟩
  · cases x <;> decide
  · cases x <;> cases y <;> decide
  · cases x <;> cases y <;> cases z <;> decide

/-- `boolMaj` is a **majority operation**: `m(x,x,y) = m(x,y,x) = m(y,x,x) = x`.
So a genuine majority operation *exists* on `Bool` — and `xor_no_majority` says it
is nonetheless **not** a polymorphism of XOR, which is the real obstruction. -/
theorem boolMaj_majority :
    (∀ x y, boolMaj ![x, x, y] = x)
    ∧ (∀ x y, boolMaj ![x, y, x] = x)
    ∧ (∀ x y, boolMaj ![y, x, x] = x) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x y <;> cases x <;> cases y <;> decide

/-- **The algebraic kind-discriminator, named.**  The chain carries a semilattice
polymorphism (⟹ AC-solvable, `ac_kind_discriminates.1`); XOR carries the affine
Maltsev polymorphism and **no** majority (⟹ the affine wall, AC-abstains,
`ac_kind_discriminates.2`).  This is the polymorphism-algebra signature the
bounded-width dichotomy classifies — formalized for our two witnesses, no Mathlib
universal-algebra library required. -/
theorem kind_polymorphism_signature :
    IsPolymorphism chainCs 2 boolMeet
    ∧ IsPolymorphism xorCs 3 boolAffine
    ∧ ¬ IsPolymorphism xorCs 3 boolMaj :=
  ⟨chain_semilattice, xor_affine, xor_no_majority⟩

/-! ### The positive direction, algebraically.

*Why* a semilattice CSP is tractable: its solutions are closed under the
coordinate-wise semilattice meet, so they form a sub-meet-semilattice with a
canonical (least) representative that propagation converges to.  We prove the
closure directly from the polymorphism property — for **any** domain `V`, no
Mathlib universal-algebra library — turning `acStep_chain_solves` from one instance
into the structural reason behind the whole semilattice/Horn tractable class. -/

/-- **A semilattice polymorphism closes the solution set under coordinate-wise meet.**
If the binary operation `s` is a polymorphism of `cs`, then `famCons cs` is closed
under `(a ⊓ b) i = s (a i) (b i)`.  Hence the solutions form a sub-meet-semilattice —
the structural reason a semilattice CSP (e.g. the chain, via `chain_semilattice`) is
solved by arc consistency. -/
theorem famCons_closed_meet (cs : Set (Set (Str V k))) (s : V → V → V)
    (hs : IsPolymorphism cs 2 (fun v => s (v 0) (v 1)))
    {a b : Str V k} (ha : a ∈ famCons cs) (hb : b ∈ famCons cs) :
    (fun i => s (a i) (b i)) ∈ famCons cs := by
  intro C hC
  have hmem : ∀ x : Fin 2, ![a, b] x ∈ C := by
    intro x; fin_cases x
    · simpa using ha C hC
    · simpa using hb C hC
  simpa using hs C hC ![a, b] hmem

end LatticeDeduction
end Integrations
end Graphplay
