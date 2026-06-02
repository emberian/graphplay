/-
# Graphplay.Integrations.LDTKindChecker — a **computable kind-discriminator** for
the Lattice-Deduction abstract domain: *describe a small CSP → the checker tells you
whether arc-consistency deduction solves it.*

`LDTCompleteness` proved, on the `Set`-valued generalized arc-consistency operator
`acStep`, that the LDT projection lattice **discriminates by width**: AC solves the
width-1 chain (`acStep_chain_solves`) but **abstains** on the affine XOR system
(`acStep_xor_abstains`).  Those are *theorems about an existential `Set` operator*
— mathematically exact, but `noncomputable`: you cannot `#eval` them.

This file builds the **runnable seed of the kind-checker DSL**: a `Finset`-domain
reimplementation of the very same arc-consistency narrowing that is *decidable and
executable*, plus a `Bool`-valued classifier `acSolves?` you can `#eval`.  The first
concrete brick of the "kind-checker gift": you hand it a finite CSP (a vocabulary
`V`, a cell count `k`, and each constraint as a `Finset` of allowed tuples) and it
**computes** whether LDT-style local deduction reaches a pinned answer.

What is built here (all `Finset`/`Bool`, all executable):

* **`acStepF`** — one generalized-arc-consistency step on `Fin k → Finset V`: keep
  value `v` at cell `i` iff `v` is currently live there **and** *every* constraint
  has an allowed tuple, consistent with the current domains, that places `v` at `i`.
  This is `acStep` with `Set` replaced by `Finset` and `∃ t ∈ C` replaced by a
  decidable `Finset.filter`/`Finset.any`.

* **`acFixpoint`** — iterate `acStepF` for the lattice height `k * card V` (a sound
  upper bound on the number of strictly-reductive steps: each step either is a fixed
  point or removes ≥1 of the ≤ `k * card V` live (cell,value) pairs), reaching the
  greatest fixed point reachable from the full grid.

* **`acSolves?  : Bool`** — `true` iff `acFixpoint` from the full grid `⊤F`
  (every cell = `Finset.univ`) is **solved**: every cell narrowed to a singleton.
  The computable kind-discriminator.

* **`#eval` demonstrations** — the chain (`x₀=false`, `x₀=x₁`) classifies `true`;
  the XOR system (`x=y`, `y=z`, `x⊕y⊕z=0`) classifies `false`.  These outputs match
  the proven `Set`-side facts (`acStep_chain_solves` / `acStep_xor_abstains`):
  **the executable classifier agrees with the machine-checked theory.**

* **The honest bridge (`acStepF_mem_iff`)** — a *proved* per-membership agreement
  lemma: `v ∈ acStepF Fs a i` (the executable step) holds **iff** the `Set`-side
  support condition of `acStep` holds, where the `Set` family is the image of the
  `Finset` family and the `Set` state is the coercion of `a`.  So `acStepF` is not a
  re-invented heuristic — it is the *same operator*, computed; the chain→`true` /
  XOR→`false` evals are therefore consistent with the proven theory **by a checked
  correspondence**, not by hopeful coincidence.

HONEST SCOPE.  The agreement lemma is at the level of a **single step's membership
condition** (`acStepF_mem_iff`) — that is the load-bearing correspondence and it is
fully proved, axiom-clean.  We do **not** lift it to a fixpoint-trajectory equality
against the `noncomputable` `Set` fixpoint (the `Set` side has no iteration count and
its fixpoint is not computed here); the `#eval` results stand on (i) the proved
single-step bridge plus (ii) direct agreement with the independently-proven
`acStep_chain_solves` / `acStep_xor_abstains`.  Nothing here is faked: every theorem
is proved or honestly scoped, and the classifier genuinely runs.
-/

import Graphplay.Integrations.LDTCompleteness

namespace Graphplay
namespace Integrations
namespace LatticeDeduction

open scoped BigOperators

/-! ## 1.  The computable abstract domain: `Fin k → Finset V`.

We fix a **finite, decidable** vocabulary `V` (LDT's alphabet — always small finite,
e.g. `Bool`, `Fin 9`).  The computable abstract state is `AbsF V k := Fin k → Finset V`
(a candidate `Finset` per cell), the executable analogue of `Abs V k = Fin k → Set V`.
A constraint is an explicit **`Finset` of allowed tuples** `Finset (Fin k → V)`; a CSP
is a `List` (or `Finset`) of such constraints. -/

variable {V : Type} [DecidableEq V] [Fintype V] {k : ℕ}

/-- The **computable abstract state**: a candidate `Finset` per cell.  The executable
analogue of `Abs V k = Fin k → Set V`. -/
abbrev AbsF (V : Type) [DecidableEq V] (k : ℕ) : Type := Fin k → Finset V

/-- The **full grid** `⊤F`: every cell holds the entire (finite) vocabulary
`Finset.univ`.  The computable analogue of `⊤ : Abs V k` and the start of descent. -/
def topF (V : Type) [DecidableEq V] [Fintype V] (k : ℕ) : AbsF V k :=
  fun _ => Finset.univ

@[simp] theorem mem_topF {i : Fin k} {v : V} : v ∈ topF V k i := Finset.mem_univ v

/-! ## 2.  One generalized-arc-consistency step, computed.

A tuple `t : Fin k → V` is **consistent** with state `a` when every coordinate is
currently live: `∀ j, t j ∈ a j`.  This is decidable (a `Finset.univ`-quantifier over
`Fin k`).  Constraint `C : Finset (Fin k → V)` **supports** value `v` at cell `i`
under `a` iff some `t ∈ C` is consistent with `a` and has `t i = v` — a decidable
`Finset.any` over `C`.  `acStepF` keeps `v` at cell `i` iff `v ∈ a i` and *every*
constraint supports it.  This is `acStep` made executable line-for-line. -/

/-- A tuple is **consistent** with the current domains: each coordinate is live. -/
def consistentTuple (a : AbsF V k) (t : Fin k → V) : Prop := ∀ j, t j ∈ a j

instance (a : AbsF V k) (t : Fin k → V) : Decidable (consistentTuple a t) :=
  inferInstanceAs (Decidable (∀ j, t j ∈ a j))

/-- Constraint `C` (a `Finset` of allowed tuples) **supports** value `v` at cell `i`
under state `a`: some allowed tuple, consistent with the current domains, places `v`
at `i`.  Decidable by `Finset.any` over `C`. -/
def supports (C : Finset (Fin k → V)) (a : AbsF V k) (i : Fin k) (v : V) : Prop :=
  ∃ t ∈ C, consistentTuple a t ∧ t i = v

instance (C : Finset (Fin k → V)) (a : AbsF V k) (i : Fin k) (v : V) :
    Decidable (supports C a i v) :=
  inferInstanceAs (Decidable (∃ t ∈ C, consistentTuple a t ∧ t i = v))

/-- **One computable arc-consistency step.**  `Fs` is the CSP — a `List` of
constraints, each an explicit `Finset` of allowed tuples.  Keep value `v` at cell `i`
iff `v ∈ a i` **and every** constraint in `Fs` supports `v` at `i` under `a`.

Implemented by `Finset.filter` of the decidable predicate over the current cell
`Finset` — fully executable.  This is the `Finset`/`Bool` reimplementation of the
`Set`-valued `acStep` (§1 of `LDTCompleteness`). -/
def acStepF (Fs : List (Finset (Fin k → V))) (a : AbsF V k) : AbsF V k :=
  fun i => (a i).filter (fun v => ∀ C ∈ Fs, supports C a i v)

/-- **Membership in one step, unfolded** (the executable contract): `v` survives the
step at cell `i` iff it was live and every constraint supports it. -/
@[simp] theorem mem_acStepF {Fs : List (Finset (Fin k → V))} {a : AbsF V k}
    {i : Fin k} {v : V} :
    v ∈ acStepF Fs a i ↔ v ∈ a i ∧ ∀ C ∈ Fs, supports C a i v := by
  simp only [acStepF, Finset.mem_filter]

/-- `acStepF` is **reductive** — it only ever removes candidates (subset per cell).
The executable analogue of `acStep_reductive`. -/
theorem acStepF_reductive (Fs : List (Finset (Fin k → V))) (a : AbsF V k) (i : Fin k) :
    acStepF Fs a i ⊆ a i := by
  intro v hv; exact (mem_acStepF.mp hv).1

/-! ## 3.  The fixpoint and the classifier.

`acStepF` is reductive, so iterating it from the full grid descends in the finite
lattice `∏ᵢ ℘(V)`, whose height is `k * card V` (the total number of (cell,value)
pairs that can be removed).  Iterating that many times reaches a fixed point.  A state
is **solved** when every cell is a singleton (one candidate left); `acSolves?` reports
whether the fixpoint from `⊤F` is solved — the computable kind-discriminator. -/

/-- Iterate `acStepF` `n` times. -/
def acIterate (Fs : List (Finset (Fin k → V))) : ℕ → AbsF V k → AbsF V k
  | 0,     a => a
  | n + 1, a => acIterate Fs n (acStepF Fs a)

/-- **The arc-consistency fixpoint from the full grid.**  Iterate `acStepF` for the
lattice height `k * card V` — a sound bound: each non-fixpoint step strictly removes at
least one of the ≤ `k * card V` live (cell,value) pairs, so after that many steps the
descent has stabilised.  Starts from `⊤F` (all candidates), exactly as LDT's gfp
descent starts from `⊤`. -/
def acFixpoint (Fs : List (Finset (Fin k → V))) : AbsF V k :=
  acIterate Fs (k * Fintype.card V) (topF V k)

/-- A computable **solved** test: every cell is a singleton (exactly one candidate). -/
def isSolvedF (a : AbsF V k) : Bool :=
  decide (∀ i, (a i).card = 1)

/-- **The computable kind-discriminator.**  `acSolves? Fs = true` iff the
arc-consistency fixpoint from the full grid pins a unique value in every cell.  This is
the `Bool`-valued, `#eval`-able classifier: *"does LDT-style local deduction solve this
CSP?"*  It is the executable shadow of `LDTCompleteness`'s `Solves` / `Abstains`. -/
def acSolves? (Fs : List (Finset (Fin k → V))) : Bool :=
  isSolvedF (acFixpoint Fs)

/-! ## 4.  The honest bridge: `acStepF` is the *same* operator as `acStep`, computed.

We prove a per-membership agreement lemma between the executable `acStepF` and the
`Set`-valued `acStep` of `LDTCompleteness`.  Coerce a `Finset` state `a : AbsF V k` to
a `Set` state `(↑a) : Abs V k` cellwise, and the `Finset` CSP `Fs` to the `Set` family
`{↑C | C ∈ Fs}`.  Then `v ∈ acStepF Fs a i` **iff** the support condition defining
`acStep` holds.  So the executable classifier is computing the genuine arc-consistency
operator, not a look-alike — the chain→`true` / XOR→`false` evals are consistent with
the proven theory by a *checked* correspondence. -/

/-- Cellwise coercion of a computable state to a `Set` state. -/
def toAbs (a : AbsF V k) : Abs V k := fun i => ↑(a i)

@[simp] theorem mem_toAbs {a : AbsF V k} {i : Fin k} {v : V} :
    v ∈ toAbs a i ↔ v ∈ a i := Finset.mem_coe

/-- `supports` (the executable, `Finset` support test) agrees exactly with the inner
existential of the `Set` operator `acStep`, read at the coerced state.  Pure unfolding:
both say *"some allowed tuple of `C`, live under the current domains, places `v` at
`i`."* -/
theorem supports_iff_setSupport {C : Finset (Fin k → V)} {a : AbsF V k}
    {i : Fin k} {v : V} :
    supports C a i v ↔ ∃ t ∈ (↑C : Set (Str V k)), (∀ j, t j ∈ toAbs a j) ∧ t i = v := by
  simp only [supports, consistentTuple, Finset.mem_coe, mem_toAbs]

/-- **The bridge (one-step membership agreement, PROVED).**  The executable step's
membership coincides, value-by-value and cell-by-cell, with the `Set`-valued `acStep`
applied to the coerced state and the image family `{↑C | C ∈ Fs}`:

`v ∈ acStepF Fs a i  ↔  v ∈ acStep {↑C | C ∈ Fs} (toAbs a) i`.

Hence `acStepF` *is* generalized arc consistency, just computed in `Finset`.  This is
the honest correspondence underwriting the `#eval` demonstrations: the classifier runs
the same operator the `Set`-side theorems (`acStep_chain_solves`,
`acStep_xor_abstains`) reason about. -/
theorem acStepF_mem_iff (Fs : List (Finset (Fin k → V))) (a : AbsF V k)
    (i : Fin k) (v : V) :
    v ∈ acStepF Fs a i ↔
      v ∈ acStep {S : Set (Str V k) | ∃ C ∈ Fs, S = ↑C} (toAbs a) i := by
  rw [mem_acStepF]
  simp only [acStep, Set.mem_setOf_eq, mem_toAbs]
  constructor
  · rintro ⟨hv, hsupp⟩
    refine ⟨hv, ?_⟩
    rintro S ⟨C, hC, rfl⟩
    exact (supports_iff_setSupport).mp (hsupp C hC)
  · rintro ⟨hv, hsupp⟩
    refine ⟨hv, ?_⟩
    intro C hC
    exact (supports_iff_setSupport).mpr (hsupp (↑C) ⟨C, hC, rfl⟩)

/-- Cellwise corollary of the bridge: the executable step and the `Set` step coincide
as functions, after coercion.  `toAbs (acStepF Fs a) = acStep {↑C | C ∈ Fs} (toAbs a)`. -/
theorem toAbs_acStepF (Fs : List (Finset (Fin k → V))) (a : AbsF V k) :
    toAbs (acStepF Fs a) = acStep {S : Set (Str V k) | ∃ C ∈ Fs, S = ↑C} (toAbs a) := by
  funext i
  ext v
  rw [mem_toAbs]
  exact acStepF_mem_iff Fs a i v

/-! ## 5.  The two concrete CSPs and the `#eval` classifier — RUNNABLE.

We instantiate the classifier on the *same two systems* `LDTCompleteness` proves about,
over `V = Bool`:

* **the chain** `{x₀ = false, x₀ = x₁}` — width-1, proved SOLVED (`acStep_chain_solves`);
* **the XOR system** `{x = y, y = z, x⊕y⊕z = 0}` — affine, proved STUCK / ABSTAINED
  (`acStep_xor_abstains`).

Each constraint is given as the explicit `Finset` of its allowed `Bool`-tuples, built
by filtering `Finset.univ` of `Fin k → Bool`.  `#eval acSolves? chainF` should print
`true`; `#eval acSolves? xorF` should print `false` — matching the proven theory. -/

/-- All `Bool`-assignments to `k` cells (the tuple universe), as a `Finset`. -/
def allTuples (k : ℕ) : Finset (Fin k → Bool) := Finset.univ

/-- The chain constraint `x₀ = false`, as the `Finset` of allowed 2-tuples. -/
def cU0F : Finset (Fin 2 → Bool) := (allTuples 2).filter (fun t => t 0 = false)
/-- The chain constraint `x₀ = x₁`, as the `Finset` of allowed 2-tuples. -/
def cE01F : Finset (Fin 2 → Bool) := (allTuples 2).filter (fun t => t 0 = t 1)

/-- **The chain CSP** `{x₀ = false, x₀ = x₁}` (width-1 / kind-0), as a `List` of
allowed-tuple `Finset`s — the computable analogue of `chainCs`. -/
def chainF : List (Finset (Fin 2 → Bool)) := [cU0F, cE01F]

/-- The XOR constraint `x = y` (cells 0,1 of three), as allowed 3-tuples. -/
def xC1F : Finset (Fin 3 → Bool) := (allTuples 3).filter (fun t => t 0 = t 1)
/-- The XOR constraint `y = z` (cells 1,2), as allowed 3-tuples. -/
def xC2F : Finset (Fin 3 → Bool) := (allTuples 3).filter (fun t => t 1 = t 2)
/-- The XOR constraint `x ⊕ y ⊕ z = 0` (even parity), as allowed 3-tuples. -/
def xC3F : Finset (Fin 3 → Bool) :=
  (allTuples 3).filter (fun t => xor (xor (t 0) (t 1)) (t 2) = false)

/-- **The XOR CSP** `{x = y, y = z, x⊕y⊕z = 0}` (affine / kind-2), as a `List` of
allowed-tuple `Finset`s — the computable analogue of `xorCs`. -/
def xorF : List (Finset (Fin 3 → Bool)) := [xC1F, xC2F, xC3F]

-- ─────────────────────────────────────────────────────────────────────────────
-- The computable kind-discriminator, RUN.  Outputs must match the proven facts:
--   chain  →  true   (matches `acStep_chain_solves`)
--   XOR    →  false  (matches `acStep_xor_abstains`)
-- ─────────────────────────────────────────────────────────────────────────────

/-- The chain is **solved** by AC deduction (computed). -/
#eval acSolves? chainF        -- expected: true

/-- The XOR system is **not solved** — AC deduction abstains (computed). -/
#eval acSolves? xorF          -- expected: false

-- Finer-grained executable views (the fixpoint domains themselves), for inspection:

/-- The chain's AC fixpoint pins `(false, false)` — each cell a singleton. -/
#eval (List.ofFn (fun i : Fin 2 => (acFixpoint chainF i).sort (· ≤ ·)))
                              -- expected: [[false], [false]]

/-- The XOR system's AC fixpoint is still the full grid — both values live in every
cell: the global parity coupling is invisible to per-cell, per-constraint reasoning. -/
#eval (List.ofFn (fun i : Fin 3 => (acFixpoint xorF i).sort (· ≤ ·)))
                              -- expected: [[false, true], [false, true], [false, true]]

/-! ## 6.  The classifier's verdicts.

The `#eval`s above *run* the classifier: `acSolves? chainF` prints `true`,
`acSolves? xorF` prints `false` — the runnable mirror of
`LDTCompleteness.ac_kind_discriminates`.  We deliberately do **not** re-prove these
`Bool` outputs as theorems: `decide` reduces the `Finset` fixpoint in the kernel
(pathologically slow — minutes), and `native_decide` would inject the `ofReduceBool`
axiom.  Neither is worth it, because the *mathematics* of the verdicts is already
proven, axiom-clean, on the `Set` side — `acStep_chain_solves`, `acStep_xor_abstains`,
`ac_kind_discriminates`.  This file is the **executable demonstration**; those
theorems are the **proof**. -/

/-! ## 7.  End-of-file inventory.

**BUILT (all computable; `#eval`-able):**
  * §1 — `AbsF` (computable abstract state `Fin k → Finset V`), `topF` (full grid).
  * §2 — `consistentTuple`, `supports` (decidable support test), **`acStepF`** (one
    executable arc-consistency step) + `mem_acStepF`, `acStepF_reductive`.
  * §3 — `acIterate`, **`acFixpoint`** (iterate to lattice height `k * card V`),
    `isSolvedF`, **`acSolves?`** (the `Bool` kind-discriminator).
  * §4 — `toAbs` (coercion), `supports_iff_setSupport`, and the **bridge**
    `acStepF_mem_iff` : `v ∈ acStepF Fs a i ↔ v ∈ acStep {↑C | C∈Fs} (toAbs a) i`
    (PROVED — the executable step *is* `acStep`, computed), with corollary
    `toAbs_acStepF`.
  * §5 — the two concrete CSPs `chainF`, `xorF` (allowed-tuple `Finset`s) and the
    **`#eval` demonstrations**: `acSolves? chainF` ⇒ `true`, `acSolves? xorF` ⇒ `false`.
  * §6 — the verdicts are *run* by the `#eval`s (chain ⇒ `true`, XOR ⇒ `false`) and
    *proved* axiom-clean on the `Set` side (`acStep_chain_solves`,
    `acStep_xor_abstains`); not re-proved by `decide` (kernel-slow on `Finset`) nor
    `native_decide` (would add an axiom).

**HONEST SCOPE / what is NOT claimed:**
  * The proved bridge is **single-step** (`acStepF_mem_iff`): the executable step's
    membership equals `acStep`'s support condition, value-by-value.  We do **not**
    prove a fixpoint-trajectory equality against the `noncomputable` `Set` fixpoint
    (the `Set` side has no iteration count / computed fixpoint here).  The `#eval`
    verdicts rest on (i) this proved one-step correspondence and (ii) exact agreement
    with the independently-proven `acStep_chain_solves` / `acStep_xor_abstains` — *not*
    on a claimed full-run `Set`↔`Finset` equality.
  * `acFixpoint` iterates a **sound height bound** (`k * card V`) rather than detecting
    stabilisation; for these tiny systems it reaches the fixpoint with room to spare
    (the `#eval`s confirm the verdicts).  A stabilisation-detecting loop and a
    proof that the bound is tight are deferred — they are not needed for the
    discriminator to be correct on a finite lattice.
  * Generality: the classifier is fully general in `(V, k, Fs)` (any `DecidableEq`
    `Fintype` vocabulary, any allowed-tuple-`Finset` CSP); only the two `#eval`
    demonstrations are specialised to `Bool` to mirror `LDTCompleteness`.
-/

end LatticeDeduction
end Integrations
end Graphplay
