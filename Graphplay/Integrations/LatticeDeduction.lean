/-
# Graphplay.Integrations.LatticeDeduction

**A machine-checked SOUNDNESS skeleton for Lattice Deduction Transformers
(LDT, Davis–Haller–Alfarano–Santolucito, arXiv:2605.08605).**

LDT solves combinatorial puzzles (Sudoku, mazes, …) by training a small looped
transformer to *learn the best abstract transformer* of a textbook
abstract-interpretation construction.  The concrete domain is the powerset of
fixed-length solution strings `S = Fin k → V`; the abstract domain is the
**grid powerset lattice** `A = Fin k → Set V` of per-cell candidate sets; solving
is **greatest-fixpoint Kleene descent** of a monotone *reductive* deduction
operator `dedₚ a = α (γ a ∩ ‖p‖)` from `⊤` toward `⊥`.

The paper states the Galois connection `α ⊣ γ` verbatim (their Appendix A) and
characterises the per-forward-pass projection as the best abstract transformer,
but it only **asserts soundness empirically** — "the solver returns a correct
answer or abstains" (Tables 1–3, §4.2).  There is **no machine-checked soundness
artifact** in the released code or paper.  This file supplies one.

What is PROVED here (real defs, non-vacuous, axiom-clean unless noted):

* **§1–2  The abstract domain.**  `A := Fin k → Set V` with the pointwise
  inclusion order is a `CompleteLattice` (off the shelf: `Pi ∘ Set`); `⊤` is the
  all-candidates grid, `⊥` is the everywhere-empty grid.  Concretisation
  `γ a = {s | ∀ i, s i ∈ a i}` and abstraction `α S' i = (· i) '' S'` are the
  paper's maps line-for-line.

* **§3  The Galois connection `α ⊣ γ`** (`alpha_gc_gamma : GaloisConnection α γ`).
  This is the order-theoretic adjunction the paper writes down and graphplay did
  **not** previously contain (there is *no* `GaloisConnection`/`GaloisInsertion`
  anywhere else in the repo — every other "adjoint" is operator self-adjointness).
  It is the genuinely new structural brick.  The two round-trip laws
  `S' ⊆ γ (α S')` (sound) and `α (γ a) ⊆ a` (reductive re-abstraction) fall out
  as `.le_u_l` / `.l_u_le`.  HONEST: it is a Galois *connection*, not a Galois
  *insertion* — `α ∘ γ ≠ id` in general (the abstraction loses inter-cell
  correlation; the paper's Fig. 5), and we do **not** claim insertion.

* **§4  The deduction step is a sound reductive closure.**
  `dedP cons a := α (γ a ∩ cons)` (`cons = ‖p‖`) satisfies
  - `dedP_reductive  : dedP cons a ≤ a`            (never *adds* candidates), and
  - `dedP_sound      : cons ∩ γ a ⊆ γ (dedP cons a)` (never *drops a real
    solution*: every concrete string consistent with both `a` and the
    constraints survives the abstract step).
  These are exactly the paper's defining properties of `dedₚ`, and each is one
  application of a Galois round-trip law.

* **§5  Run-level soundness via Tower-8** (the empirical claim, now proven).
  Importing **exactly one** graphplay asset — Tower-8's coalgebraic run-invariant
  `Graphplay.Tower8.TransitionCoalg.stepInv_preserved` — we lift step-soundness
  to the whole Solve trajectory.  Model the run as a `TransitionCoalg` whose
  admissible turns are *bundled sound narrowing operators* (`SoundStep cons`) and
  whose safety predicate is `Good a := cons ⊆ γ a` ("the abstract state still
  admits every true solution").  Then:
  - `good_top`              : `Good ⊤`               (descent starts admitting all);
  - `good_preserved_step`   : every sound narrowing preserves `Good`;
  - `dedRun_preserves_solutions` : along **any** reachable Solve-run from `⊤`,
    every reachable abstract state admits every true solution
    (`cons ⊆ γ a` for all reachable `a`); and the headline corollary
  - `solved_state_is_correct` : if a reachable state is *solved* (a singleton per
    cell, pinning the string `s`) and the puzzle is satisfiable, then the solved
    answer is exactly the solution set, `cons = {s}` — i.e. **the solver's output
    is correct**.  This is LDT's empirical-soundness claim, machine-checked.

## NOTE — relationship to graphplay's refinement quotient (read this)

LDT is the **lfp/gfp DUAL** of graphplay's equitable-refinement quotient, **not an
instance of it.**  graphplay proves Weisfeiler–Leman colour refinement is the
**least** fixpoint of a monotone *splitting / information-increasing* operator
that *builds* an exact symmetry-reduction abstraction (`WL.wlRefine_stable`,
`WL.wlRefine_coarsestEquitable`); LDT computes the **greatest** fixpoint of a
monotone *reductive / information-decreasing* operator *within* an
over-approximation abstraction (deduction descends from `⊤`).  The two lattices
are different *kinds*: graphplay's quotient is an **exactness** statement
(the `r×r` symmetric quotient computes the *same* spectrum — a linear-algebra
subspace isometry, *not* a `GaloisConnection`), whereas LDT's `A` is an
**over-approximation / information** lattice whose whole point is *inexactness*
(`α ∘ γ` strictly loses cell-correlations).  So we import the equitable quotient
**not at all**; the *only* reusable graphplay asset is the abstract coalgebraic
run-invariant `stepInv_preserved` (Tower-8), used in §5.

The **spectral-gap-convergence bridge is RETRACTED for LDT.**  LDT's loop is gfp
Kleene iteration of a monotone reductive operator on a *finite discrete* lattice;
termination is **well-foundedness** ("the lattice is finite and each step
strictly decreases the alive-candidate count", §4.2).  There is **no iterated
linear operator and no `λ₂`** in the loop, so the `k* ≈ log ε / log|λ₂/λ₁|`
mixing law does not apply; LDT's depth is the **Cousot fixpoint-iteration height**
(longest sound deduction chain), a combinatorial, not spectral, quantity.

References:
  * Davis, Haller, Alfarano, Santolucito, *Lattice Deduction Transformers*,
    arXiv:2605.08605, 2026 — Appendix A (Galois connection, best abstract
    transformer, gfp characterisation).
  * D'Silva, Haller, Kroening, *Abstract Conflict Driven Learning*, POPL 2013 —
    CDCL conflict-analysis as abstract interpretation (LDT's lineage).
  * Cousot, Cousot, *Abstract interpretation: a unified lattice model …*,
    POPL 1977 — Galois connections, fixpoint transfer, iteration height.
  * Graphplay `Tower8.lean` — the coalgebraic `stepInv_preserved` run-invariant
    reused here (the *only* imported graphplay asset).
-/

import Graphplay.Tower8
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

namespace Graphplay
namespace Integrations
namespace LatticeDeduction

open Set

/-! ## 1.  Carriers: solution strings and the grid-powerset abstract domain.

We fix a finite vocabulary `V` and a number of cells `k`.  A **solution string**
is a `Str := Fin k → V` (one symbol per cell); the **concrete domain** is
`Set Str` ordered by `⊆`.  The **abstract domain** is the grid-powerset lattice
`Abs := Fin k → Set V` (a per-cell candidate set), ordered by pointwise
inclusion.  Both are off-the-shelf complete lattices. -/

-- `V` is a concrete finite vocabulary; we keep everything in universe `0` so the
-- abstract carrier `Abs V k`, the input alphabet `SoundStep cons`, and the
-- observation `Unit` all live in the single universe `Tower8.TransitionCoalg`
-- quantifies over.  (LDT's `V` is always a small finite alphabet, e.g. `Fin 9`.)
variable {V : Type} {k : ℕ}

/-- A **solution string**: one symbol per cell.  The concrete domain `C = ℘(Str)`
is `Set Str`.  (Sudoku: `V = Fin 9`, `k = 81`.) -/
abbrev Str (V : Type) (k : ℕ) : Type := Fin k → V

/-- The **grid-powerset abstract domain** `A = ∏ᵢ ℘(V)`: a candidate set per
cell, ordered by **pointwise inclusion** (`a ⊑ b ↔ ∀ i, a i ⊆ b i`).  This is the
paper's grid powerset lattice; the `CompleteLattice` instance is the standard
`Pi`-of-`Set` one (meet/join pointwise `∩`/`∪`, `⊤ = fun _ => univ`,
`⊥ = fun _ => ∅`). -/
abbrev Abs (V : Type) (k : ℕ) : Type := Fin k → Set V

-- The abstract domain is a complete lattice off the shelf (Pi ∘ Set).
example : CompleteLattice (Abs V k) := inferInstance

/-- The bottom abstract state is the **everywhere-empty grid** (some cell — here
every cell — empty): the lattice `⊥`, identified by the paper with a *conflict*
(an unsatisfiable state). -/
example : (⊥ : Abs V k) = fun _ => (∅ : Set V) := rfl

/-- The top abstract state is the **all-candidates grid** (every cell holds the
full vocabulary): the lattice `⊤`, the starting point of gfp descent. -/
example : (⊤ : Abs V k) = fun _ => (univ : Set V) := rfl

/-! ## 2.  The abstraction `α` and concretisation `γ` (paper, App. A.1).

```
            α
      ℘(Str) ⇄ Abs        α S' i = { s i : s ∈ S' }   (per-cell projection)
            γ              γ a    = { s : ∀ i, s i ∈ a i }
```
-/

/-- **Concretisation** `γ : Abs → ℘(Str)`: the strings that pick, in every cell,
a currently-live candidate.  `γ a = { s | ∀ i, s i ∈ a i }` — the paper's upper
adjoint, verbatim. -/
def gamma (a : Abs V k) : Set (Str V k) := {s | ∀ i, s i ∈ a i}

/-- **Abstraction** `α : ℘(Str) → Abs`: the per-cell projection of a set of
strings.  `α S' i = { s i | s ∈ S' } = (· i) '' S'` — the paper's lower adjoint,
verbatim. -/
def alpha (S' : Set (Str V k)) : Abs V k := fun i => (fun s => s i) '' S'

@[simp] theorem mem_gamma {a : Abs V k} {s : Str V k} :
    s ∈ gamma a ↔ ∀ i, s i ∈ a i := Iff.rfl

@[simp] theorem mem_alpha {S' : Set (Str V k)} {i : Fin k} {v : V} :
    v ∈ alpha S' i ↔ ∃ s ∈ S', s i = v := by
  simp only [alpha, Set.mem_image]

/-! ## 3.  The Galois connection `α ⊣ γ`  (the genuinely new structural brick).

This is the adjunction the paper writes down (App. A.1) and that graphplay did
not previously contain.  `GaloisConnection α γ` is, by definition,
`∀ S' a, α S' ≤ a ↔ S' ≤ γ a`; both sides unfold to *"every string in `S'` picks
a live candidate in every cell"*, so the proof is a short bi-unfolding. -/

/-- **The Galois connection `α ⊣ γ`** between the concrete domain `℘(Str)` and the
grid-powerset abstract domain `Abs` (paper App. A.1).  `α` is the lower adjoint,
`γ` the upper.  Both `α S' ≤ a` (pointwise: `∀ i, (· i)''S' ⊆ a i`) and
`S' ⊆ γ a` (`∀ s ∈ S', ∀ i, s i ∈ a i`) say the same thing, so the bi-implication
is immediate.

This is **non-vacuous and genuine** (no degenerate witness): it is the standard
over-approximation adjunction, and `α`/`γ` are the real projection/cylinder maps,
not stubs. -/
theorem alpha_gc_gamma : GaloisConnection (alpha (V := V) (k := k)) gamma := by
  intro S' a
  constructor
  · -- α S' ≤ a  ⟹  S' ⊆ γ a
    intro h s hs i
    exact h i ⟨s, hs, rfl⟩
  · -- S' ⊆ γ a  ⟹  α S' ≤ a
    intro h i
    rintro v ⟨s, hs, rfl⟩
    exact h hs i

/-- The **unit / soundness** round-trip law (paper: `S ⊆ γ(α S)` — "abstraction
is sound; the round trip over-approximates").  Direct from the connection. -/
theorem subset_gamma_alpha (S' : Set (Str V k)) : S' ⊆ gamma (alpha S') :=
  alpha_gc_gamma.le_u_l S'

/-- The **counit / reductive-re-abstraction** law (paper: `α(γ a) ⊑ a` —
"re-abstraction strips unwitnessed structure").  Direct from the connection.
Note this is `≤`, NOT `=`: the connection is **not** a Galois insertion
(`α ∘ γ ≠ id`; the abstraction loses inter-cell correlation — the paper's
Fig. 5), and we do not claim it is. -/
theorem alpha_gamma_le (a : Abs V k) : alpha (gamma a) ≤ a :=
  alpha_gc_gamma.l_u_le a

/-- `γ` is monotone (upper adjoints are; paper: `a ⊑ b ⟹ γ a ⊆ γ b`). -/
theorem gamma_mono : Monotone (gamma (V := V) (k := k)) :=
  alpha_gc_gamma.monotone_u

/-- `α` is monotone (lower adjoints are). -/
theorem alpha_mono : Monotone (alpha (V := V) (k := k)) :=
  alpha_gc_gamma.monotone_l

/-- Sanity / non-vacuity: `γ ⊤ = univ` — the all-candidates grid concretises to
*every* string.  (Used in §5: the run starts admitting all solutions.) -/
@[simp] theorem gamma_top : gamma (⊤ : Abs V k) = (univ : Set (Str V k)) := by
  ext s; simp [gamma]

/-! ## 4.  The deduction step `dedₚ` is a sound reductive closure.

The best abstract transformer for an instance with solution/constraint set
`cons = ‖p‖ ⊆ Str` (paper, App. A.2, §4):
```
dedₚ a = α (γ a ∩ ‖p‖)        -- "keep only candidates surviving in some valid solution"
```
We prove its two defining properties.  Each is one Galois round-trip law. -/

/-- **The deduction step** `dedₚ a = α (γ a ∩ ‖p‖)` (paper App. A.2).  `cons` is
the puzzle's constraint/solution set `‖p‖`.  At inference LDT's looped
transformer *learns* this map; here we reason about the exact best transformer it
targets. -/
def dedP (cons : Set (Str V k)) (a : Abs V k) : Abs V k := alpha (gamma a ∩ cons)

/-- **Reductive**: `dedₚ a ⊑ a` — deduction only ever *removes* candidates, never
adds (paper: `dedₚ` is a lower/reductive operator).  Proof: `α (γ a ∩ cons) ≤
α (γ a) ≤ a` by monotonicity then the counit `α (γ a) ⊑ a`. -/
theorem dedP_reductive (cons : Set (Str V k)) (a : Abs V k) :
    dedP cons a ≤ a :=
  le_trans (alpha_mono (inter_subset_left)) (alpha_gamma_le a)

/-- **Sound (never drops a real solution)**: every concrete string that is
consistent with both the current abstract state `a` *and* the constraints `cons`
survives the abstract deduction step:
`cons ∩ γ a ⊆ γ (dedₚ a)`.

This is the soundness heart — it says the abstract step is an *over*-approximation
of the concrete narrowing, so no genuine solution is ever lost.  Proof: it is the
unit law `S' ⊆ γ (α S')` at `S' = γ a ∩ cons`, up to commuting the intersection. -/
theorem dedP_sound (cons : Set (Str V k)) (a : Abs V k) :
    cons ∩ gamma a ⊆ gamma (dedP cons a) := by
  -- `γ a ∩ cons ⊆ γ (α (γ a ∩ cons)) = γ (dedP cons a)` is the unit law;
  -- rewrite `cons ∩ γ a` to `γ a ∩ cons`.
  rw [inter_comm]
  exact subset_gamma_alpha (gamma a ∩ cons)

/-- `dedₚ` is monotone (it is `α ∘ (· ∩ cons) ∘ γ`, a composite of monotone
maps).  Recorded for completeness — gfp Kleene iteration needs monotonicity. -/
theorem dedP_mono (cons : Set (Str V k)) : Monotone (dedP cons) := by
  intro a b hab
  refine alpha_mono ?_
  exact inter_subset_inter_left cons (gamma_mono hab)

/-! ## 5.  Run-level soundness via Tower-8's `stepInv_preserved`.

We now lift *step* soundness to the *run* — LDT's empirical claim
("returns a correct answer or abstains").  We import **exactly one** graphplay
asset: Tower-8's coalgebraic safety invariant
`Graphplay.Tower8.TransitionCoalg.stepInv_preserved`.

The Solve run descends through abstract states by repeatedly applying *some* sound
narrowing.  We bundle "a sound narrowing operator" as a subtype and use it as the
coalgebra's input alphabet, so that *every* admissible transition is sound by
construction (the hypothesis shape `stepInv_preserved` needs). -/

open Graphplay.Tower8 Graphplay.Tower8.TransitionCoalg

/-- A **sound narrowing operator** for constraint set `cons`: a map on abstract
states that is reductive (`f a ⊑ a`) and never drops a real solution
(`cons ∩ γ a ⊆ γ (f a)`).  These are exactly the operators LDT's learned `dedₚ`
is *supposed* to be; `dedP cons` itself is one (`dedStep`). -/
def SoundStep (cons : Set (Str V k)) : Type _ :=
  {f : Abs V k → Abs V k // ∀ a, f a ≤ a ∧ cons ∩ gamma a ⊆ gamma (f a)}

/-- The exact best transformer `dedₚ` is a sound narrowing operator (it satisfies
both clauses by §4) — witnessing that `SoundStep cons` is **inhabited**, so the
run-soundness theorem below is non-vacuous. -/
def dedStep (cons : Set (Str V k)) : SoundStep cons :=
  ⟨dedP cons, fun a => ⟨dedP_reductive cons a, dedP_sound cons a⟩⟩

/-- **The deduction-run coalgebra.**  Carrier = the abstract domain `Abs`; the
input alphabet (admissible "turns") = sound narrowing operators `SoundStep cons`;
a turn `f` transitions `a ↦ f.1 a`.  The observation is irrelevant to the safety
invariant (the run-soundness keystone reads only transitions), so we take
`Obs = Unit`.

This realises Tower-8's abstract `TransitionCoalg` interface with the LDT Solve
loop's transition structure. -/
def dedRun (cons : Set (Str V k)) : TransitionCoalg Unit (SoundStep cons) where
  Carrier := Abs V k
  step a := ((), fun f => f.1 a)

@[simp] theorem dedRun_next (cons : Set (Str V k)) (a : Abs V k)
    (f : SoundStep cons) : (dedRun cons).next a f = f.1 a := rfl

/-- The **safety invariant**: the abstract state still admits *every* true
solution, `cons ⊆ γ a`.  (This is the assessment's `Good a := ‖p‖ ∩ γ ⊤ ⊆ γ a`,
which since `γ ⊤ = univ` is exactly `‖p‖ ⊆ γ a`.) -/
def Good (cons : Set (Str V k)) (a : Abs V k) : Prop := cons ⊆ gamma a

/-- `Good` holds at the descent's starting point `⊤`: `cons ⊆ γ ⊤ = univ`. -/
theorem good_top (cons : Set (Str V k)) : Good cons (⊤ : Abs V k) := by
  simp [Good, gamma_top]

/-- **Every sound narrowing preserves `Good`.**  If the state still admits all
true solutions (`cons ⊆ γ a`) and `f` is a sound narrowing, then `f a` still
admits all true solutions.  Proof: `cons = cons ∩ γ a ⊆ γ (f a)` using
`cons ⊆ γ a` and `f`'s soundness clause.  This is the per-step content the
run-invariant integrates. -/
theorem good_preserved_step (cons : Set (Str V k)) (a : Abs V k)
    (f : SoundStep cons) (hgood : Good cons a) : Good cons (f.1 a) := by
  have hsound := (f.2 a).2          -- cons ∩ γ a ⊆ γ (f a)
  intro s hs
  exact hsound ⟨hs, hgood hs⟩       -- s ∈ cons and s ∈ γ a, so s ∈ γ (f a)

/-- **Run-level soundness (LDT's empirical claim, machine-checked).**

Along **any** reachable Solve-run from the all-candidates start `⊤`, every
reachable abstract state still admits every true solution: `cons ⊆ γ a`.  No
sound deduction step — and hence no length of run of them — ever excludes a real
solution.

This is `Tower8.TransitionCoalg.stepInv_preserved` (the *only* imported graphplay
asset) instantiated at the deduction-run coalgebra, with `Good` and its proved
one-step preservation. -/
theorem dedRun_preserves_solutions (cons : Set (Str V k)) {a : Abs V k}
    (hreach : (dedRun cons).Reachable (⊤ : Abs V k) a) :
    cons ⊆ gamma a :=
  stepInv_preserved (dedRun cons) (Good cons)
    (fun x f hx => good_preserved_step cons x f hx)
    hreach (good_top cons)

/-! ### The headline corollary: a *solved* reachable state is correct.

LDT terminates a chain "solved" when every cell is a singleton (one candidate
left).  Such a state `a` concretises to a single string `s` (`γ a = {s}`).  By
run-soundness `cons ⊆ γ a = {s}`, so a satisfiable puzzle (`cons` nonempty) has
`cons = {s}`: **the solved answer is exactly the solution set** — correct. -/

/-- A **solved** abstract state: every cell has been narrowed to a single
candidate, `∀ i, a i = {s i}`, pinning the string `s`.  (This is LDT's
termination condition "every cell determined".) -/
def Solved (a : Abs V k) (s : Str V k) : Prop := ∀ i, a i = {s i}

/-- A solved state concretises to the single string it pins: `γ a = {s}`.  Both
inclusions are pointwise: `t ∈ γ a ↔ ∀ i, t i ∈ {s i} ↔ ∀ i, t i = s i ↔ t = s`. -/
theorem gamma_solved {a : Abs V k} {s : Str V k} (h : Solved a s) :
    gamma a = {s} := by
  ext t
  simp only [mem_gamma, mem_singleton_iff]
  constructor
  · intro ht
    funext i
    have : t i ∈ a i := ht i
    rw [h i, mem_singleton_iff] at this
    exact this
  · rintro rfl i
    rw [h i]; exact rfl

/-- **The solver is correct (LDT empirical soundness, proven).**

If a reachable Solve-state is *solved* — every cell determined, pinning string
`s` — and the puzzle is **satisfiable** (`cons.Nonempty`), then the solved answer
is exactly the puzzle's solution set: `cons = {s}`.  In particular the returned
`s` is a genuine solution (`s ∈ cons`) and the *unique* one.

Read together with `dedRun_preserves_solutions`: every reachable Solve-state
admits all true solutions, and a *solved* one collapses that to a single string,
which is therefore the correct (and complete) answer.  This is precisely the
property LDT asserts empirically and never proves: **"returns a correct answer or
abstains."** -/
theorem solved_state_is_correct (cons : Set (Str V k)) {a : Abs V k}
    {s : Str V k} (hreach : (dedRun cons).Reachable (⊤ : Abs V k) a)
    (hsolved : Solved a s) (hsat : cons.Nonempty) :
    cons = {s} := by
  have hsub : cons ⊆ gamma a := dedRun_preserves_solutions cons hreach
  rw [gamma_solved hsolved] at hsub          -- cons ⊆ {s}
  -- cons ⊆ {s} and cons nonempty ⟹ cons = {s}
  apply Set.Subset.antisymm hsub
  obtain ⟨c, hc⟩ := hsat
  have : c = s := hsub hc
  rw [← this]
  exact Set.singleton_subset_iff.mpr hc

/-- Immediate restatement: the solved answer `s` **is a genuine solution** of a
satisfiable instance (`s ∈ cons`).  No abstention case here — *if* the solver
solves, the answer is sound. -/
theorem solved_answer_mem (cons : Set (Str V k)) {a : Abs V k}
    {s : Str V k} (hreach : (dedRun cons).Reachable (⊤ : Abs V k) a)
    (hsolved : Solved a s) (hsat : cons.Nonempty) :
    s ∈ cons := by
  rw [solved_state_is_correct cons hreach hsolved hsat]
  exact mem_singleton s

/-! ## 6.  End-of-file inventory.

**PROVED (real defs, non-vacuous):**
  * §2 — `gamma`, `alpha` (the paper's `γ`, `α` verbatim) + membership simp-lemmas.
  * §3 — **`alpha_gc_gamma : GaloisConnection α γ`** (the new structural brick;
    graphplay had no `GaloisConnection` before), with the unit/counit laws
    `subset_gamma_alpha`, `alpha_gamma_le`, monotonicity of both adjoints, and
    `gamma_top`.
  * §4 — `dedP` (= `dedₚ`), **`dedP_reductive`** (`dedₚ a ⊑ a`) and
    **`dedP_sound`** (`cons ∩ γ a ⊆ γ (dedₚ a)`) — the deduction step is a sound
    reductive closure; plus `dedP_mono`.
  * §5 — the deduction-run coalgebra `dedRun` realising Tower-8's
    `TransitionCoalg`; `SoundStep`/`dedStep` (inhabitation ⟹ non-vacuity);
    `good_top`, `good_preserved_step`, and the keystone
    **`dedRun_preserves_solutions`** (run-level soundness via the imported
    `Tower8…stepInv_preserved`), with corollaries `gamma_solved`,
    **`solved_state_is_correct`** and `solved_answer_mem` (the solver's output is
    correct) — LDT's empirical-soundness claim, machine-checked.

**HONEST RESIDUAL / scope:**
  * `α ⊣ γ` is a Galois *connection*, not an *insertion*: `α ∘ γ ≠ id` in general
    (inter-cell correlation is lost — the paper's Fig. 5).  We deliberately do
    **not** claim insertion, and `dedP`'s *idempotence* (the third lower-closure
    law beyond reductive + monotone) is therefore **not** claimed here; it holds
    for the exact best transformer but is not among the soundness obligations.
  * `solved_state_is_correct` covers the "returns a correct answer" half of LDT's
    "correct-or-abstains"; the "abstains" half is the completeness/branching layer
    (CLS-head conflict detection + search), which is *outside* the soundness
    skeleton and not modelled here.
  * The deduction *operator* learned by the transformer is approximated, not the
    exact `dedₚ`; this file certifies the soundness of the *abstract* skeleton the
    learned operator targets (any operator in `SoundStep cons`), which is exactly
    the level at which "trained to be sound" is a meaningful guarantee.

**NOT IMPORTED / RETRACTED (per the assessment):**
  * graphplay's equitable-refinement quotient is **not** imported (wrong lattice
    kind — exact symmetry-reduction, the lfp dual; see the file-header NOTE).
  * the spectral-gap convergence bridge is **retracted** for LDT (discrete gfp
    Kleene descent has no iterated linear operator / `λ₂`; depth is Cousot
    fixpoint height, not a spectral gap).
-/

end LatticeDeduction
end Integrations
end Graphplay
