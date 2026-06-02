/-
# Graphplay.Integrations.LDTHierarchy — the "framework of kinds" is a *real*
hierarchy: a richer abstract domain sees structure a coarser one is blind to.

`LatticeDeduction` builds the LDT **per-cell** projection lattice
`Abs = Fin k → Set V` and its Galois connection `α ⊣ γ`; `LDTCompleteness` shows
this lattice's generalized arc consistency (`acStep`) is *stuck at `⊤`* on the
affine XOR system — soundly incomplete.  The file header there names the cause:
the per-cell abstraction (`Tower9.ldt_lossy`, `α ∘ γ ≠ id`) **forgets inter-cell
correlation**.  This file turns that diagnosis into a *theorem about a lattice
hierarchy*: it exhibits, on one concrete correlation, a STRICT expressiveness gap
between two LDT-style abstract domains.

The witness is the **2-cell equality relation** (the atom of XOR):
`R := {t : Str Bool 2 | t 0 = t 1} = {(false,false), (true,true)}` — a *proper*
subset of all 4 strings (it excludes `(false,true)` and `(true,false)`).

* **The per-cell domain COLLAPSES the correlation to `⊤`** (`alpha_eq_top`):
  `α R = ⊤`.  Each cell, *projected independently*, still ranges over all of
  `{false,true}` (cell 0 is `false` in `(false,false)` and `true` in
  `(true,true)`, ditto cell 1), so the per-cell lattice's *best* description of
  "`x = y`" is "anything goes" — even though `R ≠ univ` (`R_ne_univ`).  This is
  `α (γ (α R)) = univ ⊋ R` made fully concrete: **the per-cell lattice literally
  cannot represent `x = y`.**  It is exactly why `acStep` is stuck on the single
  equality constraint (`acStep_eq_stuck`) and on XOR (`acStep_xor_stuck`,
  imported).

* **A PAIR domain `PairAbs := Set (Bool × Bool)`** — candidate sets over the
  *ordered pair* of the two cells — with its own concretisation `gammaPair`,
  abstraction `alphaPair`, and a genuine **Galois connection
  `alphaPair ⊣ gammaPair`** (`pair_gc`).  The pair lattice **retains `R` exactly**
  (`alphaPair_eq`): `αₚ R = {(false,false),(true,true)} ≠ ⊤ₚ` (`alphaPair_ne_top`).

* **Headline — the hierarchy is real** (`pair_strictly_richer_than_cell`): on the
  *same* relation `R`, the per-cell abstraction is `⊤` (blind) while the pair
  abstraction is `R` itself, *exact* (`gammaPair_alphaPair_eq : γₚ (αₚ R) = R`,
  i.e. `αₚ` is an *insertion* round-trip here where `α` is total collapse).  Pair
  > cell, strictly, witnessed.

* **And it is the same gap that bounds AC** (`pair_narrows_where_cell_stuck`): a
  pair-level support step `pairStep` — the path- / 2-consistency analogue of
  `acStep` — narrows the equality constraint from `univ` to exactly `R`
  (`pairStep_eq_solves`), *whereas `acStep` makes no progress at all*
  (`acStep_eq_stuck`).  `pairStep` is itself reductive and certificate-checked
  (`pairStep_reductive`, `pairStep_certified`), so this is a *sound* narrowing the
  per-cell domain cannot perform.  This is the concrete reason path consistency
  beats arc consistency on XOR — the "richer kind" sees the correlation.

HONESTY / scope.  We do **not** claim a full "pair-AC solves the 3-cell XOR
system."  The honest, proven deliverable is the **strict lattice-expressiveness
gap on the equality correlation** (`pair_strictly_richer_than_cell`) *plus* the
matching one-constraint narrowing contrast (`pair_narrows_where_cell_stuck`):
pair-level support narrows the equality constraint that cell-level support leaves
at `⊤`.  Lifting pair consistency to a full XOR solver (3-clique path
consistency, the join over all pair-cells) is the natural next file; here we
prove the *kind gap itself*, concretely, on the atom.

References:
  * Davis, Haller, Alfarano, Santolucito, *Lattice Deduction Transformers*,
    arXiv:2605.08605, 2026 — the per-cell projection lattice and `α ⊣ γ`.
  * Montanari, *Networks of constraints*, 1974; Mackworth, *Consistency in
    networks of relations*, AIJ 1977 — arc vs. path consistency; XOR/parity is
    the canonical relation arc consistency cannot enforce but path consistency
    can.
  * Feder, Vardi, *Computational structure of monotone monadic SNP…*, 1998 —
    bounded width; affine/Maltsev constraints escape local consistency of any
    fixed arity, the hierarchy this file's gap is the first rung of.
-/

import Graphplay.Integrations.LDTCompleteness

namespace Graphplay
namespace Integrations
namespace LatticeDeduction

open Set

/-! ## 1.  The witness relation: 2-cell equality `R = {x = y}`.

`R` is the *atom* of the XOR system (`xC1` on two cells).  Over `Bool` it is the
two "diagonal" strings; crucially it is a **proper** subset of all four strings,
so any abstraction that maps it to `⊤` has genuinely lost information. -/

/-- The **2-cell equality relation** `R := {t : Str Bool 2 | t 0 = t 1}`.
Concretely `{(false,false), (true,true)}`.  This is the inter-cell correlation
the per-cell lattice cannot see — the atom of every XOR constraint. -/
def Req : Set (Str Bool 2) := {t | t 0 = t 1}

/-- The string `(false, true)` — a *witness of asymmetry*: it is NOT in `Req`. -/
def offDiag : Str Bool 2 := ![false, true]

/-- `(false,true) ∉ R`: the relation is a **proper** subset of all strings.
Hence any abstraction sending `R` to `⊤` (which concretises to *all* strings) has
strictly over-approximated. -/
theorem offDiag_not_mem : offDiag ∉ Req := by
  simp only [Req, offDiag, Set.mem_setOf_eq]
  decide

/-- **`R ≠ univ`** — `R` genuinely constrains (it forbids `(false,true)`).  This
is what makes `α R = ⊤` a real *loss*, not a tautology. -/
theorem Req_ne_univ : Req ≠ (univ : Set (Str Bool 2)) := by
  intro h
  exact offDiag_not_mem (h ▸ mem_univ offDiag)

/-! ## 2.  The per-cell abstraction COLLAPSES the correlation: `α R = ⊤`.

This is the formal "the projection lattice loses the inter-cell correlation."
Each cell, projected on its own, sees *both* values (the relation is symmetric in
that weak, per-coordinate sense), so `α R i = univ` for every `i`. -/

/-- **The per-cell projection forgets `x = y`: `α R = ⊤`.**  Although `R` is a
proper subset of all strings (`Req_ne_univ`), its per-cell projection is the
all-candidates grid: cell `0` takes value `false` (in `(false,false)`) and `true`
(in `(true,true)`), and likewise cell `1`.  So the per-cell lattice's *best*
(tightest) abstraction of the correlated relation `R` is "anything goes."

This is `Tower9.ldt_lossy` / `α ∘ γ ≠ id` made fully concrete on the XOR atom:
the per-cell domain **cannot represent `x = y`**. -/
theorem alpha_eq_top : alpha Req = (⊤ : Abs Bool 2) := by
  funext i
  ext v
  simp only [Set.top_eq_univ, Pi.top_apply, Set.mem_univ, iff_true]
  rw [mem_alpha]
  -- exhibit a string in `R` (the constant string `fun _ => v`, which is diagonal)
  -- whose `i`-th coordinate is `v`.
  exact ⟨fun _ => v, rfl, rfl⟩

/-- **The collapse spelled out as `α (γ (α R)) = univ ⊋ R`.**  Re-abstracting the
concretisation of `α R` returns `univ` (all strings), which strictly contains the
proper relation `R`.  The per-cell round trip `γ ∘ α` does not recover `R`: it
inflates it to everything.  (Contrast the pair round trip `γₚ ∘ αₚ`, which is the
*identity* on `R` — §4.) -/
theorem cell_roundtrip_inflates :
    gamma (alpha Req) = (univ : Set (Str Bool 2)) ∧ Req ≠ gamma (alpha Req) := by
  refine ⟨?_, ?_⟩
  · rw [alpha_eq_top, gamma_top]
  · rw [alpha_eq_top, gamma_top]; exact Req_ne_univ

/-! ## 3.  Cell-level arc consistency is correspondingly stuck on `{x = y}`.

The collapse `α R = ⊤` is *why* `acStep` (generalized arc consistency on the
per-cell domain) makes no progress on the single equality constraint: every
value at every cell is locally supported by a satisfying (diagonal) string. -/

/-- The one-constraint equality family `{R}` on the per-cell domain. -/
def eqCs : Set (Set (Str Bool 2)) := {Req}

/-- **Arc consistency is stuck at `⊤` on the equality constraint**
(`acStep {R} ⊤ = ⊤`).  Each value at each cell is supported by the diagonal
string carrying it, so per-cell support removes nothing — the same blindness as
`alpha_eq_top`, now at the deduction-operator level.  (This is the 2-cell shadow
of the imported `acStep_xor_stuck`.) -/
theorem acStep_eq_stuck : acStep eqCs (⊤ : Abs Bool 2) = ⊤ := by
  funext i
  ext v
  simp only [acStep, eqCs, Req, Set.top_eq_univ, Pi.top_apply, Set.mem_setOf_eq,
    Set.mem_univ, true_and, iff_true, Set.mem_singleton_iff, forall_eq]
  -- support: the constant (diagonal) string `fun _ => v` lies in R, is ⊤-consistent,
  -- and carries `v` at cell `i`.
  exact ⟨fun _ => v, rfl, fun _ => trivial, rfl⟩

/-! ## 4.  The PAIR domain: candidate sets over *ordered pairs* of the two cells.

We refine the abstraction one rung: instead of two independent per-cell sets we
keep a single candidate set of *pairs* `(value at cell 0, value at cell 1)`.
This is the 2-consistency / path-consistency abstract domain.  It has its own
`γₚ`, `αₚ`, and — the structural point — a genuine **Galois connection**, exactly
like the per-cell one, so it is a bona-fide LDT-style abstract domain, only
*richer*. -/

/-- The **pair abstract domain**: a candidate set of ordered pairs
`(cell 0, cell 1)`.  Ordered by `⊆`; `⊤ₚ = univ` (all four pairs), `⊥ₚ = ∅`.
This is the path-consistency lattice over the two-cell window. -/
abbrev PairAbs : Type := Set (Bool × Bool)

/-- **Pair concretisation** `γₚ : PairAbs → ℘(Str)`: the strings whose
`(cell 0, cell 1)` pair is a live candidate.  Direct analogue of `γ`. -/
def gammaPair (P : PairAbs) : Set (Str Bool 2) := {s | (s 0, s 1) ∈ P}

/-- **Pair abstraction** `αₚ : ℘(Str) → PairAbs`: the set of `(cell 0, cell 1)`
pairs realised by some string.  `αₚ S = {(s 0, s 1) | s ∈ S}`.  Direct analogue
of `α`, but projecting onto the *pair* of cells rather than each cell alone. -/
def alphaPair (S : Set (Str Bool 2)) : PairAbs := (fun s => (s 0, s 1)) '' S

@[simp] theorem mem_gammaPair {P : PairAbs} {s : Str Bool 2} :
    s ∈ gammaPair P ↔ (s 0, s 1) ∈ P := Iff.rfl

@[simp] theorem mem_alphaPair {S : Set (Str Bool 2)} {p : Bool × Bool} :
    p ∈ alphaPair S ↔ ∃ s ∈ S, (s 0, s 1) = p := by
  simp only [alphaPair, Set.mem_image]

/-- **The pair Galois connection `αₚ ⊣ γₚ`.**  Exactly the over-approximation
adjunction of the per-cell case, one level up: `αₚ S ⊆ P ↔ S ⊆ γₚ P` (both say
"every string's cell-pair is a live candidate in `P`").  This certifies `PairAbs`
is a real abstract-interpretation domain, not an ad-hoc set. -/
theorem pair_gc : GaloisConnection alphaPair gammaPair := by
  intro S P
  constructor
  · -- αₚ S ⊆ P ⟹ S ⊆ γₚ P
    intro h s hs
    exact h ⟨s, hs, rfl⟩
  · -- S ⊆ γₚ P ⟹ αₚ S ⊆ P
    intro h p hp
    rw [mem_alphaPair] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    exact h hs

/-- Pair concretisation is monotone (upper adjoint). -/
theorem gammaPair_mono : Monotone gammaPair := pair_gc.monotone_u

/-- Pair abstraction is monotone (lower adjoint). -/
theorem alphaPair_mono : Monotone alphaPair := pair_gc.monotone_l

/-! ### The pair domain RETAINS `R` exactly — the heart of the hierarchy. -/

/-- **The pair abstraction is exact on `R`: `αₚ R = {(false,false),(true,true)}`.**
Where the per-cell projection collapsed `R` to `⊤` (`alpha_eq_top`), the pair
projection keeps precisely the two diagonal pairs.  The richer lattice *represents
`x = y`*. -/
theorem alphaPair_eq : alphaPair Req = {(false, false), (true, true)} := by
  ext p
  rw [mem_alphaPair]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    -- s 0 = s 1 (s ∈ R), so the pair is (b,b) for b = s 0.
    simp only [Req, Set.mem_setOf_eq] at hs
    rcases hb : s 0 with _ | _
    · exact Or.inl (by rw [Prod.ext_iff]; exact ⟨rfl, by rw [← hs]; exact hb⟩)
    · exact Or.inr (by rw [Prod.ext_iff]; exact ⟨rfl, by rw [← hs]; exact hb⟩)
  · rintro (rfl | rfl)
    · exact ⟨fun _ => false, rfl, rfl⟩
    · exact ⟨fun _ => true, rfl, rfl⟩

/-- **The pair abstraction of `R` is NOT `⊤ₚ`** — it omits the off-diagonal pairs
`(false,true)`, `(true,false)`.  So the pair lattice's tightest description of
`R` is a *proper* candidate set, capturing the constraint the per-cell lattice
threw away. -/
theorem alphaPair_ne_top : alphaPair Req ≠ (univ : PairAbs) := by
  rw [alphaPair_eq]
  intro h
  have : (false, true) ∈ ({(false, false), (true, true)} : PairAbs) :=
    h ▸ mem_univ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with h | h <;> exact absurd h (by decide)

/-- **The pair round trip recovers `R` exactly: `γₚ (αₚ R) = R`.**  On `R` the
pair abstraction is a Galois-*insertion* round trip (`γₚ ∘ αₚ = id` here),
precisely where the per-cell round trip is total collapse to `univ`
(`cell_roundtrip_inflates`).  This *equality* is the formal sense in which the
pair domain "sees" the correlation: re-concretising loses nothing. -/
theorem gammaPair_alphaPair_eq : gammaPair (alphaPair Req) = Req := by
  rw [alphaPair_eq]
  ext s
  simp only [mem_gammaPair, Set.mem_insert_iff, Set.mem_singleton_iff, Req,
    Set.mem_setOf_eq, Prod.ext_iff]
  constructor
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩) <;> rw [h0, h1]
  · intro h
    -- h : s 0 = s 1; substitute s 1 then split on s 0.
    rw [← h]
    rcases hb : s 0 with _ | _
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-! ## 5.  HEADLINE: the pair domain is strictly richer than the per-cell domain.

On the *same* relation `R`, the per-cell abstraction is `⊤` (blind: it cannot
distinguish `R` from `univ`) while the pair abstraction is `R` exactly. -/

/-- **The hierarchy is real: pair ⊋ cell, witnessed on the equality correlation.**

For the proper relation `R = {x = y}` (which is *not* `univ`, `Req_ne_univ`):

1. the **per-cell** abstraction collapses it to `⊤`, whose concretisation is all
   of `univ` — the per-cell lattice **cannot tell `R` from the universe**
   (`α R = ⊤`, `γ (α R) = univ`); while

2. the **pair** abstraction is `R` *exactly* — its concretisation is `R` back,
   losing nothing (`γₚ (αₚ R) = R`), and it is a *proper* candidate set
   (`αₚ R ≠ ⊤ₚ`).

So the pair domain represents an inter-cell correlation that the per-cell domain
provably collapses: **strictly more expressive.**  This is the "framework of
kinds" as an actual lattice hierarchy — the richer abstract domain (path
consistency / candidate sets over pairs) sees structure the coarser one (arc
consistency / per-cell sets) is blind to. -/
theorem pair_strictly_richer_than_cell :
    -- (1) per-cell collapses R to ⊤, and γ inflates it to the whole universe:
    (alpha Req = (⊤ : Abs Bool 2) ∧ gamma (alpha Req) = (univ : Set (Str Bool 2)))
    ∧ -- (2) the pair domain keeps R exactly (proper, and round-trips to R):
    (alphaPair Req ≠ (univ : PairAbs) ∧ gammaPair (alphaPair Req) = Req)
    ∧ -- (3) and R really is a proper relation, so (1) is a genuine loss:
    Req ≠ (univ : Set (Str Bool 2)) :=
  ⟨⟨alpha_eq_top, by rw [alpha_eq_top, gamma_top]⟩,
   ⟨alphaPair_ne_top, gammaPair_alphaPair_eq⟩,
   Req_ne_univ⟩

/-! ## 6.  The gap is operational: pair support narrows where cell support is stuck.

The expressiveness gap of §5 is not abstract bookkeeping — it is exactly why a
*pair-level* deduction step solves the equality constraint that the *cell-level*
`acStep` cannot touch.  We define the pair analogue of `acStep` and show it
narrows `⊤ₚ` to `R` in one step on `{x = y}`, while `acStep` stays at `⊤`. -/

/-- **Pair-level (2-consistency) support step** for a constraint family `Cs`:
keep a pair `p` iff every constraint `C ∈ Cs` has a satisfying string, consistent
with the current pair-domain `P`, realising `p`.  The path-consistency analogue
of `acStep`, on `PairAbs`. -/
def pairStep (Cs : Set (Set (Str Bool 2))) (P : PairAbs) : PairAbs :=
  {p | p ∈ P ∧ ∀ C ∈ Cs, ∃ t ∈ C, (t 0, t 1) ∈ P ∧ (t 0, t 1) = p}

/-- `pairStep` is **reductive** — it only removes pair-candidates. -/
theorem pairStep_reductive (Cs : Set (Set (Str Bool 2))) (P : PairAbs) :
    pairStep Cs P ⊆ P := fun _ hp => hp.1

/-- **`pairStep` is certificate-checked, hence sound** (the pair analogue of
`acStep_certified`): every pair it removes is genuinely placed by no solution
consistent with the current pair-state — so it never drops a real solution.
Proof: a solution `s` consistent with `P` supports its own pair `(s 0, s 1)` in
every constraint via the witness `t := s`. -/
theorem pairStep_certified (Cs : Set (Set (Str Bool 2))) (P : PairAbs)
    (s : Str Bool 2) (hs : s ∈ famCons Cs) (hsP : s ∈ gammaPair P) :
    s ∈ gammaPair (pairStep Cs P) := by
  show (s 0, s 1) ∈ pairStep Cs P
  exact ⟨hsP, fun C hC => ⟨s, hs C hC, hsP, rfl⟩⟩

/-- **The pair step SOLVES the equality constraint in one shot:
`pairStep {R} ⊤ₚ = R`'s pair set.**  Starting from all four pairs, pair-support
keeps exactly the two diagonal pairs `{(false,false),(true,true)}` — because the
off-diagonal pairs have *no* supporting string in `R`.  This is the narrowing the
per-cell `acStep` could not perform (`acStep_eq_stuck`): the pair domain enforces
`x = y`. -/
theorem pairStep_eq_solves :
    pairStep eqCs (univ : PairAbs) = {(false, false), (true, true)} := by
  ext p
  simp only [pairStep, eqCs, Req, Set.mem_setOf_eq, Set.mem_univ, true_and,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    -- t 0 = t 1, so (t 0, t 1) is diagonal.
    rcases hb : t 0 with _ | _
    · exact Or.inl (by rw [Prod.ext_iff]; exact ⟨rfl, by rw [← ht]; exact hb⟩)
    · exact Or.inr (by rw [Prod.ext_iff]; exact ⟨rfl, by rw [← ht]; exact hb⟩)
  · rintro (rfl | rfl)
    · exact ⟨fun _ => false, rfl, rfl⟩
    · exact ⟨fun _ => true, rfl, rfl⟩

/-- **The operational hierarchy gap (companion headline).**  On the equality
constraint `{x = y}`:

* the **per-cell** arc-consistency step is *stuck at `⊤`* — it removes nothing
  (`acStep eqCs ⊤ = ⊤`); while
* the **pair** support step *narrows `⊤ₚ` to a proper candidate set* — exactly the
  two diagonal pairs `{(false,false),(true,true)} ≠ univ`
  (`pairStep eqCs ⊤ₚ = R`-pairs).

Same constraint, two abstract domains: the richer (pair / path-consistency)
domain makes the deduction the coarser (per-cell / arc-consistency) domain
provably cannot.  This is the operational face of `pair_strictly_richer_than_cell`
— and the concrete reason path consistency cracks XOR atoms that arc consistency
leaves untouched.  (`pairStep` is sound: `pairStep_reductive`,
`pairStep_certified`.) -/
theorem pair_narrows_where_cell_stuck :
    -- per-cell arc consistency: no progress, stuck at ⊤
    (acStep eqCs (⊤ : Abs Bool 2) = ⊤)
    ∧ -- pair support: narrows to the two diagonal pairs, a PROPER candidate set
    (pairStep eqCs (univ : PairAbs) = {(false, false), (true, true)})
    ∧ (pairStep eqCs (univ : PairAbs) ≠ (univ : PairAbs)) :=
  ⟨acStep_eq_stuck, pairStep_eq_solves, by
    rw [pairStep_eq_solves]; exact alphaPair_eq ▸ alphaPair_ne_top⟩

/-! ## 7.  End-of-file inventory.

**PROVED (real defs, non-vacuous, axiom-clean):**

  * §1 — `Req` (= `{x = y}` on 2 cells), `offDiag`, `offDiag_not_mem`,
    **`Req_ne_univ`** (the relation is a *proper* subset — so the collapse below
    is a genuine loss).
  * §2 — **`alpha_eq_top`** (`α R = ⊤`): the per-cell projection forgets `x = y`;
    `cell_roundtrip_inflates` (`γ (α R) = univ ⊋ R`).
  * §3 — `eqCs`, **`acStep_eq_stuck`** (`acStep {R} ⊤ = ⊤`): arc consistency
    inherits the blindness — no progress on the equality constraint.
  * §4 — the **pair domain** `PairAbs` with `gammaPair`, `alphaPair`, membership
    simp-lemmas, and **`pair_gc : GaloisConnection αₚ γₚ`** (a real abstract
    domain, one rung richer), monotonicity of both adjoints; **`alphaPair_eq`**
    (`αₚ R = {(ff,ff),(tt,tt)}`), **`alphaPair_ne_top`**, and
    **`gammaPair_alphaPair_eq`** (`γₚ (αₚ R) = R`: the pair round trip is exact
    where the cell round trip collapses).
  * §5 — **`pair_strictly_richer_than_cell`**: the headline strict-expressiveness
    gap on `R` (cell = `⊤`/blind, pair = `R`/exact).
  * §6 — `pairStep` (pair / path-consistency support step) with
    `pairStep_reductive`, **`pairStep_certified`** (sound), **`pairStep_eq_solves`**
    (`pairStep {R} ⊤ₚ = R`-pairs), and the companion headline
    **`pair_narrows_where_cell_stuck`** (pair narrows where `acStep` is stuck).

**HONEST RESIDUAL / scope:**
  * We prove the strict *kind gap* on the equality atom and the matching
    *one-constraint* narrowing contrast.  We deliberately do **NOT** claim
    "pair-AC solves the full 3-cell XOR system": that needs path consistency over
    *all* pair-windows with a join/propagation loop (the next file).  The proven
    statement is the rung-1 expressiveness separation between the per-cell and
    pair lattices — which is the formal content of "the framework of kinds is a
    real hierarchy," and the concrete mechanism by which the imported
    `acStep_xor_stuck` blindness is overcome one level up.
  * `pairStep` is shown reductive + certificate-sound (so its narrowing is a
    legitimate sound deduction), but we do not here re-bundle it into the Tower-8
    `SoundStep`/run-soundness machinery (that is the per-cell `Abs` interface; the
    pair domain would need its own `dedRun`, again deferred).  The point made here
    is the *expressiveness* separation, which is domain-intrinsic.
-/

end LatticeDeduction
end Integrations
end Graphplay
