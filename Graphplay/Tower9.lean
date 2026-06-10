/-
# Graphplay.Tower9 — Abstract interpretation: refinement ⊣ deduction as one
verified Knaster–Tarski / Cousot interface.

**What this file makes first-class.** graphplay's WL/equitable-partition
*refinement* (Tower-8: = coarsest bisimulation = 1-WL) and the Lattice Deduction
Transformer's *deduction* (`Integrations.LatticeDeduction`) are the **two
order-dual halves of one abstract-interpretation story** (Cousot–Cousot, POPL
1977). This module builds the interface that contains both and proves the
**Cousot fixpoint-transfer theorem** over it, then exhibits the two legs as
instances — encoding, as a machine-checked statement, the *distinction* the
prose insists on:

* the **deduction leg** (LDT) is a Galois **connection** that is **not** an
  insertion — `α ∘ γ ≠ id`, a *lossy over-approximation* (inter-cell
  correlation is forgotten; the paper's Fig. 5);
* the **refinement leg** (partitions) is a Galois **insertion** —
  `α ∘ γ = id`, an *exact* closure (Mathlib's `Setoid.gi`: a relation's
  equivalence-closure, coerced back, is itself).

This is the content of "refinement ⊣ deduction": **same interface,
opposite species** (exact insertion vs lossy connection), the order-dual of one
another. The `cellInflate ⊣ cells` "adjunction" floated in early notes is **not**
a Galois connection (it is a linear matrix lift, a category error) and is
deliberately absent here; the equivalence-closure insertion (`Setoid.gi`) is the
real partition-world adjunction, in the spirit of Ranzato–Tapparo (2008),
"Generalizing the Paige–Tarjan algorithm by abstract interpretation".

**Proved:**
* `AbstractInterpretation` — the structure (two complete lattices + a Galois
  connection).
* `lfp_transfer`, `gfp_transfer` — the Cousot fixpoint-transfer theorems
  (the abstract fixpoint soundly over-approximates or under-approximates the
  concrete one).
* `ldtAbstraction` — the LDT deduction leg as an instance, and
  `ldt_deduction_run_sound` — LDT's run-soundness (`cons ⊆ γ(gfp dedₚ)`)
  re-derived as a **corollary of `gfp_transfer`** (the unification cashes out:
  LDT soundness IS Cousot fixpoint transfer).
* `partitionAbstraction` — the partition/equivalence leg as an instance (from
  Mathlib `Setoid.gi`).
* `ldt_lossy` (lossy: `∃ a, α(γ a) ≠ a`) vs `partition_is_insertion`
  (exact: `∀ s, α(γ s) = s`) — the species distinction, machine-checked.

**Scope.** This delivers the interface + transfer + both
instances + the exact/lossy contrast.
What it does **not** yet do: re-express graphplay's *specific* WL refinement
operator `wlStep` as an `OrderHom` on `Setoid V` whose `gfp` is *literally*
`wlRefine_coarsestEquitable`. `wlStep` changes its colour
*type* each round (`α → α × Multiset α`), so that is a parallel fixed-carrier
construction, not a repackaging; it is the documented next step.  §3 below
instead instantiates the partition leg through Mathlib's equivalence-closure
insertion `Setoid.gi` — enough to exhibit the refinement side as an
`AbstractInterpretation` of the *exact / insertion* species, but it does **not**
yet identify graphplay's `wlStep` gfp with `wlRefine_coarsestEquitable`.  No
iterated CEGAR loop and no k-WL=k-consistency=Sherali–Adams equivalence are
claimed (aspirational).

No quantum deduction-dual is claimed: the duality is **classical**; only the
refinement leg carries the quantum-walk lift (the equitable quotient, exact and
spectrum-preserving). That asymmetry is the correct statement, not a symmetric
"quantum deduction".

References: Tarski 1955; Cousot–Cousot POPL'77/'79; Ranzato–Tapparo, Inf. Comput.
206 (2008); D'Silva–Haller–Kroening POPL 2013; LDT arXiv:2605.08605.
-/

import Graphplay.Integrations.LatticeDeduction
import Mathlib.Order.FixedPoints
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Setoid.Basic

namespace Graphplay
namespace Tower9

open OrderHom

/-! ## 1.  The abstract-interpretation interface.

A Cousot abstract interpretation is, at its core, a **Galois connection**
`α ⊣ γ` between a *concrete* complete lattice `C` and an *abstract* one `A`:
`α` (the lower adjoint) over-approximates a concrete object by an abstract one,
`γ` (the upper adjoint) concretises. -/

/-- An **abstract interpretation**: a Galois connection `α ⊣ γ` between two
complete lattices.  `α` is the lower adjoint (abstraction), `γ` the upper
(concretisation).  This is the single interface that both graphplay's partition
refinement and the LDT deduction instantiate. -/
structure AbstractInterpretation (C A : Type*) [CompleteLattice C]
    [CompleteLattice A] where
  /-- Abstraction (lower adjoint): over-approximate a concrete object. -/
  abst : C → A
  /-- Concretisation (upper adjoint): the largest concrete object an abstract
  one denotes. -/
  conc : A → C
  /-- The Galois connection `abst ⊣ conc`. -/
  gc : GaloisConnection abst conc

namespace AbstractInterpretation

variable {C A : Type*} [CompleteLattice C] [CompleteLattice A]

/-- `γ` is monotone (upper adjoints are). -/
theorem conc_mono (ai : AbstractInterpretation C A) : Monotone ai.conc :=
  ai.gc.monotone_u

/-- `α` is monotone (lower adjoints are). -/
theorem abst_mono (ai : AbstractInterpretation C A) : Monotone ai.abst :=
  ai.gc.monotone_l

/-- The **unit / soundness** law: `c ≤ γ(α c)` (abstraction over-approximates). -/
theorem le_conc_abst (ai : AbstractInterpretation C A) (c : C) :
    c ≤ ai.conc (ai.abst c) := ai.gc.le_u_l c

/-- The **counit** law: `α(γ a) ≤ a` (re-abstraction is reductive). -/
theorem abst_conc_le (ai : AbstractInterpretation C A) (a : A) :
    ai.abst (ai.conc a) ≤ a := ai.gc.l_u_le a

/-! ### Cousot fixpoint transfer — the abstract fixpoint approximates the
concrete one.  This is the theorem that makes "analyse the small abstract
object instead of the big concrete one" *sound*. -/

/-- **Least-fixpoint transfer** (Cousot–Cousot 1977).  If the abstract transformer
`g` is sound relative to the concrete `f` *in the `f ∘ γ ≤ γ ∘ g` form*, then the
abstract least fixpoint **over-approximates** the abstracted concrete one:
`α (lfp f) ≤ lfp g`.

Proof: by the adjunction, `α (lfp f) ≤ lfp g ↔ lfp f ≤ γ (lfp g)`; the latter is
`lfp_le` applied to the pre-fixpoint witness `f (γ (lfp g)) ≤ γ (g (lfp g)) =
γ (lfp g)` (soundness then `map_lfp`).  No join-preservation needed. -/
theorem lfp_transfer (ai : AbstractInterpretation C A)
    (f : C →o C) (g : A →o A)
    (hsound : ∀ a : A, f (ai.conc a) ≤ ai.conc (g a)) :
    ai.abst (OrderHom.lfp f) ≤ OrderHom.lfp g := by
  rw [ai.gc.le_iff_le]
  apply OrderHom.lfp_le
  calc f (ai.conc (OrderHom.lfp g)) ≤ ai.conc (g (OrderHom.lfp g)) := hsound _
    _ = ai.conc (OrderHom.lfp g) := by rw [OrderHom.map_lfp]

/-- **Greatest-fixpoint transfer** (the order-dual; the form the *deduction* leg
uses — gfp Kleene descent from `⊤`).  If `g` is sound in the `α ∘ f ≤ g ∘ α`
form, the concrete greatest fixpoint is **under-approximated** by the abstract
one through `γ`: `gfp f ≤ γ (gfp g)`.

Proof: by the adjunction, `gfp f ≤ γ (gfp g) ↔ α (gfp f) ≤ gfp g`; the latter is
`le_gfp` applied to the post-fixpoint witness `α (gfp f) = α (f (gfp f)) ≤
g (α (gfp f))` (`map_gfp` then soundness). -/
theorem gfp_transfer (ai : AbstractInterpretation C A)
    (f : C →o C) (g : A →o A)
    (hsound : ∀ c : C, ai.abst (f c) ≤ g (ai.abst c)) :
    OrderHom.gfp f ≤ ai.conc (OrderHom.gfp g) := by
  rw [← ai.gc.le_iff_le]
  apply OrderHom.le_gfp
  calc ai.abst (OrderHom.gfp f) = ai.abst (f (OrderHom.gfp f)) := by
        rw [OrderHom.map_gfp]
    _ ≤ g (ai.abst (OrderHom.gfp f)) := hsound _

end AbstractInterpretation

/-! ## 2.  Instance — the deduction leg (LDT): a lossy Galois *connection*.

The Lattice Deduction Transformer's `α ⊣ γ` (per-cell projection ⊣ cylinder),
already proven `Integrations.LatticeDeduction.alpha_gc_gamma`, is an abstract
interpretation.  Its *over-approximation* is lossy — `α ∘ γ ≠ id` — so
it is a connection, **not** an insertion.  We then re-derive LDT's run-soundness
as a corollary of `gfp_transfer`. -/

open Graphplay.Integrations.LatticeDeduction

variable {V : Type} {k : ℕ}

/-- The **LDT deduction leg** as an abstract interpretation: the grid-powerset
over-approximation `℘(Str) ⇄ Abs`. -/
def ldtAbstraction : AbstractInterpretation (Set (Str V k)) (Abs V k) where
  abst := alpha
  conc := gamma
  gc := alpha_gc_gamma

/-- The concrete deduction transformer: intersect the candidate string-set with
the constraints `cons`.  Its `gfp` from `⊤ = univ` is exactly `cons` (the
solution set). -/
def consMeet (cons : Set (Str V k)) : Set (Str V k) →o Set (Str V k) where
  toFun S := S ∩ cons
  monotone' _ _ h := Set.inter_subset_inter_left cons h

/-- The abstract deduction transformer `dedₚ` as an `OrderHom` (monotone by
`dedP_mono`). -/
def dedPHom (cons : Set (Str V k)) : Abs V k →o Abs V k where
  toFun := dedP cons
  monotone' := dedP_mono cons

/-- `gfp (consMeet cons) = cons`: descending `S ↦ S ∩ cons` from `⊤` lands on the
solution set. -/
theorem gfp_consMeet (cons : Set (Str V k)) :
    OrderHom.gfp (consMeet cons) = cons := by
  apply le_antisymm
  · -- gfp ≤ cons : gfp = (gfp ∩ cons) ⊆ cons
    have h := OrderHom.map_gfp (consMeet cons)
    calc OrderHom.gfp (consMeet cons)
        = (consMeet cons) (OrderHom.gfp (consMeet cons)) := h.symm
      _ = OrderHom.gfp (consMeet cons) ∩ cons := rfl
      _ ⊆ cons := Set.inter_subset_right
  · -- cons ≤ gfp : cons is a post-fixpoint (cons ⊆ cons ∩ cons)
    apply OrderHom.le_gfp
    show cons ⊆ cons ∩ cons
    exact Set.subset_inter (le_refl cons) (le_refl cons)

/-- **LDT run-soundness as Cousot fixpoint transfer.**  The deduction closure
(greatest fixpoint of `dedₚ`, the result of gfp Kleene descent from `⊤`) still
admits every true solution: `cons ⊆ γ (gfp dedₚ)`.  This is the run-soundness
that `Integrations.LatticeDeduction.dedRun_preserves_solutions` proves via the
coalgebraic invariant — here it falls out of the *general* `gfp_transfer`,
witnessing that the two legs really do share one interface. -/
theorem ldt_deduction_run_sound (cons : Set (Str V k)) :
    cons ⊆ gamma (OrderHom.gfp (dedPHom cons)) := by
  have key := (ldtAbstraction (V := V) (k := k)).gfp_transfer
    (consMeet cons) (dedPHom cons) ?_
  · -- key : gfp (consMeet cons) ≤ γ (gfp (dedPHom cons));  rewrite gfp = cons
    rwa [gfp_consMeet] at key
  · -- soundness:  α (S ∩ cons) ≤ dedₚ (α S)
    intro S
    show alpha (S ∩ cons) ≤ dedP cons (alpha S)
    -- dedP cons (α S) = α (γ (α S) ∩ cons);  S ⊆ γ(α S) ⟹ S∩cons ⊆ γ(αS)∩cons
    refine alpha_mono ?_
    exact Set.inter_subset_inter_left cons (subset_gamma_alpha S)

/-! ## 2′.  The deduction leg is lossy — a *connection*, not an insertion. -/

/-- **The deduction leg is lossy** (`α ∘ γ ≠ id`): with at least two cells and a
nonempty vocabulary, an abstract state with one empty and one full cell has
`α (γ a) = ⊥ ≠ a`.  Hence LDT's `α ⊣ γ` is a Galois *connection*, **not** an
insertion — a lossy over-approximation. -/
theorem ldt_lossy [Nonempty V] (h2 : 2 ≤ k) :
    ∃ a : Abs V k, alpha (gamma a) ≠ a := by
  classical
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  -- cell 0 empty, all others full; cell 1 is full and 1 ≠ 0.
  refine ⟨fun i => if i = ⟨0, h0⟩ then (∅ : Set V) else Set.univ, ?_⟩
  -- γ a = ∅ because cell 0 is empty.
  have hgamma : gamma (fun i => if i = ⟨0, h0⟩ then (∅ : Set V) else Set.univ)
      = (∅ : Set (Str V k)) := by
    ext s
    simp only [mem_gamma, Set.mem_empty_iff_false, iff_false, not_forall]
    exact ⟨⟨0, h0⟩, by simp⟩
  intro hcontra
  rw [hgamma] at hcontra
  -- Evaluate the function equality at cell ⟨1,h1⟩ ≠ ⟨0,h0⟩: LHS `α ∅ = ∅`,
  -- RHS = `univ`; so `∅ = univ`, contradiction (V nonempty).
  have e1 := congrFun hcontra ⟨1, h1⟩
  rw [if_neg (by simp [Fin.ext_iff])] at e1
  simp only [alpha, Set.image_empty] at e1
  exact Set.empty_ne_univ e1

/-! ## 3.  Instance — the refinement leg (partitions): an exact Galois
*insertion*.

The partition world carries a genuine Galois insertion off the shelf: Mathlib's
`Setoid.gi`, the **equivalence-closure** abstraction
`EqvGen.setoid ⊣ (⇑·)` between binary relations `W → W → Prop` (concrete) and
equivalence relations `Setoid W` (abstract).  Unlike LDT this is an *insertion*:
`α ∘ γ = id` (closing an equivalence's own relation returns it) — the **exact**
species.  This is the partition-world adjunction in the spirit of
Ranzato–Tapparo; it is the order-dual *kind* of the LDT connection. -/

variable {W : Type*}

open Relation

/-- The **refinement / partition leg** as an abstract interpretation: the
equivalence-closure Galois insertion between binary relations and equivalence
relations on `W`. -/
def partitionAbstraction : AbstractInterpretation (W → W → Prop) (Setoid W) where
  abst := EqvGen.setoid
  conc := fun s => ⇑s
  gc := Setoid.gi.gc

/-- **The refinement leg is exact: `α ∘ γ = id`, a Galois insertion.**  Closing
an equivalence relation's own relation returns the equivalence — no information
is lost.  This is the *exact-reduction* species, the order-dual of LDT's lossy
over-approximation (`ldt_lossy`). -/
theorem partition_is_insertion (s : Setoid W) :
    (partitionAbstraction (W := W)).abst ((partitionAbstraction (W := W)).conc s)
      = s :=
  Setoid.gi.l_u_eq s

/-! ## 4.  The duality, machine-stated: same interface, opposite species.

`ldtAbstraction` and `partitionAbstraction` are both `AbstractInterpretation`s
(the unification), but of **opposite species**: the deduction leg is a lossy
*connection* (`ldt_lossy`: `α∘γ ≠ id`) and the refinement leg is an exact
*insertion* (`partition_is_insertion`: `α∘γ = id`).  This is the precise,
non-inflated formal content of "refinement ⊣ deduction": one Cousot interface,
two order-dual legs — refinement *distinguishes states* (exact symmetry
reduction), deduction *eliminates values* (lossy candidate narrowing). -/

/-- **The refinement⊣deduction duality, as one statement.**  Both legs are
abstract interpretations; the refinement leg is an *exact* insertion
(`α∘γ = id`) while the deduction leg is a *lossy* connection (`α∘γ ≠ id`).  The
shared `gfp_transfer` makes the deduction leg's run-soundness a transfer
corollary (`ldt_deduction_run_sound`); the refinement leg carries the (classical)
quantum-walk lift, the deduction leg does not — the duality is classical, the
quotient leg is where the quantum content lives. -/
theorem refinement_deduction_duality [Nonempty V] (h2 : 2 ≤ k) :
    -- refinement leg: exact insertion
    (∀ s : Setoid W, (partitionAbstraction (W := W)).abst
        ((partitionAbstraction (W := W)).conc s) = s)
    ∧ -- deduction leg: lossy connection (NOT an insertion)
    (∃ a : Abs V k, (ldtAbstraction (V := V) (k := k)).abst
        ((ldtAbstraction (V := V) (k := k)).conc a) ≠ a) :=
  ⟨partition_is_insertion, ldt_lossy h2⟩

end Tower9
end Graphplay
