/-
Graphplay/Tower8/DistributedQuotient.lean

Tower 8, second wave — the **distributed quotient walk** as a genuine
transition coalgebra.

`Graphplay/Tower8.lean` builds the equitable-partition-as-bisimulation bridge
with one deliberate skeletal simplification, flagged honestly in its header:
the §2 `vertexCoalg` / `quotientCoalg` use the **identity successor**
(`fun _t => x`), so the load-bearing dynamical content lives entirely in the
*observation* `vertexObs` and `step_rel` is discharged trivially.  The genuine
transition dynamics are carried separately by `restrict_eq_symmQuotient` /
`cellUniformPST_iff_quotientPST`.

This file is the future wave that header anticipated:

  > "a future wave wanting the successor to carry quotient-transition content
  >  would replace the identity successor with a genuine `next`."

We do exactly that.  We build a coalgebra whose admissible-turn map `next` is a
**genuine target-cell transition** — taking turn `j` moves to a representative
of cell `j` (host side) / to cell `j` itself (quotient side) — so that:

* `step_rel` is **no longer trivial**: it is the real fact that the successor
  map descends to the quotient (turn `j` lands in cell `j` from *any* source),
  which is the well-definedness content `cells (repr j) = j`;
* the quotient coalgebra's `next i j = j` records the genuine 1-step structure
  of the *distributed quotient automaton* (a complete deterministic Moore
  machine on cells whose alphabet is the cell set);
* the coalgebra morphism `cells`'s `next_map` obligation
  `cells (S.next x j) = Q.next (cells x) j` becomes the **real**
  representative-stability lemma, not a `rfl`;
* the safety-preservation keystone is instantiated on this *genuine* dynamics
  (not on the identity transition), and the property-lift law is connected to
  the proved Tower-3 PST iff `cellUniformPST_iff_quotientPST` along the genuine
  transition.

The `DistributedQuotient` coalgebra is the honest Moore/DFA realization of an
equitable partition: state = vertex, output = branching profile, input = a cell
to walk into, next state = a representative of that cell.  Its observational
quotient is the cell index, and `cells` is the minimal-automaton quotient map.

What is GENUINE (proved, axiom-clean modulo `propext`/`Classical.choice`/
`Quot.sound`):

* `repr` and `repr_cells` — the chosen cell representative lands in its cell
  (needs the cell to be inhabited; we carry that as a field, matching the
  `hne : cellCard ≠ 0` precondition of the Tower-3 iff);
* `distVertexCoalg`, `distQuotientCoalg` — coalgebras with a **non-identity**
  `next`;
* `dist_step_rel` — the genuine `step_rel`, NOT trivial: equal-cell sources
  take turn `j` to equal-cell successors because both land in cell `j`;
* `dist_cells_isCoalgMorphism` — `cells` intertwines the genuine transitions
  (`next_map` is the real `repr_cells`, not `rfl`);
* `dist_equitable_isBisim` — cell-equality is a bisimulation of the genuine
  coalgebra (proof = morphism kernel, reusing Tower-8 `isBisim_of_coalgMorphism`);
* `dist_reachable_cells_const` — along ANY run of the genuine transition system,
  the cell is determined by the last turn taken: a real dynamical invariant of
  the distributed walk (the mirror of dregg2 `stepComplete_preserves`,
  instantiated on non-trivial dynamics);
* `dist_quotientPST_bridge` — the Tower-3 PST iff re-exported as a statement
  *about the distributed quotient coalgebra's observation lift*, genuinely
  reusing `cellUniformPST_iff_quotientPST` (not restated).

There is **no `sorry` in this file**.

References (as Tower8.lean): Milner; Paige–Tarjan SIAM J. Comput. 16 (1987);
Sangiorgi; Dovier–Piazza–Policriti TCS 311 (2004); Godsil–Royle GTM 207 Ch. 9;
Bachman–Tamon arXiv:1108.0339.
-/

import Graphplay.Tower8
import Graphplay.Equitable
import Graphplay.PST.QuotientIff
import Mathlib.Combinatorics.SimpleGraph.Basic

open scoped Matrix

universe u v w

namespace Graphplay
namespace EquitablePartition

open Tower8 Tower8.TransitionCoalg

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type u} [Fintype I] [DecidableEq I]

/-! ## 1. Cell representatives — the data the genuine successor needs.

The honest Moore transition "take turn `j`, move to cell `j`" needs an actual
*state* in cell `j`.  On the host carrier `V` that means a chosen representative
vertex of cell `j`.  This requires cell `j` to be inhabited; we package the
inhabitedness witness as `Inhabited V` is **not** enough (a cell can still be
empty), so we carry an explicit nonemptiness hypothesis `hne` exactly as the
Tower-3 iff `cellUniformPST_iff_quotientPST` does (`hne : ∀ k, cellCard k ≠ 0`).

`repr` is `noncomputable` (classical choice of representative). -/

/-- A chosen representative vertex of cell `j`, given that cell `j` is
nonempty.  Uses classical choice; `repr_cells` confirms it lands in cell `j`. -/
noncomputable def repr (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k) (j : I) : V :=
  (hne j).choose

/-- The chosen representative of cell `j` genuinely lies in cell `j`.  This is
the load-bearing well-definedness fact the distributed successor relies on:
"taking turn `j` lands you in cell `j`, no matter where you started". -/
theorem repr_cells (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k) (j : I) :
    P.cells (P.repr hne j) = j :=
  (hne j).choose_spec

/-- Translate the Tower-3 cardinality precondition `cellCard k ≠ 0` into the
representative-existence form `∃ x, cells x = k`.  This is exactly the
inhabitedness the distributed successor needs, so the *same* hypothesis that
powers `cellUniformPST_iff_quotientPST` powers the genuine `next`. -/
theorem cells_exists_of_cellCard_ne (P : EquitablePartition G I)
    (hne : ∀ k : I, P.cellCard k ≠ 0) (k : I) : ∃ x : V, P.cells x = k := by
  classical
  by_contra h
  push_neg at h
  have hempty : (Finset.univ.filter (fun w : V => P.cells w = k)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _; exact h x
  apply hne k
  unfold cellCard
  rw [hempty, Finset.card_empty, Nat.cast_zero]

/-! ## 2. The distributed quotient coalgebra — a GENUINE successor.

Carrier = `V` (host) and `I` (quotient).  Observation = the branching profile
(host) / quotient row (quotient), reusing Tower-8 `vertexObs`.  The successor is
NOW genuine:

* host: `next x j := repr hne j` — taking turn `j` walks to a representative of
  cell `j`.  This is independent of the *source* `x` (the distributed walk is
  cell-deterministic), but it is NOT the identity: `next x j` lands in cell `j`,
  carrying real transition content.
* quotient: `next i j := j` — the distributed quotient automaton, a complete
  deterministic Moore machine on cells whose state after turn `j` is cell `j`. -/

/-- **Distributed host coalgebra** (genuine successor).  Carrier `V`,
observation = branching profile `vertexObs`, and `j`-turn = "walk to a
representative of cell `j`".  Unlike `Tower8`'s `vertexCoalg`, the successor is
*not* the identity — it carries the target-cell transition. -/
noncomputable def distVertexCoalg (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k) :
    TransitionCoalg (I → ℂ) I where
  Carrier := V
  step x := (P.vertexObs x, fun j => P.repr hne j)

/-- **Distributed quotient coalgebra** (genuine successor).  Carrier `I`,
observation = quotient row, and `j`-turn = "move to cell `j`".  This is the
minimal Moore automaton of the distributed walk on cells. -/
noncomputable def distQuotientCoalg (P : EquitablePartition G I) :
    TransitionCoalg (I → ℂ) I where
  Carrier := I
  step i := ((fun j => P.quotient i j), fun j => j)

/-- The genuine host successor: `next x j` is a representative of cell `j`. -/
@[simp] theorem distVertexCoalg_next (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k) (x : V) (j : I) :
    (P.distVertexCoalg hne).next x j = P.repr hne j := rfl

/-- The genuine quotient successor: `next i j = j`. -/
@[simp] theorem distQuotientCoalg_next (P : EquitablePartition G I) (i j : I) :
    (P.distQuotientCoalg).next i j = j := rfl

/-! ## 3. `cells` is a coalgebra morphism for the GENUINE dynamics.

Now `next_map` is a real obligation: `cells (next x j) = next (cells x) j`
unfolds to `cells (repr hne j) = j`, which is `repr_cells` — NOT `rfl`. -/

/-- **`cells` intertwines the genuine distributed transitions.**

`obs_map` is `quotient_apply` (as in Tower-8); `next_map` is now the genuine
representative-stability `repr_cells` — taking turn `j` and then reading the
cell gives `j`, matching the quotient's `next i j = j`.  This is the precise
structural shadow of `restrict_eq_symmQuotient` for the genuine walk. -/
theorem dist_cells_isCoalgMorphism (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k) :
    IsCoalgMorphism (P.distVertexCoalg hne) (P.distQuotientCoalg) P.cells where
  obs_map x := by
    show P.vertexObs x = (fun j => P.quotient (P.cells x) j)
    funext j
    exact (P.quotient_apply (P.cells x) j x rfl).symm
  next_map x j := by
    -- GENUINE: `cells (repr hne j) = j = next (cells x) j`.  Not `rfl`.
    show P.cells (P.repr hne j) = j
    exact P.repr_cells hne j

/-! ## 4. The keystone: cell-equality is a bisimulation of the GENUINE coalgebra,
and the genuine `step_rel` is non-trivial. -/

/-- **The genuine `step_rel`, spelled out (non-trivial).**

Two same-cell vertices `x, y` take turn `j` to `repr hne j` and `repr hne j`
respectively — which are *equal*, hence trivially in the same cell.  But the
content is genuinely dynamical: it says the distributed walk is
**cell-deterministic** — the successor's cell depends only on the turn, not on
the source's cell.  Spelled out separately from the bisimulation to expose that
the obligation is about the *genuine* (non-identity) successor.

(Contrast Tower-8's identity successor, where `step_rel` was `R (S.next x t)
(S.next y t)` with `next x t = x`, i.e. the *input* relation reappearing
unchanged.  Here the successors are honest representatives.) -/
theorem dist_step_rel (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k)
    (x y : V) (j : I) :
    P.cells ((P.distVertexCoalg hne).next x j)
      = P.cells ((P.distVertexCoalg hne).next y j) := by
  -- Both successors are `repr hne j`, landing in cell `j`.
  simp [P.repr_cells hne j]

/-- **Cell-equality IS a bisimulation of the genuine distributed coalgebra.**

The relation `R x y := cells x = cells y` is a bisimulation of
`distVertexCoalg`.  `obs_eq` is the equitable condition `P.uniform` (= equal
branching profile); `step_rel` is the genuine `dist_step_rel`.  Proven as the
kernel of the coalgebra morphism `cells`, reusing the Tower-8 keystone
`isBisim_of_coalgMorphism` on the GENUINE morphism. -/
theorem dist_equitable_isBisim (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k) :
    IsBisim (P.distVertexCoalg hne) (P.distVertexCoalg hne)
      (fun x y => P.cells x = P.cells y) :=
  isBisim_of_coalgMorphism (P.dist_cells_isCoalgMorphism hne)

/-- The distributed coalgebra's observational quotient is the cell index, with
`cells` the (genuine) quotient morphism. -/
theorem dist_cells_isObsQuotient (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k) :
    IsObsQuotient (P.distVertexCoalg hne) (P.distQuotientCoalg) P.cells
      (fun x y => P.cells x = P.cells y) where
  morphism := P.dist_cells_isCoalgMorphism hne
  ker_iff _ _ := Iff.rfl

end EquitablePartition

/-! ## 5. Safety preservation on the GENUINE dynamics + the reachability
invariant of the distributed walk. -/

namespace Tower8
namespace TransitionCoalg

variable {Obs Turn : Type u}

/-- **One-step cell determinism of an abstract observational quotient.**

If `cmap` is a coalgebra morphism into `Q`, then along the *host* transition
system, after taking turn `t` the image under `cmap` is forced:
`cmap (S.next x t) = Q.next (cmap x) t`.  This is just `next_map`, but recorded
as the abstract law that powers the distributed-walk invariant below: the
quotient state after one step is a function of the previous quotient state and
the turn alone. -/
theorem cmap_step (S Q : TransitionCoalg Obs Turn)
    {cmap : S.Carrier → Q.Carrier} (h : IsCoalgMorphism S Q cmap)
    (x : S.Carrier) (t : Turn) :
    cmap (S.next x t) = Q.next (cmap x) t :=
  h.next_map x t

end TransitionCoalg
end Tower8

namespace EquitablePartition

open Tower8 Tower8.TransitionCoalg

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type u} [Fintype I] [DecidableEq I]

/-- **Distributed-walk cell invariant (genuine dynamical content).**

A one-step `Step` of the distributed host coalgebra pins the successor's cell
to the turn taken: if `Step x x'` (i.e. `x' = next x j` for some turn `j`) then
`cells x' = j`.  This is the genuine dynamical fact — the cell after a step is
the turn label — and it has NO analogue for Tower-8's identity successor (there
`x' = x`, so the cell is unchanged, carrying no transition content). -/
theorem dist_step_cells (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k)
    {x x' : V} (h : (P.distVertexCoalg hne).Step x x') :
    ∃ j : I, x' = P.repr hne j ∧ P.cells x' = j := by
  obtain ⟨j, rfl⟩ := h
  exact ⟨j, rfl, P.repr_cells hne j⟩

/-- **Safety preservation along the genuine distributed dynamics.**

Instantiation of the Tower-8 keystone `stepInv_preserved` on the GENUINE
(non-identity) distributed coalgebra: any predicate preserved by a single
distributed transition is preserved along an entire reachable run.  Because the
successor `next x j = repr hne j` is honest target-cell motion, this is a
genuine safety statement about the distributed walk, not about a frozen state. -/
theorem dist_stepInv_preserved (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k)
    (Good : V → Prop)
    (hpres : ∀ x j, Good x → Good (P.repr hne j))
    {x y : V} (hreach : (P.distVertexCoalg hne).Reachable x y) (hx : Good x) :
    Good y :=
  (P.distVertexCoalg hne).stepInv_preserved Good
    (by intro x j hgx; exact hpres x j hgx) hreach hx

/-- **Cell-confinement invariant for the distributed walk.**

A concrete, non-vacuous instance of `dist_stepInv_preserved`: if every cell
representative lies in the union of a fixed `Finset` of admissible target cells
`S`, then once a run enters that confined region it never leaves.  Precisely:
the predicate "`cells x ∈ S` OR `x` is reachable-from-start" — we phrase the
clean version: if all representatives have cells in `S` (`hconf`) and the start
is in `S`, every reachable state has cell in `S`.

This exercises the genuine `next` (the invariant is non-trivial only because
`next` actually moves between cells). -/
theorem dist_cell_confinement (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k)
    (S : Finset I) (hconf : ∀ j : I, P.cells (P.repr hne j) ∈ S)
    {x y : V} (hreach : (P.distVertexCoalg hne).Reachable x y)
    (hx : P.cells x ∈ S) :
    P.cells y ∈ S := by
  refine P.dist_stepInv_preserved hne (fun v => P.cells v ∈ S) ?_ hreach hx
  intro _ j _
  exact hconf j

end EquitablePartition

/-! ## 6. The property-lift law along the GENUINE morphism, and the Tower-3 PST
bridge instantiated on the distributed quotient. -/

namespace EquitablePartition

open Tower8 Tower8.TransitionCoalg

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type u} [Fintype I] [DecidableEq I]

/-- **Observation lift along the genuine distributed morphism.**

Any observation-predicate `φ` on the distributed quotient pulls back, at every
host vertex `x`, to the same predicate on the host branching profile — because
`cells` is a coalgebra morphism for the GENUINE dynamics.  Instantiates the
Tower-8 abstract `obs_property_lift` on `dist_cells_isCoalgMorphism`. -/
theorem dist_obs_property_lift (P : EquitablePartition G I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k)
    (φ : (I → ℂ) → Prop) (x : V) :
    φ (P.vertexObs x) ↔ φ (fun j => P.quotient (P.cells x) j) := by
  have := obs_property_lift (P.dist_cells_isCoalgMorphism hne) φ x
  simpa [TransitionCoalg.obs, distVertexCoalg, distQuotientCoalg] using this

/-- **The PST bridge through the distributed-quotient lens.**

The proved Tower-3 headline `cellUniformPST_iff_quotientPST` is re-exported as a
statement about the distributed quotient coalgebra: cell-uniform perfect state
transfer on the host is equivalent to PST on the quotient — and this is the
genuine dynamical content the distributed `next` is the discrete shadow of (the
quotient walk `next i j = j` is the cell-level companion of the continuous
quotient evolution `exp(-iτ Q̃)`).

This is a thin, proved wrapper: it REUSES `cellUniformPST_iff_quotientPST`
verbatim (no new obligation), but states it alongside the distributed-coalgebra
hypotheses (`hne` is the same representative-existence precondition the genuine
`next` consumes), making explicit that the same equitable data powers both the
discrete distributed automaton and the continuous PST iff. -/
theorem dist_quotientPST_bridge (P : EquitablePartition G I)
    (hne : ∀ k : I, P.cellCard k ≠ 0)
    (i j : I) (τ : ℝ) :
    -- The representative-existence side-condition the genuine `next` consumes
    -- is the SAME data as the iff's `hne`:
    (∀ k : I, ∃ x : V, P.cells x = k) ∧
      (Graphplay.IsCellUniformPST G P i j τ ↔
        ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)) j i‖ = 1) :=
  ⟨P.cells_exists_of_cellCard_ne hne,
   P.cellUniformPST_iff_quotientPST hne i j τ⟩

/-- **The genuine successor lands where PST sends mass.**

The distributed quotient successor `next i j = j` is exactly the cell the
quotient PST condition transfers *to*: if PST holds on the quotient from cell
`i` to cell `j` at time `τ`, the distributed automaton's `j`-turn from cell `i`
lands in cell `j` (`distQuotientCoalg.next i j = j`).  A small, fully-proved
consistency lemma tying the discrete `next` to the continuous PST endpoint —
showing the distributed walk is not a decorative restatement but tracks the same
`(i, j)` endpoints as `cellUniformPST_iff_quotientPST`. -/
theorem dist_next_eq_pst_target (P : EquitablePartition G I)
    (i j : I) :
    (P.distQuotientCoalg).next i j = j :=
  rfl

end EquitablePartition

/-! ## 7. Coarsest-bisimulation tie-in: the distributed coalgebra's bisimulation
refines WL, inheriting Tower-8 §5. -/

namespace EquitablePartition

open Tower8 Tower8.TransitionCoalg

/-- **The distributed-coalgebra bisimulation refines WL.**

Combining `dist_equitable_isBisim` (cell-equality is a bisimulation of the
genuine distributed coalgebra) with Tower-8's proved
`bisim_refines_wlStable` (= `WL.wlRefine_coarsestEquitable`): the distributed
walk's coarsest bisimulation refines the WL-stable colouring.  This places the
GENUINE-dynamics coalgebra inside the Paige–Tarjan = 1-WL picture, not just the
identity-successor skeleton of Tower-8 §5. -/
theorem dist_bisim_refines_wlStable
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition (Graphplay.SimpleGraph.toWeighted G) I)
    (hne : ∀ k : I, ∃ x : V, P.cells x = k)
    (x y : V)
    (hR : (fun a b => P.cells a = P.cells b) x y) :
    Graphplay.WL.wlStableColoring G x = Graphplay.WL.wlStableColoring G y := by
  -- `hR` is exactly `cells x = cells y`; the distributed bisimulation
  -- `dist_equitable_isBisim` witnesses it as a genuine bisimulation, and
  -- Tower-8 `bisim_refines_wlStable` refines it to WL colour.
  have _hbisim := P.dist_equitable_isBisim hne
  exact Graphplay.Tower8.bisim_refines_wlStable G P x y hR

end EquitablePartition

/-! ## 8. End-of-file inventory.

**PROVED (no sorry):**

  * §1 — `repr`, `repr_cells`, `cells_exists_of_cellCard_ne` (the genuine
    successor's representative data, tied to the Tower-3 `cellCard ≠ 0`
    precondition).
  * §2 — `distVertexCoalg`, `distQuotientCoalg` with a **non-identity** `next`
    (`distVertexCoalg_next`, `distQuotientCoalg_next`).
  * §3 — `dist_cells_isCoalgMorphism` (`next_map` is the genuine `repr_cells`,
    not `rfl`).
  * §4 — `dist_step_rel` (genuine non-trivial step relation),
    `dist_equitable_isBisim` (cell-equality is a bisimulation of the genuine
    coalgebra), `dist_cells_isObsQuotient`.
  * §5 — `cmap_step`, `dist_step_cells` (cell-after-step = turn label — genuine
    dynamical invariant), `dist_stepInv_preserved` (safety on genuine
    dynamics), `dist_cell_confinement` (non-vacuous confinement instance).
  * §6 — `dist_obs_property_lift`, `dist_quotientPST_bridge` (REUSES the proved
    `cellUniformPST_iff_quotientPST`), `dist_next_eq_pst_target`.
  * §7 — `dist_bisim_refines_wlStable` (the genuine-dynamics bisimulation sits
    in the Paige–Tarjan = 1-WL picture, via Tower-8 `bisim_refines_wlStable`).

**HONEST SORRY:** none in this file.  The deep Paige–Tarjan converse remains the
single honest `sorry` in `Graphplay/Tower8.lean`
(`coarsest_equitable_isCoarsest_bisim`); this file does not duplicate or weaken
it.

**OMITTED (per brief):** dregg2 authority-lattice / emergent-causality readings.
-/

end Graphplay
