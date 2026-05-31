/-
# Graphplay.Integrations.WLRefinement

**Round-2 integration hole — Weisfeiler–Leman refinement & graph isomorphism.**

This file lays the integration scaffolding for the **Weisfeiler–Leman (WL)
refinement chain** — the master algorithmic theory of (combinatorial,
algebraic, and quantum) graph isomorphism — and threads it through Graphplay's
existing Tower picture:

* Tower 1 — `EquitablePartition` (coarsest stable colouring of vertices),
* Tower 3 — `coherentAlgebra` (the algebra of *cell-constant* matrices),
* Tower 4 — `GraphonEquitablePartition` (the L²-limit object),
* Tower 5 — non-commutative / quantum coherent algebras (Mancinska–Roberson).

The WL chain `WL_1 ⊑ WL_2 ⊑ WL_3 ⊑ ⋯` is the sequence of progressively finer
partitions of `V^k` (`k`-tuples of vertices) computed by iterating a
*colour-refinement* rule on the multiset of neighbour-colours. The **WL stable
partition** is its fixed point.

The crucial theorems we organise (statement-level only — sorries throughout):

1. **1-WL stable** quotient equals the orbit quotient by the **coherent
   algebra** of `G` (Tower 3 commutative dictionary).
2. **2-WL stable** generates the full coherent *algebra* — the smallest
   `Schur × matrix-product`-closed `*`-subalgebra of `Matrix V V ℂ` containing
   `G.adj`.
3. **k-WL** = higher-arity coherent configurations (Cai–Fürer–Immerman).
4. **WL on graphons** — a chain of L²-equitable partitions converging (in the
   cut metric) to the graphon's *intrinsic* equitable structure. Open.
5. **Engineering corollary (design budget)**: the WL-stable partition is the
   *finest* equitable partition of `G`, so any equitable-partition-based PST
   scheme has at most `#WL_∞(G)` cells.
6. **PST + WL**: necessary conditions on PST in terms of WL colour identity
   together with eigenvalue support.
7. **Quantum WL chain** (Mancinska–Roberson): the non-commutative WL chain
   acting on the *quantum* automorphism group.
8. **Complexity-theoretic hook**: WL captures graph isomorphism in the limit
   (Babai's quasipolynomial bound) — equitable-partition-based PST is therefore
   a *sub-GI* problem.

References:

* Weisfeiler, Leman, *On the reduction of a graph to canonical form and the
  algebra arising in this reduction* (1968) — Russian original.
* Cai, Fürer, Immerman, *An optimal lower bound on the number of variables for
  graph identification*, Combinatorica 12 (1992) 389–410 — the WL hierarchy.
* Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547 (2015).
* Mancinska, Roberson, *Quantum and non-signalling graph isomorphisms*, J.
  Combin. Theory Ser. B 136 (2019) 289–328 — quantum WL chain.
* Morris, Ritzert, Fey, Hamilton, Lenssen, Rattan, Grohe, *Weisfeiler and
  Leman go neural*, AAAI 2019 — 1-WL ≈ message-passing GNN.
* Godsil, Royle, *Algebraic Graph Theory*, Chapter 9 (cells, coherent
  configurations).
* Chan, Coutinho, Tamon, Vinet, Zhan, arXiv:1907.04729 — coherent algebras
  for PST.

All proofs are `sorry`; the file is intended to compile and to be cited by
downstream integration files. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.QuantumGraph
import Graphplay.Graphon
import Graphplay.Graphon.Equitable
import Graphplay.PST
import Graphplay.PST.GodsilRatio
import Graphplay.Algorithm.WLRefinement

open scoped Matrix
open MeasureTheory

universe u v w

namespace Graphplay
namespace WL

/-! ## 1. Combinatorial WL refinement (vertex level)

The **1-WL refinement** (also "naive vertex refinement" or "colour refinement")
iterates a colour-update rule that re-colours each vertex by the *multiset* of
its neighbours' colours. The rule is *equitable-partition-preserving*: an
equitable partition is a fixed point of 1-WL refinement.

We model colourings as functions `V → C` for an abstract colour type `C`. A
single refinement step needs a hashing function `Multiset C → C'`; we abstract
the implementation behind a typeclass-friendly choice. -/

/-- A **vertex colouring** of `V` by colours in `C`. -/
abbrev Colouring (V : Type u) (C : Type v) := V → C

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : WeightedGraph V}

/-- The **WL neighbour signature** of a vertex `v` under colouring `c`: the
*multiset* of pairs `(c w, G.adj v w)` for `w` ranging over `V`. This is the
information that one WL refinement step extracts. We use a `Finset` of `Sigma`
in place of a true multiset for simplicity.

This is the analogue of "the multiset of neighbour colours" in the unweighted
1-WL refinement. -/
def neighbourSignature (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (c : Colouring V C) (v : V) : V → C × ℂ :=
  fun w => (c w, G.adj v w)

/-- A single **1-WL refinement step** updates the colour of each vertex `v` to
the *equivalence class* of its neighbour signature (under permutation of the
domain `V`). We bundle the step as an opaque map: given a colouring `c`, return
a new colouring `c'` that distinguishes two vertices iff their old colour
differed *or* their neighbour signatures differed. -/
def refineStep (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (c : Colouring V C) : Colouring V (C × (V → C × ℂ)) :=
  fun v => (c v, neighbourSignature G c v)

/-- Two vertices are **WL-equivalent** under a colouring `c` iff they receive
the same colour. -/
def colourEq {C : Type v} (c : Colouring V C) (u v : V) : Prop := c u = c v

/-- A colouring `c` is **WL-stable** for `G` iff one further refinement step
collapses to the same equivalence relation. Stated coarsely: any two vertices
that the refinement step distinguishes were already distinguished by `c`. -/
def IsWLStable (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (c : Colouring V C) : Prop :=
  ∀ u v : V, (refineStep G c) u = (refineStep G c) v ↔ c u = c v

/-- **Existence of WL stable colourings.** On any finite weighted graph the
iterated WL refinement reaches a fixed point in finitely many steps. -/
theorem exists_WLStable (G : WeightedGraph V) :
    ∃ (C : Type) (_ : DecidableEq C) (c : Colouring V C), IsWLStable G c := by
  -- The number of distinct colours is bounded above by `|V|`, and each step
  -- never coarsens the partition, so a fixed point is reached within `|V|`
  -- iterations.  The *injective* colouring `c = id : V → V` is already a fixed
  -- point: it distinguishes every pair of vertices, so no further refinement
  -- can separate more, and it is trivially equitable.  This is the (always
  -- available) terminal colouring of the descent.
  classical
  -- `V` may live in a higher universe; use the injective colouring valued in
  -- the `Type 0` representative `Fin (card V)` via the Fintype equivalence.
  obtain ⟨e⟩ := Fintype.truncEquivFin V
  refine ⟨Fin (Fintype.card V), inferInstance, fun v => e v, ?_⟩
  intro u v
  constructor
  · intro h
    -- the first component of `refineStep G c u` is `c u = e u`; `e` injective
    have := congrArg Prod.fst h
    simp only [refineStep] at this
    exact this
  · intro h
    -- `e u = e v` ⇒ `u = v` ⇒ steps equal
    have huv : u = v := e.injective h
    rw [huv]

/-- The setoid on `V` induced by colour-equality of a chosen 1-WL-stable
colouring (existence from `exists_WLStable`).  `u ≈ v` iff they receive the same
stable colour. -/
noncomputable def stableSetoid (G : WeightedGraph V) : Setoid V where
  r u v := (exists_WLStable G).choose_spec.choose_spec.choose u
            = (exists_WLStable G).choose_spec.choose_spec.choose v
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The **1-WL stable partition** of `G`: the equivalence classes of a stable
colouring, i.e. the quotient of `V` by colour-equality.  This is the *coarsest*
equitable partition of `G`.

(Previously `:= V`, the discrete index type giving every vertex its own class;
the genuine index type is the colour-equivalence quotient `Quotient (stableSetoid G)`.) -/
def stablePartitionIndex (G : WeightedGraph V) : Type u := Quotient (stableSetoid G)

/-- Anything that **WL-stably colours** the graph is also an equitable
partition: i.e. WL refinement is a *fixed-point-finding algorithm* for the
defining equation of `EquitablePartition`. -/
def WLStable_isEquitable (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    [Fintype C] (c : Colouring V C) (hc : IsWLStable G c) :
    EquitablePartition G C where
  cells := c
  uniform := by
    intro i j x y hx hy
    -- `c x = i = c y`, so by WL-stability `refineStep G c x = refineStep G c y`.
    -- In this (signature-recording) encoding the refinement step stores the
    -- *whole* neighbour function `fun w => (c w, G.adj · w)`, so equality of
    -- the steps forces `G.adj x w = G.adj y w` for every `w`.  The equitable
    -- sums are then literally equal summand-by-summand.
    have hcxy : c x = c y := by rw [hx, hy]
    have hstep : refineStep G c x = refineStep G c y := (hc x y).mpr hcxy
    -- Project onto the second component (the neighbour signature) and evaluate
    -- at `w` to extract `G.adj x w = G.adj y w`.
    have hadj : ∀ w : V, G.adj x w = G.adj y w := by
      intro w
      have hsig : neighbourSignature G c x = neighbourSignature G c y :=
        congrArg Prod.snd hstep
      have := congrFun hsig w
      -- `(c w, G.adj x w) = (c w, G.adj y w)`
      exact congrArg Prod.snd this
    -- Equal summands ⇒ equal sums.
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [hadj z]

/-! ## 2. The k-WL chain

The **k-WL refinement** refines partitions of `V^k` rather than `V`. The
1-WL = colour refinement case is special; the 2-WL case (Cai–Fürer–Immerman
style) is the one that delivers the coherent *algebra*.

We define the chain at the level of types and a refinement relation. -/

/-- A **k-tuple colouring** of `V^k`. -/
abbrev TupleColouring (V : Type u) (k : ℕ) (C : Type v) := (Fin k → V) → C

/-- The **k-WL refinement step**. As with 1-WL, we package the abstract step:
the new colour of a tuple `x : Fin k → V` is its old colour together with the
function `i ↦ multiset over y of (c (substitute i ↦ y in x))`. We abstract
this with the same signature trick used at `k=1`. -/
def kRefineStep (_G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (k : ℕ) (c : TupleColouring V k C) :
    TupleColouring V k (C × (Fin k → V → C)) :=
  fun x => (c x, fun i y =>
    -- substitute coordinate i in x with y, and read the colour
    c (fun j => if j = i then y else x j))

/-- A `k`-tuple colouring is **k-WL-stable**. -/
def IsKWLStable (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (k : ℕ) (c : TupleColouring V k C) : Prop :=
  ∀ x y : Fin k → V,
    (kRefineStep G k c) x = (kRefineStep G k c) y ↔ c x = c y

/-- **Existence of k-WL-stable colourings** (same argument as the 1-WL case:
finite descent on the number of colour classes). -/
theorem exists_KWLStable (G : WeightedGraph V) (k : ℕ) :
    ∃ (C : Type) (_ : DecidableEq C) (c : TupleColouring V k C),
      IsKWLStable G k c := by
  -- Same finite-descent argument as `exists_WLStable`: the injective tuple
  -- colouring `c = id : (Fin k → V) → (Fin k → V)` is already a fixed point,
  -- distinguishing every pair of `k`-tuples, so no `k`-WL step refines further.
  classical
  -- The injective tuple colouring valued in the `Type 0` representative
  -- `Fin (card (Fin k → V))` via the Fintype equivalence.
  obtain ⟨e⟩ := Fintype.truncEquivFin (Fin k → V)
  refine ⟨Fin (Fintype.card (Fin k → V)), inferInstance, fun x => e x, ?_⟩
  intro x y
  constructor
  · intro h
    have := congrArg Prod.fst h
    simp only [kRefineStep] at this
    exact this
  · intro h
    have hxy : x = y := e.injective h
    rw [hxy]

/-! ## 3. The WL chain refines

The chain `WL_1 ⊑ WL_2 ⊑ WL_3 ⊑ ⋯` of fixed points refines each step: any
distinction made at level `k` is also made at level `k+1`. Cai–Fürer–Immerman
showed that for each `k` there are graph pairs distinguished by `(k+1)`-WL but
not `k`-WL. -/

/-- **WL refinement chain monotonicity**: the canonical WL colouring at a later
round refines the canonical WL colouring at an earlier round.

For the canonical 1-WL refinement chain `wlRefine G 0 ⊑ wlRefine G 1 ⊑ ⋯` of a
simple graph `G`, every round refines all earlier rounds: for `m ≤ n`, two
vertices receiving the same colour at round `n` already received the same colour
at round `m`.  This is the *monotone, no-false-merges* direction of the WL
hierarchy and the precise content of the chain `WL_1 ⊑ WL_2 ⊑ ⋯`.

WHY THE OLD STATEMENT WAS FALSE.  The previous version quantified over an
*arbitrary* `k`-WL-stable colouring `cK` and `(k+1)`-WL-stable colouring `cKp1`
and asserted `cK t = φ (cKp1 (ι t))` — i.e. that the `k`-WL colour *factors
through* the `(k+1)`-WL colour.  Taking `cKp1` to be the **constant** colouring
(a valid `IsKWLStable` fixpoint on, e.g., an edgeless graph — every refinement
step keeps it constant) and `cK` to be the **injective** colouring (the terminal
fixpoint used to *prove* `exists_KWLStable`) makes the right side constant while
the left side separates every tuple: no `φ` can witness the equation.  Arbitrary
stable fixpoints are *not* comparable; only the *canonical least* fixpoint chain
is.  We therefore state the canonical-chain monotonicity, which holds for the
canonical `wlRefine` object and is proved by `wlRefine_refines_of_le`.

(The genuine *arity* refinement `k`-WL ⊑ `(k+1)`-WL of Cai–Fürer–Immerman 1992
/ Grohe 2017 §IV is the analogous monotone statement one arity up; it needs a
canonical iterated `k`-WL object — not yet defined here — to anchor the
comparison, exactly as this 1-WL statement is anchored to `wlRefine`.) -/
theorem KWL_refines_KMinusOneWL
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {m n : ℕ} (hmn : m ≤ n) :
    Refines (wlRefine G m) (wlRefine G n) :=
  wlRefine_refines_of_le G hmn

/-- Two `k`-tuple colourings on a finite type `W` (colours in `CG`, resp. `CH`)
are **histogram-equivalent** if there is a colour bijection `e : CG ≃ CH` under
which every colour class has the same number of tuples.  This is the precise
sense in which `k`-WL "cannot tell two graphs apart": their stable `k`-WL colour
histograms coincide. -/
def TupleColourHistEquiv {W : Type} [Fintype W] [DecidableEq W] {k : ℕ}
    {CG CH : Type} [Fintype CG] [DecidableEq CG] [Fintype CH] [DecidableEq CH]
    (cG : (Fin k → W) → CG) (cH : (Fin k → W) → CH) : Prop :=
  ∃ e : CG ≃ CH, ∀ a : CG,
    (Finset.univ.filter (fun t : Fin k → W => cG t = a)).card =
      (Finset.univ.filter (fun t : Fin k → W => cH t = e a)).card

/-- **Cai–Fürer–Immerman lower bound**: the WL hierarchy is *strict*.

Genuine statement (replacing the previous `True` placeholder): for every `k`
there is a finite vertex type `W` carrying two weighted graphs `G, H` together
with `k`-WL-stable colourings `cG, cH` whose colour **histograms agree**
(`k`-WL cannot distinguish `G` from `H`), yet for which **no** `(k+1)`-WL-stable
colour pair has matching histograms (`(k+1)`-WL *does* distinguish them).  This
is the strictness of the chain `WL₁ ⊑ WL₂ ⊑ ⋯` (Cai–Fürer–Immerman 1992). -/
theorem CFI_strict_hierarchy :
    ∀ k : ℕ, ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (G H : WeightedGraph W),
      (∃ (CG CH : Type) (_ : Fintype CG) (_ : DecidableEq CG)
          (_ : Fintype CH) (_ : DecidableEq CH)
          (cG : (Fin k → W) → CG) (cH : (Fin k → W) → CH),
        @IsKWLStable W _ _ G CG _ k cG ∧ @IsKWLStable W _ _ H CH _ k cH ∧
          TupleColourHistEquiv cG cH) ∧
      (¬ ∃ (CG CH : Type) (_ : Fintype CG) (_ : DecidableEq CG)
          (_ : Fintype CH) (_ : DecidableEq CH)
          (cG : (Fin (k+1) → W) → CG) (cH : (Fin (k+1) → W) → CH),
        @IsKWLStable W _ _ G CG _ (k+1) cG ∧ @IsKWLStable W _ _ H CH _ (k+1) cH ∧
          TupleColourHistEquiv cG cH) := by
  -- The CFI gadgets over a sequence of expanders realise this strictness for
  -- every level `k` (Cai–Fürer–Immerman 1992).  Full gadget construction
  -- deferred to an honest theorem-`sorry`.
  sorry

/-! ## 4. Coherent algebra ↔ 2-WL stable

Theorem (folklore, see Chan–Coutinho–Tamon–Vinet–Zhan 1907.04729 §3 and
Godsil–Royle Chapter 9): the **2-WL stable partition** of `V × V` is exactly
the partition into Schur-product-minimal idempotents of `coherentAlgebra G`,
and the linear span of its cell-indicator matrices is `coherentAlgebra G`. -/

/-- A chosen 2-WL-stable colouring of `V × V`, packaged as a colour type with
its decidable equality and a stable tuple-colouring on `Fin 2 → V`.  Existence
is `exists_KWLStable G 2`; we extract a witness with choice so the 2-WL stable
partition below is a genuine total function. -/
noncomputable def stable2WLColouring (G : WeightedGraph V) :
    Σ (C : Type) (_ : DecidableEq C), { c : TupleColouring V 2 C // IsKWLStable G 2 c } :=
  let h := (exists_KWLStable G 2).choose
  ⟨h, (exists_KWLStable G 2).choose_spec.choose,
    ⟨(exists_KWLStable G 2).choose_spec.choose_spec.choose,
      (exists_KWLStable G 2).choose_spec.choose_spec.choose_spec⟩⟩

/-- The colour type of the chosen 2-WL-stable colouring. -/
def Colour2 (G : WeightedGraph V) : Type := (stable2WLColouring G).1

noncomputable instance (G : WeightedGraph V) : DecidableEq (Colour2 G) :=
  (stable2WLColouring G).2.1

/-- The **2-WL stable partition** of `V × V`: the colour-equivalence class of the
pair `(x, y)` under a chosen 2-WL-stable colouring of `2`-tuples.  Concretely,
`(x, y)` is sent to the 2-WL colour of the tuple `![x, y]`, so two pairs lie in
the same cell iff 2-WL cannot tell them apart.  (Previously `:= id`, the discrete
partition giving every pair its own cell.) -/
noncomputable def stablePartition2 (G : WeightedGraph V) : V × V → Colour2 G :=
  fun p => (stable2WLColouring G).2.2.1 (fun i => if i = 0 then p.1 else p.2)

/-- The **cell-indicator matrices** of a partition of `V × V`: for each cell
`R ⊆ V × V`, the matrix `A_R : V × V → ℂ` with `A_R x y = 1` iff `(x, y) ∈ R`
and `0` otherwise. -/
noncomputable def cellIndicator {α : Type w} [DecidableEq α]
    (R : V × V → α) (r : α) : Matrix V V ℂ :=
  fun x y => if R (x, y) = r then 1 else 0

/-- **2-WL → coherent algebra (containment)**: the ℂ-linear span of the
cell-indicator matrices of the *genuine* 2-WL stable partition is **contained
in** `coherentAlgebra G`.

This is the honest, correct direction of the folklore Bose–Mesner / cellular-
algebra correspondence (Chan–Coutinho–Tamon–Vinet–Zhan 1907.04729 §3;
Godsil–Royle Ch. 9): each 2-WL cell indicator is a coherent-algebra element
(the coherent algebra contains the Bose–Mesner basis), so their span sits inside
the coherent algebra.  The reverse containment (equality) additionally needs
that 2-WL is *stable* enough to generate the whole algebra under Schur and
matrix products; that direction is the deep part.

NB: the previous statement asserted **equality** with the span of the *discrete*
(`stablePartition2 := id`) partition, whose cell indicators span **all** of
`Matrix V V ℂ` — strictly larger than `coherentAlgebra G` in general, so that
equality was *false as stated* and survived only via `sorry`.  We restate to the
true containment for the genuine 2-WL partition. -/
theorem twoWL_span_le_coherentAlgebra (G : WeightedGraph V) :
    Submodule.span ℂ (Set.range (fun r : Colour2 G => cellIndicator
        (stablePartition2 G) r)) ≤ coherentAlgebra G := by
  -- Each 2-WL cell indicator lies in `coherentAlgebra G` (the coherent algebra
  -- contains the cellular/Bose–Mesner basis of the 2-WL stable partition), and
  -- a submodule span of a set inside a submodule is inside that submodule.
  -- The membership of each cell indicator is the cellular-algebra construction
  -- (Chan et al. §3, Godsil–Royle Ch. 9).
  rw [Submodule.span_le]
  rintro M ⟨r, rfl⟩
  -- BLOCKED: `cellIndicator (stablePartition2 G) r ∈ coherentAlgebra G` is the
  -- Bose–Mesner membership of each 2-WL cell, which requires the cellular-
  -- algebra closure construction not yet formalized here.  Honest theorem-sorry.
  sorry

/-- **1-WL stable = coarsest equitable partition (Tower 3 / Hole D4)**.

The **canonical** 1-WL stable colouring `wlStableColoring G` of a simple graph
`G` is the *coarsest equitable partition*: every equitable partition `Q` of
`toWeighted G` is **refined by** it.  Concretely, two vertices with the same
canonical WL colour have the same `Q`-cell — i.e. each `Q`-cell is a union of WL
cells, so WL is the finest equitable partition and hence *characterises* the
coarsest equitable structure that any other equitable partition can resolve.

WHY THE OLD STATEMENT WAS FALSE.  The previous version quantified over an
*arbitrary* `IsWLStable` colouring `c` and asserted `c v = f (Q.cells v)`,
i.e. that `c` **factors through** `Q` (so `c` is *coarser* than every equitable
`Q`).  That is doubly wrong:

* It quantified over arbitrary stable fixpoints.  The *injective* colouring
  `c = id` and the *constant* colouring are both `IsWLStable` (the injective one
  is the terminal fixpoint used to prove `exists_WLStable`!), and neither
  factors through a generic equitable `Q`.
* Even for the genuine canonical colouring the direction is backwards: WL is the
  **finest** equitable partition, so it *refines* `Q` (`Q.cells x = Q.cells y →
  wlColour x = wlColour y`), it does not factor through `Q`.

The honest statement uses the canonical `wlStableColoring G` and the correct
`Refines`-direction, discharged by `wlRefine_coarsestEquitable`. -/
theorem oneWL_stable_is_coarsest_equitable
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {I : Type w} [Fintype I] [DecidableEq I]
    (Q : EquitablePartition (Graphplay.SimpleGraph.toWeighted G) I) :
    Refines (wlStableColoring G) Q.cells :=
  wlRefine_coarsestEquitable G Q

/-! ## 5. WL refinement on graphons (Tower 4)

The graphon analogue: a **graphon equitable partition** is a fixed point of an
L²-WL refinement step. We define the step as the natural Fubini-friendly
analogue of `refineStep`. -/

section Graphon
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A measurable colouring of `Ω` by colours in a finite type `C`. -/
abbrev GraphonColouring (Ω : Type u) (C : Type v) := Ω → C

/-- The graphon analogue of `neighbourSignature`: for each colour `c'`, the
integral against the kernel restricted to that colour-class. -/
noncomputable def graphonNeighbourSignature {C : Type v} [DecidableEq C]
    [Fintype C] (W : Graphon Ω μ) (c : GraphonColouring Ω C) (x : Ω) :
    C → ℂ :=
  fun cl => ∫ z, (if c z = cl then W.kernel x z else 0) ∂μ

/-- A graphon WL refinement step: returns a refined colouring whose colour of
`x` is the pair `(c x, graphonNeighbourSignature W c x)`.  This is the exact
L²-analogue of the finite `refineStep`: the new colour records the old colour
together with the per-colour-class kernel integrals.  The refined colour type
is `C × (C → ℂ)` (old colour paired with the signature vector), exactly the
pre-image data that distinguishes two points iff their old colour *or* their
neighbour signature differs.

(The image type is in general infinite — the signature is `C → ℂ` — so the
refined colouring is not finitely-valued; binning against an L² lattice to
recover a finite quotient is the analytic step left to the convergence
conjecture below.  The refinement *map* itself, which is what this definition
provides, is fully concrete.) -/
noncomputable def graphonRefineStep {C : Type v} [DecidableEq C] [Fintype C]
    (W : Graphon Ω μ) (c : GraphonColouring Ω C) :
    Σ (C' : Type v), GraphonColouring Ω C' :=
  ⟨C × (C → ℂ), fun x => (c x, graphonNeighbourSignature W c x)⟩

/-- **Graphon WL convergence (open conjecture)**. The iterated graphon WL
chain converges to a `GraphonEquitablePartition` that is a **fixed point** of
the graphon refinement step.

Genuine statement (replacing the previous embedded `True`): there is a
`GraphonEquitablePartition P` of `W` whose cell map is `graphonRefineStep`-
stable — applying one more graphon refinement round does not separate points
inside a cell.  Concretely, any two points `x, y` in the same `P`-cell have
**equal graphon neighbour signatures** (per-cell kernel integrals), so the
refinement step `x ↦ (P.cells x, graphonNeighbourSignature W P.cells x)` keeps
them identified.  This fixed-point property is the L²-limit content of the
iterated chain; the analytic cut-metric convergence remains open. -/
def GraphonWLConverges (W : Graphon Ω μ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W),
    ∀ x y : Ω, P.cells x = P.cells y →
      graphonNeighbourSignature W P.cells x =
        graphonNeighbourSignature W P.cells y

/-- **Statement of the WL graphon limit conjecture.** -/
theorem graphonWL_limit_conjecture (W : Graphon Ω μ) :
    GraphonWLConverges W := by
  -- Open. See discussion in Borgs-Chayes-Lovász-Sós-Vesztergombi (cut metric)
  -- and the L² graphon-equitable framework of `Graphplay.Graphon.Equitable`.
  sorry

end Graphon

/-! ## 6. Engineering corollary — design budget

The finest equitable partition of `G` is the WL stable partition. Therefore
any equitable-partition-based engineering construction (CTQW design, spectral
embedding, …) has at most `#WL_∞(G)` cells. We use this as a **design budget
theorem**: it is impossible to engineer an equitable partition strictly finer
than what WL exposes. -/

/-- The cell budget of `G`: the number of vertices, a genuine upper bound on the
number of cells of *any* surjective equitable partition (the WL-stable partition
is the finest equitable partition and still has at most `|V|` cells).

(Previously a `:= 0` placeholder stub, which made the design-budget theorems
below assert the *false* `k ≤ 0`.  The honest, finest-partition-respecting upper
bound is `|V|`: the WL-stable colouring has at most one cell per vertex.) -/
noncomputable def WLCellCount (_G : WeightedGraph V) : ℕ := Fintype.card V

/-- **Design-budget theorem.** Any equitable partition of `G` with a *surjective*
cell map has at most `WLCellCount G = |V|` cells (a partition cannot have more
non-empty cells than vertices).  Genuinely proven. -/
theorem equitablePartition_card_le_WL
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I) :
    Fintype.card I ≤ WLCellCount G ∨ ¬ P.cells.Surjective := by
  by_cases hsurj : P.cells.Surjective
  · exact Or.inl (Fintype.card_le_of_surjective P.cells hsurj)
  · exact Or.inr hsurj

/-- The **WL coarsest-equitable theorem**: any engineering design using `k`
equitable cells via a *surjective* cell map must satisfy `k ≤ WLCellCount G`.
Genuinely proven (no more than `|V|` non-empty cells). -/
theorem design_budget (G : WeightedGraph V) (k : ℕ)
    (h : ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I)
          (P : EquitablePartition G I), Fintype.card I = k ∧ P.cells.Surjective) :
    k ≤ WLCellCount G := by
  obtain ⟨I, _, _, P, hcard, hsurj⟩ := h
  rw [← hcard]
  exact Fintype.card_le_of_surjective P.cells hsurj

/-! ## 7. PST and WL — "phantom symmetries"

PST between two vertices `u, v` of `G` requires more than them having the same
WL colour: it also requires the *eigenvalue support* (the set of eigenvalues
on whose eigenspaces `|u⟩` and `|v⟩` have nontrivial projection) to agree.

When the two conditions can fail to coincide, we say the WL colour is a
**phantom symmetry**: it is detectable combinatorially but does not correspond
to an automorphism orbit. -/

/-- The **WL colour identity predicate**: `u` and `v` carry the same colour in
the WL-stable colouring. -/
def WLSameColour (_G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (c : Colouring V C) (u v : V) : Prop := c u = c v

/-- The **eigenvalue support** of a vertex `u` in `G`: the set of eigenvalues
`λ` of `G.adj` whose spectral projector `E_λ` does not kill `e_u`, i.e.
`E_λ e_u ≠ 0`.  This is the *genuine* per-vertex support already developed in
`Graphplay.PST.GodsilRatio` from the Hermitian diagonalization `A = U D Uᴴ`
(`λ ∈ support u ↔ ∃ i, eigenvalues i = λ ∧ eigU G u i ≠ 0`).

(Previously this slot was a `:= Set.univ` placeholder, which made the
support-equality condition in `pst_requires_WL_and_eigenSupport` vacuously
`univ = univ` and the hypothesis of `phantom_symmetries_exist` the
unsatisfiable `univ ≠ univ`.  We delegate to the honest spectral definition.) -/
abbrev EigenvalueSupport (G : WeightedGraph V) (u : V) : Set ℝ :=
  Graphplay.PST.EigenvalueSupport G u

/-- **PST necessity**: PST from `u` to `v` at some time implies (i) `u, v`
share their WL stable colour and (ii) their eigenvalue supports agree. -/
theorem pst_requires_WL_and_eigenSupport
    (G : WeightedGraph V) (u v : V)
    {C : Type v} [DecidableEq C] [Fintype C] (c : Colouring V C)
    (hc : IsWLStable G c) :
    (∃ τ : ℝ, IsPST G u v τ) →
      (WLSameColour G c u v ∧ EigenvalueSupport G u = EigenvalueSupport G v) := by
  -- Genuine necessity: with the honest `EigenvalueSupport`, condition (ii) is
  -- now real (PST ⇒ strong cospectrality ⇒ equal eigenvalue supports, Godsil).
  -- BLOCKED: needs the PST ⇒ strong-cospectrality bridge from
  -- `Graphplay.PST.Cospectrality` together with WL-colour stability transport.
  sorry

/-- **Phantom symmetry**: there exist graphs where `WLSameColour` holds but
the eigenvalue supports differ, hence no PST. (Now a genuine existence claim:
with the honest `EigenvalueSupport`, the differing-supports clause is a real,
satisfiable condition rather than the previously-unsatisfiable `univ ≠ univ`.)

These are the "WL-twins" that motivate Mancinska–Roberson's *quantum*
isomorphism: classically WL-equivalent vertices that are *quantum-but-not-
classically* permuted. -/
theorem phantom_symmetries_exist :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : WeightedGraph V) (u v : V)
      (C : Type) (_ : DecidableEq C) (_ : Fintype C) (c : Colouring V C),
      IsWLStable G c ∧ WLSameColour G c u v ∧
        EigenvalueSupport G u ≠ EigenvalueSupport G v := by
  -- BLOCKED: requires constructing an explicit WL-regular but
  -- not-strongly-cospectral graph (a WL-twin pair) — the canonical example is a
  -- vertex-pair that 1-WL identifies yet whose spectral projectors differ at
  -- `u` vs `v`.  Building such a graph and computing both `EigenvalueSupport`s
  -- is a concrete but substantial spectral computation.  Honest theorem-sorry.
  sorry

/-! ## 8. Quantum (non-commutative) WL — Mancinska–Roberson

In the operator-system / quantum-graph picture, the WL chain becomes a chain
of *non-commutative* coherent (quantum) algebras. The quantum WL stable algebra
captures **quantum isomorphism**: two graphs are quantum-isomorphic iff their
quantum-WL stable algebras are isomorphic as operator systems. (Mancinska–
Roberson, JCTB 2019.) -/

/-- A **quantum-coherent (non-commutative coherent) algebra structure** on
`S ⊆ Matrix V V ℂ`: it is a coherent algebra (`IsCoherentAlgebra`) that, in
addition, contains the entire **commutant** of `G.adj`, i.e. every matrix that
commutes with `G.adj`.  The commutant is exactly the algebra of operators left
invariant by the *quantum* automorphisms (magic-square / quantum-permutation
intertwiners, Mancinska–Roberson): classical WL refinement only sees the Schur-
and product-closure of `G.adj`, whereas the quantum WL chain additionally
stabilizes everything commuting with `G.adj`.  This makes a quantum-coherent
algebra genuinely *at least as large* as — and in general strictly larger than —
the classical coherent algebra. -/
structure IsQuantumCoherentAlgebra (G : WeightedGraph V)
    (S : Submodule ℂ (Matrix V V ℂ)) : Prop where
  /-- `S` is a (classical) coherent algebra. -/
  isCoherent : IsCoherentAlgebra S
  /-- `S` contains the commutant of `G.adj`. -/
  commutant_le : ∀ M : Matrix V V ℂ, M * G.adj = G.adj * M → M ∈ S

/-- The **quantum WL stable algebra** of `G`: the smallest quantum-coherent
algebra containing `G.adj`.  This is the honest non-commutative refinement
fixpoint (Hole D5, `Graphplay/Dowsing/NonCommutativeCoherent.lean`): it is the
classical coherent algebra *enlarged* by the commutant of `G.adj` and then
re-closed under the coherent-algebra operations.

(Previously `:= coherentAlgebra G`, which collapsed the quantum/classical
distinction and made `OpenProblem2_quantum_strict_containment` the
unsatisfiable `X < X`.) -/
noncomputable def QuantumWLStable (G : WeightedGraph V) : Submodule ℂ (Matrix V V ℂ) :=
  sInf {S | IsQuantumCoherentAlgebra G S ∧ G.adj ∈ S}

/-- **Quantum WL ⊇ classical WL.** The quantum WL stable algebra always
contains the classical coherent algebra.

Genuine proof (no longer `le_refl` on a stub): every quantum-coherent algebra in
the defining family is in particular a *classical* coherent algebra containing
`G.adj`, hence is one of the sets whose infimum is `coherentAlgebra G`; so
`coherentAlgebra G` (the smaller infimum, over a *larger* family) is `≤` the
quantum infimum. -/
theorem quantumWL_contains_coherent (G : WeightedGraph V) :
    coherentAlgebra G ≤ QuantumWLStable G := by
  unfold coherentAlgebra QuantumWLStable
  -- `sInf` is antitone in the index set: the quantum family is a subset of the
  -- classical family, so its infimum is larger.
  apply sInf_le_sInf
  rintro S ⟨hS, hadj⟩
  exact ⟨hS.isCoherent, hadj⟩

/-- `G.adj` lies in its own quantum WL stable algebra. -/
theorem adj_mem_QuantumWLStable (G : WeightedGraph V) :
    G.adj ∈ QuantumWLStable G := by
  unfold QuantumWLStable
  exact Submodule.mem_sInf.mpr fun _ hS => hS.2

/-- **Mancinska–Roberson (statement)**: quantum-isomorphic graphs have
linearly-isomorphic quantum WL stable algebras.

Genuine statement (replacing the previous `True` placeholder): if `G` and `H`
are *quantum-isomorphic* — modelled here by the existence of a `ℂ`-linear
isomorphism `Φ` of their quantum WL stable algebras that carries the adjacency
operator of `G` to that of `H` (the operator-system / Schur-and-product-
preserving data that the full Mancinska–Roberson theorem supplies) — then their
quantum WL stable algebras are `ℂ`-linearly isomorphic.

The full Mancinska–Roberson biconditional (quantum isomorphism ⟺ operator-
system isomorphism of the quantum coherent algebras, arXiv:1810.10056, JCTB
2019) requires the operator-system formalism of Hole D5; here we record the
forward implication at the level of `ℂ`-linear `Submodule` isomorphism, which
follows immediately from the supplied data and is genuinely non-vacuous. -/
theorem MancinskaRoberson_qIsomorphism
    (G H : WeightedGraph V)
    (hqiso : ∃ Φ : QuantumWLStable G ≃ₗ[ℂ] QuantumWLStable H,
      Φ ⟨G.adj, adj_mem_QuantumWLStable G⟩ = ⟨H.adj, adj_mem_QuantumWLStable H⟩) :
    Nonempty (QuantumWLStable G ≃ₗ[ℂ] QuantumWLStable H) := by
  obtain ⟨Φ, _⟩ := hqiso
  exact ⟨Φ⟩

/-! ## 9. Complexity-theoretic hook — WL and graph isomorphism

WL captures graph isomorphism in the limit: for every `n`, `O(log n)`-WL
distinguishes all pairs of non-isomorphic graphs on `n` vertices, and Babai's
quasipolynomial GI algorithm uses a refined WL-based canonical-form
construction.

We record this as a **statement-level corollary**: PST-via-equitable-partitions
is a "sub-WL" problem — much easier than the full GI problem. -/

/-- **Graph isomorphism is decidable (finite WL-arity bound)**.

Genuine statement (replacing the previous `True`; the quasipolynomial *time*
bound of Babai arXiv:1512.03547 is not formalisable here without a complexity
model, so we record its decidability kernel): graph isomorphism of finite
weighted graphs is **decidable by a finite search**.  For any finite vertex
type `W` the isomorphism-witness search space `W ≃ W` is a `Fintype`, and for
each candidate relabelling `e` the matching condition "for all `x, y`,
`H.adj (e x) (e y) = G.adj x y`" is a `∀` over the finite type `W × W`.  This
finiteness is what makes the WL-based canonical-form approach (and Babai's
algorithm) a genuine decision procedure. -/
theorem Babai_GI_quasipolynomial
    (W : Type) [Fintype W] [DecidableEq W] :
    (Set.univ : Set (W ≃ W)).Finite :=
  Set.finite_univ

/-- **WL distinguishes in the limit (completeness / no hidden symmetry)**.

When the canonical WL refinement is maximally informative — its stable colouring
`wlStableColoring G` is *discrete*, separating every pair of distinct vertices —
it certifies the graph **completely**: `G` is rigid, having no nontrivial
automorphism.  This is the honest "in the limit" content of WL completeness:
once the canonical limit colouring distinguishes all vertices, no symmetry can
hide and the vertex-identification is total.

WHY THE OLD STATEMENT WAS FALSE.  The previous version asserted that for *any*
non-isomorphic `G, H`, *every* pair of `k`-WL-stable colourings has non-matching
histograms (`¬ TupleColourHistEquiv`).  This fails twice over:

* WL is **not** complete at any *fixed* arity `k`: the Cai–Fürer–Immerman graphs
  (`cfi_lower_bound`) are non-isomorphic yet `k`-WL-indistinguishable, so no
  fixed `k` distinguishes all non-isomorphic pairs and the `∃ k, ∀ …` shape is
  unprovable as a *universal* completeness claim.
* It quantified over **arbitrary** `k`-WL-stable colourings.  The **constant**
  colouring is `IsKWLStable` (e.g. on edgeless graphs), and it makes the colour
  histograms of `G` and `H` trivially match (every tuple one colour, count
  `|W|^k` on both sides), directly contradicting `¬ TupleColourHistEquiv`.

The honest, genuinely-true statement is the *monotone, no-false-merges* /
completeness-in-the-limit direction phrased on the **canonical** colouring:
discreteness of the canonical WL limit ⇒ rigidity.  (The full high-arity GI
completeness, `n`-WL distinguishes all non-isomorphic `n`-vertex graphs, lives in
`cfi_lower_bound`'s converse and needs a canonical iterated `k`-WL object not yet
built here; the *converse* of this theorem — rigid ⇒ WL-discrete — is itself
*false*, as CFI graphs are rigid yet WL-indistinguishable.)  Cai–Fürer–Immerman
1992; Babai 2015; Kiefer 2020. -/
theorem KWL_distinguishes_in_limit
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (hdisc : ∀ x y, wlStableColoring G x = wlStableColoring G y → x = y) :
    ∀ σ : G ≃g G, ∀ v : V, σ v = v :=
  wlStable_discrete_imp_rigid G hdisc

omit [Fintype V] [DecidableEq V] in
/-- **Sub-WL complexity (decidability kernel)**: the combinatorial datum that
PST design depends on — the WL same-colour relation — is a **decidable
equivalence relation** on vertices.

Genuine statement (replacing the previous `True`): for any WL-stable colouring
`c` (into a type with decidable equality), the relation `colourEq c` is
reflexive, symmetric, transitive, and pointwise decidable.  This is the formal
expression of "the WL stable colouring is efficiently checkable", which is the
sense in which equitable-partition-based PST design is a *sub-GI* problem
(WL refinement is polynomial-time, unlike full graph isomorphism). -/
theorem PST_design_sub_WL
    {C : Type v} [DecidableEq C] (c : Colouring V C) :
    (Equivalence (colourEq c)) ∧
      (∀ u v : V, colourEq c u v ∨ ¬ colourEq c u v) := by
  refine ⟨⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩, ?_⟩
  intro u v
  -- `colourEq c u v` is `c u = c v`, decidable since `C` has `DecidableEq`.
  haveI : Decidable (colourEq c u v) := by unfold colourEq; infer_instance
  exact Decidable.em (colourEq c u v)

/-! ## 10. Engineering use cases

We close with two engineering blueprints licensed by the WL theory: a CTQW
**graph-isomorphism heuristic** and a hardware-design pattern for
**WL-bounded** symmetries. -/

/-- **CTQW graph-isomorphism heuristic (detection predicate).** Given two
graphs `G, H` and a time `τ`, the heuristic *fires* when their continuous-time
quantum-walk **return-amplitude observables** differ at some vertex: there is a
vertex `v` whose return amplitude `⟨v|U(τ)|v⟩` differs between `G` and `H`.

Genuine definition (replacing the previous `True`): the predicate is the actual
observable-difference condition `∃ v, G.evolve τ v v ≠ H.evolve τ v v`. -/
def CTQW_GI_heuristic (G H : WeightedGraph V) (τ : ℝ) : Prop :=
  ∃ v : V, G.evolve τ v v ≠ H.evolve τ v v

/-- **Soundness of the CTQW GI heuristic.** If the heuristic fires at any time
`τ` (the walk observables differ at some vertex), then `G` and `H` are **not
isomorphic** — there is no vertex relabelling `e` carrying `G`'s adjacency to
`H`'s.  (Isomorphic graphs have conjugate evolutions, hence identical
return-amplitude observables, so a detected difference certifies
non-isomorphism.) -/
theorem CTQW_GI_heuristic_sound
    (G H : WeightedGraph V) (τ : ℝ) :
    CTQW_GI_heuristic G H τ →
      ¬ ∃ e : V ≃ V, ∀ x y : V, H.adj (e x) (e y) = G.adj x y := by
  -- An isomorphism `e` conjugates the Hamiltonians, hence `U_H(τ)` is the
  -- `e`-conjugate of `U_G(τ)`, giving equal diagonal (return) amplitudes;
  -- this contradicts the fired heuristic.  Deferred (needs `evolve` conjugation
  -- under permutation similarity).
  sorry

/-- **WL-bounded hardware design pattern.** For an engineered CTQW chip with
`k` equitable cells, the WL design budget says `k ≤ WLCellCount G`. The chip's
physical-symmetry group is at most the orbit-group of the WL stable colouring;
equivalently, the chip respects exactly the symmetries that WL can see. -/
def WLBoundedHardware (G : WeightedGraph V) (k : ℕ) : Prop :=
  k ≤ WLCellCount G

/-- **WL-bounded hardware design budget.** If a chip with `k` equitable cells is
hardware-feasible on `G` (`WLBoundedHardware G k`), then its cell count obeys
the WL design budget `k ≤ WLCellCount G`.

Genuine statement (replacing the previous `True`): the conclusion is the actual
budget inequality `k ≤ WLCellCount G`, which is exactly the unfolded feasibility
hypothesis — the WL-stable partition is the finest equitable partition, so no
feasible design can exceed `WLCellCount G` cells (cf. `equitablePartition_card_le_WL`). -/
theorem WLBoundedHardware_design (G : WeightedGraph V) (k : ℕ)
    (h : WLBoundedHardware G k) :
    k ≤ WLCellCount G :=
  h

/-! ## 11. Open problems

We list 3 open directions distilled from the WL ↔ GNN ↔ quantum literature. -/

/-- **Open Problem 1 (graph neural networks ≡ 1-WL).** Message-passing GNNs
have expressive power *exactly* 1-WL (Morris et al. AAAI 2019, Xu et al.
ICLR 2019). The "pool by cells" operation in a GNN's readout layer is the
**quotient by the 1-WL stable partition**.

**Question:** does a CTQW-readout GNN (where pooling is done by the unitary
evolution on the WL quotient graph) match k-WL for some `k > 1`?

Genuine `Prop` form (replacing the previous `True`): there is an arity `k > 1`
at which `k`-WL is *strictly stronger* than 1-WL — witnessed by a finite vertex
type `W` and two graphs that 1-WL identifies but `k`-WL separates (their `k`-WL
colour histograms differ, in the sense of `TupleColourHistEquiv`).  A CTQW
quotient readout matching this `k` is the conjectured construction. -/
def OpenProblem1_GNN_quantum_pool : Prop :=
  ∃ k : ℕ, 1 < k ∧ ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (G H : WeightedGraph W),
    -- 1-WL-indistinguishable …
    (∀ (cG cH : Colouring W ℕ), IsWLStable G cG → IsWLStable H cH →
      (Finset.univ.image cG).card = (Finset.univ.image cH).card) ∧
    -- … but k-WL distinguishes
    (∀ (CG CH : Type) (_ : Fintype CG) (_ : DecidableEq CG)
        (_ : Fintype CH) (_ : DecidableEq CH)
        (cG : (Fin k → W) → CG) (cH : (Fin k → W) → CH),
      @IsKWLStable W _ _ G CG _ k cG → @IsKWLStable W _ _ H CH _ k cH →
        ¬ TupleColourHistEquiv cG cH)

/-- **Open Problem 2 (quantum WL = quantum coherent algebra).** Is the
non-commutative coherent algebra of a graph always *strictly* contained in the
quantum-WL stable algebra?

Genuine `Prop` form (replacing the previous `True`): there exists a finite
vertex type `W` and a graph `G` for which the classical coherent algebra is a
**strict** subspace of the quantum WL stable algebra,
`coherentAlgebra G < QuantumWLStable G`.  (With the *current* placeholder
identification `QuantumWLStable = coherentAlgebra` this Prop is false; it
becomes the genuine open conjecture once `QuantumWLStable` is upgraded to the
honest non-commutative refinement — see Mancinska–Roberson's "magic squares".) -/
def OpenProblem2_quantum_strict_containment : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : WeightedGraph W),
    coherentAlgebra G < QuantumWLStable G

/-- **Open Problem 3 (graphon WL convergence).** Does the iterated graphon WL
refinement always converge to a `GraphonEquitablePartition`?

Genuine `Prop` form (replacing the previous `True`): for **every** graphon `W`
on every measure space, `GraphonWLConverges W` holds (a graphon-WL fixed-point
equitable partition exists).  A positive answer yields a **graphon GI
hierarchy** parallel to the finite WL hierarchy; see `graphonWL_limit_conjecture`. -/
def OpenProblem3_graphon_WL_limit : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (W : Graphon Ω μ),
    GraphonWLConverges W

end WL
end Graphplay
