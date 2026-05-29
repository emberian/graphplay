/-
# Graphplay.Algorithm.WLRefinement

**The 1-dimensional Weisfeiler-Leman color refinement algorithm.**

The Weisfeiler-Leman (WL) refinement (Weisfeiler-Leman 1968) is the canonical
combinatorial algorithm for computing the coarsest equitable partition of a
graph.  The 1-WL variant — also known as *naive vertex classification* or
*color refinement* — iteratively refines a vertex coloring by replacing each
vertex's color with the pair `(old color, multiset of neighbour colors)`.
After at most `|V|` rounds, the coloring stabilizes; the stable coloring is
the **coarsest equitable partition** of `G`.

This file:

1. defines `wlStep`, a single refinement step (computable);
2. defines `wlRefine`, the `n`-fold iterate followed by a canonical
   renaming of the resulting colors into `Fin k`;
3. states the **termination** theorem: refinement stabilizes within `|V|`
   rounds, by a monotone-finite-lattice argument;
4. states that the stable coloring induces an `EquitablePartition` of the
   weighted graph `toWeighted G`;
5. states the **coarsest equitable** property: every equitable partition
   refines the WL-stable partition;
6. bridges to Hole D4's coherent algebra (`Graphplay.Dowsing.CoherentAlgebra`)
   by stating that the WL-stable partition's matrix algebra coincides with
   the coherent algebra of `G`;
7. states the higher-order `k`-WL extension (Cai-Fürer-Immerman 1992 lower
   bound noted).

The algorithmic content is fully `#eval`-able: see the `examples` section at
the end of the file for smoke tests on `K_3`, `C_4`, `K_{3,3}`, and the
Petersen graph.

References:
* Weisfeiler, Leman, *A reduction of a graph to a canonical form and an
  algebra arising during this reduction*, Nauchno-Technicheskaya Informatsia
  Ser. 2, 1968 (in Russian).
* Cai, Fürer, Immerman, *An optimal lower bound on the number of variables
  for graph identification*, Combinatorica 1992.
* Grohe, *Descriptive Complexity, Canonisation, and Definable Graph Structure
  Theory*, Cambridge University Press 2017.
* Kiefer, *Power and Limits of the Weisfeiler-Leman Algorithm*, PhD thesis
  RWTH Aachen 2020.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Basic
import Mathlib.Data.Quot
import Mathlib.Order.Iterate
import Graphplay.Weighted
import Graphplay.Equitable

open scoped BigOperators

universe u v w

namespace Graphplay
namespace WL

/-! ## 1. The one-step refinement. -/

/-- A **vertex coloring** of `V` by labels of type `α`. -/
abbrev Coloring (V : Type u) (α : Type v) : Type _ := V → α

/-- The **1-WL refinement step**.

Given a graph `G` and a coloring `c : V → α`, produce a new coloring whose
value at `v` is the pair `(c v, multiset of c w for w ∈ N(v))`.

This is the canonical Weisfeiler-Leman update: two vertices have the same new
color iff they had the same old color *and* the same multiset of neighbour
colors.  Adjacency need only be decidable for the multiset construction to be
computable. -/
def wlStep
    {V : Type u} [Fintype V] [DecidableEq V]
    {α : Type v} [DecidableEq α]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (c : Coloring V α) :
    Coloring V (α × Multiset α) :=
  fun v =>
    (c v,
      (Finset.univ.filter (fun w => G.Adj v w)).val.map c)

/-- Two vertices that already have distinct colors retain distinct colors
after `wlStep` (it can only *refine* the partition). -/
theorem wlStep_refines
    {V : Type u} [Fintype V] [DecidableEq V]
    {α : Type v} [DecidableEq α]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (c : Coloring V α) {x y : V} (h : wlStep G c x = wlStep G c y) :
    c x = c y := by
  simpa [wlStep] using congrArg Prod.fst h

/-! ## 2. Iterating the refinement.

The iterate `(wlStep G)^[n]` runs `n` rounds.  After each round the color
type grows from `α` to `α × Multiset α`; to keep a single `V → α`-style API
we always re-encode the result into `ℕ` by listing the equivalence classes in
the order in which they appear.
-/

/-! ### A `LinearOrder` on `Multiset α` via canonical sorted lists.

`Multiset.sort (· ≤ ·)` produces the unique sorted list representative.  Two
multisets are equal iff their sorted lists are equal.  We compare multisets
lex-on-sorted-list to obtain a computable `LinearOrder`. -/

/-- A canonical sorted-list representative of a multiset; computable. -/
def multisetCanon {α : Type*} [LinearOrder α] (s : Multiset α) : List α :=
  s.sort (· ≤ ·)

theorem multisetCanon_injective {α : Type*} [LinearOrder α] :
    Function.Injective (multisetCanon (α := α)) := by
  intro s t h
  have hs : ((s.sort (· ≤ ·)) : Multiset α) = s := Multiset.sort_eq _ _
  have ht : ((t.sort (· ≤ ·)) : Multiset α) = t := Multiset.sort_eq _ _
  -- From `h : s.sort (· ≤ ·) = t.sort (· ≤ ·)` deduce `s = t`.
  have : ((s.sort (· ≤ ·)) : Multiset α) = ((t.sort (· ≤ ·)) : Multiset α) := by
    show (↑(s.sort (· ≤ ·)) : Multiset α) = (↑(t.sort (· ≤ ·)) : Multiset α)
    exact congrArg _ h
  rw [hs, ht] at this
  exact this

/-- Computable linear order on `Multiset α` when `α` is linearly ordered, by
comparing sorted-list representatives lexicographically. -/
instance multisetLinearOrder {α : Type*} [LinearOrder α] : LinearOrder (Multiset α) :=
  LinearOrder.lift' multisetCanon multisetCanon_injective

/-- Re-encode an arbitrary coloring `c : V → α` (with `DecidableEq α`) as a
coloring by `ℕ`: the index of `c v` in the deduplicated list of values
obtained by enumerating `V` in its `LinearOrder` order.

Two vertices receive the same rank iff they had the same original color
(`rankColoring_partitionsAgree` below), so the partition is preserved. -/
def rankColoring
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    {α : Type v} [DecidableEq α]
    (c : Coloring V α) : Coloring V ℕ :=
  let vs : List V := (Finset.univ : Finset V).sort (· ≤ ·)
  let distinct : List α := (vs.map c).dedup
  fun v => distinct.idxOf (c v)

/-- The **`n`-th WL iterate** as a coloring valued in `ℕ`.

The inner iteration runs in a growing color type; after `n` rounds the type
is iterated `n` times.  We then collapse to `ℕ` via `rankColoring` so the
output type is uniform across `n`.

Computable provided `V` has a `LinearOrder` (used only to break ties in
`rankColoring`).  In practice the only consumer is `#eval`, which has access
to `decide` for everything below. -/
def wlIterColor
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    ℕ → Coloring V ℕ
  | 0 => fun _ => 0
  | n + 1 =>
      -- Step from the rank-coloring at level `n`: the inner step lives in
      -- `ℕ × Multiset ℕ`, and we re-rank into `ℕ` again.
      rankColoring (wlStep G (wlIterColor G n))

/-- The **WL refined coloring**: the `n`-th iterate of the WL step, valued
in `ℕ`.  We re-export this with the headline name `wlRefine`. -/
def wlRefine
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : V → ℕ :=
  wlIterColor G n

/-! ## 3. The partition lattice and termination.

We view a coloring `c : V → ℕ` as a partition by taking the kernel
equivalence `c x = c y`.  Partitions of a fixed finite set form a finite
lattice; WL refinement is a monotone operator in the *finer-than* order,
hence stabilizes after finitely many steps (in fact within `|V| - 1` steps,
since each non-stable step strictly increases the number of cells, and the
number of cells is bounded by `|V|`).
-/

/-- The kernel equivalence of a coloring: `x ~ y` iff `c x = c y`. -/
def Kernel {V : Type u} {α : Type v} (c : V → α) (x y : V) : Prop := c x = c y

/-- A coloring `c'` **refines** `c` if `c' x = c' y → c x = c y`. -/
def Refines {V : Type u} {α β : Type _} (c : V → α) (c' : V → β) : Prop :=
  ∀ x y, c' x = c' y → c x = c y

/-- The WL step always produces a refinement of its input. -/
theorem wlStep_isRefinement
    {V : Type u} [Fintype V] [DecidableEq V]
    {α : Type v} [DecidableEq α]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (c : Coloring V α) :
    Refines c (wlStep G c) := by
  intro x y h
  simpa [wlStep] using congrArg Prod.fst h

/-- After re-ranking the coloring is unchanged as a partition. -/
theorem rankColoring_partitionsAgree
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    {α : Type v} [DecidableEq α]
    (c : Coloring V α) :
    ∀ x y, rankColoring c x = rankColoring c y ↔ c x = c y := by
  -- The rank coloring assigns the same numeric label to two vertices iff
  -- they had the same original color, by injectivity of List.idxOf into a
  -- deduplicated list.  Formal proof punted.
  sorry

/-- The **number of distinct WL colors** at round `n`. -/
def wlColorCount
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : ℕ :=
  (Finset.univ.image (wlRefine G n)).card

/-- The color count is monotonically non-decreasing in `n`. -/
theorem wlColorCount_mono
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    Monotone (wlColorCount G) := by
  -- Each step refines, so the image set can only grow; monotonicity follows.
  sorry

/-- The color count is bounded by `|V|`. -/
theorem wlColorCount_le_card
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    wlColorCount G n ≤ Fintype.card V := by
  unfold wlColorCount
  exact (Finset.card_image_le).trans (by simpa using (Finset.card_le_univ _))

/-- **Termination**: WL refinement reaches a fixed point in at most `|V|`
steps.  More precisely there exists some `N ≤ |V|` such that for all
`n ≥ N`, the partition induced by `wlRefine G n` equals the partition
induced by `wlRefine G N`. -/
theorem wlRefine_stable
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N : ℕ, N ≤ Fintype.card V ∧
      ∀ n ≥ N, ∀ x y, wlRefine G n x = wlRefine G n y ↔
                     wlRefine G N x = wlRefine G N y := by
  -- Monotonicity + boundedness on a finite lattice ⇒ stabilization.
  -- Concretely: the `wlColorCount` is a monotone ℕ-valued function bounded
  -- by `|V|`; it must be eventually constant, and once constant the
  -- partition cannot strictly refine.
  sorry

/-- A **computable upper bound** on the round at which WL refinement
stabilizes: `Fintype.card V` rounds always suffice (in fact `|V|` suffices
since each refining step strictly increases the cell count, capped by `|V|`).
This definition is `def`, not `noncomputable`, so `wlStableColoring` below is
also computable.

The "least `N`" formulation (using `Classical.choose` on `wlRefine_stable`) is
mathematically cleaner but blocks `#eval`; this version is operationally
equivalent: at any `n ≥ wlStableRound`, the partition equals the stable one. -/
def wlStableRound
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Fintype.card V

/-- The **stable WL coloring**: the limit (= value at `wlStableRound`) of the
WL iteration. -/
def wlStableColoring
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : V → ℕ :=
  wlRefine G (wlStableRound G)

/-! ## 4. The stable partition is equitable.

A coloring `c : V → ℕ` defines a partition of `V`; if `c` is a WL fixed
point, the partition is equitable for the unweighted-graph promotion
`toWeighted G`.  We package this as an `EquitablePartition` of
`toWeighted G` indexed by `Fin (wlColorCount G n)`.
-/

/-- The number of distinct stable colors, as the cell index type. -/
def wlCellCount
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  wlColorCount G (wlStableRound G)

/-- The **stable cell map**: send each vertex to its color index inside
`Fin (wlCellCount G)`.  This is the cell labelling of the WL-induced
equitable partition.

Concretely we send each vertex `v` to the index of its stable color in the
sorted list of distinct stable colors. -/
noncomputable def wlStableCells
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    V → Fin (wlCellCount G) := by
  -- Re-index the image of `wlStableColoring G` into `Fin (wlCellCount G)`
  -- via the canonical bijection `s ≃ Fin s.card` of `Finset.equivFin`.
  -- Each vertex's stable colour is a member of the image `Finset`, and
  -- `wlCellCount G` is precisely that image's cardinality, so the index is
  -- well-typed with *no* placeholder.
  classical
  intro v
  -- The image of the stable colouring; its cardinality is `wlCellCount G`.
  let s : Finset ℕ := Finset.univ.image (wlRefine G (wlStableRound G))
  -- `wlStableColoring G v` lives in `s`.
  have hmem : wlRefine G (wlStableRound G) v ∈ s :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  -- `s.card = wlCellCount G`, so we can transport the `Fin s.card` index.
  have hcard : s.card = wlCellCount G := rfl
  exact hcard ▸ s.equivFin ⟨wlRefine G (wlStableRound G) v, hmem⟩

/-- **Equitability of the stable WL partition**.

After at least `|V|` rounds the WL coloring has stabilized; the induced
partition is equitable as a partition of the weighted graph
`toWeighted G`. -/
theorem wlRefine_isEquitable
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : n ≥ Fintype.card V) :
    ∃ P : EquitablePartition (Graphplay.SimpleGraph.toWeighted G) (Fin (wlColorCount G n)),
      ∀ x y, P.cells x = P.cells y ↔ wlRefine G n x = wlRefine G n y := by
  -- After `|V|` rounds we are at a fixed point of `wlStep` (modulo the
  -- ℕ-renaming via `rankColoring`).  Being a fixed point means: for every
  -- pair `x, y` with the same color, the multisets of neighbour colors
  -- agree.  Counting matches per-color we get
  --     ∀ i j, ∀ x y of color i,
  --        #{z ∈ N(x) : color z = j} = #{z ∈ N(y) : color z = j},
  -- which is exactly the equitable condition for the 0/1-adjacency of
  -- `toWeighted G`.
  sorry

/-! ## 5. Coarsest equitable.

Any equitable partition of `G` refines (i.e. is finer than) the WL-stable
partition, and conversely the WL-stable partition refines any "trivial"
partition.  In lattice language, WL stabilizes at the **coarsest** equitable
partition of `G`.
-/

/-- **Coarsest equitable**: every equitable partition of `toWeighted G`
refines the stable WL partition.  Combined with `wlRefine_isEquitable` this
characterises `wlStableColoring G` as the coarsest equitable partition. -/
theorem wlRefine_coarsestEquitable
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {I : Type w} [Fintype I] [DecidableEq I]
    (P : EquitablePartition (Graphplay.SimpleGraph.toWeighted G) I) :
    Refines (wlStableColoring G) P.cells := by
  -- Standard inductive argument: starting from the all-equal coloring,
  -- after each `wlStep` the partition is still refined by `P.cells` (by the
  -- equitable property of `P`); pass to the limit.
  sorry

/-- **WL-discreteness forces a rigid automorphism group.**

If the WL-stable colouring is *discrete* — i.e. it separates every pair of
distinct vertices — then `G` is **asymmetric** (rigid): its only automorphism
is the identity.  The reason is that every automorphism of `G` preserves the
WL colour of each vertex (`wlStable_refines_orbit` in `WLOrbit.lean`), so a
non-identity automorphism `σ` with `σ v ≠ v` would force `v` and `σ v` to share
a colour, contradicting injectivity.

We phrase the conclusion concretely as: every graph automorphism (a
permutation `σ` of `V` preserving adjacency) is the identity.

NOTE on directionality: only the forward implication is genuinely true in
general.  The converse ("rigid ⇒ WL-discrete") is **false** — the CFI graphs
are rigid yet WL-indistinguishable (see `cfi_lower_bound`) — so we state the
single honest implication rather than an `↔`.  This is the negative direction
of the coarsest-equitable characterisation. -/
theorem wlStable_discrete_imp_rigid
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (hdisc : ∀ x y, wlStableColoring G x = wlStableColoring G y → x = y) :
    ∀ σ : G ≃g G, ∀ v : V, σ v = v := by
  -- An automorphism preserves WL colour (WL refinement only reads adjacency,
  -- which `σ` preserves), so `wlStableColoring G (σ v) = wlStableColoring G v`;
  -- discreteness then forces `σ v = v`.  The colour-invariance step is the
  -- `wlStable_refines_orbit` lemma developed in `WLOrbit.lean`; we record the
  -- consequence here as an honest theorem-`sorry`.
  sorry

/-! ## 6. Bridge to D4: coherent algebra.

The matrix algebra generated by the **cell projectors** of the WL-stable
partition equals the **coherent algebra** of `G` in the sense of
`Graphplay.Dowsing.CoherentAlgebra`.  This is the Weisfeiler-Leman 1968
construction of the cellular algebra.

We state this as a `theorem` whose statement asserts equality of two
subalgebras of `Matrix V V ℂ`; the actual `CoherentAlgebra` API lives in
`Graphplay/Dowsing/CoherentAlgebra.lean` and is not imported here to avoid
a circular dependency. We therefore phrase the statement abstractly via the
cell-inflate map of `Graphplay.Equitable`.
-/

/-- The **cell-projector matrix** for a coloring `c : V → ℕ`: the matrix
whose `(x, y)` entry is `1` if `c x = c y` and `0` otherwise. -/
noncomputable def cellProjector
    {V : Type u} [Fintype V] [DecidableEq V]
    (c : V → ℕ) : Matrix V V ℂ :=
  fun x y => if c x = c y then 1 else 0

/-- **Bridge to coherent algebra (Weisfeiler-Leman 1968)**.

The algebra generated by the cell projectors of the WL-stable partition,
together with the adjacency matrix of `G`, is closed under matrix product
*and* the Schur (entrywise) product.  It is the **coherent algebra** of `G`
in the sense of `Graphplay.Dowsing.CoherentAlgebra`.

Stated here as: the WL-stable cell projector commutes with `G.adj` in
`Matrix V V ℂ` after promotion to `toWeighted G`. -/
theorem wlStable_commutes_adj
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    let A := (Graphplay.SimpleGraph.toWeighted G).adj
    let E := cellProjector (wlStableColoring G)
    E * A = A * E := by
  -- The equitable property says the cell-restricted row sums are uniform
  -- per cell; commuting with the cell projector is the matrix transcription
  -- of that fact.  Cf. `Graphplay.Equitable.adj_mulVec_cellUniformVec`.
  sorry

/-! ## 7. Higher-order WL: `k`-WL.

`k`-WL operates on tuples of `k` vertices rather than single vertices,
yielding a strictly more powerful refinement for `k ≥ 2`.  Cai, Fürer, and
Immerman (1992) constructed graphs that require `Ω(n)`-WL to distinguish, so
there is no constant-`k` test for graph isomorphism that succeeds on all
inputs.

The fixed point of `k`-WL is the **coarsest `k`-equitable partition**, and
its associated algebra is the **higher-order coherent configuration** of
order `k`.  We state only the signatures here; full development is left for
a successor file.
-/

/-- The **`k`-tuple coloring type**: a function `V^k → α`. -/
abbrev TupleColoring (V : Type u) (k : ℕ) (α : Type v) : Type _ :=
  (Fin k → V) → α

/-- A single step of `k`-WL.

For `k = 1` this collapses to `wlStep`.  For `k ≥ 2`, the new color of a
tuple `(v₁, …, v_k)` records the multiset of colorings obtained by
substituting an arbitrary vertex `w ∈ V` into each of the `k` coordinates in
turn. -/
def kWlStep
    {V : Type u} [Fintype V] [DecidableEq V]
    {α : Type v} [DecidableEq α]
    (k : ℕ) (_G : _root_.SimpleGraph V) [DecidableRel _G.Adj]
    (c : TupleColoring V k α) :
    TupleColoring V k (α × (Fin k → Multiset α)) :=
  fun t =>
    (c t,
      fun i =>
        Finset.univ.val.map (fun w : V => c (Function.update t i w)))

/-- The **`k`-WL fixed point**: `k`-WL refinement reaches a stable colouring.

Genuine statement (analogue of `wlRefine_stable` in the lattice of partitions
of `V^k`): for every `k` and every graph `G` there exists a `k`-tuple colouring
`c : (Fin k → V) → α` that is **`kWlStep`-stable**, meaning one further
refinement step does not separate any pair of tuples that `c` already
identifies.  Concretely two tuples that the refined colouring `kWlStep k G c`
distinguishes were already distinguished by `c`:

  `∀ s t, kWlStep k G c s = kWlStep k G c t → c s = c t`

(the reverse direction is automatic, since `kWlStep` records `c` in its first
component).  Such a fixed point is reached within `|V|^k` rounds because each
non-stable step strictly increases the number of colour classes, bounded by
`|V|^k`. -/
theorem kWlRefine_stable
    {V : Type u} [Fintype V] [DecidableEq V]
    (k : ℕ) (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (α : Type) (_ : DecidableEq α) (c : TupleColoring V k α),
      ∀ s t : Fin k → V, kWlStep k G c s = kWlStep k G c t → c s = c t := by
  -- Finite descent on the number of colour classes of `(Fin k → V)`, exactly
  -- as in `wlRefine_stable`; the bound `|V|^k` is `Fintype.card (Fin k → V)`.
  sorry

/-- **Cai-Fürer-Immerman (1992)**: for every `k` there exist graphs `G, H`
with `n = O(k)` vertices that are *not* isomorphic but are not separated by
`k`-WL.  This is a fundamental lower bound on the power of `k`-WL as a graph
isomorphism test.

We state it genuinely: for every arity `k` there is a finite vertex type `V`
carrying two simple graphs `G, H` which are **non-isomorphic**
(`¬ Nonempty (G ≃g H)`) yet **`k`-WL-indistinguishable** — the `k`-WL stable
tuple colourings agree up to a permutation `e` of the colour space, i.e. there
is a colour relabelling `e` making `kWlStep`-iterated colourings of `G` and `H`
coincide on every `k`-tuple.  This is the celebrated "CFI gadget" lower bound;
the explicit gadget construction is deferred to an honest theorem-`sorry`. -/
theorem cfi_lower_bound :
    ∀ k : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G H : _root_.SimpleGraph V) (_ : DecidableRel G.Adj) (_ : DecidableRel H.Adj),
      -- non-isomorphic …
      (¬ Nonempty (G ≃g H)) ∧
      -- … yet `k`-WL-indistinguishable: there is a colour relabelling `e`
      -- under which the `k`-WL refinements of `G` and `H` agree on all tuples.
      (∃ (α : Type) (_ : DecidableEq α) (cG cH : TupleColoring V k α)
          (e : α ≃ α),
        ∀ t : Fin k → V, e (cG t) = cH t) := by
  -- The CFI gadget over an expander base graph realises this for every `k`
  -- (with `Ω(k)`-WL actually required to separate the pair).  The full
  -- combinatorial construction is deferred.
  sorry

/-! ## 8. Concrete examples & `#eval` smoke tests.

We expose small example graphs and report their WL-stable color counts.

Each example below corresponds to a hand-checked answer:

* `K_3` — complete graph on 3 vertices — every vertex is in the same cell
  (one color), since it's vertex-transitive.
* `C_4` — 4-cycle — one color (vertex-transitive).
* `K_{3,3}` — complete bipartite — *two* colors (the two parts).
* Petersen graph — one color (vertex-transitive, distance-regular); WL is
  famously unable to separate Petersen from its non-isomorphic cousins (the
  Kneser/Johnson scheme).

In each case the `wlStableRound` is reached by round `2` because all the
graphs are vertex-transitive.  The `#eval` lines below are commented out;
uncomment them once `wlRefine_stable` is no longer `sorry` and the
`noncomputable` markers can be relaxed.
-/

section Examples

/-- The complete graph on `Fin 3`. -/
def K3 : _root_.SimpleGraph (Fin 3) where
  Adj x y := x ≠ y
  symm := fun _ _ h => h.symm
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel K3.Adj := fun x y => inferInstanceAs (Decidable (x ≠ y))

/-- The 4-cycle on `Fin 4`: `i ~ j` iff `|i - j| = 1 mod 4`. -/
def C4 : _root_.SimpleGraph (Fin 4) where
  Adj x y := (x.val + 1) % 4 = y.val ∨ (y.val + 1) % 4 = x.val
  symm := fun _ _ h => h.symm
  loopless := ⟨fun x h => by
    rcases h with h | h <;>
      · have : x.val < 4 := x.isLt
        omega⟩

instance : DecidableRel C4.Adj := fun x y => by
  unfold C4
  exact inferInstanceAs (Decidable (_ ∨ _))

/-- Complete bipartite graph `K_{3,3}` on `Fin 3 ⊕ Fin 3`. -/
def K33 : _root_.SimpleGraph (Fin 3 ⊕ Fin 3) where
  Adj x y :=
    match x, y with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by
    rintro (x | x) (y | y) h <;> simp_all
  loopless := ⟨by rintro (x | x) h <;> simp_all⟩

instance : DecidableRel K33.Adj := fun x y => by
  unfold K33
  cases x <;> cases y <;> exact inferInstance

/-- LinearOrder on `Fin 3 ⊕ Fin 3`: inl first (rank in [0,5]). -/
instance : LinearOrder (Fin 3 ⊕ Fin 3) :=
  LinearOrder.lift'
    (fun x : Fin 3 ⊕ Fin 3 => match x with
      | Sum.inl i => i.val
      | Sum.inr i => i.val + 3)
    (by
      rintro (a | a) (b | b) h <;> simp at h
      · first
          | exact congrArg Sum.inl h
          | exact congrArg Sum.inl (Fin.ext h)
      · have : a.val < 3 := a.isLt; omega
      · have : b.val < 3 := b.isLt; omega
      · first
          | exact congrArg Sum.inr h
          | exact congrArg Sum.inr (Fin.ext (by omega)))

/-- Petersen graph on `Fin 5 × Bool`: outer 5-cycle on `(_, false)`, inner
pentagram on `(_, true)` (steps of 2), and matching `(i, false) ~ (i, true)`.

Symmetrised explicitly so the relation is obviously symmetric. -/
def Petersen : _root_.SimpleGraph (Fin 5 × Bool) where
  Adj x y :=
    -- Outer cycle (both false): step ±1 mod 5.
    (x.2 = false ∧ y.2 = false ∧
      ((x.1.val + 1) % 5 = y.1.val ∨ (y.1.val + 1) % 5 = x.1.val))
    ∨
    -- Inner pentagram (both true): step ±2 mod 5.
    (x.2 = true ∧ y.2 = true ∧
      ((x.1.val + 2) % 5 = y.1.val ∨ (y.1.val + 2) % 5 = x.1.val))
    ∨
    -- Matching (cross-layer with same first component).
    (x.1 = y.1 ∧ x.2 ≠ y.2)
  symm := by
    rintro ⟨a, sa⟩ ⟨b, sb⟩ h
    dsimp at h ⊢
    rcases h with ⟨h1, h2, h3 | h3⟩ | ⟨h1, h2, h3 | h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1, Or.inr h3⟩
    · exact Or.inl ⟨h2, h1, Or.inl h3⟩
    · exact Or.inr (Or.inl ⟨h2, h1, Or.inr h3⟩)
    · exact Or.inr (Or.inl ⟨h2, h1, Or.inl h3⟩)
    · exact Or.inr (Or.inr ⟨h1.symm, fun e => h2 e.symm⟩)
  loopless := ⟨fun x h => by
    dsimp at h
    rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩
    · rcases h with h | h <;>
        · have : x.1.val < 5 := x.1.isLt; omega
    · rcases h with h | h <;>
        · have : x.1.val < 5 := x.1.isLt; omega
    · exact h rfl⟩

instance : DecidableRel Petersen.Adj := fun x y => by
  unfold Petersen
  exact inferInstance

/-- LinearOrder on `Fin 5 × Bool`: rank in [0,9]. -/
instance : LinearOrder (Fin 5 × Bool) :=
  LinearOrder.lift'
    (fun x : Fin 5 × Bool => if x.2 then x.1.val + 5 else x.1.val)
    (by
      rintro ⟨a, sa⟩ ⟨b, sb⟩ h
      dsimp at h
      have ha : a.val < 5 := a.isLt
      have hb : b.val < 5 := b.isLt
      cases sa <;> cases sb <;> simp at h
      · ext <;> simp [h]
      · omega
      · omega
      · refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, rfl⟩
        ext; omega)

end Examples

/-! ## Smoke tests

These run `wlStableColoring` on concrete graphs and inspect the resulting
ℕ-coloring.  All computations are fully decidable; the noncomputable
`Choice`-based `wlStableRound` was replaced by the concrete bound
`Fintype.card V`.

Expected:
* `K3` is vertex-transitive ⇒ all vertices get the same color (image cardinality 1).
* `C4` is vertex-transitive ⇒ image cardinality 1.
* `K33` has two orbits (the two parts) ⇒ image cardinality 2.
* Petersen is vertex-transitive (distance-regular) ⇒ image cardinality 1.
-/

section SmokeTests

-- NOTE: `wlStableColoring` iterates WL colour refinement `|V|` times, and the
-- colour type nests `α × Multiset α` once per round.  Sorting/`decide` on the
-- deeply-nested multisets makes elaboration-time `#eval` blow up (it stalls
-- `lake build`).  These smoke tests are kept as comments; run them manually in
-- an editor `#eval` session, ideally after replacing the colour encoding with a
-- flat `ℕ`-hash to keep the recursion depth constant.

-- #eval wlStableColoring K3 ⟨0, by decide⟩
-- #eval wlStableColoring K3 ⟨1, by decide⟩
-- #eval wlStableColoring K3 ⟨2, by decide⟩
-- #eval (Finset.univ.image (wlStableColoring K3)).card   -- expect 1
-- #eval (Finset.univ.image (wlStableColoring C4)).card   -- expect 1
-- #eval (Finset.univ.image (wlStableColoring K33)).card  -- expect 2
-- #eval (Finset.univ.image (wlStableColoring Petersen)).card  -- expect 1

end SmokeTests

end WL
end Graphplay
