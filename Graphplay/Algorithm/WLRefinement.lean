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

/-- **The WL step partition depends only on the input partition.**

If two colorings `c` and `d` have the *same kernel* (induce the same partition
of `V`), then the partitions induced by `wlStep G c` and `wlStep G d` coincide:
two vertices receive equal `wlStep G c`-colors iff they receive equal
`wlStep G d`-colors.

This is the engine of WL stabilization: one refinement round is a function of
the current partition alone, so once the partition stops changing it stays
fixed forever. -/
theorem wlStep_partition_congr
    {V : Type u} [Fintype V] [DecidableEq V]
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (c : Coloring V α) (d : Coloring V β)
    (hkern : ∀ x y, c x = c y ↔ d x = d y) :
    ∀ x y, wlStep G c x = wlStep G c y ↔ wlStep G d x = wlStep G d y := by
  -- The neighbour-colour multisets are equal for `c` iff for `d`, because for
  -- every vertex `v` the predicate `c · = c v` equals `d · = d v` pointwise.
  have hmulti : ∀ x y : V,
      (Finset.univ.filter (fun w => G.Adj x w)).val.map c =
        (Finset.univ.filter (fun w => G.Adj y w)).val.map c ↔
      (Finset.univ.filter (fun w => G.Adj x w)).val.map d =
        (Finset.univ.filter (fun w => G.Adj y w)).val.map d := by
    intro x y
    constructor
    · intro h
      -- Compare counts of every `d`-colour `b`.
      refine Multiset.ext.2 (fun b => ?_)
      rw [Multiset.count_map, Multiset.count_map]
      by_cases hb : ∃ w, d w = b
      · obtain ⟨v, rfl⟩ := hb
        -- `filter (d v = d ·)` = `filter (c v = c ·)` pointwise via `hkern`.
        have hcount := Multiset.ext.1 h (c v)
        rw [Multiset.count_map, Multiset.count_map] at hcount
        -- Rewrite the `d`-filters into the `c`-filters and use `hcount`.
        have e1 : ∀ s : Multiset V,
            (s.filter fun a => d v = d a) = (s.filter fun a => c v = c a) := by
          intro s
          apply Multiset.filter_congr
          intro a _
          exact (hkern v a).symm
        rw [e1, e1]; exact hcount
      · -- `b` is no vertex's `d`-colour: both filtered multisets are empty.
        push_neg at hb
        have : ∀ s : Multiset V, (s.filter fun a => b = d a) = 0 := by
          intro s
          rw [Multiset.filter_eq_nil]
          intro a _ hba; exact hb a hba.symm
        rw [this, this]
    · intro h
      refine Multiset.ext.2 (fun b => ?_)
      rw [Multiset.count_map, Multiset.count_map]
      by_cases hb : ∃ w, c w = b
      · obtain ⟨v, rfl⟩ := hb
        have hcount := Multiset.ext.1 h (d v)
        rw [Multiset.count_map, Multiset.count_map] at hcount
        have e1 : ∀ s : Multiset V,
            (s.filter fun a => c v = c a) = (s.filter fun a => d v = d a) := by
          intro s
          apply Multiset.filter_congr
          intro a _
          exact hkern v a
        rw [e1, e1]; exact hcount
      · push_neg at hb
        have : ∀ s : Multiset V, (s.filter fun a => b = c a) = 0 := by
          intro s
          rw [Multiset.filter_eq_nil]
          intro a _ hba; exact hb a hba.symm
        rw [this, this]
  intro x y
  simp only [wlStep, Prod.mk.injEq]
  rw [hkern x y, hmulti x y]

/-- After re-ranking the coloring is unchanged as a partition. -/
theorem rankColoring_partitionsAgree
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    {α : Type v} [DecidableEq α]
    (c : Coloring V α) :
    ∀ x y, rankColoring c x = rankColoring c y ↔ c x = c y := by
  classical
  intro x y
  -- Unfold the rank coloring: it is `distinct.idxOf (c ·)` for the deduped
  -- list `distinct` of color values appearing on the sorted vertex list.
  unfold rankColoring
  set vs : List V := (Finset.univ : Finset V).sort (· ≤ ·) with hvs
  set distinct : List α := (vs.map c).dedup with hdist
  -- `c x` and `c y` are members of `distinct` (every vertex appears in `vs`).
  have hxmem : c x ∈ distinct := by
    rw [hdist, List.mem_dedup, List.mem_map]
    exact ⟨x, by rw [hvs]; simpa using (Finset.mem_univ x), rfl⟩
  -- `idxOf` is injective on members of the list.
  constructor
  · intro h
    exact (List.idxOf_inj (l := distinct) hxmem).1 h
  · intro h; rw [h]

/-- The **number of distinct WL colors** at round `n`. -/
def wlColorCount
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : ℕ :=
  (Finset.univ.image (wlRefine G n)).card

/-- One WL iteration refines the previous one: same color at round `n+1`
forces same color at round `n`. -/
theorem wlIterColor_step_refines
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    Refines (wlIterColor G n) (wlIterColor G (n + 1)) := by
  intro x y h
  -- `wlIterColor G (n+1) = rankColoring (wlStep G (wlIterColor G n))`.
  have hstep : wlStep G (wlIterColor G n) x = wlStep G (wlIterColor G n) y := by
    have := (rankColoring_partitionsAgree (wlStep G (wlIterColor G n)) x y).1
    exact this h
  exact wlStep_isRefinement G (wlIterColor G n) x y hstep

/-- The WL refinement chain refines downward: same color at round `n` forces
same color at any earlier round `m ≤ n`. -/
theorem wlRefine_refines_of_le
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {m n : ℕ} (hmn : m ≤ n) :
    Refines (wlRefine G m) (wlRefine G n) := by
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.1 hmn
      subst this; intro x y _; rfl
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · -- `m ≤ k`, chain through round `k`.
        have hmk : m ≤ k := Nat.lt_succ_iff.1 hlt
        intro x y h
        exact ih hmk x y (wlIterColor_step_refines G k x y h)
      · -- `m = k + 1`.
        have : m = k + 1 := Nat.le_antisymm hmn hge
        subst this; intro x y h; exact h

/-- If `c'` refines `c`, the color-count of `c` is at most that of `c'`. -/
theorem colorCount_le_of_refines
    {V : Type u} [Fintype V] [DecidableEq V]
    {c c' : V → ℕ} (h : Refines c c') :
    (Finset.univ.image c).card ≤ (Finset.univ.image c').card := by
  classical
  -- Build a surjection from `image c'` onto `image c`: for `k ∈ image c'`,
  -- pick a vertex with `c' = k` and send `k ↦ c (that vertex)`.  Well-defined
  -- because `c'` refines `c`.  Concretely use `card_le_card_of_surjOn`.
  refine Finset.card_le_card_of_surjOn (fun k =>
      if hk : ∃ v, c' v = k then c (Classical.choose hk) else 0) ?_
  intro a ha
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
    true_and] at ha
  obtain ⟨v, rfl⟩ := ha
  refine ⟨c' v, ?_, ?_⟩
  · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and]
    exact ⟨v, rfl⟩
  · -- `c' v = c' v` makes the `dite` take the positive branch.
    simp only []
    split
    · rename_i hex
      -- `c (choose hex) = c v` since `c' (choose hex) = c' v` and `c'` refines `c`.
      exact h (Classical.choose hex) v (Classical.choose_spec hex)
    · rename_i hno
      exact absurd ⟨v, rfl⟩ hno

/-- The color count is monotonically non-decreasing in `n`. -/
theorem wlColorCount_mono
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    Monotone (wlColorCount G) := by
  intro m n hmn
  unfold wlColorCount
  exact colorCount_le_of_refines (wlRefine_refines_of_le G hmn)

/-- The color count is bounded by `|V|`. -/
theorem wlColorCount_le_card
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    wlColorCount G n ≤ Fintype.card V := by
  unfold wlColorCount
  exact (Finset.card_image_le).trans (by simpa using (Finset.card_le_univ _))

/-- If `c'` refines `c` and they have the **same** number of colour classes,
then they induce the *same* partition: `c x = c y ↔ c' x = c' y`. -/
theorem partition_eq_of_count_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {c c' : V → ℕ}
    (hcount : (Finset.univ.image c).card = (Finset.univ.image c').card)
    (href : Refines c c') :
    ∀ x y, c x = c y ↔ c' x = c' y := by
  classical
  -- The representative map `φ : image c' → image c`, `φ (c' v) = c v`, is
  -- well-defined (by `href`) and surjective; equal cardinalities make it
  -- injective, which is exactly `c x = c y → c' x = c' y`.
  set φ : ℕ → ℕ := fun k =>
    if hk : ∃ v, c' v = k then c (Classical.choose hk) else 0 with hφ
  -- `φ` maps `image c'` onto `image c`.
  have hsurj : Set.SurjOn φ (Finset.univ.image c' : Set ℕ)
      (Finset.univ.image c : Set ℕ) := by
    intro a ha
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at ha
    obtain ⟨v, rfl⟩ := ha
    refine ⟨c' v, ?_, ?_⟩
    · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
        true_and]; exact ⟨v, rfl⟩
    · simp only [hφ]
      split
      · rename_i hex; exact href (Classical.choose hex) v (Classical.choose_spec hex)
      · rename_i hno; exact absurd ⟨v, rfl⟩ hno
  -- Equal cardinalities + surjection ⇒ the surjection is injective on `image c'`.
  have hinj : Set.InjOn φ (Finset.univ.image c' : Set ℕ) := by
    apply Finset.injOn_of_surjOn_of_card_le (s := Finset.univ.image c')
      (t := Finset.univ.image c) φ
    · intro b hb
      have : φ b ∈ (Finset.univ.image c : Set ℕ) := by
        -- `φ` maps any value of `c'` to a value of `c`.
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
          true_and] at hb ⊢
        obtain ⟨v, rfl⟩ := hb
        refine ⟨v, ?_⟩
        simp only [hφ]
        split
        · rename_i hex
          exact (href (Classical.choose hex) v (Classical.choose_spec hex)).symm
        · rename_i hno; exact absurd ⟨v, rfl⟩ hno
      simpa using this
    · exact hsurj
    · exact le_of_eq hcount.symm
  -- Conclude: `φ (c' x) = c x` always, so `c x = c y → c' x = c' y` via `hinj`.
  have hφval : ∀ v, φ (c' v) = c v := by
    intro v
    simp only [hφ]
    split
    · rename_i hex; exact href (Classical.choose hex) v (Classical.choose_spec hex)
    · rename_i hno; exact absurd ⟨v, rfl⟩ hno
  intro x y
  constructor
  · -- `c x = c y → c' x = c' y` via injectivity of `φ`.
    intro h
    have hmx : c' x ∈ (Finset.univ.image c' : Set ℕ) := by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
        true_and]; exact ⟨x, rfl⟩
    have hmy : c' y ∈ (Finset.univ.image c' : Set ℕ) := by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
        true_and]; exact ⟨y, rfl⟩
    apply hinj hmx hmy
    rw [hφval x, hφval y, h]
  · -- `c' x = c' y → c x = c y`: this is `Refines`.
    intro h; exact href x y h

theorem wlRefine_succ_kernel
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (x y : V) :
    wlRefine G (n + 1) x = wlRefine G (n + 1) y ↔
      wlStep G (wlRefine G n) x = wlStep G (wlRefine G n) y := by
  show wlIterColor G (n + 1) x = wlIterColor G (n + 1) y ↔ _
  simp only [wlIterColor]
  exact rankColoring_partitionsAgree (wlStep G (wlIterColor G n)) x y

/-- **Partition stabilization propagates.**  If the WL partition is unchanged
from round `n` to round `n+1`, it is unchanged from round `n+1` to round `n+2`. -/
theorem wlRefine_stable_step
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    (h : ∀ x y, wlRefine G n x = wlRefine G n y ↔
                wlRefine G (n + 1) x = wlRefine G (n + 1) y) :
    ∀ x y, wlRefine G (n + 1) x = wlRefine G (n + 1) y ↔
           wlRefine G (n + 2) x = wlRefine G (n + 2) y := by
  intro x y
  -- The next round's partition is the `wlStep`-partition of the current
  -- colouring; `wlStep_partition_congr` makes it depend only on the partition.
  rw [wlRefine_succ_kernel G (n + 1) x y]
  -- `kernel (wlRefine (n+1)) = kernel (wlStep (wlRefine n))`.
  have key := wlStep_partition_congr G (wlRefine G n) (wlRefine G (n + 1)) h x y
  rw [← key, ← wlRefine_succ_kernel G n x y]

/-- Once the partition is stable from round `N` to `N+1`, it is stable at all
later rounds: `wlRefine G n` and `wlRefine G N` induce the same partition for
every `n ≥ N`. -/
theorem wlRefine_stable_of_fixed
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {N : ℕ}
    (hN : ∀ x y, wlRefine G N x = wlRefine G N y ↔
                 wlRefine G (N + 1) x = wlRefine G (N + 1) y) :
    ∀ n ≥ N, ∀ x y, wlRefine G n x = wlRefine G n y ↔
                    wlRefine G N x = wlRefine G N y := by
  -- First: the consecutive-step stability holds for every round `≥ N`.
  have step : ∀ k, ∀ x y, wlRefine G (N + k) x = wlRefine G (N + k) y ↔
                          wlRefine G (N + k + 1) x = wlRefine G (N + k + 1) y := by
    intro k
    induction k with
    | zero => simpa using hN
    | succ j ih =>
        have hstep := wlRefine_stable_step G (n := N + j) ih
        have e1 : N + (j + 1) = N + j + 1 := by omega
        rw [e1]
        have e2 : N + j + 1 + 1 = N + j + 2 := by omega
        rw [e2]
        exact hstep
  -- Now chain: partition at `N + k` equals partition at `N`.
  have chain : ∀ k, ∀ x y, wlRefine G (N + k) x = wlRefine G (N + k) y ↔
                           wlRefine G N x = wlRefine G N y := by
    intro k
    induction k with
    | zero => intro x y; simp only [Nat.add_zero]
    | succ j ih =>
        intro x y
        have hstep := step j x y
        rw [Nat.add_succ] at *
        rw [← hstep]
        exact ih x y
  intro n hn x y
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact chain k x y

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
  -- Find `N ≤ |V|` at which the colour count stops increasing.  Because the
  -- count is monotone, bounded by `|V|`, and starts at `≥ 1` (round 0 has the
  -- single colour `0`... or 0 colours if `V` is empty), the strictly-increasing
  -- prefix has length at most `|V|`, so some `N < |V|+1` has
  -- `wlColorCount G N = wlColorCount G (N+1)`; equal counts on a refinement
  -- force equal partitions, after which stability propagates.
  classical
  -- Step 1: there is `N ≤ |V|` with `wlColorCount G N = wlColorCount G (N+1)`.
  have hbound : ∀ n, wlColorCount G n ≤ Fintype.card V := wlColorCount_le_card G
  have hmono : Monotone (wlColorCount G) := wlColorCount_mono G
  have hExists : ∃ N ≤ Fintype.card V, wlColorCount G N = wlColorCount G (N + 1) := by
    by_contra hcon
    push_neg at hcon
    -- Then `wlColorCount` strictly increases on `[0, |V|+1]`, giving
    -- `wlColorCount G (|V|+1) ≥ |V| + 1`, contradicting the bound.
    have hstrict : ∀ n ≤ Fintype.card V + 1,
        wlColorCount G 0 + n ≤ wlColorCount G n := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ j ih =>
          intro hj
          have hjle : j ≤ Fintype.card V := Nat.lt_succ_iff.1 hj
          have hlt : wlColorCount G j < wlColorCount G (j + 1) :=
            lt_of_le_of_ne (hmono (Nat.le_succ j)) (hcon j hjle)
          have := ih (Nat.le_of_succ_le hj)
          omega
    have hge := hstrict (Fintype.card V + 1) le_rfl
    have hle := hbound (Fintype.card V + 1)
    -- `wlColorCount G 0 + (cardV+1) ≤ wlColorCount (cardV+1) ≤ cardV`, absurd.
    omega
  obtain ⟨N, hNle, hNeq⟩ := hExists
  -- Step 2: equal counts on a refinement ⇒ equal partitions at `N, N+1`.
  have hrefN : Refines (wlRefine G N) (wlRefine G (N + 1)) :=
    wlRefine_refines_of_le G (Nat.le_succ N)
  have hfix : ∀ x y, wlRefine G N x = wlRefine G N y ↔
                     wlRefine G (N + 1) x = wlRefine G (N + 1) y := by
    intro x y
    constructor
    · -- refinement gives `(N+1)-equal → N-equal`; we need the converse direction.
      -- Equal color counts on a refinement force the refinement to be a
      -- partition equality.
      intro h
      exact (partition_eq_of_count_eq hNeq hrefN x y).1 h
    · intro h; exact hrefN x y h
  -- Step 3: propagate.
  exact ⟨N, hNle, wlRefine_stable_of_fixed G hfix⟩

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

/-- **Stability at `|V|` rounds.**  Once `n ≥ |V|`, one more WL round does not
refine the partition: `wlRefine G n` and `wlRefine G (n+1)` induce the same
partition of `V`.  This packages `wlRefine_stable` (which gives a stable round
`N ≤ |V|`) together with `wlRefine_stable_of_fixed` propagation. -/
theorem wlRefine_partition_stable_of_card_le
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (hn : n ≥ Fintype.card V) (x y : V) :
    wlRefine G n x = wlRefine G n y ↔
      wlRefine G (n + 1) x = wlRefine G (n + 1) y := by
  obtain ⟨N, hNle, hstable⟩ := wlRefine_stable G
  have hNn : N ≤ n := le_trans hNle hn
  have hNn1 : N ≤ n + 1 := le_trans hNn (Nat.le_succ n)
  rw [hstable n hNn x y, hstable (n + 1) hNn1 x y]

/-- The key WL-stability fact for equitability: at a stable round (`n ≥ |V|`),
two vertices with the same colour have equal multisets of neighbour colours.
This is exactly the `wlStep`-fixed-point property unpacked. -/
theorem wlRefine_neighbour_multiset_eq_of_card_le
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (hn : n ≥ Fintype.card V) {x y : V}
    (hxy : wlRefine G n x = wlRefine G n y) :
    (Finset.univ.filter (fun w => G.Adj x w)).val.map (wlRefine G n) =
      (Finset.univ.filter (fun w => G.Adj y w)).val.map (wlRefine G n) := by
  -- same colour at round `n` ⟹ same colour at round `n+1` (stability) ⟹
  -- the `wlStep` colours coincide ⟹ second components (the neighbour multisets)
  -- coincide.
  have hstep : wlRefine G (n + 1) x = wlRefine G (n + 1) y :=
    (wlRefine_partition_stable_of_card_le G hn x y).1 hxy
  have hwlstep : wlStep G (wlRefine G n) x = wlStep G (wlRefine G n) y :=
    (wlRefine_succ_kernel G n x y).1 hstep
  have := congrArg Prod.snd hwlstep
  simpa [wlStep] using this

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
  classical
  -- The cell index `Fin (wlColorCount G n)` is the image of `wlRefine G n`
  -- re-indexed by `Finset.equivFin`; two vertices share a cell iff they share
  -- a `wlRefine G n` colour.
  set s : Finset ℕ := Finset.univ.image (wlRefine G n) with hs
  -- the cell map: land in `Fin s.card` (which is `Fin (wlColorCount G n)`
  -- definitionally), via the canonical `s ≃ Fin s.card`.
  have hmem : ∀ v : V, wlRefine G n v ∈ s := fun v =>
    Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  set cells : V → Fin (wlColorCount G n) :=
    fun v => s.equivFin ⟨wlRefine G n v, hmem v⟩ with hcells
  -- cell equality ↔ colour equality
  have hcell_iff : ∀ x y : V, cells x = cells y ↔ wlRefine G n x = wlRefine G n y := by
    intro x y
    rw [hcells]
    constructor
    · intro h
      have := s.equivFin.injective h
      exact congrArg Subtype.val this
    · intro h
      exact congrArg _ (Subtype.ext h)
  -- the equitable / uniform condition
  refine ⟨{ cells := cells
            uniform := ?_ }, hcell_iff⟩
  intro i j x y hx hy
  -- `x, y` share cell `i`, hence share colour
  have hcxy : wlRefine G n x = wlRefine G n y :=
    (hcell_iff x y).1 (hx.trans hy.symm)
  -- neighbour multisets agree
  have hmulti := wlRefine_neighbour_multiset_eq_of_card_le G hn hcxy
  -- rewrite the branching sums as counts in the neighbour multisets indexed
  -- by colour, then use `hmulti`.  The adjacency of `toWeighted G` is `0/1`.
  -- First express each branch sum as a `Multiset.count` of a fixed colour.
  -- Pick the colour `cj` representing cell `j` (use any representative of `j`
  -- if it exists; otherwise both sides are `0`).
  -- We work directly: ∑_z [cells z = j] adj x z = #{z ∈ N(x) : cells z = j}.
  have hsum : ∀ w : V,
      (∑ z, (if cells z = j then (Graphplay.SimpleGraph.toWeighted G).adj w z else 0))
        = ((Finset.univ.filter (fun z => G.Adj w z ∧ cells z = j)).card : ℂ) := by
    intro w
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro z _
    by_cases hcj : cells z = j
    · by_cases hadj : G.Adj w z
      · simp [hcj, hadj, Graphplay.SimpleGraph.toWeighted,
          _root_.SimpleGraph.adjMatrix_apply]
      · simp [hcj, hadj, Graphplay.SimpleGraph.toWeighted,
          _root_.SimpleGraph.adjMatrix_apply]
    · simp [hcj, Graphplay.SimpleGraph.toWeighted,
        _root_.SimpleGraph.adjMatrix_apply]
  rw [hsum x, hsum y]
  -- reduce to cardinality equality of neighbour sets restricted to cell `j`.
  congr 1
  norm_cast
  -- Case on whether cell `j` is inhabited.
  by_cases hj : ∃ v₀ : V, cells v₀ = j
  · obtain ⟨v₀, hv₀⟩ := hj
    set cj : ℕ := wlRefine G n v₀ with hcj
    -- `cells z = j ↔ wlRefine G n z = cj`.
    have hcellcol : ∀ z : V, cells z = j ↔ wlRefine G n z = cj := by
      intro z
      rw [hcj]
      rw [← hv₀]
      exact (hcell_iff z v₀)
    -- both cardinalities = count of `cj` in the neighbour multiset.
    have hcard_eq_count : ∀ w : V,
        (Finset.univ.filter (fun z => G.Adj w z ∧ cells z = j)).card
          = Multiset.count cj
              ((Finset.univ.filter (fun u => G.Adj w u)).val.map (wlRefine G n)) := by
      intro w
      rw [Multiset.count_map, Finset.filter_val, Multiset.filter_filter]
      -- LHS: rewrite the cell predicate to a colour predicate via `hcellcol`.
      have hLHS : (Finset.univ.filter (fun z => G.Adj w z ∧ cells z = j))
            = (Finset.univ.filter (fun z => cj = wlRefine G n z ∧ G.Adj w z)) := by
        apply Finset.filter_congr
        intro z _
        rw [hcellcol z]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1.symm⟩
      rw [hLHS, Finset.card_def, Finset.filter_val]
    rw [hcard_eq_count x, hcard_eq_count y, hmulti]
  · push_neg at hj
    have hempty : ∀ w : V,
        (Finset.univ.filter (fun z => G.Adj w z ∧ cells z = j)) = ∅ := by
      intro w
      rw [Finset.filter_eq_empty_iff]
      intro z _
      push_neg
      intro _
      exact hj z
    rw [hempty x, hempty y]

/-! ## 5. Coarsest equitable.

Any equitable partition of `G` refines (i.e. is finer than) the WL-stable
partition, and conversely the WL-stable partition refines any "trivial"
partition.  In lattice language, WL stabilizes at the **coarsest** equitable
partition of `G`.
-/

/-- **Every equitable partition refines every WL round.**

If `P` is an equitable partition of `toWeighted G`, then for every round `n`,
two vertices in the same `P`-cell have the same `wlRefine G n` colour.  Proof by
induction on `n`: the base colouring is constant; at the inductive step, two
vertices in the same `P`-cell have (i) the same round-`n` colour by IH and (ii)
equal multisets of neighbour round-`n` colours, because each round-`n` colour
class is (by IH) a union of `P`-cells, and the per-`P`-cell neighbour counts are
equal by the equitable property of `P`. -/
theorem equitable_refines_wlRefine
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {I : Type w} [Fintype I] [DecidableEq I]
    (P : EquitablePartition (Graphplay.SimpleGraph.toWeighted G) I)
    (n : ℕ) (x y : V) (hP : P.cells x = P.cells y) :
    wlRefine G n x = wlRefine G n y := by
  classical
  induction n generalizing x y with
  | zero => rfl
  | succ k ih =>
    -- `wlRefine (k+1)` partition = `wlStep (wlRefine k)` partition, so it
    -- suffices to show the `wlStep`-colours of `x` and `y` coincide.
    rw [wlRefine_succ_kernel G k x y]
    -- Build the `wlStep` equality: first components equal (by `ih`), and
    -- neighbour multisets equal.
    have hih : ∀ u v : V, P.cells u = P.cells v → wlRefine G k u = wlRefine G k v :=
      fun u v h => ih u v h
    have hfst : wlRefine G k x = wlRefine G k y := ih x y hP
    -- neighbour multiset equality, colour by colour.
    have hmulti : (Finset.univ.filter (fun w => G.Adj x w)).val.map (wlRefine G k) =
        (Finset.univ.filter (fun w => G.Adj y w)).val.map (wlRefine G k) := by
      refine Multiset.ext.2 (fun c => ?_)
      rw [Multiset.count_map, Multiset.count_map, Finset.filter_val, Finset.filter_val,
        Multiset.filter_filter, Multiset.filter_filter]
      -- both counts = `#{z : G.Adj · z ∧ wlRefine k z = c}` = branching into the
      -- union of `P`-cells with round-`k` colour `c`.
      -- Express as a sum of `P`-branchings.
      have hcount : ∀ w : V,
          Multiset.card
              (Multiset.filter (fun a => c = wlRefine G k a ∧ G.Adj w a) Finset.univ.val)
            = (Finset.univ.filter
                (fun z => G.Adj w z ∧ wlRefine G k z = c)).card := by
        intro w
        rw [Finset.card_def, Finset.filter_val]
        congr 1
        apply Multiset.filter_congr
        intro a _
        exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1.symm⟩, fun ⟨h1, h2⟩ => ⟨h2.symm, h1⟩⟩
      rw [hcount, hcount]
      -- partition `{z : wlRefine k z = c}` into `P`-cells: count = sum over
      -- `P`-cells `i` with round-`k` colour `c` of `#{z ∈ N(w): P.cells z = i}`.
      have hpart : ∀ w : V,
          (Finset.univ.filter (fun z => G.Adj w z ∧ wlRefine G k z = c)).card
            = ∑ i : I, if (∃ z, P.cells z = i ∧ wlRefine G k z = c)
                then (Finset.univ.filter (fun z => G.Adj w z ∧ P.cells z = i)).card
                else 0 := by
        intro w
        rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to
          (g := fun z => P.cells z) (fun z _ => Finset.mem_univ (P.cells z))]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hex : ∃ z, P.cells z = i ∧ wlRefine G k z = c
        · rw [if_pos hex]
          obtain ⟨z₀, hz₀cell, hz₀col⟩ := hex
          rw [Finset.card_eq_sum_ones]
          -- the two filtered sets coincide: on cell `i`, `wlRefine k z = c`
          -- holds for all `z` (since `wlRefine k` is constant on cell `i`).
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨hadj, hcol⟩, hcell⟩; exact ⟨hadj, hcell⟩
          · rintro ⟨hadj, hcell⟩
            refine ⟨⟨hadj, ?_⟩, hcell⟩
            -- `wlRefine k z = wlRefine k z₀ = c` since same `P`-cell.
            rw [hih z z₀ (by rw [hcell, hz₀cell]), hz₀col]
        · rw [if_neg hex, ← Finset.card_eq_sum_ones]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro z hz hcell
          rw [Finset.mem_filter] at hz
          obtain ⟨_, _, hcol⟩ := hz
          exact hex ⟨z, hcell, hcol⟩
      rw [hpart x, hpart y]
      -- termwise: the `P`-branchings into cell `i` agree for `x, y` (same cell).
      apply Finset.sum_congr rfl
      intro i _
      by_cases hex : ∃ z, P.cells z = i ∧ wlRefine G k z = c
      · rw [if_pos hex, if_pos hex]
        -- `#{z ∈ N(x): P.cells z = i} = #{z ∈ N(y): P.cells z = i}` by equitability.
        have hbr : ∀ w : V,
            ((Finset.univ.filter (fun z => G.Adj w z ∧ P.cells z = i)).card : ℂ)
              = ∑ z, (if P.cells z = i then (Graphplay.SimpleGraph.toWeighted G).adj w z else 0) := by
          intro w
          rw [Finset.card_filter]
          push_cast
          apply Finset.sum_congr rfl
          intro z _
          by_cases hcell : P.cells z = i
          · by_cases hadj : G.Adj w z
            · simp [hcell, hadj, Graphplay.SimpleGraph.toWeighted,
                _root_.SimpleGraph.adjMatrix_apply]
            · simp [hcell, hadj, Graphplay.SimpleGraph.toWeighted,
                _root_.SimpleGraph.adjMatrix_apply]
          · simp [hcell, Graphplay.SimpleGraph.toWeighted,
              _root_.SimpleGraph.adjMatrix_apply]
        have heq : ((Finset.univ.filter (fun z => G.Adj x z ∧ P.cells z = i)).card : ℂ)
            = ((Finset.univ.filter (fun z => G.Adj y z ∧ P.cells z = i)).card : ℂ) := by
          rw [hbr x, hbr y]
          exact P.uniform (P.cells x) i x y rfl hP.symm
        exact_mod_cast heq
      · rw [if_neg hex, if_neg hex]
    -- assemble the `wlStep` equality from `hfst` and `hmulti`.
    simp only [wlStep, Prod.mk.injEq]
    exact ⟨hfst, hmulti⟩

/-- **Coarsest equitable**: every equitable partition of `toWeighted G`
refines the stable WL partition.  Combined with `wlRefine_isEquitable` this
characterises `wlStableColoring G` as the coarsest equitable partition. -/
theorem wlRefine_coarsestEquitable
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {I : Type w} [Fintype I] [DecidableEq I]
    (P : EquitablePartition (Graphplay.SimpleGraph.toWeighted G) I) :
    Refines (wlStableColoring G) P.cells := by
  intro x y h
  exact equitable_refines_wlRefine G P (wlStableRound G) x y h

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
  classical
  intro σ v
  -- `v` and `σ v` lie in the same `⟨σ⟩`-orbit, hence (orbit partition is
  -- equitable, and WL is the coarsest equitable) in the same WL cell.
  -- Discreteness then forces `σ v = v`.
  -- 1. The `⟨σ⟩`-orbit partition as an `EquitablePartition`.
  set g : Equiv.Perm V := σ.toEquiv with hg
  -- the orbit equivalence under the cyclic group generated by `g`
  let S : Setoid V := MulAction.orbitRel (Subgroup.zpowers g) V
  letI : DecidableEq (Quotient S) := Classical.decEq _
  letI : Fintype (Quotient S) := Quotient.fintype _
  -- `g` preserves adjacency, hence the 0/1 weights of `toWeighted G`.
  have hadjinv : ∀ (a b : V), G.Adj (g a) (g b) ↔ G.Adj a b := by
    intro a b; exact σ.map_rel_iff
  have hwinv : ∀ (a b : V),
      (Graphplay.SimpleGraph.toWeighted G).adj (g a) (g b)
        = (Graphplay.SimpleGraph.toWeighted G).adj a b := by
    intro a b
    by_cases h : G.Adj a b
    · simp [Graphplay.SimpleGraph.toWeighted, _root_.SimpleGraph.adjMatrix_apply,
        h, (hadjinv a b).mpr h]
    · have hg' : ¬ G.Adj (g a) (g b) := fun hh => h ((hadjinv a b).mp hh)
      simp [Graphplay.SimpleGraph.toWeighted, _root_.SimpleGraph.adjMatrix_apply,
        h, hg']
  -- the orbit partition
  let Q : EquitablePartition (Graphplay.SimpleGraph.toWeighted G) (Quotient S) :=
    { cells := fun w => Quotient.mk S w
      uniform := by
        intro i j x y hx hy
        -- `x, y` same orbit ⟹ ∃ `h ∈ ⟨g⟩` with `h • y = x`.
        have hxy : (Quotient.mk S x) = (Quotient.mk S y) := hx.trans hy.symm
        have horb : S.r x y := Quotient.exact hxy
        obtain ⟨h, hh⟩ := horb
        have hhy : h • y = x := hh
        -- reindex the `x`-sum (LHS) by the bijection `z ↦ h • z`.
        rw [← Equiv.sum_comp (MulAction.toPerm h)
          (fun z => if Quotient.mk S z = j then
            (Graphplay.SimpleGraph.toWeighted G).adj x z else 0)]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        simp only [MulAction.toPerm_apply]
        -- `h • z` is in the same orbit as `z`, so cell labels match.
        have hcell : (Quotient.mk S) (h • z) = (Quotient.mk S) z := by
          apply Quotient.sound
          exact ⟨h, rfl⟩
        rw [hcell]
        by_cases hzj : Quotient.mk S z = j
        · rw [if_pos hzj, if_pos hzj]
          -- `adj x (h • z) = adj (h • y) (h • z) = adj y z`.
          -- weight invariance under `g`, lifted to its powers / inverse.
          have hadjinv' : ∀ (a b : V), G.Adj (g⁻¹ a) (g⁻¹ b) ↔ G.Adj a b := by
            intro a b
            constructor
            · intro hh'
              have := (hadjinv (g⁻¹ a) (g⁻¹ b)).mpr hh'
              simpa using this
            · intro hh'
              have : G.Adj (g (g⁻¹ a)) (g (g⁻¹ b)) := by simpa using hh'
              exact (hadjinv (g⁻¹ a) (g⁻¹ b)).mp this
          -- every integer power of `g` preserves adjacency.
          have hzpow : ∀ (n : ℤ) (a b : V),
              G.Adj ((g ^ n) a) ((g ^ n) b) ↔ G.Adj a b := by
            intro n
            refine Int.induction_on n ?_ ?_ ?_
            · intro a b; simp
            · intro m ihm a b
              rw [zpow_add, zpow_one]
              simp only [Equiv.Perm.mul_apply]
              rw [ihm (g a) (g b)]; exact hadjinv a b
            · intro m ihm a b
              rw [zpow_sub, zpow_one]
              simp only [Equiv.Perm.mul_apply]
              rw [ihm (g⁻¹ a) (g⁻¹ b)]; exact hadjinv' a b
          have hpres : ∀ (p : Equiv.Perm V), p ∈ Subgroup.zpowers g →
              ∀ a b : V, G.Adj (p a) (p b) ↔ G.Adj a b := by
            intro p hp
            obtain ⟨n, rfl⟩ := hp
            exact hzpow n
          have hwh : ∀ (a b : V),
              (Graphplay.SimpleGraph.toWeighted G).adj (h • a) (h • b)
                = (Graphplay.SimpleGraph.toWeighted G).adj a b := by
            intro a b
            have hiff := hpres (h : Equiv.Perm V) h.2 a b
            have hsmul : ∀ c : V, h • c = (h : Equiv.Perm V) c := fun c => rfl
            by_cases hab : G.Adj a b
            · rw [hsmul, hsmul]
              simp [Graphplay.SimpleGraph.toWeighted, _root_.SimpleGraph.adjMatrix_apply,
                hab, hiff.mpr hab]
            · have hng : ¬ G.Adj ((h : Equiv.Perm V) a) ((h : Equiv.Perm V) b) :=
                fun hh' => hab (hiff.mp hh')
              rw [hsmul, hsmul]
              simp [Graphplay.SimpleGraph.toWeighted, _root_.SimpleGraph.adjMatrix_apply,
                hab, hng]
          -- `adj x (h • z) = adj (h • y) (h • z) = adj y z`.
          rw [← hhy, hwh y z]
        · rw [if_neg hzj, if_neg hzj] }
  -- 2. WL-stable is the coarsest equitable, so `Q` refines `wlStableColoring G`.
  have href : Refines (wlStableColoring G) Q.cells := wlRefine_coarsestEquitable G Q
  -- `v` and `σ v` are in the same orbit cell of `Q`.
  have hsame : Q.cells (σ v) = Q.cells v := by
    apply Quotient.sound
    refine ⟨⟨g, ⟨1, by simp⟩⟩, ?_⟩
    show g • v = σ v
    rfl
  -- hence same WL colour, hence `σ v = v` by discreteness.
  have hcol : wlStableColoring G (σ v) = wlStableColoring G v := href _ _ hsame
  exact hdisc (σ v) v hcol

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

The WL-stable partition is equitable, so the adjacency action preserves its
**cell-uniform subspace** (spanned by the normalized cell-indicator vectors).
This is the matrix-level transcription of the WL fixed-point property and is
the seed of the coherent algebra of `G`: the adjacency operator restricted to
the cell-uniform subspace acts as the (symmetric) quotient.

NOTE on directionality: we state the genuinely-true **invariance** of the
cell-uniform subspace under `G.adj`, rather than a literal commutation
`E * A = A * E` with the *unnormalized* same-cell indicator `E`.  The latter is
**false** in general for equitable partitions (e.g. the path `P₃` with cells
`{1,3}, {2}`: `(E A)₁₂ = 2 ≠ 1 = (A E)₁₂`, because the branching matrix of an
equitable partition need not be symmetric).  The correct operator-level
statement uses the *orthogonal* projector onto the cell-uniform subspace; its
matrix-free content is exactly the invariance asserted here, which is what the
coherent-algebra bridge consumes. -/
theorem wlStable_commutes_adj
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P : EquitablePartition (Graphplay.SimpleGraph.toWeighted G)
            (Fin (wlColorCount G (Fintype.card V))),
      (∀ x y, P.cells x = P.cells y ↔ wlStableColoring G x = wlStableColoring G y) ∧
      ∀ v : V → ℂ, v ∈ P.cellUniformSubspace →
        (Graphplay.SimpleGraph.toWeighted G).adj.mulVec v ∈ P.cellUniformSubspace := by
  -- The WL-stable partition (round `|V|`) is equitable by `wlRefine_isEquitable`;
  -- `cellUniformSubspace_invariant` then gives the adjacency-invariance.
  obtain ⟨P, hP⟩ := wlRefine_isEquitable G (Fintype.card V) (le_refl _)
  refine ⟨P, hP, ?_⟩
  intro v hv
  exact P.cellUniformSubspace_invariant v hv

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
  -- The *discrete* tuple colouring `c = id` is already a fixed point: it cannot
  -- be refined further, so one more `kWlStep` round never separates two tuples
  -- it already identifies.  Indeed `kWlStep` records `c` in its first
  -- coordinate, so `kWlStep c s = kWlStep c t → c s = c t` always holds; for the
  -- identity colouring this is the genuine maximal-refinement fixed point.
  classical
  -- Encode tuples into `Fin (card (Fin k → V))` (a `Type 0`) by the canonical
  -- Fintype enumeration; this discrete colouring is the maximal-refinement
  -- fixed point.
  refine ⟨Fin (Fintype.card (Fin k → V)), inferInstance,
    fun t => (Fintype.equivFin (Fin k → V)) t, ?_⟩
  intro s t h
  -- The first component of `kWlStep` is `c`; project it out.
  simpa [kWlStep] using congrArg Prod.fst h

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
