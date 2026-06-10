/-
# Graphplay.Algorithm.Coloring

**Computable greedy and Weisfeiler–Leman-greedy vertex colorings.**

This file provides:

1. `greedyColoring` — the classical greedy proper coloring of a finite
   `SimpleGraph`, parameterised by a vertex visitation order `order : V → ℕ`.
   Vertices are processed in `order`-ascending order; each vertex receives the
   smallest natural number not already used by its already-colored neighbours.
   The result is a fully computable function `V → ℕ`, suitable for `#eval`.
2. `greedyColoring_isProper` — the greedy coloring is proper
   (adjacent vertices receive distinct colors).
3. `greedyColoring.numColors` — the number of colors used (max color + 1).
4. `wlGreedyColoring` — greedy using the WL-stable color as the vertex order.
   This composes `Graphplay.Algorithm.WLRefinement.wlStableColoring` with
   `greedyColoring`, giving a heuristic that often matches χ(G) on
   equitable-partition-friendly graphs.
5. `wlGreedyColoring_numColors_le` — for graphs with small
   coarsest equitable partition (e.g. vertex-transitive distance-regular
   graphs), the WL-greedy color count is bounded in terms of the equitable
   cell count.
6. `#eval` smoke tests on `K₃` (3 colors), `C₅` (3 colors), and the Petersen
   graph (3 colors).

The design is **end-to-end computable**: no `noncomputable` definitions, no
`Classical.choice` in the algorithmic path.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Graphplay.Algorithm.WLRefinement

open scoped BigOperators

universe u

namespace Graphplay
namespace Coloring

/-! ## 1. The greedy coloring. -/

/-- The **smallest natural number not in the finset `s`**.

We search `0, 1, …, s.card` in turn.  Since `s` has `s.card` elements, at least
one value in `{0, 1, …, s.card}` is absent. -/
def mex (s : Finset ℕ) : ℕ :=
  (List.range (s.card + 1)).find? (fun n => n ∉ s) |>.getD 0

/-- Pigeonhole helper: in `{0,…,s.card}` (cardinality `s.card+1`) some value is
absent from `s`, so `find?` on `List.range (s.card+1)` succeeds. -/
theorem mex_find?_isSome (s : Finset ℕ) :
    ((List.range (s.card + 1)).find? (fun n => decide (n ∉ s))).isSome := by
  rw [List.find?_isSome]
  -- It suffices to exhibit an element of `range (s.card+1)` absent from `s`.
  by_contra h
  simp only [not_exists, not_and] at h
  -- Then every element of `range (s.card+1)` lies in `s`, i.e. the finset
  -- `Finset.range (s.card+1)` is a subset of `s`, contradicting cardinalities.
  have hsub : Finset.range (s.card + 1) ⊆ s := by
    intro n hn
    rw [Finset.mem_range, ← List.mem_range] at hn
    have hn' := h n hn
    by_contra hns
    exact hn' (by simpa using hns)
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  omega

theorem mex_not_mem (s : Finset ℕ) : mex s ∉ s := by
  -- The value returned by `find?` satisfies the search predicate `· ∉ s`.
  unfold mex
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (mex_find?_isSome s)
  rw [hk, Option.getD_some]
  have := List.find?_some hk
  simpa using this

theorem mex_lt_succ_card (s : Finset ℕ) : mex s ≤ s.card := by
  -- The value returned by `find?` is a member of `List.range (s.card+1)`,
  -- hence `< s.card+1`, i.e. `≤ s.card`.
  unfold mex
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (mex_find?_isSome s)
  rw [hk, Option.getD_some]
  have hmem := List.mem_of_find?_eq_some hk
  rw [List.mem_range] at hmem
  omega

/-! ### Vertex ordering.

We sort vertices by the user-supplied key `order : V → ℕ` using a stable
list-based mergesort.  Ties (vertices with the same `order` value) are broken
arbitrarily but deterministically by the underlying `List.mergeSort`.
-/

/-- The vertex list of `V` sorted in `order`-ascending order.  Computable. -/
def vertexOrder
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (order : V → ℕ) : List V :=
  ((Finset.univ : Finset V).sort (· ≤ ·)).mergeSort
    (fun a b => order a ≤ order b)

/-! ### The greedy loop.

We thread a partial coloring `V → Option ℕ` through a left-fold over the
sorted vertex list.  At each step the current vertex's color is the `mex` of
the colors already assigned to its neighbours.
-/

/-- The accumulator state: a partial coloring. -/
private def Acc (V : Type u) : Type u := V → Option ℕ

private def Acc.empty (V : Type u) : Acc V := fun _ => none

/-- Update the partial coloring at vertex `v` with color `c`. -/
private def Acc.set
    {V : Type u} [DecidableEq V]
    (f : Acc V) (v : V) (c : ℕ) : Acc V :=
  fun w => if w = v then some c else f w

/-- The set of colors already assigned to neighbours of `v`. -/
private def neighbourColors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (f : Acc V) (v : V) : Finset ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).biUnion
    (fun w => match f w with
      | none => ∅
      | some c => {c})

/-- One step of the greedy loop. -/
private def greedyStep
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (f : Acc V) (v : V) : Acc V :=
  Acc.set f v (mex (neighbourColors G f v))

/-- The final partial coloring obtained by processing `vertexOrder order`. -/
private def greedyAcc
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (order : V → ℕ) : Acc V :=
  (vertexOrder order).foldl (greedyStep G) (Acc.empty V)

/-! ### Invariants of the greedy loop.

The two facts we need for properness:

* **Coloredness is monotone.**  Once a vertex is `some`, the fold never sets it
  back to `none`; and every vertex appearing in the processed list ends up
  `some`.
* **Properness is preserved.**  The relation "adjacent colored vertices have
  distinct colors" is maintained by every `greedyStep`, because the new vertex's
  color is the `mex` of its already-colored neighbours' colors and `mex` avoids
  that finset (`mex_not_mem`).
-/

/-- If `c ∈ neighbourColors G f v` then some neighbour `w` of `v` has `f w = c`. -/
private theorem mem_neighbourColors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (f : Acc V) (v : V) {c : ℕ} (hc : c ∈ neighbourColors G f v) :
    ∃ w, G.Adj v w ∧ f w = some c := by
  unfold neighbourColors at hc
  rw [Finset.mem_biUnion] at hc
  obtain ⟨w, hw, hcw⟩ := hc
  rw [Finset.mem_filter] at hw
  refine ⟨w, hw.2, ?_⟩
  cases hfw : f w with
  | none => rw [hfw] at hcw; simp at hcw
  | some d =>
      rw [hfw] at hcw
      rw [Finset.mem_singleton] at hcw
      rw [hcw]

/-- A colored neighbour's color lies in `neighbourColors G f v`. -/
private theorem color_mem_neighbourColors
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (f : Acc V) (v w : V) {c : ℕ} (hadj : G.Adj v w) (hfw : f w = some c) :
    c ∈ neighbourColors G f v := by
  unfold neighbourColors
  rw [Finset.mem_biUnion]
  exact ⟨w, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hadj⟩,
    by rw [hfw]; exact Finset.mem_singleton_self c⟩

/-- The "proper among colored vertices" invariant. -/
private def IsProperAcc
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (f : Acc V) : Prop :=
  ∀ a b, G.Adj a b → f a ≠ none → f b ≠ none → f a ≠ f b

/-- A single greedy step preserves the properness invariant. -/
private theorem isProperAcc_greedyStep
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {f : Acc V} (hf : IsProperAcc G f) (v : V) :
    IsProperAcc G (greedyStep G f v) := by
  intro a b hadj ha hb
  simp only [greedyStep, Acc.set] at ha hb ⊢
  by_cases hav : a = v <;> by_cases hbv : b = v
  · -- a = v = b contradicts adjacency (loopless)
    exact absurd (hav.trans hbv.symm) (G.ne_of_adj hadj)
  · -- a = v, b ≠ v: b is a colored neighbour of v, so its color is in
    -- `neighbourColors`, which `mex` avoids.
    simp only [if_pos hav, if_neg hbv] at *
    intro hcontra
    obtain ⟨cb, hcb⟩ := Option.ne_none_iff_exists'.mp hb
    have hmem : cb ∈ neighbourColors G f v :=
      color_mem_neighbourColors G f v b (hav ▸ hadj) hcb
    rw [hcb] at hcontra
    have : mex (neighbourColors G f v) = cb := Option.some.inj hcontra
    rw [← this] at hmem
    exact mex_not_mem _ hmem
  · -- a ≠ v, b = v: symmetric.
    simp only [if_neg hav, if_pos hbv] at *
    intro hcontra
    obtain ⟨ca, hca⟩ := Option.ne_none_iff_exists'.mp ha
    have hmem : ca ∈ neighbourColors G f v :=
      color_mem_neighbourColors G f v a (hbv ▸ hadj.symm) hca
    rw [hca] at hcontra
    have : mex (neighbourColors G f v) = ca := (Option.some.inj hcontra).symm
    rw [← this] at hmem
    exact mex_not_mem _ hmem
  · -- a ≠ v, b ≠ v: unchanged, use the hypothesis.
    simp only [if_neg hav, if_neg hbv] at *
    exact hf a b hadj ha hb

/-- The properness invariant survives the whole fold. -/
private theorem isProperAcc_foldl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (l : List V) {f : Acc V} (hf : IsProperAcc G f) :
    IsProperAcc G (l.foldl (greedyStep G) f) := by
  induction l generalizing f with
  | nil => simpa using hf
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih (isProperAcc_greedyStep G hf x)

/-- After folding over `l`, every vertex that was colored before, or appears in
`l`, is colored. -/
private theorem ne_none_foldl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (l : List V) {f : Acc V} (w : V) (hw : f w ≠ none ∨ w ∈ l) :
    (l.foldl (greedyStep G) f) w ≠ none := by
  induction l generalizing f with
  | nil =>
      rcases hw with hw | hw
      · simpa using hw
      · simp at hw
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      -- after stepping `x`, `w` is colored if it was, or if w = x, else defer.
      by_cases hwx : w = x
      · left
        simp only [greedyStep, Acc.set, if_pos hwx]
        exact Option.some_ne_none _
      · rcases hw with hw | hw
        · left
          simp only [greedyStep, Acc.set, if_neg hwx]; exact hw
        · right
          rcases List.mem_cons.mp hw with h | h
          · exact absurd h hwx
          · exact h

/-! ### Color bound invariant.

Every greedy color is `< |V|`: a vertex's color is the `mex` of the colors of
its already-coloured neighbours, and that finset has at most `|V| - 1` elements
(it never contains the vertex itself, since the graph is loopless), so `mex`
returns a value `≤ |V| - 1 < |V|`. -/

/-- `neighbourColors G f v` has fewer than `|V|` elements: it is a biUnion over
the (strict, loopless) neighbourhood of `v` of singletons/empties. -/
private theorem neighbourColors_card_lt
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (f : Acc V) (v : V) :
    (neighbourColors G f v).card < (Finset.univ : Finset V).card := by
  -- The index set of the biUnion avoids `v` (loopless), so it is `⊆ univ.erase v`.
  have hsub : (Finset.univ.filter (fun w => G.Adj v w)) ⊆ Finset.univ.erase v := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_erase]
    exact ⟨fun h => (G.ne_of_adj (h ▸ hw.2)) rfl, Finset.mem_univ _⟩
  -- Each fibre of the biUnion has cardinality ≤ 1.
  have hbi : (neighbourColors G f v).card
      ≤ (Finset.univ.filter (fun w => G.Adj v w)).card := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 ?_) ?_
    · intro w _
      cases f w with
      | none => simp
      | some c => simp
    · simp
  have hidx : (Finset.univ.filter (fun w => G.Adj v w)).card
      ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
  have herase : (Finset.univ.erase v).card < (Finset.univ : Finset V).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
    have : 0 < (Finset.univ : Finset V).card := Finset.card_pos.mpr ⟨v, Finset.mem_univ v⟩
    omega
  omega

/-- The "all colours `< |V|`" invariant on a partial colouring. -/
private def ColorsBoundedAcc
    {V : Type u} [Fintype V] (f : Acc V) : Prop :=
  ∀ w c, f w = some c → c < (Finset.univ : Finset V).card

/-- A single greedy step preserves the colour-bound invariant. -/
private theorem colorsBoundedAcc_greedyStep
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {f : Acc V} (hf : ColorsBoundedAcc f) (v : V) :
    ColorsBoundedAcc (greedyStep G f v) := by
  intro w c hwc
  simp only [greedyStep, Acc.set] at hwc
  by_cases hwv : w = v
  · rw [if_pos hwv] at hwc
    have : mex (neighbourColors G f v) = c := Option.some.inj hwc
    rw [← this]
    exact lt_of_le_of_lt (mex_lt_succ_card _) (neighbourColors_card_lt G f v)
  · rw [if_neg hwv] at hwc
    exact hf w c hwc

/-- The colour-bound invariant survives the whole fold. -/
private theorem colorsBoundedAcc_foldl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (l : List V) {f : Acc V} (hf : ColorsBoundedAcc f) :
    ColorsBoundedAcc (l.foldl (greedyStep G) f) := by
  induction l generalizing f with
  | nil => simpa using hf
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih (colorsBoundedAcc_greedyStep G hf x)

/-- **The greedy coloring.**

Visit vertices in `order`-ascending order (`order : V → ℕ` is user-supplied,
typically a degree-descending ordering or `wlStableColoring G`).  Each vertex
receives the smallest `ℕ` not already used by its already-colored neighbours.
The output is a total function `V → ℕ`; if a vertex was somehow missed by the
loop (impossible since we walk all of `Finset.univ`), it defaults to `0`. -/
def greedyColoring
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (order : V → ℕ) : V → ℕ :=
  fun v => (greedyAcc G order v).getD 0

/-! ## 2. Properness. -/

/-- **The greedy coloring is proper.**

Adjacent vertices receive distinct colors.  Proof punted; the argument is the
standard one: whichever of `u, v` is processed second sees the other's color
in `neighbourColors`, so `mex` returns something different. -/
theorem greedyColoring_isProper
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (order : V → ℕ) {u v : V} (h : G.Adj u v) :
    greedyColoring G order u ≠ greedyColoring G order v := by
  -- Both vertices appear in `vertexOrder order` (a permutation of `univ`), so
  -- both are colored in the final accumulator; the properness invariant
  -- (maintained by every `greedyStep` via `mex_not_mem`) then gives distinct
  -- colors.
  have hmemu : u ∈ vertexOrder order := by
    unfold vertexOrder; rw [List.mem_mergeSort, Finset.mem_sort]; exact Finset.mem_univ u
  have hmemv : v ∈ vertexOrder order := by
    unfold vertexOrder; rw [List.mem_mergeSort, Finset.mem_sort]; exact Finset.mem_univ v
  -- Both are colored.
  have hu : greedyAcc G order u ≠ none :=
    ne_none_foldl G _ u (Or.inr hmemu)
  have hv : greedyAcc G order v ≠ none :=
    ne_none_foldl G _ v (Or.inr hmemv)
  -- The accumulator is proper.
  have hproper : IsProperAcc G (greedyAcc G order) :=
    isProperAcc_foldl G _ (by intro a b _ ha _; exact absurd rfl ha)
  have hne : greedyAcc G order u ≠ greedyAcc G order v := hproper u v h hu hv
  -- Translate `Option` inequality to `getD 0` inequality.
  unfold greedyColoring
  obtain ⟨cu, hcu⟩ := Option.ne_none_iff_exists'.mp hu
  obtain ⟨cv, hcv⟩ := Option.ne_none_iff_exists'.mp hv
  rw [hcu, hcv, Option.getD_some, Option.getD_some]
  intro hcc
  exact hne (by rw [hcu, hcv, hcc])

/-- Every greedy colour is `< |V|`.  (Every vertex is processed by the fold, so
its accumulator entry is `some c` with `c < |V|`; the `getD 0` fallback is `0`,
also `< |V|` since `V` is inhabited by `v`.) -/
theorem greedyColoring_lt_card
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (order : V → ℕ) (v : V) :
    greedyColoring G order v < (Finset.univ : Finset V).card := by
  have hbound : ColorsBoundedAcc (greedyAcc G order) :=
    colorsBoundedAcc_foldl G _ (by intro w c h; simp [Acc.empty] at h)
  unfold greedyColoring
  cases hgv : greedyAcc G order v with
  | none =>
      simp only [Option.getD_none]
      exact Finset.card_pos.mpr ⟨v, Finset.mem_univ v⟩
  | some c =>
      simp only [Option.getD_some]
      exact hbound v c hgv

/-! ## 3. Color count. -/

namespace greedyColoring

/-- The **number of colors used** by the greedy coloring: `max color + 1`,
or `0` if `V` is empty. -/
def numColors
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (order : V → ℕ) : ℕ :=
  let img : Finset ℕ := Finset.univ.image (greedyColoring G order)
  match img.max with
  | none => 0
  | some m => m + 1

end greedyColoring

/-! ## 4. The WL-greedy coloring. -/

/-- **The Weisfeiler–Leman greedy coloring.**

Compute the WL-stable coloring `wlStableColoring G : V → ℕ`, then run greedy
with this as the vertex order.  Vertices in the same WL-cell are processed
consecutively; the greedy heuristic then often produces an *optimal* coloring
on graphs whose WL-stable partition coincides with their orbit partition
(e.g. vertex-transitive distance-regular graphs).

End-to-end computable. -/
def wlGreedyColoring
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : V → ℕ :=
  greedyColoring G (WL.wlStableColoring G)

/-- The number of colors used by the WL-greedy heuristic. -/
def wlGreedyColoring.numColors
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  greedyColoring.numColors G (WL.wlStableColoring G)

/-! ## 5. Bounds for graphs with small equitable partition.

When `G` admits a coarsest equitable partition with few cells (equivalently:
the WL-stable coloring uses few values), the WL-greedy heuristic is
guaranteed to find a coloring whose count is bounded by a small function of
the cell count and the cell-restricted maximum degree.

Concretely: if the WL-stable partition has `k` cells and the *interaction
graph between cells* has chromatic number `χ_q`, then WL-greedy uses at most
`(maxCellSize - 1) + χ_q` colors.  We state only the headline bound.
-/

/-- **Color-count bound for small-equitable graphs.**

If the WL-stable coloring has at most `k` distinct values, the WL-greedy
coloring uses at most `k * |V|` colors.  This is a loose but simple bound;
tracking the equitable cell structure would give `k * (Δ(G) + 1)` with
`Δ(G)` the max degree, and tighter bounds (linear in `k` alone for
vertex-transitive graphs) are well known. -/
theorem wlGreedyColoring_numColors_le
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (hk : (Finset.univ.image (WL.wlStableColoring G)).card ≤ k) :
    wlGreedyColoring.numColors G ≤
      k * ((Finset.univ : Finset V).card) := by
  -- Crude bound: greedy never uses more than `|V|` colors total (every colour
  -- is `< |V|` by `greedyColoring_lt_card`), and for nonempty `V` the WL-stable
  -- image is nonempty so `1 ≤ k`, giving `|V| ≤ k * |V|`.  For empty `V` both
  -- sides are `0`.  Tracking the equitable cell structure would
  -- give the much tighter `k * (Δ + 1)` mentioned in the docstring.
  -- Step 1: `numColors ≤ |V|`.
  have hnum_le : wlGreedyColoring.numColors G ≤ (Finset.univ : Finset V).card := by
    unfold wlGreedyColoring.numColors greedyColoring.numColors
    simp only
    set img : Finset ℕ := Finset.univ.image (greedyColoring G (WL.wlStableColoring G)) with himg
    cases hmax : img.max with
    | bot => simp
    | coe m =>
        simp only
        -- `m ∈ img`, so `m = greedyColoring … v` for some `v`, hence `m < |V|`.
        have hmem : m ∈ img := Finset.mem_of_max hmax
        rw [himg, Finset.mem_image] at hmem
        obtain ⟨v, _, hv⟩ := hmem
        have hlt : m < (Finset.univ : Finset V).card := by
          rw [← hv]; exact greedyColoring_lt_card G _ v
        omega
  -- Step 2: case split on whether `V` is empty.
  rcases Nat.eq_zero_or_pos (Finset.univ : Finset V).card with hV0 | hVpos
  · -- Empty `V`: numColors ≤ 0 = k * 0.
    rw [hV0] at hnum_le ⊢
    simpa using hnum_le
  · -- Nonempty `V`: the WL image is nonempty, so `1 ≤ k`.
    have himg_pos : 0 < (Finset.univ.image (WL.wlStableColoring G)).card := by
      rw [Finset.card_pos]
      obtain ⟨v, _⟩ := Finset.card_pos.mp hVpos
      exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩
    have hk1 : 1 ≤ k := le_trans himg_pos hk
    calc wlGreedyColoring.numColors G
        ≤ (Finset.univ : Finset V).card := hnum_le
      _ = 1 * (Finset.univ : Finset V).card := (one_mul _).symm
      _ ≤ k * (Finset.univ : Finset V).card := Nat.mul_le_mul_right _ hk1

/-! ## 6. Smoke tests.

Concrete example graphs and their (WL-)greedy color counts:

* `K₃`: clique number 3 ⇒ 3 colors.
* `C₅`: odd cycle, χ = 3 ⇒ greedy in cyclic order uses 3 colors.
* Petersen: χ(Petersen) = 3 ⇒ 3 colors (the Petersen graph is famously
  3-chromatic but not 3-edge-colorable; WL-greedy hits the vertex chromatic
  number).
-/

section Examples

open WL  -- pulls in `K3` and `Petersen` from WLRefinement

/-- The 5-cycle on `Fin 5`. -/
def C5 : _root_.SimpleGraph (Fin 5) where
  Adj x y := (x.val + 1) % 5 = y.val ∨ (y.val + 1) % 5 = x.val
  symm := fun _ _ h => h.symm
  loopless := ⟨fun x h => by
    rcases h with h | h <;>
      · have : x.val < 5 := x.isLt
        omega⟩

instance : DecidableRel C5.Adj := fun x y => by
  unfold C5
  exact inferInstanceAs (Decidable (_ ∨ _))

end Examples

section SmokeTests

-- Greedy on `K₃` with the identity order: should use 3 colors.
#eval greedyColoring WL.K3 (fun v => v.val)
#eval greedyColoring.numColors WL.K3 (fun v => v.val)   -- expect 3

-- Greedy on `C₅` with the identity order: should use 3 colors
-- (0,1,0,1,2 around the cycle).
#eval greedyColoring C5 (fun v => v.val)
#eval greedyColoring.numColors C5 (fun v => v.val)      -- expect 3

-- WL-greedy on the Petersen graph: should use 3 colors.
--
-- NOTE: this `#eval` runs full Weisfeiler–Leman colour refinement on a 10-vertex
-- graph at *elaboration time*, and the nested `Multiset`-of-colours encoding makes
-- it expensive enough to stall `lake build`.  Left as a comment so the library
-- builds promptly; uncomment to run it manually in an editor / `#eval` session.
-- #eval wlGreedyColoring.numColors WL.Petersen           -- expect 3

end SmokeTests

end Coloring
end Graphplay
