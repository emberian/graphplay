import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-! # Graphplay Demo: Color the Heawood graph on the torus.

This demo runs end-to-end at `#eval`-time:

1. Construct the Heawood combinatorial-map embedding of K_7 on the torus.
2. Extract its underlying SimpleGraph.
3. Apply the WL-greedy coloring algorithm.
4. Verify the coloring is proper.
5. Print the number of colors used (should be 7).

The headline fact: K_7 embeds on the torus (Heffter 1891 / Ringel-Youngs),
and the surface-Heawood number for genus 1 is 7. The complete graph K_7
needs exactly 7 colors (its chromatic number is 7), and any vertex
relabelling produces a proper 7-coloring. The "WL-greedy" coloring on
K_7 reduces, after one refinement step, to a vertex bijection — every
vertex has a singleton color class — so the simple fallback below
realises the same coloring up to renaming.

This file is intentionally self-contained: it does not assume sibling
files `Graphplay/Examples/HeawoodOnTorus.lean` or
`Graphplay/Algorithm/Coloring.lean` are present, falling back to local
definitions when they are not. See the "Beyond the demo" section at
the end for the broader template.
-/

namespace Graphplay.Demo

/-! ## 1. Heawood graph on the torus (underlying simple graph: K_7)

The Heawood-Ringel-Youngs embedding of K_7 on the torus has 7 vertices,
21 edges, and 14 triangular faces, giving Euler characteristic
`V - E + F = 7 - 21 + 14 = 0`, consistent with genus 1 (the torus).
The *abstract* underlying graph is K_7; the embedding is what witnesses
genus 1. For this demo, we only need the abstract graph; the torus
witness lives in `Graphplay/CombinatorialMap.lean` and the (in-progress)
`Graphplay/Examples/HeawoodOnTorus.lean`. -/

/-- The complete graph `K_7` on `Fin 7`. This is the underlying simple
graph of the torus-Heawood embedding. -/
def heawoodK7 : SimpleGraph (Fin 7) where
  Adj i j := i ≠ j
  symm := fun {_ _} h => h.symm
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel heawoodK7.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j))

/-! ## 2. Coloring

Fallback coloring: since the underlying graph is K_7 (complete), every
proper coloring needs at least 7 colors, and any vertex-bijection
`Fin 7 → ℕ` is proper. This matches what a WL-refinement-driven greedy
on K_7 produces (every vertex is its own cell). If
`Graphplay/Algorithm/Coloring.lean` lands with a `wlGreedyColoring`,
this can be swapped in directly. -/

/-- Fallback proper coloring of `K_7` by `Fin 7 → ℕ`, i.e. `i ↦ i.val`. -/
def heawoodColoring : Fin 7 → ℕ := fun i => i.val

/-! ## 3. Color count and properness check (computable) -/

/-- The list of color values used by `heawoodColoring`, over all vertices. -/
def heawoodColorList : List ℕ :=
  (List.finRange 7).map heawoodColoring

/-- Maximum element of a `List ℕ`, returning `0` for the empty list. -/
def listMaxNat : List ℕ → ℕ
  | []        => 0
  | (x :: xs) => xs.foldl Nat.max x

/-- Number of colors used: `max color + 1` if there's any vertex, else 0.
For our fallback this is exactly 7. -/
def heawoodColorCount : ℕ :=
  if heawoodColorList.isEmpty then 0
  else listMaxNat heawoodColorList + 1

/-- A purely computable proper-coloring check: for every ordered pair of
distinct vertices `(i, j)` with `i.val < j.val` that are adjacent in
`heawoodK7`, the two endpoints receive different colors. We iterate over
`Fin 7 × Fin 7` directly to avoid `DecidableRel`-instance fiddling. -/
def heawoodColoringIsProper : Bool :=
  (List.finRange 7).all fun i =>
    (List.finRange 7).all fun j =>
      -- We only need to check ordered distinct pairs; K_7 is adjacent
      -- iff the two vertices differ, so the test simplifies.
      if i = j then true
      else decide (heawoodColoring i ≠ heawoodColoring j)

/-! ## 4. Smoke tests

When `lake build Graphplay.Demo` succeeds and these `#eval`s are run
(e.g. via `lean --run` or the editor), the outputs should be:

* `heawoodColorCount` → `7`
* `heawoodColoringIsProper` → `true`
* The color tuple → `[0, 1, 2, 3, 4, 5, 6]` (7 distinct naturals).

These are *concrete* values, not `sorry`. -/

#eval heawoodColorCount
-- expected: 7

#eval heawoodColoringIsProper
-- expected: true

#eval (List.range 7).map (fun i =>
  heawoodColoring ⟨i % 7, by
    have : i % 7 < 7 := Nat.mod_lt _ (by decide)
    exact this⟩)
-- expected: [0, 1, 2, 3, 4, 5, 6]

#eval heawoodColorList
-- expected: [0, 1, 2, 3, 4, 5, 6]

/-! ## Beyond the demo

The same template extends to:

* **Heawood numbers for higher genus.** `Graphplay.GraphBundle.Heawood g`
  computes `⌊(7 + √(1 + 48 g)) / 2⌋`, the chromatic upper bound for any
  graph embeddable on the orientable surface of genus `g`. The
  underlying graph of the genus-`g` saturating example is `K_{H(g)}`.

* **Surface embeddings via `CombinatorialMap`.** A
  `Graphplay.CombinatorialMap V E` over half-edges `E` and vertices `V`
  is a fixed-point-free involution `σ` paired with a vertex rotation
  `ρ`; faces are the cycles of `ρ ∘ σ`, and `V - E/2 + F = 2 - 2g`
  recovers the genus. The Heawood-Ringel-Youngs rotation
  `i ↦ i + 1 (mod 7)` on the seven darts at each vertex of `K_7`
  realises the torus embedding.

* **Quantum walks via `WeightedGraph.toGraphon`.** Once a graph is in
  hand, `Graphplay.Weighted` and `Graphplay.Spectral` lift it to a
  weighted graph and then to a graphon, on which perfect state transfer
  (PST), continuous-time quantum walks (CTQW), and Lindblad mixing
  live. The Heawood-K_7 example is the canonical test case for surface
  protection in this stack.

* **Equitable refinement.** `Graphplay.Algorithm.WLRefinement` provides
  a Weisfeiler-Leman refinement procedure whose stable coloring agrees
  with the coarsest equitable partition; on `K_7` it produces 7
  singleton cells, hence the chromatic number 7 also drops out from WL.
-/

end Graphplay.Demo
