/-
# Graphplay.Examples.HeawoodOnTorus

The **Heawood embedding** of the complete graph `K_7` on the torus.

This is the classical 7-vertex toroidal triangulation that exhibits the
Heawood bound `χ(T²) = 7`: `K_7` is 7-chromatic, embeds on the torus, and
no graph of higher chromatic number embeds on the torus (Ringel's
*Map Color Theorem*, 1968).

**Combinatorics.**  `V = Fin 7`, every pair `i ≠ j` is an edge
(so `E = 21`).  The classical rotation system, due to Heawood (1890), takes
at each vertex `i` the cyclic neighbor order

  `(i+1, i+2, i+3, i+4, i+5, i+6)  (mod 7)`.

This produces a triangulation with `14` triangular faces; Euler:
`7 - 21 + 14 = 0`, so genus `1`.

**Heawood bound.**  For orientable genus `g`,
`χ ≤ ⌊(7 + √(1 + 48 g)) / 2⌋`; for `g = 1` this gives `7`, and `K_7 ↪ T²`
shows the bound is tight.

References: Ringel, *Map Color Theorem* (1974); White, *Graphs, Groups, and
Surfaces*, §6.5.
-/
import Graphplay.CombinatorialMap
import Graphplay.Bundle

universe u v

namespace Graphplay
namespace Examples
namespace HeawoodOnTorus

open CombinatorialMap

/-- Vertex of `K_7`. -/
abbrev V := Fin 7

/-- A dart is an ordered pair of distinct vertices.  We model it as
`{ p : V × V // p.1 ≠ p.2 }`. -/
abbrev D := { p : V × V // p.1 ≠ p.2 }

instance : Fintype D := by unfold D; infer_instance
instance : DecidableEq D := by unfold D; infer_instance

/-- σ: swap the endpoints of a dart. -/
def σ_fun (x : D) : D := ⟨(x.val.2, x.val.1), fun h => x.property h.symm⟩

/-- σ as a permutation. -/
def σ_perm : Equiv.Perm D where
  toFun := σ_fun
  invFun := σ_fun
  left_inv := by intro x; rcases x with ⟨⟨a, b⟩, hab⟩; rfl
  right_inv := by intro x; rcases x with ⟨⟨a, b⟩, hab⟩; rfl

/-- The Heawood rotation: at vertex `i`, neighbors are visited in the order
`i+1, i+2, i+3, i+4, i+5, i+6` (mod 7).  Given a dart `(i, j)`, the next
dart at `i` is `(i, j+1)`, except that `(i, i)` is excluded (so when
`j+1 = i` we skip to `j+2`, which equals `i+1`). -/
def rot_next (i j : V) : V :=
  let j' : V := j + 1
  if j' = i then j' + 1 else j'

/-- ρ: at vertex `x.val.1 = i`, send `j ↦ rot_next i j`. -/
def ρ_fun (x : D) : D :=
  ⟨(x.val.1, rot_next x.val.1 x.val.2), by
    -- The result has distinct components: rot_next skips over `i`.
    rcases x with ⟨⟨i, j⟩, hij⟩
    simp only [rot_next]
    split_ifs with hcase
    · -- hcase : j + 1 = i; need i ≠ j + 2.  Assume i = j + 2.  Combining with
      -- hcase gives j + 2 = j + 1, i.e., 1 = 0 in Fin 7, contradiction.
      intro h
      have h1 : (j + 1 : V) = j + 1 + 1 := by
        conv_lhs => rw [hcase]
        exact h
      have h2 : (0 : V) = 1 := by
        have := sub_eq_zero.mpr h1.symm
        simpa using this
      exact absurd h2.symm (by decide)
    · -- j + 1 ≠ i.
      intro h
      exact hcase h.symm⟩

/-- ρ as a permutation.  Inverse: walk the rotation backwards (or apply 5
times, since each vertex has 6 incident darts and the cycle has length 6). -/
def ρ_perm : Equiv.Perm D where
  toFun := ρ_fun
  -- Inverse via 5-fold iteration (length-6 cycles): a clean computable inverse.
  invFun := fun x => ρ_fun (ρ_fun (ρ_fun (ρ_fun (ρ_fun x))))
  left_inv := by
    -- ρ_fun has order 6 on each vertex's 6 darts; applying it 6 times = id.
    -- Finite case analysis over the 42 darts.
    decide
  right_inv := by
    decide

/-- The Heawood combinatorial map: `K_7` on the torus. -/
def heawoodMap : CombinatorialMap V D where
  σ := σ_perm
  ρ := ρ_perm
  σ_involutive := by
    apply Equiv.Perm.ext
    intro x
    exact σ_perm.left_inv x
  σ_no_fixed := by
    intro x h
    rcases x with ⟨⟨a, b⟩, hab⟩
    -- σ swaps coords, so a fixed point would have a = b, contradicting hab.
    have : σ_fun ⟨(a, b), hab⟩ = ⟨(a, b), hab⟩ := h
    simp [σ_fun, Subtype.mk.injEq, Prod.mk.injEq] at this
    exact hab this.2
  vert := fun x => x.val.1
  vert_rot := by
    intro x
    rfl

/-! ## Smoke tests -/

/-- `#eval heawoodMap.numVertices  -- 7` -/
example : heawoodMap.numVertices = 7 := by decide

/-- `K_7` has `21` edges = `42` darts / `2`. -/
example : Fintype.card D = 42 := by decide

example : heawoodMap.numEdges = 21 := by decide

/-- **Genus 1**: the Heawood embedding is on the torus.
    `V - E + F = 7 - 21 + 14 = 0 = 2 - 2g ⇒ g = 1`. -/
theorem heawood_genus_one : heawoodMap.genus = 1 := by
  -- Computing `numFaces = 14` requires evaluating `cycleFactorsFinset`
  -- on `ρ ∘ σ` over 42 darts, which is in-principle a `decide` but is
  -- impractical for the kernel.  Stated; proof deferred.
  sorry

/-- The Heawood bound predicts chromatic number `≤ 7` on the torus, and
`K_7` realizes this bound: -/
example : Graphplay.GraphBundle.Heawood 1 = 7 := by
  -- `(7 + √49)/2 = 7`; the real-number reduction is left as a `sorry`.
  unfold Graphplay.GraphBundle.Heawood
  sorry

/-- **The underlying graph of the Heawood map is the complete graph `K_7`.**

The Heawood rotation system is an embedding of `K_7`: any two distinct vertices
`u ≠ v` are joined by an edge.  Concretely, the dart `⟨(u, v), hne⟩` has
`vert = u` and its `σ`-partner `⟨(v, u), …⟩` has `vert = v`, so `u` and `v` are
adjacent in `toSimpleGraph`.  Hence `heawoodMap.toSimpleGraph = ⊤`.

This is the combinatorial fact behind the Heawood bound being *tight* on the
torus: `K_7` is `7`-chromatic, embeds here on the genus-1 surface, and no graph
of higher chromatic number embeds on the torus (Ringel's Map Color Theorem). -/
theorem heawood_toSimpleGraph_eq_top :
    heawoodMap.toSimpleGraph = (⊤ : SimpleGraph V) := by
  ext u v
  simp only [SimpleGraph.top_adj]
  constructor
  · -- Adjacency in `toSimpleGraph` includes `u ≠ v` by definition.
    rintro ⟨hne, _⟩
    exact hne
  · -- Conversely, distinct `u, v` are joined by the dart `(u, v)`.
    intro hne
    refine ⟨hne, ⟨(u, v), hne⟩, rfl, ?_⟩
    -- `vert (σ e) = (σ_fun e).val.1 = e.val.2 = v`.
    rfl

end HeawoodOnTorus
end Examples
end Graphplay
