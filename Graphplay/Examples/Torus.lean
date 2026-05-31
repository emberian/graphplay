/-
# Graphplay.Examples.Torus

The 4×4 toroidal grid as a combinatorial map.

**Combinatorics.**  Vertices `V = Fin 4 × Fin 4` (`|V| = 16`), undirected
edges `E_grid = 32` (each vertex has 4 incident edges, double-counted),
faces are quadrilateral 4-cycles (16 of them).  Euler characteristic
`χ = 16 - 32 + 16 = 0`, hence orientable genus `g = 1`: the torus.

**Half-edge model.**  A *dart* is a triple `(v, d)` where `v : Fin 4 × Fin 4`
is a vertex and `d : Fin 4` is a direction (0=right, 1=up, 2=left, 3=down).
There are `16 × 4 = 64` darts.  The edge involution `σ` sends `(v, d)` to
`(v + step d, opposite d)`, and the rotation `ρ` at a fixed vertex sends
direction `d ↦ d + 1` (counterclockwise), so cycles of `ρ` are the
length-4 rotations at each vertex.

**Genus.**  The 4×4 grid embeds on the torus; its faces are the 16 unit
squares.  The Euler characteristic is `0`, so `genus = 1`.
-/
import Graphplay.CombinatorialMap
import Graphplay.Bundle

universe u v

namespace Graphplay
namespace Examples
namespace Torus

open CombinatorialMap

/-- Vertex of the 4×4 toroidal grid. -/
abbrev V := Fin 4 × Fin 4

/-- Direction (0=right, 1=up, 2=left, 3=down). -/
abbrev Dir := Fin 4

/-- Half-edge / dart: a vertex together with a direction. -/
abbrev D := V × Dir

/-- The step vector for each direction. -/
def step : Dir → V
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (-1, 0)  -- (3, 0) in Fin 4
  | ⟨3, _⟩ => (0, -1)  -- (0, 3) in Fin 4
  | ⟨_+4, h⟩ => absurd h (by omega)

/-- Opposite of a direction (`+2 mod 4`). -/
def opp (d : Dir) : Dir := d + 2

/-- σ: edge involution.  Walk along the dart, then look back. -/
def σ_fun (x : D) : D := (x.1 + step x.2, opp x.2)

/-- σ is an involution: σ(σ(v,d)) = (v,d).  `opp ∘ opp = id` and
`step (opp d) = - step d`, so the walked-to vertex walks back. -/
def σ_perm : Equiv.Perm D where
  toFun := σ_fun
  invFun := σ_fun
  left_inv := by
    intro x
    rcases x with ⟨v, d⟩
    fin_cases d <;>
      · simp [σ_fun, step, opp]
        rcases v with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;> decide
  right_inv := by
    intro x
    rcases x with ⟨v, d⟩
    fin_cases d <;>
      · simp [σ_fun, step, opp]
        rcases v with ⟨a, b⟩
        fin_cases a <;> fin_cases b <;> decide

/-- ρ: rotate the direction by `+1` at the same vertex. -/
def ρ_perm : Equiv.Perm D where
  toFun := fun x => (x.1, x.2 + 1)
  invFun := fun x => (x.1, x.2 - 1)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The combinatorial map for the 4×4 toroidal grid. -/
def gridMap : CombinatorialMap V D where
  σ := σ_perm
  ρ := ρ_perm
  σ_involutive := by
    apply Equiv.Perm.ext
    intro x
    show σ_perm (σ_perm x) = x
    exact σ_perm.left_inv x
  σ_no_fixed := by
    intro x h
    rcases x with ⟨v, d⟩
    -- σ moves the vertex by a nonzero step (in Fin 4 × Fin 4 each step is
    -- nonzero), so it cannot fix a dart.
    have : σ_fun (v, d) = (v, d) := h
    fin_cases d <;> simp [σ_fun, step, opp] at this <;>
      (rcases this with ⟨h1, h2⟩; revert h1 h2;
       rcases v with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩;
       interval_cases a <;> interval_cases b <;> decide)
  vert := fun x => x.1
  vert_rot := by intro e; rfl

/-! ## Smoke tests -/

/-- `#eval gridMap.numVertices  -- 16` -/
example : gridMap.numVertices = 16 := by decide

/-- `#eval gridMap.numEdges  -- 32 = 64 / 2` -/
example : gridMap.numEdges = 32 := by decide

/-- The dart set has 64 elements (16 vertices × 4 directions). -/
example : Fintype.card D = 64 := by decide

/-- Genus = 1 (torus).  This relies on `numFaces = 16`, which is provable
by `decide` once `cycleFactorsFinset` reduction kicks in but is too heavy
for the kernel; left as `sorry`. -/
theorem grid_genus_one : gridMap.genus = 1 := by
  have hF : gridMap.numFaces = 16 := by native_decide
  unfold CombinatorialMap.genus CombinatorialMap.eulerChar
    CombinatorialMap.numVertices CombinatorialMap.numEdges
  rw [hF]
  norm_num

/-- Heawood-bound connection (`Graphplay/Bundle.lean`): on the torus
`g = 1`, the Heawood number is `⌊(7 + √49)/2⌋ = 7`, so the chromatic
number of any toroidal graph is `≤ 7`.  `gridMap`, having maximum degree
4, is properly 5-colorable in fact. -/
example : Graphplay.GraphBundle.Heawood 1 = 7 := by
  -- `(7 + √49)/2 = 7`
  unfold Graphplay.GraphBundle.Heawood
  have hsqrt : Real.sqrt (1 + 48 * ((1 : ℕ) : ℝ)) = 7 := by
    rw [show (1 + 48 * ((1 : ℕ) : ℝ)) = 7 ^ 2 by push_cast; norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

end Torus
end Examples
end Graphplay
