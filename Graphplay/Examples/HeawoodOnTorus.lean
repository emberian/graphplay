/-
# Graphplay.Examples.HeawoodOnTorus

The **Heawood embedding** of the complete graph `K_7` on the torus.

This is the classical 7-vertex toroidal triangulation that exhibits the
Heawood bound `χ(T²) = 7`: `K_7` is 7-chromatic, embeds on the torus, and
no graph of higher chromatic number embeds on the torus (Ringel's
*Map Color Theorem*, 1968).

**Combinatorics.**  `V = Fin 7`, every pair `i ≠ j` is an edge
(so `E = 21`).  The classical rotation system, due to Heawood (1890), takes
at each vertex `i` the cyclic neighbor order whose successive offsets are
multiplied by `3 (mod 7)`:

  `(i+1, i+3, i+2, i+6, i+4, i+5)  (mod 7)`,

i.e. the rotation sends the dart `(i, i+d)` to `(i, i+3d)`.

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

/-- The Heawood rotation: at vertex `i`, the cyclic neighbor order is
`i+1, i+3, i+2, i+6, i+4, i+5` (mod 7) — successive offsets multiply by `3`.
Given a dart `(i, j)` with offset `d = j - i`, the next dart at `i` is
`(i, i + 3d)`.  Since `3` is invertible mod `7`, this fixes no offset and
visits all six neighbors. -/
def rot_next (i j : V) : V :=
  i + 3 * (j - i)

/-- `rot_next` never returns the base vertex: `3d ≠ 0` for `d ≠ 0` mod 7. -/
theorem rot_next_ne : ∀ i j : V, i ≠ j → i ≠ rot_next i j := by decide

/-- ρ: at vertex `x.val.1 = i`, send `j ↦ rot_next i j`. -/
def ρ_fun (x : D) : D :=
  ⟨(x.val.1, rot_next x.val.1 x.val.2), rot_next_ne _ _ x.property⟩

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

/-! ## The 14 triangular faces

`cycleFactorsFinset` is not kernel-reducible at this size, so we exhibit the
face decomposition explicitly: the face permutation `φ = ρ ∘ σ` is the product
of 14 disjoint 3-cycles, one per triangle `{(i,j), (j,k), (k,i)}` of the
triangulation.  Mathlib's `cycleFactorsFinset_eq_list_toFinset` then pins down
`faceCycles` exactly. -/

/-- The face 3-cycle through the darts `(i,j) → (j,k) → (k,i)` of a triangle
`{i, j, k}`. -/
def tri (i j k : V) (hij : i ≠ j := by decide) (hjk : j ≠ k := by decide)
    (hki : k ≠ i := by decide) : Equiv.Perm D :=
  [(⟨(i, j), hij⟩ : D), ⟨(j, k), hjk⟩, ⟨(k, i), hki⟩].formPerm

/-- Each `tri` is a cycle: its defining dart list is nontrivial and
duplicate-free. -/
theorem tri_isCycle (i j k : V) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    (tri i j k hij hjk hki).IsCycle := by
  refine List.isCycle_formPerm ?_ (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or, Subtype.mk.injEq, Prod.mk.injEq, not_and]
  refine ⟨⟨fun h => absurd h hij, fun h => absurd h.symm hki⟩, ?_⟩
  tauto

/-- The 14 triangular faces of the Heawood embedding, as disjoint 3-cycles of
darts.  Triangle `tri i j k` traverses darts `(i,j) → (j,k) → (k,i)`. -/
def faceList : List (Equiv.Perm D) :=
  [tri 0 1 5, tri 0 2 3, tri 0 3 1, tri 0 4 6, tri 0 5 4, tri 0 6 2,
   tri 1 2 6, tri 1 3 4, tri 1 4 2, tri 1 6 5,
   tri 2 4 5, tri 2 5 3, tri 3 5 6, tri 3 6 4]

theorem faceList_nodup : faceList.Nodup := by decide

theorem faceList_isCycle : ∀ f ∈ faceList, f.IsCycle := by
  simp only [faceList, List.mem_cons, List.not_mem_nil, or_false]
  rintro f (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl) <;>
    exact tri_isCycle _ _ _ (by decide) (by decide) (by decide)

/-- Pointwise disjointness of permutations, in directly decidable form. -/
instance : DecidableRel (fun f g : Equiv.Perm D => ∀ x : D, f x = x ∨ g x = x) :=
  fun f g => inferInstanceAs (Decidable (∀ x : D, f x = x ∨ g x = x))

set_option maxRecDepth 8192 in
theorem faceList_pairwise_disjoint : faceList.Pairwise Equiv.Perm.Disjoint := by
  have h : faceList.Pairwise (fun f g => ∀ x : D, f x = x ∨ g x = x) := by decide
  exact h.imp fun hfg => hfg

set_option maxRecDepth 8192 in
/-- The product of the 14 face triangles is exactly the face permutation
`φ = ρ ∘ σ`. -/
theorem faceList_prod : faceList.prod = heawoodMap.facePerm :=
  Equiv.ext (by decide +kernel : ∀ x : D, faceList.prod x = heawoodMap.facePerm x)

/-- The face cycles of the Heawood map are precisely the 14 triangles. -/
theorem heawood_faceCycles : heawoodMap.faceCycles = faceList.toFinset :=
  (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset faceList_nodup).mpr
    ⟨faceList_isCycle, faceList_pairwise_disjoint, faceList_prod⟩

/-- The Heawood rotation triangulates the torus: `14` (triangular) faces. -/
theorem heawood_numFaces : heawoodMap.numFaces = 14 := by
  unfold CombinatorialMap.numFaces
  have h1 : heawoodMap.faceCycles.card = 14 := by
    rw [heawood_faceCycles, List.toFinset_card_of_nodup faceList_nodup]
    decide
  have h2 : heawoodMap.faceFixedPoints.card = 0 := by decide
  rw [h1, h2]

/-- **Genus 1**: the Heawood embedding is on the torus.
    `V - E + F = 7 - 21 + 14 = 0 = 2 - 2g ⇒ g = 1`. -/
theorem heawood_genus_one : heawoodMap.genus = 1 := by
  have hV : heawoodMap.numVertices = 7 := by decide
  have hE : heawoodMap.numEdges = 21 := by decide
  unfold CombinatorialMap.genus CombinatorialMap.eulerChar
  rw [hV, hE, heawood_numFaces]
  decide

/-- The Heawood bound predicts chromatic number `≤ 7` on the torus, and
`K_7` realizes this bound: -/
example : Graphplay.GraphBundle.Heawood 1 = 7 := by
  -- `(7 + √49)/2 = 7`.
  unfold Graphplay.GraphBundle.Heawood
  have hsqrt : Real.sqrt (1 + 48 * ((1 : ℕ) : ℝ)) = 7 := by
    rw [show (1 + 48 * ((1 : ℕ) : ℝ)) = 7 ^ 2 by push_cast; norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hsqrt]
  norm_num

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
