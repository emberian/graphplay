/-
# Graphplay.CombinatorialMap

Combinatorial maps (rotation systems) for graph embeddings on orientable
surfaces.  A combinatorial map encodes a 2-cell embedding of a finite graph
on an orientable surface purely combinatorially: at each vertex one specifies
a *cyclic order* on the incident half-edges ("darts"), and the surface is
recovered (up to homeomorphism) by gluing the faces predicted by the rotation
system.

The standard half-edge formulation, due to Heffter and made systematic by
Edmonds, takes an edge to be a pair of *darts*; an involution `σ : E → E`
without fixed points pairs the two darts of each edge, and a permutation
`ρ : E → E` (whose cycles are the vertex rotations) gives the cyclic order
around each vertex.  The **faces** are then the orbits of `ρ ∘ σ`, and
Euler's formula

  `V - E/2 + F = 2 - 2g`

determines the orientable genus `g` of the embedding.

This file provides:

* `RotationSystem` — a per-vertex rotation as a cyclic permutation.
* `CombinatorialMap` — the half-edge model `(V, E, σ, ρ)` with `σ` a
  fixed-point-free involution and `ρ` an arbitrary permutation of `E`.
* `CombinatorialMap.faces` — a `Finset (Equiv.Perm E)` of face-cycle factors
  of `ρ ∘ σ`, together with `numFaces`, `eulerChar`, and `genus`.
* `toSimpleGraph`, `toWeightedGraph` — extract the underlying graph.
* Properness lemmas + Euler-Poincaré relations (statements + `sorry`).

All arithmetic on finite combinatorial maps is computable via Mathlib's
`Equiv.Perm` infrastructure; the proofs of correctness against the topological
notion of "face" are left to a future pass.

References: Mohar-Thomassen *Graphs on Surfaces* §3.2; Gross-Tucker
*Topological Graph Theory* §3.2; White *Graphs, Groups and Surfaces* §6.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Graphplay.Weighted

universe u v

namespace Graphplay

/-! ## Rotation systems -/

/-- A **rotation system** on a vertex type `V`: each vertex `v` carries a
permutation `rot v` of the half-edges (darts) incident to `v`.  We do not
embed the incidence relation here; that is the role of `CombinatorialMap`
below, where the darts at `v` form a single `ρ`-cycle. -/
structure RotationSystem (V : Type u) [Fintype V] [DecidableEq V]
    (E : Type v) [Fintype E] [DecidableEq E] where
  /-- The rotation permutation at each vertex. -/
  rot : V → Equiv.Perm E

namespace RotationSystem

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {E : Type v} [Fintype E] [DecidableEq E]

/-- The half-edges (darts) lying in the support of the rotation at `v`. -/
def incidentDarts (R : RotationSystem V E) (v : V) : Finset E :=
  (R.rot v).support

end RotationSystem

/-! ## Combinatorial maps (half-edge model) -/

/-- A **combinatorial map** (oriented embedding) on dart set `E` with vertex
set `V`:

* `σ : Equiv.Perm E` is the edge involution — `σ² = 1` with no fixed points,
  pairing the two darts of each edge.
* `ρ : Equiv.Perm E` is the global rotation — its cycles are the
  *vertex rotations*, and each cycle is indexed by a unique vertex via `vert`.

The faces are then the cycles of `ρ ∘ σ`, and the Euler-genus formula

  `V - E/2 + F = 2 - 2g`

determines the orientable genus. -/
structure CombinatorialMap (V : Type u) [Fintype V] [DecidableEq V]
    (E : Type v) [Fintype E] [DecidableEq E] where
  /-- Edge involution: pairs the two darts of each edge. -/
  σ : Equiv.Perm E
  /-- Global rotation: the cycle through `e` is the cyclic order at the vertex
  incident to `e`. -/
  ρ : Equiv.Perm E
  /-- `σ` is an involution. -/
  σ_involutive : σ * σ = 1
  /-- `σ` has no fixed points (every dart has a distinct partner). -/
  σ_no_fixed : ∀ e : E, σ e ≠ e
  /-- The vertex incident to a dart. -/
  vert : E → V
  /-- `vert` is constant along ρ-cycles. -/
  vert_rot : ∀ e : E, vert (ρ e) = vert e

namespace CombinatorialMap

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {E : Type v} [Fintype E] [DecidableEq E]

/-- The face permutation `φ := ρ ∘ σ`. Its cycles are the *faces*. -/
def facePerm (M : CombinatorialMap V E) : Equiv.Perm E :=
  M.ρ * M.σ

/-- The cycles of `ρ ∘ σ` are the **faces** of the embedding.  Note that fixed
points of `facePerm` are *not* in `cycleFactorsFinset`; they are 1-cycles
(monogons) and are counted separately by `numFaces`. -/
def faceCycles (M : CombinatorialMap V E) : Finset (Equiv.Perm E) :=
  M.facePerm.cycleFactorsFinset

/-- Darts that are fixed by `facePerm`; each such dart bounds a *monogon* face
on its own. -/
def faceFixedPoints (M : CombinatorialMap V E) : Finset E :=
  (Finset.univ : Finset E).filter (fun e => M.facePerm e = e)

/-- Number of faces of the embedding: non-trivial face cycles plus monogons. -/
def numFaces (M : CombinatorialMap V E) : ℕ :=
  M.faceCycles.card + M.faceFixedPoints.card

/-- Number of (undirected) edges: each edge contributes two darts. -/
def numEdges (M : CombinatorialMap V E) : ℕ :=
  Fintype.card E / 2

/-- Number of vertices. -/
def numVertices (_ : CombinatorialMap V E) : ℕ :=
  Fintype.card V

/-- **Euler characteristic** `V - E + F`. -/
def eulerChar (M : CombinatorialMap V E) : ℤ :=
  (M.numVertices : ℤ) - (M.numEdges : ℤ) + (M.numFaces : ℤ)

/-- **Orientable genus**: `g = (2 - χ) / 2`.  For a *valid* (i.e. connected,
cellular) embedding, `eulerChar` is even and `≤ 2`. -/
def genus (M : CombinatorialMap V E) : ℤ :=
  (2 - M.eulerChar) / 2

/-! ### Underlying graph extraction -/

/-- Two vertices are adjacent in the underlying simple graph iff there is a
dart `e` at `u` whose σ-partner is at `v`, and `u ≠ v` (we discard loops). -/
def Adj (M : CombinatorialMap V E) (u v : V) : Prop :=
  u ≠ v ∧ ∃ e : E, M.vert e = u ∧ M.vert (M.σ e) = v

instance (M : CombinatorialMap V E) : DecidableRel M.Adj := by
  intro u v
  unfold Adj
  classical
  exact inferInstance

/-- Underlying simple graph: adjacent vertices share an edge (`σ`-paired
darts on different vertices). -/
def toSimpleGraph (M : CombinatorialMap V E) : SimpleGraph V where
  Adj := M.Adj
  symm := by
    classical
    intro u v ⟨hne, e, hu, hv⟩
    refine ⟨hne.symm, M.σ e, hv, ?_⟩
    have : M.σ (M.σ e) = e := by
      have h := congrArg (fun (g : Equiv.Perm E) => g e) M.σ_involutive
      simpa [Equiv.Perm.mul_apply] using h
    simp [this, hu]
  loopless := ⟨fun _ hv => hv.1 rfl⟩

instance (M : CombinatorialMap V E) : DecidableRel M.toSimpleGraph.Adj :=
  fun u v => (inferInstance : Decidable (M.Adj u v))

/-- Underlying weighted graph (0/1 adjacency). -/
noncomputable def toWeightedGraph (M : CombinatorialMap V E) : WeightedGraph V :=
  Graphplay.SimpleGraph.toWeighted (toSimpleGraph M)

/-! ## Basic properties -/

/-- Every edge is shared by exactly two darts. -/
theorem σ_pairs_two_darts (M : CombinatorialMap V E) :
    ∀ e : E, M.σ (M.σ e) = e := by
  intro e
  have h := congrArg (fun (g : Equiv.Perm E) => g e) M.σ_involutive
  simpa [Equiv.Perm.mul_apply] using h

/-- The number of darts equals twice the number of edges (assuming `E` has
even cardinality, which follows from `σ` being a fixed-point-free involution
on a finite set). -/
theorem card_E_eq_two_mul_numEdges (M : CombinatorialMap V E) :
    Fintype.card E = 2 * M.numEdges := by
  -- `σ` is a fixed-point-free involution, so its support is all of `E` and its
  -- cycle type consists entirely of 2-cycles; hence `Fintype.card E` is even.
  classical
  -- `σ` has no fixed points, so its support is the whole dart set.
  have hsupp : M.σ.support = (Finset.univ : Finset E) := by
    rw [Finset.eq_univ_iff_forall]
    intro e
    exact Equiv.Perm.mem_support.mpr (M.σ_no_fixed e)
  -- `σ ^ 2 = σ * σ = 1`.
  have hsq : M.σ ^ 2 = 1 := by
    rw [pow_two]; exact M.σ_involutive
  -- Therefore `2 ∣ #support = card E`.
  have hdvd : 2 ∣ Fintype.card E := by
    have h := Equiv.Perm.two_dvd_card_support hsq
    rwa [hsupp, Finset.card_univ] at h
  -- `card E = 2 * (card E / 2) = 2 * numEdges`.
  unfold numEdges
  exact (Nat.mul_div_cancel' hdvd).symm

/-- **Euler-Poincaré identity for orientable embeddings.**  When the
combinatorial map represents a connected cellular embedding on the orientable
surface of genus `g`, `V - E + F = 2 - 2g`.  Stated, not proved. -/
theorem eulerChar_eq (M : CombinatorialMap V E) :
    M.eulerChar = 2 - 2 * M.genus := by
  sorry

/-- The face cycles partition the dart set together with the fixed-point set
of `ρ ∘ σ`. -/
theorem darts_partition_by_faces (M : CombinatorialMap V E) :
    (M.faceCycles.sum (fun c => c.support.card)) + M.faceFixedPoints.card
      = Fintype.card E := by
  sorry

/-- Each face cycle is in fact a cycle (non-trivial cyclic permutation). -/
theorem faceCycles_isCycle (M : CombinatorialMap V E) :
    ∀ c ∈ M.faceCycles, c.IsCycle := by
  intro c hc
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1

/-- `numFaces` is the total number of `(ρ ∘ σ)`-orbits, including monogons. -/
theorem numFaces_pos (M : CombinatorialMap V E) [Nonempty E] :
    1 ≤ M.numFaces := by
  sorry

/-! ## Convenience constructors -/

/-- Build a combinatorial map from per-vertex rotations and a dart-to-vertex
labelling, when the rotation at each vertex is given explicitly and the darts
incident to `v` are exactly `vert ⁻¹' {v}`. -/
noncomputable def ofPerVertexRotations
    (vert : E → V) (σ : Equiv.Perm E)
    (rotations : V → Equiv.Perm E)
    (hσ_inv : σ * σ = 1) (hσ_no_fix : ∀ e, σ e ≠ e)
    (h_rot_supp : ∀ v e, (rotations v) e ≠ e → vert e = v)
    (h_rot_compat : ∀ v e, vert e = v → vert ((rotations v) e) = v) :
    CombinatorialMap V E :=
  let ρ : Equiv.Perm E :=
    { toFun := fun e => (rotations (vert e)) e
      invFun := fun e => (rotations (vert e))⁻¹ e
      left_inv := by
        intro e
        have hv : vert ((rotations (vert e)) e) = vert e := by
          by_cases h : (rotations (vert e)) e = e
          · simp [h]
          · exact h_rot_compat _ _ rfl
        simp [hv]
      right_inv := by
        intro e
        show (rotations (vert ((rotations (vert e))⁻¹ e))) ((rotations (vert e))⁻¹ e) = e
        -- Let `e' = (rotations (vert e))⁻¹ e`.  We first show `vert e' = vert e`:
        -- either `e' = e` (then immediate), or `rotations (vert e)` moves `e'`
        -- (it sends `e'` to `e ≠ e'`), so by `h_rot_supp`, `vert e' = vert e`.
        -- `g (g⁻¹ x) = x` for any permutation `g`, via `g * g⁻¹ = 1`.
        have cancel : ∀ (g : Equiv.Perm E) (x : E), g (g⁻¹ x) = x := by
          intro g x
          have h := congrArg (fun (p : Equiv.Perm E) => p x) (mul_inv_cancel g)
          simpa [Equiv.Perm.mul_apply] using h
        have hv : vert ((rotations (vert e))⁻¹ e) = vert e := by
          by_cases h : (rotations (vert e))⁻¹ e = e
          · rw [h]
          · refine h_rot_supp (vert e) _ ?_
            -- `rotations (vert e)` sends `e'` to `e`, and `e ≠ e'`.
            rw [cancel]
            exact fun heq => h heq.symm
        -- With `vert e' = vert e`, the outer rotation cancels the inverse.
        rw [hv]
        exact cancel (rotations (vert e)) e }
  { σ := σ
    ρ := ρ
    σ_involutive := hσ_inv
    σ_no_fixed := hσ_no_fix
    vert := vert
    vert_rot := by
      intro e
      show vert ((rotations (vert e)) e) = vert e
      by_cases h : (rotations (vert e)) e = e
      · simp [h]
      · exact h_rot_compat _ _ rfl }

/-! ## Small concrete examples (smoke tests)

The single-edge map: `V = Fin 2`, `E = Fin 2`, `σ = swap`, `ρ = id`.
This is `K_2` embedded on the sphere: V=2, E=1, F=1, χ=2, g=0. -/

/-- Single-edge sphere embedding `K_2 ↪ S²`. -/
def K2OnSphere : CombinatorialMap (Fin 2) (Fin 2) where
  σ := Equiv.swap 0 1
  ρ := 1
  σ_involutive := by
    ext x; fin_cases x <;> simp [Equiv.swap_apply_def]
  σ_no_fixed := by
    intro e; fin_cases e <;> decide
  vert := id
  vert_rot := by intro e; rfl

/-- `#eval K2OnSphere.numVertices  -- 2` -/
example : K2OnSphere.numVertices = 2 := by decide

/-- `#eval K2OnSphere.numEdges  -- 1` -/
example : K2OnSphere.numEdges = 1 := by decide

end CombinatorialMap

end Graphplay
