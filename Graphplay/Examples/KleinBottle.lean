/-
# Graphplay.Examples.KleinBottle

The **Klein bottle** is the closed non-orientable surface of
non-orientable genus `2` (or "demigenus 2"), with Euler characteristic `0`,
just like the torus.  Combinatorial maps as defined in
`Graphplay/CombinatorialMap.lean` model only *orientable* embeddings; to
encode a Klein-bottle embedding we need a *signed rotation system*,
adjoining to each edge an orientation-reversal flag (the "twist" or
"signature").

This file introduces a lightweight `SignedCombinatorialMap` structure with
face counting via the orientation double cover (faces are `signedFacePerm`
orbits on `E × Bool`, halved), together with one concrete example: the
1-vertex 2-edge Klein-bottle map obtained by identifying opposite sides
of a square with one pair reversed (`abab⁻¹`).

Main result: `klein_eulerChar` — the signed Euler characteristic of this map
is `0`, proved by exhibiting the explicit two-cycle decomposition of its
signed face permutation on the 8-element double cover.

References: Mohar-Thomassen *Graphs on Surfaces* §3.3; Gross-Tucker
*Topological Graph Theory* §3.2 (signed rotation projection).
-/
import Graphplay.CombinatorialMap
import Graphplay.Bundle

universe u v

namespace Graphplay
namespace Examples
namespace KleinBottle

open CombinatorialMap

/-! ## Signed combinatorial maps (placeholder for non-orientable embeddings) -/

/-- A **signed combinatorial map** is a combinatorial map together with an
edge signature `λ : E → Bool` (with `True` = orientation-preserving,
`False` = orientation-reversing along that edge).  We require `λ` to be
constant on σ-orbits (each undirected edge has one signature). -/
structure SignedCombinatorialMap (V : Type u) [Fintype V] [DecidableEq V]
    (E : Type v) [Fintype E] [DecidableEq E] extends CombinatorialMap V E where
  /-- Edge signature: `True` = positive (orientation-preserving),
  `False` = negative (twist). -/
  sign : E → Bool
  /-- Signs respect the σ-pairing of darts. -/
  sign_σ : ∀ e : E, sign (σ e) = sign e

namespace SignedCombinatorialMap

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {E : Type v} [Fintype E] [DecidableEq E]

/-- `g (g⁻¹ x) = x` for any permutation `g` (via `g * g⁻¹ = 1`). -/
private theorem perm_apply_inv {α : Type _} (g : Equiv.Perm α) (x : α) :
    g (g⁻¹ x) = x := by
  have h := congrArg (fun (p : Equiv.Perm α) => p x) (mul_inv_cancel g)
  simpa [Equiv.Perm.mul_apply] using h

/-- `g⁻¹ (g x) = x` for any permutation `g` (via `g⁻¹ * g = 1`). -/
private theorem perm_inv_apply {α : Type _} (g : Equiv.Perm α) (x : α) :
    g⁻¹ (g x) = x := by
  have h := congrArg (fun (p : Equiv.Perm α) => p x) (inv_mul_cancel g)
  simpa [Equiv.Perm.mul_apply] using h

/-- The underlying (oriented) combinatorial map. -/
def underlying (M : SignedCombinatorialMap V E) : CombinatorialMap V E :=
  M.toCombinatorialMap

/-- Number of negative (orientation-reversing) edges, counted by σ-orbits.
A map is *orientable* iff this is `0` modulo orientation-equivalence; the
Klein bottle has a representation with a single negative-edge twist. -/
def numNegativeEdges (M : SignedCombinatorialMap V E) : ℕ :=
  ((Finset.univ : Finset E).filter (fun e => M.sign e = false)).card / 2

/-! ### Signed face tracing via the orientation double cover.

For an *orientable* combinatorial map the faces are the orbits of `ρ ∘ σ` on
the dart set `E`.  For a *signed* (possibly non-orientable) map one cannot use
`ρ ∘ σ` directly, because crossing a negative edge reverses the local
orientation and hence the *sense* in which the next rotation must be read.

The standard fix (Mohar–Thomassen, *Graphs on Surfaces* §3.3) is the
**orientation double cover**: work on *signed darts* `E × Bool`, where the
`Bool` records the current local orientation (`true` = with the chosen global
orientation, `false` = against it).  Tracing a face boundary is one step of the
permutation

  `φ⁺(e, o) = ( (if o then ρ else ρ⁻¹) (σ e) ,  o `xor` ¬sign(e) )`.

Concretely: cross the edge with `σ`; if the edge is negative, flip the
orientation bit; then advance around the next vertex using `ρ` when the local
orientation is positive and `ρ⁻¹` when it is negative (because a reversed local
orientation reads the rotation backwards).  This is a genuine permutation of
`E × Bool` (its inverse reverses each step).

Each *face* of the embedded graph lifts to exactly **two** orbits of `φ⁺` in
the double cover (the two senses of traversal), so the number of faces is the
number of `φ⁺`-orbits divided by two. -/

/-- **Edge-crossing permutation** on signed darts: `(e, o) ↦ (σ e, o xor ¬sign e)`.
Crossing an edge applies the involution `σ` and flips the local orientation bit
exactly when the edge is negative.  Because `sign (σ e) = sign e` and `σ² = 1`,
this is itself an *involution* of `E × Bool`. -/
def crossEdgePerm (M : SignedCombinatorialMap V E) : Equiv.Perm (E × Bool) where
  toFun := fun x => (M.σ x.1, x.2.xor (!M.sign x.1))
  invFun := fun x => (M.σ x.1, x.2.xor (!M.sign x.1))
  left_inv := by
    intro x
    obtain ⟨e, o⟩ := x
    have hσσ : M.σ (M.σ e) = e := M.toCombinatorialMap.σ_pairs_two_darts e
    have hsign : M.sign (M.σ e) = M.sign e := M.sign_σ e
    simp only [hσσ, hsign, Prod.mk.injEq, true_and]
    cases o <;> cases (M.sign e) <;> rfl
  right_inv := by
    intro x
    obtain ⟨e, o⟩ := x
    have hσσ : M.σ (M.σ e) = e := M.toCombinatorialMap.σ_pairs_two_darts e
    have hsign : M.sign (M.σ e) = M.sign e := M.sign_σ e
    simp only [hσσ, hsign, Prod.mk.injEq, true_and]
    cases o <;> cases (M.sign e) <;> rfl

/-- **Orientation-dependent rotation** on signed darts:
`(e, o) ↦ ((if o then ρ else ρ⁻¹) e, o)`.  The vertex rotation is read forwards
under a positive local orientation and backwards under a negative one; the
orientation bit is untouched.  Its inverse swaps `ρ ↔ ρ⁻¹`. -/
def rotatePerm (M : SignedCombinatorialMap V E) : Equiv.Perm (E × Bool) where
  toFun := fun x => ((if x.2 then M.ρ else M.ρ⁻¹) x.1, x.2)
  invFun := fun x => ((if x.2 then M.ρ⁻¹ else M.ρ) x.1, x.2)
  left_inv := by
    intro x
    obtain ⟨e, o⟩ := x
    cases o <;>
      simp only [if_true, if_false, Prod.mk.injEq, and_true]
    · exact perm_apply_inv M.ρ e
    · exact perm_inv_apply M.ρ e
  right_inv := by
    intro x
    obtain ⟨e, o⟩ := x
    cases o <;>
      simp only [if_true, if_false, Prod.mk.injEq, and_true]
    · exact perm_inv_apply M.ρ e
    · exact perm_apply_inv M.ρ e

/-- **The signed face permutation** on the orientation double cover, as the
composite "cross the edge, then rotate around the next vertex".  Concretely
`signedFacePerm = rotatePerm ∘ crossEdgePerm`, which on a signed dart `(e, o)`
gives `((if o' then ρ else ρ⁻¹) (σ e), o')` with `o' = o xor ¬sign e`.  Being a
product of two permutations, it is automatically invertible. -/
def signedFacePerm (M : SignedCombinatorialMap V E) : Equiv.Perm (E × Bool) :=
  M.rotatePerm * M.crossEdgePerm

/-- **Number of faces of a signed combinatorial map.**  Each face lifts to two
orbits of the orientation-double-cover face permutation `signedFacePerm`, so the
number of faces is the number of distinct `signedFacePerm`-orbits divided by 2.

We count orbits concretely as the number of equivalence classes of the
`Equiv.Perm.SameCycle` relation, realised as the cardinality of the image of the
"orbit representative" map `x ↦ min over the cycle`.  For computability we use
the number of cycles plus fixed points of the permutation, matching the
orientable `numFaces` convention on the double cover. -/
def numFacesSigned (M : SignedCombinatorialMap V E) : ℕ :=
  let φ := M.signedFacePerm
  (φ.cycleFactorsFinset.card +
    ((Finset.univ : Finset (E × Bool)).filter (fun x => φ x = x)).card) / 2

/-- Signed Euler characteristic. -/
def eulerCharSigned (M : SignedCombinatorialMap V E) : ℤ :=
  (Fintype.card V : ℤ) - (Fintype.card E / 2 : ℤ) + (M.numFacesSigned : ℤ)

end SignedCombinatorialMap

/-! ## A Klein-bottle example: 1-vertex, 2-edge map

The simplest Klein-bottle map has a single vertex, two loops, and one face.
The two loops correspond to the two pairs of opposite sides of the square
fundamental polygon `abab⁻¹`: edge `a` is identified head-to-tail (a torus
identification), while edge `b` is identified head-to-head (the twist).

* `V = Unit`, so `|V| = 1`.
* `E_darts` = 4 darts (each loop has 2 darts).
* `|E_edges|` = 2, so `Fintype.card E = 4` and `numEdges = 2`.
* One face (a square wrapped around the fundamental polygon), so `F = 1`.
* `χ = 1 - 2 + 1 = 0` — consistent with the Klein bottle.

We encode this with `E := Fin 4`, σ swapping `0↔1` and `2↔3` (the two
edges), ρ rotating `0 → 2 → 1 → 3 → 0` at the single vertex (the cyclic
order around the vertex on the polygon boundary), and sign `False` on
darts `2,3` (the twisted edge `b`) and `True` on `0,1`. -/

/-- The 1-vertex 2-edge Klein-bottle map (dart set). -/
abbrev V := Unit
abbrev D := Fin 4

/-- σ on the 4 darts: `0↔1`, `2↔3`. -/
def σ_perm : Equiv.Perm D :=
  Equiv.swap 0 1 * Equiv.swap 2 3

/-- ρ on the 4 darts: a 4-cycle `0 → 2 → 1 → 3 → 0` reflecting the corner
sequence `a, b, a⁻¹, b⁻¹` (the Klein-bottle gluing word `abab⁻¹` has the
same cyclic dart sequence at the unique vertex up to relabelling). -/
def ρ_perm : Equiv.Perm D :=
  -- The 4-cycle (0 2 1 3) written as a product of transpositions.
  Equiv.swap 0 2 * Equiv.swap 2 1 * Equiv.swap 1 3

/-- The Klein-bottle (under)lying combinatorial map.  We *can* package it
as `CombinatorialMap`, but `genus` will lie because that formula assumes
orientability. -/
def kleinUnderlying : CombinatorialMap V D where
  σ := σ_perm
  ρ := ρ_perm
  σ_involutive := by
    apply Equiv.Perm.ext
    intro x
    fin_cases x <;> decide
  σ_no_fixed := by
    intro e h
    fin_cases e <;> revert h <;> decide
  vert := fun _ => ()
  vert_rot := by intro e; rfl

/-- The full signed map adds the twist signature. -/
def kleinMap : SignedCombinatorialMap V D :=
  { kleinUnderlying with
    sign := fun e => e.val < 2  -- darts 0,1 positive; 2,3 negative (twisted)
    sign_σ := by
      intro e
      fin_cases e <;> decide }

/-! ## Smoke tests -/

/-- `#eval kleinUnderlying.numVertices  -- 1` -/
example : kleinUnderlying.numVertices = 1 := by decide

/-- `#eval kleinUnderlying.numEdges  -- 2` -/
example : kleinUnderlying.numEdges = 2 := by decide

/-- Two darts are negative (the twisted edge contributes one to the
σ-orbit count). -/
example : kleinMap.numNegativeEdges = 1 := by decide

/-- Expected Euler characteristic of the Klein bottle. -/
def expectedEulerChar : ℤ := 0

/-! ### The explicit cycle decomposition of the signed face permutation

Tracing `signedFacePerm kleinMap` on all eight signed darts of the orientation
double cover `Fin 4 × Bool` yields exactly two disjoint 4-cycles — the two
orientation-reversed lifts of the single `abab⁻¹` face:

* `(0,+) → (3,+) → (0,−) → (2,−) → (0,+)`
* `(1,+) → (2,+) → (1,−) → (3,−) → (1,+)`.

`Equiv.Perm.cycleFactorsFinset` is noncomputable, so instead of `decide` we
exhibit the two cycles as `List.formPerm`s, check the (decidable) equality of
permutations pointwise, and pin the cycle-factor count via the
`Disjoint.cycleFactorsFinset_mul_eq_union` API. -/

/-- First lift of the unique face: the 4-cycle `(0,+) (3,+) (0,−) (2,−)`. -/
def faceCycleA : Equiv.Perm (D × Bool) :=
  [((0 : D), true), ((3 : D), true), ((0 : D), false), ((2 : D), false)].formPerm

/-- Second (orientation-reversed) lift: the 4-cycle `(1,+) (2,+) (1,−) (3,−)`. -/
def faceCycleB : Equiv.Perm (D × Bool) :=
  [((1 : D), true), ((2 : D), true), ((1 : D), false), ((3 : D), false)].formPerm

/-- The signed face permutation of the Klein-bottle map is exactly the product
of the two explicit face-lift cycles. -/
theorem signedFacePerm_eq_cycles :
    kleinMap.signedFacePerm = faceCycleA * faceCycleB :=
  Equiv.ext (by decide)

theorem faceCycleA_isCycle : faceCycleA.IsCycle :=
  List.isCycle_formPerm (by decide) (by decide)

theorem faceCycleB_isCycle : faceCycleB.IsCycle :=
  List.isCycle_formPerm (by decide) (by decide)

theorem faceCycles_disjoint : Equiv.Perm.Disjoint faceCycleA faceCycleB :=
  Equiv.Perm.disjoint_iff_eq_or_eq.mpr (by decide)

/-- The signed face permutation has exactly two cycle factors: the two
orientation-reversed lifts of the single face. -/
theorem klein_cycleFactors_card :
    kleinMap.signedFacePerm.cycleFactorsFinset.card = 2 := by
  rw [signedFacePerm_eq_cycles,
    faceCycles_disjoint.cycleFactorsFinset_mul_eq_union,
    faceCycleA_isCycle.cycleFactorsFinset_eq_singleton,
    faceCycleB_isCycle.cycleFactorsFinset_eq_singleton]
  have hne : faceCycleA ≠ faceCycleB := fun h =>
    absurd (congrArg (fun p => p ((0 : D), true)) h) (by decide)
  simp [hne]

/-- The Klein-bottle map has one face: two `signedFacePerm`-orbits on the
double cover (and no fixed points), halved. -/
theorem klein_numFacesSigned : kleinMap.numFacesSigned = 1 := by
  have hfix : ((Finset.univ : Finset (D × Bool)).filter
      (fun x => kleinMap.signedFacePerm x = x)).card = 0 := by decide
  show (kleinMap.signedFacePerm.cycleFactorsFinset.card +
    ((Finset.univ : Finset (D × Bool)).filter
      (fun x => kleinMap.signedFacePerm x = x)).card) / 2 = 1
  rw [klein_cycleFactors_card, hfix]

/-- The Klein bottle has Euler characteristic `0` (non-orientable genus `2`):
`χ = |V| - |E| + F = 1 - 2 + 1 = 0`, with the face count obtained from the
explicit two-cycle decomposition of the signed face permutation on the
orientation double cover. -/
theorem klein_eulerChar : SignedCombinatorialMap.eulerCharSigned kleinMap
    = expectedEulerChar := by
  show (Fintype.card V : ℤ) - (Fintype.card D / 2 : ℤ)
      + (kleinMap.numFacesSigned : ℤ) = expectedEulerChar
  rw [klein_numFacesSigned]
  rfl

end KleinBottle
end Examples
end Graphplay
