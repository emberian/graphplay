/-
# Graphplay.Examples.KleinBottle

The **Klein bottle** is the closed non-orientable surface of
non-orientable genus `2` (or "demigenus 2"), with Euler characteristic `0`,
just like the torus.  Combinatorial maps as defined in
`Graphplay/CombinatorialMap.lean` model only *orientable* embeddings; to
encode a Klein-bottle embedding we need a *signed rotation system*,
adjoining to each edge an orientation-reversal flag (the "twist" or
"signature").

This file introduces a lightweight `SignedCombinatorialMap` structure
(placeholder — the face-cycle computation requires walking signed faces
rather than the orbits of `ρ ∘ σ`), together with one concrete example: the
standard 4-vertex Klein-bottle map obtained by identifying opposite sides
of a square with one pair reversed.

We do *not* attempt to compute faces or genus in the non-orientable case
here; that needs a small extension to the orbit machinery.  We only:

* introduce the type `SignedCombinatorialMap`,
* expose the example,
* state the expected Euler characteristic.

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

/-- The underlying (oriented) combinatorial map. -/
def underlying (M : SignedCombinatorialMap V E) : CombinatorialMap V E :=
  M.toCombinatorialMap

/-- Number of negative (orientation-reversing) edges, counted by σ-orbits.
A map is *orientable* iff this is `0` modulo orientation-equivalence; the
Klein bottle has a representation with a single negative-edge twist. -/
def numNegativeEdges (M : SignedCombinatorialMap V E) : ℕ :=
  ((Finset.univ : Finset E).filter (fun e => M.sign e = false)).card / 2

/-- For a *signed* combinatorial map, the face computation must walk along
signed faces rather than orbits of `ρ ∘ σ`.  We leave this as `sorry` here;
the Klein-bottle Euler characteristic of `0` is asserted as the expected
value. -/
def numFacesSigned (_ : SignedCombinatorialMap V E) : ℕ := sorry

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

/-- The Klein bottle has non-orientable genus `2` (and Euler char `0`).
We do not attempt to prove this from the signed map structure here; it is
recorded as the expected outcome of a proper signed-face computation. -/
theorem klein_eulerChar : SignedCombinatorialMap.eulerCharSigned kleinMap
    = expectedEulerChar := by
  -- Requires `numFacesSigned`, which is `sorry`.
  sorry

end KleinBottle
end Examples
end Graphplay
