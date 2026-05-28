/-
# Graphplay.StdLib.Hypercube

Standard-library entry for the **Boolean hypercube** `Q_n`, viewed as the
Cayley graph of `(ℤ/2)^n` with the standard generating set of unit vectors.

The hypercube is the canonical example of an integral, distance-regular,
vertex-transitive Cayley graph.  It exhibits:

* **Perfect state transfer (PST)** between any pair of antipodal vertices
  at time `τ = π / 2` (Christandl–Datta–Ekert–Landahl 2004, arXiv:quant-
  ph/0309131, Theorem 2; also Bernasconi–Godsil–Severini 2008,
  arXiv:0801.0686).
* **Uniform mixing** at time `τ = π / 4` (Moore–Russell, *Quantum walks on
  the hypercube*, RANDOM 2002; the closed form
  `M(π/4) = (1/2^n) J` is verified by direct computation on the
  character basis).

We expose the family `Hypercube n : WeightedGraph (Fin (2^n))` (with the
identification `Fin (2^n) ≃ (ℤ/2)^n` left implicit) and state both
primitives.  Proofs are `sorry`-ed.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.Mixing

open scoped Matrix Real
open Real

universe u

namespace Graphplay
namespace StdLib

/-! ## Hamming weight, Boolean cube, and `Fin (2^n) ≃ (ℤ/2)^n` -/

/-- The bit at position `i` of an element of `Fin (2^n)`, viewed as a
length-`n` binary string. -/
def bitOf (n : ℕ) (x : Fin (2^n)) (i : Fin n) : Bool :=
  Nat.testBit x.val i.val

/-- The **Hamming distance** between two elements of `Fin (2^n)`, viewed as
binary strings of length `n`. -/
def hammingDist (n : ℕ) (x y : Fin (2^n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => bitOf n x i ≠ bitOf n y i)).card

/-- The **Boolean hypercube** `Q_n` as a weighted graph on `Fin (2^n)`:
adjacency is `1` between strings of Hamming distance `1`, and `0`
otherwise.  Equivalently, the Cayley graph of `(ℤ/2)^n` with respect to
the standard basis. -/
noncomputable def Hypercube (n : ℕ) : WeightedGraph (Fin (2^n)) where
  adj := fun x y => if hammingDist n x y = 1 then (1 : ℂ) else 0
  herm := by
    -- `hammingDist` is symmetric ⇒ adjacency matrix is real-symmetric ⇒
    -- Hermitian.
    sorry
  loopless := by
    intro v
    -- `hammingDist v v = 0 ≠ 1`.
    sorry

/-- The all-zeros bit-string in `Fin (2^n)` (the **base point** of the
hypercube). -/
def hypercubeOrigin (n : ℕ) : Fin (2^n) :=
  ⟨0, Nat.pos_of_ne_zero (by
    intro h
    have : (2^n : ℕ) > 0 := Nat.pos_pow_of_pos n (by decide)
    omega)⟩

/-- The all-ones bit-string in `Fin (2^n)` (the **antipode** of the origin
on the hypercube): the unique vertex at maximal Hamming distance `n` from
the origin. -/
def hypercubeAntipode (n : ℕ) : Fin (2^n) :=
  ⟨2^n - 1, by
    have h2 : (2^n : ℕ) > 0 := Nat.pos_pow_of_pos n (by decide)
    omega⟩

/-! ## Perfect state transfer at the antipode -/

/-- **Christandl–Datta–Ekert–Landahl (2004) / Bernasconi–Godsil–Severini
(2008).**  The Boolean hypercube `Q_n` admits PST between the origin
`0 = 00…0` and the antipode `1 = 11…1` at time `τ = π / 2`, for every
`n ≥ 1`.

References: arXiv:quant-ph/0309131 §III (the hypercube as the `n`-fold
tensor product of `P_2` PST chains) and arXiv:0801.0686.

Proof sketch: `Hypercube n = ⊕_{k=1}^{n} I ⊗ ⋯ ⊗ X ⊗ ⋯ ⊗ I`, a sum of
`n` commuting tensor factors; hence
`exp(-iτ A) = ⊗_{k=1}^{n} exp(-iτ X)`, and `exp(-iπ/2 · X) = -i X`,
whose `(0,1)`-entry has modulus `1` on each factor. -/
theorem hypercube_PST_antipodal (n : ℕ) (h : 1 ≤ n) :
    IsPST (Hypercube n)
      (hypercubeOrigin n) (hypercubeAntipode n) (Real.pi / 2) := by
  -- Tensor-product decomposition + `exp(-iπ/2 X) = -i X`.
  sorry

/-! ## Uniform mixing -/

/-- **Moore–Russell (RANDOM 2002).**  The Boolean hypercube `Q_n` exhibits
uniform mixing at time `τ = π / 4`, for every `n ≥ 1`.

Reference: *Quantum walks on the hypercube*, Lemma 4.1; the proof passes
to the character (Hadamard) basis, where `A` is diagonal with eigenvalues
`n - 2·|S|` for `S ⊆ {1,…,n}`, and a direct computation gives
`|U(π/4)_{x,y}|^2 = 1 / 2^n` for all `x, y`. -/
theorem hypercube_uniformMixing (n : ℕ) (h : 1 ≤ n) :
    IsUniformMixing (Hypercube n) (Real.pi / 4) := by
  -- Character-basis computation; deferred.
  sorry

/-- Equivalent statement: the **average mixing matrix** of the hypercube
is the all-`1/2^n` constant matrix. -/
theorem hypercube_averageUniformMixing (n : ℕ) (h : 1 ≤ n) :
    IsAverageUniformMixing (Hypercube n) := by
  -- Follows from `hypercube_uniformMixing` plus the fact that uniform
  -- mixing at any time implies average uniform mixing.
  sorry

/-! ## Convenience aliases -/

/-- The 1-cube `Q_1 = K_2`. -/
noncomputable def Q1 : WeightedGraph (Fin 2) := Hypercube 1

/-- The 2-cube `Q_2 = C_4`. -/
noncomputable def Q2 : WeightedGraph (Fin 4) := Hypercube 2

/-- The 3-cube `Q_3`. -/
noncomputable def Q3 : WeightedGraph (Fin 8) := Hypercube 3

/-- PST on `Q_1` between its two vertices at `τ = π / 2`. -/
theorem Q1_PST :
    IsPST Q1 (hypercubeOrigin 1) (hypercubeAntipode 1) (Real.pi / 2) :=
  hypercube_PST_antipodal 1 (by decide)

/-- PST on `Q_3` between antipodes at `τ = π / 2`. -/
theorem Q3_PST :
    IsPST Q3 (hypercubeOrigin 3) (hypercubeAntipode 3) (Real.pi / 2) :=
  hypercube_PST_antipodal 3 (by decide)

/-- Uniform mixing on `Q_2` at `τ = π / 4`. -/
theorem Q2_uniformMixing : IsUniformMixing Q2 (Real.pi / 4) :=
  hypercube_uniformMixing 2 (by decide)

end StdLib
end Graphplay
