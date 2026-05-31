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

/-- The Hamming distance is symmetric. -/
theorem hammingDist_comm (n : ℕ) (x y : Fin (2^n)) :
    hammingDist n x y = hammingDist n y x := by
  unfold hammingDist
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [ne_comm]

/-- The Hamming distance from a vertex to itself is `0`. -/
@[simp] theorem hammingDist_self (n : ℕ) (x : Fin (2^n)) :
    hammingDist n x x = 0 := by
  unfold hammingDist
  simp

/-- The **Boolean hypercube** `Q_n` as a weighted graph on `Fin (2^n)`:
adjacency is `1` between strings of Hamming distance `1`, and `0`
otherwise.  Equivalently, the Cayley graph of `(ℤ/2)^n` with respect to
the standard basis. -/
noncomputable def Hypercube (n : ℕ) : WeightedGraph (Fin (2^n)) where
  adj := fun x y => if hammingDist n x y = 1 then (1 : ℂ) else 0
  herm := by
    -- `hammingDist` is symmetric ⇒ adjacency matrix is real-symmetric ⇒
    -- Hermitian.
    refine Matrix.IsHermitian.ext (fun x y => ?_)
    show star (if hammingDist n y x = 1 then (1 : ℂ) else 0)
        = if hammingDist n x y = 1 then (1 : ℂ) else 0
    rw [hammingDist_comm n y x]
    by_cases h : hammingDist n x y = 1
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp
  loopless := by
    intro v
    -- `hammingDist v v = 0 ≠ 1`.
    rw [hammingDist_self]
    simp

/-- The all-zeros bit-string in `Fin (2^n)` (the **base point** of the
hypercube). -/
def hypercubeOrigin (n : ℕ) : Fin (2^n) :=
  ⟨0, Nat.pos_of_ne_zero (by
    intro h
    have : (2^n : ℕ) > 0 := Nat.two_pow_pos n
    omega)⟩

/-- The all-ones bit-string in `Fin (2^n)` (the **antipode** of the origin
on the hypercube): the unique vertex at maximal Hamming distance `n` from
the origin. -/
def hypercubeAntipode (n : ℕ) : Fin (2^n) :=
  ⟨2^n - 1, by
    have h2 : (2^n : ℕ) > 0 := Nat.two_pow_pos n
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
`|U(π/4)_{x,y}|^2 = 1 / 2^n` for all `x, y`.

HONEST SORRY (residual = ONE named bridge).  The `n = 1` case is fully
computable now: `Hypercube 1 = K₂` (`HypercubeProduct.K2`) and
`HypercubeProduct.exp_smul_X_lit` gives every entry of `U(π/4)` modulus
`2^{-1/2}` (`|cos(π/4)| = |sin(π/4)| = 2^{-1/2}`), so `Q₁` mixes.  The
general `n` reduces to this via the `n`-fold Cartesian product
(`WeightedGraph.evolve_cartesianProduct_apply` makes `U(π/4)` factor
entrywise as `∏ 2^{-1/2} = 2^{-n/2}`), but only after the **missing graph
isomorphism** `Fin (2ⁿ) ≃ HypercubeProduct.HCVert n` (bit-decomposition,
intertwining `hammingDist`-adjacency with the product adjacency) and a
mixing-transport-across-iso lemma are built.  Those two facts are the only
remaining gap; the statement itself is the genuine Moore–Russell result. -/
theorem hypercube_uniformMixing (n : ℕ) (h : 1 ≤ n) :
    IsUniformMixing (Hypercube n) (Real.pi / 4) := by
  -- Residual: `Fin (2ⁿ) ≃ HCVert n` graph iso + mixing transport; base case
  -- `Q₁ = K₂` is closed by `exp_smul_X_lit`.
  sorry

/-- Equivalent statement: the **average mixing matrix** of the hypercube
is the all-`1/2^n` constant matrix. -/
theorem hypercube_averageUniformMixing (n : ℕ) (h : 1 ≤ n) :
    IsAverageUniformMixing (Hypercube n) := by
  -- HONEST SORRY.  WARNING: this does *not* follow from
  -- `hypercube_uniformMixing` — uniform mixing at a single time `τ = π/4`
  -- says nothing about the Cesàro time-average `T⁻¹ ∫₀ᵀ |U(t)_{xy}|² dt`.
  -- The genuine statement requires the average mixing matrix
  -- `M̄_{xy} = ∑_λ ‖E_λ e_x‖² ‖E_λ e_y‖²` (sum over spectral idempotents),
  -- which for the hypercube is uniform `= 1/2ⁿ` because every eigenvalue of
  -- `Q_n` (the integers `n - 2|S|`) has a flat, sign-balanced eigenprojector
  -- in the Hadamard basis.  Concretely the eigenprojector `E_λ` is built from
  -- the product characters `χ_w` (the analogue of `Hamming.hamChi`, here with
  -- `q = 2`, `χ_w(x) = (-1)^{w·x}`, eigenvalue `n - 2·wt(w)` by
  -- `Hamming.hamLambda` at `q = 2`); the Cesàro limit picks out
  -- `∑_w |⟨χ_w, e_x⟩|² |⟨χ_w, e_y⟩|² = ∑_w 2^{-2n} = 2^{-n}`.  Formalizing this
  -- needs (a) the spectral idempotents of `Q_n` and (b) evaluation of the
  -- Cesàro `limUnder` — neither is built on `Fin (2ⁿ)` yet.  The residual is
  -- exactly the average-mixing spectral formula; the statement is the correct,
  -- non-vacuous time-average (NOT a corollary of single-time mixing).
  sorry

/-! ## Computable rational companions -/

/-- Computable companion to `Hypercube n`: the 0/1 adjacency matrix
of the Boolean hypercube `Q_n` on `Fin (2^n)`, valued in `ℚ`. -/
def Hypercube.adjMatrixℚ (n : ℕ) : Matrix (Fin (2^n)) (Fin (2^n)) ℚ :=
  fun x y => if hammingDist n x y = 1 then (1 : ℚ) else 0

/-- The number of edges of `Q_n`, closed form: `n * 2^(n-1)`.
Computable.  (For `n = 0` we adopt the convention `0 * 2^0 = 0`,
matching `Nat.sub` truncation.) -/
def Hypercube.numEdges (n : ℕ) : ℕ := n * 2^(n-1)

/-- Smoke test: `Q_3` has 8 vertices and 12 edges. -/
example : Hypercube.numEdges 3 = 12 := by decide

#eval Hypercube.numEdges 3
#eval Hypercube.numEdges 4
#eval (Hypercube.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨1, by decide⟩
#eval (Hypercube.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨7, by decide⟩
#eval Matrix.trace (Hypercube.adjMatrixℚ 3)

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
