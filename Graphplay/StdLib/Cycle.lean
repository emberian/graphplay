/-
# Graphplay.StdLib.Cycle

Standard-library entry for the **cycle graph** `C_n` on vertex set
`Fin n`.  Vertex `i` is adjacent to `(i + 1) mod n` and `(i - 1) mod n`.

This file is the computable companion in the StdLib aggregator: a
decidable `SimpleGraph` and a rational adjacency matrix that is
`#eval`-able, alongside a noncomputable real eigenvalue formula
`λ_k = 2 cos(2πk/n)` (Brouwer–Haemers, *Spectra of Graphs*, §1.4.4).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open scoped Matrix Real
open Real

universe u

namespace Graphplay
namespace StdLib

/-! ## The cycle graph `C_n` -/

/-- The **cycle graph** `C_n` on `Fin n`: vertex `i` is adjacent to
`(i + 1) mod n` and `(i - 1) mod n` (equivalently to its two neighbours
in cyclic order).  For `n ≤ 2` the graph degenerates (we keep the
combinatorial definition; `C_1` is a self-loop free single vertex and
`C_2` is a multi-edge collapsing to a single edge after de-duplication). -/
def Cycle (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j :=
    i ≠ j ∧
    ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val)
  symm := by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h1 | h2
    · exact Or.inr h1
    · exact Or.inl h2
  loopless := ⟨by intro i h; exact h.1 rfl⟩

instance (n : ℕ) : DecidableRel (Cycle n).Adj := by
  intro i j
  unfold Cycle
  infer_instance

/-! ## Computable rational adjacency -/

/-- Computable companion: the 0/1 adjacency matrix of `Cycle n`
on `Fin n`, valued in `ℚ`. -/
def Cycle.adjMatrixℚ (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j =>
    if i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) then
      (1 : ℚ)
    else 0

/-- Vertex count of `C_n` (trivially `n`). -/
def Cycle.numVertices (n : ℕ) : ℕ := n

/-- Edge count of `C_n`: equals `n` for `n ≥ 3`, equals `0` for `n ≤ 1`,
and equals `1` for `n = 2` (since the two "neighbour" pairs coincide). -/
def Cycle.numEdges : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => n + 3

/-- Each vertex of `C_n` (for `n ≥ 3`) has degree exactly `2`. -/
def Cycle.degree (_n : ℕ) (_v : Unit) : ℕ := 2

/-! ## Eigenvalue formula (noncomputable, for reference) -/

/-- The **eigenvalues** of the cycle `C_n` (Brouwer–Haemers, *Spectra of
Graphs*, §1.4.4):
  `λ_k = 2 cos (2 π k / n)`  for `k = 0, 1, …, n - 1`.
Real-valued; not directly computable in Lean but used in proofs. -/
noncomputable def Cycle.eigenvaluesℝ (n : ℕ) (k : Fin n) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k.val : ℝ) / (n : ℝ))

/-! ## Smoke tests -/

example : Cycle.numVertices 5 = 5 := by decide
example : Cycle.numEdges 5 = 5 := by decide
example : Cycle.numEdges 3 = 3 := by decide
example : (Cycle.adjMatrixℚ 5) ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 := by decide
example : (Cycle.adjMatrixℚ 5) ⟨0, by decide⟩ ⟨4, by decide⟩ = 1 := by decide
example : (Cycle.adjMatrixℚ 5) ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by decide
example : (Cycle.adjMatrixℚ 5) ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by decide

#eval Cycle.numVertices 5
#eval Cycle.numEdges 5
#eval Cycle.degree 5 ()
#eval (Cycle.adjMatrixℚ 5) ⟨0, by decide⟩ ⟨1, by decide⟩
#eval (Cycle.adjMatrixℚ 5) ⟨0, by decide⟩ ⟨4, by decide⟩
#eval (Cycle.adjMatrixℚ 5) ⟨2, by decide⟩ ⟨3, by decide⟩

end StdLib
end Graphplay
