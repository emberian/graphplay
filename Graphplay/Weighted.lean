/-
# Graphplay.Weighted

Canonical home of the `WeightedGraph` data type used throughout the Graphplay
formalization.  A weighted graph is a Hermitian complex matrix with zero
diagonal; this is the standard quantum-walk Hamiltonian in the Bachman–Tamon
(arXiv 1108.0339) and Godsil–Guo (perfect-state-transfer) setting.

We provide:

* basic Hermitian / trace lemmas,
* a real-spectrum lemma (Hermitian ⇒ all eigenvalues are real),
* the weighted row sum / `degree`,
* an `isRegular` predicate,
* properties of the continuous-time quantum walk `U(t) = exp(-it·A)`
  (unitarity, `U(0) = 1`, `U(s+t) = U(s) * U(t)`), and
* a `SimpleGraph.toWeighted` bridge for ordinary unweighted graphs.

All proofs that genuinely need Mathlib infrastructure are left as `sorry`,
but the *types and statements* are intended to compile once Mathlib is wired
into the lakefile.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Basic

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay

/-- A **weighted graph** on a finite vertex type `V` is a Hermitian complex
matrix with zero diagonal.  This is the standard form used for continuous-time
quantum walks: the matrix plays the role of the Hamiltonian, the Hermiticity
guarantees unitary evolution, and the loopless condition rules out trivial
self-energies on the vertices. -/
structure WeightedGraph (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The (Hermitian, loopless) adjacency matrix. -/
  adj : Matrix V V ℂ
  /-- Hermiticity of the adjacency matrix. -/
  herm : adj.IsHermitian
  /-- Zero diagonal: there are no loops. -/
  loopless : ∀ v, adj v v = 0

namespace WeightedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The continuous-time quantum walk: `U(t) = exp(-i t A)`. -/
noncomputable def evolve (G : WeightedGraph V) (t : ℝ) : Matrix V V ℂ :=
  NormedSpace.exp (-(Complex.I * (t : ℂ)) • G.adj)

/-- The trace of a `WeightedGraph` adjacency matrix is zero (no loops). -/
theorem trace_eq_zero (G : WeightedGraph V) : G.adj.trace = 0 := by
  simp [Matrix.trace, G.loopless]

/-- Every eigenvalue of a `WeightedGraph` is a real number. This is the
specialization of the Hermitian real-spectrum theorem to weighted graphs:
the eigenvalues returned by `IsHermitian.eigenvalues` are valued in `ℝ`
by construction, and each lies in `spectrum ℝ G.adj`. -/
theorem eigenvalues_mem_real_spectrum (G : WeightedGraph V) (i : V) :
    G.herm.eigenvalues i ∈ spectrum ℝ G.adj :=
  G.herm.eigenvalues_mem_spectrum_real i

/-- The complex spectrum of a Hermitian adjacency matrix is contained in the
image of the real eigenvalues — packaged form of Mathlib's
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`. -/
theorem spectrum_subset_real (G : WeightedGraph V) :
    spectrum ℂ G.adj = (fun (r : ℝ) => (r : ℂ)) '' Set.range G.herm.eigenvalues := by
  -- Follows from `IsHermitian.spectrum_eq_image_range`, modulo a coercion;
  -- requires the Mathlib lemma to be in scope.
  sorry

/-- Weighted **row sum** at vertex `v`: the total signed weight of edges out
of `v`.  For an ordinary (0/1) graph this is the usual vertex degree. -/
noncomputable def degree (G : WeightedGraph V) (v : V) : ℂ :=
  ∑ w, G.adj v w

/-- A weighted graph is **regular** of degree `d` if every vertex has the same
weighted row sum `d`. -/
def isRegular (G : WeightedGraph V) (d : ℂ) : Prop :=
  ∀ v, G.degree v = d

/-- Regularity says that the all-ones vector is an eigenvector of the
adjacency matrix with eigenvalue `d`. -/
theorem isRegular_iff_mulVec_one (G : WeightedGraph V) (d : ℂ) :
    G.isRegular d ↔ ∀ v, (G.adj.mulVec (fun _ => (1 : ℂ))) v = d := by
  unfold isRegular degree
  constructor
  · intro h v
    simpa [Matrix.mulVec, dotProduct] using h v
  · intro h v
    simpa [Matrix.mulVec, dotProduct] using h v

/-- For a weighted graph, the regularity eigenvalue is automatically real. -/
theorem isRegular_eigenvalue_real (G : WeightedGraph V) (d : ℂ)
    (h : G.isRegular d) (hV : Nonempty V) : d.im = 0 := by
  -- `d = degree v` for any `v`; the column sum of a Hermitian matrix is the
  -- complex conjugate of the row sum, so the sum-of-row-and-column-sums is
  -- self-conjugate and equals `2 d` real-coeffwise.  Hermitian-with-zero-diag
  -- forces the row sum to be self-conjugate.  Proof left as `sorry` for
  -- brevity.
  sorry

/-! ### Properties of the continuous-time quantum walk. -/

/-- `evolve` at time zero is the identity. -/
theorem evolve_zero (G : WeightedGraph V) : G.evolve 0 = (1 : Matrix V V ℂ) := by
  unfold evolve
  simp [NormedSpace.exp_zero]

/-- The negative time evolution is the inverse of the positive: this is the
core "unitarity" identity `U(-t) = U(t)⁻¹`. -/
theorem evolve_neg (G : WeightedGraph V) (t : ℝ) :
    G.evolve (-t) = (G.evolve t)⁻¹ := by
  unfold evolve
  -- `-(-(I * t)) = (I * t)` and `Matrix.exp_neg` from Mathlib.
  sorry

/-- The semigroup law: `U(s + t) = U(s) · U(t)`. -/
theorem evolve_add (G : WeightedGraph V) (s t : ℝ) :
    G.evolve (s + t) = G.evolve s * G.evolve t := by
  -- Two scalar multiples of the same matrix commute; combine with
  -- `Matrix.exp_add_of_commute`.
  sorry

/-- Each `evolve t` is the conjugate-transpose of `evolve (-t)`.  Together
with `evolve_neg` this is unitarity. -/
theorem evolve_conjTranspose (G : WeightedGraph V) (t : ℝ) :
    (G.evolve t)ᴴ = G.evolve (-t) := by
  unfold evolve
  -- `(-iA)ᴴ = i Aᴴ = i A` for Hermitian A; combine with `Matrix.exp_conjTranspose`.
  sorry

/-- **Unitarity** of the evolution operator: `U(t)ᴴ * U(t) = 1`. -/
theorem evolve_unitary (G : WeightedGraph V) (t : ℝ) :
    (G.evolve t)ᴴ * G.evolve t = (1 : Matrix V V ℂ) := by
  rw [evolve_conjTranspose]
  -- `evolve (-t) * evolve t = evolve ((-t) + t) = evolve 0 = 1`.
  calc (G.evolve (-t)) * G.evolve t
      = G.evolve ((-t) + t) := (G.evolve_add (-t) t).symm
    _ = G.evolve 0 := by rw [show (-t : ℝ) + t = 0 by ring]
    _ = 1 := G.evolve_zero

/-- The other side of unitarity: `U(t) * U(t)ᴴ = 1`. -/
theorem evolve_unitary' (G : WeightedGraph V) (t : ℝ) :
    G.evolve t * (G.evolve t)ᴴ = (1 : Matrix V V ℂ) := by
  rw [evolve_conjTranspose]
  calc G.evolve t * G.evolve (-t)
      = G.evolve (t + (-t)) := (G.evolve_add t (-t)).symm
    _ = G.evolve 0 := by rw [show t + (-t) = 0 by ring]
    _ = 1 := G.evolve_zero

/-- The evolution operator is Hermitian-preserving in the sense that
`evolve t` is normal: it commutes with its adjoint. -/
theorem evolve_normal (G : WeightedGraph V) (t : ℝ) :
    G.evolve t * (G.evolve t)ᴴ = (G.evolve t)ᴴ * G.evolve t := by
  rw [G.evolve_unitary t, G.evolve_unitary' t]

end WeightedGraph

/-! ### Unweighted-to-weighted bridge. -/

namespace SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Promote an ordinary (unweighted) `SimpleGraph` to a `WeightedGraph` by
using the 0/1 adjacency matrix valued in `ℂ`. -/
noncomputable def toWeighted
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : Graphplay.WeightedGraph V where
  adj := G.adjMatrix ℂ
  herm := by
    -- `(G.adjMatrix ℂ)ᴴ = G.adjMatrix ℂ` because the matrix is real-valued
    -- and symmetric.
    unfold Matrix.IsHermitian
    ext i j
    by_cases h : G.Adj j i <;>
      simp [_root_.SimpleGraph.adjMatrix_apply, _root_.SimpleGraph.adj_comm, h]
  loopless := by
    intro v
    simp [_root_.SimpleGraph.adjMatrix_apply, G.loopless]

/-- The bridge sends an unweighted regular graph to a weighted regular graph
with the same (real, hence complex-coerced) degree. -/
theorem toWeighted_isRegular (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, (G.neighborFinset v).card = d) :
    (toWeighted G).isRegular (d : ℂ) := by
  intro v
  unfold Graphplay.WeightedGraph.degree toWeighted
  -- `∑ w, adjMatrix ℂ v w = (G.neighborFinset v).card`.
  sorry

end SimpleGraph

end Graphplay
