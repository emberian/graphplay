/-
# Graphplay.Loopy

**The loopless-free Hermitian layer.**

This module resolves *structural blocker #2*: the `WeightedGraph` structure of
`Graphplay.Weighted` bakes in a zero-diagonal (`loopless`) constraint, which is
the right model for the standard quantum-walk Hamiltonian but is *wrong* for
several objects that legitimately carry a nonzero diagonal:

* the **symmetric quotient** `Q̃ = D^{1/2} Q D^{-1/2}` of an equitable
  partition (its diagonal records the fiber regularity degrees `d i`), so a
  quotient of a loopless graph is generally *not* loopless;
* the **Laplacian** `L = D − A` (diagonal entries are the vertex degrees);
* **self-loop / lackadaisical** continuous-time walks
  (cf. arXiv:1409.5840 Wong, arXiv:1706.06939, arXiv:1508.05458).

`LoopyWeightedGraph` is identical to `WeightedGraph` but **without** the
`loopless` field.  Crucially, *all* of the evolution theory of `WeightedGraph`
(`evolve_zero/neg/add/conjTranspose/unitary/unitary'/normal`) only ever uses
the Hermiticity field `herm` — never `loopless` — so those proofs port
verbatim to this layer.

We also provide:

* `IsLoopyPST`, matching the index convention of `Graphplay.IsPST`;
* `toLoopy : WeightedGraph V → LoopyWeightedGraph V`, the forgetful embedding,
  with `toLoopy_evolve` and `isLoopyPST_toLoopy_iff` definitional bridges;
* `laplacian : WeightedGraph V → LoopyWeightedGraph V`, the Hermitian
  Laplacian `diag (Re (degree v)) − A`.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Graphplay.Weighted
import Graphplay.PST

open scoped Matrix
open NormedSpace

universe u

namespace Graphplay

/-- A **loopy weighted graph** on a finite vertex type `V` is a Hermitian
complex matrix, with **no** zero-diagonal constraint.  This is the natural home
of the symmetric quotient `Q̃`, the Laplacian `L = D − A`, and self-loop /
lackadaisical walks — all of which carry a nonzero diagonal.

The Hermiticity field alone suffices for the entire continuous-time evolution
theory `U(t) = exp(-i t A)` (unitarity, semigroup law, etc.), so this layer is
strictly more general than `WeightedGraph` while retaining all of its quantum
walk machinery. -/
structure LoopyWeightedGraph (V : Type u) [Fintype V] [DecidableEq V] where
  /-- The (Hermitian) adjacency matrix.  No loopless constraint. -/
  adj : Matrix V V ℂ
  /-- Hermiticity of the adjacency matrix. -/
  herm : adj.IsHermitian

namespace LoopyWeightedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The continuous-time quantum walk: `U(t) = exp(-i t A)`.  Identical to
`WeightedGraph.evolve`, but on the loopless-free layer. -/
noncomputable def evolve (G : LoopyWeightedGraph V) (t : ℝ) : Matrix V V ℂ :=
  NormedSpace.exp (-(Complex.I * (t : ℂ)) • G.adj)

/-! ### Properties of the continuous-time quantum walk.

These are copied verbatim from `Graphplay.WeightedGraph`; each proof uses only
the `herm` field, never any zero-diagonal hypothesis, so it ports unchanged. -/

/-- `evolve` at time zero is the identity. -/
theorem evolve_zero (G : LoopyWeightedGraph V) : G.evolve 0 = (1 : Matrix V V ℂ) := by
  unfold evolve
  simp [NormedSpace.exp_zero]

/-- The negative time evolution is the inverse of the positive: the core
"unitarity" identity `U(-t) = U(t)⁻¹`. -/
theorem evolve_neg (G : LoopyWeightedGraph V) (t : ℝ) :
    G.evolve (-t) = (G.evolve t)⁻¹ := by
  unfold evolve
  rw [← Matrix.exp_neg]
  congr 1
  push_cast
  module

/-- The semigroup law: `U(s + t) = U(s) · U(t)`. -/
theorem evolve_add (G : LoopyWeightedGraph V) (s t : ℝ) :
    G.evolve (s + t) = G.evolve s * G.evolve t := by
  unfold evolve
  have hcomm : Commute (-(Complex.I * (s : ℂ)) • G.adj) (-(Complex.I * (t : ℂ)) • G.adj) :=
    ((Commute.refl G.adj).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hcomm]
  congr 1
  push_cast
  module

/-- Each `evolve t` is the conjugate-transpose of `evolve (-t)`.  Together with
`evolve_neg` this is unitarity. -/
theorem evolve_conjTranspose (G : LoopyWeightedGraph V) (t : ℝ) :
    (G.evolve t)ᴴ = G.evolve (-t) := by
  unfold evolve
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, G.herm.eq]
  congr 1
  have : (starRingEnd ℂ) (-(Complex.I * (t : ℂ))) = -(Complex.I * ((-t : ℝ) : ℂ)) := by
    push_cast
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [starRingEnd_apply] at this ⊢
  rw [this]

/-- **Unitarity** of the evolution operator: `U(t)ᴴ * U(t) = 1`. -/
theorem evolve_unitary (G : LoopyWeightedGraph V) (t : ℝ) :
    (G.evolve t)ᴴ * G.evolve t = (1 : Matrix V V ℂ) := by
  rw [evolve_conjTranspose]
  calc (G.evolve (-t)) * G.evolve t
      = G.evolve ((-t) + t) := (G.evolve_add (-t) t).symm
    _ = G.evolve 0 := by rw [show (-t : ℝ) + t = 0 by ring]
    _ = 1 := G.evolve_zero

/-- The other side of unitarity: `U(t) * U(t)ᴴ = 1`. -/
theorem evolve_unitary' (G : LoopyWeightedGraph V) (t : ℝ) :
    G.evolve t * (G.evolve t)ᴴ = (1 : Matrix V V ℂ) := by
  rw [evolve_conjTranspose]
  calc G.evolve t * G.evolve (-t)
      = G.evolve (t + (-t)) := (G.evolve_add t (-t)).symm
    _ = G.evolve 0 := by rw [show t + (-t) = 0 by ring]
    _ = 1 := G.evolve_zero

/-- The evolution operator is normal: it commutes with its adjoint. -/
theorem evolve_normal (G : LoopyWeightedGraph V) (t : ℝ) :
    G.evolve t * (G.evolve t)ᴴ = (G.evolve t)ᴴ * G.evolve t := by
  rw [G.evolve_unitary t, G.evolve_unitary' t]

/-- Perfect state transfer on a loopy weighted graph between vertices `u` and
`v` at time `τ`: the modulus of the `(u, v)`-entry of `U(τ)` is one.  This
matches the index convention of `Graphplay.IsPST` (`‖G.evolve τ u v‖ = 1`). -/
def IsLoopyPST (G : LoopyWeightedGraph V) (u v : V) (τ : ℝ) : Prop :=
  ‖G.evolve τ u v‖ = 1

end LoopyWeightedGraph

/-! ### Forgetful embedding `WeightedGraph → LoopyWeightedGraph`. -/

/-- The forgetful embedding: a (loopless) `WeightedGraph` is in particular a
loopy one, by simply dropping the `loopless` field. -/
def WeightedGraph.toLoopy {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : LoopyWeightedGraph V :=
  ⟨G.adj, G.herm⟩

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The embedding preserves evolution, definitionally. -/
@[simp] theorem WeightedGraph.toLoopy_evolve (G : WeightedGraph V) (t : ℝ) :
    G.toLoopy.evolve t = G.evolve t := rfl

/-- PST on the embedded loopy graph is the same proposition as PST on the
original weighted graph. -/
theorem WeightedGraph.isLoopyPST_toLoopy_iff (G : WeightedGraph V) (u v : V) (τ : ℝ) :
    G.toLoopy.IsLoopyPST u v τ ↔ IsPST G u v τ := Iff.rfl

/-! ### The Laplacian as a loopy weighted graph.

`L = D − A` where `D = diag (Re (degree v))`.  Using the real part of the
weighted degree makes the diagonal automatically real, hence the diagonal block
is Hermitian with no extra hypothesis; for a graph whose degrees are real
(e.g. any `SimpleGraph.toWeighted`) this equals the usual Laplacian. -/

/-- The **Laplacian** `L = D − A` of a weighted graph, as a loopy weighted
graph.  `D` is the diagonal matrix of the real parts of the weighted degrees.
The diagonal of real entries is Hermitian, and `A` is Hermitian, so `L` is
Hermitian. -/
noncomputable def WeightedGraph.laplacian (G : WeightedGraph V) :
    LoopyWeightedGraph V where
  adj := Matrix.diagonal (fun v => ((G.degree v).re : ℂ)) - G.adj
  herm := by
    -- A diagonal matrix of real entries is Hermitian, and `A` is Hermitian,
    -- so their difference is.
    have hdiag : (Matrix.diagonal (fun v => ((G.degree v).re : ℂ))).IsHermitian := by
      apply Matrix.isHermitian_diagonal_iff.mpr
      intro v
      -- each `(·.re : ℂ)` is self-adjoint via `Complex.conj_ofReal`.
      rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
    exact hdiag.sub G.herm

/-- The Laplacian of a `d`-regular weighted graph (with real degree `d`) has
constant diagonal `d`: every diagonal entry equals `(d.re : ℂ)`. -/
theorem WeightedGraph.laplacian_diagonal_of_regular (G : WeightedGraph V) (d : ℂ)
    (hreg : G.isRegular d) (v : V) :
    G.laplacian.adj v v = (d.re : ℂ) := by
  -- Off-diagonal of `A` at `(v, v)` is `0` by looplessness, and `degree v = d`.
  show (Matrix.diagonal (fun v => ((G.degree v).re : ℂ)) - G.adj) v v = (d.re : ℂ)
  rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, hreg v, G.loopless v, sub_zero]

end Graphplay
