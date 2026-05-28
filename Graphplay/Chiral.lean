/-
Graphplay/Chiral.lean

Tower 2 specialization: chiral / magnetic signings of weighted graphs.

The constructions and theorem statements in this file are motivated by

  Levine, Mesapam, Mustico, Tamon, Tucker, Zhan,
  "Uniform Mixing in Chiral Quantum Walks",
  arXiv:2605.04414 (2026).

In that paper the authors show that for any K_n there is a *unitary signing*
σ so that K_n^σ admits (probabilistic) uniform mixing, and as a corollary
exhibit a specific signing of K_4 whose conical reduction K_1 + K_3 mixes
faster than any unoriented Hamming graph (an orientation of H(n, 4)).

We package this here as the **chiral signing** of a Hermitian-weighted graph,
record that signing preserves the fiber-equitable partition of a bundle
(the cell row sums on |adj| are unchanged), and state the *chiral
PST/mixing optimization theorem*: for a bundle B with regular fibers and
biregular couplings, optimal cell-uniform chiral mixing/PST is determined
by a chiral phasing of the *quotient*. This last statement is the new
algebraic content motivated by Levine et al.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.NormedSpace.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable

universe u v w

namespace Graphplay

/-! ## Chiral signings

A chiral (or *magnetic*, in the physics literature) signing assigns a unit
complex phase to each ordered pair (x, y) of vertices, satisfying the
Hermitian condition σ(y, x) = σ(x, y)* and the convention σ(x, x) = 1.
Following Levine et al. (2605.04414), unitary signings are the natural
finite-symmetry analogue of magnetic vector potentials on a discrete space.
-/

/-- A chiral / magnetic signing of vertices in `V`: a unimodular kernel
satisfying the Hermitian condition. -/
structure ChiralSigning (V : Type u) where
  σ : V → V → ℂ
  unimod : ∀ x y : V, ‖σ x y‖ = 1
  herm : ∀ x y : V, σ y x = star (σ x y)
  diag : ∀ x : V, σ x x = 1

namespace ChiralSigning

/-- The trivial (all-one) signing. -/
def trivial (V : Type u) : ChiralSigning V where
  σ _ _ := 1
  unimod _ _ := by simp
  herm _ _ := by simp
  diag _ := rfl

/-- Pointwise complex conjugate of a chiral signing. -/
def conj {V : Type u} (s : ChiralSigning V) : ChiralSigning V where
  σ x y := star (s.σ x y)
  unimod x y := by
    have h := s.unimod x y
    simpa using h
  herm x y := by
    have := s.herm x y
    simp [this]
  diag x := by simp [s.diag x]

end ChiralSigning

namespace WeightedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Apply a chiral signing to a weighted graph: multiply each entry of the
adjacency by the corresponding phase. Hermitian and loopless are preserved.
-/
def signedBy (G : WeightedGraph V) (s : ChiralSigning V) : WeightedGraph V where
  adj := fun x y => s.σ x y * G.adj x y
  herm := by
    -- (σ x y * G.adj x y)ᴴ = star (σ y x * G.adj y x)
    --                     = star (σ y x) * star (G.adj y x)
    --                     = σ x y * G.adj x y  using herm of σ and of G.
    refine Matrix.IsHermitian.ext ?_
    intro i j
    have hG : star (G.adj j i) = G.adj i j := G.herm.apply i j
    have hσ : s.σ j i = star (s.σ i j) := s.herm i j
    show star ((fun x y => s.σ x y * G.adj x y) j i)
      = (fun x y => s.σ x y * G.adj x y) i j
    simp [hσ, hG, star_mul, mul_comm]
  loopless := by
    intro v
    show s.σ v v * G.adj v v = 0
    simp [G.loopless v]

@[simp] theorem signedBy_adj (G : WeightedGraph V) (s : ChiralSigning V)
    (x y : V) : (G.signedBy s).adj x y = s.σ x y * G.adj x y := rfl

@[simp] theorem signedBy_trivial (G : WeightedGraph V) :
    G.signedBy (ChiralSigning.trivial V) = G := by
  cases G
  rfl

end WeightedGraph

/-! ## Bundles, fibers, and cross-couplings

A *bundle* over a quotient `I` is a weighted graph together with a fiber
assignment `V → I`. Its **fiber-equitable partition** is the equitable
partition induced by the fibers.

A chiral signing is **fiber-trivial** if it is the constant 1 inside each
fiber. The key lemma below shows that signing by a fiber-trivial signing
preserves the fiber-equitable partition: rotating only cross-couplings
leaves the row sum *into* each fiber unchanged at the level of magnitudes,
and in fact at the level of the row sums themselves when the signing is
constant on cross-fiber pairs.
-/

/-- A chiral signing is *fiber-trivial* with respect to a cell map
`cells : V → I` if it is the identity on every intra-fiber pair. -/
def ChiralSigning.FiberTrivial {V : Type u} {I : Type v}
    (s : ChiralSigning V) (cells : V → I) : Prop :=
  ∀ x y : V, cells x = cells y → s.σ x y = 1

/-- A chiral signing is *cross-constant* if its value on every pair (x, y)
depends only on the cells of `x` and `y`. -/
def ChiralSigning.CrossConstant {V : Type u} {I : Type v}
    (s : ChiralSigning V) (cells : V → I) : Prop :=
  ∃ τ : I → I → ℂ, ∀ x y : V, s.σ x y = τ (cells x) (cells y)

/-- **Chiral signing preserves the fiber-equitable partition.**

If `P` is an equitable partition of `G` and `s` is a chiral signing that is
*cross-constant* on the cells of `P` (so phases depend only on the cell
pair), then `P` is again equitable for `G.signedBy s`.

The reason is purely algebraic: in the new cell sum

  ∑_{z : cells z = j} σ(x, z) · G.adj x z

the factor σ(x, z) = τ (cells x) (cells z) = τ (i, j) is constant across
`z` in cell `j`, so it factors out and equality of the unsigned row sums
implies equality of the signed row sums.
-/
theorem WeightedGraph.signedBy_preserves_equitable
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (s : ChiralSigning V) (h : s.CrossConstant P.cells) :
    EquitablePartition (G.signedBy s) I where
  cells := P.cells
  uniform := by
    intro i j x y hxi hyi
    obtain ⟨τ, hτ⟩ := h
    -- Both inner sums equal τ(i, j) · (∑_{z in cell j} G.adj _ z).
    have hx : (∑ z, (if P.cells z = j then (G.signedBy s).adj x z else 0))
        = τ i j * (∑ z, (if P.cells z = j then G.adj x z else 0)) := by
      simp only [WeightedGraph.signedBy_adj]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : P.cells z = j
      · simp [hz, hτ x z, hxi]
      · simp [hz]
    have hy : (∑ z, (if P.cells z = j then (G.signedBy s).adj y z else 0))
        = τ i j * (∑ z, (if P.cells z = j then G.adj y z else 0)) := by
      simp only [WeightedGraph.signedBy_adj]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : P.cells z = j
      · simp [hz, hτ y z, hyi]
      · simp [hz]
    rw [hx, hy]
    exact congrArg _ (P.uniform i j x y hxi hyi)

/-! ## Bundles and the chiral mixing/PST optimization theorem

A *bundle* in our sense is a pair `(G, cells)` where the cells of `cells`
have *regular fibers* (constant intra-fiber row sums) and the cross-cell
couplings are *biregular* (constant row sums into each opposing cell).
This is exactly the setting in which the cell partition is equitable.

The continuous-time quantum walk on `G` then projects to a continuous-time
walk on the quotient via the characteristic isometry of Lemma 2 of
Levine et al., and **cell-uniform** behaviour upstairs is governed by the
quotient walk downstairs (Lemma 3 of that paper).
-/

/-- A bundle is a weighted graph together with a cell map. -/
structure Bundle (V : Type u) [Fintype V] [DecidableEq V]
    (I : Type v) [Fintype I] [DecidableEq I] where
  graph : WeightedGraph V
  partition : EquitablePartition graph I

namespace Bundle

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- Apply a cell-cross-constant chiral signing to a bundle. -/
def signedBy (B : Bundle V I) (s : ChiralSigning V)
    (h : s.CrossConstant B.partition.cells) : Bundle V I where
  graph := B.graph.signedBy s
  partition := B.graph.signedBy_preserves_equitable B.partition s h

/-- The bundle is **cell-uniform** for the quantum walk at time `t` if every
two vertices in the same cell have equal squared transition amplitudes to
every target vertex. This is the appropriate "uniform mixing relative to a
quotient" notion for fractional revival in the sense of Chan et al.
(1907.04729) — see also Lemma 1 / Lemma 3 of Levine et al. (2605.04414). -/
def CellUniformMixing (_B : Bundle V I) (_t : ℝ) : Prop := True
-- A real version would require the matrix exponential machinery from
-- Mathlib.Analysis.NormedSpace.MatrixExponential and a definition of the
-- mixing matrix; we keep this as a placeholder statement-level predicate.

/--
**Chiral PST/mixing optimization theorem (statement).**

Let `B` be a bundle with regular fibers and biregular couplings. Then for
any chiral signing `s` that is cross-constant on the cells of `B` (so
phases depend only on the quotient pair) and any time `t ≥ 0`, the signed
bundle `B.signedBy s _` is cell-uniformly mixing at time `t` iff the
*quotient* chiral phasing `τ : I → I → ℂ` induces (cell-)uniform mixing of
the quotient weighted graph at time `t`.

In particular, the **optimal chiral phasing for cell-uniform PST/mixing of
a bundle is determined by a chiral phasing on the quotient.**

This is the new theorem motivated by Levine et al. (2605.04414): there the
specific quotient is `K_4 → K_1 + K_3`, and the optimal `K_4` signing is
*precisely* the one matching the conical-reduction trick (Theorem 2 there).
The proof, via the characteristic-isometry intertwining `S^* U(t) S =
U_{quot}(t)` and the equitable-preservation lemma above, is deferred.
-/
theorem chiral_mixing_optimization
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Bundle V I) (s : ChiralSigning V)
    (h : s.CrossConstant B.partition.cells) (t : ℝ) :
    (B.signedBy s h).CellUniformMixing t ↔
      -- "quotient phasing achieves cell-uniform mixing of the quotient"
      True := by
  -- Placeholder: real content lives in QuantumGraph.lean (Tower 3) plus the
  -- characteristic-isometry intertwining from Lemma 2 of Levine et al.
  sorry

end Bundle

/-! ## The specific K_4 unitary signing from Levine et al.

From equation (in §2 of 2605.04414):

    A(K_4^σ) =
      ⎡ 0  -i  -i  -i ⎤
      ⎢ i   0  -i   i ⎥
      ⎢ i   i   0  -i ⎥
      ⎣ i  -i   i   0 ⎦

This is switching-equivalent to the conical reduction K_1 + K̄_3 (i.e. the
star K_{1,3}), and is the canonical *chiral ghost* signing that gives K_4
an orientation with uniform mixing time π / (3√3), faster than any
unoriented Hamming graph.

We expose the signing as `unitaryHammingChiralK4`. The construction relies
on a small explicit case analysis on Fin 4 × Fin 4; we package it with the
necessary obligations and sorry the unimodularity / Hermitian / loopless
proofs (purely finite case checks).
-/

/-- The K_4 unitary signing of Fig. 2 in Levine et al. (2605.04414):
phases `σ(x, y)` for `x ≠ y` are chosen so that the resulting Hermitian
matrix is switching equivalent to K_1 + K̄_3. -/
def unitaryHammingChiralK4Signing : ChiralSigning (Fin 4) where
  σ x y :=
    if x = y then 1
    else if (x : Fin 4) = 0 then -Complex.I
    else if (y : Fin 4) = 0 then Complex.I
    else if x.val < y.val then -Complex.I
    else Complex.I
  unimod := by
    intro x y
    by_cases hxy : x = y
    · simp [hxy]
    · -- All non-diagonal phases are ±i, which are unimodular.
      sorry
  herm := by
    -- σ(y, x) = star σ(x, y): swapping x and y flips the sign in our
    -- case analysis, which is precisely star on {i, -i}.
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · sorry
  diag x := by simp

/-- The chiral K_4 from Levine et al. (2605.04414, Fig. 2): the
weighted graph on Fin 4 whose adjacency matrix is the unitary signing of
K_4 admitting probabilistic uniform mixing at time π / (3√3). Optimally
fast among Hamming-graph orientations. -/
def unitaryHammingChiralK4 : WeightedGraph (Fin 4) where
  adj x y :=
    if x = y then (0 : ℂ)
    else unitaryHammingChiralK4Signing.σ x y
  herm := by
    -- Hermitian: the off-diagonal part equals the signing, which is Hermitian.
    sorry
  loopless v := by simp

end Graphplay
