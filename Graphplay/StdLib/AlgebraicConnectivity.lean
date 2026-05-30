/-
# Graphplay.StdLib.AlgebraicConnectivity

**Algebraic connectivity (the Fiedler value) and the genus / embedding upper
bound.**

For a weighted graph `G` with Laplacian `L = D − A`, the **algebraic
connectivity** (Fiedler 1973) is the second-smallest Laplacian eigenvalue
`a(G) = λ₂(L)`.  The smallest Laplacian eigenvalue is always `0` (with the
all-ones eigenvector on a connected graph), and `a(G) > 0` iff `G` is connected;
`a(G)` measures how "well-connected" the graph is.

The Fiedler value has the variational (Courant–Fischer) characterisation as a
**Rayleigh-quotient minimum over vectors orthogonal to the all-ones vector**:

  `a(G) = min { ⟨x, L x⟩ / ⟨x, x⟩ : x ≠ 0, x ⟪⊥⟫ 𝟙 }`.

We take that Rayleigh-quotient infimum as the *concrete* definition (it is the
faithful Fiedler/Courant–Fischer object; cf. math0109191 §2, Freitas et al.),
and connect it to the eigenvalue picture.

The headline upper bound (math0109191, M. A. Fiedler and successors; see also
Freitas, Del-Vecchio, Abreu) is the **genus / embedding bound**

  `a(G) ≤ H(S)`,

bounding the algebraic connectivity by a Heawood-type quantity `H(S)` of the
surface `S` on which `G` embeds — concretely, of the orientable genus `g` of an
embedding.  We connect `H` to `Graphplay.CombinatorialMap.genus`.

We also record the spine connection: **equitable partitions interlace the
Laplacian spectrum**, so the quotient Laplacian's eigenvalues interlace those of
`L`, which controls `a(G)` from the quotient.

This is a *clean standalone* model on `Graphplay.Weighted` / `Graphplay.Loopy`
(for the Laplacian `WeightedGraph.laplacian`) and `Graphplay.Equitable`.  The
deep eigenvalue/embedding bounds carry honest `sorry`; all `def`s are concrete.

References:

  * M. Fiedler, "Algebraic connectivity of graphs", *Czech. Math. J.* **23**
    (1973), 298–305.
  * "Algebraic connectivity and the genus of a graph" (arXiv:math/0109191).
  * Freitas, Del-Vecchio, Abreu, "Spectral properties of the Laplacian of
    graphs on surfaces".
  * Godsil–Royle, *Algebraic Graph Theory* (interlacing for equitable
    partitions).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Graphplay.Weighted
import Graphplay.Loopy
import Graphplay.Equitable
import Graphplay.CombinatorialMap

open scoped Matrix

universe u v

namespace Graphplay

namespace AlgebraicConnectivity

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## 1.  The Laplacian quadratic form and Rayleigh quotient -/

/-- The all-ones vector on `V`. -/
def onesVec (V : Type u) : V → ℂ := fun _ => 1

/-- The **Laplacian quadratic form** `⟨x, L x⟩ = xᴴ L x`, as a complex number
(real for real `x`, since `L` is Hermitian).  Here `L = (G.laplacian).adj`. -/
noncomputable def laplacianForm (G : WeightedGraph V) (x : V → ℂ) : ℂ :=
  ∑ u, ∑ w, star (x u) * (G.laplacian.adj u w) * x w

/-- The squared Euclidean norm `⟨x, x⟩ = ∑ |x u|²`. -/
noncomputable def normSq (x : V → ℂ) : ℝ := ∑ u, ‖x u‖ ^ 2

/-- A vector is **orthogonal to the all-ones vector** when `∑ u, x u = 0`
(i.e. `⟨𝟙, x⟩ = 0`). -/
def orthToOnes (x : V → ℂ) : Prop := (∑ u, x u) = 0

/-- The **Rayleigh-quotient value set** of the Laplacian over nonzero vectors
orthogonal to the all-ones vector: the real parts of `laplacianForm G x / normSq x`.

(The Laplacian form is real because `L` is Hermitian; we take `.re` to land in
`ℝ` without carrying the vanishing-imaginary-part proof at the definition site.) -/
noncomputable def rayleighSet (G : WeightedGraph V) : Set ℝ :=
  { r : ℝ | ∃ x : V → ℂ, x ≠ 0 ∧ orthToOnes x ∧
      r = (laplacianForm G x).re / normSq x }

/-- **Algebraic connectivity / Fiedler value** `a(G)`: the infimum of the
Laplacian Rayleigh quotient over nonzero vectors orthogonal to the all-ones
vector.  By Courant–Fischer this equals the second-smallest Laplacian
eigenvalue `λ₂(L)`.  When `V` has fewer than two vertices the set is empty and
`sInf ∅ = 0`. -/
noncomputable def algebraicConnectivity (G : WeightedGraph V) : ℝ :=
  sInf (rayleighSet G)

/-! ## 2.  Eigenvalue characterisation -/

/-- The Laplacian eigenvalues of `G`, indexed in **antitone** order by
`Fin (card V)` (largest first): `eigenvalues₀` of the Hermitian Laplacian. -/
noncomputable def laplacianEigenvalues (G : WeightedGraph V) :
    Fin (Fintype.card V) → ℝ :=
  G.laplacian.herm.eigenvalues₀

/-- The Laplacian eigenvalues are antitone in the `Fin (card V)` index (largest
at index `0`, smallest at the last index). -/
theorem laplacianEigenvalues_antitone (G : WeightedGraph V) :
    Antitone (laplacianEigenvalues G) :=
  G.laplacian.herm.eigenvalues₀_antitone

/-- The **second-smallest** Laplacian eigenvalue, as an explicit index into the
antitone eigenvalue list: the smallest is at index `card V − 1`, so the
second-smallest is at index `card V − 2`.  Requires `2 ≤ card V`. -/
noncomputable def secondSmallestLaplacianEigenvalue
    (G : WeightedGraph V) (h : 2 ≤ Fintype.card V) : ℝ :=
  laplacianEigenvalues G ⟨Fintype.card V - 2, by omega⟩

/-- **Fiedler's eigenvalue characterisation (statement).**  The algebraic
connectivity (Rayleigh-quotient infimum over `𝟙^⊥`) coincides with the
second-smallest Laplacian eigenvalue.  This is Courant–Fischer applied to the
Hermitian Laplacian, using that the smallest eigenvalue `0` is realised by the
all-ones vector (which we project out by the `orthToOnes` constraint).
(Deep: Courant–Fischer min-max plus identification of the bottom eigenvector.) -/
theorem algebraicConnectivity_eq_secondSmallest
    (G : WeightedGraph V) (h : 2 ≤ Fintype.card V) :
    algebraicConnectivity G = secondSmallestLaplacianEigenvalue G h := by
  sorry

/-! ## 3.  Nonnegativity and Fiedler monotonicity -/

/-- **Algebraic connectivity is nonnegative.**  The Laplacian is positive
semidefinite (it is a Hermitian "difference" `D − A` with nonnegative quadratic
form `∑_{u<w} |x u − x w|²`-type structure for ordinary graphs), so every
Rayleigh quotient — and hence the infimum — is `≥ 0`.  (Deep: positive
semidefiniteness of the Laplacian quadratic form.) -/
theorem algebraicConnectivity_nonneg (G : WeightedGraph V) :
    0 ≤ algebraicConnectivity G := by
  sorry

/-- **Fiedler monotonicity (edge-addition statement).**  Adding edges (passing
to a graph `G'` whose Laplacian quadratic form dominates that of `G` on every
vector) cannot decrease the algebraic connectivity: `a(G) ≤ a(G')`.  We phrase
the hypothesis as pointwise domination of the Rayleigh value via the real
Laplacian forms on the common vertex set.  (Deep: monotonicity of the
Rayleigh-quotient infimum under domination of the quadratic form.) -/
theorem algebraicConnectivity_mono (G G' : WeightedGraph V)
    (hdom : ∀ x : V → ℂ, (laplacianForm G x).re ≤ (laplacianForm G' x).re) :
    algebraicConnectivity G ≤ algebraicConnectivity G' := by
  sorry

/-! ## 4.  The genus / Heawood embedding upper bound -/

/-- The **Heawood-type surface bound** `H(g)` for the orientable genus `g ≥ 0`:
the value `H(g) = (7 + √(1 + 48 g)) / 2` (the Heawood number's analytic form,
`Δ(S) = ⌊H(g)⌋` for the chromatic/connectivity bounds on a surface of genus
`g`).  We keep the analytic (un-floored) form so the inequality `a(G) ≤ H(g)`
is a clean real bound; cf. math0109191. -/
noncomputable def heawoodBound (g : ℕ) : ℝ :=
  (7 + Real.sqrt (1 + 48 * (g : ℝ))) / 2

/-- **Genus upper bound on algebraic connectivity (math0109191, statement).**
If `G` embeds on an orientable surface of genus `g` — witnessed here by a
`CombinatorialMap` `M` whose underlying graph is `G` and whose orientable
`genus` is `g` — then the algebraic connectivity is bounded by the Heawood
surface quantity:

  `a(G) ≤ H(g)`.

This is the headline result of "Algebraic connectivity and the genus of a
graph" (arXiv:math/0109191): the topology of the embedding surface caps the
spectral connectivity.  (Deep: the genus-based eigenvalue bound; combines the
Euler/Heawood inequality with the Fiedler eigenvalue interlacing.) -/
theorem algebraicConnectivity_le_heawood
    {E : Type v} [Fintype E] [DecidableEq E]
    (G : WeightedGraph V) (M : CombinatorialMap V E) (g : ℕ)
    (_hgenus : M.genus = (g : ℤ))
    (_hunder : M.toWeightedGraph.adj = G.adj) :
    algebraicConnectivity G ≤ heawoodBound g := by
  sorry

/-! ## 5.  Equitable partitions interlace the Laplacian spectrum -/

/-- **Equitable-partition Laplacian interlacing (statement).**  If `P` is an
equitable partition of `G`, the eigenvalues of the *quotient Laplacian* (the
Laplacian of the symmetric quotient `P.symmQuotient`) interlace the eigenvalues
of the full Laplacian `L`.  Concretely: every eigenvalue of the quotient
Laplacian lies in the (complex) spectrum of the full Laplacian, so the quotient
contributes a subset of the Laplacian spectrum that bounds `a(G)`.

This is the Laplacian analogue of `Graphplay.EquitablePartition.spectrum_subset`
(adjacency version, already proved in `Graphplay.Spectral`): the equitable
quotient embeds into the spectral picture, and interlacing follows by
Cauchy/Courant–Fischer.  (Deep: the Laplacian quotient and the interlacing
estimate.) -/
theorem equitable_laplacian_interlacing
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0)
    (μ : ℂ) (_hμ : μ ∈ spectrum ℂ
        (Matrix.diagonal (fun i => ∑ j, P.symmQuotient i j) - P.symmQuotient)) :
    μ ∈ spectrum ℂ ((G.laplacian.adj)) := by
  sorry

end AlgebraicConnectivity

end Graphplay
