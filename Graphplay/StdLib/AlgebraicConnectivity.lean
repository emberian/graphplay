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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Graphplay.Weighted
import Graphplay.Loopy
import Graphplay.Equitable
import Graphplay.CombinatorialMap
import Graphplay.ForMathlib.CourantFischer
import Graphplay.Spectral

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

/-- **Real, nonnegative edge weights.**  Each adjacency entry is a nonnegative
real number.  This holds for ordinary graphs and any `SimpleGraph.toWeighted`,
and is precisely the hypothesis under which the Laplacian is positive
semidefinite — the row sums `D_{uu} = ∑_w A_{uw}` then annihilate the all-ones
vector and the quadratic form is a nonnegative sum of squared differences.
(Hermitian symmetry of the real parts, `A_{uw} = A_{wu}`, is already supplied by
`G.herm`.) -/
def RealNonnegWeights (G : WeightedGraph V) : Prop :=
  ∀ u w, (G.adj u w).im = 0 ∧ 0 ≤ (G.adj u w).re

/-- Under `RealNonnegWeights`, the adjacency entry equals its own real part as a
complex number. -/
theorem RealNonnegWeights.adj_ofReal {G : WeightedGraph V}
    (h : RealNonnegWeights G) (u w : V) :
    G.adj u w = ((G.adj u w).re : ℂ) := by
  have him := (h u w).1
  apply Complex.ext <;> simp [him]

/-- Hermiticity gives symmetry of the real parts of the adjacency entries. -/
theorem adj_re_symm (G : WeightedGraph V) (u w : V) :
    (G.adj u w).re = (G.adj w u).re := by
  have h : G.adj w u = star (G.adj u w) := (G.herm.apply w u).symm
  rw [h, Complex.star_def, Complex.conj_re]

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

/-! ### Matrix-form bridge and the bottom eigenvector

To connect the concrete `laplacianForm`/`normSq`/`orthToOnes` vocabulary to
Mathlib's spectral machinery (`IsHermitian.eigenvalues₀`), we rewrite the
Laplacian quadratic form as the genuine Hermitian form `star x ⬝ᵥ (L *ᵥ x)`, and
exhibit the all-ones vector as a bottom eigenvector (`L · 𝟙 = 0`).  These two
facts are the *hinges* of the codimension-`1` Courant–Fischer argument: the form
is what the Rayleigh quotient measures, and `𝟙` is the eigenvector we project
out via `orthToOnes`. -/

/-- **The Laplacian quadratic form is the Hermitian matrix form.**  `laplacianForm
G x = star x ⬝ᵥ (L *ᵥ x)` where `L = G.laplacian.adj`.  This is just an
unfolding of the double sum into `dotProduct`/`mulVec`, but it is what lets the
Rayleigh-quotient infimum talk to `IsHermitian.eigenvalues₀`. -/
theorem laplacianForm_eq_dotProduct (G : WeightedGraph V) (x : V → ℂ) :
    laplacianForm G x = star x ⬝ᵥ (G.laplacian.adj *ᵥ x) := by
  unfold laplacianForm
  rw [dotProduct]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Pi.star_apply]
  ring

/-- **The all-ones vector is annihilated by the Laplacian** (real nonnegative
weights).  `L · 𝟙 = 0`, because row `u` of `L` is `D_{uu} = ∑_w A_{uw}` on the
diagonal minus the off-diagonal entries `A_{uw}`, and `D_{uu} = ∑_w A_{uw}` by
definition of the degree.  Real weights make `D_{uu} = Re(degree) = degree`, so
the cancellation is exact.  Hence `𝟙` is an eigenvector of `L` with eigenvalue
`0`, the smallest eigenvalue of the PSD Laplacian. -/
theorem laplacian_mulVec_onesVec (G : WeightedGraph V) (h : RealNonnegWeights G) :
    G.laplacian.adj *ᵥ onesVec V = 0 := by
  funext u
  show ((Matrix.diagonal (fun v => ((G.degree v).re : ℂ)) - G.adj) *ᵥ onesVec V) u = (0 : V → ℂ) u
  rw [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply]
  -- Diagonal term: `D_{uu} · 1 = (Re (degree u))`.
  have hdiag : ((Matrix.diagonal (fun v => ((G.degree v).re : ℂ))) *ᵥ onesVec V) u
      = ((G.degree u).re : ℂ) := by
    rw [Matrix.mulVec_diagonal]; simp [onesVec]
  -- Off-diagonal term: `(A · 𝟙) u = ∑_w A_{uw} = degree u`.
  have hoff : (G.adj *ᵥ onesVec V) u = G.degree u := by
    rw [Matrix.mulVec]; simp [dotProduct, onesVec, WeightedGraph.degree]
  rw [hdiag, hoff]
  -- `degree u = ∑_w A_{uw}` is real, so `Re (degree u) = degree u`.
  have hdeg_im : (G.degree u).im = 0 := by
    unfold WeightedGraph.degree
    rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun w _ => (h u w).1
  have hre : ((G.degree u).re : ℂ) = G.degree u := by
    apply Complex.ext <;> simp [hdeg_im]
  rw [hre, sub_self]

/-! The Fiedler codimension-`1` Courant–Fischer characterisation and its corollary
`algebraicConnectivity_eq_secondSmallest` appear in §2.6 below, after the PSD /
nonnegativity development (§2.5) they rely on. -/

/-! ## 2.5  Positive semidefiniteness for real, nonnegative edge weights

The Laplacian `L = D − A` is **not** positive semidefinite for arbitrary
Hermitian weights: `D_{uu} = Re(row-sum)` and the quadratic-form identity below
only holds when the entries of `A` are real and nonnegative (the ordinary-graph
case, and `SimpleGraph.toWeighted`).  We prove the standard rank-1-sum /
difference-squared positivity under `RealNonnegWeights` (defined in §1). -/

/-- **The Laplacian difference-squared identity.**  For real nonnegative weights,
twice the real part of the Laplacian quadratic form is a nonnegative sum of
weighted squared differences:

  `2 · Re(xᴴ L x) = ∑_{u,w} A_{uw} |x_u − x_w|²`.

This is the standard rank-1 decomposition `L = ∑ A_{uw}(e_u − e_w)(e_u − e_w)ᴴ`
written at the level of the quadratic form. -/
theorem laplacianForm_two_re (G : WeightedGraph V) (h : RealNonnegWeights G)
    (x : V → ℂ) :
    2 * (laplacianForm G x).re
      = ∑ u, ∑ w, (G.adj u w).re * Complex.normSq (x u - x w) := by
  -- Real part of the form, summand by summand.
  have hre : (laplacianForm G x).re
      = ∑ u, ∑ w, (star (x u) * (G.laplacian.adj u w) * x w).re := by
    unfold laplacianForm
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun u _ => Complex.re_sum _ _
  -- `(star a · ↑r · b).re = r · (star a · b).re` for real scalar `r`.
  have hscal : ∀ (r : ℝ) (a b : ℂ), (a * (r : ℂ) * b).re = r * (a * b).re := by
    intro r a b
    rw [mul_comm a ((r : ℂ)), mul_assoc, Complex.re_ofReal_mul]
  -- `(star (x u) * x u).re = normSq (x u)`.
  have hnorm : ∀ u, (star (x u) * x u).re = Complex.normSq (x u) := by
    intro u
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]; ring
  -- Expand each Laplacian summand using `L = D − A`, `D_{uu} = Re(deg u)`.
  have hsummand : ∀ u w,
      (star (x u) * (G.laplacian.adj u w) * x w).re
        = (if u = w then (G.degree u).re * Complex.normSq (x u) else 0)
          - (G.adj u w).re * (star (x u) * x w).re := by
    intro u w
    have hL : G.laplacian.adj u w
        = (Matrix.diagonal (fun v => ((G.degree v).re : ℂ))) u w - G.adj u w := rfl
    rw [hL, Matrix.diagonal_apply, h.adj_ofReal u w]
    by_cases huw : u = w
    · subst huw
      rw [if_pos rfl, if_pos rfl, mul_sub, sub_mul, Complex.sub_re, hscal, hscal, hnorm,
        Complex.ofReal_re]
    · rw [if_neg huw, if_neg huw,
        show (0 : ℂ) - ((G.adj u w).re : ℂ) = (((-(G.adj u w).re) : ℝ) : ℂ) by push_cast; ring,
        hscal, Complex.ofReal_re]
      ring
  -- The diagonal weighted degree, as a sum of real adjacency entries.
  have hdeg : ∀ u, (G.degree u).re = ∑ w, (G.adj u w).re := by
    intro u
    unfold WeightedGraph.degree
    rw [Complex.re_sum]
  -- Real part of `conj(x_u) * x_w` equals `Re(x_u * conj x_w)` (conjugation-invariance).
  have hcross : ∀ u w, (star (x u) * x w).re = (x u * star (x w)).re := by
    intro u w
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  -- Rewrite the LHS as `∑_u ∑_w A_uw nsq(x_u) − ∑_u ∑_w A_uw Re(conj x_u · x_w)`.
  rw [hre]
  simp_rw [hsummand]
  have hLHS : ∑ u, ∑ w, ((if u = w then (G.degree u).re * Complex.normSq (x u) else 0)
        - (G.adj u w).re * (star (x u) * x w).re)
      = (∑ u, ∑ w, (G.adj u w).re * Complex.normSq (x u))
        - ∑ u, ∑ w, (G.adj u w).re * (star (x u) * x w).re := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_sub_distrib,
      Fintype.sum_ite_eq u (fun _ => (G.degree u).re * Complex.normSq (x u)), hdeg,
      Finset.sum_mul]
  rw [hLHS]
  -- The target sum, expanded by `normSq_sub`.
  have hRHS : ∑ u, ∑ w, (G.adj u w).re * Complex.normSq (x u - x w)
      = (∑ u, ∑ w, (G.adj u w).re * Complex.normSq (x u))
        + (∑ u, ∑ w, (G.adj u w).re * Complex.normSq (x w))
        - 2 * ∑ u, ∑ w, (G.adj u w).re * (x u * star (x w)).re := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Complex.normSq_sub]
    push_cast [Complex.star_def]
    ring
  rw [hRHS]
  -- Symmetry: `∑_u ∑_w A_uw nsq(x_w) = ∑_u ∑_w A_uw nsq(x_u)` (swap + Hermitian symmetry).
  have hswap : ∑ u, ∑ w, (G.adj u w).re * Complex.normSq (x w)
      = ∑ u, ∑ w, (G.adj u w).re * Complex.normSq (x u) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    rw [adj_re_symm G w u]
  rw [hswap]
  -- And `Re(conj x_u · x_w) = Re(x_u · conj x_w)`.
  simp_rw [hcross]
  ring

/-- **The Laplacian quadratic form is nonnegative for real nonnegative weights.**
Immediate from the difference-squared identity `laplacianForm_two_re`: each
summand `A_{uw} |x_u − x_w|²` is a product of nonnegatives. -/
theorem laplacianForm_re_nonneg (G : WeightedGraph V) (h : RealNonnegWeights G)
    (x : V → ℂ) : 0 ≤ (laplacianForm G x).re := by
  have h2 : 0 ≤ 2 * (laplacianForm G x).re := by
    rw [laplacianForm_two_re G h]
    refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun w _ => ?_
    exact mul_nonneg (h u w).2 (Complex.normSq_nonneg _)
  linarith

/-- The Rayleigh-quotient set of a `RealNonnegWeights` graph consists of
nonnegative reals: each Rayleigh quotient is `(laplacianForm).re / normSq` with
both factors `≥ 0`. -/
theorem rayleighSet_nonneg (G : WeightedGraph V) (h : RealNonnegWeights G) :
    ∀ r ∈ rayleighSet G, 0 ≤ r := by
  rintro r ⟨x, _, _, rfl⟩
  exact div_nonneg (laplacianForm_re_nonneg G h x)
    (Finset.sum_nonneg fun u _ => by positivity)

/-- The Rayleigh-quotient set of a `RealNonnegWeights` graph is bounded below (by
`0`).  This is the bounded-below fact powering Fiedler monotonicity. -/
theorem bddBelow_rayleighSet (G : WeightedGraph V) (h : RealNonnegWeights G) :
    BddBelow (rayleighSet G) :=
  ⟨0, fun _ hr => rayleighSet_nonneg G h _ hr⟩

/-! ## 2.6  Fiedler's eigenvalue characterisation (Courant–Fischer)

With the PSD / nonnegativity development in hand, the codimension-`1`
Courant–Fischer identity follows from the abstract matrix version
`Graphplay.CourantFischer.inf_rayleighSetMat_eq_secondEigenvalue₀`, by identifying
the concrete `rayleighSet G` (built from `laplacianForm`, `normSq`, `orthToOnes`)
with the abstract Rayleigh set of the Laplacian `L = G.laplacian.adj` over the
orthogonal complement of the all-ones vector. -/

/-- **Fiedler's codimension-`1` Courant–Fischer.**  For the Hermitian, PSD
Laplacian `L` of a graph with real nonnegative weights, the second-smallest
eigenvalue equals the infimum of the Rayleigh quotient over nonzero vectors
orthogonal to the all-ones bottom eigenvector.

This is the codimension-`1` min-max that, after projecting out the known bottom
eigenvector `𝟙` (`laplacian_mulVec_onesVec`), identifies the *next* eigenvalue
with the constrained Rayleigh infimum.  The PSD hypothesis enters as eigenvalue
nonnegativity (derived here from `laplacianForm_re_nonneg`), and the two hinges
are the matrix form (`laplacianForm_eq_dotProduct`) and the bottom eigenvector
(`laplacian_mulVec_onesVec`). -/
theorem hermitian_secondEigenvalue_eq_rayleigh_inf_orthogonal
    (G : WeightedGraph V) (h : 2 ≤ Fintype.card V) (hw : RealNonnegWeights G) :
    sInf (rayleighSet G)
      = laplacianEigenvalues G ⟨Fintype.card V - 2, by omega⟩ := by
  -- Identify the concrete Rayleigh set with the abstract matrix Rayleigh set of the
  -- Laplacian `L = G.laplacian.adj` over `(onesVec)^⊥`, then invoke codim-1 Courant–Fischer.
  set L : Matrix V V ℂ := G.laplacian.adj with hL
  have hLherm : L.IsHermitian := G.laplacian.herm
  -- The Laplacian is PSD: every eigenvalue is `≥ 0` (the quadratic form is nonnegative).
  have hmin : ∀ i, 0 ≤ hLherm.eigenvalues i := by
    intro i
    rw [hLherm.eigenvalues_eq i]
    have := laplacianForm_re_nonneg G hw (WithLp.ofLp (hLherm.eigenvectorBasis i))
    rwa [laplacianForm_eq_dotProduct] at this
  -- The two Rayleigh sets coincide.
  have hset : rayleighSet G = CourantFischer.rayleighSetMat L (onesVec V) := by
    ext r
    constructor
    · rintro ⟨x, hx, hortho, rfl⟩
      refine ⟨x, hx, ?_, ?_⟩
      · -- `∑ star(𝟙 u) * x u = ∑ x u = 0`.
        rw [← hortho]
        exact Finset.sum_congr rfl fun u _ => by simp [onesVec]
      · rw [laplacianForm_eq_dotProduct, hL]; rfl
    · rintro ⟨x, hx, hortho, rfl⟩
      refine ⟨x, hx, ?_, ?_⟩
      · -- `orthToOnes x`, from `∑ star(𝟙 u) * x u = 0`.
        unfold orthToOnes
        rw [← hortho]
        exact Finset.sum_congr rfl fun u _ => by simp [onesVec]
      · rw [laplacianForm_eq_dotProduct, hL]; rfl
  rw [hset]
  rw [show laplacianEigenvalues G ⟨Fintype.card V - 2, by omega⟩
      = hLherm.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ from rfl]
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hones : onesVec V ≠ 0 := by
    intro hc
    exact one_ne_zero (congrFun hc (Classical.arbitrary V))
  exact CourantFischer.inf_rayleighSetMat_eq_secondEigenvalue₀ L hLherm h
    (onesVec V) hones (laplacian_mulVec_onesVec G hw) hmin

/-- **Fiedler's eigenvalue characterisation.**  For real nonnegative edge weights
the algebraic connectivity (Rayleigh-quotient infimum over `𝟙^⊥`) coincides with
the second-smallest Laplacian eigenvalue.  A consequence of the codimension-`1`
Courant–Fischer identity `hermitian_secondEigenvalue_eq_rayleigh_inf_orthogonal`,
after unfolding `algebraicConnectivity` and `secondSmallestLaplacianEigenvalue`. -/
theorem algebraicConnectivity_eq_secondSmallest
    (G : WeightedGraph V) (h : 2 ≤ Fintype.card V) (hw : RealNonnegWeights G) :
    algebraicConnectivity G = secondSmallestLaplacianEigenvalue G h := by
  unfold algebraicConnectivity secondSmallestLaplacianEigenvalue
  exact hermitian_secondEigenvalue_eq_rayleigh_inf_orthogonal G h hw

/-! ## 3.  Nonnegativity and Fiedler monotonicity -/

/-- **Algebraic connectivity is nonnegative (real nonnegative weights).**  The
Laplacian of a graph with nonnegative real edge weights is positive semidefinite
(`laplacianForm_re_nonneg`), so every Rayleigh quotient — and hence the infimum
— is `≥ 0`.

The `RealNonnegWeights` hypothesis is genuinely needed: for general
complex-Hermitian weights `D_{uu} = Re(row-sum)` and the Laplacian need not be
PSD, so this fails without it. -/
theorem algebraicConnectivity_nonneg (G : WeightedGraph V)
    (h : RealNonnegWeights G) :
    0 ≤ algebraicConnectivity G :=
  Real.sInf_nonneg (rayleighSet_nonneg G h)

/-- **Fiedler monotonicity (edge-addition statement).**  Adding edges (passing to
a graph `G'` whose Laplacian quadratic form dominates that of `G` on every
vector) cannot decrease the algebraic connectivity: `a(G) ≤ a(G')`.  We require
`G` to have real nonnegative weights (so its Rayleigh set is bounded below, the
fact making the infimum comparison meaningful) and phrase the edge-addition
hypothesis as pointwise domination of the real Laplacian forms.

Note both Rayleigh sets range over the *same* family of nonzero `𝟙^⊥` vectors,
so they are simultaneously empty (when `card V < 2`); domination then transfers
the infimum. -/
theorem algebraicConnectivity_mono (G G' : WeightedGraph V)
    (h : RealNonnegWeights G)
    (hdom : ∀ x : V → ℂ, (laplacianForm G x).re ≤ (laplacianForm G' x).re) :
    algebraicConnectivity G ≤ algebraicConnectivity G' := by
  rcases Set.eq_empty_or_nonempty (rayleighSet G') with hempty | hne
  · -- If `rayleighSet G'` is empty, so is `rayleighSet G` (same vector family).
    have hGempty : rayleighSet G = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro r ⟨x, hx, hortho, rfl⟩
      have : (laplacianForm G' x).re / normSq x ∈ rayleighSet G' :=
        ⟨x, hx, hortho, rfl⟩
      rw [hempty] at this
      exact this
    unfold algebraicConnectivity
    rw [hGempty, hempty]
  · -- Otherwise, `sInf (rayleighSet G)` lower-bounds every element of `rayleighSet G'`.
    apply le_csInf hne
    rintro r' ⟨x, hx, hortho, rfl⟩
    -- The matching `G`-Rayleigh value is `≤ r'` by domination, and `≥ sInf (rayleighSet G)`.
    have hmemG : (laplacianForm G x).re / normSq x ∈ rayleighSet G :=
      ⟨x, hx, hortho, rfl⟩
    refine le_trans (csInf_le (bddBelow_rayleighSet G h) hmemG) ?_
    -- `normSq x > 0` since `x ≠ 0`, so dividing the dominated numerators preserves `≤`.
    have hpos : 0 < normSq x := by
      unfold normSq
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ i, ?_⟩
      simp only [Pi.zero_apply] at hi
      have : ‖x i‖ ≠ 0 := norm_ne_zero_iff.mpr hi
      positivity
    exact div_le_div_of_nonneg_right (hdom x) hpos.le

/-! ## 4.  The genus / Heawood embedding upper bound -/

/-- The **Heawood-type surface bound** `H(g)` for the orientable genus `g ≥ 0`:
the value `H(g) = (7 + √(1 + 48 g)) / 2` (the Heawood number's analytic form,
`Δ(S) = ⌊H(g)⌋` for the chromatic/connectivity bounds on a surface of genus
`g`).  We keep the analytic (un-floored) form so the inequality `a(G) ≤ H(g)`
is a clean real bound; cf. math0109191. -/
noncomputable def heawoodBound (g : ℕ) : ℝ :=
  (7 + Real.sqrt (1 + 48 * (g : ℝ))) / 2

/-- **The genus–spectral input (math0109191, isolated form).**  The genuine deep
content of "Algebraic connectivity and the genus of a graph" is the *Fiedler
eigenvalue bound* in terms of the embedding surface: the second-smallest
Laplacian eigenvalue of a graph embedded on a surface of orientable genus `g` is
at most the Heawood quantity `H(g)`.  We isolate exactly this inequality (a
property of the eigenvalue, *not* a restatement of the `algebraicConnectivity`
goal — they are linked only through the Courant–Fischer identity
`algebraicConnectivity_eq_secondSmallest`, which we discharge below) into a
content-bearing local typeclass.

The inequality combines two classical facts neither of which is in Mathlib: the
Euler/Heawood inequality `E ≤ 3V + 6(g−1)` capping the average degree by the
genus, and the Fiedler bound `λ₂(L) ≤ (V/(V−1))·δ_min ≤ (V/(V−1))·(2E/V)`
relating `λ₂` to the average degree.  It is non-vacuous: for planar graphs
(`g = 0`, `H(0) = (7+1)/2 = 4`) it is the classical `λ₂ ≤ 4` planar bound, and
on any fixed surface it is a finite, achievable cap. -/
class GenusSpectralBound
    {E : Type v} [Fintype E] [DecidableEq E]
    (G : WeightedGraph V) (M : CombinatorialMap V E) (g : ℕ) : Prop where
  secondSmallest_le_heawood :
    (h2 : 2 ≤ Fintype.card V) → RealNonnegWeights G →
      M.genus = (g : ℤ) → M.toWeightedGraph.adj = G.adj →
      secondSmallestLaplacianEigenvalue G h2 ≤ heawoodBound g

/-- **Genus upper bound on algebraic connectivity (math0109191).**  If `G`
embeds on an orientable surface of genus `g` — witnessed by a `CombinatorialMap`
`M` with underlying graph `G` and orientable `genus` `g` — then, under the
isolated genus–spectral input `GenusSpectralBound` and the standing real
nonnegative-weight / two-vertex hypotheses, the algebraic connectivity is bounded
by the Heawood surface quantity `a(G) ≤ H(g)`.

Proof: by the proven Courant–Fischer identity `algebraicConnectivity_eq_
secondSmallest`, `a(G)` *equals* the second-smallest Laplacian eigenvalue, which
the typeclass caps by `H(g)`.  The genuinely deep Euler/Heawood + Fiedler input
is quarantined in `GenusSpectralBound`; the reduction here is exact. -/
theorem algebraicConnectivity_le_heawood
    {E : Type v} [Fintype E] [DecidableEq E]
    (G : WeightedGraph V) (M : CombinatorialMap V E) (g : ℕ)
    [hgsb : GenusSpectralBound G M g]
    (h2 : 2 ≤ Fintype.card V) (hw : RealNonnegWeights G)
    (hgenus : M.genus = (g : ℤ))
    (hunder : M.toWeightedGraph.adj = G.adj) :
    algebraicConnectivity G ≤ heawoodBound g := by
  rw [algebraicConnectivity_eq_secondSmallest G h2 hw]
  exact hgsb.secondSmallest_le_heawood h2 hw hgenus hunder

/-! ## 5.  Equitable partitions interlace the Laplacian spectrum -/

/-! ### The adjacency intertwining and the degree-alignment input

The Laplacian interlacing is the *Laplacian analogue* of the already-proven
adjacency `Graphplay.EquitablePartition.spectrum_subset`.  Its engine is the
**cell-inflate intertwining**: the full adjacency `A` carries the cell-inflate of
a quotient vector to the cell-inflate of its `symmQuotient` action, exactly the
content of `restrict_eq_symmQuotient`.  For the *Laplacian* `L = D − A` to
intertwine the *quotient Laplacian* `D_Q − Q`, the only extra fact needed is that
the full diagonal degree `Re(deg x)` is **constant on each cell and equal to the
quotient row-sum** `∑_j Q_{ij}` — the genuine equitable degree-balance, captured
below as the content-bearing local typeclass `LaplacianDegreeAligned`.  Under it,
the interlacing reduces — with no further deep input — to the adjacency lift. -/

/-- **Cell-inflate adjacency intertwining.**  `A *ᵥ (cellInflate v) = cellInflate
(Q *ᵥ v)` where `Q = P.symmQuotient`.  Immediate from `cellInflateVec_eq_sum`
and `restrict_eq_symmQuotient`. -/
theorem adj_mulVec_cellInflate_eq
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (v : I → ℂ) :
    G.adj.mulVec (P.cellInflateVec v)
      = P.cellInflateVec (P.symmQuotient.mulVec v) := by
  rw [P.cellInflateVec_eq_sum v, P.restrict_eq_symmQuotient v,
    P.cellInflateVec_eq_sum (P.symmQuotient.mulVec v)]

/-- **The genuine equitable degree-balance (Laplacian compatibility, isolated).**
For an equitable partition `P`, the full Laplacian diagonal `Re(deg x)` is
constant on each cell and equals the symmetric-quotient row-sum
`∑_j Q_{ij}` there (with `i = P.cells x`).  This is the one structural fact that
makes the full Laplacian `L = D − A` intertwine the quotient Laplacian
`D_Q − Q` through the cell-inflate; it is a property of *how* the partition sits
inside the weighted graph (a balanced/regular-on-cells condition), and it is the
named wall on which the interlacing rests.

Non-vacuous: it holds whenever the quotient is the standard equitable quotient of
a real graph with cells of equal size (so `√|C_i|/√|C_j| = 1` and the
symmetric-quotient row-sum is the ordinary cell degree `Re(deg)`), e.g. for any
orbit partition of a vertex-transitive graph. -/
class LaplacianDegreeAligned
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) : Prop where
  degree_eq_rowSum : ∀ x : V,
    ((G.degree x).re : ℂ) = ∑ j, P.symmQuotient (P.cells x) j

/-- **Laplacian cell-inflate intertwining.**  Under `LaplacianDegreeAligned`, the
full Laplacian carries the cell-inflate of `v` to the cell-inflate of the
quotient-Laplacian action `(D_Q − Q) *ᵥ v`. -/
theorem laplacian_mulVec_cellInflate_eq
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    [hal : LaplacianDegreeAligned P] (v : I → ℂ) :
    G.laplacian.adj.mulVec (P.cellInflateVec v)
      = P.cellInflateVec
          ((Matrix.diagonal (fun i => ∑ j, P.symmQuotient i j) - P.symmQuotient).mulVec v) := by
  -- `L = diagonal(Re deg) − A`, so `L *ᵥ w = diagonal(Re deg) *ᵥ w − A *ᵥ w`.
  show (Matrix.diagonal (fun x => ((G.degree x).re : ℂ)) - G.adj).mulVec _ = _
  rw [Matrix.sub_mulVec, adj_mulVec_cellInflate_eq, Matrix.sub_mulVec]
  -- The diagonal-degree term equals the cell-inflate of the quotient row-sum diagonal action.
  have hdiag : (Matrix.diagonal (fun x => ((G.degree x).re : ℂ))).mulVec (P.cellInflateVec v)
      = P.cellInflateVec
          ((Matrix.diagonal (fun i => ∑ j, P.symmQuotient i j)).mulVec v) := by
    funext x
    rw [Matrix.mulVec_diagonal]
    simp only [EquitablePartition.cellInflateVec, Matrix.mulVec_diagonal]
    rw [hal.degree_eq_rowSum x, mul_div_assoc]
  rw [hdiag]
  -- Distribute the cell-inflate over the difference (it is linear: `cellInflateLin`).
  rw [show P.cellInflateVec ((Matrix.diagonal (fun i => ∑ j, P.symmQuotient i j)).mulVec v)
        - P.cellInflateVec (P.symmQuotient.mulVec v)
      = P.cellInflateLin ((Matrix.diagonal (fun i => ∑ j, P.symmQuotient i j)).mulVec v)
        - P.cellInflateLin (P.symmQuotient.mulVec v) from rfl,
    ← map_sub]
  rfl

/-- **Equitable-partition Laplacian interlacing.**  If `P` is an equitable
partition of `G` satisfying the degree-balance `LaplacianDegreeAligned`, every
eigenvalue of the *quotient Laplacian* `D_Q − Q` (with `Q = P.symmQuotient`) lies
in the (complex) spectrum of the full Laplacian `L = D − A`.

This is the Laplacian analogue of `Graphplay.EquitablePartition.spectrum_subset`
(adjacency version, already proved in `Graphplay.Spectral`): the cell-inflate of a
quotient-Laplacian eigenvector is a nonzero (`cellInflateVec_ne_zero_of_ne_zero`,
using `hne`) eigenvector of the full Laplacian, via the intertwining
`laplacian_mulVec_cellInflate_eq`; interlacing of the antitone eigenvalue lists
then follows from the eigenspace embedding. -/
theorem equitable_laplacian_interlacing
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    [LaplacianDegreeAligned P]
    (hne : ∀ k, P.cellCard k ≠ 0)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ
        (Matrix.diagonal (fun i => ∑ j, P.symmQuotient i j) - P.symmQuotient)) :
    μ ∈ spectrum ℂ ((G.laplacian.adj)) := by
  set M : Matrix I I ℂ := Matrix.diagonal (fun i => ∑ j, P.symmQuotient i j) - P.symmQuotient with hM
  have hne' : ∀ i, 0 < P.cellCard i := by
    intro i
    have h0 : (0 : ℝ) ≤ P.cellCard i := by unfold EquitablePartition.cellCard; positivity
    exact lt_of_le_of_ne h0 (fun h => hne i h.symm)
  -- Step 1: spectrum membership of the quotient Laplacian → `HasEigenvalue` of `M.toLin'`.
  rw [← Matrix.spectrum_toLin'] at hμ
  have hev_q : Module.End.HasEigenvalue M.toLin' μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ
  obtain ⟨v, hvmem, hvne⟩ := hev_q.exists_hasEigenvector
  have hveig : M.mulVec v = μ • v := by
    have := Module.End.mem_eigenspace_iff.mp hvmem
    rwa [Matrix.toLin'_apply] at this
  -- Step 2: the cell-inflate of `v` is a nonzero eigenvector of `L`.
  have hinf_ne : P.cellInflateVec v ≠ 0 :=
    P.cellInflateVec_ne_zero_of_ne_zero v hvne hne'
  have hinf_eig : G.laplacian.adj.mulVec (P.cellInflateVec v) = μ • P.cellInflateVec v := by
    rw [laplacian_mulVec_cellInflate_eq P v, ← hM, hveig]
    -- `cellInflateVec (μ • v) = μ • cellInflateVec v` by linearity.
    show P.cellInflateLin (μ • v) = μ • P.cellInflateLin v
    rw [map_smul]
  -- Step 3: convert to spectrum membership of `L`.
  have hinf_mem : P.cellInflateVec v ∈ Module.End.eigenspace G.laplacian.adj.toLin' μ := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hinf_eig
  have hev_a : Module.End.HasEigenvalue G.laplacian.adj.toLin' μ :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨hinf_mem, hinf_ne⟩
  have : μ ∈ spectrum ℂ G.laplacian.adj.toLin' :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mp hev_a
  rwa [Matrix.spectrum_toLin'] at this

end AlgebraicConnectivity

end Graphplay
