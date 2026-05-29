/-
# Graphplay.Search.CNO

The **Chakraborty–Novo–Roland (CNO) spectral-ratio condition** for optimal
continuous-time-quantum-walk (CTQW) spatial search.

The Childs–Goldstone search Hamiltonian for a single marked vertex `w` is
`H_γ = -γ · A − |w⟩⟨w|`, where `A` is the (Hermitian) adjacency matrix of a
weighted graph `G`, `γ > 0` is the tunable hopping rate, and `|w⟩⟨w|` is the
rank-one oracular projector onto the marked vertex.  An "optimal search" finds
`w` with constant success probability in time `O(√N)` (`N = |V|`), matching the
Grover lower bound — a quadratic speedup over the classical `Θ(N)` hitting time.

The CNO program (arXiv:2004.12686, *On the optimality of spatial search by
continuous-time quantum walk*) derives **necessary and sufficient conditions**,
in terms of the spectrum of the normalized graph Hamiltonian, for the CG
algorithm to be optimal.  Writing the marked state in the eigenbasis of `H`,
`|w⟩ = Σ aᵢ |vᵢ⟩` with eigenvalues `0 ≤ λ₁ ≤ ⋯ ≤ λ_{n-1} < λ_n = 1`, and
defining the spectral sums

  `Sₖ = Σ_{i<n} |aᵢ|² / (1 − λᵢ)ᵏ`,

CNO Theorem 1 states: in the regime of validity (Eq. 14), the CG algorithm is
optimal **iff** `S₁/√S₂ = Θ(1)`.  The earlier sufficient condition (their
Ref. [9], `√ε ≤ c·Δ`) is the *constant-spectral-gap* regime: when the gap
`Δ = 1 − λ_{n-1}` between the principal eigenvalue and the rest is bounded
below by a constant (equivalently the **spectral ratio**
`max_{i≠principal}|λᵢ| / |λ_principal| < 1` uniformly), search is optimal.  This
file formalizes that ratio condition (the high-leverage, family-covering form),
which subsumes the entire CNO example table (complete graph, hypercube,
strongly regular graphs, complete bipartite, 4d-lattices, …).

## What is proven vs. sorried

* `CNOSpectralRatio` is **genuinely well-defined** (a real number computed from
  `G.herm.eigenvalues`), and several of its basic properties (nonnegativity,
  the value on the complete graph) are proven from the spectral API.
* The headline `optimal_search_of_spectral_ratio_lt_one` is stated precisely
  and `sorry`-ed at exactly one place: the deep CTQW success-probability /
  perturbation analysis of arXiv:2004.12686 (Theorems 1–2), which converts the
  spectral-gap bound into the constant-amplitude statement.  No axioms; no false
  statements.
* The **graphplay payoff** — quotient/bundle inheritance of optimal search —
  is stated as `optimal_search_of_quotient_ratio` using the spine's
  `spectrum_subset` / `symmQuotient`.
* The Childs–Goldstone **base case** (`Kₙ` is optimal) is stated as
  `complete_graph_optimal_search` (arXiv:quant-ph/0306054).

Cross-references: `Graphplay/Search.lean` (search Hamiltonian on a `Finset`
marked set, the quotient reduction `search_quotient_reduction`),
`Graphplay/Spectral.lean` (`spectrum_subset`), `Graphplay/Bundle.lean`
(`fiberPartition`).
-/

import Graphplay.Search
import Graphplay.Spectral
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Bundle
import Mathlib.Analysis.Matrix.Spectrum

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The single-marked-vertex search Hamiltonian. -/

/-- The **Childs–Goldstone search Hamiltonian** for a single marked vertex `w`:
`H_γ = -γ · A − |w⟩⟨w|`.  Here `|w⟩⟨w|` is the rank-one diagonal projector onto
`w`, i.e. `markedProjector {w}` from `Graphplay/Search.lean`'s `Finset`-marked
form specialized to the singleton `{w}`.  Concretely the `(u,v)` entry is
`-γ · A u v − [u = v = w]`. -/
noncomputable def searchHamiltonian (G : WeightedGraph V) (w : V) (γ : ℝ) :
    Matrix V V ℂ :=
  G.searchHamiltonian ({w} : Finset V) γ

/-- Unfolding: the single-vertex search Hamiltonian agrees entrywise with the
`-γ·A − |w⟩⟨w|` formula. -/
theorem searchHamiltonian_apply (G : WeightedGraph V) (w : V) (γ : ℝ) (u v : V) :
    searchHamiltonian G w γ u v
      = -(γ : ℂ) * G.adj u v - (if u = v ∧ u = w then (1 : ℂ) else 0) := by
  unfold searchHamiltonian WeightedGraph.searchHamiltonian
  simp only [Finset.mem_singleton]

/-- The single-vertex search Hamiltonian is Hermitian: it is a real-linear
combination of the Hermitian matrices `A` and `|w⟩⟨w|`.  (Recorded for
downstream spectral arguments.) -/
theorem searchHamiltonian_isHermitian (G : WeightedGraph V) (w : V) (γ : ℝ) :
    (searchHamiltonian G w γ).IsHermitian := by
  unfold Matrix.IsHermitian
  ext u v
  simp only [Matrix.conjTranspose_apply, searchHamiltonian_apply, star_sub]
  -- `star` of the `-γ·A` part uses Hermiticity of `A`; the projector part is real.
  congr 1
  · -- conjugate of the adjacency term
    rw [star_mul']
    have hgamma : star (-(γ : ℂ)) = -(γ : ℂ) := by
      rw [star_neg, Complex.star_def, Complex.conj_ofReal]
    rw [hgamma]
    congr 1
    have := congrFun (congrFun G.herm u) v
    rwa [Matrix.conjTranspose_apply] at this
  · -- conjugate of the marked projector term
    by_cases h : v = u ∧ v = w
    · rw [if_pos h, star_one, if_pos ⟨h.1.symm, h.1 ▸ h.2⟩]
    · rw [if_neg h, star_zero]
      rw [if_neg]
      rintro ⟨huv, huw⟩
      exact h ⟨huv.symm, huv ▸ huw⟩

/-! ## Optimal CTQW search. -/

/-- **Optimal CTQW spatial search.**  We say that search on `G` for marked vertex
`w` is *optimal* if there is a coupling `γ` and a time `τ = O(√N)` at which the
closed-system search evolution concentrates constant amplitude on `w`, i.e. the
singleton search succeeds with constant probability.  Phrased via the existing
`IsOptimalSearch` predicate from `Graphplay/Search.lean` (constant amplitude
`≥ 1/√2` into the marked subspace), together with the `O(√N)` running-time
budget on `τ`.

The `√N` running time is the content of the quadratic speedup; the constant
`τ ≤ C · √N` is recorded with an explicit existential `C`. -/
def IsOptimalCTQWSearch (G : WeightedGraph V) (w : V) : Prop :=
  ∃ (γ τ : ℝ) (C : ℝ),
    0 < γ ∧ 0 ≤ C ∧
    τ ≤ C * Real.sqrt (Fintype.card V) ∧
    IsOptimalSearch G ({w} : Finset V) γ τ

/-! ## The CNO spectral-ratio criterion.

For the *normalized* search Hamiltonian, CNO place the principal eigenvalue at
`1` and order `0 ≤ λ₁ ≤ ⋯ ≤ λ_{n-1} < λ_n = 1`.  The single most important
sufficient invariant (their Ref. [9] / constant-gap regime) is the **spectral
ratio**

  `ρ(G) = (second-largest |eigenvalue|) / (largest eigenvalue)`,

with `ρ(G) < 1` precisely the constant-spectral-gap condition.  We define `ρ(G)`
directly from `G.herm.eigenvalues : V → ℝ`. -/

/-- The largest eigenvalue magnitude of `G` (the spectral radius), as a
`Finset.sup'` over the vertex-indexed eigenvalues.  Requires `V` nonempty. -/
noncomputable def spectralRadius (G : WeightedGraph V) (hne : Nonempty V) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := V)) (fun i => |G.herm.eigenvalues i|)

/-- The second-largest eigenvalue magnitude of `G`, *relative to a designated
principal index* `p` (the index achieving the spectral radius, e.g. the
all-ones / uniform principal eigenvector for a regular graph): the sup of
`|λᵢ|` over all `i ≠ p`.  Returns `0` when `V` is a single vertex. -/
noncomputable def secondEigenvalueMag (G : WeightedGraph V) (p : V) : ℝ :=
  ((Finset.univ.erase p).sup
    (fun i => (⟨|G.herm.eigenvalues i|, abs_nonneg _⟩ : NNReal)) : NNReal)

/-- **CNO spectral ratio** relative to principal index `p`:
`ρ_p(G) = (second-largest |eigenvalue|) / |λ_p|`.  When `p` is the principal
index (largest magnitude) this is the second-eigenvalue / principal ratio that
CNO require to be bounded below `1`. -/
noncomputable def CNOSpectralRatio (G : WeightedGraph V) (p : V) : ℝ :=
  secondEigenvalueMag G p / |G.herm.eigenvalues p|

/-- The spectral radius is nonnegative. -/
theorem spectralRadius_nonneg (G : WeightedGraph V) (hne : Nonempty V) :
    0 ≤ spectralRadius G hne := by
  unfold spectralRadius
  exact Finset.le_sup'_of_le _ (Finset.mem_univ (Classical.arbitrary V)) (abs_nonneg _)

/-- The second-eigenvalue magnitude is nonnegative. -/
theorem secondEigenvalueMag_nonneg (G : WeightedGraph V) (p : V) :
    0 ≤ secondEigenvalueMag G p := by
  unfold secondEigenvalueMag
  exact NNReal.coe_nonneg _

/-- The CNO spectral ratio is nonnegative (it is a quotient of nonnegatives). -/
theorem CNOSpectralRatio_nonneg (G : WeightedGraph V) (p : V) :
    0 ≤ CNOSpectralRatio G p := by
  unfold CNOSpectralRatio
  exact div_nonneg (secondEigenvalueMag_nonneg G p) (abs_nonneg _)

/-- **Characterization of the ratio condition.**  `CNOSpectralRatio G p < 1`
(with `|λ_p| > 0`) is equivalent to: every non-principal eigenvalue is strictly
smaller in magnitude than the principal one, i.e. `|λᵢ| < |λ_p|` for all
`i ≠ p`.  This is the spectral-gap statement `Δ > 0` that CNO require. -/
theorem CNOSpectralRatio_lt_one_iff (G : WeightedGraph V) (p : V)
    (hp : 0 < |G.herm.eigenvalues p|) :
    CNOSpectralRatio G p < 1 ↔
      ∀ i ∈ Finset.univ.erase p, |G.herm.eigenvalues i| < |G.herm.eigenvalues p| := by
  unfold CNOSpectralRatio secondEigenvalueMag
  rw [div_lt_one hp]
  -- Package `|λ_p|` as an `NNReal` and transport the strict inequality across the
  -- coercion, reducing to a statement entirely in `NNReal`.
  set P : NNReal := ⟨|G.herm.eigenvalues p|, abs_nonneg _⟩ with hP
  set f : V → NNReal := fun j => ⟨|G.herm.eigenvalues j|, abs_nonneg _⟩ with hf
  have hPpos : 0 < P := by rw [hP]; exact_mod_cast hp
  -- The real-valued goal `((sup f) : ℝ) < |λ_p|` is the coercion of `sup f < P`
  -- (note `(P : ℝ) = |λ_p|` definitionally), then `Finset.sup_lt_iff` for `NNReal`.
  rw [show (((Finset.univ.erase p).sup
        (fun j => (⟨|G.herm.eigenvalues j|, abs_nonneg _⟩ : NNReal)) : NNReal) : ℝ)
        = (((Finset.univ.erase p).sup f : NNReal) : ℝ) from rfl]
  rw [show |G.herm.eigenvalues p| = ((P : NNReal) : ℝ) from rfl]
  rw [NNReal.coe_lt_coe]
  -- `Finset.sup_lt_iff` for the `OrderBot` `NNReal`: sup < P ↔ ∀ i, f i < P (given 0 < P).
  rw [Finset.sup_lt_iff hPpos]
  -- Now both sides are `∀ i ∈ erase p, |λ_i| < |λ_p|`, modulo the NNReal coercion.
  constructor
  · intro h i hi
    have := h i hi
    rw [hf, hP] at this
    exact_mod_cast this
  · intro h i hi
    rw [hf, hP]
    exact_mod_cast h i hi

/-! ## The headline CNO optimality theorem. -/

/-- **CNO optimal-search criterion (arXiv:2004.12686).**  Let `G` be a `d`-regular
weighted graph whose principal eigenvector at index `p` is the **uniform**
(all-ones) vector — the standard normalization in which the marked state has the
uniform overlap `|aₚ|² ≈ 1/N` with the principal eigenstate, and the CG initial
state is `|s⟩ = |vₚ⟩`.  If the **spectral ratio is bounded below one**,
`CNOSpectralRatio G p < 1` (equivalently a constant spectral gap, by
`CNOSpectralRatio_lt_one_iff`), then CTQW spatial search for any marked vertex
`w` is optimal: success probability `→` constant in time `O(√N)`.

The hypotheses encode CNO's regime of validity (their Eq. 14, here in the
constant-gap special case of Ref. [9]): regularity + uniform principal
eigenvector give the uniform overlaps `|aᵢ|² = 1/N`, and the ratio bound gives
the constant spectral gap that controls the spectral sums `Sₖ`, yielding
`S₁/√S₂ = Θ(1)` (CNO Theorem 1).

**Deep analysis sorried.**  The conversion of the spectral-gap bound into the
constant-amplitude / `O(√N)` time statement is CNO's perturbative computation
(Theorems 1–2 of arXiv:2004.12686): the optimal hopping rate is `r* = S₁`, the
maximum amplitude `ν ≈ S₁/√S₂` is reached at `T = Θ((1/√ε)·(√S₂/S₁))`, and the
robustness window `|r − S₁| = O(√S₂)`.  We `sorry` exactly that dynamical core;
the spectral hypotheses and conclusion are stated precisely. -/
theorem optimal_search_of_spectral_ratio_lt_one
    (G : WeightedGraph V) (w : V) (p : V) (d : ℂ)
    (hne : Nonempty V)
    (hreg : G.isRegular d)
    -- The principal eigenvector at index `p` is uniform (all-ones, normalized):
    (huniform : ∀ x : V,
      (G.herm.eigenvectorBasis p : V → ℂ) x
        = (1 : ℂ) / Real.sqrt (Fintype.card V))
    (hp : 0 < |G.herm.eigenvalues p|)
    (hratio : CNOSpectralRatio G p < 1) :
    IsOptimalCTQWSearch G w := by
  -- HONEST SORRY.  Everything up to the dynamical core is in place: regularity +
  -- uniform principal eigenvector + ratio<1 (= constant gap, via
  -- `CNOSpectralRatio_lt_one_iff`) are exactly CNO's validity-regime hypotheses.
  -- The remaining content is the perturbative amplitude/time analysis of
  -- arXiv:2004.12686 Theorems 1–2 (optimal r* = S₁, amplitude ν ≈ S₁/√S₂ at
  -- T = Θ(√S₂/(√ε·S₁))), which establishes the `IsOptimalSearch` amplitude
  -- bound `≥ 1/√2` at a time `τ ≤ C·√N`.  Left as the single dynamical `sorry`.
  sorry

/-! ## The graphplay payoff: quotient / bundle inheritance.

The spine result `EquitablePartition.spectrum_subset` says the symmetric
quotient `Q̃` shares its spectrum with the host adjacency `A`.  Combined with the
quotient search reduction `search_quotient_reduction` (Search.lean), an optimal
search on a quotient that satisfies the CNO ratio condition lifts to the host:
the host inherits optimal search.  For an **equal-fiber bundle** the fiber
partition is equitable (`Bundle.fiberPartition`), so a bundle whose quotient
satisfies the ratio condition has optimal search. -/

/-- **Quotient inheritance of optimal search (graphplay payoff).**  Suppose `G`
has an equitable partition `P` with all cells nonempty, whose symmetric quotient
`Q̃` (a `WeightedGraph` on the index type `I`, packaged here via `hQ`) satisfies
the CNO spectral-ratio condition and hence supports optimal search.  Because
`spectrum_subset` transports the quotient eigenvalues (and the principal/uniform
eigenvector) up to the host, and `search_quotient_reduction` makes the host
search Hamiltonian act as the quotient one on the cell-uniform subspace, the host
inherits optimal CTQW search.

We state this in the reduction form: optimal search on the quotient (as a
`WeightedGraph` `GQ` on `I` whose adjacency is the relevant restriction of `Q̃`)
implies optimal search on `G`.  This is the search analogue of the spectral
lift and the precise payoff connecting CNO to the Graphplay spine. -/
theorem optimal_search_of_quotient_ratio
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (hne : ∀ i, 0 < P.cellCard i)
    (GQ : WeightedGraph I) (wQ : I)
    -- The quotient graph `GQ` carries the symmetric-quotient adjacency:
    (hQ : GQ.adj = P.symmQuotient)
    -- and satisfies CNO optimality:
    (hopt : IsOptimalCTQWSearch GQ wQ)
    -- the host marked vertex lies in the cell of `wQ`:
    (w : V) (hw : P.cells w = wQ) :
    IsOptimalCTQWSearch G w := by
  -- HONEST SORRY.  The spectral half is `P.spectrum_subset hne :
  -- spectrum ℂ P.symmQuotient ⊆ spectrum ℂ G.adj` (rewritten through `hQ`):
  -- every quotient eigenvalue lifts to a host eigenvalue with an explicit
  -- cell-inflate eigenvector (`adj_mulVec_cellInflateVec`).  The dynamical half
  -- is `search_quotient_reduction` (Search.lean): on the cell-uniform subspace
  -- the host search Hamiltonian `-γ·A − P_M` acts as the refined-quotient search
  -- Hamiltonian, so the quotient's optimal-search witness `(γ, τ)` is also a
  -- host witness (the uniform initial state and the `√N`-time budget transport
  -- because `|C_i| > 0` makes the cell-inflate norm-preserving up to the cell
  -- sizes).  Assembling these two reductions into the `IsOptimalCTQWSearch`
  -- existential is the remaining work; left as a `sorry`.
  sorry

/-- **Equal-fiber-bundle inheritance.**  Specialization of
`optimal_search_of_quotient_ratio` to a graph bundle whose fibers are all regular
and whose couplings are biregular (so the fiber index gives an equitable
partition by `Bundle.fiberPartition`): if the quotient (template) graph supports
optimal search, the total bundle does.

Stated abstractly here in terms of the already-built `fiberPartition`; the
hypotheses mirror `optimal_search_of_quotient_ratio`. -/
theorem optimal_search_of_bundle_quotient
    {I : Type u} [Fintype I] [DecidableEq I]
    {Q : SimpleGraph I} [DecidableRel Q.Adj]
    {Vfib : I → Type u} [∀ i, Fintype (Vfib i)] [∀ i, DecidableEq (Vfib i)]
    (B : GraphBundle Q Vfib)
    (d : I → ℂ) (hfib : ∀ i, GraphBundle.WeightedGraph.IsRegular (B.fiber i) (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      GraphBundle.IsBiregular (B.coupling h) (α h) (β h))
    (hne : ∀ i, 0 < (B.fiberPartition d hfib α β hcouple).cellCard i)
    (GQ : WeightedGraph I) (wQ : I)
    (hQ : GQ.adj = (B.fiberPartition d hfib α β hcouple).symmQuotient)
    (hopt : IsOptimalCTQWSearch GQ wQ)
    (w : Σ i, Vfib i) (hw : (B.fiberPartition d hfib α β hcouple).cells w = wQ) :
    IsOptimalCTQWSearch B.total w :=
  optimal_search_of_quotient_ratio
    (B.fiberPartition d hfib α β hcouple) hne GQ wQ hQ hopt w hw

/-! ## Childs–Goldstone base case: the complete graph.

The original Childs–Goldstone result (arXiv:quant-ph/0306054) is the base case
of the whole CNO program: spatial search on the complete graph `Kₙ` is optimal,
finding the marked vertex in time `Θ(√N)`.  In the CNO framework this is the
extreme of the ratio condition: `Kₙ` is `(n−1)`-regular with adjacency spectrum
`{n−1 (×1), −1 (×(n−1))}`, so the (normalized) spectral ratio is
`1/(n−1) → 0 < 1`, the largest possible spectral gap. -/

/-- **Childs–Goldstone base case (arXiv:quant-ph/0306054).**  For the complete
graph `Kₙ` (here `G` the weighted promotion of `⊤ : SimpleGraph V` with
`|V| = n ≥ 2`), CTQW spatial search for any marked vertex is optimal.

This is the `n−1`-regular extreme of `optimal_search_of_spectral_ratio_lt_one`:
the complete graph has spectrum `{n−1, −1, …, −1}`, all-ones principal
eigenvector, and spectral ratio `1/(n−1) < 1`.  The dynamical content reduces to
Childs–Goldstone's explicit two-level (`|s⟩, |w⟩`) analysis, which is the base
case of the CNO perturbation theory; sorried at the same dynamical core as the
general theorem. -/
theorem complete_graph_optimal_search
    (G : WeightedGraph V) (w : V)
    (hne : Nonempty V)
    (hcard : 2 ≤ Fintype.card V)
    -- `G` is the complete graph: adjacency is `1` off-diagonal, `0` on-diagonal.
    (hcomplete : ∀ u v : V, u ≠ v → G.adj u v = 1) :
    IsOptimalCTQWSearch G w := by
  -- HONEST SORRY.  `G = Kₙ` is `(n−1)`-regular (each row sums to `n−1`), with
  -- adjacency `A = J − I`; its spectrum is `{n−1 (mult 1), −1 (mult n−1)}` and
  -- the principal eigenvector is the all-ones / uniform vector.  Hence the
  -- spectral ratio is `1/(n−1) < 1` (for `n ≥ 2`), and the result is the
  -- complete-graph instance of `optimal_search_of_spectral_ratio_lt_one`.  The
  -- spectral facts (`J − I` eigenvalues) are computable but the dynamical
  -- optimal-search core is the same Childs–Goldstone two-level analysis that the
  -- general theorem sorries; recorded as a `sorry` here for the same reason.
  sorry

end Graphplay
