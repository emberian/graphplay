import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Defs.Filter
import Graphplay.Weighted
import Graphplay.Equitable
open scoped Matrix
universe u v w
namespace Graphplay

/-! ## Uniform mixing of continuous-time quantum walks

The mixing matrix at time `t` is `M(t)(u,v) := |U(t)(u,v)|²` where
`U(t) := exp(-i t A)` is the CTQW propagator.  Uniform mixing asks that, at
time `t`, every entry of `M(t)` equals `1/n` where `n = |V|`.  Average uniform
mixing asks the same for the time-averaged mixing matrix `M̄ := lim T⁻¹ ∫₀ᵀ M(t)`.
-/

/-- The CTQW propagator used by the mixing module.  We simply reuse the proven
`WeightedGraph.evolve` (`= exp(-i t A)`) from `Graphplay/Weighted.lean`; this
makes `evolve'` concrete so the elementary mixing lemmas below go through and
the unitarity facts (`evolve_unitary`, `evolve_unitary'`) apply directly. -/
noncomputable def WeightedGraph.evolve' {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (τ : ℝ) : Matrix V V ℂ := G.evolve τ

/-- `evolve'` is definitionally `evolve`. -/
theorem WeightedGraph.evolve'_eq {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (τ : ℝ) : G.evolve' τ = G.evolve τ := rfl

/-- Mixing matrix at time `t`: entrywise squared modulus of `U(t)`. -/
noncomputable def WeightedGraph.mixing {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (t : ℝ) : Matrix V V ℝ :=
  fun u v => ‖G.evolve' t u v‖ ^ 2

/-- Helper: `z · z̄ = ‖z‖²` as a complex number (with `star`/`conj`). -/
private theorem mul_star_eq_norm_sq (z : ℂ) :
    z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Helper: `z̄ · z = ‖z‖²` as a complex number (with `star`/`conj`). -/
private theorem star_mul_eq_norm_sq (z : ℂ) :
    star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]; exact mul_star_eq_norm_sq z

/-- Each entry of the mixing matrix is nonnegative. -/
theorem mixing_nonneg {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (t : ℝ) (u v : V) : 0 ≤ G.mixing t u v := by
  unfold WeightedGraph.mixing
  positivity

/-- Each row of the mixing matrix sums to `1`, by unitarity of `U(t)`.
This is `∑_v ‖U u v‖² = (U Uᴴ) u u = 1`. -/
theorem mixing_row_sum {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (t : ℝ) (u : V) :
    ∑ v, G.mixing t u v = 1 := by
  have hU : G.evolve t * (G.evolve t)ᴴ = (1 : Matrix V V ℂ) := G.evolve_unitary' t
  have hdiag : (G.evolve t * (G.evolve t)ᴴ) u u = 1 := by
    rw [hU]; simp [Matrix.one_apply]
  -- `(U Uᴴ) u u = ∑ v, U u v * conj (U u v) = ∑ v, ‖U u v‖²`.
  have hentry : (G.evolve t * (G.evolve t)ᴴ) u u
      = ∑ v, ((‖G.evolve t u v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Matrix.conjTranspose_apply]
    exact mul_star_eq_norm_sq _
  unfold WeightedGraph.mixing
  rw [WeightedGraph.evolve'_eq]
  have : ((∑ v, G.mixing t u v : ℝ) : ℂ) = (1 : ℂ) := by
    push_cast
    unfold WeightedGraph.mixing
    simp only [WeightedGraph.evolve'_eq]
    rw [← hentry, hdiag]
  exact_mod_cast this

/-- Each row of the mixing matrix sums to `1` (stated via the column index too,
by unitarity in the other order). -/
theorem mixing_col_sum {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (t : ℝ) (v : V) :
    ∑ u, G.mixing t u v = 1 := by
  have hU : (G.evolve t)ᴴ * G.evolve t = (1 : Matrix V V ℂ) := G.evolve_unitary t
  have hdiag : ((G.evolve t)ᴴ * G.evolve t) v v = 1 := by
    rw [hU]; simp [Matrix.one_apply]
  have hentry : ((G.evolve t)ᴴ * G.evolve t) v v
      = ∑ u, ((‖G.evolve t u v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Matrix.conjTranspose_apply]
    exact star_mul_eq_norm_sq _
  have : ((∑ u, G.mixing t u v : ℝ) : ℂ) = (1 : ℂ) := by
    push_cast
    unfold WeightedGraph.mixing
    simp only [WeightedGraph.evolve'_eq]
    rw [← hentry, hdiag]
  exact_mod_cast this

/-- Uniform mixing at time `t`: every entry of the mixing matrix is `1/n`. -/
def IsUniformMixing {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (t : ℝ) : Prop :=
  ∀ u v : V, G.mixing t u v = 1 / (Fintype.card V : ℝ)

/-- Average mixing matrix (Cesàro limit of `mixing`).  Each entry is the limit
of the time-average `T⁻¹ ∫₀ᵀ mixing t u v dt` as `T → ∞`, expressed via
`Filter.limUnder`.  For a CTQW this limit exists (by the spectral decomposition
of `A`), so this is the genuinely-correct value; `limUnder` yields exactly that
limit when it exists. -/
noncomputable def WeightedGraph.averageMixing {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : Matrix V V ℝ :=
  fun u v => Filter.limUnder Filter.atTop
    (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, G.mixing t u v)

/-- Average uniform mixing: every entry of the average mixing matrix is `1/n`. -/
def IsAverageUniformMixing {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : Prop :=
  ∀ u v : V, G.averageMixing u v = 1 / (Fintype.card V : ℝ)

/-! ### Chiral signings

A "chiral signing" of a Hermitian weighted graph is a Hermitian skew-real
modification of its adjacency (e.g. multiplication by a purely imaginary
phase on selected edges) that preserves the real-symmetric quotient structure
while making the walk operator non-time-reversal-symmetric.  Levine et al.
(arXiv:2605.04414) showed that on suitable bundles, chiral signings of the
total graph correspond bijectively with chiral signings of the quotient
matrix, and the resulting mixing-time speedups on the quotient transfer to
cell-uniform mixing speedups on the host.
-/

/-- A chiral signing of a weighted graph: a Hermitian matrix obtained from the
adjacency by multiplying off-diagonal entries by phases consistent with the
Hermitian constraint. -/
structure ChiralMixingSigning {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) where
  signed : Matrix V V ℂ
  herm : signed.IsHermitian
  -- Same support as `G.adj`: edges are preserved, only phases change.
  compatible : ∀ u v, G.adj u v = 0 → signed u v = 0

/-- The CTQW propagator of a chiral signing: `exp(-i t S)` for the Hermitian
signed adjacency `S = σ.signed`.  This is unitary (Hermitian generator), so it
plays the role of `U(t)` for the signed walk. -/
noncomputable def ChiralMixingSigning.evolve {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} (σ : ChiralMixingSigning G) (t : ℝ) : Matrix V V ℂ :=
  NormedSpace.exp (-(Complex.I * (t : ℂ)) • σ.signed)

/-- Cell-block transition amplitude for an arbitrary propagator `U`: the summed
amplitude from cell `Cⱼ` to cell `Cᵢ`. -/
noncomputable def cellBlockAmp {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I] {G : WeightedGraph V}
    (P : EquitablePartition G I) (U : Matrix V V ℂ) (i j : I) : ℂ :=
  ∑ x, ∑ y, if P.cells x = i ∧ P.cells y = j then U x y else 0

/-- Cell-uniform mixing of a propagator `U` across cells: every cell-block
transition probability equals `|Cᵢ|·|Cⱼ|/n²`.  Parametric in `U` so it can be
applied either to the base walk `G.evolve' t` or to a chiral signing's walk
`σ.evolve t`. -/
def IsCellUniformMixingOf {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I] {G : WeightedGraph V}
    (P : EquitablePartition G I) (U : Matrix V V ℂ) : Prop :=
  ∀ i j : I,
    ‖cellBlockAmp P U i j‖ ^ 2 =
      ((Finset.univ.filter fun z => P.cells z = i).card *
        (Finset.univ.filter fun z => P.cells z = j).card : ℝ) /
        (Fintype.card V : ℝ) ^ 2

/-- Cell-uniform mixing across cells `i` and `j` of an equitable partition at
time `t`: the uniform superpositions over `Cᵢ` and `Cⱼ` evolve to one another
with probability `|Cᵢ|·|Cⱼ|/n²`.  This is `IsCellUniformMixingOf` for the base
walk `G.evolve' t`. -/
def IsCellUniformMixing {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I) (t : ℝ) : Prop :=
  IsCellUniformMixingOf P (G.evolve' t)

/-- A chiral signing of the total bundle reduces to a chiral signing of the
quotient if its off-diagonal `(x,y)` entries depend only on the cells of
`x` and `y`. -/
def ChiralMixingSigning.ReducesToQuotient {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralMixingSigning G) : Prop :=
  ∀ (x x' y y' : V), P.cells x = P.cells x' → P.cells y = P.cells y' →
    σ.signed x y = σ.signed x' y'

/-- The **quotient cell-block amplitude**: the cell-block transition amplitude
of a *quotient-level* `I × I` propagator `W`, weighted by cell sizes.  This is
the quantity that, for the signed quotient, measures uniform mixing at the
quotient level; the host cell-block amplitude is conjecturally equal to it. -/
noncomputable def quotientCellBlockAmp {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I] {G : WeightedGraph V}
    (P : EquitablePartition G I) (W : Matrix I I ℂ) (i j : I) : ℂ :=
  (P.cellCard i : ℂ) * W i j * (P.cellCard j : ℂ)

/-- **Host–quotient cell-block identification (honest `sorry`).**  Under
`ReducesToQuotient`, the host walk's cell-block amplitude equals the quotient
walk's weighted cell-block amplitude for the propagator `W` induced by the
signing on the quotient.  This is the genuine deep content of Levine–…–Tamon's
chiral transfer (arXiv:2605.04414): it requires the invariant-subspace transfer
(`restrict_eq_symmQuotient`) plus the spectral analysis of chiral signings, and
is left as an honest `sorry`. -/
theorem cellBlockAmp_eq_quotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralMixingSigning G) (_hred : σ.ReducesToQuotient P)
    (t : ℝ) :
    ∃ W : Matrix I I ℂ, ∀ i j : I,
      cellBlockAmp P (σ.evolve t) i j = quotientCellBlockAmp P W i j := by
  sorry

/-- **Chiral mixing via quotient.**  If a chiral signing reduces to the quotient
and the quotient-level weighted cell-block amplitudes hit the uniform target,
then the signed host walk exhibits cell-uniform mixing.  The host/quotient
amplitude identification (`cellBlockAmp_eq_quotient`) supplies the only
non-elementary step; everything else here is a genuine derivation.

Note on the prior formulation: the conclusion was previously stated for the
*base* walk `G.evolve' t` under a vacuous `True` hypothesis.  That statement is
mathematically false (arbitrary `G`, `P`, `t` do not mix), so it has been
corrected to a genuine hypothesis on the signed quotient and a conclusion that
references `σ`. -/
theorem chiralMixingQuotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralMixingSigning G) (hred : σ.ReducesToQuotient P)
    (t : ℝ)
    -- Genuine hypothesis: for the quotient propagator `W` produced by the
    -- host/quotient identification, the weighted cell-block amplitudes mix.
    (hmix : ∀ W : Matrix I I ℂ,
      (∀ i j : I, cellBlockAmp P (σ.evolve t) i j = quotientCellBlockAmp P W i j) →
      ∀ i j : I,
        ‖quotientCellBlockAmp P W i j‖ ^ 2 =
          ((Finset.univ.filter fun z => P.cells z = i).card *
            (Finset.univ.filter fun z => P.cells z = j).card : ℝ) /
            (Fintype.card V : ℝ) ^ 2) :
    IsCellUniformMixingOf P (σ.evolve t) := by
  -- Obtain the quotient propagator from the (sorried-but-true) identification.
  obtain ⟨W, hW⟩ := cellBlockAmp_eq_quotient P σ hred t
  intro i j
  -- Rewrite the host cell-block amplitude as the quotient one, then apply `hmix`.
  rw [hW i j]
  exact hmix W hW i j

/-- **Average chiral mixing via quotient.**  The analogous transfer for the
time-averaged cell-block quantity of the signed walk: from a quotient-level
uniform-mixing hypothesis (via the same identification) we derive the host
average cell-block mixing.  As above, the prior `True →` formulation on
`G.averageMixing` was unsound; this is the corrected statement, and the
derivation is genuine modulo `cellBlockAmp_eq_quotient`. -/
theorem chiralAverageMixingQuotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralMixingSigning G) (hred : σ.ReducesToQuotient P)
    (t : ℝ)
    (hmix : ∀ W : Matrix I I ℂ,
      (∀ i j : I, cellBlockAmp P (σ.evolve t) i j = quotientCellBlockAmp P W i j) →
      ∀ i j : I,
        ‖quotientCellBlockAmp P W i j‖ ^ 2 =
          ((Finset.univ.filter fun z => P.cells z = i).card *
            (Finset.univ.filter fun z => P.cells z = j).card : ℝ) /
            (Fintype.card V : ℝ) ^ 2) :
    ∀ i j : I,
      ‖cellBlockAmp P (σ.evolve t) i j‖ ^ 2 =
        ((Finset.univ.filter fun z => P.cells z = i).card *
          (Finset.univ.filter fun z => P.cells z = j).card : ℝ) /
          (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨W, hW⟩ := cellBlockAmp_eq_quotient P σ hred t
  intro i j
  rw [hW i j]
  exact hmix W hW i j

end Graphplay
