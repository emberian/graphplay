import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Defs.Filter
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST
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
of `A`), and `limUnder` yields exactly that
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

/-- The **signed graph** of a chiral signing: a `WeightedGraph` whose adjacency
is `σ.signed`.  Hermiticity is the signing's `herm`; looplessness follows from
`compatible` together with `G`'s own looplessness (`G.adj v v = 0 ⇒
σ.signed v v = 0`).  This packages the signed walk as a genuine quantum-walk
Hamiltonian so the proven cell-uniform/quotient machinery applies verbatim. -/
def ChiralMixingSigning.signedGraph {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} (σ : ChiralMixingSigning G) : WeightedGraph V where
  adj := σ.signed
  herm := σ.herm
  loopless := fun v => σ.compatible v v (G.loopless v)

/-- `σ.evolve t` is the CTQW evolution of the `signedGraph`: by definition both
are `exp(-(I·t) • σ.signed)`. -/
theorem ChiralMixingSigning.evolve_eq_signedGraph_evolve
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} (σ : ChiralMixingSigning G) (t : ℝ) :
    σ.evolve t = σ.signedGraph.evolve t := rfl

/-- The Gram matrix `Bᴴ * B` of `cellEmbed` collapses on a **nonempty** row `i`:
`(Bᴴ * B) i k = δ_{ik}` for that `i` (off-diagonal cells are orthogonal always;
the diagonal is `1` precisely when cell `i` is nonempty).  Unlike the global
`cellEmbed_conjTranspose_mul_cellEmbed`, this needs only `C_i ≠ ∅`, so it
applies entrywise even when *other* cells are empty. -/
theorem EquitablePartition.cellEmbed_gram_row {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) {i : I}
    (hi : P.cellCard i ≠ 0) (k : I) :
    (P.cellEmbedᴴ * P.cellEmbed) i k = if i = k then 1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, EquitablePartition.cellEmbed,
    EquitablePartition.cellUniformVec]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    have hsum : (∑ v, star (if P.cells v = i then (1:ℂ)/(Real.sqrt (P.cellCard i):ℂ) else 0)
                  * (if P.cells v = i then (1:ℂ)/(Real.sqrt (P.cellCard i):ℂ) else 0))
        = ∑ v, (if P.cells v = i then ((1:ℂ)/(Real.sqrt (P.cellCard i):ℂ))^2 else 0) := by
      apply Finset.sum_congr rfl; intro v _
      by_cases hv : P.cells v = i
      · rw [if_pos hv, if_pos hv, star_div₀, star_one, Complex.star_def,
          Complex.conj_ofReal]; ring
      · rw [if_neg hv, if_neg hv, star_zero, mul_zero]
    rw [hsum, ← Finset.sum_filter, Finset.sum_const]
    have hci : (0 : ℝ) < P.cellCard i :=
      lt_of_le_of_ne (P.cellCard_nonneg i) (Ne.symm hi)
    have hcardeq : ((Finset.univ.filter (fun v : V => P.cells v = i)).card : ℂ)
        = (P.cellCard i : ℂ) := by unfold EquitablePartition.cellCard; push_cast; rfl
    rw [nsmul_eq_mul, hcardeq]
    have hsq : (Real.sqrt (P.cellCard i) : ℂ) ^ 2 = (P.cellCard i : ℂ) := by
      rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (P.cellCard_nonneg i)]
    have hsqrt : (Real.sqrt (P.cellCard i) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (Real.sqrt_pos.mpr hci)
    field_simp; exact hsq.symm
  · rw [if_neg hik]
    apply Finset.sum_eq_zero; intro v _
    by_cases hvi : P.cells v = i
    · have hvk : P.cells v ≠ k := fun h => hik (hvi ▸ h)
      rw [if_neg hvk, mul_zero]
    · rw [if_neg hvi, star_zero, zero_mul]

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

/-- Under `ReducesToQuotient`, the original equitable partition `P` of `G` is
also equitable for the **signed** graph: since `σ.signed x z` depends only on
the cells of `x` and `z`, the cell-`j` branching of `σ.signed` from any two
vertices in the same cell coincides termwise. -/
def ChiralMixingSigning.signedPartition {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralMixingSigning G) (hred : σ.ReducesToQuotient P) :
    EquitablePartition σ.signedGraph I where
  cells := P.cells
  uniform := by
    intro i j x y hx hy
    -- `signedGraph.adj = σ.signed`; rewrite `σ.signed x z = σ.signed y z` cellwise.
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hz : P.cells z = j
    · rw [if_pos hz, if_pos hz]
      -- `cells x = i = cells y`, same `z`; `ReducesToQuotient` gives equality.
      exact hred x y z z (hx.trans hy.symm) rfl
    · rw [if_neg hz, if_neg hz]

/-- The **quotient cell-block amplitude**: the cell-block transition amplitude
of a *quotient-level* `I × I` propagator `W`, weighted by cell sizes.  This is
the quantity that, for the signed quotient, measures uniform mixing at the
quotient level; the host cell-block amplitude is conjecturally equal to it. -/
noncomputable def quotientCellBlockAmp {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I] {G : WeightedGraph V}
    (P : EquitablePartition G I) (W : Matrix I I ℂ) (i j : I) : ℂ :=
  (P.cellCard i : ℂ) * W i j * (P.cellCard j : ℂ)

/-- **Host–quotient cell-block identification.**  Under `ReducesToQuotient`,
the host walk's cell-block amplitude equals the quotient walk's weighted
cell-block amplitude for a propagator `W` induced by the signing on the
quotient.

This is the mixing analogue of the cell-uniform PST lift
(`EquitablePartition.pst_lift` in `Graphplay/PST.lean`), driven by the same
invariant-subspace intertwining `restrict_eq_symmQuotient` /
`exp_smul_adj_mul_cellEmbed`.

The witness `W` is the *quotient cell-block amplitude density*
`W i j = cellBlockAmp P (σ.evolve t) i j / (|C_i|·|C_j|)`.  For nonempty cells
this is exactly the entry of the quotient evolution
`exp(-iτ Q̃_S)` rescaled by the cell-uniform normalizations (the value forced by
the intertwining); for an empty cell both sides vanish identically.  The
resulting identity `cellBlockAmp = |C_i|·W i j·|C_j|` then holds for *all*
`i, j` simultaneously. -/
theorem cellBlockAmp_eq_quotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralMixingSigning G) (hred : σ.ReducesToQuotient P)
    (t : ℝ) :
    ∃ W : Matrix I I ℂ, ∀ i j : I,
      cellBlockAmp P (σ.evolve t) i j = quotientCellBlockAmp P W i j := by
  classical
  -- Work with the signed graph and its (equitable, by `hred`)
  -- partition `P'`; the PST/quotient machinery applies to it verbatim.
  set Gs := σ.signedGraph with hGs
  set P' := σ.signedPartition P hred with hP'
  -- `P'.cells = P.cells`, so cell cardinalities and cell-block sums agree.
  have hcells : ∀ v, P'.cells v = P.cells v := fun _ => rfl
  have hcard : ∀ k, P'.cellCard k = P.cellCard k := by
    intro k; unfold EquitablePartition.cellCard; simp_rw [hcells]
  set s : ℂ := -(Complex.I * (t : ℂ)) with hs
  -- The witness: the entry of the symmetric-quotient evolution `exp(s • Q̃)`,
  -- rescaled by `1/(√|C_i|·√|C_j|)` so that the `|C_i|·|C_j|` weighting of
  -- `quotientCellBlockAmp` reproduces the `√|C_i|·√|C_j|` normalization that
  -- the cell-uniform matrix element carries.
  refine ⟨fun i j =>
      (NormedSpace.exp (s • P'.symmQuotient)) i j /
        ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ)), ?_⟩
  intro i j
  unfold quotientCellBlockAmp
  -- The cell-block amplitude rewritten as a `cellUniform_matrixElement` of `P'`.
  -- `cellBlockAmp P U i j = ∑_{x∈C_i,y∈C_j} U x y`; the PST matrix-element lemma
  -- (with indices swapped) gives `∑_{x∈C_j,y∈C_i} U y x / (√|C_j|√|C_i|) =
  -- (Bᴴ U B) i j`, and the two double sums coincide after `Finset.sum_comm`.
  have hswap : cellBlockAmp P (σ.evolve t) i j
      = ∑ x, ∑ y, if P'.cells x = j ∧ P'.cells y = i
          then σ.evolve t y x else 0 := by
    unfold cellBlockAmp
    simp_rw [hcells]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
    by_cases h : P.cells x = i ∧ P.cells y = j
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun hc => h ⟨hc.2, hc.1⟩)]
  -- Either both cells are nonempty (the matrix-element identity applies and the
  -- normalizations recombine), or one is empty (both sides vanish).
  by_cases hi : P.cellCard i = 0
  · have hamp : cellBlockAmp P (σ.evolve t) i j = 0 := by
      unfold cellBlockAmp
      apply Finset.sum_eq_zero; intro x _
      apply Finset.sum_eq_zero; intro y _
      by_cases hx : P.cells x = i
      · exfalso
        have : (Finset.univ.filter fun w : V => P.cells w = i).Nonempty :=
          ⟨x, by simp [hx]⟩
        rw [← Finset.card_pos] at this
        exact absurd (by unfold EquitablePartition.cellCard at hi; exact_mod_cast hi) this.ne'
      · rw [if_neg (fun h => hx h.1)]
    rw [hamp]; simp [hi]
  · by_cases hj : P.cellCard j = 0
    · have hamp : cellBlockAmp P (σ.evolve t) i j = 0 := by
        unfold cellBlockAmp
        apply Finset.sum_eq_zero; intro x _
        apply Finset.sum_eq_zero; intro y _
        by_cases hy : P.cells y = j
        · exfalso
          have : (Finset.univ.filter fun w : V => P.cells w = j).Nonempty :=
            ⟨y, by simp [hy]⟩
          rw [← Finset.card_pos] at this
          exact absurd (by unfold EquitablePartition.cellCard at hj; exact_mod_cast hj) this.ne'
        · rw [if_neg (fun h => hy h.2)]
      rw [hamp]; simp [hj]
    · -- Both cells nonempty.  Identify the cell-block amplitude with the
      -- symmetric-quotient evolution entry via the proven intertwining.
      have hsi : (Real.sqrt (P.cellCard i) : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]
        exact ne_of_gt (Real.sqrt_pos.mpr
          (lt_of_le_of_ne (P.cellCard_nonneg i) (Ne.symm hi)))
      have hsj : (Real.sqrt (P.cellCard j) : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]
        exact ne_of_gt (Real.sqrt_pos.mpr
          (lt_of_le_of_ne (P.cellCard_nonneg j) (Ne.symm hj)))
      -- `(Bᴴ * (σ.evolve t) * B) i j = exp(s • symmQuotient) i j`.  We need only
      -- cell `i` nonempty: `E·B = B·exp(s•Q̃)` (intertwining, no nonemptiness),
      -- then the row-`i` Gram collapse `(Bᴴ B) i k = δ_{ik}` (cell `i` nonempty).
      have hP'i : P'.cellCard i ≠ 0 := by rw [hcard]; exact hi
      have hev : σ.evolve t = NormedSpace.exp (s • Gs.adj) := rfl
      have hEB : σ.evolve t * P'.cellEmbed
          = P'.cellEmbed * NormedSpace.exp (s • P'.symmQuotient) := by
        rw [hev]; exact P'.exp_smul_adj_mul_cellEmbed s
      have hBEB : (P'.cellEmbedᴴ * σ.evolve t * P'.cellEmbed) i j
          = (NormedSpace.exp (s • P'.symmQuotient)) i j := by
        rw [Matrix.mul_assoc, hEB, ← Matrix.mul_assoc]
        -- `(Bᴴ * B * exp) i j = ∑_k (Bᴴ B) i k · exp k j = exp i j`.
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · rw [P'.cellEmbed_gram_row hP'i i, if_pos rfl, one_mul]
        · intro k _ hki
          rw [P'.cellEmbed_gram_row hP'i k, if_neg (fun h => hki h.symm), zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h
      -- The matrix-element identity for `P'` and `E = σ.evolve t`.
      have hme := P'.cellUniform_matrixElement (σ.evolve t) j i
      rw [hcard j, hcard i] at hme
      -- `cellBlockAmp = (Bᴴ E B) i j · (√|C_j|·√|C_i|)`.
      have hcb : cellBlockAmp P (σ.evolve t) i j
          = (P'.cellEmbedᴴ * σ.evolve t * P'.cellEmbed) i j *
              ((Real.sqrt (P.cellCard j) : ℂ) * (Real.sqrt (P.cellCard i) : ℂ)) := by
        rw [hswap, ← hme, div_mul_cancel₀]
        exact mul_ne_zero hsj hsi
      rw [hcb, hBEB]
      -- Now both sides are `(exp(s•Q̃)) i j` times the same scalar; collapse the
      -- normalizations `√|C|·√|C| = |C|` (the `quotientCellBlockAmp` weighting).
      have hsqi : (Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard i) : ℂ)
          = (P.cellCard i : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (P.cellCard_nonneg i)]
      have hsqj : (Real.sqrt (P.cellCard j) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ)
          = (P.cellCard j : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (P.cellCard_nonneg j)]
      simp only [] -- beta-reduce the `W` lambda application
      rw [mul_comm ((P.cellCard i : ℂ))
        (NormedSpace.exp (s • P'.symmQuotient) i j / _), mul_assoc, div_mul_eq_mul_div,
        eq_div_iff (mul_ne_zero hsi hsj)]
      -- Goal (denominator cleared): collapse `√·√ = |C|` on both factors.
      linear_combination
        (NormedSpace.exp (s • P'.symmQuotient) i j) * (Real.sqrt (P.cellCard j) : ℂ)
            * (Real.sqrt (P.cellCard j) : ℂ) * hsqi
        + (NormedSpace.exp (s • P'.symmQuotient) i j) * (P.cellCard i : ℂ) * hsqj

/-- **Chiral mixing via quotient.**  If a chiral signing reduces to the quotient
and the quotient-level weighted cell-block amplitudes hit the uniform target,
then the signed host walk exhibits cell-uniform mixing.  The host/quotient
amplitude identification (`cellBlockAmp_eq_quotient`) supplies the only
non-elementary step.

The hypothesis must live on the *signed* quotient and the conclusion must
reference `σ`: the corresponding claim for the base walk `G.evolve' t` is
false (arbitrary `G`, `P`, `t` do not mix). -/
theorem chiralMixingQuotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (σ : ChiralMixingSigning G) (hred : σ.ReducesToQuotient P)
    (t : ℝ)
    -- Hypothesis: for the quotient propagator `W` produced by the
    -- host/quotient identification, the weighted cell-block amplitudes mix.
    (hmix : ∀ W : Matrix I I ℂ,
      (∀ i j : I, cellBlockAmp P (σ.evolve t) i j = quotientCellBlockAmp P W i j) →
      ∀ i j : I,
        ‖quotientCellBlockAmp P W i j‖ ^ 2 =
          ((Finset.univ.filter fun z => P.cells z = i).card *
            (Finset.univ.filter fun z => P.cells z = j).card : ℝ) /
            (Fintype.card V : ℝ) ^ 2) :
    IsCellUniformMixingOf P (σ.evolve t) := by
  -- Obtain the quotient propagator from the identification.
  obtain ⟨W, hW⟩ := cellBlockAmp_eq_quotient P σ hred t
  intro i j
  -- Rewrite the host cell-block amplitude as the quotient one, then apply `hmix`.
  rw [hW i j]
  exact hmix W hW i j

/-- **Average chiral mixing via quotient.**  The analogous transfer for the
time-averaged cell-block quantity of the signed walk: from a quotient-level
uniform-mixing hypothesis (via the same identification) we derive the host
average cell-block mixing.  As above, the hypothesis must live on the signed
quotient (the corresponding claim for `G.averageMixing` is false); the
derivation runs through `cellBlockAmp_eq_quotient`. -/
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
