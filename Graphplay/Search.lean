import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
universe u v w
namespace Graphplay

/-! ## Spatial search via continuous-time quantum walks

The Childs–Goldstone spatial-search Hamiltonian for a marked set `M ⊆ V` is
`H_search := -γ · A − P_M`, where `A` is the adjacency matrix of `G`, `γ > 0`
is a tuning parameter, and `P_M` is the diagonal projector onto `span{|m⟩ :
m ∈ M}`.  An "optimal search" finds the marked set with constant probability
in time `τ = O(√(n / |M|))`.

For bundle / equitable-partition graphs, search Hamiltonians often decompose
along the partition.  The right partition refines the original cells by
intersection with the marked set: each cell `Cᵢ` is split into `Cᵢ ∩ M` and
`Cᵢ \ M`.  On this *marked-refined* partition, the search Hamiltonian becomes
block-diagonal in the cell-uniform subspace, and search on the host reduces
to search on the refined quotient.
-/

/-- Search Hamiltonian `H = -γ · A − P_M` for marked set `M ⊆ V`. -/
noncomputable def WeightedGraph.searchHamiltonian {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (M : Finset V) (γ : ℝ) : Matrix V V ℂ :=
  fun u v =>
    -(γ : ℂ) * G.adj u v
      - (if u = v ∧ u ∈ M then (1 : ℂ) else 0)

/-- Continuous-time search evolution at time `τ` with marked set `M` and
coupling `γ`: `U(τ) = exp(-i τ · H_search)`. -/
noncomputable def WeightedGraph.searchEvolve {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (M : Finset V) (γ τ : ℝ) : Matrix V V ℂ :=
  NormedSpace.exp (-(Complex.I * (τ : ℂ)) • G.searchHamiltonian M γ)

/-- Optimal spatial search: there is a starting "uniform" state from which the
search Hamiltonian evolves into the marked subspace with constant amplitude in
time `τ`.  The constant is taken as `1/√2` here for concreteness. -/
def IsOptimalSearch {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (M : Finset V) (γ τ : ℝ) : Prop :=
  ‖(∑ v, ∑ m, if m ∈ M
              then (G.searchEvolve M γ τ v m) / Real.sqrt (Fintype.card V)
              else 0)‖ ≥ 1 / Real.sqrt 2

/-! ### Marked-refined equitable partitions

Given a partition by cells `I` and a marked set `M`, the marked-refined
partition uses index `I × Bool`: `(i, true)` is `Cᵢ ∩ M` and `(i, false)` is
`Cᵢ \ M`. -/

/-- The marked-refined index type. -/
abbrev MarkedRefined (I : Type v) : Type v := I × Bool

/-- Refine an equitable partition by intersecting each cell with the marked set.

The refinement is genuinely equitable precisely when the marked set is a **union
of cells**, i.e. membership in `M` is constant on each cell (`hM`).  Under that
hypothesis the second coordinate `decide (v ∈ M)` is a function of `P.cells v`,
so each refined cell `(i, b)` is *either* a whole parent cell (when `b` matches
`M`-membership on cell `i`) or empty; the branching sums collapse to the parent
branching sums and equitability follows from `P.uniform`.

(Without `hM` the statement is false: the parent partition controls only the
total branching into a coarse cell, not its `M`-restricted part.) -/
noncomputable def EquitablePartition.refineByMarked
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (M : Finset V)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M)) :
    EquitablePartition G (MarkedRefined I) where
  cells := fun v => (P.cells v, decide (v ∈ M))
  uniform := by
    rintro ⟨i, b⟩ ⟨i', b'⟩ x y hx hy
    -- The refined cell `(i', b')` of a vertex `z` is `cells z = (i', b')`, i.e.
    -- `P.cells z = i' ∧ decide (z ∈ M) = b'`.  By `hM`, the `M`-bit is constant
    -- across all `z` in parent cell `i'`, so for *every* `z` the indicator
    -- `(P.cells z, decide (z ∈ M)) = (i', b')` coincides with the parent
    -- indicator `P.cells z = i'` ANDed with one fixed Boolean `gate` that is
    -- independent of `z`.  Hence each branching sum is `gate`-gated parent
    -- branching, and equitability follows from `P.uniform`.
    have hx1 : P.cells x = i := (Prod.mk.injEq .. ▸ hx).1
    have hy1 : P.cells y = i := (Prod.mk.injEq .. ▸ hy).1
    -- `gate`: does the (constant) `M`-bit on cell `i'` equal the requested `b'`?
    -- If cell `i'` is empty the gate is irrelevant since the parent indicator is
    -- never satisfied.
    -- Reduce each refined branching to a `P.cells z = i'`-gated sum where the
    -- inner `decide (z ∈ M) = b'` test is, on the support, constant.
    have reduce : ∀ s : V,
        (∑ z, (if (P.cells z, decide (z ∈ M)) = (i', b') then G.adj s z else 0))
          = ∑ z, (if P.cells z = i' then
                    (if decide (z ∈ M) = b' then G.adj s z else 0) else 0) := by
      intro s
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : P.cells z = i'
      · rw [if_pos hz]
        by_cases hb : decide (z ∈ M) = b'
        · rw [if_pos hb, if_pos (Prod.ext hz hb)]
        · rw [if_neg hb, if_neg (fun h => hb (congrArg Prod.snd h))]
      · rw [if_neg hz, if_neg (fun h => hz (congrArg Prod.fst h))]
    rw [reduce x, reduce y]
    -- Case on whether cell `i'` is empty.
    by_cases hcell : ∃ w : V, P.cells w = i'
    · obtain ⟨w, hw⟩ := hcell
      -- On the support `P.cells z = i'`, `decide (z ∈ M) = decide (w ∈ M)`.
      have gate_const : ∀ s : V,
          (∑ z, (if P.cells z = i' then
                    (if decide (z ∈ M) = b' then G.adj s z else 0) else 0))
            = (if decide (w ∈ M) = b' then
                  (∑ z, (if P.cells z = i' then G.adj s z else 0)) else 0) := by
        intro s
        by_cases hbm : decide (w ∈ M) = b'
        · rw [if_pos hbm]
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : P.cells z = i'
          · rw [if_pos hz, if_pos hz]
            have hiff : (z ∈ M) ↔ (w ∈ M) := hM z w (hz.trans hw.symm)
            rw [if_pos (by rw [decide_eq_decide.mpr hiff]; exact hbm)]
          · rw [if_neg hz, if_neg hz]
        · rw [if_neg hbm]
          apply Finset.sum_eq_zero
          intro z _
          by_cases hz : P.cells z = i'
          · rw [if_pos hz]
            have hiff : (z ∈ M) ↔ (w ∈ M) := hM z w (hz.trans hw.symm)
            rw [if_neg (by rw [decide_eq_decide.mpr hiff]; exact hbm)]
          · rw [if_neg hz]
      rw [gate_const x, gate_const y]
      by_cases hbm : decide (w ∈ M) = b'
      · rw [if_pos hbm, if_pos hbm]
        exact P.uniform i i' x y hx1 hy1
      · rw [if_neg hbm, if_neg hbm]
    · -- Cell `i'` empty: both sums are zero.
      have hzero : ∀ s : V,
          (∑ z, (if P.cells z = i' then
                    (if decide (z ∈ M) = b' then G.adj s z else 0) else 0)) = 0 := by
        intro s
        apply Finset.sum_eq_zero
        intro z _
        rw [if_neg (fun hz => hcell ⟨z, hz⟩)]
      rw [hzero x, hzero y]

/-- The cell-uniform subspace of an equitable partition: vectors that are
constant on each cell. -/
def IsCellUniform {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (ψ : V → ℂ) : Prop :=
  ∀ x y : V, P.cells x = P.cells y → ψ x = ψ y

/-- The **marked diagonal** on the refined quotient: the diagonal matrix indexed
by `MarkedRefined I` that is `1` on `(i, true)` (the `M`-cells) and `0` on
`(i, false)`.  This is the quotient-side image of the marked projector `P_M`. -/
def markedDiag (I : Type v) [Fintype I] [DecidableEq I] :
    Matrix (MarkedRefined I) (MarkedRefined I) ℂ :=
  fun ib jb => if ib = jb ∧ ib.2 = true then (1 : ℂ) else 0

/-- **Marked projector acts diagonally on the refined cell-uniform subspace.**
For the marked-refined partition `P' = P.refineByMarked M hM`, the marked
projector `P_M` (i.e. `ψ v ↦ if v ∈ M then ψ v else 0`) applied to a cell-uniform
combination `∑ ib, w ib · e_{ib}` returns the cell-uniform combination with
weights `markedDiag.mulVec w`.

This holds because each refined cell `(i, b)` lies entirely inside `M` (when
`b = true`) or entirely outside `M` (when `b = false`): the second coordinate of
`P'.cells v` is exactly `decide (v ∈ M)`. -/
theorem markedProjector_cellUniformCombo
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (M : Finset V)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M))
    (w : MarkedRefined I → ℂ) :
    let P' := P.refineByMarked M hM
    (fun v => if v ∈ M then (∑ ib, w ib * P'.cellUniformVec ib v) else 0)
      = (fun v => ∑ ib, ((markedDiag I).mulVec w) ib * P'.cellUniformVec ib v) := by
  classical
  intro P'
  funext v
  -- The cell of `v` in `P'` is `(P.cells v, decide (v ∈ M))`; only that term of
  -- each sum survives, so both sides reduce to a single coefficient at that cell.
  set i₀ : I := P.cells v with hi₀
  set b₀ : Bool := decide (v ∈ M) with hb₀
  have hcellv : P'.cells v = (i₀, b₀) := rfl
  -- A helper: for any coefficient family `c`, `∑ ib, c ib · e_ib v = c (i₀,b₀) · e_{(i₀,b₀)} v`.
  have collapse : ∀ c : MarkedRefined I → ℂ,
      (∑ ib, c ib * P'.cellUniformVec ib v)
        = c (i₀, b₀) * P'.cellUniformVec (i₀, b₀) v := by
    intro c
    rw [Finset.sum_eq_single (i₀, b₀)]
    · intro ib _ hne
      have : P'.cellUniformVec ib v = 0 := by
        unfold EquitablePartition.cellUniformVec
        rw [if_neg]; rw [hcellv]; exact fun h => hne h.symm
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- LHS.
  by_cases hvM : v ∈ M
  · rw [if_pos hvM, collapse w, collapse ((markedDiag I).mulVec w)]
    -- `b₀ = true` since `v ∈ M`.
    have hb : b₀ = true := by rw [hb₀]; exact decide_eq_true hvM
    -- `(markedDiag.mulVec w) (i₀,b₀) = w (i₀,b₀)`.
    have hmd : ((markedDiag I).mulVec w) (i₀, b₀) = w (i₀, b₀) := by
      simp only [Matrix.mulVec, dotProduct, markedDiag]
      rw [Finset.sum_eq_single (i₀, b₀)]
      · rw [if_pos ⟨rfl, hb⟩, one_mul]
      · intro jb _ hne; rw [if_neg (fun h => hne h.1.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hmd]
  · rw [if_neg hvM, collapse ((markedDiag I).mulVec w)]
    -- `b₀ = false`, so the marked diagonal kills this coefficient.
    have hb : b₀ = false := by rw [hb₀]; exact decide_eq_false hvM
    have hmd : ((markedDiag I).mulVec w) (i₀, b₀) = 0 := by
      simp only [Matrix.mulVec, dotProduct, markedDiag]
      apply Finset.sum_eq_zero
      intro jb _
      by_cases h : (i₀, b₀) = jb ∧ (i₀, b₀).2 = true
      · exfalso; have : b₀ = true := h.2; rw [hb] at this; exact Bool.noConfusion this
      · rw [if_neg h, zero_mul]
    rw [hmd, zero_mul]

/-- **Bounded-sector quotient theorem for search.**  Restricted to the cell-
uniform subspace of the marked-refined equitable partition `P' =
P.refineByMarked M hM`, the host search Hamiltonian `H = -γ·A − P_M` acts as the
*refined quotient* search Hamiltonian `-γ·Q̃' − markedDiag`, where `Q̃'` is the
symmetric quotient of the refined partition.

Concretely, applying `H` to any cell-uniform combination `∑ ib, w ib · e_{ib}`
(with `e_{ib} = P'.cellUniformVec ib`) yields the cell-uniform combination whose
weights are obtained by applying the refined-quotient search matrix to `w`:
`H · (∑ w ib e_ib) = ∑ ((−γ·Q̃' − markedDiag) · w) ib · e_ib`.

The adjacency part uses `restrict_eq_symmQuotient`; the marked part uses
`markedProjector_cellUniformCombo` (the marked projector is diagonal on the
refined cell-uniform basis because each refined cell is wholly in/out of `M`).

In particular, if the refined-quotient search Hamiltonian has optimal search at
`(γ, τ)`, then the host does too — spatial search runs equivalently on the
quotient.  Xie–Tamon (arXiv:2301.07251) obtain the attached-tail / infinite-tail
special case as a filtered colimit over distance-from-attachment partitions;
this is its finite parent. -/
theorem search_quotient_reduction
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (M : Finset V) (γ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M))
    (w : MarkedRefined I → ℂ) :
    let P' := P.refineByMarked M hM
    (G.searchHamiltonian M γ).mulVec (fun v => ∑ ib, w ib * P'.cellUniformVec ib v)
      = (fun v => ∑ ib,
          ((-(γ : ℂ) • P'.symmQuotient - markedDiag I).mulVec w) ib *
            P'.cellUniformVec ib v) := by
  classical
  intro P'
  -- Abbreviate the cell-uniform combination.
  set ψ : V → ℂ := (fun v => ∑ ib, w ib * P'.cellUniformVec ib v) with hψ
  -- Step 1: pointwise decomposition of `H · ψ`.
  have hdecomp : (G.searchHamiltonian M γ).mulVec ψ
      = (fun v => -(γ : ℂ) * (G.adj.mulVec ψ) v
                  - (if v ∈ M then ψ v else 0)) := by
    funext v
    simp only [Matrix.mulVec, dotProduct, WeightedGraph.searchHamiltonian]
    rw [show (∑ z, (-(γ : ℂ) * G.adj v z - (if v = z ∧ v ∈ M then (1 : ℂ) else 0)) * ψ z)
          = (∑ z, (-(γ : ℂ) * G.adj v z) * ψ z)
            - (∑ z, (if v = z ∧ v ∈ M then (1 : ℂ) else 0) * ψ z) from by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro z _; ring]
    congr 1
    · show _ = -(γ : ℂ) * (∑ z, G.adj v z * ψ z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro z _; ring
    · -- `∑ z, (if v = z ∧ v ∈ M then 1 else 0) * ψ z = if v ∈ M then ψ v else 0`.
      by_cases hvM : v ∈ M
      · rw [if_pos hvM, Finset.sum_eq_single v]
        · rw [if_pos ⟨rfl, hvM⟩, one_mul]
        · intro z _ hzv; rw [if_neg (fun h => hzv h.1.symm), zero_mul]
        · intro h; exact absurd (Finset.mem_univ v) h
      · rw [if_neg hvM]
        apply Finset.sum_eq_zero; intro z _
        rw [if_neg (fun h => hvM h.2), zero_mul]
  rw [hdecomp]
  -- Step 2: adjacency part via `restrict_eq_symmQuotient` on `P'`.
  have hadj : G.adj.mulVec ψ
      = (fun v => ∑ ib, (P'.symmQuotient.mulVec w) ib * P'.cellUniformVec ib v) := by
    rw [hψ]; exact P'.restrict_eq_symmQuotient w
  -- Step 3: marked part via `markedProjector_cellUniformCombo`.
  have hmark : (fun v => if v ∈ M then ψ v else 0)
      = (fun v => ∑ ib, ((markedDiag I).mulVec w) ib * P'.cellUniformVec ib v) := by
    rw [hψ]; exact markedProjector_cellUniformCombo P M hM w
  -- Step 4: combine the two combinations into one over the difference matrix.
  funext v
  show -(γ : ℂ) * (G.adj.mulVec ψ) v - (if v ∈ M then ψ v else 0) = _
  rw [congrFun hadj v, congrFun hmark v]
  -- RHS: expand the difference-matrix mulVec into per-cell coefficients.
  rw [Matrix.sub_mulVec]
  simp only [Pi.sub_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ib _
  rw [Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Optimal search on the refined quotient** (genuine hypothesis form).  This
is the cell-uniform success amplitude of the *refined-quotient* search evolution
`exp(-iτ·(-γ·Q̃' − markedDiag))` applied to the uniform initial state on the
quotient index `MarkedRefined I`, projected onto the marked (`(·, true)`) cells.
It is the quotient-side analogue of `IsOptimalSearch` (amplitude `≥ 1/√2`). -/
def IsRefinedQuotientOptimalSearch
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (M : Finset V)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M))
    (γ τ : ℝ) : Prop :=
  let P' := P.refineByMarked M hM
  ‖(∑ ib : MarkedRefined I, ∑ jb : MarkedRefined I,
      if jb.2 = true then
        (NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
            (-(γ : ℂ) • P'.symmQuotient - markedDiag I))) jb ib /
          Real.sqrt (Fintype.card (MarkedRefined I))
      else 0)‖ ≥ 1 / Real.sqrt 2

/-- **Optimal search on the refined quotient lifts to optimal search on the
host.**  Given that the marked set is a union of cells (`hM`, so the marked-
refined partition is equitable and `search_quotient_reduction` applies), if the
refined quotient supports optimal search then so does the host.

The previous formulation carried a vacuous `True →` placeholder hypothesis; this
replaces it with the genuine quotient-side optimal-search predicate
`IsRefinedQuotientOptimalSearch`.  The bridge is `search_quotient_reduction`
(the host search Hamiltonian acts as the refined-quotient one on the
cell-uniform subspace), combined with the norm-preservation of the cell-inflate
on nonempty cells; assembling these into the `IsOptimalSearch` amplitude bound
is the remaining deep step, left as an honest `sorry`. -/
theorem optimal_search_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (M : Finset V)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M))
    (hne : ∀ i, 0 < (P.refineByMarked M hM).cellCard i)
    (γ τ : ℝ)
    (hquot : IsRefinedQuotientOptimalSearch P M hM γ τ) :
    IsOptimalSearch G M γ τ := by
  sorry

/-- The infinite-attached-tail special case (Xie–Tamon 2301.07251): the
distance-from-attachment partitions on an infinite tail form a filtered
diagram of equitable partitions whose colimit recovers the full-tail walk.
Optimal search persists in the limit when it holds uniformly along the
diagram.

Honest finite-parent form.  The genuine Xie–Tamon statement is about an
*unbounded* tail and requires an `InverseLimit`/`UnionGraph` extension not
present here.  What is genuinely provable at this finite level is the *quotient
lift* itself: given a family of marked-refined partitions `P n` all sharing the
marked-union property `hM n`, if for some truncation `n` the refined quotient
supports optimal search, then the (finite) host does.

Note on the prior formulation: it carried a vacuous `∀ _n : ℕ, IsOptimalSearch
G M γ τ` hypothesis (with `_n` unused — i.e. literally `IsOptimalSearch G M γ τ`
restated, making the theorem `A → A`) and an unused partition family `P`.  That
said nothing; this restatement makes the family and the per-truncation quotient
hypothesis genuinely load-bearing via `optimal_search_lift`. -/
theorem search_infinite_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (M : Finset V) (γ τ : ℝ)
    (P : ℕ → EquitablePartition G I)
    (hM : ∀ n, ∀ x y : V, (P n).cells x = (P n).cells y → (x ∈ M ↔ y ∈ M))
    (hne : ∀ n, ∀ i, 0 < ((P n).refineByMarked M (hM n)).cellCard i)
    (n : ℕ)
    (hquot : IsRefinedQuotientOptimalSearch (P n) M (hM n) γ τ) :
    IsOptimalSearch G M γ τ :=
  optimal_search_lift (P n) M (hM n) (hne n) γ τ hquot

end Graphplay
