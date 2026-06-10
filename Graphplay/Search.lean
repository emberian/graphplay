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

/-- **The search Hamiltonian is symmetric when the adjacency is.**  For a graph
with *symmetric* adjacency (`G.adj u v = G.adj v u`, i.e. real-symmetric — the
standard 0/1 or real-weighted undirected case), `H = -γ·A − P_M` is a symmetric
matrix (`Hᵀ = H`); the diagonal projector `P_M` is symmetric and `A` is by
hypothesis. -/
theorem WeightedGraph.searchHamiltonian_transpose_of_symm
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (M : Finset V)
    (γ : ℝ) (hsymm : ∀ u v : V, G.adj u v = G.adj v u) :
    Matrix.transpose (G.searchHamiltonian M γ) = G.searchHamiltonian M γ := by
  ext u v
  simp only [Matrix.transpose_apply, WeightedGraph.searchHamiltonian]
  rw [hsymm v u]
  by_cases h : u = v
  · subst h; simp
  · rw [if_neg (fun hc => h hc.1.symm), if_neg (fun hc => h hc.1)]

/-- **The search evolution is symmetric when the adjacency is.**  Since
`H = -γ·A − P_M` is symmetric (`searchHamiltonian_transpose_of_symm`), and
matrix exponential commutes with transpose (`Matrix.exp_transpose`), the
propagator `U(τ) = exp(-iτ·H)` is a *symmetric* matrix: `U(τ)ᵀ = U(τ)`.  (It is
unitary by Hermiticity; here it is additionally symmetric, hence *orthogonal up
to phase* — the real-symmetric-Hamiltonian special case.) -/
theorem WeightedGraph.searchEvolve_transpose_of_symm
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (M : Finset V)
    (γ τ : ℝ) (hsymm : ∀ u v : V, G.adj u v = G.adj v u) :
    Matrix.transpose (G.searchEvolve M γ τ) = G.searchEvolve M γ τ := by
  unfold WeightedGraph.searchEvolve
  rw [← Matrix.exp_transpose, Matrix.transpose_smul,
    G.searchHamiltonian_transpose_of_symm M γ hsymm]

/-- **Entrywise symmetry of the search propagator** for symmetric adjacency:
`U(τ)_{u,v} = U(τ)_{v,u}`.  This is what makes the genuine row success
amplitude `∑_v U_{m,v}` (the Childs–Goldstone `⟨w|U|s⟩` functional) coincide
with the column sum `∑_v U_{v,m}` for the real-symmetric search graphs
(complete graph, hypercube, lattice, …). -/
theorem WeightedGraph.searchEvolve_apply_comm_of_symm
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) (M : Finset V)
    (γ τ : ℝ) (hsymm : ∀ u v : V, G.adj u v = G.adj v u) (u v : V) :
    G.searchEvolve M γ τ u v = G.searchEvolve M γ τ v u := by
  have h := congrFun (congrFun (G.searchEvolve_transpose_of_symm M γ τ hsymm) v) u
  rwa [Matrix.transpose_apply] at h

/-- Optimal spatial search: starting from the **uniform** state
`|s⟩ = 𝟙/√N` (`N = card V`), the search evolution `U(τ)` reaches the marked
subspace with constant success amplitude in time `τ`.  The constant is taken
as `1/√2` here for concreteness.

**Marked-subspace success functional (Childs–Goldstone).**  The success
amplitude is the marked-block projection of `U(τ)|s⟩`:

  `⟨w|U(τ)|s⟩ = ∑_{m∈M} (U(τ)·s)_m = ∑_{m∈M} (∑_v U(τ)_{m,v})/√N`,

i.e. the matrix element of `U(τ)` between the uniform start `|s⟩` and
the (unnormalised) marked indicator `|M⟩ = ∑_{m∈M}|m⟩`.  The amplitude is
`Real.sqrt N`-normalised (only on the start `|s⟩`; the marked indicator is
*not* renormalised, exactly as in Childs–Goldstone, so the constant `1/√2` is
the standard `Θ(1)` success threshold).

The row/column orientation matters: summing `U(τ)_{v,m}` over *all*
rows `v`,
`‖∑_v ∑_{m∈M} U(τ)_{v,m}/√N‖ = ‖⟨s|U(τ)|M⟩‖`, is the success amplitude
of the *time-reversed* search (`|M⟩ → |s⟩`), equal to
`‖⟨w|U(τ)|s⟩‖` only when `U(τ)` is *symmetric* (real-symmetric adjacency).
Since `WeightedGraph.adj` is merely *Hermitian*, the two differ in general,
so the row form below — the `⟨w|U|s⟩` projection — is the faithful
Childs–Goldstone functional. -/
def IsOptimalSearch {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (M : Finset V) (γ τ : ℝ) : Prop :=
  ‖(∑ m, if m ∈ M
              then (∑ v, G.searchEvolve M γ τ m v) / Real.sqrt (Fintype.card V)
              else 0)‖ ≥ 1 / Real.sqrt 2

/-! ### Marked-refined equitable partitions

Given a partition by cells `I` and a marked set `M`, the marked-refined
partition uses index `I × Bool`: `(i, true)` is `Cᵢ ∩ M` and `(i, false)` is
`Cᵢ \ M`. -/

/-- The marked-refined index type. -/
abbrev MarkedRefined (I : Type v) : Type v := I × Bool

/-- Refine an equitable partition by intersecting each cell with the marked set.

The refinement is equitable precisely when the marked set is a **union
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
quotient.  Bernard–Tamon–Vinet–Xie (arXiv:2211.14704, Lin. Alg. Appl. 2025) study
the attached-tail / `K_n + path` family (where transfer *persists* along the tail);
the attached-tail special case here is its finite parent. -/
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

/-! ### The cell-embedding isometry and the evolution-level intertwining.

`search_quotient_reduction` is the *generator*-level statement (`H_search` acts as
the refined-quotient generator on the cell-uniform subspace).  To lift *optimal
search* we need the same identity for the *evolution* `U(τ) = exp(-iτ·H_search)`,
obtained by intertwining the matrix exponential through the **cell-embedding
matrix** `E'` (columns = normalized cell indicators), and then projecting onto the
marked rows.  The genuine host start `|s⟩ = 𝟙/√N` is the cell-embedding image of
the **cell-mass vector** `m̂_{ib} = √|C'_{ib}|` (each normalized cell indicator
rescaled to the raw indicator), so the host success amplitude is *exactly* the
refined-quotient block amplitude contracted against the cell masses on both the
start and the marked projection — the genuine quotient-side functional. -/

section CellEmbedLift

open NormedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {V : Type u} [Fintype V] [DecidableEq V]
  {I : Type v} [Fintype I] [DecidableEq I]
  {G : WeightedGraph V}

/-- The **cell-embedding matrix** of an equitable partition: the `V × I` matrix
whose `(v, i)` entry is `cellUniformVec i v`.  Its columns are the normalized cell
indicators; `mulVec` is the canonical cell-uniform combination map. -/
noncomputable def cellEmbed (P : EquitablePartition G I) : Matrix V I ℂ :=
  fun v i => P.cellUniformVec i v

/-- `cellEmbed.mulVec w` is the cell-uniform combination `∑ i, w i · e_i`. -/
theorem cellEmbed_mulVec (P : EquitablePartition G I) (w : I → ℂ) :
    (cellEmbed P).mulVec w = fun v => ∑ i, w i * P.cellUniformVec i v := by
  funext v
  simp only [cellEmbed, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- The **cell-mass vector** `m̂_i = √|C_i|`: the chain image of the host uniform
state's *unnormalized* weights. -/
noncomputable def massVec (P : EquitablePartition G I) : I → ℂ :=
  fun i => (Real.sqrt (P.cellCard i) : ℂ)

/-- **The cell-embedding of the cell-mass vector is the all-ones vector.**  Each
normalized cell indicator `e_i = 𝟙_{C_i}/√|C_i|`, rescaled by `√|C_i|`, is the raw
indicator `𝟙_{C_i}`; summing the raw indicators over all cells gives `𝟙`.  Hence
`E·m̂ = 𝟙`, i.e. the host uniform start `|s⟩ = 𝟙/√N` is the cell-embedding image of
`m̂/√N` — the chain image of the uniform state. -/
theorem cellEmbed_mulVec_massVec (P : EquitablePartition G I)
    (hne : ∀ i, 0 < P.cellCard i) :
    (cellEmbed P).mulVec (massVec P) = (fun _ => (1 : ℂ)) := by
  funext v
  rw [cellEmbed_mulVec]
  simp only [massVec]
  rw [Finset.sum_eq_single (P.cells v)]
  · unfold EquitablePartition.cellUniformVec
    rw [if_pos rfl]
    have hne' : (Real.sqrt (P.cellCard (P.cells v)) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      exact ne_of_gt (Real.sqrt_pos.mpr (hne (P.cells v)))
    field_simp
  · intro i _ hi
    unfold EquitablePartition.cellUniformVec
    rw [if_neg (fun h => hi h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Generator-level search intertwining through the cell-embedding.**  Packaging
`search_quotient_reduction` as a matrix identity (one column per refined cell):
the host search Hamiltonian acts on the refined cell-uniform subspace as the
refined-quotient generator `H_chain = -γ·Q̃' − markedDiag`. -/
theorem searchH_mul_cellEmbed (P : EquitablePartition G I) (M : Finset V) (γ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M)) :
    let P' := P.refineByMarked M hM
    G.searchHamiltonian M γ * cellEmbed P'
      = cellEmbed P' * (-(γ : ℂ) • P'.symmQuotient - markedDiag I) := by
  intro P'
  apply Matrix.ext_of_mulVec_single
  intro jb
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [cellEmbed_mulVec P' (Pi.single jb (1 : ℂ))]
  rw [search_quotient_reduction P M γ hM (Pi.single jb (1 : ℂ))]
  rw [cellEmbed_mulVec P' ((-(γ : ℂ) • P'.symmQuotient - markedDiag I).mulVec (Pi.single jb 1))]

/-- **Generic exponential intertwining through a rectangular embedding.**  If
`H · E = E · M` (intertwining at the generator level), then
`exp(s•H) · E = E · exp(s•M)`.  Pushes the power intertwining through the
convergent `exp` series. -/
theorem exp_intertwine_cellEmbed (H : Matrix V V ℂ) (E : Matrix V I ℂ)
    (M : Matrix I I ℂ) (s : ℂ) (hHE : H * E = E * M) :
    NormedSpace.exp (s • H) * E = E * NormedSpace.exp (s • M) := by
  have hpow : ∀ k : ℕ, (s • H) ^ k * E = E * (s • M) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : (s • H) * E = E * (s • M) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, hHE]
      rw [pow_succ, pow_succ, Matrix.mul_assoc, hstep, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  let φ : Matrix V V ℂ →+ Matrix V I ℂ :=
    { toFun := fun A => A * E, map_zero' := Matrix.zero_mul _,
      map_add' := fun A C => Matrix.add_mul A C _ }
  have hφc : Continuous φ := Continuous.matrix_mul continuous_id continuous_const
  let ψ : Matrix I I ℂ →+ Matrix V I ℂ :=
    { toFun := fun N => E * N, map_zero' := Matrix.mul_zero _,
      map_add' := fun M₁ M₂ => Matrix.mul_add _ M₁ M₂ }
  have hψc : Continuous ψ := Continuous.matrix_mul continuous_const continuous_id
  have hH : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k)
      (NormedSpace.exp (s • H)) := exp_series_hasSum_exp' _
  have hM : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k)
      (NormedSpace.exp (s • M)) := exp_series_hasSum_exp' _
  have hHφ := hH.map φ hφc
  have hMψ := hM.map ψ hψc
  have hterm : (φ ∘ fun k => (Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k)
      = (ψ ∘ fun k => (Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k) := by
    funext k
    show ((Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k) * E
        = E * ((Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k)
    rw [Matrix.smul_mul, Matrix.mul_smul, hpow k]
  rw [hterm] at hHφ
  exact hHφ.unique hMψ

/-- **Evolution-level search intertwining through the cell-embedding.**  The full
search evolution `U(τ) = exp(-iτ·H_search)`, restricted to the refined cell-uniform
subspace, is the refined-quotient chain evolution `exp(-iτ·H_chain)`:
`U(τ) · E' = E' · exp(-iτ·H_chain)`. -/
theorem searchEvolve_mul_cellEmbed (P : EquitablePartition G I) (M : Finset V) (γ τ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M)) :
    let P' := P.refineByMarked M hM
    G.searchEvolve M γ τ * cellEmbed P'
      = cellEmbed P'
        * NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
            (-(γ : ℂ) • P'.symmQuotient - markedDiag I)) := by
  intro P'
  unfold WeightedGraph.searchEvolve
  exact exp_intertwine_cellEmbed _ _ _ _ (searchH_mul_cellEmbed P M γ hM)

/-- **Marked-row projection of a refined cell-uniform combination.**  Summing a
cell-uniform combination `E'·z` over the marked rows `m ∈ M` contracts `z` against
the cell masses `√|C'_{ib}|` over the *marked* refined cells `(·, true)` — because
each refined cell lies wholly in or out of `M`, the marked rows are exactly the
union of the `(·, true)` cells, and summing the value `z_{ib}/√|C'_{ib}|` over the
`|C'_{ib}|` vertices of a marked cell gives `√|C'_{ib}|·z_{ib}`. -/
theorem markedProj_cellEmbed (P : EquitablePartition G I) (M : Finset V)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M)) (z : MarkedRefined I → ℂ) :
    let P' := P.refineByMarked M hM
    (∑ m, if m ∈ M then ((cellEmbed P').mulVec z) m else 0)
      = ∑ ib : MarkedRefined I,
          (if ib.2 = true then (Real.sqrt (P'.cellCard ib) : ℂ) * z ib else 0) := by
  intro P'
  classical
  -- Pointwise, `(E'·z) m = z (cell m) · e_{cell m} m`, only the own-cell term survives.
  have hpt : ∀ m : V, ((cellEmbed P').mulVec z) m
      = z (P'.cells m) * P'.cellUniformVec (P'.cells m) m := by
    intro m
    rw [cellEmbed_mulVec]
    simp only
    rw [Finset.sum_eq_single (P'.cells m)]
    · intro ib _ hib
      have : P'.cellUniformVec ib m = 0 := by
        unfold EquitablePartition.cellUniformVec
        rw [if_neg (fun h => hib h.symm)]
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hev : ∀ m : V, P'.cellUniformVec (P'.cells m) m
      = (1 : ℂ) / (Real.sqrt (P'.cellCard (P'.cells m)) : ℂ) := by
    intro m; unfold EquitablePartition.cellUniformVec; rw [if_pos rfl]
  -- Rewrite the LHS as a sum depending only on `P'.cells m`, gated by `(cells m).2`.
  rw [show (∑ m, if m ∈ M then ((cellEmbed P').mulVec z) m else 0)
        = ∑ m, (if (P'.cells m).2 = true
                  then z (P'.cells m) * (1 / (Real.sqrt (P'.cellCard (P'.cells m)) : ℂ)) else 0)
      from ?_]
  · -- Group by cell; each marked cell `ib` contributes `|C'_ib|·z_ib/√|C'_ib| = √|C'_ib|·z_ib`.
    rw [← Finset.sum_fiberwise_of_maps_to (g := P'.cells)
        (fun m _ => Finset.mem_univ (P'.cells m))]
    apply Finset.sum_congr rfl
    intro ib _
    by_cases hb : ib.2 = true
    · rw [if_pos hb]
      have hconst : ∀ m ∈ Finset.univ.filter (fun m => P'.cells m = ib),
          (if (P'.cells m).2 = true
              then z (P'.cells m) * (1 / (Real.sqrt (P'.cellCard (P'.cells m)) : ℂ)) else 0)
            = z ib * (1 / (Real.sqrt (P'.cellCard ib) : ℂ)) := by
        intro m hm; rw [Finset.mem_filter] at hm; rw [hm.2, if_pos hb]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcardeq : ((Finset.univ.filter (fun m => P'.cells m = ib)).card : ℂ)
          = (P'.cellCard ib : ℂ) := by
        unfold EquitablePartition.cellCard; push_cast; rfl
      rw [hcardeq]
      by_cases hc0 : P'.cellCard ib = 0
      · rw [hc0]; simp
      · have hpos : 0 < P'.cellCard ib :=
          lt_of_le_of_ne (P'.cellCard_nonneg ib) (Ne.symm hc0)
        have hsqne : (Real.sqrt (P'.cellCard ib) : ℂ) ≠ 0 := by
          rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (Real.sqrt_pos.mpr hpos)
        have hsq : (Real.sqrt (P'.cellCard ib) : ℂ) * (Real.sqrt (P'.cellCard ib) : ℂ)
            = (P'.cellCard ib : ℂ) := by
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (P'.cellCard_nonneg ib)]
        rw [← hsq]; field_simp
    · rw [if_neg hb]
      apply Finset.sum_eq_zero
      intro m hm; rw [Finset.mem_filter] at hm; rw [hm.2, if_neg hb]
  · apply Finset.sum_congr rfl
    intro m _
    rw [hpt m, hev m]
    have hmem : (m ∈ M) ↔ (P'.cells m).2 = true := by
      show (m ∈ M) ↔ (P.cells m, decide (m ∈ M)).2 = true; simp
    by_cases hmM : m ∈ M
    · rw [if_pos hmM, if_pos (hmem.mp hmM)]
    · rw [if_neg hmM, if_neg (fun h => hmM (hmem.mpr h))]

end CellEmbedLift

/-- **Optimal search on the refined quotient** (genuine, host-faithful hypothesis
form).  This is the **exact** refined-quotient image of the host's uniform-overlap
success amplitude `⟨𝟙_M | U(τ) | 𝟙⟩/√N`.

The host start `|s⟩ = 𝟙/√N` is the cell-embedding image of the cell-mass weights
`m̂'_{jb} = √|C'_{jb}|` (`cellEmbed_mulVec_massVec`), and the marked indicator
`𝟙_M` projects a refined cell-uniform combination onto the cell masses over the
*marked* cells `(·, true)` (`markedProj_cellEmbed`).  Hence the quotient
amplitude is the refined-quotient block evolution `exp(-iτ·(-γ·Q̃' − markedDiag))`
applied to the cell-mass vector, contracted against the cell masses on the marked
cells, normalized by `√N`:

  `‖(∑_{ib.2=true} √|C'_{ib}| · (exp(-iτ·H_chain)·m̂')_{ib}) / √N‖ ≥ 1/√2`.

This `√|C'|`-weighting on *both* the start (`m̂'`) and the marked projection is
the correct chain image of the host functional (a
`1/√(2|I|)` uniform-over-quotient-cells weighting would match the host
only when all cells are equal-sized).
It is the host-faithful quotient-side analogue of `IsOptimalSearch`. -/
def IsRefinedQuotientOptimalSearch
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (M : Finset V)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M))
    (γ τ : ℝ) : Prop :=
  let P' := P.refineByMarked M hM
  ‖(∑ ib : MarkedRefined I,
      if ib.2 = true then
        (Real.sqrt (P'.cellCard ib) : ℂ) *
          ((NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
              (-(γ : ℂ) • P'.symmQuotient - markedDiag I))).mulVec
                (fun jb => (Real.sqrt (P'.cellCard jb) : ℂ))) ib
      else 0) / Real.sqrt (Fintype.card V)‖ ≥ 1 / Real.sqrt 2

/-- **Optimal search on the refined quotient lifts to optimal search on the
host.**  Given that the marked set is a union of cells (`hM`, so the marked-
refined partition is equitable and `search_quotient_reduction` applies) and all
refined cells are nonempty (`hne`), if the refined quotient supports optimal
search (in the host-faithful `IsRefinedQuotientOptimalSearch` sense) then so does
the host.

The proof is the exact transport of the
host success amplitude onto the finite refined-quotient chain:

* `∑_{m∈M} ∑_v U(τ)_{m,v} = ∑_{m∈M} (U(τ)·𝟙)_m` — the host functional is the
  marked-row projection of `U(τ)` applied to the all-ones vector `𝟙`;
* `𝟙 = E'·m̂'` with `m̂'_{ib} = √|C'_{ib}|` (`cellEmbed_mulVec_massVec`, using
  `hne`) — the uniform start is the cell-embedding image of the cell-mass vector;
* `U(τ)·E' = E'·exp(-iτ·H_chain)` (`searchEvolve_mul_cellEmbed`, the evolution-level
  intertwining built from `search_quotient_reduction`), so
  `U(τ)·𝟙 = E'·(exp(-iτ·H_chain)·m̂')`;
* `∑_{m∈M} (E'·z)_m = ∑_{ib.2=true} √|C'_{ib}|·z_{ib}` (`markedProj_cellEmbed`,
  each refined cell wholly in/out of `M`).

Composing these makes the host amplitude `‖∑_{m∈M}∑_v U_{m,v}/√N‖` *definitionally*
equal to the `IsRefinedQuotientOptimalSearch` amplitude, so the `≥ 1/√2` bound
transfers verbatim.  No symmetry of the adjacency is needed: the host functional
here is the `⟨𝟙_M|U(τ)|𝟙⟩` row projection. -/
theorem optimal_search_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) (M : Finset V)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M))
    (hne : ∀ i, 0 < (P.refineByMarked M hM).cellCard i)
    (γ τ : ℝ)
    (hquot : IsRefinedQuotientOptimalSearch P M hM γ τ) :
    IsOptimalSearch G M γ τ := by
  classical
  set P' := P.refineByMarked M hM with hP'
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  set Hc : Matrix (MarkedRefined I) (MarkedRefined I) ℂ :=
    -(γ : ℂ) • P'.symmQuotient - markedDiag I with hHc
  set U := G.searchEvolve M γ τ with hU
  set mhat : MarkedRefined I → ℂ := fun jb => (Real.sqrt (P'.cellCard jb) : ℂ) with hmhat
  -- The refined-quotient block column at the cell-mass start.
  set z : MarkedRefined I → ℂ := (NormedSpace.exp (s • Hc)).mulVec mhat with hz
  -- Fold the (host-faithful) quotient hypothesis to the `z`/`mhat`/`Hc` abbreviations.
  rw [IsRefinedQuotientOptimalSearch] at hquot
  simp only [← hP', ← hs, ← hHc, ← hmhat, ← hz] at hquot
  unfold IsOptimalSearch
  -- Step A: pull `/√N` out and rewrite the inner row sum `∑_v U_{m,v}` as `(U·𝟙)_m`.
  rw [show (∑ m, if m ∈ M then (∑ v, U m v) / Real.sqrt (Fintype.card V) else 0)
        = (∑ m, if m ∈ M then (U.mulVec (fun _ => (1 : ℂ))) m else 0)
            / Real.sqrt (Fintype.card V) from ?_]
  · -- Step C: `U·𝟙 = E'·z` via `𝟙 = E'·m̂'` and the evolution intertwining.
    have hone : (cellEmbed P').mulVec (massVec P') = (fun _ => (1 : ℂ)) :=
      cellEmbed_mulVec_massVec P' hne
    have hUone : U.mulVec (fun _ => (1 : ℂ)) = (cellEmbed P').mulVec z := by
      rw [← hone, Matrix.mulVec_mulVec]
      have hint : U * cellEmbed P' = cellEmbed P' * NormedSpace.exp (s • Hc) := by
        rw [hU, hHc, hs]; exact searchEvolve_mul_cellEmbed P M γ τ hM
      rw [hint, ← Matrix.mulVec_mulVec]; rfl
    rw [show (∑ m, if m ∈ M then (U.mulVec (fun _ => (1 : ℂ))) m else 0)
          = (∑ m, if m ∈ M then ((cellEmbed P').mulVec z) m else 0) from by rw [hUone]]
    -- Step D: marked-row projection onto the cell masses over the `(·, true)` cells.
    -- The result is exactly the (folded) `IsRefinedQuotientOptimalSearch` amplitude.
    rw [markedProj_cellEmbed P M hM z]
    exact hquot
  · -- Step A side goal: `∑_v U_{m,v} = (U·𝟙)_m` (all-ones), and factor `/√N`.
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : m ∈ M
    · rw [if_pos h, if_pos h]
      simp only [Matrix.mulVec, dotProduct, mul_one]
    · rw [if_neg h, if_neg h, zero_div]

/-- The infinite-attached-tail special case (Bernard–Tamon–Vinet–Xie,
arXiv:2211.14704): the distance-from-attachment partitions on an infinite tail
form a filtered diagram of equitable partitions whose colimit recovers the
full-tail walk.  Optimal search persists in the limit when it holds uniformly
along the diagram (matching the BTVX finite-graph *persistence* direction).

Finite-parent form: the unbounded-tail statement proper is about an
*unbounded* tail and requires an `InverseLimit`/`UnionGraph` extension not
present here.  What is provable at this finite level is the *quotient
lift* itself: given a family of marked-refined partitions `P n` all sharing the
marked-union property `hM n`, if for some truncation `n` the refined quotient
supports optimal search, then the (finite) host does.  The family and the
per-truncation quotient hypothesis are load-bearing via
`optimal_search_lift`. -/
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
