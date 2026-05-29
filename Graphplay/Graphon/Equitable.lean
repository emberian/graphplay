/-
# Graphon/Equitable.lean — the headline definition

This file contains what we believe is the **genuinely unpublished** core of
Graphplay: a definition of **equitable partition** for a graphon `W` on a
measure space `(Ω, μ)`, together with the statement of a **lifting theorem**
that identifies the restriction of the graphon transition operator `W.op` to
the "cell-uniform" subspace of `L²(μ)` with a finite Hermitian matrix — the
**quotient adjacency** induced by the partition.

This is the graphon-level analogue of the classical finite equitable-partition
theorem (Godsil–Royle, *Algebraic Graph Theory*, §9.3) and of the ODE
equitable-partition theorem for continuous dynamical systems
(Gerlach–von der Gönna, arXiv:2110.13686, Thm. 4.4).  We have not been able to
locate this theorem in the graphon literature; the closest ancestors are:

* the BCLSV graphon framework (cut-norm convergence, but no equitable
  partitions of the kernel), arXiv:1003.5588;
* the BCLSV stepping operator (the *uniform-partition* projection),
  arXiv:1003.5588 §3;
* the Bachman–Tamon analysis of perfect state transfer for finite graphs with
  an equitable partition (arXiv:1108.0339);
* the Gao–Caines graphon LQR control framework (arXiv:2004.00677), which uses
  graphon operators but does not invoke equitable partitions.

The headline operator-level lift theorem is stated as
`Graphon.cellUniformSubspaceInvariant` and its corollary
`Graphon.opRestrict_eq_quotient` below.  The cell-uniform subspace
`Graphon.cellUniformSubspace` is the closed subspace of `L²(μ; ℂ)` of functions
that are constant on each cell.

The raw divisor matrix `GraphonEquitablePartition.quotient` uses an *asymmetric*
per-cell normalisation `(μ_i)⁻¹` and is **not** Hermitian in general (only when
all cell masses coincide).  The genuinely Hermitian, spectrum-sharing object is
the **symmetric quotient** `GraphonEquitablePartition.symmQuotient =
D^{1/2} Q D^{-1/2}` (`symmQuotient_isHermitian`): it is the matrix of `W.op` in
the orthonormal `cellIndicator` basis, and its operator on `L²(I, counting)` is
**unitarily equivalent** to the restriction of `W.op` to the cell-uniform
subspace.  This mirrors the finite Tower-2 fix in `Graphplay.Equitable`
(`restrict_eq_symmQuotient`).

Notation:

* `Ω` ambient measure space, `μ` the measure;
* `I` finite index type for cells;
* `W : Graphon Ω μ` the kernel;
* `P : GraphonEquitablePartition W` an equitable partition;
* `C_i := P.cells ⁻¹' {i}` the cell of `i ∈ I`;
* `μ_i := μ (C_i)` the cell mass.

We always assume `0 < μ_i < ∞` for every `i`, since otherwise the cell is
degenerate (we restate this as the hypothesis `cells_finite_pos`).
-/

import Graphplay.Graphon

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory

universe u v

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The headline definition.**  A **graphon equitable partition** of a
graphon `W` on `(Ω, μ)` is a finite measurable partition `cells : Ω → I` of
`Ω` together with the **uniform-row-sum** property: for any pair of cells
`i, j ∈ I` and any two `x, y` in the same cell `i`, the *cell-restricted
column sums* are equal:
$$ \int_{C_j} W(x, z)\, d\mu(z) = \int_{C_j} W(y, z)\, d\mu(z). $$

This is the graphon analogue of the finite-graph notion (each vertex in cell
`i` has the same number of neighbours in cell `j`).

Auxiliary fields: positive finite cell mass, so that we can normalise
indicator vectors.

Reference for the closest classical statement: Godsil–Royle, *Algebraic Graph
Theory*, §9.3 (finite graphs).  The graphon-level version appears to be new. -/
structure _root_.Graphplay.GraphonEquitablePartition
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) where
  /-- The cell-membership function `Ω → I`. -/
  cells : Ω → I
  /-- The cell map is measurable. -/
  measurable_cells : @Measurable _ _ _ (⊤ : MeasurableSpace I) cells
  /-- Each cell has finite positive measure. -/
  cell_pos : ∀ i : I, 0 < μ (cells ⁻¹' {i})
  cell_finite : ∀ i : I, μ (cells ⁻¹' {i}) < ∞
  /-- **Uniform property** — for any two points `x, y` in the same cell, and
  any other cell `j`, the kernel restricted-and-integrated against the cell
  `j` is the same.

  This is the analytic shape of the equitable-partition condition. -/
  uniform : ∀ (i j : I) (x y : Ω),
    cells x = i → cells y = i →
    ∫ z, (if cells z = j then W.kernel x z else 0) ∂μ
      = ∫ z, (if cells z = j then W.kernel y z else 0) ∂μ

end Graphon

namespace GraphonEquitablePartition

/-- The cell `C_i := cells ⁻¹' {i}`. -/
def cell {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) : Set Ω :=
  P.cells ⁻¹' {i}

/-- The mass of the cell `C_i`, as an `ℝ`. -/
noncomputable def cellMass {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) : ℝ :=
  (μ (P.cell i)).toReal

theorem cellMass_pos {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) :
    0 < P.cellMass i := by
  unfold cellMass
  exact ENNReal.toReal_pos (ne_of_gt (P.cell_pos i)) (ne_of_lt (P.cell_finite i))

/-- The cell is measurable. -/
theorem measurableSet_cell {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) :
    MeasurableSet (P.cell i) := by
  -- preimage of the singleton `{i}` under `P.cells`, which is measurable
  -- w.r.t. the discrete MeasurableSpace on `I` (where every set is measurable).
  unfold GraphonEquitablePartition.cell
  exact P.measurable_cells (by trivial : @MeasurableSet I ⊤ {i})

/-! ### The quotient adjacency matrix

The **quotient adjacency** `P.quotient` is the `I × I` Hermitian complex matrix
whose `(i, j)` entry is
$$ B_{i j} \;=\; \frac{1}{\mu(C_i)} \int_{C_i \times C_j} W(x, z)\, d(\mu \otimes \mu).$$
Equivalently, for any fixed `x ∈ C_i`,
$$ B_{i j} = \int_{C_j} W(x, z)\, d\mu(z), $$
by the uniform property.  This is the **per-vertex** flux from cell `i` to
cell `j`.

We define it as an integral over `Ω`, picking out the cell-`j` part using a
characteristic function, and dividing by `μ(C_i)`.  The well-definedness
(independence on the choice of `x ∈ C_i`) is exactly `P.uniform`. -/

/-- The quotient adjacency matrix `B : I × I → ℂ`.  Defined as a "per-vertex"
cell-`j` flux from an arbitrary `x ∈ C_i`; the result is independent of the
choice of `x` by `P.uniform`. -/
noncomputable def quotient {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) : Matrix I I ℂ :=
  fun i j =>
    -- pick a representative of `C_i`; we use the cellMass-normalized integral
    -- to make the choice independent of the representative
    (P.cellMass i)⁻¹ • ∫ x in P.cell i,
      ∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ ∂μ

/-- The quotient adjacency, evaluated cell-by-cell, equals the per-vertex flux
out of any representative `x ∈ C_i`. -/
theorem quotient_apply_of_mem {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I)
    {x : Ω} (hx : x ∈ P.cell i) :
    P.quotient i j = ∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ := by
  -- by `P.uniform`, the inner integral is constant on `C_i`, so dividing by
  -- `P.cellMass i` gives that constant.
  have hxi : P.cells x = i := hx
  -- The inner integrand `g y := ∫ z, [cells z = j] W y z` is constant (= its
  -- value at `x`) on the cell `C_i`, by `P.uniform`.
  have hconst : Set.EqOn
      (fun y => ∫ z, (if P.cells z = j then W.kernel y z else 0) ∂μ)
      (fun _ => ∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ)
      (P.cell i) := by
    intro y hy
    have hyi : P.cells y = i := hy
    exact P.uniform i j y x hyi hxi
  unfold GraphonEquitablePartition.quotient
  rw [setIntegral_congr_fun (P.measurableSet_cell i) hconst, setIntegral_const]
  -- `(cellMass i)⁻¹ • (μ.real (cell i) • c) = c` since `μ.real (cell i) = cellMass i > 0`.
  have hcm : μ.real (P.cell i) = P.cellMass i := rfl
  rw [hcm, smul_smul]
  rw [inv_mul_cancel₀ (ne_of_gt (P.cellMass_pos i)), one_smul]

/-! ### Cross-mass, the handshake identity, and the symmetric quotient

The raw `quotient` uses the *asymmetric* per-cell normalisation `(μ_i)⁻¹`, so it
is **not** Hermitian as stated (only when all cell masses coincide).  Following
the finite Tower-2 fix in `Graphplay.Equitable`, we keep the raw `quotient`
(divisor matrix) but introduce:

* `crossMass i j` — the total mass `∫_{C_i} ∫_{C_j} W` from cell `i` to cell `j`;
* `crossMass_conj` — conjugate-symmetry `crossMass i j = star (crossMass j i)`,
  from the Hermitian kernel `W.herm` (this is where the genuine Fubini swap
  enters; see the isolated `sorry` note in `crossMass_conj`);
* `quotient_handshake` — `μ_i · Q i j = star (μ_j · Q j i)`;
* `symmQuotient i j := √μ_i · Q i j / √μ_j` (= `D^{1/2} Q D^{-1/2}`), which **is**
  genuinely Hermitian (`symmQuotient_isHermitian`).

`symmQuotient` is the matrix of `W.op` in the orthonormal `cellIndicator` basis,
hence the spectrum-sharing quotient operator. -/

/-- The total weighted mass flowing from cell `i` into cell `j`,
written as a **double integral over the whole space** with a paired
cell-indicator so that conjugate-symmetry is a clean Fubini swap:
`∫_x ∫_z [cells x = i ∧ cells z = j] · W x z = ∫_{C_i × C_j} W`.

This is the (unnormalised) numerator of `quotient i j`: indeed
`crossMass i j = μ(C_i) · quotient i j` (`crossMass_eq_cellMass_mul_quotient`). -/
noncomputable def crossMass {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) : ℂ :=
  ∫ x, ∫ z, (if P.cells x = i ∧ P.cells z = j then W.kernel x z else 0) ∂μ ∂μ

/-- Cross-mass equals cell mass times the (raw) quotient entry:
`crossMass i j = μ(C_i) · quotient i j`.

Collapse the outer `cells x = i` indicator into a `setIntegral` over `C_i`
(`integral_indicator`), then the inner `∧` into the single `cells z = j`
indicator that defines `quotient`, and finally cancel `μ_i · (μ_i)⁻¹`. -/
theorem crossMass_eq_cellMass_mul_quotient {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) :
    P.crossMass i j = (P.cellMass i : ℂ) • P.quotient i j := by
  unfold GraphonEquitablePartition.crossMass GraphonEquitablePartition.quotient
  -- Inner sum collapses: `[cells x = i ∧ cells z = j] = [cells x = i] · [cells z = j]`.
  have hinner : ∀ x : Ω,
      (∫ z, (if P.cells x = i ∧ P.cells z = j then W.kernel x z else 0) ∂μ)
        = (P.cell i).indicator
            (fun x => ∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ) x := by
    intro x
    by_cases hx : P.cells x = i
    · rw [Set.indicator_of_mem (show x ∈ P.cell i from hx)]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show (if P.cells x = i ∧ P.cells z = j then W.kernel x z else 0)
        = (if P.cells z = j then W.kernel x z else 0)
      by_cases hz : P.cells z = j
      · rw [if_pos ⟨hx, hz⟩, if_pos hz]
      · rw [if_neg (fun h => hz h.2), if_neg hz]
    · rw [Set.indicator_of_notMem (show x ∉ P.cell i from hx)]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall (fun z => ?_))
      show (if P.cells x = i ∧ P.cells z = j then W.kernel x z else 0) = 0
      rw [if_neg (fun h => hx h.1)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner),
    integral_indicator (P.measurableSet_cell i)]
  -- Now `∫_{C_i} g = μ_i • quotient i j`, i.e. `μ_i • ((μ_i)⁻¹ • ∫_{C_i} g)`.
  rw [smul_eq_mul, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (ne_of_gt (P.cellMass_pos i)), Complex.ofReal_one, one_mul]

/-- **Conjugate symmetry of cross-mass.**  Hermiticity of the kernel
(`W.herm : W z x = star (W x z)`) makes the mass from `C_i` to `C_j` the complex
conjugate of the mass from `C_j` to `C_i`:
`crossMass i j = star (crossMass j i)`.

The algebra is: push `star` (= `conj` on ℂ) through both integrals
(`integral_conj`), rewrite the integrand by `W.herm` to flip the kernel
arguments and swap the paired indicator `[cells x = j ∧ cells z = i]` into
`[cells z = i ∧ cells x = j]`, and then **swap the order of integration**
(Fubini, `integral_integral_swap`), relabelling the bound variables.

The Fubini swap is the single honest measure-theory gap: it requires
`Integrable (uncurry …) (μ.prod μ)`, which in turn needs the Hilbert–Schmidt
integrability of the kernel over the product measure.  That fact is *not*
established anywhere in this development (it is the same gap that forces the
`sorry`s in `Graphon.opFun_memLp` / `Graphon.op_isSelfAdjoint`).  We therefore
discharge **only** the swap step with a `sorry`; everything else is genuine. -/
theorem crossMass_conj {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) :
    P.crossMass i j = star (P.crossMass j i) := by
  unfold GraphonEquitablePartition.crossMass
  -- Step 1: push `star` (= `conj`) through both integrals.
  rw [show (star : ℂ → ℂ) = (starRingEnd ℂ) from rfl, ← integral_conj]
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x =>
    (integral_conj (f := fun z =>
      if P.cells x = j ∧ P.cells z = i then W.kernel x z else 0)).symm))]
  -- Step 2: rewrite the conjugated integrand via `W.herm`, turning
  -- `star ([cells x = j ∧ cells z = i] · W x z)` into
  -- `[cells z = i ∧ cells x = j] · W z x` (note the swapped roles of `x, z`).
  have hherm : ∀ x z : Ω,
      (starRingEnd ℂ) (if P.cells x = j ∧ P.cells z = i then W.kernel x z else 0)
        = (if P.cells z = i ∧ P.cells x = j then W.kernel z x else 0) := by
    intro x z
    by_cases h : P.cells x = j ∧ P.cells z = i
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩, starRingEnd_apply, ← W.herm x z]
    · rw [if_neg h, if_neg (fun hc => h ⟨hc.2, hc.1⟩), starRingEnd_apply, star_zero]
  rw [show (∫ x, ∫ z, (starRingEnd ℂ)
        (if P.cells x = j ∧ P.cells z = i then W.kernel x z else 0) ∂μ ∂μ)
        = ∫ x, ∫ z, (if P.cells z = i ∧ P.cells x = j then W.kernel z x else 0) ∂μ ∂μ from
      integral_congr_ae (Filter.Eventually.of_forall (fun x =>
        integral_congr_ae (Filter.Eventually.of_forall (fun z => hherm x z))))]
  -- Step 3: a genuine Fubini swap.  Writing `g x z := [cells z = i ∧ cells x = j]
  -- · W z x`, the LHS is `∫_x ∫_z g x z`; `integral_integral_swap` turns it into
  -- `∫_z ∫_x g x z`, which (after the canonical α-renaming of the bound
  -- variables) is exactly the RHS `∫_x ∫_z [cells x = i ∧ cells z = j] · W x z`.
  --
  -- The integrability of `uncurry g` is genuine: `g` is supported on the
  -- finite-product-measure rectangle `C_j ×ˢ C_i` (since `g x z ≠ 0` forces
  -- `x ∈ C_j ∧ z ∈ C_i`) and is bounded there by `W.essBound`.  We dominate it by
  -- the integrable indicator `essBound · 1_{C_j ×ˢ C_i}`.
  set g : Ω → Ω → ℂ :=
    fun x z => if P.cells z = i ∧ P.cells x = j then W.kernel z x else 0 with hg
  -- The dominating rectangle and its finite product mass.
  have hCj : MeasurableSet (P.cell j) := P.measurableSet_cell j
  have hCi : MeasurableSet (P.cell i) := P.measurableSet_cell i
  have hrect : MeasurableSet (P.cell j ×ˢ P.cell i) := hCj.prod hCi
  have hmass : (μ.prod μ) (P.cell j ×ˢ P.cell i) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (ne_of_lt (P.cell_finite j)) (ne_of_lt (P.cell_finite i))
  -- a.e. strong measurability of `uncurry g` (it is built from the measurable
  -- kernel composed with `swap` and an `if` over a measurable predicate).
  have hgmeas : AEStronglyMeasurable (Function.uncurry g) (μ.prod μ) := by
    have hswap : Measurable (fun p : Ω × Ω => W.kernel p.2 p.1) :=
      W.measurable.comp measurable_swap
    have hpred : MeasurableSet {p : Ω × Ω | P.cells p.2 = i ∧ P.cells p.1 = j} := by
      have h2 : MeasurableSet {p : Ω × Ω | P.cells p.2 = i} :=
        (P.measurableSet_cell i).preimage (measurable_snd) -- cell i = cells ⁻¹' {i}
      have h1 : MeasurableSet {p : Ω × Ω | P.cells p.1 = j} :=
        (P.measurableSet_cell j).preimage (measurable_fst)
      exact h2.inter h1
    refine (Measurable.aestronglyMeasurable ?_)
    refine Measurable.ite hpred hswap measurable_const
  -- `W.essBound ≥ 0`: the cells have positive mass, so `μ ≠ 0` (hence
  -- `μ.prod μ ≠ 0`), and the a.e. bound `‖·‖ ≤ essBound` against a nonzero
  -- measure forces `0 ≤ essBound`.
  have hμne : μ ≠ 0 := by
    intro h
    have hpos : 0 < μ (P.cell i) := P.cell_pos i
    have hzero : μ (P.cell i) = 0 := by
      have := DFunLike.congr_fun h (P.cell i)
      simpa using this
    exact absurd hzero (ne_of_gt hpos)
  haveI hprodne : NeZero (μ.prod μ) := by
    refine ⟨fun h => ?_⟩
    have := Measure.prod_prod (μ := μ) (ν := μ) Set.univ Set.univ
    rw [h] at this; simp only [Measure.coe_zero, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this.symm with h0 | h0 <;>
      exact hμne (by simpa [Measure.measure_univ_eq_zero] using h0)
  have hB0 : 0 ≤ W.essBound := by
    obtain ⟨p, hp⟩ := W.bounded.exists
    exact le_trans (norm_nonneg _) hp
  -- the dominating function: `essBound` on the rectangle, `0` outside.
  have hdom : Integrable
      ((P.cell j ×ˢ P.cell i).indicator (fun _ => (W.essBound : ℝ))) (μ.prod μ) :=
    (integrableOn_const (μ := μ.prod μ) (s := P.cell j ×ˢ P.cell i)
      (C := (W.essBound : ℝ)) hmass).integrable_indicator hrect
  -- The swapped a.e. bound `‖W.kernel p.2 p.1‖ ≤ essBound`, transported from
  -- `W.bounded` through the measure-preserving swap `Prod.swap`
  -- ((μ⊗μ).map swap = μ⊗μ), via `ae_map_iff` (the bound predicate is measurable).
  have hpredmeas : MeasurableSet
      {q : Ω × Ω | ‖Function.uncurry W.kernel q‖ ≤ W.essBound} :=
    measurableSet_le W.measurable.norm measurable_const
  have hbddswap : ∀ᵐ p ∂(μ.prod μ), ‖W.kernel p.2 p.1‖ ≤ W.essBound := by
    have hmap : (μ.prod μ).map (Prod.swap : Ω × Ω → Ω × Ω) = μ.prod μ :=
      Measure.measurePreserving_swap.map_eq
    have hae : ∀ᵐ q ∂((μ.prod μ).map (Prod.swap : Ω × Ω → Ω × Ω)),
        ‖Function.uncurry W.kernel q‖ ≤ W.essBound := by rw [hmap]; exact W.bounded
    have := (ae_map_iff (measurable_swap.aemeasurable) hpredmeas).1 hae
    filter_upwards [this] with p hp using hp
  -- domination: `‖g x z‖ ≤ 1_{C_j ×ˢ C_i} · essBound` a.e.
  have hint : Integrable (Function.uncurry g) (μ.prod μ) := by
    refine hdom.mono' hgmeas ?_
    filter_upwards [hbddswap] with p hp
    show ‖Function.uncurry g p‖ ≤
      (P.cell j ×ˢ P.cell i).indicator (fun _ => (W.essBound : ℝ)) p
    by_cases hp' : P.cells p.2 = i ∧ P.cells p.1 = j
    · -- on the support: `p ∈ C_j ×ˢ C_i`, and `‖W.kernel p.2 p.1‖ ≤ essBound`.
      have hmem : p ∈ P.cell j ×ˢ P.cell i := by
        refine Set.mk_mem_prod ?_ ?_
        · show P.cells p.1 = j; exact hp'.2
        · show P.cells p.2 = i; exact hp'.1
      rw [Set.indicator_of_mem hmem]
      show ‖Function.uncurry g p‖ ≤ (W.essBound : ℝ)
      have hval : Function.uncurry g p = W.kernel p.2 p.1 := by
        simp only [Function.uncurry, hg, if_pos hp']
      rw [hval]; exact hp
    · -- off the support: `g p = 0`, dominating function `≥ 0`.
      have hz : Function.uncurry g p = 0 := by simp only [Function.uncurry, hg, if_neg hp']
      rw [hz, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hB0) p
  -- Perform the swap.  `∫_x ∫_z g x z = ∫_z ∫_x g x z` (renamed bound vars = RHS).
  rw [integral_integral_swap hint]

/-- **Graphon handshake identity.**  `μ(C_i) · Q i j = star (μ(C_j) · Q j i)`.
The graphon analogue of the finite degree-balance `|C_i|·b_{ij} = |C_j|·b_{ji}`;
it is exactly `crossMass_conj` rewritten through
`crossMass = cellMass • quotient`.  Note `μ(C_i)` is real, so the `star` only
acts on the quotient entry on the right. -/
theorem quotient_handshake {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) :
    (P.cellMass i : ℂ) * P.quotient i j = star ((P.cellMass j : ℂ) * P.quotient j i) := by
  have h := P.crossMass_conj i j
  rw [crossMass_eq_cellMass_mul_quotient, crossMass_eq_cellMass_mul_quotient] at h
  simpa only [smul_eq_mul] using h

/-- The **symmetric quotient** `Q̃ i j = √μ(C_i) · Q i j / √μ(C_j)`
(i.e. `D^{1/2} Q D^{-1/2}` with `D = diag μ(C_i)`).  This is the matrix of
`W.op` in the orthonormal `cellIndicator` basis, and — unlike the raw
asymmetrically-normalised `quotient` — it is genuinely Hermitian
(`symmQuotient_isHermitian`). -/
noncomputable def symmQuotient {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) : Matrix I I ℂ :=
  fun i j =>
    (Real.sqrt (P.cellMass i) : ℂ) * P.quotient i j / (Real.sqrt (P.cellMass j) : ℂ)

/-- **The symmetric quotient is Hermitian.**  Unlike the raw `quotient`, `Q̃` is
genuinely Hermitian — this is the handshake identity rescaled by `√μ(C_i)`.
(Cells always have positive mass here — `P.cellMass_pos` — so there are no
empty-cell degeneracies; the `√`-cancellation is unconditional.) -/
theorem symmQuotient_isHermitian {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    P.symmQuotient.IsHermitian := by
  ext i j
  show star (P.symmQuotient j i) = P.symmQuotient i j
  unfold GraphonEquitablePartition.symmQuotient
  -- All cell masses are positive, so every `√μ`-cast is nonzero.
  have hsi : (Real.sqrt (P.cellMass i) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (P.cellMass_pos i))
  have hsj : (Real.sqrt (P.cellMass j) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (P.cellMass_pos j))
  have hsqi : (Real.sqrt (P.cellMass i) : ℂ) * (Real.sqrt (P.cellMass i) : ℂ)
      = (P.cellMass i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (P.cellMass_pos i))]
  have hsqj : (Real.sqrt (P.cellMass j) : ℂ) * (Real.sqrt (P.cellMass j) : ℂ)
      = (P.cellMass j : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt (P.cellMass_pos j))]
  -- The conjugated handshake: `μ(C_j) · star (Q j i) = μ(C_i) · Q i j`.
  have hhand : (P.cellMass j : ℂ) * star (P.quotient j i)
      = (P.cellMass i : ℂ) * P.quotient i j := by
    have h := P.quotient_handshake i j
    rw [star_mul',
      show star (↑(P.cellMass j) : ℂ) = (↑(P.cellMass j) : ℂ) from Complex.conj_ofReal _] at h
    -- h : ↑μ(C_i) * Q i j = star (Q j i) * ↑μ(C_j)
    linear_combination -h
  -- Push `star` through the LHS, collapse the real `√`-casts, clear denominators.
  rw [star_div₀, star_mul',
    show star (↑(Real.sqrt (P.cellMass j)) : ℂ) = (↑(Real.sqrt (P.cellMass j)) : ℂ)
      from Complex.conj_ofReal _,
    show star (↑(Real.sqrt (P.cellMass i)) : ℂ) = (↑(Real.sqrt (P.cellMass i)) : ℂ)
      from Complex.conj_ofReal _,
    div_eq_div_iff hsi hsj]
  -- Goal: `(√μ_j · star (Q j i)) · √μ_j = (√μ_i · Q i j) · √μ_i`; collapse the
  -- `√·√ = μ` products and finish with the handshake.
  linear_combination hhand + star (P.quotient j i) * hsqj - P.quotient i j * hsqi

/-! The quotient adjacency has zero diagonal **on average**: the per-vertex
self-flux is the integral of the loopless kernel `W x z` for `z ∈ C_i`, which
need not vanish in general because the cell `C_i` is not a single point.

We therefore do **not** assert `P.quotient i i = 0`.  It is the
*off-diagonal* part of the quotient that captures cell-to-cell transitions. -/

end GraphonEquitablePartition

namespace Graphon

/-! ### The cell-uniform subspace

The subspace of `L²(μ; ℂ)` of functions that are (μ-a.e.) constant on each
cell `C_i` is naturally isometric to `ℂ^I` with the weighted inner product
`⟨v, w⟩_w := Σ_i μ(C_i) · star (v i) · w i` — equivalently, isometric to
`L²(I, μ_count)` where the counting measure is replaced by the **cell-mass
measure** `i ↦ μ(C_i)`.

We **state** this subspace and the isometry to the finite Hilbert space; the
actual construction touches Mathlib's `Lp` quotient subtleties and we defer
the details to `sorry`. -/

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {W : Graphon Ω μ}

/-- The **normalised cell indicator** `e_i ∈ L²(μ; ℂ)`:
`e_i = (1/√μ(C_i)) · 1_{C_i}`.  Constructed by scaling Mathlib's
`indicatorConstLp` on the cell `C_i` (which is measurable via
`P.measurable_cells`) by the unit-normalising scalar
`(√(P.cellMass i))⁻¹ : ℂ`. -/
noncomputable def _root_.Graphplay.GraphonEquitablePartition.cellIndicator
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) :
    Lp ℂ 2 μ :=
  -- measurability of the cell: `P.cells` is measurable w.r.t. the discrete
  -- σ-algebra on `I`, so the singleton-preimage `P.cell i` is measurable.
  -- Finiteness comes from `P.cell_finite`.  We then multiply the
  -- indicator-Lp element by `(√(P.cellMass i))⁻¹` to obtain a unit vector.
  ((Real.sqrt (P.cellMass i))⁻¹ : ℂ) •
    MeasureTheory.indicatorConstLp 2
      (P.measurableSet_cell i)
      (ne_of_lt (P.cell_finite i)) (1 : ℂ)

/-- The **cell-uniform subspace** of `L²(μ; ℂ)` for an equitable partition
`P`: the `ℂ`-linear span of the normalised cell indicators `{e_i}_{i ∈ I}`
in `L²(μ; ℂ)`.  (For a finite index type `I` the span is automatically closed,
since finite-dimensional subspaces of normed spaces are closed.) -/
noncomputable def _root_.Graphplay.GraphonEquitablePartition.cellUniformSubspace
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    Submodule ℂ (Lp ℂ 2 μ) :=
  Submodule.span ℂ (Set.range P.cellIndicator)

/-- The cell-uniform subspace is closed in `L²(μ; ℂ)`. -/
theorem cellUniformSubspace_isClosed {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    IsClosed (P.cellUniformSubspace : Set (Lp ℂ 2 μ)) := by
  -- The span of the (finite) range of `cellIndicator` is finite-dimensional,
  -- hence closed over the complete field `ℂ`.
  have hfin : (Set.range P.cellIndicator).Finite := Set.finite_range _
  haveI : FiniteDimensional ℂ (P.cellUniformSubspace) :=
    FiniteDimensional.span_of_finite ℂ hfin
  exact Submodule.closed_of_finiteDimensional _

/-- The cells `C_i`, `C_j` are disjoint when `i ≠ j` (they are fibres of the
cell map). -/
theorem cell_inter_eq_empty {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) {i j : I} (hij : i ≠ j) :
    P.cell i ∩ P.cell j = ∅ := by
  unfold GraphonEquitablePartition.cell
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hxi hxj
  exact hij (hxi ▸ hxj ▸ rfl)

/-- The cell indicators are orthonormal: `⟨e_i, e_j⟩ = [i = j]`. -/
theorem cellIndicator_orthonormal {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    Orthonormal ℂ (fun i : I => P.cellIndicator i) := by
  rw [orthonormal_iff_ite]
  intro i j
  -- Unfold the cell indicators and pull the scalars out of the inner product.
  simp only [GraphonEquitablePartition.cellIndicator, inner_smul_left, inner_smul_right,
    MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp]
  -- `⟪(1:ℂ),(1:ℂ)⟫ = 1`; the inner product reduces to `μ.real (C_i ∩ C_j)`.
  rw [RCLike.inner_apply]
  simp only [map_one, mul_one]
  split_ifs with hij
  · -- diagonal case: `i = j`, so `C_i ∩ C_j = C_i` and `μ.real (C_i) = cellMass i`.
    subst hij
    rw [Set.inter_self]
    -- `star (√μᵢ)⁻¹ * ((√μᵢ)⁻¹ * μ.real (C_i)) = 1`.
    have hcm : μ.real (P.cell i) = P.cellMass i := rfl
    rw [hcm]
    have hpos : (0 : ℝ) < P.cellMass i := P.cellMass_pos i
    have hsq : Real.sqrt (P.cellMass i) ^ 2 = P.cellMass i :=
      Real.sq_sqrt (le_of_lt hpos)
    have hsqpos : (0 : ℝ) < Real.sqrt (P.cellMass i) := Real.sqrt_pos.mpr hpos
    -- Goal: `(↑√μᵢ)⁻¹ * ((starRingEnd ℂ) (↑√μᵢ)⁻¹ * (μᵢ • 1)) = 1`.
    rw [map_inv₀, Complex.conj_ofReal, Complex.real_smul, mul_one]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    norm_cast
    field_simp
    nlinarith [hsq, hsqpos]
  · -- off-diagonal: `i ≠ j`, so `C_i ∩ C_j = ∅` and `μ.real (∅) = 0`.
    rw [Graphon.cell_inter_eq_empty P hij, measureReal_empty]
    simp

/-- The **cell-uniform isometry**: the unitary map
`L²(I, counting; ℂ) → L²(μ; ℂ)` sending the `i`-th basis vector to the
normalised cell indicator `e_i`.  Concretely
`v ↦ ∑ i, v i • P.cellIndicator i`.

The norm-preservation property `‖∑ v i • e_i‖² = ∑ |v i|²` is exactly
orthonormality of `{e_i}` (`cellIndicator_orthonormal`), and is now proved. -/
noncomputable def _root_.Graphplay.GraphonEquitablePartition.cellUniformIsometry
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] (Lp ℂ 2 μ) where
  toFun := fun v => ∑ i : I, v i • P.cellIndicator i
  map_add' := by
    intro v w
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' := by
    intro c v
    simp [Finset.smul_sum, smul_smul]
  norm_map' := by
    -- Norm preservation: `‖∑ v i • e_i‖² = ∑ ‖v i‖² = ‖v‖²`, since `{e_i}` is
    -- orthonormal (`cellIndicator_orthonormal`).
    intro v
    have hv := Graphon.cellIndicator_orthonormal P
    show ‖∑ i : I, v i • P.cellIndicator i‖ = ‖v‖
    -- It suffices to compare the squared norms (both sides nonneg).
    rw [← Real.sqrt_sq (norm_nonneg (∑ i : I, v i • P.cellIndicator i)),
        ← Real.sqrt_sq (norm_nonneg v)]
    congr 1
    -- Reduce both squared norms to `re` of self inner products.
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    congr 1
    -- LHS inner product: expand over the orthonormal family.
    rw [sum_inner]
    simp only [inner_smul_left, hv.inner_right_fintype]
    -- RHS inner product on EuclideanSpace ℂ I is `∑ i, conj (v i) * v i`.
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [RCLike.inner_apply']

/-- The image of the cell-uniform isometry is exactly the cell-uniform
subspace. -/
theorem range_cellUniformIsometry {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I] {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    (LinearMap.range (P.cellUniformIsometry.toLinearMap)) =
      P.cellUniformSubspace := by
  unfold GraphonEquitablePartition.cellUniformSubspace
  apply le_antisymm
  · -- Range ⊆ span: each image `∑ v i • e_i` is a span element.
    rintro _ ⟨v, rfl⟩
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · -- span ⊆ range: each `e_i` is the image of the standard basis vector.
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    refine ⟨EuclideanSpace.single i (1 : ℂ), ?_⟩
    -- `∑ j, (single i 1) j • e_j = e_i`.
    show ∑ j : I, (EuclideanSpace.single i (1 : ℂ)) j • P.cellIndicator j
        = P.cellIndicator i
    rw [Finset.sum_eq_single i]
    · rw [EuclideanSpace.single_apply]; simp
    · intro j _ hji
      rw [EuclideanSpace.single_apply, if_neg hji, zero_smul]
    · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ### **THE HEADLINE LIFTING THEOREM**

The cell-uniform subspace is **invariant** under the graphon operator `W.op`,
and the restriction of `W.op` to that subspace, **transported across the
cell-uniform isometry**, equals the finite matrix `P.quotient` acting on
`EuclideanSpace ℂ I`.

Statement form, in pseudo-LaTeX:
$$
  \Big(\;W.\mathrm{op}\big|_{\mathrm{cellUniform}}\;\Big)
  \;\;\cong\;\;
  P.\mathrm{quotient}\ \text{as an operator on}\ \mathbb{C}^I.
$$
-/

/-! ### Op-level intertwining (the genuine Tower-4 lift content)

We compute `W.op` on a normalised cell indicator `e_i` **explicitly** as a
cell-uniform combination with the symmetric-quotient coefficients
`W.op e_i = ∑_j (symmQuotient j i) • e_j`.  This is the L²/operator analogue of
the finite `EquitablePartition.adj_mulVec_cellUniformVec_eq` /
`restrict_eq_symmQuotient`, and is proved *genuinely* from
`crossMass_eq_cellMass_mul_quotient` + `quotient_apply_of_mem` +
`kernelIntegralCLM_apply` — it does **not** use the sorried `Graphon.evolve`
group laws. -/

/-- The coeFn of the normalised cell indicator: `e_i =ᵐ (√μ_i)⁻¹ · 1_{C_i}`. -/
theorem _root_.Graphplay.GraphonEquitablePartition.cellIndicator_coeFn
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) :
    ⇑(P.cellIndicator i)
      =ᵐ[μ] ((Real.sqrt (P.cellMass i))⁻¹ : ℂ) • (P.cell i).indicator (fun _ => (1 : ℂ)) := by
  unfold GraphonEquitablePartition.cellIndicator
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (P.cellMass i))⁻¹ : ℂ)
    (MeasureTheory.indicatorConstLp 2 (P.measurableSet_cell i)
      (ne_of_lt (P.cell_finite i)) (1 : ℂ)),
    MeasureTheory.indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ)
      (hs := P.measurableSet_cell i) (hμs := ne_of_lt (P.cell_finite i)) (c := (1 : ℂ))]
    with x hx hx2
  rw [hx, Pi.smul_apply, hx2, Pi.smul_apply]

/-- The coeFn of `W.op (e_i)` is its pointwise integral action `opFun e_i`. -/
theorem _root_.Graphplay.GraphonEquitablePartition.op_cellIndicator_coeFn [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) :
    ⇑(W.op (P.cellIndicator i)) =ᵐ[μ] W.opFun ((P.cellIndicator i : Ω → ℂ)) := by
  unfold Graphon.op
  rw [Graphplay.ForMathlib.kernelIntegralCLM_apply]
  exact (W.opFun_memLp (P.cellIndicator i)).coeFn_toLp

/-- **The pointwise value of `W.op e_i`.**  For *every* `x`, the integral action
`opFun e_i` at `x` is `(√μ_i)⁻¹ · (per-vertex cell-`i` flux out of `x`)`.  This
holds for all `x` (not merely a.e.) because we only a.e.-rewrite the *integrand*
in `y` — equal-a.e. integrands have equal integrals. -/
theorem _root_.Graphplay.GraphonEquitablePartition.opFun_cellIndicator_apply [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) (x : Ω) :
    W.opFun ((P.cellIndicator i : Ω → ℂ)) x
      = ((Real.sqrt (P.cellMass i))⁻¹ : ℂ)
        * ∫ z, (if P.cells z = i then W.kernel x z else 0) ∂μ := by
  show (∫ y, W.kernel x y * (P.cellIndicator i : Ω → ℂ) y ∂μ) = _
  -- Step 1: a.e.-rewrite the integrand in `y` using the clean indicator coeFn, and
  -- simultaneously pull the constant `(√μ_i)⁻¹` out and collapse the indicator into
  -- a `[cells z = i]` `if`.
  rw [integral_congr_ae (g := fun y => ((Real.sqrt (P.cellMass i))⁻¹ : ℂ)
        * (if P.cells y = i then W.kernel x y else 0))
      (by
        filter_upwards [P.cellIndicator_coeFn i] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul]
        by_cases hyi : P.cells y = i
        · rw [Set.indicator_of_mem (show y ∈ P.cell i from hyi), if_pos hyi, mul_one]; ring
        · rw [Set.indicator_of_notMem (show y ∉ P.cell i from hyi), if_neg hyi,
            mul_zero, mul_zero]),
    integral_const_mul]

/-- **Op-level intertwining (explicit form).**  The graphon operator sends the
normalised cell indicator `e_i` to the cell-uniform combination with the
*symmetric* quotient coefficients:
$$ W.\mathrm{op}(e_i) \;=\; \sum_{j} (P.\mathrm{symmQuotient}\ j\ i)\cdot e_j. $$

This is the genuine Tower-4 lift content — the L² analogue of the finite
`EquitablePartition.adj_mulVec_cellUniformVec_eq`.  The coefficient on cell `j`
is `√μ_j · Q_{ji} / √μ_i = symmQuotient j i`.

Proved by comparing coeFns a.e.: `opFun e_i` is (everywhere) `(√μ_i)⁻¹` times the
cell-`i` flux, which by `quotient_apply_of_mem` is `(√μ_i)⁻¹ · Q_{(cells x) i}`
on each cell, matching the coeFn of the RHS sum. -/
theorem _root_.Graphplay.GraphonEquitablePartition.op_cellIndicator_eq [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) :
    W.op (P.cellIndicator i) = ∑ j : I, (P.symmQuotient j i) • P.cellIndicator j := by
  -- Compare a.e. as functions; both are cell-uniform.
  apply Lp.ext
  -- RHS coeFn: `∑ j, symmQuotient j i • (√μ_j)⁻¹ · 1_{C_j}`.
  have hRHS : ⇑(∑ j : I, (P.symmQuotient j i) • P.cellIndicator j)
      =ᵐ[μ] fun x => ∑ j : I, (P.symmQuotient j i)
        * (((Real.sqrt (P.cellMass j))⁻¹ : ℂ) • (P.cell j).indicator (fun _ => (1 : ℂ)) x) := by
    have hsum : ⇑(∑ j : I, (P.symmQuotient j i) • P.cellIndicator j)
        =ᵐ[μ] fun x => ∑ j : I, ((P.symmQuotient j i) • P.cellIndicator j : Lp ℂ 2 μ) x := by
      classical
      induction (Finset.univ : Finset I) using Finset.induction with
      | empty =>
        simp only [Finset.sum_empty]
        filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx; rw [hx]; rfl
      | @insert a s ha ih =>
        filter_upwards [Lp.coeFn_add (∑ j ∈ s, (P.symmQuotient j i) • P.cellIndicator j)
            ((P.symmQuotient a i) • P.cellIndicator a), ih] with x hx hix
        rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm
          ((P.symmQuotient a i) • P.cellIndicator a), hx, Pi.add_apply, hix, add_comm]
    refine hsum.trans ?_
    have hterm : ∀ j : I, ⇑((P.symmQuotient j i) • P.cellIndicator j)
        =ᵐ[μ] fun x => (P.symmQuotient j i)
          * (((Real.sqrt (P.cellMass j))⁻¹ : ℂ) • (P.cell j).indicator (fun _ => (1 : ℂ)) x) := by
      intro j
      filter_upwards [Lp.coeFn_smul (P.symmQuotient j i) (P.cellIndicator j),
        P.cellIndicator_coeFn j] with x hx hcx
      rw [hx, Pi.smul_apply, hcx]
      simp only [Pi.smul_apply, smul_eq_mul]
    filter_upwards [(MeasureTheory.ae_all_iff.mpr hterm)] with x hx
    exact Finset.sum_congr rfl (fun j _ => by rw [hx j])
  -- LHS coeFn: `opFun e_i`, evaluated explicitly; show it equals the RHS coeFn a.e.
  refine (P.op_cellIndicator_coeFn i).trans (Filter.EventuallyEq.trans ?_ hRHS.symm)
  -- Show: for every x, `opFun e_i x = ∑ j, symmQuotient j i • (√μ_j)⁻¹·1_{C_j} x`.
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [P.opFun_cellIndicator_apply i]
  simp only []
  -- The sum collapses to the single `j = cells x` term.
  set k := P.cells x with hk
  have hxk : x ∈ P.cell k := hk.symm
  rw [Finset.sum_eq_single k]
  · -- the surviving term: `symmQuotient k i · (√μ_k)⁻¹ · 1 = (√μ_i)⁻¹ · Q_{ki}`.
    rw [Set.indicator_of_mem hxk, smul_eq_mul, mul_one,
      ← P.quotient_apply_of_mem k i hxk]
    -- `symmQuotient k i = √μ_k · Q_{ki} / √μ_i`; multiply by `(√μ_k)⁻¹`.
    unfold GraphonEquitablePartition.symmQuotient
    have hsk : (Real.sqrt (P.cellMass k) : ℂ) ≠ 0 := by
      simp only [Ne, Complex.ofReal_eq_zero]
      exact ne_of_gt (Real.sqrt_pos.mpr (P.cellMass_pos k))
    field_simp
  · -- vanishing terms: `j ≠ k = cells x`, so `x ∉ C_j`.
    intro j _ hjk
    rw [Set.indicator_of_notMem (show x ∉ P.cell j from fun hxj => hjk (by
      have hxj' : P.cells x = j := hxj
      rw [← hk] at hxj'; exact hxj'.symm)), smul_zero, mul_zero]
  · intro hk'; exact absurd (Finset.mem_univ k) hk'

/-- **Inner-tested intertwining.**  The matrix element of `W.op` in the
orthonormal `cellIndicator` basis is exactly the symmetric quotient entry:
`⟨e_j, W.op e_i⟩ = symmQuotient j i`.  Immediate from `op_cellIndicator_eq` and
orthonormality (`cellIndicator_orthonormal`). -/
theorem _root_.Graphplay.GraphonEquitablePartition.inner_cellIndicator_op_cellIndicator
    [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) :
    inner ℂ (P.cellIndicator j) (W.op (P.cellIndicator i)) = P.symmQuotient j i := by
  rw [P.op_cellIndicator_eq i,
    (Graphon.cellIndicator_orthonormal P).inner_right_fintype (fun k => P.symmQuotient k i) j]

/-- **Headline lifting theorem (invariance).**  The cell-uniform subspace is
invariant under the graphon operator `W.op`:
$$ W.\mathrm{op}\big( \mathrm{cellUniformSubspace} \big) \subseteq
   \mathrm{cellUniformSubspace}. $$

Proved genuinely from `op_cellIndicator_eq`: `W.op e_i` is a finite combination
of the spanning vectors `e_j`, and `W.op` is linear, so the whole subspace is
preserved (`Submodule.span_induction`). -/
theorem cellUniformSubspaceInvariant [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∀ f ∈ P.cellUniformSubspace, W.op f ∈ P.cellUniformSubspace := by
  intro f hf
  unfold GraphonEquitablePartition.cellUniformSubspace at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [P.op_cellIndicator_eq i]
    exact Submodule.sum_mem _ (fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- **Headline lifting theorem (operator identification).**
Transporting the restriction of `W.op` to `cellUniformSubspace` across the
cell-uniform isometry yields the matrix-operator induced by the **symmetric**
quotient `P.symmQuotient` acting on `EuclideanSpace ℂ I`:
$$ \big(W.\mathrm{op}\big|_{\mathrm{cellUniform}}\big)^{\sharp}
    = P.\mathrm{symmQuotient}\ \text{(as a matrix on}\ \mathbb{C}^I\text{)}. $$

Here `(·)^{\sharp}` is the unitary conjugation by `cellUniformIsometry`, and the
right-hand side is `Matrix.toEuclideanLin P.symmQuotient`.

**The spectrum-sharing object is `symmQuotient`, not the raw `quotient`.**  The
`cellUniformIsometry` carries the *orthonormal* basis `{cellIndicator i}`
(`cellIndicator_orthonormal`), so the matrix of `W.op` in that basis is
self-adjoint — and equals `D^{1/2} Q D^{-1/2} = symmQuotient`, not the
asymmetrically-normalised `quotient` (which is not Hermitian; see
`symmQuotient_isHermitian` and the finite analogue
`Graphplay.EquitablePartition.restrict_eq_symmQuotient`).

This is the central theorem of Tower 4.  Its proof reduces to:

1. Compute `W.op (cellIndicator i)` for each `i`.
2. By `P.uniform`, this is `Σ_j (P.quotient j i) · √μ(C_j)/√μ(C_i) · cellIndicator j
   = Σ_j (P.symmQuotient j i) · cellIndicator j`.
3. Reading off coefficients in the orthonormal `cellIndicator` basis gives
   exactly `P.symmQuotient`.

Statement only; proof deferred. -/
theorem op_restrict_eq_quotient [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    ∀ (v : EuclideanSpace ℂ I),
      W.op (P.cellUniformIsometry v) =
        P.cellUniformIsometry (Matrix.toEuclideanLin P.symmQuotient v) := by
  -- Genuine: push `W.op` (linear) through `cellUniformIsometry v = ∑ i v i • e_i`,
  -- expand each `W.op e_i` via `op_cellIndicator_eq`, then recollect the double
  -- sum into the `symmQuotient`-matrix-vector image, matching the RHS isometry.
  intro v
  -- LHS: unfold the isometry and push `W.op` through the finite sum.
  show W.op (∑ i : I, v i • P.cellIndicator i) = _
  rw [map_sum]
  have hLHS : ∀ i : I, W.op (v i • P.cellIndicator i)
      = ∑ j : I, (v i * P.symmQuotient j i) • P.cellIndicator j := by
    intro i
    rw [map_smul, P.op_cellIndicator_eq i, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [smul_smul])
  simp_rw [hLHS]
  rw [Finset.sum_comm]
  -- RHS: `cellUniformIsometry (toEuclideanLin symmQuotient v) = ∑ j, (∑ i, Q̃ j i v i) • e_j`.
  show (∑ j : I, ∑ i : I, (v i * P.symmQuotient j i) • P.cellIndicator j)
      = ∑ j : I, (Matrix.toEuclideanLin P.symmQuotient v) j • P.cellIndicator j
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_smul]
  congr 1
  -- `∑ i, v i * Q̃ j i = (toEuclideanLin Q̃ v) j = (Q̃.mulVec v) j`.
  have hmv : (Matrix.toEuclideanLin P.symmQuotient v) j
      = Matrix.mulVec P.symmQuotient (fun i => v i) j := by
    rw [Matrix.toEuclideanLin_apply]
  rw [hmv, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => by rw [mul_comm])

/-- **Spectral corollary.**  The spectrum of the **symmetric** quotient matrix
`P.symmQuotient` is contained in the spectrum of `W.op`.  Equivalently, every
eigenvalue of the (genuinely Hermitian) symmetric quotient matrix is an
eigenvalue of the (bounded self-adjoint) graphon operator.

This is the graphon-level version of the classical "quotient eigenvalues are
graph eigenvalues" fact.  We use `symmQuotient`, not the raw `quotient`: only
`symmQuotient` is the matrix of `W.op` in the orthonormal `cellIndicator` basis
(see `op_restrict_eq_quotient`), and only it is Hermitian, so only its spectrum
embeds into `spectrum ℂ W.op`. -/
theorem spectrum_quotient_subset_spectrum_op [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    spectrum ℂ (Matrix.toEuclideanLin P.symmQuotient) ⊆ spectrum ℂ W.op := by
  -- Genuine, from the proven `op_restrict_eq_quotient`.  In finite dimensions an
  -- element of `spectrum` of `toEuclideanLin symmQuotient` is an eigenvalue
  -- (`hasEigenvalue_iff_mem_spectrum`); transporting its (nonzero) eigenvector
  -- through the isometry `B = cellUniformIsometry` yields an eigenvector of `W.op`
  -- (via `op_restrict_eq_quotient`), so `λ•1 - W.op` is not injective, hence not a
  -- unit, hence `λ ∈ spectrum ℂ W.op`.
  intro lam hlam
  -- Step 1: extract a nonzero eigenvector `v` of `toEuclideanLin symmQuotient`.
  have hev : Module.End.HasEigenvalue (Matrix.toEuclideanLin P.symmQuotient) lam :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlam
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff] at hv
  obtain ⟨hv_mem, hv_ne⟩ := hv
  -- `hv_mem : Matrix.toEuclideanLin P.symmQuotient v = lam • v`.
  have hv_eig : (Matrix.toEuclideanLin P.symmQuotient) v = lam • v :=
    Module.End.mem_eigenspace_iff.mp hv_mem
  -- Step 2: `W.op (B v) = lam • (B v)`, with `B v ≠ 0` (B injective isometry).
  set Bv := P.cellUniformIsometry v with hBv
  have hBv_ne : Bv ≠ 0 := by
    rw [hBv]
    intro h0
    exact hv_ne (P.cellUniformIsometry.injective (by rw [h0, map_zero]))
  have hop_eig : W.op Bv = lam • Bv := by
    rw [hBv, Graphon.op_restrict_eq_quotient P v, hv_eig, map_smul]
  -- Step 3: `lam ∈ spectrum ℂ W.op`, since `lam•1 - W.op` kills `Bv ≠ 0`.
  rw [spectrum.mem_iff]
  intro hunit
  -- `(algebraMap ℂ _ lam - W.op) Bv = lam • Bv - W.op Bv = 0`.
  have hker : (algebraMap ℂ ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) lam - W.op) Bv = 0 := by
    rw [ContinuousLinearMap.sub_apply, hop_eig, Algebra.algebraMap_eq_smul_one]
    show (lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) Bv - lam • Bv = 0
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, sub_self]
  -- A unit CLM is injective, so its kernel is trivial — contradiction with `Bv ≠ 0`.
  obtain ⟨u, hu⟩ := hunit
  have hinj : Function.Injective (algebraMap ℂ ((Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) lam - W.op) := by
    rw [← hu]
    intro a b hab
    have : (↑u⁻¹ * ↑u : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) a
        = (↑u⁻¹ * ↑u : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) b := by
      simp only [ContinuousLinearMap.mul_apply]
      rw [show (u : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) a = (u : (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ)) b
        from hab]
    rwa [u.inv_mul, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply] at this
  exact hBv_ne (hinj (by rw [hker, map_zero]))

/-- **Generic `exp`-propagation of an operator intertwining.**  If a bounded
operator `T` on `F` is intertwined with a bounded operator `S` on `G` by a
bounded linear map `B : F →L G` (i.e. `S ∘ B = B ∘ T`, tested pointwise), then
the same intertwining holds after exponentiation:
`exp S (B v) = B (exp T v)`.

Proof: `S^n (B v) = B (T^n v)` by induction, and `exp` is the (norm-)convergent
power series `∑ (n!)⁻¹ • (·)^n`; push the continuous linear `B` through the sum
via `HasSum.mapL`, using uniqueness of sums. -/
theorem exp_intertwine {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (B : F →L[ℂ] G) (S : G →L[ℂ] G) (T : F →L[ℂ] F)
    (h : ∀ w : F, S (B w) = B (T w)) (v : F) :
    (NormedSpace.exp S) (B v) = B ((NormedSpace.exp T) v) := by
  -- Provide the `ℚ`-algebra structures needed by `NormedSpace.exp`'s series API.
  let _ : NormedAlgebra ℚ (G →L[ℂ] G) := .restrictScalars ℚ ℂ _
  let _ : NormedAlgebra ℚ (F →L[ℂ] F) := .restrictScalars ℚ ℂ _
  -- `S^n (B v) = B (T^n v)` for all `n`.
  have hpow : ∀ n : ℕ, ∀ w : F, (S ^ n) (B w) = B ((T ^ n) w) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ k ih =>
      intro w
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
        ih w, h ((T ^ k) w)]
  -- `exp S` is the sum of `(n!)⁻¹ • S^n`; evaluate both `exp`-series at `B v` / `v`
  -- through the continuous evaluation maps, then push `B` through the `F`-side sum.
  have hSsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) S
  have hTsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T
  -- Evaluate the operator-valued sums at the respective vectors.
  have hSeval : HasSum (fun n => ((n ! : ℂ)⁻¹ • (S ^ n)) (B v)) ((NormedSpace.exp S) (B v)) :=
    (ContinuousLinearMap.apply ℂ G (B v)).hasSum hSsum
  have hTeval : HasSum (fun n => B (((n ! : ℂ)⁻¹ • (T ^ n)) v)) (B ((NormedSpace.exp T) v)) :=
    B.hasSum ((ContinuousLinearMap.apply ℂ F v).hasSum hTsum)
  -- The two summand families agree termwise: `((n!)⁻¹ • S^n)(B v) = B ((n!)⁻¹ • T^n v)`.
  refine HasSum.unique hSeval (hSeval.unique ?_ ▸ hTeval)
  refine HasSum.congr hTeval (fun n => ?_)
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hpow n v, map_smul]

/-- **Evolution corollary.**  The graphon CTQW restricted to the cell-uniform
subspace is unitarily equivalent to the finite CTQW driven by `P.symmQuotient`
(the spectrum-sharing symmetric quotient — *not* the raw `quotient`).

Concretely:
$$ W.\mathrm{evolve}(t)\big|_{\mathrm{cellUniform}}
    \;=\; \exp\!\big(-i\,t \,\cdot\, P.\mathrm{symmQuotient}\big)
    \text{ as an operator on}\ \mathbb{C}^I, $$
under `cellUniformIsometry`.

Proved genuinely by `exp`-propagation (`exp_intertwine`) of the **proven**
op-level intertwining `op_restrict_eq_quotient`, no longer depending on the
`NormedSpace.exp`-on-CLM group laws being open. -/
theorem evolve_restrict_eq_finite_evolve [IsFiniteMeasure μ]
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (t : ℝ)
    (v : EuclideanSpace ℂ I) :
    W.evolve t (P.cellUniformIsometry v) =
      P.cellUniformIsometry
        (Matrix.toEuclideanLin
          (NormedSpace.exp (-(Complex.I * (t : ℂ)) • P.symmQuotient)) v) := by
  -- `B := cellUniformIsometry` (as a CLM); `S := (-iτ)•W.op`; `T := (-iτ)•(matrix op)`.
  set B : EuclideanSpace ℂ I →L[ℂ] (Lp ℂ 2 μ) := P.cellUniformIsometry.toContinuousLinearMap
    with hB
  set T : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
    Matrix.toEuclideanCLM (𝕜 := ℂ) ((-(Complex.I * (t : ℂ))) • P.symmQuotient) with hT
  -- Op-level intertwining: `((-iτ)•W.op) ∘ B = B ∘ T`, pointwise.
  have hinter : ∀ w : EuclideanSpace ℂ I,
      (((-(Complex.I * (t : ℂ))) • W.op)) (B w) = B (T w) := by
    intro w
    show (((-(Complex.I * (t : ℂ))) • W.op)) (P.cellUniformIsometry w)
      = P.cellUniformIsometry (T w)
    rw [ContinuousLinearMap.smul_apply, Graphon.op_restrict_eq_quotient P w]
    -- `(-iτ) • B (toEuclideanLin Q̃ w) = B (toEuclideanCLM ((-iτ)•Q̃) w)`.
    rw [← map_smul]
    congr 1
    show (-(Complex.I * (t : ℂ))) • (Matrix.toEuclideanLin P.symmQuotient) w = T w
    rw [hT, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ← map_smul, ← LinearMap.map_smul]
    congr 1
    rw [Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply]
    simp only [Matrix.smul_mulVec_assoc]
  -- Now propagate through `exp` and identify `exp T` with `toEuclideanCLM (exp matrix)`.
  have key := exp_intertwine B (((-(Complex.I * (t : ℂ))) • W.op)) T hinter v
  rw [Graphon.evolve, hB, LinearIsometry.coe_toContinuousLinearMap] at key ⊢
  rw [show ((-Complex.I) * (t : ℂ)) • W.op = (-(Complex.I * (t : ℂ))) • W.op by
        rw [neg_mul, neg_smul, neg_smul, neg_mul], key]
  congr 1
  -- `exp T v = exp (toEuclideanCLM ((-iτ)•Q̃)) v = toEuclideanCLM (exp ((-iτ)•Q̃)) v`,
  -- and `toEuclideanCLM = toEuclideanLin` on a vector.
  rw [hT]
  rw [show (NormedSpace.exp (Matrix.toEuclideanCLM (𝕜 := ℂ)
          ((-(Complex.I * (t : ℂ))) • P.symmQuotient)))
        = Matrix.toEuclideanCLM (𝕜 := ℂ)
          (NormedSpace.exp ((-(Complex.I * (t : ℂ))) • P.symmQuotient)) from ?_]
  · rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    congr 2
    rw [neg_smul, neg_smul, neg_mul, neg_neg, ← neg_smul]
    congr 1
    rw [neg_mul]
  · -- `toEuclideanCLM` is a continuous star-algebra equiv, so it commutes with `exp`.
    let _ : NormedAlgebra ℚ (EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :=
      .restrictScalars ℚ ℂ _
    exact (map_exp (Matrix.toEuclideanCLM (𝕜 := ℂ)).toAlgEquiv.toRingEquiv
      (Matrix.toEuclideanCLM (𝕜 := ℂ)).toContinuousAlgEquiv.continuous _).symm

end Graphon

end Graphplay
