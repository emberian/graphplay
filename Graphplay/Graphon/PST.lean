/-
# Graphon/PST.lean — Perfect state transfer on graphons

The classical theory of **perfect state transfer** (PST) for continuous-time
quantum walks on finite graphs (Christandl–Datta–Ekert–Landahl 2004,
Bachman–Tamon arXiv:1108.0339, Godsil's survey arXiv:1102.0184) admits a
direct graphon-level lift, via the headline lifting theorem of
`Graphon/Equitable.lean`.

In this file we:

* define `Graphon.IsCellUniformPST W P i j τ` — *cell-uniform PST* from cell
  `i` to cell `j` at time `τ`, in terms of the normalised cell-indicator
  matrix element `|⟨e_j, evolve τ · e_i⟩| = 1`;
* state the **graphon-PST headline theorem**: cell-uniform PST on `(W, P)`
  is equivalent to finite-graph PST on the quotient matrix `P.quotient`;
* state the analogous theorems for **uniform mixing** and **spatial search**.

The headline theorem (now genuinely proved) is
`Graphon.cellUniformPST_iff_quotientPST`.

References:

* Bachman–Tamon, *Perfect state transfer on signed graphs*, arXiv:1108.0339 —
  the finite predecessor.
* Coutinho–Godsil, *Perfect state transfer on graphs*, Annals of Combinatorics
  (2016) — survey of finite PST.
* Gerlach–von der Gönna, arXiv:2110.13686 — closest structural ancestor in
  the continuous-dynamics setting.
* Xie–Tamon, arXiv:2301.07251 — "no infinite tail beats optimality" (a
  Tower-4 corollary, see `Graphon/Limit.lean`).
-/

import Graphplay.Graphon.Equitable
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped MeasureTheory ENNReal Complex
open MeasureTheory

universe u v

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {W : Graphon Ω μ}

/-! ## Finite PST recap

We restate the finite PST predicate on a Hermitian matrix `H : Matrix I I ℂ`,
acting on `EuclideanSpace ℂ I`, for self-containedness. -/

/-- **Finite PST**: for a Hermitian matrix `H` on `I` and a time `τ : ℝ`,
there is PST between standard-basis vectors `e_i, e_j` if
`|⟨e_j, exp(-i τ H) e_i⟩| = 1`.

(The phase factor is allowed to be arbitrary; PST is "unit fidelity".)
This is the classical CTQW perfect-state-transfer condition. -/
def IsPST_finite (H : Matrix I I ℂ) (i j : I) (τ : ℝ) : Prop :=
  -- Born-rule modulus of the amplitude `((exp (-i τ H)) e_i) j`, i.e. the
  -- `(j, i)` entry of the matrix exponential `exp(-(I·τ)·H)`.  This matches the
  -- Tower-2 finite predicate `Graphplay.IsPST` (`‖G.evolve τ u v‖ = 1`) with
  -- `G.evolve τ = NormedSpace.exp (-(I·τ) • G.adj)`.
  ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H)) j i‖ = 1

/-! ## Cell-uniform PST on a graphon

The notion of PST on a graphon, *between cells*, is defined via the normalised
cell-indicator basis `e_i = 1_{C_i}/√μ(C_i)` of the cell-uniform subspace. -/

/-- **Cell-uniform graphon PST.**  We say `W` exhibits perfect state transfer
between cell `i` and cell `j` at time `τ` (with respect to the equitable
partition `P`) iff
$$ \big| \langle e_j,\; W.\mathrm{evolve}(\tau)\; e_i \rangle \big| = 1, $$
where `e_i = (1/√μ(C_i)) · 1_{C_i}` is the normalised indicator of cell `i`.

This is the graphon analogue of finite PST: a CTQW initialised in the
**uniform superposition** over cell `i` evolves to (a phase times) the
uniform superposition over cell `j` exactly at time `τ`.

Reference for the finite predecessor: Bachman–Tamon, arXiv:1108.0339. -/
def IsCellUniformPST (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i j : I) (τ : ℝ) : Prop :=
  ‖inner ℂ (P.cellIndicator j) (W.evolve τ (P.cellIndicator i))‖
    = 1

/-! ## The evolve-level intertwining (now genuinely closed)

The op-level lift `Graphon.op_restrict_eq_quotient` is **genuinely closed**, and so
is its *exponential* upgrade: that `W.evolve τ` (`= NormedSpace.exp ((-iτ)·W.op)`)
restricted to the cell-uniform subspace is the finite CTQW driven by
`exp((-iτ)·symmQuotient)`.  Abstractly this is "intertwining propagates through
`exp`": from `W.op ∘ B = B ∘ (toEuclideanLin symmQuotient)`
(`op_restrict_eq_quotient`, with `B = cellUniformIsometry`) one gets
`exp(W.op) ∘ B = B ∘ exp(toEuclideanLin symmQuotient)`.

This is now discharged by `Graphon.exp_intertwine` (the generic `exp`-propagation
of an operator intertwining through a bounded `B`, proved via the `exp` power
series and `HasSum.mapL`), using the now-closed `NormedSpace.exp`-on-CLM group
laws in `Graphplay/Graphon.lean` (`evolve_zero`, `evolve_add`, `evolve_isUnitary`).
Everything downstream is genuine. -/

/-- **Exponential upgrade of `op_restrict_eq_quotient`** (genuinely closed):
`W.evolve τ` restricted to the cell-uniform subspace is unitarily equivalent
(via `cellUniformIsometry`) to the finite CTQW `exp((-iτ)·symmQuotient)`.

This is `exp`-propagation of the **proven** op-level intertwining
`Graphon.op_restrict_eq_quotient` (`W.op ∘ B = B ∘ toEuclideanLin symmQuotient`),
established by `Graphon.evolve_restrict_eq_finite_evolve` / `Graphon.exp_intertwine`.
All PST/mixing/search headlines below are derived from it without gaps. -/
theorem _root_.Graphplay.GraphonEquitablePartition.evolve_cellUniformIsometry_eq
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (τ : ℝ) (v : EuclideanSpace ℂ I) :
    W.evolve τ (P.cellUniformIsometry v) =
      P.cellUniformIsometry
        ((Matrix.toEuclideanCLM (𝕜 := ℂ)
          (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient))) v) := by
  -- This is exactly `evolve_restrict_eq_finite_evolve` (proven genuinely by
  -- `exp`-propagation of `op_restrict_eq_quotient`), modulo the defeq coercion
  -- `toEuclideanCLM A v = toEuclideanLin A v`.
  rw [Graphon.evolve_restrict_eq_finite_evolve P τ v]
  -- `toEuclideanLin A v = toEuclideanCLM A v` (the CLM coerces to the linear map).
  congr 1

/-- **Matrix-element identity (genuine, modulo the named gap).**  The cell-uniform
matrix element of `W.evolve τ` is exactly the `(j,i)` entry of the finite matrix
exponential `exp(-(iτ)·symmQuotient)`:
$$ \langle e_j,\; W.\mathrm{evolve}(\tau)\, e_i \rangle
   = \big(\exp(-(i\tau)\,\mathrm{symmQuotient})\big)_{j\,i}. $$

This is derived **genuinely** from `evolve_cellUniformIsometry_eq` (the single
named gap): `e_i = B (E_i)`, orthonormality of `{e_j}` reads off the `j`-th
coefficient of `B⁻¹`-side, and `toEuclideanCLM` (a star-algebra equiv) sends the
matrix exponential to the operator exponential entrywise. -/
theorem _root_.Graphplay.GraphonEquitablePartition.evolve_cellIndicator_matrixElement
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) (τ : ℝ) :
    inner ℂ (P.cellIndicator j) (W.evolve τ (P.cellIndicator i))
      = (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)) j i := by
  -- `e_i = cellUniformIsometry (E_i)` with `E_i = EuclideanSpace.single i 1`.
  have hei : P.cellIndicator i = P.cellUniformIsometry (EuclideanSpace.single i (1 : ℂ)) := by
    show P.cellIndicator i = ∑ k : I, (EuclideanSpace.single i (1 : ℂ)) k • P.cellIndicator k
    rw [Finset.sum_eq_single i]
    · rw [EuclideanSpace.single_apply, if_pos rfl, one_smul]
    · intro k _ hki; rw [EuclideanSpace.single_apply, if_neg hki, zero_smul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hei, P.evolve_cellUniformIsometry_eq τ (EuclideanSpace.single i (1 : ℂ))]
  -- `⟨e_j, B w⟩ = w j` by orthonormality (`B w = ∑ k w k • e_k`).
  show inner ℂ (P.cellIndicator j)
      (∑ k : I, ((Matrix.toEuclideanCLM (𝕜 := ℂ)
        (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)))
          (EuclideanSpace.single i (1 : ℂ))) k • P.cellIndicator k) = _
  rw [(Graphon.cellIndicator_orthonormal P).inner_right_fintype]
  -- `(toEuclideanCLM (exp H) E_i) j = (exp H *ᵥ E_i) j = (exp H) j i`.
  show ((Matrix.toEuclideanCLM (𝕜 := ℂ)
      (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)))
        (EuclideanSpace.single i (1 : ℂ))) j = _
  rw [show (EuclideanSpace.single i (1 : ℂ)) = (WithLp.toLp 2 (Pi.single i (1 : ℂ))) from rfl,
    Matrix.toEuclideanCLM_toLp]
  show ((NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)).mulVec
      (Pi.single i (1 : ℂ))) j = _
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]

/-! ## **The headline PST theorem** -/

/-- **Graphon PST ↔ finite PST on the symmetric quotient.**  Under an equitable
partition `P`, cell-uniform graphon PST from cell `i` to cell `j` at time `τ` is
equivalent to (ordinary, finite) PST from basis vector `e_i` to `e_j` at time
`τ` on the **symmetric** quotient matrix `P.symmQuotient`.

This is the **headline graphon-PST theorem**, the Tower-4 analogue of the proven
Tower-2 lift `Graphplay.EquitablePartition.cellUniformPST_iff_quotientPST`.  Note
the spectrum-sharing object is `P.symmQuotient = D^{1/2} Q D^{-1/2}` (genuinely
Hermitian, `symmQuotient_isHermitian`), **not** the raw asymmetric `P.quotient`:
`cellUniformIsometry` carries the *orthonormal* `cellIndicator` basis, so the
matrix of `W.op`/`W.evolve` in that basis is `symmQuotient` (see
`Graphon.op_restrict_eq_quotient`), matching Tower-2's `restrict_eq_symmQuotient`.

It is an immediate consequence of `Graphon.evolve_restrict_eq_finite_evolve` (the
cell-uniform subspace is invariant under `W.evolve`, and the restricted operator
is unitarily equivalent to `exp(-i τ · P.symmQuotient)`) — once that headline
lifting corollary is available, this is *almost* free: read off the modulus of
the `(j,i)` matrix element on each side.

**Genuinely closed.**  The supporting restriction lift
`Graphon.evolve_restrict_eq_finite_evolve` and the operator-level lift
`Graphon.op_restrict_eq_quotient` are both proved, so this iff is discharged by
reading off the modulus of the `(j,i)` matrix element on each side (via
`evolve_cellIndicator_matrixElement`); routed to the spectrum-sharing
`symmQuotient`. -/
theorem cellUniformPST_iff_quotientPST (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i j : I) (τ : ℝ) :
    IsCellUniformPST W P i j τ ↔ IsPST_finite P.symmQuotient i j τ := by
  -- Genuine, given the single named gap `evolve_cellUniformIsometry_eq`: by
  -- `evolve_cellIndicator_matrixElement`, the cell-uniform matrix element
  -- `⟨e_j, W.evolve τ e_i⟩` equals the `(j,i)` entry of `exp(-(iτ)·symmQuotient)`,
  -- so the two `‖·‖ = 1` conditions are literally the same.
  unfold IsCellUniformPST IsPST_finite
  rw [P.evolve_cellIndicator_matrixElement i j τ]

/-! ## Mixing

Uniform mixing is the average-over-time version of PST; it admits the same
quotient lift. -/

/-- **Cell-uniform graphon mixing.**  At time `τ`, the graphon CTQW exhibits
*uniform mixing* over the cells starting from cell `i` iff the probability of
being in **any** cell `j` is `1/|I|`:
$$ \big| \langle e_j,\; W.\mathrm{evolve}(\tau)\; e_i \rangle \big|^2
    = \frac{1}{|I|}\quad\text{for every } j. $$

This is the graphon analogue of finite uniform mixing (Godsil, *State transfer
on graphs*, Discrete Math. 2012). -/
def IsCellUniformGraphonMixing
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i : I) (τ : ℝ) : Prop :=
  ∀ j : I,
    ‖inner ℂ (P.cellIndicator j) (W.evolve τ (P.cellIndicator i))‖ ^ 2
      = (1 : ℝ) / Fintype.card I

/-- **Finite uniform mixing** on the quotient matrix `H`, for reference. -/
def IsUniformMixing_finite (H : Matrix I I ℂ) (i : I) (τ : ℝ) : Prop :=
  -- `∀ j, ‖((exp (-i τ H)) e_i) j‖² = 1/|I|`: Born-rule modulus-squared of each
  -- amplitude, i.e. the `(j, i)` entry of the matrix exponential, is uniform.
  ∀ j : I,
    ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H)) j i‖ ^ 2
      = (1 : ℝ) / Fintype.card I

/-- **Graphon mixing ↔ finite mixing on the symmetric quotient.**  Cell-uniform
mixing on a graphon is equivalent to ordinary uniform mixing on the **symmetric**
quotient matrix `P.symmQuotient` (the spectrum-sharing Hermitian object — *not*
the raw `P.quotient`; see `cellUniformPST_iff_quotientPST` and
`symmQuotient_isHermitian`).  Same proof skeleton as the PST theorem, via the same
`Graphon.evolve_restrict_eq_finite_evolve` lift.

**Genuinely closed** for the same reason as `cellUniformPST_iff_quotientPST`: the
supporting restriction lift is proved, so the per-cell amplitudes coincide
entrywise (`evolve_cellIndicator_matrixElement`); routed to `symmQuotient`. -/
theorem cellUniformGraphonMixing_iff_quotientMixing
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) (τ : ℝ) :
    IsCellUniformGraphonMixing W P i τ
      ↔ IsUniformMixing_finite P.symmQuotient i τ := by
  -- Genuine, given the single named gap `evolve_cellUniformIsometry_eq`: the
  -- per-cell amplitudes coincide entrywise by `evolve_cellIndicator_matrixElement`,
  -- so the two "modulus² = 1/|I|" conditions agree term by term.
  unfold IsCellUniformGraphonMixing IsUniformMixing_finite
  refine forall_congr' (fun j => ?_)
  rw [P.evolve_cellIndicator_matrixElement i j τ]

/-! ## Spatial search

The Childs–Goldstone spatial search Hamiltonian on a graph is
`H = -γ A - |w⟩⟨w|`, and the search succeeds at time `τ` if `|⟨w, e^{-i τ H}|s⟩|`
is close to 1, where `|s⟩` is the uniform superposition.  On a graphon this
generalises by replacing the marked vertex by a marked **cell**, and the
adjacency `A` by `W.op`. -/

/-- **Graphon search Hamiltonian.**  For coupling `γ : ℝ` and marked cell
`w : I`, the search Hamiltonian on `L²(μ; ℂ)` is
$$ H_\gamma = \gamma\, W.\mathrm{op} - \mathbb{1}_{C_w} \otimes \mathbb{1}_{C_w}^*,$$
where the projector is onto the normalised indicator `e_w`. -/
noncomputable def searchHamiltonian (W : Graphon Ω μ)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (γ : ℝ) (w : I) :
    (Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ) :=
  -- `γ • W.op  -  |e_w⟩⟨e_w|`.  The rank-one projector `|e_w⟩⟨e_w|` onto the
  -- normalised cell indicator `e_w = P.cellIndicator w` is built concretely as
  -- the composite `toSpanSingleton ℂ e_w ∘L innerSL ℂ e_w`, i.e. the map
  -- `f ↦ ⟨e_w, f⟩ • e_w`.  Since `‖e_w‖ = 1` (`cellIndicator_orthonormal`), this
  -- is an honest orthogonal projector onto the line `ℂ·e_w`.
  (γ : ℂ) • W.op -
    (ContinuousLinearMap.toSpanSingleton ℂ (P.cellIndicator w)) ∘L
      (innerSL ℂ (P.cellIndicator w))

/-- The rank-one projector `|e_w⟩⟨e_w|` underlying `searchHamiltonian` acts as
`f ↦ ⟨e_w, f⟩ • e_w`.  This unfolds the concrete `toSpanSingleton ∘ innerSL`
construction. -/
@[simp] theorem searchHamiltonian_apply (W : Graphon Ω μ)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (γ : ℝ) (w : I) (f : Lp ℂ 2 μ) :
    searchHamiltonian W P γ w f
      = (γ : ℂ) • W.op f - (inner ℂ (P.cellIndicator w) f) • P.cellIndicator w := by
  rfl

/-- **Cell-uniform spatial search success.**  Starting from the uniform
superposition `|s⟩ = (1/√|I|) Σ_j e_j` over all cells, the graphon spatial
search at coupling `γ`, marked cell `w`, time `τ`, succeeds iff the modulus
of the amplitude at `e_w` is `1`:
$$ \big| \langle e_w,\; \exp(-i \tau H_\gamma)\, |s\rangle \big| = 1. $$ -/
def IsCellUniformSearchSuccess (W : Graphon Ω μ)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (γ : ℝ) (w : I) (τ : ℝ) : Prop :=
  -- Uniform superposition over the cells `|s⟩ = (1/√|I|) Σ_j e_j`, evolved by
  -- the search Hamiltonian `exp(-iτ H_γ)`, has unit overlap with the marked
  -- cell indicator `e_w`.  Concrete now that `searchHamiltonian` is honest.
  ‖inner ℂ (P.cellIndicator w)
      (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • searchHamiltonian W P γ w)
        ((((Fintype.card I : ℝ).sqrt)⁻¹ : ℂ) • ∑ j : I, P.cellIndicator j))‖ = 1

/-- **Finite spatial-search Hamiltonian** on a Hermitian matrix `H`:
`H_γ = γ • H - |E_w⟩⟨E_w|`, the Childs–Goldstone search operator with marked
vertex `w` and coupling `γ`, acting on `EuclideanSpace ℂ I`.  The rank-one
projector `|E_w⟩⟨E_w|` is built from the standard basis vector via
`toSpanSingleton ∘ innerSL`. -/
noncomputable def finiteSearchHamiltonian (H : Matrix I I ℂ) (γ : ℝ) (w : I) :
    EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  (γ : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) H) -
    (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single w (1 : ℂ))) ∘L
      (innerSL ℂ (EuclideanSpace.single w (1 : ℂ)))

/-- **Finite spatial-search success** on a Hermitian matrix `H`: starting from
the uniform superposition `|s⟩ = (1/√|I|) Σ_j E_j`, the search Hamiltonian
`exp(-iτ H_γ)` has unit overlap with the marked basis vector `E_w`. -/
def IsSearchSuccess_finite (H : Matrix I I ℂ) (γ : ℝ) (w : I) (τ : ℝ) : Prop :=
  ‖inner ℂ (EuclideanSpace.single w (1 : ℂ))
      (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • finiteSearchHamiltonian H γ w)
        ((((Fintype.card I : ℝ).sqrt)⁻¹ : ℂ) •
          ∑ j : I, EuclideanSpace.single j (1 : ℂ)))‖ = 1

/-- **Graphon search ↔ finite search on the symmetric quotient.**  Spatial
search on the graphon is equivalent to spatial search on the **symmetric**
quotient matrix `P.symmQuotient` with the same coupling `γ`, marked vertex `w`
(corresponding to the marked cell), and time `τ`.

The skeleton mirrors the PST theorem: the cell-uniform subspace is invariant
under both `W.op` (`cellUniformSubspaceInvariant`) and the rank-one perturbation
`|e_w⟩⟨e_w|` (since `e_w` lies in that subspace), hence under `H_γ`, hence under
`exp(-iτ H_γ)`; on that subspace `cellUniformIsometry` carries `H_γ` to the finite
`finiteSearchHamiltonian P.symmQuotient γ w`, matching the uniform superposition
and the marked indicator entrywise.

Genuine, now that the `NormedSpace.exp`-on-CLM interface (`Graphon.evolve_*`) and
the `exp`-propagation lemma `Graphon.exp_intertwine` are closed: the search
Hamiltonian intertwines with the finite one through `cellUniformIsometry`
(`op_restrict_eq_quotient` for the `γ•W.op` term, and isometry-preservation of the
inner product for the rank-one `|e_w⟩⟨e_w|` term), so `exp_intertwine` carries the
evolution over, and the marked-cell amplitude matches entrywise. -/
theorem cellUniformSearch_iff_quotientSearch
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (γ : ℝ) (w : I) (τ : ℝ) :
    IsCellUniformSearchSuccess W P γ w τ ↔ IsSearchSuccess_finite P.symmQuotient γ w τ := by
  unfold IsCellUniformSearchSuccess IsSearchSuccess_finite
  set B : EuclideanSpace ℂ I →L[ℂ] (Lp ℂ 2 μ) := P.cellUniformIsometry.toContinuousLinearMap
    with hB
  -- `e_k = B (E_k)` for the standard basis vector `E_k`.
  have heB : ∀ k : I, P.cellIndicator k = B (EuclideanSpace.single k (1 : ℂ)) := by
    intro k
    rw [hB, LinearIsometry.coe_toContinuousLinearMap]
    show P.cellIndicator k = ∑ l : I, (EuclideanSpace.single k (1 : ℂ)) l • P.cellIndicator l
    rw [Finset.sum_eq_single k]
    · rw [EuclideanSpace.single_apply, if_pos rfl, one_smul]
    · intro l _ hlk; rw [EuclideanSpace.single_apply, if_neg hlk, zero_smul]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  -- Op-level intertwining of the search Hamiltonians: `H_γ ∘ B = B ∘ H_γ^{fin}`.
  have hHinter : ∀ v : EuclideanSpace ℂ I,
      searchHamiltonian W P γ w (B v) = B (finiteSearchHamiltonian P.symmQuotient γ w v) := by
    intro v
    rw [searchHamiltonian_apply]
    show (γ : ℂ) • W.op (B v) - (inner ℂ (P.cellIndicator w) (B v)) • P.cellIndicator w
      = B (((γ : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) P.symmQuotient)) v
            - (inner ℂ (EuclideanSpace.single w (1 : ℂ)) v) • EuclideanSpace.single w (1 : ℂ))
    rw [map_sub, map_smul]
    congr 1
    · -- adjacency term: `γ • W.op (B v) = B (γ • toEuclideanCLM Q̃ v)`.
      rw [hB, LinearIsometry.coe_toContinuousLinearMap,
        Graphon.op_restrict_eq_quotient P v, ContinuousLinearMap.smul_apply, map_smul]
      rfl
    · -- rank-one term: `⟨e_w, B v⟩ • e_w = ⟨E_w, v⟩ • B E_w`, with `e_w = B E_w`.
      rw [heB w]
      -- Goal: `⟨B E_w, B v⟩ • B E_w = ⟨E_w, v⟩ • B E_w`; inner products match (isometry).
      congr 1
      rw [hB, LinearIsometry.coe_toContinuousLinearMap, P.cellUniformIsometry.inner_map_map]
  -- Scale by `-(I·τ)` to intertwine the generators, then propagate through `exp`.
  have hSinter : ∀ v : EuclideanSpace ℂ I,
      (-(Complex.I * (τ : ℂ)) • searchHamiltonian W P γ w) (B v)
        = B ((-(Complex.I * (τ : ℂ)) • finiteSearchHamiltonian P.symmQuotient γ w) v) := by
    intro v
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hHinter v, map_smul]
  -- The uniform superposition over cells is `B` of the uniform superposition over `I`.
  have hsuper : (((Fintype.card I : ℝ).sqrt)⁻¹ : ℂ) • ∑ j : I, P.cellIndicator j
      = B ((((Fintype.card I : ℝ).sqrt)⁻¹ : ℂ) • ∑ j : I, EuclideanSpace.single j (1 : ℂ)) := by
    rw [map_smul, map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => heB j)
  -- Propagate the evolution through `exp_intertwine`, then read off the `e_w`/`E_w` overlap.
  rw [hsuper, Graphon.exp_intertwine B _ _ hSinter, heB w]
  rw [hB, LinearIsometry.coe_toContinuousLinearMap, P.cellUniformIsometry.inner_map_map]

/-! ## Summary: the lift in one line

| Phenomenon | Finite                          | Graphon (cell-uniform)        |
| ---------- | ------------------------------- | ----------------------------- |
| PST        | `IsPST_finite H i j τ`          | `IsCellUniformPST W P i j τ`  |
| Mixing     | `IsUniformMixing_finite H i τ`  | `IsCellUniformGraphonMixing`  |
| Search     | (finite spatial search)         | `IsCellUniformSearchSuccess`  |

In each row the **left and right are equivalent** via `cellUniformIsometry`
and the headline lifting theorem `op_restrict_eq_quotient`. -/

end Graphon

end Graphplay
