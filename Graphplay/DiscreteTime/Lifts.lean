/-
# Graphplay.DiscreteTime.Lifts

**DTQW Szegedy property-lift skeleton.**

This file is the discrete-time (Szegedy-walk) analogue of the continuous-time
PST lift `Graphplay.EquitablePartition.pst_lift` (`Graphplay/PST.lean`).  The
CTQW lift falls out of a *single* intertwiner — the cell-embedding `B`
satisfies `A · B = B · symmQuotient` (`adj_mul_cellEmbed`, a one-line
consequence of `restrict_eq_symmQuotient`) and `Bᴴ · B = 1`
(`cellEmbed_conjTranspose_mul_cellEmbed`).  The DTQW story is *structurally
identical*: it falls out of the already-proven equitable-partition lift
`Graphplay.EquitablePartition.dtqw_equitable_lift` (the Szegedy walk preserves
the doubled cell-uniform subspace) plus the **doubled** isometry
`(B⊗B)ᴴ(B⊗B) = 1`.

The doubled cell-embed `B⊗B : Matrix (V×V) (I×I) ℂ` is the DTQW analogue of
`cellEmbed`: its `(i,j)` column is the doubled cell-uniform basis vector
`doubledCellUniformVec i j = e_i ⊗ e_j`.  Compressing the Szegedy walk by it
gives the **Szegedy quotient** `szegedyQuotient = (B⊗B)ᴴ · U_Sz · (B⊗B)`, and
the property lifts characterize host-side cell-uniform PST / mixing against
this compression — exactly as the CTQW iff
(`cellUniformPST_iff_quotientPST`) characterizes against `symmQuotient`
rather than against the raw quotient graph.

### What is proven here (real bodies) vs. carried as honest `sorry`

* **§1** `doubledCellEmbed`, `doubledCellEmbed_col`, `doubledCellEmbed_mulVec`
  — real bodies.  The doubled isometry `doubledCellEmbed_conjTranspose_mul`
  (`(B⊗B)ᴴ(B⊗B) = 1` under `hne`) — **real body**, reduced to two copies of
  `cellEmbed_conjTranspose_mul_cellEmbed` via `Fintype.sum_prod_type`.
* **§2** `szegedyQuotient` — real definition (compression).
* **§3** `szegedyWalk_mul_doubledCellEmbed_col_mem` — **real body**: literally
  `dtqw_equitable_lift` applied to each generator column.  The "range projector
  fixes the doubled subspace" fact `doubledCellEmbed_projFix` (span induction on
  the generators via the isometry) and the intertwiner
  `szegedyWalk_mul_doubledCellEmbed` (★ `U_Sz·B⊗B = B⊗B·szegedyQuotient`,
  column-wise via `Matrix.ext_of_mulVec_single` + `projFix`) are **real bodies**
  — all content sits in the proven `dtqw_equitable_lift` + the isometry.  The
  power form `szegedyWalk_pow_mul_doubledCellEmbed` and the compression identity
  `doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed` are **real bodies**,
  proved by induction from (★) + isometry.
* **§4** genuine, non-vacuous `‖·‖`-transfer predicates
  (`IsCellUniformSzegedyPST`, `IsQuotientSzegedyPST`,
  `IsCellUniformSzegedyMixing`) mirroring `IsCellUniformPST` / `dtqwMixing`.
  Both arc coordinates are cell-resolved (tail cells `(i,j)`, head cells
  `(b,b')`), the head being summed as the DTQW history-marginal; a *free*
  vertex-head sum is not walk-invariant, the cell-uniform head is.
* **§5** the lift theorems, **all real bodies now**.  The general doubled
  matrix-element `doubledCellUniform_matrixElement` (the literal doubled
  `cellUniform_matrixElement`, pure index bookkeeping) powers the bridge
  `cellUniformSzegedyBlock_eq_quotient` (per head cell, doubled matrix element +
  the compression identity).  The three named PST iff lifts
  `cellUniformSzegedyPST_iff_quotient`, `quotientSzegedyPST_of_cellUniform`,
  `cellUniformSzegedyPST_of_quotient` and the `‖·‖²` analogue
  `cellUniformSzegedyMixing_iff_quotient` all close by a single rewrite through
  the bridge / matrix element.
* **§6** `szegedyQuotient_eq_quotientWalk` — the **one genuinely-deep
  residue**: identifying the compression with the *intrinsic* Szegedy walk of
  the quotient graph (correct coin amplitudes, swap coordinates), gated on
  `MagnitudeEquitable`.  This has no CTQW shortcut — CTQW's restriction is
  *literally* `symmQuotient` by a one-line intertwiner, whereas the DTQW
  coin's `√` makes this a real theorem.  The property lifts deliberately do
  **not** depend on it.

Honest hypotheses threaded throughout: `[Nonempty V]`,
`hME : P.MagnitudeEquitable` (the DTQW-only extra, strictly stronger than
signed equitability), `hne : ∀ k, P.cellCard k ≠ 0`.

References: Szegedy, FOCS 2004; Bachman–Tamon, arXiv:1108.0339; Portugal,
*Quantum Walks and Search Algorithms* (2018), §10.3.
-/

import Graphplay.DiscreteTime
import Graphplay.PST

open scoped Matrix
open Complex

universe u v w

namespace Graphplay

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-! ## §1 The doubled cell-embed `B ⊗ B`

The DTQW analogue of `cellEmbed`.  Where the CTQW lift compresses the vertex-
space evolution by `B : Matrix V I ℂ`, the Szegedy walk lives on the arc space
`V × V`, so we compress by the tensor square `B ⊗ B : Matrix (V × V) (I × I) ℂ`.
Its `(i, j)` column is the doubled cell-uniform basis vector
`doubledCellUniformVec i j = e_i ⊗ e_j`.
-/

/-- The **doubled cell-embed** `B ⊗ B : Matrix (V × V) (I × I) ℂ`: the tensor
square of the CTQW cell-embedding.  Entry `(B⊗B)_{(x,y),(i,j)}` is
`cellUniformVec i x · cellUniformVec j y`, so its `(i,j)` column is the doubled
cell-uniform basis vector `doubledCellUniformVec i j`. -/
noncomputable def doubledCellEmbed (P : EquitablePartition G I) :
    Matrix (V × V) (I × I) ℂ :=
  fun p ij => P.cellUniformVec ij.1 p.1 * P.cellUniformVec ij.2 p.2

/-- The `(i, j)` column of `B ⊗ B` is the doubled cell-uniform basis vector
`doubledCellUniformVec i j = e_i ⊗ e_j`.  This is the bridge between the
matrix `doubledCellEmbed` and the span generators used by
`dtqw_equitable_lift`. -/
theorem doubledCellEmbed_col (P : EquitablePartition G I) (i j : I) :
    (fun p => P.doubledCellEmbed p (i, j)) = P.doubledCellUniformVec i j := by
  funext p
  rfl

/-- `B ⊗ B` applied to a quotient-side vector `w : I × I → ℂ` is the doubled
cell-uniform combination:
`((B⊗B) ·ᵥ w) p = ∑_{ij} w ij · (cellUniformVec ij.1 p.1 · cellUniformVec ij.2 p.2)`. -/
theorem doubledCellEmbed_mulVec (P : EquitablePartition G I) (w : I × I → ℂ) :
    P.doubledCellEmbed.mulVec w
      = fun p => ∑ ij, w ij *
          (P.cellUniformVec ij.1 p.1 * P.cellUniformVec ij.2 p.2) := by
  funext p
  simp only [Matrix.mulVec, dotProduct, doubledCellEmbed]
  exact Finset.sum_congr rfl (fun ij _ => mul_comm _ _)

/-- **The doubled cell-embed is an isometry**: `(B⊗B)ᴴ · (B⊗B) = 1`, provided
every cell is nonempty (`hne`).  Proved by reducing the arc-space sum to a
product of two vertex-space sums via `Fintype.sum_prod_type`, each of which is
an entry of the CTQW isometry `cellEmbed_conjTranspose_mul_cellEmbed`.  This is
the doubled analogue of `cellEmbed_conjTranspose_mul_cellEmbed`, and the second
half of what makes the property lift fall out of the proven square. -/
theorem doubledCellEmbed_conjTranspose_mul (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) :
    P.doubledCellEmbedᴴ * P.doubledCellEmbed = (1 : Matrix (I × I) (I × I) ℂ) := by
  have hiso : P.cellEmbedᴴ * P.cellEmbed = (1 : Matrix I I ℂ) :=
    P.cellEmbed_conjTranspose_mul_cellEmbed hne
  ext ij ij'
  rw [Matrix.mul_apply]
  -- Sum over arcs `p = (x, y)`; factor into vertex-space sums in `x` and `y`.
  rw [Fintype.sum_prod_type]
  have hfactor : (∑ x : V, ∑ y : V,
        (P.doubledCellEmbedᴴ ij (x, y)) * P.doubledCellEmbed (x, y) ij')
      = (∑ x : V, star (P.cellUniformVec ij.1 x) * P.cellUniformVec ij'.1 x)
          * (∑ y : V, star (P.cellUniformVec ij.2 y) * P.cellUniformVec ij'.2 y) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    simp only [Matrix.conjTranspose_apply, doubledCellEmbed]
    rw [star_mul']
    ring
  rw [hfactor]
  -- Each factor is an entry of `cellEmbedᴴ * cellEmbed = 1`.
  have hx : (∑ x : V, star (P.cellUniformVec ij.1 x) * P.cellUniformVec ij'.1 x)
      = (1 : Matrix I I ℂ) ij.1 ij'.1 := by
    rw [← hiso, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro x _
    rw [Matrix.conjTranspose_apply]; rfl
  have hy : (∑ y : V, star (P.cellUniformVec ij.2 y) * P.cellUniformVec ij'.2 y)
      = (1 : Matrix I I ℂ) ij.2 ij'.2 := by
    rw [← hiso, Matrix.mul_apply]
    apply Finset.sum_congr rfl; intro y _
    rw [Matrix.conjTranspose_apply]; rfl
  rw [hx, hy]
  -- `[ij.1 = ij'.1] · [ij.2 = ij'.2] = [ij = ij']`.
  simp only [Matrix.one_apply]
  by_cases h1 : ij.1 = ij'.1
  · by_cases h2 : ij.2 = ij'.2
    · rw [if_pos h1, if_pos h2, if_pos (Prod.ext h1 h2), mul_one]
    · rw [if_neg h2, mul_zero, if_neg (fun h => h2 (by rw [h]))]
  · rw [if_neg h1, zero_mul, if_neg (fun h => h1 (by rw [h]))]

/-! ## §2 The Szegedy quotient (compression)

The compression of the Szegedy walk by the doubled cell-embed. -/

/-- The **Szegedy quotient** `szegedyQuotient := (B⊗B)ᴴ · U_Sz · (B⊗B)`: the
compression of the Szegedy walk operator to the quotient arc space `I × I`.
This is the DTQW analogue of the CTQW compression
`(Bᴴ · evolve τ · B) = exp(s • symmQuotient)`.  The property lifts of §5
characterize host-side cell-uniform PST / mixing against this compression. -/
noncomputable def szegedyQuotient (P : EquitablePartition G I) :
    Matrix (I × I) (I × I) ℂ :=
  P.doubledCellEmbedᴴ * G.SzegedyWalk * P.doubledCellEmbed

/-! ## §3 The intertwiner chain

The clean reuse of the proven square.  `dtqw_equitable_lift` is exactly the
statement that the Szegedy walk maps each doubled generator back into the
doubled cell-uniform subspace; we package it as a range-membership of each
column, then promote it to the matrix intertwiner `U_Sz·B⊗B = B⊗B·szegedyQuotient`,
the power form, and the compression identity. -/

/-- **Range membership of each generator column** — the clean reuse of the
proven square.  This is literally `dtqw_equitable_lift` applied to the `(i,j)`
column of `B ⊗ B` (which is the generator `doubledCellUniformVec i j`): the
Szegedy walk maps it back into the doubled cell-uniform subspace. -/
theorem szegedyWalk_mul_doubledCellEmbed_col_mem [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable) (i j : I) :
    (G.SzegedyWalk).mulVec (fun p => P.doubledCellEmbed p (i, j))
      ∈ P.doubledCellUniformSubspace := by
  rw [doubledCellEmbed_col]
  exact dtqw_equitable_lift P hME _
    (Submodule.subset_span ⟨(i, j), rfl⟩)

/-- The `(i,j)` column of `B ⊗ B`, as a `mulVec` against the standard basis
vector `Pi.single (i,j) 1`, is the doubled generator `doubledCellUniformVec i j`.
This is the `mulVec`-form of `doubledCellEmbed_col`, used to feed each column of
`U_Sz·(B⊗B)` into the membership lemma and the range-projector identity. -/
theorem doubledCellEmbed_mulVec_single (P : EquitablePartition G I) (i j : I) :
    P.doubledCellEmbed.mulVec (Pi.single (i, j) 1) = P.doubledCellUniformVec i j := by
  rw [Matrix.mulVec_single_one]
  funext p
  exact congrFun (doubledCellEmbed_col P i j) p

/-- **The range projector fixes the doubled cell-uniform subspace.**  For any
`v` in `doubledCellUniformSubspace`, the range projector `(B⊗B)(B⊗B)ᴴ` fixes it:
`(B⊗B) ·ᵥ ((B⊗B)ᴴ ·ᵥ v) = v`.  This is the *mechanical* span/projector fact
behind the intertwiner (★): a vector in the range of the isometry `B⊗B` is fixed
by its range projector.  Proved by `span_induction` over the doubled generators,
using only the isometry `(B⊗B)ᴴ(B⊗B) = 1` (`doubledCellEmbed_conjTranspose_mul`).
On a generator `doubledCellUniformVec i j = (B⊗B) ·ᵥ e_{ij}`, the round-trip
collapses via `(B⊗B)ᴴ(B⊗B) = 1`. -/
theorem doubledCellEmbed_projFix (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (v : (V × V) → ℂ)
    (hv : v ∈ P.doubledCellUniformSubspace) :
    P.doubledCellEmbed.mulVec (P.doubledCellEmbedᴴ.mulVec v) = v := by
  have hiso : P.doubledCellEmbedᴴ * P.doubledCellEmbed
      = (1 : Matrix (I × I) (I × I) ℂ) := doubledCellEmbed_conjTranspose_mul P hne
  unfold doubledCellUniformSubspace at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hx
    -- `x = doubledCellUniformVec i j = (B⊗B) ·ᵥ e_{ij}`; round-trip via `(B⊗B)ᴴ(B⊗B)=1`.
    show P.doubledCellEmbed.mulVec (P.doubledCellEmbedᴴ.mulVec (P.doubledCellUniformVec i j))
      = P.doubledCellUniformVec i j
    -- The inner round-trip `(B⊗B)ᴴ ·ᵥ doubledCellUniformVec i j = e_{ij}`: write
    -- `doubledCellUniformVec i j = B⊗B ·ᵥ e_{ij}`, combine, and collapse via the isometry.
    have hinner : P.doubledCellEmbedᴴ.mulVec (P.doubledCellUniformVec i j)
        = (Pi.single (i, j) 1 : I × I → ℂ) := by
      rw [← doubledCellEmbed_mulVec_single P i j, Matrix.mulVec_mulVec, hiso, Matrix.one_mulVec]
    rw [hinner, doubledCellEmbed_mulVec_single]
  | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy]
  | smul a x _ hx =>
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hx]

/-- **The Szegedy intertwiner** (★): `U_Sz · (B⊗B) = (B⊗B) · szegedyQuotient`.

This is the DTQW analogue of `adj_mul_cellEmbed`
(`A · B = B · symmQuotient`).  Mathematically it is the statement that the
range of `B⊗B` (the doubled cell-uniform subspace) is `U_Sz`-invariant
(`szegedyWalk_mul_doubledCellEmbed_col_mem`, i.e. `dtqw_equitable_lift`), so the
range projector `(B⊗B)(B⊗B)ᴴ` fixes the columns of `U_Sz·(B⊗B)`; combined with
the isometry `(B⊗B)ᴴ(B⊗B)=1` this gives `U_Sz·(B⊗B) = (B⊗B)(B⊗B)ᴴ U_Sz (B⊗B) =
(B⊗B)·szegedyQuotient`.

**Now proven** (sorry-free): column-wise via `Matrix.ext_of_mulVec_single`.
Each column `U_Sz ·ᵥ (col_{ij} (B⊗B))` lands in the subspace
(`szegedyWalk_mul_doubledCellEmbed_col_mem` = `dtqw_equitable_lift`), so the range
projector fixes it (`doubledCellEmbed_projFix`); reassociating gives the
`(B⊗B)·szegedyQuotient` column.  All mathematical content sits in the proven
`dtqw_equitable_lift` + the isometry `doubledCellEmbed_conjTranspose_mul`. -/
theorem szegedyWalk_mul_doubledCellEmbed [Nonempty V] (P : EquitablePartition G I)
    (hME : P.MagnitudeEquitable) (hne : ∀ k, P.cellCard k ≠ 0) :
    G.SzegedyWalk * P.doubledCellEmbed
      = P.doubledCellEmbed * P.szegedyQuotient := by
  -- Column-wise: it suffices to match `· ·ᵥ Pi.single (i,j) 1` for every `(i,j)`.
  apply Matrix.ext_of_mulVec_single
  rintro ⟨i, j⟩
  -- LHS column: `U_Sz ·ᵥ (col_{ij} (B⊗B)) = U_Sz ·ᵥ doubledCellUniformVec i j`.
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, doubledCellEmbed_mulVec_single]
  -- The image lies in the doubled cell-uniform subspace (the proven square).
  have hmem : (G.SzegedyWalk).mulVec (P.doubledCellUniformVec i j)
      ∈ P.doubledCellUniformSubspace := by
    have := szegedyWalk_mul_doubledCellEmbed_col_mem P hME i j
    rwa [doubledCellEmbed_col] at this
  -- RHS column: `B⊗B ·ᵥ (szegedyQuotient ·ᵥ e_{ij})` unfolds to the range projector
  -- applied to `U_Sz ·ᵥ doubledCellUniformVec i j`, which the projector fixes.
  unfold szegedyQuotient
  -- `(B⊗B · (B⊗Bᴴ · U · B⊗B)) ·ᵥ single = B⊗B ·ᵥ (B⊗Bᴴ ·ᵥ (U ·ᵥ (B⊗B ·ᵥ single)))`.
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, doubledCellEmbed_mulVec_single]
  -- Goal: `U ·ᵥ doubledCellUniformVec i j = B⊗B ·ᵥ (B⊗Bᴴ ·ᵥ (U ·ᵥ doubledCellUniformVec i j))`.
  exact (doubledCellEmbed_projFix P hne _ hmem).symm

/-- **Power form** of the intertwiner: `U_Sz^τ · (B⊗B) = (B⊗B) · szegedyQuotient^τ`.
Proved by induction from the base intertwiner (★) and the isometry, exactly as
`smul_adj_pow_mul_cellEmbed` is proved from `adj_mul_cellEmbed`. -/
theorem szegedyWalk_pow_mul_doubledCellEmbed [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (τ : ℕ) :
    G.SzegedyWalk ^ τ * P.doubledCellEmbed
      = P.doubledCellEmbed * P.szegedyQuotient ^ τ := by
  induction τ with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc,
      szegedyWalk_mul_doubledCellEmbed P hME hne,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

/-- **The compression identity** (DTQW analogue of the CTQW
`cellEmbedᴴ · evolve · cellEmbed = exp(s • symmQuotient)`, the step inside
`pst_lift`): `(B⊗B)ᴴ · U_Sz^τ · (B⊗B) = szegedyQuotient^τ`.  Proved from the
power form (★) plus the isometry `(B⊗B)ᴴ(B⊗B) = 1`. -/
theorem doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (τ : ℕ) :
    P.doubledCellEmbedᴴ * G.SzegedyWalk ^ τ * P.doubledCellEmbed
      = P.szegedyQuotient ^ τ := by
  rw [Matrix.mul_assoc, szegedyWalk_pow_mul_doubledCellEmbed P hME hne,
    ← Matrix.mul_assoc, doubledCellEmbed_conjTranspose_mul P hne, Matrix.one_mul]

/-! ## §4 Genuine, non-vacuous DTQW transfer predicates

These mirror `IsCellUniformPST` / `dtqwMixing`: Born-modulus,
`√(|C_·|)`-normalized amplitudes of the **doubled** cell-uniform sector (the
sector the equitable lift preserves).  The Szegedy walker's two arc coordinates
are *both* cell-resolved — the tail at cells `(i, j)`, the head at cells
`(b, b')` — and the DTQW "history marginal" is the sum over the head cell(s),
mirroring `IsDTQW_PST`'s `∑_y` but at the level of the doubled cell-uniform
basis rather than raw vertices (a free vertex-head sum is *not* preserved by the
walk; the cell-uniform head is).  They are NOT stubs — each is a genuine
`‖·‖ = 1` (resp. `= 1/|I|`) transfer condition on the *normalized* amplitude;
e.g. `IsCellUniformSzegedyPST i i 0` already fails for `|I| > 1`. -/

/-- **Cell-uniform Szegedy PST.**  Born-modulus-1 of the normalized doubled
arc-block amplitude after `τ` steps.  The Szegedy walker lives on the arc space
`V × V` (tail, head); the *doubled cell-uniform arc state at `(i, b)`* is the
tensor `e_i ⊗ e_b` of the tail-cell-uniform state on cell `i` with the
head-cell-uniform state on cell `b`.  The amplitude here is

  `∑_b ⟨e_j ⊗ e_b | U_Sz^τ | e_i ⊗ e_b⟩`,

the position-marginal over the *head cell* `b` of the tail-`i` → tail-`j`
transition: with the tail at cell `i`/`j` (vertices `x ∈ C_i`, `x' ∈ C_j`) and
the head at the common cell `b` (vertices `y, y' ∈ C_b`), normalized by
`√|C_i| √|C_j|` for the tails and `|C_b| = √|C_b|·√|C_b|` for the head.  Summing
over `b` is the DTQW head-marginal exactly mirroring `IsDTQW_PST`'s `∑_y` (but
*cell*-resolved, because the doubled cell-uniform sector is what the equitable
lift preserves).  This is the DTQW analogue of `IsCellUniformPST` (the Szegedy
walk replacing `G.evolve`).  It is a genuine transfer condition (modulus exactly
one of a normalized unit-vector amplitude), not a degenerate existential. -/
def IsCellUniformSzegedyPST (P : EquitablePartition G I) (i j : I) (τ : ℕ) : Prop :=
  ‖∑ b, (∑ x, ∑ x', ∑ y, ∑ y',
      if P.cells x = i ∧ P.cells x' = j ∧ P.cells y = b ∧ P.cells y' = b
        then (G.SzegedyWalk ^ τ) (x', y') (x, y) else 0) /
      ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ) *
        ((Real.sqrt (P.cellCard b) : ℂ) * (Real.sqrt (P.cellCard b) : ℂ)))‖ = 1

/-- **Quotient Szegedy PST.**  Born-modulus-1 of the quotient arc-block
amplitude `∑_b (szegedyQuotient^τ)_{(j,b),(i,b)}` — the position-marginal of the
compressed walk on the quotient arc space `I × I`.  This is the quotient-side
predicate that the lift transfers from / to. -/
def IsQuotientSzegedyPST (P : EquitablePartition G I) (i j : I) (τ : ℕ) : Prop :=
  ‖∑ b, (P.szegedyQuotient ^ τ) (j, b) (i, b)‖ = 1

/-- **Cell-uniform Szegedy mixing.**  The `‖·‖²` (Born-probability) analogue of
`IsCellUniformSzegedyPST`: the total Born probability of the doubled
cell-uniform tail-`i` → tail-`j` transition, summed over *all* head-cell pairs
`(b, b')`, equals `1/|I|` — the uniform distribution on the `|I|` quotient cells.
Each squared term is the modulus-squared of the same normalized doubled
arc-block amplitude `⟨e_j ⊗ e_{b'} | U_Sz^τ | e_i ⊗ e_b⟩` whose un-squared,
head-diagonal (`b = b'`) marginal drives `IsCellUniformSzegedyPST`.  This is the
DTQW analogue of `IsDTQW_UniformMixing` lifted to the doubled cell-uniform
sector. -/
def IsCellUniformSzegedyMixing (P : EquitablePartition G I) (i j : I) (τ : ℕ) : Prop :=
  (∑ b, ∑ b', ‖(∑ x, ∑ x', ∑ y, ∑ y',
      if P.cells x = i ∧ P.cells x' = j ∧ P.cells y = b ∧ P.cells y' = b'
        then (G.SzegedyWalk ^ τ) (x', y') (x, y) else 0) /
      ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ) *
        ((Real.sqrt (P.cellCard b) : ℂ) * (Real.sqrt (P.cellCard b') : ℂ)))‖ ^ 2)
      = 1 / (Fintype.card I : ℝ)

/-! ## §5 The LIFT theorems

These mirror `cellUniformPST_iff_quotientPST` / `pst_lift`.  The bridge
identifies the host-side normalized block amplitude with the quotient-side
amplitude (the doubled `cellUniform_matrixElement`); the iff then follows by a
single `congrArg norm` rewrite — exactly as the CTQW iff falls out of the
compression identity. -/

/-- **The doubled cell-uniform matrix element** (pure index bookkeeping, the
DTQW analogue of `cellUniform_matrixElement`).  For any arc-space matrix
`M : Matrix (V×V) (V×V) ℂ`, the `√`-normalized doubled arc-block sum over the
tail cells `(i, j)` and head cells `(b, b')` equals the `((j,b'),(i,b))` entry
of the compression `(B⊗B)ᴴ · M · (B⊗B)`.  No equitability is used; this is the
literal doubled `cellUniform_matrixElement` (two factors of the proof, one per
arc coordinate). -/
theorem doubledCellUniform_matrixElement (P : EquitablePartition G I)
    (M : Matrix (V × V) (V × V) ℂ) (i j b b' : I) :
    (∑ x, ∑ x', ∑ y, ∑ y',
        if P.cells x = i ∧ P.cells x' = j ∧ P.cells y = b ∧ P.cells y' = b'
          then M (x', y') (x, y) else 0) /
        ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ) *
          ((Real.sqrt (P.cellCard b) : ℂ) * (Real.sqrt (P.cellCard b') : ℂ)))
      = (P.doubledCellEmbedᴴ * M * P.doubledCellEmbed) (j, b') (i, b) := by
  classical
  rw [Matrix.mul_apply]
  -- RHS = ∑_q (B⊗Bᴴ·M)_{(j,b') q} (B⊗B)_{q (i,b)}
  --     = ∑_q ∑_p star((B⊗B)_{p (j,b')}) M_{p q} (B⊗B)_{q (i,b)}.
  have hRHS : (∑ q : V × V, (P.doubledCellEmbedᴴ * M) (j, b') q * P.doubledCellEmbed q (i, b))
      = ∑ q : V × V, ∑ p : V × V,
          star (P.doubledCellEmbed p (j, b')) * M p q * P.doubledCellEmbed q (i, b) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Matrix.conjTranspose_apply]
  rw [hRHS]
  -- Reindex both `q = (x, y)` and `p = (x', y')`, push the division through.
  rw [Fintype.sum_prod_type]
  rw [show (∑ x : V, ∑ y : V, ∑ p : V × V,
        star (P.doubledCellEmbed p (j, b')) * M p (x, y) * P.doubledCellEmbed (x, y) (i, b))
        = ∑ x : V, ∑ y : V, ∑ x' : V, ∑ y' : V,
            star (P.doubledCellEmbed (x', y') (j, b')) * M (x', y') (x, y)
              * P.doubledCellEmbed (x, y) (i, b) from by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    rw [Fintype.sum_prod_type]]
  -- Now both sides are sums over (x, y, x', y'); match termwise after the division.
  -- LHS triple-sum is in order (x, x', y, y'); reorder to (x, y, x', y').
  rw [show (∑ x : V, ∑ x' : V, ∑ y : V, ∑ y' : V,
          if P.cells x = i ∧ P.cells x' = j ∧ P.cells y = b ∧ P.cells y' = b'
            then M (x', y') (x, y) else 0)
        = ∑ x : V, ∑ y : V, ∑ x' : V, ∑ y' : V,
            if P.cells x = i ∧ P.cells x' = j ∧ P.cells y = b ∧ P.cells y' = b'
              then M (x', y') (x, y) else 0 from by
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_comm]]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro x' _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro y' _
  -- Pointwise: expand the doubled embeds, push `star` inside the real factors,
  -- then split the four cell indicators and finish with field arithmetic.
  simp only [doubledCellEmbed, cellUniformVec, star_mul', apply_ite (star : ℂ → ℂ),
    star_zero, Complex.star_def, map_div₀, map_one, Complex.conj_ofReal]
  split_ifs with h h1 h2 h3 h4 h5 h6 h7 <;>
    first
      | (exfalso; tauto)
      | ring

/-- **The bridge** (doubled `cellUniform_matrixElement`): the normalized
host-side doubled arc-block amplitude equals the quotient-side position-marginal
amplitude.  This is the DTQW analogue of `cellUniform_matrixElement` composed
with the compression identity
`doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed`.

**Now proven** (sorry-free): per head cell `b`, the inner block sum is the
doubled `cellUniform_matrixElement` of `U_Sz^τ` at tail cells `(i, j)` and head
cells `(b, b)`, i.e. `((B⊗B)ᴴ U_Sz^τ (B⊗B))((j,b),(i,b))`; the compression
identity `doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed` rewrites that
matrix to `szegedyQuotient^τ`, and summing over `b` gives the position-marginal.
All content is mechanical bookkeeping on top of the proven square. -/
theorem cellUniformSzegedyBlock_eq_quotient [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) (τ : ℕ) :
    (∑ b, (∑ x, ∑ x', ∑ y, ∑ y',
        if P.cells x = i ∧ P.cells x' = j ∧ P.cells y = b ∧ P.cells y' = b
          then (G.SzegedyWalk ^ τ) (x', y') (x, y) else 0) /
        ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ) *
          ((Real.sqrt (P.cellCard b) : ℂ) * (Real.sqrt (P.cellCard b) : ℂ))))
      = ∑ b, (P.szegedyQuotient ^ τ) (j, b) (i, b) := by
  apply Finset.sum_congr rfl
  intro b _
  -- Each summand is a doubled cell-uniform matrix element of `U_Sz^τ`, which the
  -- compression identity rewrites to a `szegedyQuotient^τ` entry.
  rw [doubledCellUniform_matrixElement P (G.SzegedyWalk ^ τ) i j b b,
    ← doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed P hME hne τ]

/-- **The DTQW PST iff lift** (DTQW analogue of `cellUniformPST_iff_quotientPST`):
host-side cell-uniform Szegedy PST holds **iff** the Szegedy quotient exhibits
quotient PST.  Proved sorry-free by a single rewrite through the (now proven)
bridge `cellUniformSzegedyBlock_eq_quotient`; all the mathematical content sits
in `dtqw_equitable_lift` (the square) + the doubled `cellUniform_matrixElement`.
Neither *direction* of this iff is deep. -/
theorem cellUniformSzegedyPST_iff_quotient [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) (τ : ℕ) :
    P.IsCellUniformSzegedyPST i j τ ↔ P.IsQuotientSzegedyPST i j τ := by
  unfold IsCellUniformSzegedyPST IsQuotientSzegedyPST
  rw [cellUniformSzegedyBlock_eq_quotient P hME hne i j τ]

/-- **Forward direction** (`.mp`): cell-uniform Szegedy PST on the host implies
quotient PST on the Szegedy quotient. -/
theorem quotientSzegedyPST_of_cellUniform [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) {i j : I} {τ : ℕ}
    (h : P.IsCellUniformSzegedyPST i j τ) :
    P.IsQuotientSzegedyPST i j τ :=
  (cellUniformSzegedyPST_iff_quotient P hME hne i j τ).mp h

/-- **Backward direction** (`.mpr`) — the DTQW `pst_lift`: quotient PST on the
Szegedy quotient lifts to cell-uniform Szegedy PST on the host graph.  This is
the discrete-time analogue of `EquitablePartition.pst_lift`. -/
theorem cellUniformSzegedyPST_of_quotient [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) {i j : I} {τ : ℕ}
    (h : P.IsQuotientSzegedyPST i j τ) :
    P.IsCellUniformSzegedyPST i j τ :=
  (cellUniformSzegedyPST_iff_quotient P hME hne i j τ).mpr h

/-- **The DTQW mixing iff lift.**  Host-side cell-uniform Szegedy mixing holds
iff the Szegedy quotient's doubled mixing block equals `1/|I|`.  This is the
`‖·‖²` analogue of `cellUniformSzegedyPST_iff_quotient`.

**Now proven** (sorry-free): the `‖·‖²` analogue of the bridge — applying the
*same* doubled `cellUniform_matrixElement` + compression identity per head-cell
pair `(b, b')` turns each normalized host block amplitude into the quotient
entry `(szegedyQuotient^τ)((j,b'),(i,b))`; squaring the moduli and summing over
`(b, b')` is then termwise identical on both sides.  Mechanical bookkeeping on
top of the proven square, with `‖·‖²` in place of the bare amplitude. -/
theorem cellUniformSzegedyMixing_iff_quotient [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) (τ : ℕ) :
    P.IsCellUniformSzegedyMixing i j τ ↔
      (∑ b, ∑ b', ‖(P.szegedyQuotient ^ τ) (j, b') (i, b)‖ ^ 2)
        = 1 / (Fintype.card I : ℝ) := by
  unfold IsCellUniformSzegedyMixing
  -- Each host block amplitude is the quotient entry (doubled matrix element +
  -- compression); squared moduli therefore match termwise.
  have hterm : ∀ b b' : I,
      ‖(∑ x, ∑ x', ∑ y, ∑ y',
          if P.cells x = i ∧ P.cells x' = j ∧ P.cells y = b ∧ P.cells y' = b'
            then (G.SzegedyWalk ^ τ) (x', y') (x, y) else 0) /
          ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ) *
            ((Real.sqrt (P.cellCard b) : ℂ) * (Real.sqrt (P.cellCard b') : ℂ)))‖ ^ 2
        = ‖(P.szegedyQuotient ^ τ) (j, b') (i, b)‖ ^ 2 := by
    intro b b'
    rw [doubledCellUniform_matrixElement P (G.SzegedyWalk ^ τ) i j b b',
      ← doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed P hME hne τ]
  rw [show (∑ b, ∑ b', ‖(∑ x, ∑ x', ∑ y, ∑ y',
          if P.cells x = i ∧ P.cells x' = j ∧ P.cells y = b ∧ P.cells y' = b'
            then (G.SzegedyWalk ^ τ) (x', y') (x, y) else 0) /
          ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ) *
            ((Real.sqrt (P.cellCard b) : ℂ) * (Real.sqrt (P.cellCard b') : ℂ)))‖ ^ 2)
        = ∑ b, ∑ b', ‖(P.szegedyQuotient ^ τ) (j, b') (i, b)‖ ^ 2 from by
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro b' _
    exact hterm b b']

/-! ## §6 The one genuinely-deep residue: identification with the intrinsic
quotient Szegedy walk.

`szegedyQuotient` is, by construction, the *compression* `(B⊗B)ᴴ U_Sz (B⊗B)`.
The property lifts of §5 characterize against this compression — exactly as the
CTQW iff characterizes against `symmQuotient`.  The genuinely-deep theorem,
with no CTQW shortcut, is that this compression *equals* the Szegedy walk of
the quotient graph built intrinsically from its own coin amplitudes and swap.

CTQW has a one-line intertwiner here (`A·B = B·symmQuotient`); the DTQW coin's
`√` does not commute with the cell-sum, so this is a real theorem, additionally
gated on `MagnitudeEquitable`. -/

/-- **Identification with the intrinsic quotient Szegedy walk** — the one
genuinely-deep residue.

Given a quotient weighted graph `Q : WeightedGraph I` whose adjacency matrix
agrees off-diagonal with the symmetric quotient `symmQuotient` of `P` (so `Q`
is the bona-fide quotient graph on the cell index set `I`), the Szegedy-walk
compression `szegedyQuotient` equals the *intrinsic* Szegedy walk `Q.SzegedyWalk`
of the quotient graph.

This is what has **no CTQW shortcut**: the continuous-time restriction is
*literally* `symmQuotient` by the one-line intertwiner `adj_mul_cellEmbed`,
whereas matching the Szegedy *coin amplitudes* `√(‖Q.adj‖ / D)` after
compression (rather than the linear adjacency) is a genuine identity, true only
because magnitude-equitability (`hME`) makes the host coin amplitudes
cell-functions.  The property lifts of §5 deliberately do **not** depend on
this; they characterize against the compression `szegedyQuotient` directly. -/
theorem szegedyQuotient_eq_quotientWalk [Nonempty V] (P : EquitablePartition G I)
    (hME : P.MagnitudeEquitable) (hne : ∀ k, P.cellCard k ≠ 0)
    (Q : WeightedGraph I)
    (hQ : ∀ i j, i ≠ j → Q.adj i j = P.symmQuotient i j) :
    P.szegedyQuotient = Q.SzegedyWalk := by
  sorry

end EquitablePartition

end Graphplay
