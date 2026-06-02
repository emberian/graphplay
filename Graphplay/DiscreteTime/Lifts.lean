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
* **§6** identification of the compression with the *intrinsic* Szegedy walk of
  the quotient graph — the **one genuinely-deep residue**, now **resolved** (all
  real bodies, sorry-free).  The compression factors as `szegedyQuotient =
  S_I · (2 • ψProj − 1)` (`szegedyQuotient_factor`), where `S_I = szSwap I`
  (`szSwapQuotient`, real body) and `ψProj` is the rank-one-per-block projector
  built from the **compression coin amplitudes** `ψ(i,b) =
  √|C_b|·szCoinAmp(r_i,r_b)` (`szReflectionProjQuotient`, the real combinatorial
  engine, extracted from `szReflectionProj_preserves_doubled`).  The whole
  identification thereby reduces to a **single per-edge scalar identity**
  `Q.szCoinAmp = ψ`, under which `szegedyQuotient = Q.SzegedyWalk` is proved
  (`szegedyQuotient_eq_quotientWalk_of_coinAmp`).  **Correction:** the naive
  `Q.adj = symmQuotient`-gated form is *false* — `ψ`'s probabilities are the
  *cell masses* `|C_b|·‖A_{r_i r_b}‖`, whereas `symmQuotient` carries an extra
  `1/√|C_b|` distortion; they disagree on any tail cell reaching two
  unequal-sized cells (smallest witness `K_{1,3}` with leaves split `{·}⊔{·,·}`,
  see `szegedyQuotient_ne_symmQuotientWalk_counterexample`).  The correct
  intrinsic walk is that of the *lumped Markov chain* on cells.  The property
  lifts of §5 deliberately do **not** depend on any of this.

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
gated on `MagnitudeEquitable`.

### What is genuinely true here, and the precise obstruction (read this).

The clean, *proved* facts below reduce the whole identification to a **single
per-edge scalar identity**, and pin down exactly what the intrinsic quotient
walk must be built from.

The compression splits as `szegedyQuotient = (B⊗B)ᴴ S R (B⊗B)`.  Two pieces:

* **Swap** (`szSwapQuotient`, real body): `(B⊗B)ᴴ · S_V · (B⊗B) = S_I`, the
  swap on the *quotient* arc space.  The swap permutes the doubled generators
  `e_i ⊗ e_j ↦ e_j ⊗ e_i`, so its compression is literally `szSwap I`.  No
  hypothesis beyond the isometry.

* **Projector** (`szReflectionProjQuotient`, real body): the compression of the
  Szegedy projector is again a rank-one-per-tail-block projector,
  `(B⊗B)ᴴ · Π_V · (B⊗B) = ψProj`, with entry
  `ψProj_{(i',j'),(i,j)} = [i' = i] · ψ(i,j') · ψ(i,j)`, where the **compression
  coin amplitude** is
  `ψ(i,b) = √|C_b| · G.szCoinAmp (cellRep i) (cellRep b)`
  (`compressionCoinAmp`).  Its square is `ψ(i,b)² = |C_b|·‖A_{r_i r_b}‖ / D_{r_i}`,
  the transition probability of the **lumped random walk on cells** (jump from
  cell `i` to cell `b` with probability proportional to the *total* magnitude
  mass `|C_b|·‖A_{r_i r_b}‖` into cell `b`).  This is the genuine content,
  extracted from the proven `szReflectionProj_preserves_doubled`.

Assembling, `szegedyQuotient = S_I · (2 • ψProj − 1)`.  The intrinsic
`Q.SzegedyWalk = S_I · (2 • Q.szReflectionProj − 1)`, with
`Q.szReflectionProj_{(i',j'),(i,j)} = [i'=i] · Q.szCoinAmp i j' · Q.szCoinAmp i j`.
So the identification holds **iff** the single per-edge identity

  `(†)   ψ(i,b) = Q.szCoinAmp i b      ∀ i b : I`

holds (`compressionCoinAmp_eq` is exactly this hypothesis), via
`szegedyQuotient_eq_quotientWalk_of_coinAmp` (real body).

**The obstruction — the originally-stated `symmQuotient` hypothesis is FALSE.**
`(†)` squares to `|C_b|·‖A_{r_i r_b}‖ / D_{r_i} = ‖Q.adj i b‖ / Q.D_i`, i.e.
`‖Q.adj i b‖` must be **proportional (per row `i`) to the cell mass
`|C_b|·‖A_{r_i r_b}‖`**.  But the symmetric quotient has magnitude
`‖symmQuotient i b‖ = √|C_i|·‖∑_{z∈C_b} A_{r_i z}‖ / √|C_b|`, which even in the
real-nonnegative case (`‖∑_{z∈C_b} A_{r_i z}‖ = |C_b|·‖A_{r_i r_b}‖`) equals
`√|C_i|·√|C_b|·‖A_{r_i r_b}‖` — carrying an **extra `1/√|C_b|` distortion**
relative to the mass `|C_b|·‖A_{r_i r_b}‖`.  So with `Q.adj = symmQuotient` the
coin amplitudes differ whenever two cells reached from one tail have *unequal
size* (and agree iff all reachable cells are equal-sized).

Smallest witness (`szegedyQuotient_ne_symmQuotientWalk_counterexample`, an honest
prose record): the star `K_{1,3}` with the three leaves split `{1} ⊔ {2,3}`,
magnitude-equitable.  From tail cell `0`: the compression coin amplitudes are
`ψ(0,·) = (0, 1/√3, √(2/3)) ≈ (0, 0.577, 0.816)`, whereas the `symmQuotient`-built
intrinsic amplitudes are `(0, √(2−√2)/·, …) ≈ (0, 0.644, 0.765)`.  Distinct —
the `symmQuotient`-gated statement is *false*.

The **correct** intrinsic walk to compare against is the Szegedy walk of the
*lumped chain*: the one whose adjacency magnitudes are the cell masses
`|C_b|·‖A_{r_i r_b}‖` (equivalently, in the real-nonnegative case, the **raw
branching quotient** `P.quotient`, whose magnitude `‖∑_{z∈C_b} A_{r_i z}‖ =
|C_b|·‖A_{r_i r_b}‖` is exactly the mass — verified numerically to match `ψ`
edge-for-edge).  That is the content of the honest, gated
`szegedyQuotient_eq_quotientWalk_of_coinAmp`. -/

/-- **`(B⊗B)ᴴ` collapses a doubled generator to a quotient basis vector.**
`(B⊗B)ᴴ ·ᵥ doubledCellUniformVec a b = e_{(a,b)}` (the standard basis vector
`Pi.single (a,b) 1` on the quotient arc space), provided every cell is nonempty.
This is the isometry round-trip `(B⊗B)ᴴ (B⊗B) e_{(a,b)} = e_{(a,b)}` read on the
generator `doubledCellUniformVec a b = (B⊗B) ·ᵥ e_{(a,b)}`. -/
theorem doubledCellEmbedH_mulVec_generator (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (a b : I) :
    P.doubledCellEmbedᴴ.mulVec (P.doubledCellUniformVec a b)
      = (Pi.single (a, b) 1 : I × I → ℂ) := by
  have hiso : P.doubledCellEmbedᴴ * P.doubledCellEmbed
      = (1 : Matrix (I × I) (I × I) ℂ) := doubledCellEmbed_conjTranspose_mul P hne
  rw [← doubledCellEmbed_mulVec_single P a b, Matrix.mulVec_mulVec, hiso, Matrix.one_mulVec]

/-- **Swap compression.**  `(B⊗B)ᴴ · S_V · (B⊗B) = S_I`: the compression of the
arc-space swap is the swap on the quotient arc space.  Column-wise: on
`e_{(i,j)}` the chain is
`e_{(i,j)} → (B⊗B) → e_i⊗e_j → S_V → e_j⊗e_i → (B⊗B)ᴴ → e_{(j,i)}`, which is
exactly `S_I ·ᵥ e_{(i,j)} = e_{(j,i)}`.  No equitability needed; pure
generator-permutation + isometry. -/
theorem szSwapQuotient (P : EquitablePartition G I) (hne : ∀ k, P.cellCard k ≠ 0) :
    P.doubledCellEmbedᴴ * WeightedGraph.szSwap V * P.doubledCellEmbed
      = WeightedGraph.szSwap I := by
  apply Matrix.ext_of_mulVec_single
  rintro ⟨i, j⟩
  -- LHS column.
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, doubledCellEmbed_mulVec_single,
    szSwap_mulVec_doubledCellUniformVec, doubledCellEmbedH_mulVec_generator P hne]
  -- RHS column: `S_I ·ᵥ e_{(i,j)} = e_{(j,i)}`.
  funext p
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  -- LHS: `e_{(j,i)} p = [p = (j,i)]`; RHS: `szSwap I p (i,j) = [p.1 = j ∧ p.2 = i]`.
  rw [Pi.single_apply]
  show (if p = (j, i) then (1 : ℂ) else 0)
      = (if p.1 = (i, j).2 ∧ p.2 = (i, j).1 then (1 : ℂ) else 0)
  by_cases h : p = (j, i)
  · rw [if_pos h, if_pos ⟨by rw [h], by rw [h]⟩]
  · rw [if_neg h, if_neg (fun hc => h (Prod.ext hc.1 hc.2))]

/-- The **compression coin amplitude** `ψ(i, b) := √|C_b| · φ_{r_i}(r_b)` where
`r_i = cellRep i` and `φ = szCoinAmp`.  Its square `ψ(i,b)² = |C_b|·‖A_{r_i r_b}‖
/ D_{r_i}` is the transition probability of the lumped random walk on cells.
This is the coin amplitude of the *compressed* Szegedy walk; the identification
with the intrinsic quotient walk is exactly the assertion `ψ = Q.szCoinAmp`. -/
noncomputable def compressionCoinAmp [Nonempty V] (P : EquitablePartition G I)
    (i b : I) : ℂ :=
  (Real.sqrt (P.cellCard b) : ℂ) * G.szCoinAmp (P.cellRep i) (P.cellRep b)

/-- **The middle scalar `t(r_i)` is `√|C_j| · φ_{r_i}(r_j)`.**  In
`szReflectionProj_preserves_doubled`, the projector's action on `e_i ⊗ e_j`
carried a scalar `t(r_i) = ∑_y conj(φ_{r_i}(y)) · (e_j)_y`.  Under
magnitude-equitability this collapses: `φ_{r_i}(y) = φ_{r_i}(r_j)` for `y ∈ C_j`
(real), and `(e_j)_y = 1/√|C_j|` there, so `t(r_i) = |C_j| · φ_{r_i}(r_j)/√|C_j|
= √|C_j| · φ_{r_i}(r_j) = ψ(i, j)`. -/
theorem szReflectionProj_middleScalar [Nonempty V] (P : EquitablePartition G I)
    (hME : P.MagnitudeEquitable) (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) :
    (∑ y, (starRingEnd ℂ) (G.szCoinAmp (P.cellRep i) y) * P.cellUniformVec j y)
      = P.compressionCoinAmp i j := by
  classical
  -- nonemptiness of cell `j`
  have hjpos : (0 : ℝ) < P.cellCard j :=
    lt_of_le_of_ne (P.cellCard_nonneg j) (Ne.symm (hne j))
  have hcj : (Real.sqrt (P.cellCard j) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (Real.sqrt_pos.mpr hjpos)
  have hjne : (Finset.univ.filter (fun w : V => P.cells w = j)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hne j; unfold EquitablePartition.cellCard; rw [h]; simp
  obtain ⟨yj, hyj⟩ := hjne
  rw [Finset.mem_filter] at hyj
  -- only `y ∈ C_j` contributes; there the coin amp is `φ_{r_i}(r_j)` (mag-eq, real).
  have hstep : ∀ y, (starRingEnd ℂ) (G.szCoinAmp (P.cellRep i) y) * P.cellUniformVec j y
      = if P.cells y = j
          then G.szCoinAmp (P.cellRep i) (P.cellRep j) * (1 / (Real.sqrt (P.cellCard j) : ℂ))
          else 0 := by
    intro y
    unfold EquitablePartition.cellUniformVec
    by_cases hy : P.cells y = j
    · rw [if_pos hy, if_pos hy, G.szCoinAmp_conj]
      rw [szCoinAmp_magEquitable P hME (x := P.cellRep i) (y := y) (x' := P.cellRep i)
        (y' := P.cellRep j) rfl (hy.trans (P.cellRep_cells j ⟨yj, hyj.2⟩).symm)]
    · rw [if_neg hy, if_neg hy, mul_zero]
  rw [Finset.sum_congr rfl (fun y _ => hstep y)]
  -- `∑_y [cells y = j] · c = |C_j| · c`, then `|C_j|/√|C_j| = √|C_j|`.
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- `(filter (cells · = j)).card = cellCard j` (as a cast on ℂ).
  have hcard : ((Finset.univ.filter (fun w : V => P.cells w = j)).card : ℂ)
      = (P.cellCard j : ℂ) := by
    unfold EquitablePartition.cellCard; push_cast; rfl
  rw [hcard]
  -- `(|C_j| : ℂ) · (φ · (1/√|C_j|)) = √|C_j| · φ = ψ(i,j)`.
  unfold compressionCoinAmp
  have hsq : (Real.sqrt (P.cellCard j) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ)
      = (P.cellCard j : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (P.cellCard_nonneg j)]
  field_simp
  rw [← hsq]; ring

/-- **The Szegedy projector on a doubled generator, in `ψ` form.**  Under
magnitude-equitability, `Π ·ᵥ (e_i ⊗ e_j) = ∑_k (ψ(i,j)·ψ(i,k)) • (e_i ⊗ e_k)`,
where `ψ = compressionCoinAmp`.  This is `szReflectionProj_preserves_doubled`'s
internal formula with its scalar `t(r_i)` resolved to `ψ(i,j)` (via
`szReflectionProj_middleScalar`) and the coin row resolved via
`szCoinAmp_eq_cellUniform_combo`; the coefficient `c_{kij}` is exactly
`ψ(i,j)·ψ(i,k)`.  This is the genuine combinatorial engine of the
identification. -/
theorem szReflectionProj_mulVec_generator_eq [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) :
    (G.szReflectionProj).mulVec (P.doubledCellUniformVec i j)
      = ∑ k, (P.compressionCoinAmp i j * P.compressionCoinAmp i k) •
          P.doubledCellUniformVec i k := by
  classical
  -- Step 1: pointwise formula `(Π ·ᵥ ψ) p = (e_i)_{p.1} · t(p.1) · φ_{p.1}(p.2)`.
  set t : V → ℂ := fun x => ∑ y, (starRingEnd ℂ) (G.szCoinAmp x y) *
    P.cellUniformVec j y with ht
  have hPi0 : ∀ p : V × V,
      (G.szReflectionProj).mulVec (P.doubledCellUniformVec i j) p
        = P.cellUniformVec i p.1 * t p.1 * G.szCoinAmp p.1 p.2 := by
    intro p
    simp only [Matrix.mulVec, dotProduct, WeightedGraph.szReflectionProj,
      EquitablePartition.doubledCellUniformVec]
    rw [Fintype.sum_prod_type]
    have hcollapse : ∀ a : V, (∑ b : V,
          (if p.1 = a then G.szCoinAmp p.1 p.2 *
              (starRingEnd ℂ) (G.szCoinAmp p.1 b) else 0) *
            (P.cellUniformVec i a * P.cellUniformVec j b))
        = if p.1 = a then
            P.cellUniformVec i a * (G.szCoinAmp p.1 p.2 *
              ∑ b, (starRingEnd ℂ) (G.szCoinAmp p.1 b) * P.cellUniformVec j b)
          else 0 := by
      intro a
      by_cases ha : p.1 = a
      · simp only [if_pos ha, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b _; ring
      · simp only [if_neg ha, zero_mul, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl (fun a _ => hcollapse a)]
    rw [Finset.sum_ite_eq Finset.univ p.1
      (fun a => P.cellUniformVec i a * (G.szCoinAmp p.1 p.2 *
        ∑ b, (starRingEnd ℂ) (G.szCoinAmp p.1 b) * P.cellUniformVec j b))]
    rw [if_pos (Finset.mem_univ p.1)]
    show _ = P.cellUniformVec i p.1 * t p.1 * G.szCoinAmp p.1 p.2
    rw [ht]; ring
  -- Step 2: package as a sum of doubled generators with coefficient `ψ(i,j)·ψ(i,k)`.
  have hcombo := szCoinAmp_eq_cellUniform_combo P hME
  funext p
  rw [hPi0 p]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    EquitablePartition.doubledCellUniformVec]
  by_cases hpi : P.cells p.1 = i
  · -- on cell `i`: replace `t(p.1)` and `φ_{p.1}` by representative-`i` values.
    have hrepi : P.cells (P.cellRep i) = P.cells p.1 := by
      rw [P.cellRep_cells i ⟨p.1, hpi⟩, hpi]
    -- `t(p.1) = t(r_i) = ψ(i,j)`.
    have htp : t p.1 = P.compressionCoinAmp i j := by
      show (∑ y, (starRingEnd ℂ) (G.szCoinAmp p.1 y) * P.cellUniformVec j y)
        = P.compressionCoinAmp i j
      rw [show (∑ y, (starRingEnd ℂ) (G.szCoinAmp p.1 y) * P.cellUniformVec j y)
          = ∑ y, (starRingEnd ℂ) (G.szCoinAmp (P.cellRep i) y) * P.cellUniformVec j y from by
        apply Finset.sum_congr rfl; intro y _
        rw [szCoinAmp_magEquitable P hME (x := p.1) (y := y) hrepi.symm rfl]]
      exact szReflectionProj_middleScalar P hME hne i j
    -- `φ_{p.1}(p.2) = ∑_k ψ(i,k)·(e_k)_{p.2}` (coin row resolved at rep `i`).
    have hrow : G.szCoinAmp p.1 p.2
        = ∑ k, P.compressionCoinAmp i k * P.cellUniformVec k p.2 := by
      have := congrFun (hcombo p.1) p.2
      simp only at this
      rw [this]; apply Finset.sum_congr rfl; intro k _
      rw [show G.szCoinAmp p.1 (P.cellRep k)
          = G.szCoinAmp (P.cellRep i) (P.cellRep k) from
        szCoinAmp_magEquitable P hME (x := p.1) (y := P.cellRep k) hrepi.symm rfl]
      unfold compressionCoinAmp; ring
    rw [htp, hrow, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring
  · -- off cell `i`: `(e_i)_{p.1} = 0`, both sides vanish.
    have hei : P.cellUniformVec i p.1 = 0 := by
      simp only [EquitablePartition.cellUniformVec]; rw [if_neg hpi]
    rw [hei]
    simp only [zero_mul, mul_zero, Finset.sum_const_zero]

/-- **Projector compression** — the genuine content.  `(B⊗B)ᴴ · Π_V · (B⊗B)` is
the rank-one-per-tail-block matrix built from the *compression coin amplitudes*
`ψ`: its `((i',j'),(i,j))` entry is `[i' = i] · ψ(i,j') · ψ(i,j)`.  This is the
DTQW analogue, after compression, of the host Szegedy projector, with the
intrinsic coin amplitudes replaced by `ψ` (the lumped-chain amplitudes).  Proved
column-wise from `szReflectionProj_mulVec_generator_eq` + the isometry
collapse `(B⊗B)ᴴ (e_i ⊗ e_k) = e_{(i,k)}`. -/
theorem szReflectionProjQuotient [Nonempty V] (P : EquitablePartition G I)
    (hME : P.MagnitudeEquitable) (hne : ∀ k, P.cellCard k ≠ 0) :
    P.doubledCellEmbedᴴ * G.szReflectionProj * P.doubledCellEmbed
      = fun p q => if p.1 = q.1
          then P.compressionCoinAmp q.1 p.2 * P.compressionCoinAmp q.1 q.2 else 0 := by
  apply Matrix.ext_of_mulVec_single
  rintro ⟨i, j⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, doubledCellEmbed_mulVec_single,
    szReflectionProj_mulVec_generator_eq P hME hne i j]
  -- `(B⊗B)ᴴ ·ᵥ ∑_k coeff_k • (e_i ⊗ e_k) = ∑_k coeff_k • e_{(i,k)}`.
  rw [Matrix.mulVec_sum, Matrix.mulVec_single_one]
  simp only [Matrix.mulVec_smul, doubledCellEmbedH_mulVec_generator P hne]
  -- Read off entry `p`: column index is `(i,j)`, so RHS is `[p.1 = i]·ψ(i,p.2)·ψ(i,j)`.
  funext p
  rw [Matrix.col_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  -- Goal: `∑_x ψ(i,j)·ψ(i,x)·[p = (i,x)] = [p.1 = i]·ψ(i,p.2)·ψ(i,j)`.
  by_cases hpi : p.1 = i
  · -- the surviving term is `x = p.2`.
    rw [Finset.sum_eq_single p.2]
    · rw [if_pos (show p = (i, p.2) from Prod.ext hpi rfl), mul_one, if_pos hpi]
      ring
    · intro k _ hk
      rw [if_neg (fun h : p = (i, k) => hk (by rw [h])), mul_zero]
    · intro h; exact absurd (Finset.mem_univ p.2) h
  · -- `p.1 ≠ i`: every `(i,x) ≠ p`, so the whole sum is `0`; RHS `if` is `0` too.
    rw [if_neg hpi]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (fun h : p = (i, k) => hpi (by rw [h])), mul_zero]

/-- **Reflection compression** `(B⊗B)ᴴ · R_V · (B⊗B) = 2 • ψProj − 1`, where
`ψProj` is the compression of the projector (`szReflectionProjQuotient`).  Since
`R_V = 2 • Π_V − 1`, the compression distributes: `(B⊗B)ᴴ (2•Π − 1)(B⊗B) =
2•((B⊗B)ᴴ Π (B⊗B)) − (B⊗B)ᴴ(B⊗B) = 2•ψProj − 1` using the isometry. -/
theorem szReflectionQuotient (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) :
    P.doubledCellEmbedᴴ * G.szReflection * P.doubledCellEmbed
      = (2 : ℂ) • (P.doubledCellEmbedᴴ * G.szReflectionProj * P.doubledCellEmbed)
          - (1 : Matrix (I × I) (I × I) ℂ) := by
  unfold WeightedGraph.szReflection
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, doubledCellEmbed_conjTranspose_mul P hne]

/-- **The doubled range projector fixes `R_V · (B⊗B)`.**  Each column of
`R_V · (B⊗B)` is `R_V ·ᵥ (e_i ⊗ e_j)`, which lies in the doubled cell-uniform
subspace (`szReflection_preserves_doubled`), so the range projector
`(B⊗B)(B⊗B)ᴴ` fixes it (`doubledCellEmbed_projFix`).  This is what lets the
swap–reflection compression *factor* as a product of compressions. -/
theorem doubledCellEmbed_projFix_szReflection [Nonempty V] (P : EquitablePartition G I)
    (hME : P.MagnitudeEquitable) (hne : ∀ k, P.cellCard k ≠ 0) :
    P.doubledCellEmbed * P.doubledCellEmbedᴴ * (G.szReflection * P.doubledCellEmbed)
      = G.szReflection * P.doubledCellEmbed := by
  apply Matrix.ext_of_mulVec_single
  rintro ⟨i, j⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    doubledCellEmbed_mulVec_single]
  -- column `R_V ·ᵥ (e_i ⊗ e_j)` is in the subspace.
  have hmem : (G.szReflection).mulVec (P.doubledCellUniformVec i j)
      ∈ P.doubledCellUniformSubspace :=
    szReflection_preserves_doubled P hME _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  exact doubledCellEmbed_projFix P hne _ hmem

/-- **Factorization of the Szegedy compression** as swap-quotient times the
reflection compression: `szegedyQuotient = S_I · ((B⊗B)ᴴ R_V (B⊗B))`.  The
walk is `U_Sz = S_V R_V`; insert the range projector
`(B⊗B)(B⊗B)ᴴ = 1`-on-the-subspace between `S_V` and `R_V` (it fixes the columns
of `R_V·(B⊗B)`, `doubledCellEmbed_projFix_szReflection`), then compress the swap
factor (`szSwapQuotient`).  This is the honest content-free assembly: the deep
content is already in `szReflectionProjQuotient`. -/
theorem szegedyQuotient_factor [Nonempty V] (P : EquitablePartition G I)
    (hME : P.MagnitudeEquitable) (hne : ∀ k, P.cellCard k ≠ 0) :
    P.szegedyQuotient
      = WeightedGraph.szSwap I *
          (P.doubledCellEmbedᴴ * G.szReflection * P.doubledCellEmbed) := by
  unfold szegedyQuotient WeightedGraph.SzegedyWalk
  -- `(B⊗B)ᴴ (S_V R_V)(B⊗B) = (B⊗B)ᴴ S_V [(B⊗B)(B⊗B)ᴴ] R_V (B⊗B)`.
  calc P.doubledCellEmbedᴴ * (WeightedGraph.szSwap V * G.szReflection) * P.doubledCellEmbed
      = P.doubledCellEmbedᴴ * WeightedGraph.szSwap V *
          (P.doubledCellEmbed * P.doubledCellEmbedᴴ * (G.szReflection * P.doubledCellEmbed)) := by
        rw [doubledCellEmbed_projFix_szReflection P hME hne]
        simp only [Matrix.mul_assoc]
    _ = (P.doubledCellEmbedᴴ * WeightedGraph.szSwap V * P.doubledCellEmbed) *
          (P.doubledCellEmbedᴴ * (G.szReflection * P.doubledCellEmbed)) := by
        simp only [Matrix.mul_assoc]
    _ = WeightedGraph.szSwap I *
          (P.doubledCellEmbedᴴ * G.szReflection * P.doubledCellEmbed) := by
        rw [szSwapQuotient P hne]; simp only [Matrix.mul_assoc]

/-! ### The honest, gated identification.

The factorization `szegedyQuotient = S_I · (2 • ψProj − 1)` is now *proved*.  The
intrinsic quotient walk is `Q.SzegedyWalk = S_I · (2 • Q.szReflectionProj − 1)`.
So the identification holds **exactly when** the per-edge coin-amplitude identity
holds; we state that as the hypothesis and discharge the rest. -/

/-- **Identification with the intrinsic quotient Szegedy walk — honest, gated
form.**  IF the intrinsic quotient coin amplitudes `Q.szCoinAmp` agree with the
*compression coin amplitudes* `ψ = compressionCoinAmp` (the per-edge identity
`hcoin`), THEN the Szegedy compression equals the intrinsic quotient Szegedy walk.

This is the genuine theorem, reduced to a single scalar identity.  The
hypothesis `hcoin` is exactly the condition that the quotient walk is built from
the *lumped Markov chain* on cells (transition probability into cell `b`
proportional to the mass `|C_b|·‖A_{r_i r_b}‖`), which is what the compression
produces.  **It is NOT implied by `Q.adj = symmQuotient`** — see
`szReflectionProjQuotient` (the compression coin amplitude is
`√|C_b|·szCoinAmp(r_i,r_b)`, whose probability is the cell *mass*, whereas
`symmQuotient` carries an extra `1/√|C_b|` distortion). -/
theorem szegedyQuotient_eq_quotientWalk_of_coinAmp [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (Q : WeightedGraph I)
    (hcoin : ∀ i b : I, Q.szCoinAmp i b = P.compressionCoinAmp i b) :
    P.szegedyQuotient = Q.SzegedyWalk := by
  -- compression side: `szegedyQuotient = S_I · (2 • ψProj − 1)`.
  rw [szegedyQuotient_factor P hME hne, szReflectionQuotient P hne,
    szReflectionProjQuotient P hME hne]
  -- intrinsic side: `Q.SzegedyWalk = S_I · (2 • Q.Π − 1)`.
  unfold WeightedGraph.SzegedyWalk WeightedGraph.szReflection
  congr 1
  -- `2 • ψProj − 1 = 2 • Q.szReflectionProj − 1`, i.e. `ψProj = Q.szReflectionProj`.
  congr 1
  congr 1
  -- `ψProj = Q.szReflectionProj` entrywise, via `hcoin`.
  funext p q
  unfold WeightedGraph.szReflectionProj
  by_cases h : p.1 = q.1
  · rw [if_pos h, if_pos h, Q.szCoinAmp_conj, h, hcoin q.1 p.2, hcoin q.1 q.2]
  · rw [if_neg h, if_neg h]

/-- **The originally-stated `symmQuotient`-gated identity is FALSE** (honest
record; not provable, and we do not pretend otherwise).

For the would-be statement `(∀ i j, i ≠ j → Q.adj i j = symmQuotient i j) →
szegedyQuotient = Q.SzegedyWalk` to hold one needs (by `szegedyQuotient_factor`
+ `szReflectionProjQuotient`) the per-edge identity `Q.szCoinAmp i b =
compressionCoinAmp i b`, i.e. `‖Q.adj i b‖` proportional (per row) to the cell
mass `|C_b|·‖A_{r_i r_b}‖`.  But `‖symmQuotient i b‖ = √|C_i|·√|C_b|·‖A_{r_i r_b}‖`
in the real-nonnegative case, carrying an extra `1/√|C_b|` distortion relative to
the mass `|C_b|·‖A_{r_i r_b}‖`.  These differ whenever a single tail cell reaches
two cells of unequal size.

**Smallest concrete witness.**  `V = {0,1,2,3}`, `A = ` adjacency of the star
`K_{1,3}` (center `0`, leaves `1,2,3`, unit weights, real-nonnegative).
Partition `cells = (0,1,2,2)`: cells `{0}`, `{1}`, `{2,3}` of sizes `1, 1, 2`.
This is magnitude-equitable.  From tail cell `0` the compression coin amplitudes
are `ψ(0,1) = 1/√3 ≈ 0.5774`, `ψ(0,2) = √(2/3) ≈ 0.8165`; the `symmQuotient`-built
intrinsic coin amplitudes are `Q.szCoinAmp 0 1 ≈ 0.6436`, `Q.szCoinAmp 0 2 ≈
0.7654`.  Since `ψ(0,1) ≠ Q.szCoinAmp 0 1`, the `((0,1),(0,1))` diagonal entry of
`ψProj` differs from that of `Q.szReflectionProj` (`ψ(0,1)² ≈ 0.333` vs `≈
0.414`), so `szegedyQuotient ≠ Q.SzegedyWalk` for this `Q`.  (Conversely the same
amplitudes `ψ` match the walk of the *raw branching quotient* `P.quotient` edge
for edge.)

This is recorded as a comment-bearing `True` (no false `Prop` is asserted); the
real, provable identification is `szegedyQuotient_eq_quotientWalk_of_coinAmp`. -/
theorem szegedyQuotient_ne_symmQuotientWalk_counterexample : True := trivial

end EquitablePartition

end Graphplay
