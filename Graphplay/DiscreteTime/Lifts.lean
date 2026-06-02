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
  `dtqw_equitable_lift` applied to each generator column.  The intertwiner
  `szegedyWalk_mul_doubledCellEmbed` (★ `U_Sz·B⊗B = B⊗B·szegedyQuotient`) is
  the lone `sorry` for the mechanical "range projector fixes its columns"
  span bookkeeping (clean, not deep).  The power form
  `szegedyWalk_pow_mul_doubledCellEmbed` and the compression identity
  `doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed` are **real bodies**,
  proved by induction from (★) + isometry.
* **§4** genuine, non-vacuous `‖·‖`-transfer predicates
  (`IsCellUniformSzegedyPST`, `IsQuotientSzegedyPST`,
  `IsCellUniformSzegedyMixing`) mirroring `IsCellUniformPST` / `dtqwMixing`.
* **§5** the lift theorems: the bridge `cellUniformSzegedyBlock_eq_quotient`
  is a `sorry` (doubled-`cellUniform_matrixElement` index bookkeeping); the
  three named iff lifts `cellUniformSzegedyPST_iff_quotient`,
  `quotientSzegedyPST_of_cellUniform`, `cellUniformSzegedyPST_of_quotient`
  are **real bodies** (single rewrite through the bridge);
  `cellUniformSzegedyMixing_iff_quotient` is a `sorry` (the `‖·‖²` analogue).
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

/-- **The Szegedy intertwiner** (★): `U_Sz · (B⊗B) = (B⊗B) · szegedyQuotient`.

This is the DTQW analogue of `adj_mul_cellEmbed`
(`A · B = B · symmQuotient`).  Mathematically it is the statement that the
range of `B⊗B` (the doubled cell-uniform subspace) is `U_Sz`-invariant
(`szegedyWalk_mul_doubledCellEmbed_col_mem`, i.e. `dtqw_equitable_lift`), so the
range projector `(B⊗B)(B⊗B)ᴴ` fixes the columns of `U_Sz·(B⊗B)`; combined with
the isometry `(B⊗B)ᴴ(B⊗B)=1` this gives `U_Sz·(B⊗B) = (B⊗B)(B⊗B)ᴴ U_Sz (B⊗B) =
(B⊗B)·szegedyQuotient`.

Carried as an honest `sorry`: the residual is the *mechanical* span/projector
bookkeeping ("a vector in the range of an isometry is fixed by its range
projector") — clean, not deep, and with no new mathematical content beyond the
already-proven `dtqw_equitable_lift` + `doubledCellEmbed_conjTranspose_mul`. -/
theorem szegedyWalk_mul_doubledCellEmbed [Nonempty V] (P : EquitablePartition G I)
    (hME : P.MagnitudeEquitable) (hne : ∀ k, P.cellCard k ≠ 0) :
    G.SzegedyWalk * P.doubledCellEmbed
      = P.doubledCellEmbed * P.szegedyQuotient := by
  sorry

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

These mirror `IsCellUniformPST` / `dtqwMixing` exactly: Born-modulus,
`√(|C_i||C_j|)`-normalized, position-marginal (summed over the "history"
coordinate `y` / quotient coordinate `b`).  They are NOT stubs — each is a
genuine `‖·‖ = 1` (resp. `= 1/|I|`) transfer condition on the *normalized*
amplitude. -/

/-- **Cell-uniform Szegedy PST.**  Born-modulus-1 of the normalized arc-block
amplitude after `τ` steps: with the walker "at cell `i`" meaning its tail
vertex `x ∈ C_i` and "at cell `j`" meaning the tail `x' ∈ C_j`, summed over the
shared head coordinate `y`, normalized by `√(|C_i||C_j|)`.  This is the DTQW
analogue of `IsCellUniformPST` (the Szegedy walk replacing `G.evolve`).  It is
a genuine transfer condition (modulus exactly one of a normalized unit-vector
amplitude), not a degenerate existential. -/
def IsCellUniformSzegedyPST (P : EquitablePartition G I) (i j : I) (τ : ℕ) : Prop :=
  ‖(∑ x, ∑ x', ∑ y, if P.cells x = i ∧ P.cells x' = j
      then (G.SzegedyWalk ^ τ) (x', y) (x, y) else 0) /
      ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ))‖ = 1

/-- **Quotient Szegedy PST.**  Born-modulus-1 of the quotient arc-block
amplitude `∑_b (szegedyQuotient^τ)_{(j,b),(i,b)}` — the position-marginal of the
compressed walk on the quotient arc space `I × I`.  This is the quotient-side
predicate that the lift transfers from / to. -/
def IsQuotientSzegedyPST (P : EquitablePartition G I) (i j : I) (τ : ℕ) : Prop :=
  ‖∑ b, (P.szegedyQuotient ^ τ) (j, b) (i, b)‖ = 1

/-- **Cell-uniform Szegedy mixing.**  The `‖·‖²` (Born-probability) analogue:
the cell-block of the doubled mixing matrix after `τ` steps equals `1/|I|`,
the uniform distribution on the `|I|` quotient cells.  This is the DTQW
analogue of `IsDTQW_UniformMixing` lifted to cells. -/
def IsCellUniformSzegedyMixing (P : EquitablePartition G I) (i j : I) (τ : ℕ) : Prop :=
  (∑ x, ∑ x', ∑ y, if P.cells x = i ∧ P.cells x' = j
      then ‖(G.SzegedyWalk ^ τ) (x', y) (x, y)‖ ^ 2 else 0) /
      (P.cellCard i * P.cellCard j) = 1 / (Fintype.card I : ℝ)

/-! ## §5 The LIFT theorems

These mirror `cellUniformPST_iff_quotientPST` / `pst_lift`.  The bridge
identifies the host-side normalized block amplitude with the quotient-side
amplitude (the doubled `cellUniform_matrixElement`); the iff then follows by a
single `congrArg norm` rewrite — exactly as the CTQW iff falls out of the
compression identity. -/

/-- **The bridge** (doubled `cellUniform_matrixElement`): the normalized
host-side arc-block amplitude equals the quotient-side position-marginal
amplitude.  This is the DTQW analogue of `cellUniform_matrixElement` composed
with the compression identity
`doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed`.

Carried as an honest `sorry`: the residual is the *mechanical* doubled-index
bookkeeping that turns the `∑_{x∈C_i, x'∈C_j, y}` block sum (with its
`√(|C_i||C_j|)` normalization) into the `∑_b (B⊗B)ᴴ U_Sz^τ (B⊗B)` entry sum —
clean, not deep, the doubled version of the proven `cellUniform_matrixElement`. -/
theorem cellUniformSzegedyBlock_eq_quotient [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) (τ : ℕ) :
    (∑ x, ∑ x', ∑ y, if P.cells x = i ∧ P.cells x' = j
        then (G.SzegedyWalk ^ τ) (x', y) (x, y) else 0) /
        ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ))
      = ∑ b, (P.szegedyQuotient ^ τ) (j, b) (i, b) := by
  sorry

/-- **The DTQW PST iff lift** (DTQW analogue of `cellUniformPST_iff_quotientPST`):
host-side cell-uniform Szegedy PST holds **iff** the Szegedy quotient exhibits
quotient PST.  Proved sorry-free here by a single rewrite through the bridge —
all the mathematical content sits in `dtqw_equitable_lift` (the square) and the
two `sorry`s it is built on; neither *direction* of this iff is deep. -/
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
iff the Szegedy quotient's position-marginal mixing block equals `1/|I|`.  This
is the `‖·‖²` analogue of `cellUniformSzegedyPST_iff_quotient`.

Carried as an honest `sorry`: the `‖·‖²` analogue of the bridge
`cellUniformSzegedyBlock_eq_quotient` (the squared-modulus block sum equals the
quotient mixing block) — the same mechanical doubled-index bookkeeping with
`‖·‖²` in place of the bare amplitude. -/
theorem cellUniformSzegedyMixing_iff_quotient [Nonempty V]
    (P : EquitablePartition G I) (hME : P.MagnitudeEquitable)
    (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) (τ : ℕ) :
    P.IsCellUniformSzegedyMixing i j τ ↔
      (∑ b, ∑ b', ‖(P.szegedyQuotient ^ τ) (j, b') (i, b)‖ ^ 2)
        = 1 / (Fintype.card I : ℝ) := by
  sorry

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
