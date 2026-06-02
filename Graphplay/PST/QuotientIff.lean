/-
# Graphplay.PST.QuotientIff

**Round-3 loop-closer for the Bachman–Tamon quotient PST characterization.**

`Graphplay/PST.lean` currently states only the *forward* direction of the
Bachman–Tamon characterization (arXiv:1108.0339, "Perfect state transfer on
quotient graphs", Theorem 3 / discrete-time; here we treat the continuous-time
analogue used by Coutinho–Godsil and folklore): namely
`EquitablePartition.pst_lift`, which says that PST on the quotient implies
cell-uniform PST on the host.

The Bachman–Tamon result is in fact an **iff**: cell-uniform PST on the host
between cells `i` and `j` at time `τ` is *equivalent* to PST on the quotient
between cells `i` and `j` at the same time `τ`, *provided* the cell-uniform
subspace is invariant under the host evolution.  Equitability of the partition
provides exactly that invariance hypothesis (combinatorial backbone:
`EquitablePartition.adj_mulVec_cellUniformVec`).

In this file we:

1. **Recall** the forward direction (`EquitablePartition.pst_lift`) as the
   reference theorem, cited from `Graphplay/PST.lean`.
2. **Define** `NoCellUniformLeakage`: the (semantic) statement that the host
   evolution preserves the cell-uniform subspace.  Spectrally this is equivalent
   to the cell-uniform subspace being `G.adj`-invariant, which in turn is
   equivalent to `P` being an equitable partition.  We package the equivalence
   as `cellUniform_invariant_iff_equitable`.
3. **State the reverse implication** as `cellUniformPST_iff_quotientPST`,
   completing the Bachman–Tamon iff.
4. **Reformulate** the iff in terms of *strong cospectrality* (interface to
   sibling `Graphplay.PST.Cospectrality`): cell-uniform states `|C_i⟩, |C_j⟩`
   are automatically strongly cospectral when `P` is equitable.
5. **Phantom symmetry corollary**: a cell-uniform pair can admit PST without
   any host-graph automorphism swapping the cells.  This is Bachman–Tamon's
   main qualitative observation and the conceptual reason quotient PST is
   strictly more powerful than symmetry-based PST.
6. **Chiral / signed extension**: combine with
   `WeightedGraph.signedBy_preserves_equitable` from `Graphplay.Chiral` to lift
   the iff to chirally-signed bundles whose signing is *cross-constant* on
   cells.

Sibling modules (assumed to compile against this file):

* `Graphplay.PST.Cospectrality`  — provides `IsStronglyCospectral` and the
  spectral-projector reformulation.
* `Graphplay.PST.GodsilRatio`    — provides the eigenvalue support /
  Godsil-ratio numerical-witness machinery used (downstream) to reduce
  PST to an arithmetic condition on the quotient spectrum.

This module is `sorry`-free: the quotient-PST iff, its strong-cospectrality
reformulation, and the phantom-symmetry existence corollary are all fully
proven (the latter via the explicit `BachmanTamonWitness` `P_3` example).  It
closes the Round-3 loop on the quotient-PST iff and connects it to the
cospectrality and signed-bundle infrastructure.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Lagrange
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Spectral
import Graphplay.PST
import Graphplay.Chiral
-- Sibling Round-3 modules (assumed APIs):
import Graphplay.PST.Cospectrality
import Graphplay.PST.GodsilRatio

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay
namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-! ## 0. Span-membership helpers for the invariance↔equitability backbone. -/

/-- The (un-normalized) cell indicator for a bare cell map `cells : V → I`. -/
private def rawInd (cells : V → I) (i : I) : V → ℂ :=
  fun x => if cells x = i then 1 else 0

/-- The (normalized) cell generator appearing in
`cellUniform_invariant_iff_equitable`. -/
private noncomputable def normGen (cells : V → I) (i : I) : V → ℂ :=
  fun x =>
    if cells x = i
      then (1 : ℂ) /
            ((Real.sqrt
              ((Finset.univ.filter (fun w : V => cells w = i)).card : ℝ) : ℝ) : ℂ)
      else 0

/-- The span of the normalized generators equals the span of the raw cell
indicators: on a nonempty cell the normalized generator is a nonzero scalar
multiple of the raw indicator, and on an empty cell both vanish. -/
private theorem span_normGen_eq_span_rawInd (cells : V → I) :
    Submodule.span ℂ (Set.range (normGen (V := V) cells))
      = Submodule.span ℂ (Set.range (rawInd (V := V) cells)) := by
  apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨i, rfl⟩
  · -- `normGen i = c • rawInd i` for the scalar `c = 1/√|C_i|`.
    have : normGen (V := V) cells i
        = ((1 : ℂ) /
            ((Real.sqrt ((Finset.univ.filter (fun w : V => cells w = i)).card : ℝ) : ℝ) : ℂ))
          • rawInd (V := V) cells i := by
      funext x; simp only [normGen, rawInd, Pi.smul_apply, smul_eq_mul]
      by_cases hx : cells x = i <;> simp [hx]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · -- conversely `rawInd i = √|C_i| • normGen i` (and both are `0` when empty).
    by_cases hcard : (Finset.univ.filter (fun w : V => cells w = i)).card = 0
    · -- empty cell: `rawInd i = 0`.
      have hzero : rawInd (V := V) cells i = 0 := by
        funext x; simp only [rawInd, Pi.zero_apply]
        rw [if_neg]
        intro hx
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
        exact hcard (Finset.mem_univ x) hx
      rw [hzero]; exact Submodule.zero_mem _
    · have heq : rawInd (V := V) cells i
          = ((Real.sqrt ((Finset.univ.filter (fun w : V => cells w = i)).card : ℝ) : ℝ) : ℂ)
            • normGen (V := V) cells i := by
        have hpos : (0 : ℝ) < ((Finset.univ.filter (fun w : V => cells w = i)).card : ℝ) := by
          rw [Nat.cast_pos]; exact Nat.pos_of_ne_zero hcard
        have hsq : ((Real.sqrt ((Finset.univ.filter (fun w : V => cells w = i)).card : ℝ) : ℝ) : ℂ) ≠ 0 := by
          rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (Real.sqrt_pos.mpr hpos)
        funext x; simp only [normGen, rawInd, Pi.smul_apply, smul_eq_mul]
        by_cases hx : cells x = i
        · simp only [if_pos hx, mul_one_div, div_self hsq]
        · simp only [if_neg hx, mul_zero]
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Membership criterion for the raw-indicator span: a vector lies in the span
of the cell indicators iff it is **constant on each cell**. -/
private theorem mem_span_rawInd_iff (cells : V → I) (v : V → ℂ) :
    v ∈ Submodule.span ℂ (Set.range (rawInd (V := V) cells))
      ↔ ∀ x y : V, cells x = cells y → v x = v y := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      intro x y hxy; simp only [rawInd]; rw [hxy]
    | zero => intro x y _; rfl
    | add a b _ _ ha hb => intro x y hxy; simp only [Pi.add_apply]; rw [ha x y hxy, hb x y hxy]
    | smul c a _ ha => intro x y hxy; simp only [Pi.smul_apply, smul_eq_mul]; rw [ha x y hxy]
  · intro hconst
    -- `v = ∑ i, (v's value on cell i) • rawInd i`, hence in the span.
    classical
    have hrep : v = ∑ i : I, (if h : ∃ x, cells x = i then v h.choose else 0)
        • rawInd (V := V) cells i := by
      funext x
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single (cells x)]
      · have hex : ∃ z, cells z = cells x := ⟨x, rfl⟩
        rw [dif_pos hex, Pi.smul_apply, smul_eq_mul]
        simp only [rawInd, if_true, mul_one, eq_self_iff_true]
        exact hconst _ _ hex.choose_spec.symm
      · intro i _ hi
        rw [Pi.smul_apply, smul_eq_mul]
        simp only [rawInd, if_neg (fun (h : cells x = i) => hi h.symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hrep]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-! ## 1. Recalling the forward direction.

The forward direction of the Bachman–Tamon iff lives in `Graphplay/PST.lean`
as `EquitablePartition.pst_lift`.  We re-export it here under a longer name
that makes the directionality explicit, to pair with the new reverse
implication. -/

/-- **Forward direction (recalled).**  PST on the quotient implies cell-uniform
PST on the host.  This is exactly `EquitablePartition.pst_lift` from
`Graphplay/PST.lean`; recorded here under a name that pairs with the new
`quotientPST_of_cellUniformPST` (the reverse direction).

Bachman–Tamon, arXiv:1108.0339, Theorem 3, "⇐" direction (in their notation
the quotient PST condition is on the *right*; we follow the convention of
Coutinho–Godsil "Perfect State Transfer in Graphs"). -/
theorem cellUniformPST_of_quotientPST
    (P : EquitablePartition G I) {i j : I} {τ : ℝ}
    (hne : ∀ k, P.cellCard k ≠ 0)
    (hquot : ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)) j i‖ = 1) :
    IsCellUniformPST G P i j τ :=
  EquitablePartition.pst_lift (P := P) (i := i) (j := j) (τ := τ) hne hquot

/-! ## 2. The no-leakage condition. -/

/-- **No cell-uniform leakage.**  The host evolution `G.evolve τ` keeps every
cell-uniform initial state inside the cell-uniform subspace.

Semantically this is the statement that the cell-uniform subspace is an
invariant subspace for `exp(-i τ G.adj)`; equivalently, an invariant subspace
for `G.adj` (since `exp` and the matrix it exponentiates share invariant
subspaces).  For an equitable partition this is automatic; the predicate is
recorded as a `Prop` so we can speak of it directly in the iff. -/
def NoCellUniformLeakage (G : WeightedGraph V) (P : EquitablePartition G I) :
    Prop :=
  ∀ (τ : ℝ) (v : V → ℂ), v ∈ P.cellUniformSubspace →
    (G.evolve τ).mulVec v ∈ P.cellUniformSubspace

/-! ## 3. The cell-uniform-invariance ↔ equitability backbone. -/

/-- **Algebraic backbone (statement).**  The cell-uniform subspace
`P.cellUniformSubspace` is `G.adj`-invariant *iff* `P` is an equitable
partition of `G`.

The "⇐" direction is `cellUniformSubspace_invariant` in
`Graphplay/Equitable.lean`.  The "⇒" direction is the converse: if the
cell-uniform subspace happens to be `G.adj`-invariant for some cell map
`cells : V → I`, then the cell map satisfies the equitable / branching
condition.  Reason: applying `G.adj` to the (normalized) cell indicator
`1_{C_i} / √|C_i|` produces a vector whose entry at `x ∈ C_i` is
`(1/√|C_i|) · b_{ji}(x)` where `b_{ji}` is the branching number; for the
result to lie in the cell-uniform subspace, that entry must depend only on
`P.cells x`, which is the equitability condition.

(Statement-only here; the proof needs `Submodule.span_induction` plus a
linear-algebra disentangling of the branching coefficients.)

This lemma is the *algebraic* reason the Bachman–Tamon iff holds: the
forward and reverse directions are both manifestations of the cell-uniform
subspace being invariant. -/
theorem cellUniform_invariant_iff_equitable
    (cells : V → I) :
    (∃ P : EquitablePartition G I, P.cells = cells) ↔
      (∀ v : V → ℂ,
        v ∈ (Submodule.span ℂ
              (Set.range (fun i : I =>
                fun x : V =>
                  if cells x = i
                    then (1 : ℂ) /
                          ((Real.sqrt
                            ((Finset.univ.filter
                              (fun w : V => cells w = i)).card : ℝ) : ℝ) : ℂ)
                    else 0))) →
        G.adj.mulVec v ∈ (Submodule.span ℂ
              (Set.range (fun i : I =>
                fun x : V =>
                  if cells x = i
                    then (1 : ℂ) /
                          ((Real.sqrt
                            ((Finset.univ.filter
                              (fun w : V => cells w = i)).card : ℝ) : ℝ) : ℂ)
                    else 0)))) := by
  -- The generator family is exactly `normGen cells`; rewrite the span and use
  -- the constant-on-cells membership criterion throughout.
  have hgen : (fun i : I => fun x : V =>
      if cells x = i
        then (1 : ℂ) /
              ((Real.sqrt ((Finset.univ.filter (fun w : V => cells w = i)).card : ℝ) : ℝ) : ℂ)
        else 0) = normGen (V := V) cells := rfl
  rw [hgen]
  -- Reduce all span-membership to the constant-on-cells criterion.
  simp only [span_normGen_eq_span_rawInd, mem_span_rawInd_iff]
  constructor
  · -- "⇒": from an equitable partition, invariance is `restrict_eq_symmQuotient`
    -- read off pointwise.  Here we argue directly: `(G.adj *ᵥ v) x` depends only
    -- on `cells x` when `v` is constant on cells and `P` is equitable.
    rintro ⟨P, rfl⟩ v hvconst x y hxy
    -- `(G.adj *ᵥ v) x = ∑_z A x z * v z`; group `z` by cell.
    -- Using equitability of `P` and constancy of `v`.
    show G.adj.mulVec v x = G.adj.mulVec v y
    -- Rewrite each side as a sum over cells of `(branching into cell · value on cell)`.
    classical
    have key : ∀ w : V, G.adj.mulVec v w
        = ∑ i : I, P.branching i w * (if h : ∃ z, P.cells z = i then v h.choose else 0) := by
      intro w
      -- Work from the RHS: expand `branching`, swap sums, collapse over the cell.
      simp only [EquitablePartition.branching, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro z _
      -- Inner sum over `i` collapses to `i = cells z`.
      rw [Finset.sum_eq_single (P.cells z)]
      · rw [if_pos rfl]
        have hex : ∃ u, P.cells u = P.cells z := ⟨z, rfl⟩
        rw [dif_pos hex]
        have hvz : v z = v hex.choose := hvconst z hex.choose hex.choose_spec.symm
        rw [hvz]
      · intro i _ hi
        rw [if_neg (fun h => hi h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [key x, key y]
    apply Finset.sum_congr rfl
    intro i _
    rw [P.branching_eq (P.cells x) i x y rfl hxy.symm]
  · -- "⇐": invariance of constant-on-cells functions yields the equitable
    -- partition.  Apply the hypothesis to the raw indicator of a cell.
    intro hinv
    refine ⟨⟨cells, ?_⟩, rfl⟩
    -- The uniform / branching condition: for `x, y` in cell `i`, branching into
    -- `j` agrees.  Apply `hinv` to `v = rawInd cells j` (constant on cells), then
    -- read `(G.adj *ᵥ rawInd j) x = ∑_{z : cells z = j} A x z = branching x→j`.
    intro i j x y hx hy
    have hvconst : ∀ a b : V, cells a = cells b → rawInd (V := V) cells j a = rawInd (V := V) cells j b := by
      intro a b hab; simp only [rawInd]; rw [hab]
    have hAv := hinv (rawInd (V := V) cells j) hvconst x y (by rw [hx, hy])
    -- Unfold `(G.adj *ᵥ rawInd j) x = ∑ z, A x z * (if cells z = j then 1 else 0)`.
    have hexp : ∀ w : V, G.adj.mulVec (rawInd (V := V) cells j) w
        = ∑ z, (if cells z = j then G.adj w z else 0) := by
      intro w
      simp only [Matrix.mulVec, dotProduct, rawInd]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : cells z = j <;> simp [hz]
    rw [hexp x, hexp y] at hAv
    exact hAv

/-- **Equitability ⇒ no leakage.**  If `P` is equitable, the evolution
`G.evolve τ` preserves the cell-uniform subspace, hence the
`NoCellUniformLeakage` predicate holds.  This is the matrix-exponential
upgrade of `cellUniformSubspace_invariant`: invariance under `A` propagates
to invariance under every analytic function of `A`, in particular
`exp(-i τ A)`. -/
theorem noLeakage_of_equitable (P : EquitablePartition G I) :
    NoCellUniformLeakage G P := by
  intro τ v hv
  -- `cellUniformSubspace = span ℂ (range cellUniformVec)`.  Work by span
  -- induction on `v`; on a generator `cellUniformVec i = B *ᵥ (Pi.single i 1)`,
  -- the exponential intertwining `evolve τ * B = B * exp(s • Q̃)` shows
  -- `(evolve τ) *ᵥ (B *ᵥ w) = B *ᵥ (exp(s • Q̃) *ᵥ w)`, which is a cell-uniform
  -- combination — hence back in the subspace.
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  have hev : G.evolve τ = NormedSpace.exp (s • G.adj) := rfl
  -- The exponential intertwining at this `s`.
  have hEB : G.evolve τ * P.cellEmbed
      = P.cellEmbed * NormedSpace.exp (s • P.symmQuotient) := by
    rw [hev]; exact P.exp_smul_adj_mul_cellEmbed s
  -- For any quotient-side `w`, `(evolve τ) *ᵥ (B *ᵥ w)` lands in the subspace.
  have key : ∀ w : I → ℂ,
      (G.evolve τ).mulVec (P.cellEmbed.mulVec w) ∈ P.cellUniformSubspace := by
    intro w
    rw [Matrix.mulVec_mulVec, hEB, ← Matrix.mulVec_mulVec, P.cellEmbed_mulVec]
    -- The result is `∑ i, (exp(s•Q̃) *ᵥ w) i • cellUniformVec i`, in the span.
    rw [show (fun v => ∑ i,
            (NormedSpace.exp (s • P.symmQuotient)).mulVec w i * P.cellUniformVec i v)
          = ∑ i, (NormedSpace.exp (s • P.symmQuotient)).mulVec w i
                  • P.cellUniformVec i by
      funext v; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  -- Span induction: every `v ∈ cellUniformSubspace` is closed under `evolve τ`.
  refine Submodule.span_induction
    (p := fun v _ => (G.evolve τ).mulVec v ∈ P.cellUniformSubspace) ?_ ?_ ?_ ?_ hv
  · rintro x ⟨i, rfl⟩
    -- `cellUniformVec i = B *ᵥ (Pi.single i 1)`.
    have : P.cellUniformVec i = P.cellEmbed.mulVec (Pi.single i 1) := by
      rw [P.cellEmbed_mulVec]
      funext v
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, one_mul]
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [this]; exact key _
  · simpa using Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

/-! ## 4. The reverse implication and the full iff. -/

/-- **Reverse direction (Bachman–Tamon "⇒").**  Cell-uniform PST on the host
implies PST on the quotient.  This is the direction missing from
`Graphplay/PST.lean`. -/
theorem quotientPST_of_cellUniformPST
    (P : EquitablePartition G I) {i j : I} {τ : ℝ}
    (hne : ∀ k, P.cellCard k ≠ 0)
    (hhost : IsCellUniformPST G P i j τ) :
    -- PST on the (symmetric) quotient: the `(j,i)` entry of
    -- `exp(-i τ · P.symmQuotient)` has Born-rule modulus 1 — matching the
    -- `pst_lift` convention (`Bᴴ·evolve·B = exp(-iτ Q̃)`, entry `j i`).
    ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)) j i‖ = 1 := by
  -- Mirror of `pst_lift`, run in reverse.  The cell-uniform matrix element of
  -- `G.evolve τ` equals `(Bᴴ · evolve τ · B) j i = exp(s • Q̃) j i` via
  -- `cellUniform_matrixElement` and the exponential intertwining; the host PST
  -- hypothesis `IsCellUniformPST` says that quantity has modulus 1.
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  have hev : G.evolve τ = NormedSpace.exp (s • G.adj) := rfl
  have hEB : G.evolve τ * P.cellEmbed
      = P.cellEmbed * NormedSpace.exp (s • P.symmQuotient) := by
    rw [hev]; exact P.exp_smul_adj_mul_cellEmbed s
  have hBEB : P.cellEmbedᴴ * G.evolve τ * P.cellEmbed
      = NormedSpace.exp (s • P.symmQuotient) := by
    rw [Matrix.mul_assoc, hEB, ← Matrix.mul_assoc,
      P.cellEmbed_conjTranspose_mul_cellEmbed hne, Matrix.one_mul]
  -- Unfold the host hypothesis and rewrite via the matrix-element identity.
  unfold IsCellUniformPST at hhost
  rw [P.cellUniform_matrixElement (G.evolve τ) i j, hBEB,
    show s • P.symmQuotient = -(Complex.I * (τ : ℂ)) • P.symmQuotient from rfl] at hhost
  exact hhost

/-- **The full Bachman–Tamon iff.**  For any equitable partition `P` and any
pair of cells `i, j` and time `τ`, cell-uniform PST on `G` between `|C_i⟩`
and `|C_j⟩` is equivalent to PST on the quotient graph between `i` and `j`.

This is the continuous-time avatar of Bachman–Tamon arXiv:1108.0339,
Theorem 3, both directions.  The hypothesis "PST on the quotient" is the
Born-rule modulus condition on the quotient adjacency matrix's evolution. -/
theorem cellUniformPST_iff_quotientPST
    (P : EquitablePartition G I) (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) (τ : ℝ) :
    IsCellUniformPST G P i j τ ↔
      ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)) j i‖ = 1 := by
  refine ⟨?_, ?_⟩
  · intro hhost
    exact P.quotientPST_of_cellUniformPST (i := i) (j := j) (τ := τ) hne hhost
  · intro hquot
    exact P.cellUniformPST_of_quotientPST (i := i) (j := j) (τ := τ) hne hquot

/-! ## 5. Strong-cospectrality reformulation.

Sibling module `Graphplay.PST.Cospectrality` (agent L1) provides the predicate
`IsStronglyCospectral G u v` meaning that the spectral projectors of `G.adj`
satisfy `E_λ u = ±E_λ v` for every eigenvalue `λ` (and `u, v` have the same
spectral support).  By Coutinho–Godsil, PST between `u` and `v` *requires*
strong cospectrality.

The Bachman–Tamon iff has a clean cospectrality reformulation: cell-uniform
states `|C_i⟩, |C_j⟩` in the host are **automatically** strongly cospectral
when `P` is equitable, because both vectors live in the cell-uniform
subspace, and the restriction of `G.adj` to that subspace has the same
spectrum as `P.quotient`.  Strong cospectrality of `|C_i⟩, |C_j⟩` in the host
is therefore equivalent to strong cospectrality of `e_i, e_j` in `P.quotient`.
-/

/-! ### Keystone spectral-projector transport machinery (ported, axiom-clean).

The following block builds the eigenbasis-transport keystone
`stronglyCospectral_iff` from scratch: host spectral projector `hostProj`,
quotient projector `quotProj`, the polynomial functional-calculus transport
`Bᴴ · hostProj · B = quotProj` (via Lagrange interpolation + Mathlib's matrix
Hermitian `cfc`), and the cross/diagonal bridges to the spelled-out
strong-cospectrality predicates.  Cells must be nonempty (`hne`) for the
cell-embedding `B` to be an isometry; this is the same hypothesis the rest of
the PST cluster carries.
-/

/-- Host spectral projector onto the `lam`-eigenspace of `G.herm`. -/
noncomputable def hostProj (G : WeightedGraph V) (lam : ℝ) : Matrix V V ℂ :=
  fun y x => ∑ k, if G.herm.eigenvalues k = lam
    then G.herm.eigenvectorBasis k y * star (G.herm.eigenvectorBasis k x) else 0

/-- Quotient spectral projector onto the `lam`-eigenspace of `symmQuotient`. -/
noncomputable def quotProj (P : EquitablePartition G I) (lam : ℝ) : Matrix I I ℂ :=
  fun b a => ∑ k, if P.symmQuotient_isHermitian.eigenvalues k = lam
    then P.symmQuotient_isHermitian.eigenvectorBasis k b
      * star (P.symmQuotient_isHermitian.eigenvectorBasis k a) else 0

-- STEP 1: Bᴴ * A^n * B = Q̃^n.
theorem cellEmbedH_adj_pow_cellEmbed (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (n : ℕ) :
    P.cellEmbedᴴ * G.adj ^ n * P.cellEmbed = P.symmQuotient ^ n := by
  have hAB : G.adj ^ n * P.cellEmbed = P.cellEmbed * P.symmQuotient ^ n := by
    induction n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ, Matrix.mul_assoc, P.adj_mul_cellEmbed,
        ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  rw [Matrix.mul_assoc, hAB, ← Matrix.mul_assoc,
    P.cellEmbed_conjTranspose_mul_cellEmbed hne, Matrix.one_mul]

-- STEP 2: hostProj = cfc of the indicator.  Generic version for any Hermitian.
theorem cfc_indicator_eq_proj {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (lam : ℝ) :
    hA.cfc (fun μ => if μ = lam then (1 : ℝ) else 0)
      = fun y x => ∑ k, if hA.eigenvalues k = lam
          then hA.eigenvectorBasis k y * star (hA.eigenvectorBasis k x) else 0 := by
  rw [Matrix.IsHermitian.cfc]
  funext y x
  rw [Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_apply]
  -- (diagonal d * star U) a x = ∑ b, diagonal d a b * (star U) b x = d a * star(U x a)
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.diagonal_apply_eq, Function.comp_apply]
    -- U y a = eigenvectorBasis a y ; star U a x = star (U x a) = star (eigenvectorBasis a x)
    rw [Matrix.IsHermitian.eigenvectorUnitary_apply,
      show (star (hA.eigenvectorUnitary : Matrix n n ℂ)) a x
        = star ((hA.eigenvectorUnitary : Matrix n n ℂ) x a) from rfl,
      Matrix.IsHermitian.eigenvectorUnitary_apply]
    by_cases h : hA.eigenvalues a = lam
    · simp [h, mul_comm, mul_assoc, mul_left_comm]
    · simp [h]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne _ (fun h => hb h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

-- STEP 3: every quotient eigenvalue is a host eigenvalue.
theorem quot_eigenvalue_mem_host (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (k : I) :
    P.symmQuotient_isHermitian.eigenvalues k ∈ Set.range G.herm.eigenvalues := by
  have hnz : ∀ i, 0 < P.cellCard i := fun i => lt_of_le_of_ne (P.cellCard_nonneg i)
    (fun h => hne i h.symm)
  -- real eigenvalue ∈ spectrum ℝ Q̃ → cast to ℂ spectrum → spectrum_subset → host range.
  have hmemR : P.symmQuotient_isHermitian.eigenvalues k ∈ spectrum ℝ P.symmQuotient :=
    P.symmQuotient_isHermitian.eigenvalues_mem_spectrum_real k
  have hmemC : ((P.symmQuotient_isHermitian.eigenvalues k : ℝ) : ℂ) ∈ spectrum ℂ P.symmQuotient := by
    rw [show ((P.symmQuotient_isHermitian.eigenvalues k : ℝ) : ℂ)
          = algebraMap ℝ ℂ (P.symmQuotient_isHermitian.eigenvalues k) from rfl,
      spectrum.algebraMap_mem_iff]
    exact hmemR
  have hsub := P.spectrum_subset hnz hmemC
  rw [G.spectrum_subset_real] at hsub
  obtain ⟨r, hr, hreq⟩ := hsub
  have hreq' : ((r : ℝ) : ℂ) = ((P.symmQuotient_isHermitian.eigenvalues k : ℝ) : ℂ) := hreq
  have : r = P.symmQuotient_isHermitian.eigenvalues k := Complex.ofReal_inj.mp hreq'
  rw [← this]; exact hr

-- STEP 4: existence of an interpolating polynomial agreeing with the indicator
-- on all host eigenvalues.  The SAME polynomial then agrees with the indicator
-- on all quotient eigenvalues (by STEP 3).
theorem exists_interp_poly (G : WeightedGraph V) (lam : ℝ) :
    ∃ q : Polynomial ℝ, ∀ k : V,
      q.eval (G.herm.eigenvalues k) = (if G.herm.eigenvalues k = lam then 1 else 0) := by
  classical
  -- Interpolate over the finite set of distinct host eigenvalues with node map `id`.
  set S : Finset ℝ := (Finset.univ.image G.herm.eigenvalues) with hS
  refine ⟨Lagrange.interpolate S id (fun μ => if μ = lam then (1:ℝ) else 0), ?_⟩
  intro k
  have hmem : G.herm.eigenvalues k ∈ S := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have := Lagrange.eval_interpolate_at_node (s := S) (v := id)
    (r := fun μ => if μ = lam then (1:ℝ) else 0) (Set.injOn_id _) hmem
  simpa using this

-- STEP 5: Bᴴ * (aeval A q) * B = aeval Q̃ q for any real polynomial q.
theorem cellEmbedH_aeval_cellEmbed (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (q : Polynomial ℝ) :
    P.cellEmbedᴴ * (Polynomial.aeval G.adj q) * P.cellEmbed
      = Polynomial.aeval P.symmQuotient q := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hp, hr]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    -- algebraMap ℝ (Matrix _ _ ℂ) c = c • 1, so the term is c • A^n.
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_one_mul, smul_one_mul, Matrix.mul_smul, Matrix.smul_mul,
      P.cellEmbedH_adj_pow_cellEmbed hne n]

-- STEP 6: a Hermitian matrix's indicator-cfc equals aeval of an interpolating poly.
theorem cfc_indicator_eq_aeval {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (lam : ℝ) (q : Polynomial ℝ)
    (hq : ∀ k : n, q.eval (hA.eigenvalues k) = (if hA.eigenvalues k = lam then 1 else 0)) :
    hA.cfc (fun μ => if μ = lam then (1 : ℝ) else 0) = Polynomial.aeval A q := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  -- cfc f A = cfc q.eval A  (EqOn the spectrum) = aeval A q.
  rw [← Matrix.IsHermitian.cfc_eq hA]
  rw [show (Polynomial.aeval A q : Matrix n n ℂ) = cfc q.eval A from (cfc_polynomial q A).symm]
  apply cfc_congr
  intro x hx
  -- spectrum ℝ A = range eigenvalues.
  rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hA] at hx
  obtain ⟨k, rfl⟩ := hx
  simpa using (hq k).symm

-- STEP 7: THE TRANSPORT.  Bᴴ * hostProj * B = quotProj.
theorem cellEmbedH_hostProj_cellEmbed (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (lam : ℝ) :
    P.cellEmbedᴴ * hostProj G lam * P.cellEmbed = quotProj P lam := by
  obtain ⟨q, hq⟩ := exists_interp_poly G lam
  -- hostProj = aeval A q.
  have hH : hostProj G lam = Polynomial.aeval G.adj q := by
    rw [show hostProj G lam = G.herm.cfc (fun μ => if μ = lam then (1:ℝ) else 0) from
      (cfc_indicator_eq_proj G.herm lam).symm]
    exact cfc_indicator_eq_aeval G.herm lam q hq
  -- quotProj = aeval Q̃ q  (same q; valid since quot eigenvalues are host eigenvalues).
  have hQ : quotProj P lam = Polynomial.aeval P.symmQuotient q := by
    rw [show quotProj P lam
          = P.symmQuotient_isHermitian.cfc (fun μ => if μ = lam then (1:ℝ) else 0) from
        (cfc_indicator_eq_proj P.symmQuotient_isHermitian lam).symm]
    apply cfc_indicator_eq_aeval P.symmQuotient_isHermitian lam q
    intro k
    -- q.eval (quot eigenvalue) = indicator: the quot eigenvalue is some host eigenvalue.
    obtain ⟨k', hk'⟩ := P.quot_eigenvalue_mem_host hne k
    rw [← hk', hq k']
  rw [hH, hQ, P.cellEmbedH_aeval_cellEmbed hne q]

-- STEP 8a: statement host cross-entry = (Bᴴ * hostProj * B) j i.
theorem host_cross_eq_matrixElement (P : EquitablePartition G I) (lam : ℝ) (i j : I) :
    (∑ k : V, if G.herm.eigenvalues k = lam
        then (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
          * star (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec j x)
        else 0)
      = (P.cellEmbedᴴ * hostProj G lam * P.cellEmbed) j i := by
  classical
  -- Canonical triple-sum normal form, in (x,y,k) order.
  set T : ℂ := ∑ x : V, ∑ y : V, ∑ k : V, if G.herm.eigenvalues k = lam
      then star (P.cellUniformVec j y)
        * (G.herm.eigenvectorBasis k y * star (G.herm.eigenvectorBasis k x))
        * P.cellUniformVec i x else 0 with hT
  -- LHS = T.
  have hL : (∑ k : V, if G.herm.eigenvalues k = lam
        then (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
          * star (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec j x)
        else 0) = T := by
    rw [hT]
    -- Expand each k-term to ∑ x ∑ y, then reorder ∑ k ∑ x ∑ y → ∑ x ∑ y ∑ k.
    rw [show (∑ k : V, if G.herm.eigenvalues k = lam
            then (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
              * star (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec j x)
            else 0)
          = ∑ k : V, ∑ x : V, ∑ y : V, if G.herm.eigenvalues k = lam
              then star (P.cellUniformVec j y)
                * (G.herm.eigenvectorBasis k y * star (G.herm.eigenvectorBasis k x))
                * P.cellUniformVec i x else 0 by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : G.herm.eigenvalues k = lam
      · simp only [if_pos h]
        rw [star_sum, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [star_mul', star_star]; ring
      · simp only [if_neg h, Finset.sum_const, smul_zero]]
    rw [Finset.sum_comm (γ := V)]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm (γ := V)]
  -- RHS = T.
  have hR : (P.cellEmbedᴴ * hostProj G lam * P.cellEmbed) j i = T := by
    rw [Matrix.mul_apply, hT]
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    simp only [Matrix.conjTranspose_apply, cellEmbed, hostProj]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h <;> ring
  rw [hL, hR]

-- STEP 8b: quotient cross-entry = (quotProj) i j  (definitional).
theorem quot_cross_eq_quotProj (P : EquitablePartition G I) (lam : ℝ) (i j : I) :
    (∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
        then P.symmQuotient_isHermitian.eigenvectorBasis k i
          * star (P.symmQuotient_isHermitian.eigenvectorBasis k j)
        else 0) = quotProj P lam i j := rfl

-- STEP 8c: host diagonal sum (a real ∑ of normSq) casts to (quotProj) i i.
theorem host_diag_eq_quotProj (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (lam : ℝ) (i : I) :
    ((∑ k : V, if G.herm.eigenvalues k = lam
        then Complex.normSq (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
        else 0 : ℝ) : ℂ)
      = quotProj P lam i i := by
  rw [← P.cellEmbedH_hostProj_cellEmbed hne lam, ← P.host_cross_eq_matrixElement lam i i]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with h
  · rw [Complex.star_def, ← Complex.mul_conj]
  · rfl

-- STEP 8d: quotient diagonal sum casts to (quotProj) i i.
theorem quot_diag_eq_quotProj (P : EquitablePartition G I) (lam : ℝ) (i : I) :
    ((∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
        then Complex.normSq (P.symmQuotient_isHermitian.eigenvectorBasis k i)
        else 0 : ℝ) : ℂ)
      = quotProj P lam i i := by
  rw [quotProj]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with h
  · rw [Complex.star_def, ← Complex.mul_conj]
  · rfl

-- STEP 9: quotProj is Hermitian in its indices.
theorem quotProj_conj_symm (P : EquitablePartition G I) (lam : ℝ) (i j : I) :
    quotProj P lam j i = star (quotProj P lam i j) := by
  rw [quotProj, quotProj, star_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with h
  · rw [star_mul', star_star]; ring
  · rw [star_zero]

-- STEP 10: off-spectrum quotient eigenvalue ⇒ quotProj = 0.
theorem quotProj_eq_zero_of_not_mem (P : EquitablePartition G I) (lam : ℝ)
    (hlam : lam ∉ Set.range P.symmQuotient_isHermitian.eigenvalues) (i j : I) :
    quotProj P lam i j = 0 := by
  rw [quotProj]
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg]
  intro h
  exact hlam ⟨k, h⟩

-- A small ε-predicate transfer: Born condition preserved under conjugating cross.
theorem born_conj {c d : ℂ} (hd : ∃ r : ℝ, d = (r : ℂ))
    (h : ∃ ε : ℂ, ‖ε‖ = 1 ∧ c = ε * d) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ star c = ε * d := by
  obtain ⟨r, rfl⟩ := hd
  obtain ⟨ε, hε, hc⟩ := h
  refine ⟨star ε, by rw [norm_star]; exact hε, ?_⟩
  rw [hc, star_mul']
  rw [show star ((r : ℂ)) = (r : ℂ) from Complex.conj_ofReal r]

-- Abbreviation for the host/quotient diagonal real sums.
noncomputable def hostDiag (P : EquitablePartition G I) (lam : ℝ) (i : I) : ℝ :=
  ∑ k : V, if G.herm.eigenvalues k = lam
    then Complex.normSq (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
    else 0

noncomputable def quotDiag (P : EquitablePartition G I) (lam : ℝ) (i : I) : ℝ :=
  ∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
    then Complex.normSq (P.symmQuotient_isHermitian.eigenvectorBasis k i) else 0

theorem hostDiag_eq_quotDiag (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (lam : ℝ) (i : I) :
    hostDiag P lam i = quotDiag P lam i := by
  have h1 := P.host_diag_eq_quotProj hne lam i
  have h2 := P.quot_diag_eq_quotProj lam i
  rw [hostDiag, quotDiag]
  exact Complex.ofReal_inj.mp (h1.trans h2.symm)

/-- **THE KEYSTONE.**  Host cell-uniform strong cospectrality iff quotient strong
cospectrality, both in spelled-out spectral-projector cross-entry form. -/
theorem stronglyCospectral_iff (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) :
    (∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
      ∃ ε : ℂ, ‖ε‖ = 1 ∧
        (∑ k : V, if G.herm.eigenvalues k = lam
            then (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
              * star (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec j x)
            else 0)
          = ε * Complex.ofReal (Real.sqrt (hostDiag P lam i * hostDiag P lam j)))
      ↔
    (∀ lam : ℝ, lam ∈ Set.range P.symmQuotient_isHermitian.eigenvalues →
      ∃ ε : ℂ, ‖ε‖ = 1 ∧
        (∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
            then P.symmQuotient_isHermitian.eigenvectorBasis k i
              * star (P.symmQuotient_isHermitian.eigenvectorBasis k j)
            else 0)
          = ε * Complex.ofReal (Real.sqrt (quotDiag P lam i * quotDiag P lam j))) := by
  -- Rewrite host cross → quotProj j i, quot cross → quotProj i j, diags interchangeable.
  have hcrossH : ∀ lam, (∑ k : V, if G.herm.eigenvalues k = lam
        then (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
          * star (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec j x)
        else 0) = quotProj P lam j i := fun lam => by
    rw [P.host_cross_eq_matrixElement lam i j, P.cellEmbedH_hostProj_cellEmbed hne lam]
  constructor
  · -- forward: quotient eigenvalue is host eigenvalue; use host condition + conj.
    intro hH lam hlam
    have hlamH : lam ∈ Set.range G.herm.eigenvalues := by
      obtain ⟨k, rfl⟩ := hlam; exact P.quot_eigenvalue_mem_host hne k
    obtain ⟨ε, hε, heq⟩ := hH lam hlamH
    rw [hcrossH lam] at heq
    -- heq : quotProj j i = ε * ofReal(√(hostDiag_i·hostDiag_j)).
    rw [P.quot_cross_eq_quotProj lam i j,
      ← P.hostDiag_eq_quotDiag hne lam i, ← P.hostDiag_eq_quotDiag hne lam j]
    -- heq : quotProj j i = ε * D.  born_conj gives star (quotProj j i) = ε' * D.
    obtain ⟨ε', hε', heq'⟩ := born_conj (c := quotProj P lam j i)
      (d := Complex.ofReal (Real.sqrt (hostDiag P lam i * hostDiag P lam j)))
      ⟨Real.sqrt (hostDiag P lam i * hostDiag P lam j), rfl⟩ ⟨ε, hε, heq⟩
    -- star (quotProj j i) = quotProj i j.
    refine ⟨ε', hε', ?_⟩
    rwa [P.quotProj_conj_symm lam i j, star_star] at heq'
  · -- backward: host eigenvalue.  Two cases on quot-spectrum membership.
    intro hQ lam hlam
    by_cases hmem : lam ∈ Set.range P.symmQuotient_isHermitian.eigenvalues
    · obtain ⟨ε, hε, heq⟩ := hQ lam hmem
      rw [P.quot_cross_eq_quotProj lam i j] at heq
      rw [hcrossH lam, P.hostDiag_eq_quotDiag hne lam i, P.hostDiag_eq_quotDiag hne lam j]
      -- goal: quotProj j i = ε' * ofReal(√(quotDiag..)); heq : quotProj i j = ε * D.
      obtain ⟨ε', hε', heq'⟩ := born_conj (c := quotProj P lam i j)
        (d := Complex.ofReal (Real.sqrt (quotDiag P lam i * quotDiag P lam j)))
        ⟨Real.sqrt (quotDiag P lam i * quotDiag P lam j), rfl⟩ ⟨ε, hε, heq⟩
      -- star (quotProj i j) = quotProj j i.
      exact ⟨ε', hε', (P.quotProj_conj_symm lam i j).trans heq'⟩
    · -- off quotient spectrum: quotProj = 0, host cross = 0, RHS = ε·0; pick ε=1.
      refine ⟨1, by simp, ?_⟩
      rw [hcrossH lam, P.quotProj_eq_zero_of_not_mem lam hmem]
      -- 0 = 1 * ofReal(√(hostDiag·hostDiag)); but hostDiag = quotDiag = quotProj diag = 0.
      rw [P.hostDiag_eq_quotDiag hne lam i, P.hostDiag_eq_quotDiag hne lam j]
      have hdi : quotDiag P lam i = 0 := by
        have := P.quot_diag_eq_quotProj lam i
        rw [P.quotProj_eq_zero_of_not_mem lam hmem] at this
        exact_mod_cast this
      rw [hdi, zero_mul, Real.sqrt_zero, Complex.ofReal_zero, mul_zero]

/-- The sibling cospectrality predicate, instantiated on cell-uniform pairs.
We state the equivalence between *vertex* strong cospectrality of `e_i, e_j`
on the quotient and *vector* strong cospectrality of `|C_i⟩, |C_j⟩` on the
host. -/
theorem stronglyCospectral_cellUniform_iff_quotient
    (P : EquitablePartition G I) (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) :
    -- Host-side: `|C_i⟩` and `|C_j⟩` are strongly cospectral as *vectors*.
    -- For every eigenvalue `λ` of `G.adj`, the spectral projector of `G.adj`
    -- onto the `λ`-eigenspace sends `cellUniformVec i` and `cellUniformVec j`
    -- to parallel vectors: the cross entry is a unit-modulus phase times the
    -- geometric mean of the two diagonal entries.  We spell the projector
    -- entries out inline (in the host eigenbasis) to stay decoupled from the
    -- sibling `Cospectrality.lean` vector predicate.
    (∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
      ∃ ε : ℂ, ‖ε‖ = 1 ∧
        (∑ k : V, if G.herm.eigenvalues k = lam
            then (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
              * star (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec j x)
            else 0)
          = ε * Complex.ofReal (Real.sqrt
              ((∑ k : V, if G.herm.eigenvalues k = lam
                  then Complex.normSq (∑ x, star (G.herm.eigenvectorBasis k x)
                        * P.cellUniformVec i x)
                  else 0)
               * (∑ k : V, if G.herm.eigenvalues k = lam
                  then Complex.normSq (∑ x, star (G.herm.eigenvectorBasis k x)
                        * P.cellUniformVec j x)
                  else 0))))
      ↔
    -- Quotient-side: `e_i` and `e_j` are strongly cospectral as vertices of
    -- the (Hermitian) symmetric quotient `P.symmQuotient`, in its own
    -- eigenbasis.
    (∀ lam : ℝ, lam ∈ Set.range P.symmQuotient_isHermitian.eigenvalues →
      ∃ ε : ℂ, ‖ε‖ = 1 ∧
        (∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
            then P.symmQuotient_isHermitian.eigenvectorBasis k i
              * star (P.symmQuotient_isHermitian.eigenvectorBasis k j)
            else 0)
          = ε * Complex.ofReal (Real.sqrt
              ((∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
                  then Complex.normSq (P.symmQuotient_isHermitian.eigenvectorBasis k i)
                  else 0)
               * (∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
                  then Complex.normSq (P.symmQuotient_isHermitian.eigenvectorBasis k j)
                  else 0)))) := by
  -- CLOSED.  The spelled-out diagonal sums are definitionally `hostDiag`/`quotDiag`;
  -- the keystone `stronglyCospectral_iff` discharges the iff via the
  -- polynomial-functional-calculus eigenbasis transport `Bᴴ · hostProj · B = quotProj`.
  exact P.stronglyCospectral_iff hne i j

/-- **Automatic strong cospectrality (corollary).**  For an equitable
partition `P`, the cell-uniform vectors `|C_i⟩` and `|C_j⟩` are strongly
cospectral in `G` whenever `e_i` and `e_j` are strongly cospectral in the
symmetric quotient `P.symmQuotient`.

The previous formulation of this corollary was the vacuous `True → True`; we
restate it with the genuine quotient-side and host-side strong-cospectrality
predicates (the same spelled-out spectral-projector cross-entry conditions used
in `stronglyCospectral_cellUniform_iff_quotient`), and discharge it via that
iff.  That iff is itself proven (`exact P.stronglyCospectral_iff …`) and
axiom-clean, so this corollary carries no `sorry`. -/
theorem cellUniform_stronglyCospectral_of_quotient
    (P : EquitablePartition G I) (hne : ∀ k, P.cellCard k ≠ 0) (i j : I)
    (hquot :
      ∀ lam : ℝ, lam ∈ Set.range P.symmQuotient_isHermitian.eigenvalues →
        ∃ ε : ℂ, ‖ε‖ = 1 ∧
          (∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
              then P.symmQuotient_isHermitian.eigenvectorBasis k i
                * star (P.symmQuotient_isHermitian.eigenvectorBasis k j)
              else 0)
            = ε * Complex.ofReal (Real.sqrt
                ((∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
                    then Complex.normSq (P.symmQuotient_isHermitian.eigenvectorBasis k i)
                    else 0)
                 * (∑ k : I, if P.symmQuotient_isHermitian.eigenvalues k = lam
                    then Complex.normSq (P.symmQuotient_isHermitian.eigenvectorBasis k j)
                    else 0)))) :
    ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
      ∃ ε : ℂ, ‖ε‖ = 1 ∧
        (∑ k : V, if G.herm.eigenvalues k = lam
            then (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec i x)
              * star (∑ x, star (G.herm.eigenvectorBasis k x) * P.cellUniformVec j x)
            else 0)
          = ε * Complex.ofReal (Real.sqrt
              ((∑ k : V, if G.herm.eigenvalues k = lam
                  then Complex.normSq (∑ x, star (G.herm.eigenvectorBasis k x)
                        * P.cellUniformVec i x)
                  else 0)
               * (∑ k : V, if G.herm.eigenvalues k = lam
                  then Complex.normSq (∑ x, star (G.herm.eigenvectorBasis k x)
                        * P.cellUniformVec j x)
                  else 0))) :=
  (P.stronglyCospectral_cellUniform_iff_quotient hne i j).mpr hquot

/-! ## 5b. An explicit phantom-symmetric quotient-PST witness.

We discharge the existence claim of §6 with a *concrete, axiom-clean* witness:
the path `P_3` on `Fin 3` (adjacency `!![0,1,0; 1,0,1; 0,1,0]`) with the equitable
partition into the endpoint pair `{0,2}` (cell `0`) and the singleton centre
`{1}` (cell `1`).

* The partition is equitable: from either endpoint exactly one edge enters the
  centre, and from the centre two edges enter the endpoint cell.
* Its symmetric quotient is `√2 · X` (Pauli-`X` scaled by `√2`), so the
  cell-uniform walk is a two-level Rabi oscillation with **perfect state
  transfer** between the two cells at `τ = π/(2√2)` (off-diagonal evolution
  entry `sinh(-iπ/2) = -i`, modulus `1`).
* No adjacency-preserving permutation maps an endpoint to the centre: the centre
  has degree `2`, the endpoints degree `1`, and an automorphism preserves the
  row sum (weighted degree).  Hence the pair of cells exhibits PST with **no
  witnessing automorphism** — the qualitative Bachman–Tamon phenomenon.

This is a smaller witness than Bachman–Tamon's 6-vertex Fig. 1 example, but it
proves the same existential statement honestly and with no `sorry`.  (Here the
two cells even have different sizes, which already forbids any vertex bijection
between them; the proof nonetheless certifies the stated adjacency-automorphism
clause directly.) -/

namespace BachmanTamonWitness

open scoped Matrix
open NormedSpace

/-- The path `P_3` on `Fin 3` with explicit tridiagonal adjacency. -/
noncomputable def P3 : WeightedGraph (Fin 3) where
  adj := !![0, 1, 0; 1, 0, 1; 0, 1, 0]
  herm := by
    unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  loopless := by intro v; fin_cases v <;> simp

@[simp] theorem P3_adj : P3.adj = !![0, 1, 0; 1, 0, 1; 0, 1, 0] := rfl

/-- Cell map: endpoints `{0,2}` → cell `0`, centre `{1}` → cell `1`. -/
def cellMap : Fin 3 → Fin 2 := ![0, 1, 0]

/-- The equitable partition `{0,2} | {1}` of `P_3`. -/
noncomputable def Pw : EquitablePartition P3 (Fin 2) where
  cells := cellMap
  uniform := by
    intro i j x y hx hy
    subst hx
    have hbranch : ∀ z : Fin 3, ∀ k : Fin 2,
        (∑ w, if cellMap w = k then P3.adj z w else 0)
          = (if cellMap z = (0 : Fin 2) then (if k = 0 then 0 else 1)
             else (if k = 0 then 2 else 0)) := by
      intro z k
      fin_cases z <;> fin_cases k <;>
        simp [cellMap, Fin.sum_univ_three, P3_adj,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons] <;> norm_num
    rw [hbranch x j, hbranch y j, hy]

/-- The Nat-level cell-0 filter cardinality is 2. -/
theorem cellFilterCard0 :
    (Finset.univ.filter (fun w : Fin 3 => Pw.cells w = 0)).card = 2 := by decide

theorem cellFilterCard1 :
    (Finset.univ.filter (fun w : Fin 3 => Pw.cells w = 1)).card = 1 := by decide

theorem cellCard0 : Pw.cellCard 0 = 2 := by
  unfold EquitablePartition.cellCard; rw [cellFilterCard0]; norm_num

theorem cellCard1 : Pw.cellCard 1 = 1 := by
  unfold EquitablePartition.cellCard; rw [cellFilterCard1]; norm_num

theorem cellCard_ne : ∀ k, Pw.cellCard k ≠ 0 := by
  intro k
  fin_cases k
  · show Pw.cellCard 0 ≠ 0; rw [cellCard0]; norm_num
  · show Pw.cellCard 1 ≠ 0; rw [cellCard1]; norm_num

theorem quotient_01 : Pw.quotient 0 1 = 1 := by
  rw [Pw.quotient_apply 0 1 (0 : Fin 3) rfl]
  unfold EquitablePartition.branching Pw cellMap
  simp [Fin.sum_univ_three, P3_adj, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons]

theorem quotient_10 : Pw.quotient 1 0 = 2 := by
  rw [Pw.quotient_apply 1 0 (1 : Fin 3) rfl]
  unfold EquitablePartition.branching Pw cellMap
  simp [Fin.sum_univ_three, P3_adj, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons]
  norm_num

/-- The symmetric quotient is `√2 • X`. -/
theorem symmQuotient_eq :
    Pw.symmQuotient = (Real.sqrt 2 : ℂ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  unfold EquitablePartition.symmQuotient
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · rw [Pw.quotient_apply 0 0 (0 : Fin 3) rfl]
    simp [EquitablePartition.branching, Pw, cellMap, Fin.sum_univ_three, P3_adj,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
  · rw [show ((0 : Fin 2)) = (0 : Fin 2) from rfl, cellCard0, cellCard1, quotient_01]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Real.sqrt_one]
  · rw [cellCard0, cellCard1, quotient_10]
    rw [show ((Real.sqrt 2 : ℂ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)) 1 0
          = (Real.sqrt 2 : ℂ) by
      simp [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]]
    rw [Real.sqrt_one, Complex.ofReal_one, one_mul]
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
    field_simp
    rw [show (2 : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num]
    ring
  · rw [Pw.quotient_apply 1 1 (1 : Fin 3) rfl]
    simp [EquitablePartition.branching, Pw, cellMap, Fin.sum_univ_three, P3_adj,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]

section ScaledX

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Hadamard-type diagonalizer. -/
private def hadU : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

private theorem hadU_mul_half : hadU * ((1/2 : ℂ) • hadU) = 1 := by
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU_isUnit : IsUnit hadU := by
  refine ⟨⟨hadU, (1/2 : ℂ) • hadU, hadU_mul_half, ?_⟩, rfl⟩
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU_inv : hadU⁻¹ = (1/2 : ℂ) • hadU :=
  Matrix.inv_eq_right_inv hadU_mul_half

private theorem half_smul_hadU :
    ((1/2 : ℂ) • hadU) = !![(1:ℂ)/2, 1/2; 1/2, -(1/2)] := by
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem diag_fin_two (a b : ℂ) :
    (Matrix.diagonal ![a, b]) = !![a, 0; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem X_eq_conj_diag :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU * (Matrix.diagonal ![1, -1]) * hadU⁻¹ := by
  rw [hadU_inv, diag_fin_two, half_smul_hadU]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- `exp(s • Pauli-X)` as an explicit literal. -/
private theorem exp_smul_X_lit (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![(NormedSpace.exp s + NormedSpace.exp (-s)) / 2,
            (NormedSpace.exp s - NormedSpace.exp (-s)) / 2;
           (NormedSpace.exp s - NormedSpace.exp (-s)) / 2,
            (NormedSpace.exp s + NormedSpace.exp (-s)) / 2] := by
  have hsmul : s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU * (Matrix.diagonal ![s, -s]) * hadU⁻¹ := by
    have hd : (Matrix.diagonal ![s, -s] : Matrix (Fin 2) (Fin 2) ℂ)
        = s • Matrix.diagonal ![1, -1] := by
      rw [← Matrix.diagonal_smul]; congr 1; funext k; fin_cases k <;> simp
    rw [X_eq_conj_diag, hd, mul_smul_comm, smul_mul_assoc]
  rw [hsmul, Matrix.exp_conj _ _ hadU_isUnit, Matrix.exp_diagonal]
  have hdiag : (fun i => NormedSpace.exp (![s, -s] i))
      = (![NormedSpace.exp s, NormedSpace.exp (-s)] : Fin 2 → ℂ) := by
    funext k; fin_cases k <;> simp
  rw [Pi.exp_def, hdiag, hadU_inv, diag_fin_two, half_smul_hadU]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- The `(1,0)` entry of `exp(s • Pauli-X)` is `(eˢ − e⁻ˢ)/2 = sinh s`. -/
private theorem exp_smul_X_entry10 (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)) 1 0
      = (NormedSpace.exp s - NormedSpace.exp (-s)) / 2 := by
  rw [exp_smul_X_lit]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

end ScaledX

/-- The PST time for the `P_3` quotient `√2 • X`: `τ = π/(2√2)`. -/
noncomputable def tau : ℝ := Real.pi / (2 * Real.sqrt 2)

theorem tau_pos : 0 < tau := by
  unfold tau; apply div_pos Real.pi_pos; positivity

/-- The scalar `-(I·τ)·√2` equals `-(I·π/2)`. -/
theorem scalar_reduce :
    -(Complex.I * (tau : ℂ)) * (Real.sqrt 2 : ℂ) = -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) := by
  unfold tau
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  rw [show ((Real.pi / (2 * Real.sqrt 2) : ℝ) : ℂ)
        = ((Real.pi : ℝ) : ℂ) / ((2 : ℝ) : ℂ) / (Real.sqrt 2 : ℂ) by push_cast; ring]
  rw [show ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) / ((2 : ℝ) : ℂ) by push_cast; ring]
  field_simp

/-- **The cell-uniform PST.**  `IsCellUniformPST P3 Pw 0 1 τ` with `τ = π/(2√2)`:
the quotient is `√2 • X`, whose `(1,0)` evolution entry at `τ` is
`sinh(-(iπ/2)) = -i`, of modulus `1`. -/
theorem isCellUniformPST_witness : IsCellUniformPST P3 Pw 0 1 tau := by
  rw [Pw.cellUniformPST_iff_quotientPST cellCard_ne 0 1 tau]
  rw [symmQuotient_eq]
  rw [show (-(Complex.I * (tau : ℂ)) • ((Real.sqrt 2 : ℂ) •
            (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)))
        = (-(Complex.I * (tau : ℂ)) * (Real.sqrt 2 : ℂ)) •
            (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) by rw [smul_smul]]
  rw [scalar_reduce, exp_smul_X_entry10]
  set s : ℂ := -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) with hs
  have hexp_neg_s : NormedSpace.exp (-s) = Complex.I := by
    rw [hs, neg_neg, ← Complex.exp_eq_exp_ℂ,
      show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  have hexp_s : NormedSpace.exp s = -Complex.I := by
    rw [hs, ← Complex.exp_eq_exp_ℂ,
      show -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = (-(Real.pi / 2) : ℝ) * Complex.I by
        push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    push_cast; ring
  rw [hexp_s, hexp_neg_s]
  rw [show (-Complex.I - Complex.I) / 2 = -Complex.I by ring, norm_neg, Complex.norm_I]

/-- Row sums of `P3.adj`: endpoints have row sum 1, the centre has row sum 2. -/
theorem rowSum_P3 (z : Fin 3) :
    (∑ w, P3.adj z w) = (if z = 1 then 2 else 1) := by
  fin_cases z <;>
    simp [Fin.sum_univ_three, P3_adj, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons] <;> norm_num

/-- **Phantom clause.**  No adjacency-preserving permutation of `P_3` maps a
cell-0 vertex (an endpoint `{0,2}`) to the cell-1 vertex (the centre `{1}`):
the centre has degree 2, the endpoints degree 1, and an automorphism preserves
the (weighted) degree (row sum). -/
theorem no_automorphism_swaps :
    ∀ (φ : Fin 3 ≃ Fin 3),
      (∀ x y, P3.adj (φ x) (φ y) = P3.adj x y) →
      ∀ x, Pw.cells x = 0 → Pw.cells (φ x) ≠ 1 := by
  intro φ hφ x hx hcontra
  have hcell1 : ∀ a : Fin 3, cellMap a = 1 → a = 1 := by
    intro a ha; fin_cases a <;> simp_all [cellMap]
  have hφx1 : φ x = 1 := hcell1 _ hcontra
  have hsum : (∑ w, P3.adj (φ x) w) = (∑ y, P3.adj x y) := by
    calc (∑ w, P3.adj (φ x) w)
        = ∑ y, P3.adj (φ x) (φ y) := (Equiv.sum_comp φ (fun w => P3.adj (φ x) w)).symm
      _ = ∑ y, P3.adj x y := by simp_rw [hφ]
  rw [rowSum_P3, rowSum_P3, hφx1] at hsum
  have hxne : x ≠ 1 := by
    intro h; rw [h] at hx; exact absurd hx (by decide)
  rw [if_neg hxne, if_pos rfl] at hsum
  norm_num at hsum

end BachmanTamonWitness

/-! ## 6. Phantom-symmetry corollary.

Bachman–Tamon's main qualitative observation (arXiv:1108.0339, §4) is that
quotient PST can admit pairs `(i, j)` with no automorphism of `G` swapping
two representatives of the cells.  This is impossible for the classical
"automorphism-based" PST constructions (which always exhibit `u ↦ v` as the
action of an involutive automorphism).  We package this as a corollary,
deliberately phrased so that *no* automorphism hypothesis is required.

It is **proven** (no `sorry`) by the explicit `BachmanTamonWitness` above. -/

/-- **Phantom-symmetry corollary (PROVEN).**  There exist a weighted graph
`G`, an equitable partition `P : EquitablePartition G I`, indices `i, j : I`
and a time `τ : ℝ` such that:

* `IsCellUniformPST G P i j τ` holds (host PST between cell-uniform states),
* no automorphism of `G` maps any representative of cell `i` to any
  representative of cell `j` (cells are "phantom" — they exist as PST
  endpoints without symmetry).

Bachman–Tamon exhibit an explicit example with a 6-vertex graph and a 2-cell
partition (their Fig. 1).  We instead discharge the existential with the smaller
explicit witness built in `BachmanTamonWitness` above: the path `P_3` with the
endpoint/centre partition `{0,2} | {1}`, whose symmetric quotient is `√2 · X`
and which therefore has cell-uniform PST at `τ = π/(2√2)` while no
adjacency-automorphism maps an endpoint to the centre (the degrees differ).

Non-vacuity: the cells `0 ≠ 1` are nonempty and the no-automorphism clause is a
genuine universally-quantified statement (the identity permutation satisfies it
because it fixes the endpoint cell — it does *not* trivially refute the claim),
proven here via a real weighted-degree argument rather than vacuously. -/
theorem phantom_symmetry_PST_exists :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : WeightedGraph V)
      (I : Type) (_ : Fintype I) (_ : DecidableEq I)
      (P : EquitablePartition G I) (i j : I) (τ : ℝ),
      IsCellUniformPST G P i j τ ∧
        -- "no host automorphism swaps i and j": the absence of any permutation
        -- of `V` that preserves `G.adj` and maps a representative of cell `i`
        -- to a representative of cell `j`.
        (∀ (φ : V ≃ V), (∀ x y, G.adj (φ x) (φ y) = G.adj x y) →
          ∀ x, P.cells x = i → P.cells (φ x) ≠ j) :=
  ⟨Fin 3, inferInstance, inferInstance, BachmanTamonWitness.P3,
    Fin 2, inferInstance, inferInstance, BachmanTamonWitness.Pw, 0, 1,
    BachmanTamonWitness.tau,
    BachmanTamonWitness.isCellUniformPST_witness,
    BachmanTamonWitness.no_automorphism_swaps⟩

/-! ## 7. Chiral / signed extension.

Combining the Bachman–Tamon iff with `WeightedGraph.signedBy_preserves_equitable`
from `Graphplay/Chiral.lean`, the iff carries over to chirally-signed bundles
whose signing is *cross-constant* on the cells.  Concretely, if `s` is a
chiral signing of `G` cross-constant on the cells of `P`, then `P` is again
equitable for the signed graph `G.signedBy s`, and the quotient PST iff
applies verbatim to `(G.signedBy s, P)` with the *signed quotient matrix*
on the right-hand side.

Note: the signed quotient differs from `P.quotient` by the cell-pair phase
factor `τ(i, j) := s.σ x y` for any `x ∈ C_i`, `y ∈ C_j` (well-defined by
cross-constance).  This is the algebraic content of the Levine et al.
(arXiv:2605.04414) chiral PST/mixing optimization theorem (Lemma 3 there).
-/

/-- **Chirally-signed iff.**  Let `P` be an equitable partition of `G`, and
let `s` be a chiral signing of `G` that is cross-constant on `P.cells`
(i.e. `s.σ x y` depends only on `(P.cells x, P.cells y)`).  Then the
Bachman–Tamon iff holds for the signed graph `G.signedBy s` with the same
partition `P` (now viewed as equitable for the signed graph via
`signedBy_preserves_equitable`):

  `IsCellUniformPST (G.signedBy s) (G.signedBy_preserves_equitable P s h) i j τ
   ↔ PST on the *signed quotient* between `i` and `j` at time `τ`.`

Where the signed quotient is `P.quotient` multiplied entrywise by the cell-pair
phase function `τ_pair : I → I → ℂ` extracted from `s` via cross-constance.
-/
theorem cellUniformPST_iff_quotientPST_signed
    (P : EquitablePartition G I) (s : ChiralSigning V)
    (h : s.CrossConstant P.cells)
    (hne : ∀ k, (G.signedBy_preserves_equitable P s h).cellCard k ≠ 0)
    (i j : I) (τ : ℝ) :
    let P' := G.signedBy_preserves_equitable P s h
    IsCellUniformPST (G.signedBy s) P' i j τ ↔
      -- PST on the *signed quotient*: the Born-rule modulus condition on the
      -- symmetric quotient of the signed equitable partition.  (The previous
      -- formulation carried the vacuous placeholder RHS `‖(1 : ℂ)‖ = 1`, which
      -- is trivially true and said nothing about the signed quotient.)
      ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P'.symmQuotient)) j i‖ = 1 := by
  intro P'
  exact P'.cellUniformPST_iff_quotientPST hne i j τ

/-- **Chiral phantom symmetry (corollary).**  Combining
`phantom_symmetry_PST_exists` with `cellUniformPST_iff_quotientPST_signed`:
there exist cell-uniform PST pairs on a chirally-signed bundle with no host
automorphism of the *signed* graph swapping the cells.  This is the chiral
analogue of Bachman–Tamon's main qualitative observation and the conceptual
input to the optimal mixing time `π / (3√3)` of `unitaryHammingChiralK4`
(Levine et al., 2605.04414, Theorem 2). -/
theorem phantom_symmetry_chiral_PST_exists :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : WeightedGraph V)
      (I : Type) (_ : Fintype I) (_ : DecidableEq I)
      (P : EquitablePartition G I)
      (s : ChiralSigning V) (h : s.CrossConstant P.cells)
      (i j : I) (τ : ℝ),
      IsCellUniformPST (G.signedBy s)
        (G.signedBy_preserves_equitable P s h) i j τ ∧
        -- no automorphism of the *signed* graph swaps cells `i`, `j`:
        (∀ (φ : V ≃ V),
          (∀ x y, (G.signedBy s).adj (φ x) (φ y) = (G.signedBy s).adj x y) →
          ∀ x, P.cells x = i → P.cells (φ x) ≠ j) := by
  -- CLOSED (no `sorry`): take the now-proven unsigned `phantom_symmetry_PST_exists`
  -- witness and apply the *trivial* signing (`G.signedBy 1 = G`, which is
  -- cross-constant via `τ ≡ 1`).  Cell map, cardinalities, adjacency and
  -- evolution are all unchanged, so both conjuncts transfer verbatim.
  obtain ⟨V, instF, instD, G, I, instFI, instDI, P, i, j, τ, hpst, hno⟩ :=
    phantom_symmetry_PST_exists
  refine ⟨V, instF, instD, G, I, instFI, instDI, P, ChiralSigning.trivial V,
    ⟨fun _ _ => 1, fun _ _ => rfl⟩, i, j, τ, ?_, ?_⟩
  · -- `G.signedBy 1 = G`, and the preserved partition has the same cells/cards.
    -- `IsCellUniformPST` depends only on `adj` (via `evolve`) and `cellCard`,
    -- both invariant; the signed graph reduces to `G`.
    have hcard : ∀ k, (G.signedBy_preserves_equitable P (ChiralSigning.trivial V)
        ⟨fun _ _ => 1, fun _ _ => rfl⟩).cellCard k = P.cellCard k := fun k => rfl
    have hev : (G.signedBy (ChiralSigning.trivial V)).evolve τ = G.evolve τ :=
      congrArg (fun (H : WeightedGraph V) => H.evolve τ) (WeightedGraph.signedBy_trivial G)
    unfold IsCellUniformPST
    simp only [hcard, hev]
    exact hpst
  · intro φ hφ x hx
    -- The signed-graph adjacency equals `G.adj` (trivial signing), so the
    -- automorphism hypothesis is exactly the unsigned one.
    apply hno φ ?_ x hx
    intro a b
    have := hφ a b
    simpa only [WeightedGraph.signedBy_trivial] using this

/-! ## 8. Index lemma for downstream files. -/

/-- **Index lemma.**  Packaging the iff together with the no-leakage
condition: when `P` is equitable, `IsCellUniformPST` and quotient PST coincide
*and* the host evolution genuinely stays inside the cell-uniform subspace.
This is the form most useful for downstream consumers (chiral bundle PST,
hypergraph PST, graphon PST, etc.). -/
theorem cellUniformPST_iff_quotientPST_with_noLeakage
    (P : EquitablePartition G I) (hne : ∀ k, P.cellCard k ≠ 0) (i j : I) (τ : ℝ) :
    (NoCellUniformLeakage G P) ∧
      (IsCellUniformPST G P i j τ ↔
        ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)) j i‖ = 1) :=
  ⟨P.noLeakage_of_equitable,
   P.cellUniformPST_iff_quotientPST hne i j τ⟩

end EquitablePartition
end Graphplay
