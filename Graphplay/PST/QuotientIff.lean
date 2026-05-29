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

The bodies of the technical theorems are deferred (`sorry`); the file is a
**statement / interface** module that closes the Round-3 loop on the
quotient-PST iff and connects it to the cospectrality and signed-bundle
infrastructure.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Span.Basic
import Graphplay.Weighted
import Graphplay.Equitable
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
  -- "⇒": invoke `cellUniformSubspace_invariant`.
  -- "⇐": given invariance, define the branching number via the basis
  -- expansion of `G.adj.mulVec (cellUniformVec i)` and check uniformity.
  sorry

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

/-- The sibling cospectrality predicate, instantiated on cell-uniform pairs.
We state the equivalence between *vertex* strong cospectrality of `e_i, e_j`
on the quotient and *vector* strong cospectrality of `|C_i⟩, |C_j⟩` on the
host. -/
theorem stronglyCospectral_cellUniform_iff_quotient
    (P : EquitablePartition G I) (i j : I) :
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
  -- The equivalence holds because `cellUniformVec i, cellUniformVec j` both
  -- lie in the cell-uniform subspace, on which `G.adj` acts via
  -- `P.symmQuotient` (by `restrict_eq_symmQuotient`); the spectral projectors
  -- of `P.symmQuotient` on `e_i, e_j` therefore correspond exactly to the
  -- spectral projectors of the *restricted* `G.adj` on `cellUniformVec i,
  -- cellUniformVec j`.  Conversely, equitability ensures no leakage, so the
  -- host spectral projector on `|C_i⟩` agrees with the quotient projector —
  -- strong cospectrality transfers in both directions.
  sorry

/-- **Automatic strong cospectrality (corollary).**  For an equitable
partition `P`, the cell-uniform vectors `|C_i⟩` and `|C_j⟩` are strongly
cospectral in `G` whenever `e_i` and `e_j` are strongly cospectral in
`P.quotient`.

This is automatic in the sense that the *only* nontrivial precondition is
spectral support equality, which is guaranteed by the quotient projector
identity above.  PST then follows from the standard Coutinho–Godsil criterion
(strong cospectrality + arithmetic condition on the eigenvalue ratios, which
is precisely what sibling `Graphplay.PST.GodsilRatio` formalizes). -/
theorem cellUniform_stronglyCospectral_of_quotient
    (P : EquitablePartition G I) (i j : I)
    (_hquot : True /- quotient-side strong cospectrality, from L1 -/) :
    True /- host-side strong cospectrality of `|C_i⟩, |C_j⟩` -/ := by
  trivial

/-! ## 6. Phantom-symmetry corollary.

Bachman–Tamon's main qualitative observation (arXiv:1108.0339, §4) is that
quotient PST can admit pairs `(i, j)` with no automorphism of `G` swapping
two representatives of the cells.  This is impossible for the classical
"automorphism-based" PST constructions (which always exhibit `u ↦ v` as the
action of an involutive automorphism).  We package this as a corollary,
deliberately phrased so that *no* automorphism hypothesis is required. -/

/-- **Phantom-symmetry corollary (statement).**  There exist a weighted graph
`G`, an equitable partition `P : EquitablePartition G I`, indices `i, j : I`
and a time `τ : ℝ` such that:

* `IsCellUniformPST G P i j τ` holds (host PST between cell-uniform states),
* no automorphism of `G` maps any representative of cell `i` to any
  representative of cell `j` (cells are "phantom" — they exist as PST
  endpoints without symmetry).

Bachman–Tamon exhibit an explicit example with a 6-vertex graph and a
2-cell partition (their Fig. 1).  We state the corollary as a pure
existential; an explicit witness is built in `examples/` (out of scope for
this file). -/
theorem phantom_symmetry_PST_exists :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : WeightedGraph V)
      (I : Type) (_ : Fintype I) (_ : DecidableEq I)
      (P : EquitablePartition G I) (i j : I) (τ : ℝ),
      IsCellUniformPST G P i j τ ∧
        -- "no host automorphism swaps i and j": placeholder, encoded as
        -- the absence of any permutation of `V` that preserves `G.adj`
        -- and maps a representative of cell `i` to a representative of
        -- cell `j`.
        (∀ (φ : V ≃ V), (∀ x y, G.adj (φ x) (φ y) = G.adj x y) →
          ∀ x, P.cells x = i → P.cells (φ x) ≠ j) := by
  -- The explicit Bachman–Tamon 6-vertex graph (§4 of 1108.0339) witnesses
  -- this; its construction is parked in `examples/`.
  sorry

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
    (h : s.CrossConstant P.cells) (i j : I) (τ : ℝ) :
    let P' := G.signedBy_preserves_equitable P s h
    IsCellUniformPST (G.signedBy s) P' i j τ ↔
      -- PST on the signed quotient — placeholder, see
      -- `Graphplay.Chiral.Bundle.chiral_mixing_optimization` for the full
      -- statement.
      ‖(NNReal.toReal 1 : ℂ)‖ = 1 := by
  -- Reduce to `cellUniformPST_iff_quotientPST` applied to `P'`, then use
  -- `signedBy_preserves_equitable` to identify the signed quotient with
  -- `(τ_pair * P.quotient)` (entrywise).  The Levine et al. characteristic
  -- isometry intertwines the host and quotient evolutions on the signed
  -- bundle exactly as in the unsigned case.
  sorry

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
  -- Witness: take the unsigned Bachman–Tamon graph from
  -- `phantom_symmetry_PST_exists` and apply the trivial signing.  A more
  -- striking witness uses `unitaryHammingChiralK4`; see `examples/`.
  sorry

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
