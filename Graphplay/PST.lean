import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
universe u v w
namespace Graphplay

open scoped Matrix
open NormedSpace

/-! ## Continuous-time quantum walk evolution and perfect state transfer

For a Hermitian weighted graph `G` with adjacency matrix `A`, the
continuous-time quantum walk evolves via `U(τ) = exp(-i τ A)`.  Perfect state
transfer (PST) from `u` to `v` at time `τ` is the condition that the modulus of
the `(u,v)`-entry of `U(τ)` equals one (Born-rule probability 1).
-/

/-- Perfect state transfer (PST) between vertices `u` and `v` at time `τ`:
the modulus of the `(u,v)`-entry of `U(τ)` is one.  This is the Born-rule
modulus condition; equivalently the off-diagonal entry has unit norm and all
other amplitudes on the column are zero.

References: Bachman, Tamon, et al., "Perfect state transfer on quotient
graphs" (arXiv:1108.0339) characterize PST on quotient graphs in terms of the
parent graph in the discrete-time setting; the continuous-time analogue used
here is folklore. -/
def IsPST {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (u v : V) (τ : ℝ) : Prop :=
  ‖G.evolve τ u v‖ = 1

/-- Cell-uniform PST in an equitable partition: PST between the normalized
uniform superpositions `|C_i⟩ := (1/√|C_i|) Σ_{x ∈ C_i} |x⟩` and `|C_j⟩` at
time `τ`.  Concretely, the modulus of the cell-uniform matrix element
`⟨C_j|U(τ)|C_i⟩ = ∑_{x ∈ C_i, y ∈ C_j} (G.evolve τ) y x / √(|C_i||C_j|)`
equals one. -/
def IsCellUniformPST {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I) (i j : I) (τ : ℝ) : Prop :=
  ‖(∑ x, ∑ y, if P.cells x = i ∧ P.cells y = j
      then G.evolve τ y x else 0) /
      ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ))‖ = 1

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- The **cell-embedding matrix** `B : Matrix V I ℂ`, whose `(v, i)` entry is the
value of the normalized cell-uniform vector `cellUniformVec i` at `v`.  Its
columns are the orthonormal cell-uniform basis vectors. -/
noncomputable def cellEmbed (P : EquitablePartition G I) : Matrix V I ℂ :=
  fun v i => P.cellUniformVec i v

/-- The columns of `cellEmbed` are orthonormal: `Bᴴ * B = 1`, provided every
cell is nonempty (so the normalizations are genuine).  For an empty cell the
corresponding `cellUniformVec` is the zero vector and the identity fails. -/
theorem cellEmbed_conjTranspose_mul_cellEmbed (P : EquitablePartition G I)
    (hne : ∀ k, P.cellCard k ≠ 0) :
    P.cellEmbedᴴ * P.cellEmbed = (1 : Matrix I I ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, cellEmbed, cellUniformVec]
  by_cases hij : i = j
  · subst hij
    -- diagonal: ∑_v [cells v = i]/√|C_i| · [cells v = i]/√|C_i| = |C_i|/|C_i| = 1
    rw [Matrix.one_apply_eq]
    -- the nonzero summands are exactly v ∈ C_i, each contributing 1/|C_i|
    have hsum : (∑ v, star (if P.cells v = i then (1:ℂ)/(Real.sqrt (P.cellCard i):ℂ) else 0)
                  * (if P.cells v = i then (1:ℂ)/(Real.sqrt (P.cellCard i):ℂ) else 0))
        = ∑ v, (if P.cells v = i then ((1:ℂ)/(Real.sqrt (P.cellCard i):ℂ))^2 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : P.cells v = i
      · rw [if_pos hv, if_pos hv]
        rw [star_div₀, star_one, Complex.star_def, Complex.conj_ofReal]
        ring
      · rw [if_neg hv, if_neg hv, star_zero, mul_zero]
    rw [hsum, ← Finset.sum_filter, Finset.sum_const]
    -- card of filter = |C_i| (as a real cast); need |C_i| • (1/√|C_i|)^2 = 1.
    have hci : (0 : ℝ) < P.cellCard i :=
      lt_of_le_of_ne (P.cellCard_nonneg i) (Ne.symm (hne i))
    have hsqrt : (Real.sqrt (P.cellCard i) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (Real.sqrt_pos.mpr hci)
    have hcardeq : ((Finset.univ.filter (fun v : V => P.cells v = i)).card : ℂ)
        = (P.cellCard i : ℂ) := by
      unfold cellCard; push_cast; rfl
    rw [nsmul_eq_mul, hcardeq]
    -- |C_i| * (1/√|C_i|)^2 = |C_i| / |C_i| = 1
    have hsq : (Real.sqrt (P.cellCard i) : ℂ) ^ 2 = (P.cellCard i : ℂ) := by
      rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (P.cellCard_nonneg i)]
    field_simp
    exact hsq.symm
  · -- off-diagonal: cells v can't equal both i and j, every summand 0
    rw [Matrix.one_apply_ne hij]
    apply Finset.sum_eq_zero
    intro v _
    by_cases hvi : P.cells v = i
    · have hvj : P.cells v ≠ j := fun h => hij (hvi ▸ h)
      rw [if_neg hvj, mul_zero]
    · rw [if_neg hvi, star_zero, zero_mul]

/-- `cellEmbed` applied to a quotient-side vector is the cell-uniform
combination: `(B *ᵥ w) v = ∑ i, w i · cellUniformVec i v`. -/
theorem cellEmbed_mulVec (P : EquitablePartition G I) (w : I → ℂ) :
    P.cellEmbed.mulVec w = fun v => ∑ i, w i * P.cellUniformVec i v := by
  funext v
  simp only [Matrix.mulVec, dotProduct, cellEmbed]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- **Matrix intertwining.**  The adjacency matrix and the cell-embedding satisfy
`A * B = B * symmQuotient`.  This is the matrix form of `restrict_eq_symmQuotient`:
the cell-uniform subspace is `A`-invariant and the induced action is the
symmetric quotient. -/
theorem adj_mul_cellEmbed (P : EquitablePartition G I) :
    G.adj * P.cellEmbed = P.cellEmbed * P.symmQuotient := by
  rw [Matrix.ext_iff_mulVec]
  intro w
  -- both sides, evaluated via `mulVec`, reduce to the two sides of `restrict_eq_symmQuotient`.
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [cellEmbed_mulVec, cellEmbed_mulVec]
  exact P.restrict_eq_symmQuotient w

/-- Scaled intertwining: `(s • A) * B = B * (s • symmQuotient)`. -/
theorem smul_adj_mul_cellEmbed (P : EquitablePartition G I) (s : ℂ) :
    (s • G.adj) * P.cellEmbed = P.cellEmbed * (s • P.symmQuotient) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, adj_mul_cellEmbed]

/-- Power intertwining: `(s • A) ^ k * B = B * (s • symmQuotient) ^ k`. -/
theorem smul_adj_pow_mul_cellEmbed (P : EquitablePartition G I) (s : ℂ) (k : ℕ) :
    (s • G.adj) ^ k * P.cellEmbed = P.cellEmbed * (s • P.symmQuotient) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, smul_adj_mul_cellEmbed,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

end EquitablePartition

section ExpIntertwining

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- **Exponential intertwining.**  `exp(s • A) * B = B * exp(s • symmQuotient)`.
Pushed through the (entire) exponential power series term-by-term using the
matrix power intertwining and continuity of left/right multiplication by `B`. -/
theorem EquitablePartition.exp_smul_adj_mul_cellEmbed
    (P : EquitablePartition G I) (s : ℂ) :
    NormedSpace.exp (s • G.adj) * P.cellEmbed
      = P.cellEmbed * NormedSpace.exp (s • P.symmQuotient) := by
  -- Right multiplication by `B`, as a continuous additive hom `Matrix V V ℂ →+ Matrix V I ℂ`.
  let φ : Matrix V V ℂ →+ Matrix V I ℂ :=
    { toFun := fun M => M * P.cellEmbed
      map_zero' := Matrix.zero_mul _
      map_add' := fun M N => Matrix.add_mul M N _ }
  have hφc : Continuous φ := Continuous.matrix_mul continuous_id continuous_const
  -- Left multiplication by `B`, as a continuous additive hom `Matrix I I ℂ →+ Matrix V I ℂ`.
  let ψ : Matrix I I ℂ →+ Matrix V I ℂ :=
    { toFun := fun N => P.cellEmbed * N
      map_zero' := Matrix.mul_zero _
      map_add' := fun M N => Matrix.mul_add _ M N }
  have hψc : Continuous ψ := Continuous.matrix_mul continuous_const continuous_id
  -- The exp series for `s • A` and `s • symmQuotient`, as `HasSum`s.
  have hA : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (s • G.adj) ^ k)
      (NormedSpace.exp (s • G.adj)) := exp_series_hasSum_exp' _
  have hN : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (s • P.symmQuotient) ^ k)
      (NormedSpace.exp (s • P.symmQuotient)) := exp_series_hasSum_exp' _
  -- Map `hA` through `φ` (right-mult by B) and `hN` through `ψ` (left-mult by B).
  have hAφ := hA.map φ hφc
  have hNψ := hN.map ψ hψc
  -- The two image series are termwise equal, hence have the same sum.
  have hterm : (φ ∘ fun k => (Nat.factorial k : ℂ)⁻¹ • (s • G.adj) ^ k)
      = (ψ ∘ fun k => (Nat.factorial k : ℂ)⁻¹ • (s • P.symmQuotient) ^ k) := by
    funext k
    show ((Nat.factorial k : ℂ)⁻¹ • (s • G.adj) ^ k) * P.cellEmbed
      = P.cellEmbed * ((Nat.factorial k : ℂ)⁻¹ • (s • P.symmQuotient) ^ k)
    rw [Matrix.smul_mul, Matrix.mul_smul, P.smul_adj_pow_mul_cellEmbed]
  rw [hterm] at hAφ
  -- `φ (exp ..) = ψ (exp ..)` by uniqueness of sums.
  exact hAφ.unique hNψ

end ExpIntertwining

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- The cell-uniform matrix element of a vertex-space matrix `E` is the `(j, i)`
entry of `Bᴴ * E * B`:
`∑_{x ∈ C_i, y ∈ C_j} E_{yx} / (√|C_i| √|C_j|) = (Bᴴ * E * B) j i`. -/
theorem cellUniform_matrixElement (P : EquitablePartition G I)
    (E : Matrix V V ℂ) (i j : I) :
    (∑ x, ∑ y, if P.cells x = i ∧ P.cells y = j then E y x else 0) /
        ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ))
      = (P.cellEmbedᴴ * E * P.cellEmbed) j i := by
  rw [Matrix.mul_apply]
  -- RHS = ∑_x (Bᴴ*E)_{jx} B_{xi} = ∑_x ∑_y star(B_{yj}) E_{yx} B_{xi}.
  have hRHS : (∑ x, (P.cellEmbedᴴ * E) j x * P.cellEmbed x i)
      = ∑ x, ∑ y, (star (P.cellEmbed y j)) * E y x * (P.cellEmbed x i) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Matrix.conjTranspose_apply]
  rw [hRHS]
  -- Both sides now ∑_x ∑_y, termwise matching after pushing the division inside.
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  -- LHS: [cells x = i ∧ cells y = j] E_{yx} / (√|C_i|√|C_j|).
  -- RHS: star(B_{yj}) E_{yx} B_{xi}.
  simp only [cellEmbed, cellUniformVec]
  by_cases hx : P.cells x = i
  · by_cases hy : P.cells y = j
    · rw [if_pos ⟨hx, hy⟩, if_pos hx, if_pos hy]
      rw [Complex.star_def, map_div₀, map_one, Complex.conj_ofReal]
      ring
    · rw [if_neg (fun h => hy h.2), if_neg hy, star_zero, zero_mul, zero_mul, zero_div]
  · rw [if_neg (fun h => hx h.1), if_neg hx, mul_zero, zero_div]

end EquitablePartition

/-- **PST lifting via equitable partitions.**  If the *symmetric quotient* of an
equitable partition exhibits PST between cells `i` and `j` at time `τ`, then
the host graph exhibits cell-uniform PST between the corresponding uniform
states at the same time `τ`.

This is the continuous-time avatar of the Bachman–Tamon discrete-time
characterization (arXiv:1108.0339, "Perfect state transfer on quotient
graphs").  The quotient evolution that drives cell-uniform PST is the evolution
of the Hermitian `symmQuotient` (the matrix of `G.adj` in the
orthonormal cell-uniform basis), not the raw `quotient`.  We require every cell
to be nonempty (`hne`); otherwise the cell-embedding has a zero column, the
normalizations degenerate, and the statement fails. -/
theorem EquitablePartition.pst_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) {i j : I} {τ : ℝ}
    (hne : ∀ k, P.cellCard k ≠ 0) :
    ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)) j i‖ = 1 →
    IsCellUniformPST G P i j τ := by
  intro hquot
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  -- `evolve τ = exp(s • A)`.
  have hev : G.evolve τ = NormedSpace.exp (s • G.adj) := rfl
  -- The cell-uniform matrix element equals `(Bᴴ * evolve τ * B) j i`.
  unfold IsCellUniformPST
  rw [P.cellUniform_matrixElement (G.evolve τ) i j]
  -- `Bᴴ * evolve τ * B = exp(s • symmQuotient)`.
  have hEB : G.evolve τ * P.cellEmbed = P.cellEmbed * NormedSpace.exp (s • P.symmQuotient) := by
    rw [hev]; exact P.exp_smul_adj_mul_cellEmbed s
  have hBEB : P.cellEmbedᴴ * G.evolve τ * P.cellEmbed
      = NormedSpace.exp (s • P.symmQuotient) := by
    rw [Matrix.mul_assoc, hEB, ← Matrix.mul_assoc,
      P.cellEmbed_conjTranspose_mul_cellEmbed hne, Matrix.one_mul]
  rw [hBEB]
  -- The hypothesis is exactly `‖(exp(s • symmQuotient)) j i‖ = 1`.
  rw [show s • P.symmQuotient = -(Complex.I * (τ : ℂ)) • P.symmQuotient from rfl]
  exact hquot

/-- Pretty-good state transfer (PGST): for every `ε > 0` there is a time `τ`
at which the `(u,v)`-amplitude has modulus within `ε` of one. -/
def IsPGST {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, |‖G.evolve τ u v‖ - 1| < ε

/-- Cell-uniform PGST in an equitable partition: for every `ε > 0` there is a
time `τ` at which the modulus of the normalized cell-uniform matrix element
`⟨C_j|U(τ)|C_i⟩` is within `ε` of one (`≥ 1 - ε`). -/
def IsCellUniformPGST {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I) (i j : I) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ,
    ‖(∑ x, ∑ y, if P.cells x = i ∧ P.cells y = j
                then G.evolve τ y x else 0) /
        ((Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard j) : ℂ))‖ ≥ 1 - ε

/-- **PGST lifting via equitable partitions.**  PGST on the *symmetric quotient*
between cells `j` and `i` lifts to cell-uniform PGST on the host.  Same lineage
as `pst_lift` (Bachman–Tamon 1108.0339, continuous-time variant): the cell-
uniform matrix element equals the corresponding `symmQuotient`-evolution entry
(via `cellUniform_matrixElement` and the exponential intertwining), so the
within-`ε` condition transfers verbatim at the same time `τ`.  Requires every
cell nonempty (`hne`). -/
theorem EquitablePartition.pgst_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I) {i j : I}
    (hne : ∀ k, P.cellCard k ≠ 0)
    (hquot : ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ,
      ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • P.symmQuotient)) j i‖ ≥ 1 - ε) :
    IsCellUniformPGST G P i j := by
  intro ε hε
  obtain ⟨τ, hτ⟩ := hquot ε hε
  refine ⟨τ, ?_⟩
  -- The cell-uniform matrix element equals the `symmQuotient`-evolution entry.
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  have hev : G.evolve τ = NormedSpace.exp (s • G.adj) := rfl
  rw [P.cellUniform_matrixElement (G.evolve τ) i j]
  have hEB : G.evolve τ * P.cellEmbed = P.cellEmbed * NormedSpace.exp (s • P.symmQuotient) := by
    rw [hev]; exact P.exp_smul_adj_mul_cellEmbed s
  have hBEB : P.cellEmbedᴴ * G.evolve τ * P.cellEmbed
      = NormedSpace.exp (s • P.symmQuotient) := by
    rw [Matrix.mul_assoc, hEB, ← Matrix.mul_assoc,
      P.cellEmbed_conjTranspose_mul_cellEmbed hne, Matrix.one_mul]
  rw [hBEB, show s • P.symmQuotient = -(Complex.I * (τ : ℂ)) • P.symmQuotient from rfl]
  exact hτ

end Graphplay
