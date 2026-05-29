/-
# Graphplay.Product.PST

**Perfect state transfer on Cartesian products of weighted graphs.**

The Cartesian (□) product `G □ H` has adjacency the *Kronecker sum*
`A_{G□H} = A_G ⊗ I + I ⊗ A_H`.  The two summands commute, and the exponential
of a Kronecker sum factors as a Kronecker product of exponentials,
`exp(A_G ⊗ I + I ⊗ A_H) = exp(A_G) ⊗ exp(A_H)`.  Hence the continuous-time
quantum-walk evolution factors:

`evolve (G □ H) τ = (evolve G τ) ⊗ₖ (evolve H τ)`,

so the `((u₁,w₁),(u₂,w₂))` amplitude is the product of the factor amplitudes.
Consequently perfect state transfer (PST) on `G` between `u₁` and `u₂`, together
with periodicity of `H` at `w` (`‖(evolve H τ) w w‖ = 1`), lifts to PST on the
product between `(u₁,w)` and `(u₂,w)` at the same time `τ`.

This is the Cartesian case of Ge–Greenberg–Pérez–Tamon, *Perfect state transfer,
graph products and equitable partitions* (arXiv:1009.1340).  The Christandl et
al. hypercube `Q_n = K₂^□n` is the iterated Cartesian product of this theorem,
so PST on `Q_n` is obtained by induction from PST on the single edge `K₂`.

## Main results

* `cartesianProduct_adj_eq_kroneckerSum` : `A_{G□H} = A_G ⊗ₖ 1 + 1 ⊗ₖ A_H`.
* `exp_kronecker_one` / `exp_one_kronecker` : `exp(M ⊗ₖ 1) = exp M ⊗ₖ 1` and the
  mirror image.  **Genuinely proven** (no `sorry`) by pushing the exponential
  power series through the continuous additive Kronecker maps.
* `evolve_cartesianProduct` : `evolve (G □ H) τ = evolve G τ ⊗ₖ evolve H τ`.
* `evolve_cartesianProduct_apply` : the entrywise factorization.
* `cartesianProduct_pst` : the PST-lifting headline theorem.
-/

import Graphplay.Product
import Graphplay.PST

open scoped Matrix Kronecker
open NormedSpace

namespace Graphplay

namespace WeightedGraph

variable {V : Type*} {W : Type*}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## Step 1 : the Cartesian adjacency is a Kronecker sum -/

/-- The Cartesian-product adjacency matrix is the **Kronecker sum**
`A_{G□H} = A_G ⊗ₖ 1 + 1 ⊗ₖ A_H`.  This relates the entrywise definition in
`Graphplay.Product` (an `if … then … else 0` on each coordinate) to Mathlib's
`Matrix.kronecker` of the identity matrices. -/
theorem cartesianProduct_adj_eq_kroneckerSum (G : WeightedGraph V) (H : WeightedGraph W) :
    (cartesianProduct G H).adj = G.adj ⊗ₖ (1 : Matrix W W ℂ) + (1 : Matrix V V ℂ) ⊗ₖ H.adj := by
  ext p q
  obtain ⟨v₁, w₁⟩ := p
  obtain ⟨v₂, w₂⟩ := q
  rw [Matrix.add_apply, Matrix.kronecker_apply, Matrix.kronecker_apply,
    cartesianProduct_adj_eq]
  -- `(A_G ⊗ₖ 1)` term: `G v₁ v₂ * (1 w₁ w₂)`; `1 w₁ w₂ = if w₁ = w₂ then 1 else 0`.
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases hw : w₁ = w₂ <;> by_cases hv : v₁ = v₂ <;>
    simp [hw, hv]

/-! ## Step 2 : the two summands commute, and scaling distributes -/

/-- The two Kronecker-sum summands commute: `(A_G ⊗ₖ 1) * (1 ⊗ₖ A_H) =
A_G ⊗ₖ A_H = (1 ⊗ₖ A_H) * (A_G ⊗ₖ 1)`.  Proven by `mul_kronecker_mul`
(`(A*B) ⊗ₖ (C*D) = (A⊗ₖC) * (B⊗ₖD)`) and unit laws. -/
theorem kroneckerSum_summands_commute (G : WeightedGraph V) (H : WeightedGraph W) :
    Commute (G.adj ⊗ₖ (1 : Matrix W W ℂ)) ((1 : Matrix V V ℂ) ⊗ₖ H.adj) := by
  unfold Commute SemiconjBy
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

/-! ## A genuinely-proven `exp(M ⊗ₖ 1) = exp M ⊗ₖ 1`

We push the exponential power series through the continuous additive group
homomorphism `M ↦ M ⊗ₖ 1`, mirroring `EquitablePartition.exp_smul_adj_mul_cellEmbed`
in `Graphplay.PST`.  The two key inputs are
* `kronecker_one_pow` : `(M ⊗ₖ 1) ^ n = M ^ n ⊗ₖ 1`, and
* continuity of right-Kronecker-by-`1`.
-/

section ExpKronecker

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `(M ⊗ₖ 1) ^ n = (M ^ n) ⊗ₖ 1`.  Induction with `mul_kronecker_mul` and
`one_mul`/`one_kronecker_one`. -/
theorem kronecker_one_pow (M : Matrix V V ℂ) (n : ℕ) :
    (M ⊗ₖ (1 : Matrix W W ℂ)) ^ n = (M ^ n) ⊗ₖ (1 : Matrix W W ℂ) := by
  induction n with
  | zero => simp [Matrix.one_kronecker_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- `(1 ⊗ₖ M) ^ n = 1 ⊗ₖ (M ^ n)`. -/
theorem one_kronecker_pow (M : Matrix W W ℂ) (n : ℕ) :
    ((1 : Matrix V V ℂ) ⊗ₖ M) ^ n = (1 : Matrix V V ℂ) ⊗ₖ (M ^ n) := by
  induction n with
  | zero => simp [Matrix.one_kronecker_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Right-Kronecker by the identity, `M ↦ M ⊗ₖ 1`, is continuous. -/
theorem continuous_kronecker_one :
    Continuous (fun M : Matrix V V ℂ => M ⊗ₖ (1 : Matrix W W ℂ)) := by
  refine continuous_matrix ?_
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  -- entry `(i₁,i₂)(j₁,j₂)` is `M i₁ j₁ * (1 : Matrix W W ℂ) i₂ j₂`, continuous in `M`.
  simp only [Matrix.kronecker_apply]
  exact (continuous_id.matrix_elem i₁ j₁).mul continuous_const

/-- Left-Kronecker by the identity, `M ↦ 1 ⊗ₖ M`, is continuous. -/
theorem continuous_one_kronecker :
    Continuous (fun M : Matrix W W ℂ => (1 : Matrix V V ℂ) ⊗ₖ M) := by
  refine continuous_matrix ?_
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.kronecker_apply]
  exact continuous_const.mul (continuous_id.matrix_elem i₂ j₂)

/-- **`exp(M ⊗ₖ 1) = exp M ⊗ₖ 1`.**  The exponential power series for `M ⊗ₖ 1`
is pushed term-by-term through the continuous additive homomorphism
`X ↦ X ⊗ₖ 1`; the `n`-th term maps to `(n!)⁻¹ • (M^n ⊗ₖ 1)` by `kronecker_one_pow`
and `smul_kronecker`, which is the image of the `n`-th term of the series for
`M`.  Uniqueness of sums concludes. -/
theorem exp_kronecker_one (M : Matrix V V ℂ) :
    NormedSpace.exp (M ⊗ₖ (1 : Matrix W W ℂ))
      = (NormedSpace.exp M) ⊗ₖ (1 : Matrix W W ℂ) := by
  -- The continuous additive hom `X ↦ X ⊗ₖ 1`.
  let φ : Matrix V V ℂ →+ Matrix (V × W) (V × W) ℂ :=
    { toFun := fun X => X ⊗ₖ (1 : Matrix W W ℂ)
      map_zero' := Matrix.zero_kronecker _
      map_add' := fun X Y => Matrix.add_kronecker X Y _ }
  have hφc : Continuous φ := continuous_kronecker_one
  -- exp series, as `HasSum`s, for `M ⊗ₖ 1` and for `M`.
  have hMK : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • (M ⊗ₖ (1 : Matrix W W ℂ)) ^ n)
      (NormedSpace.exp (M ⊗ₖ (1 : Matrix W W ℂ))) := exp_series_hasSum_exp' _
  have hM : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n) (NormedSpace.exp M) :=
    exp_series_hasSum_exp' _
  -- Map the `M`-series through `φ`.
  have hMφ := hM.map φ hφc
  -- Termwise: `φ ((n!)⁻¹ • M^n) = (n!)⁻¹ • (M ⊗ₖ 1)^n`.
  have hterm : (φ ∘ fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n)
      = fun n => (Nat.factorial n : ℂ)⁻¹ • (M ⊗ₖ (1 : Matrix W W ℂ)) ^ n := by
    funext n
    show ((Nat.factorial n : ℂ)⁻¹ • M ^ n) ⊗ₖ (1 : Matrix W W ℂ)
      = (Nat.factorial n : ℂ)⁻¹ • (M ⊗ₖ (1 : Matrix W W ℂ)) ^ n
    rw [Matrix.smul_kronecker, kronecker_one_pow]
  rw [hterm] at hMφ
  -- `φ (exp M) = exp (M ⊗ₖ 1)` by uniqueness of sums.
  exact (hMφ.unique hMK).symm

/-- **`exp(1 ⊗ₖ M) = 1 ⊗ₖ exp M`** — the mirror image of `exp_kronecker_one`. -/
theorem exp_one_kronecker (M : Matrix W W ℂ) :
    NormedSpace.exp ((1 : Matrix V V ℂ) ⊗ₖ M)
      = (1 : Matrix V V ℂ) ⊗ₖ (NormedSpace.exp M) := by
  let ψ : Matrix W W ℂ →+ Matrix (V × W) (V × W) ℂ :=
    { toFun := fun X => (1 : Matrix V V ℂ) ⊗ₖ X
      map_zero' := Matrix.kronecker_zero _
      map_add' := fun X Y => Matrix.kronecker_add _ X Y }
  have hψc : Continuous ψ := continuous_one_kronecker
  have hMK : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • ((1 : Matrix V V ℂ) ⊗ₖ M) ^ n)
      (NormedSpace.exp ((1 : Matrix V V ℂ) ⊗ₖ M)) := exp_series_hasSum_exp' _
  have hM : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n) (NormedSpace.exp M) :=
    exp_series_hasSum_exp' _
  have hMψ := hM.map ψ hψc
  have hterm : (ψ ∘ fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n)
      = fun n => (Nat.factorial n : ℂ)⁻¹ • ((1 : Matrix V V ℂ) ⊗ₖ M) ^ n := by
    funext n
    show (1 : Matrix V V ℂ) ⊗ₖ ((Nat.factorial n : ℂ)⁻¹ • M ^ n)
      = (Nat.factorial n : ℂ)⁻¹ • ((1 : Matrix V V ℂ) ⊗ₖ M) ^ n
    rw [Matrix.kronecker_smul, one_kronecker_pow]
  rw [hterm] at hMψ
  exact (hMψ.unique hMK).symm

/-! ## Step 3 : the evolution factors as a Kronecker product -/

/-- **The Cartesian-product quantum walk factors:**
`evolve (G □ H) τ = evolve G τ ⊗ₖ evolve H τ`.

The Hamiltonian `-(iτ)·A_{G□H}` splits as the sum of two commuting Kronecker
terms (steps 1–2); `Matrix.exp_add_of_commute` turns the exponential into a
product, each factor is a Kronecker exponential (`exp_kronecker_one`,
`exp_one_kronecker`), and `mul_kronecker_mul` recombines them. -/
theorem evolve_cartesianProduct (G : WeightedGraph V) (H : WeightedGraph W) (τ : ℝ) :
    (cartesianProduct G H).evolve τ = (G.evolve τ) ⊗ₖ (H.evolve τ) := by
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  -- Unfold `evolve` and rewrite the Hamiltonian as a Kronecker sum.
  show NormedSpace.exp (s • (cartesianProduct G H).adj)
      = NormedSpace.exp (s • G.adj) ⊗ₖ NormedSpace.exp (s • H.adj)
  rw [cartesianProduct_adj_eq_kroneckerSum]
  -- `s • (X + Y) = s • X + s • Y`, and the scaled summands still commute.
  rw [smul_add]
  -- Name the scaled summands.
  set P : Matrix (V × W) (V × W) ℂ := s • (G.adj ⊗ₖ (1 : Matrix W W ℂ)) with hP
  set Q : Matrix (V × W) (V × W) ℂ := s • ((1 : Matrix V V ℂ) ⊗ₖ H.adj) with hQ
  have hcomm : Commute P Q := by
    rw [hP, hQ]
    exact ((kroneckerSum_summands_commute G H).smul_left s).smul_right s
  rw [Matrix.exp_add_of_commute P Q hcomm]
  -- Factor each scaled Kronecker term through the identity.
  have hPexp : NormedSpace.exp P
      = NormedSpace.exp (s • G.adj) ⊗ₖ (1 : Matrix W W ℂ) := by
    rw [hP, ← Matrix.smul_kronecker, exp_kronecker_one]
  have hQexp : NormedSpace.exp Q
      = (1 : Matrix V V ℂ) ⊗ₖ NormedSpace.exp (s • H.adj) := by
    rw [hQ, ← Matrix.kronecker_smul, exp_one_kronecker]
  rw [hPexp, hQexp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-! ## Step 4 : the entrywise factorization -/

/-- The `((u₁,w₁),(u₂,w₂))` amplitude of the product walk factors as the product
of the two factor amplitudes. -/
theorem evolve_cartesianProduct_apply (G : WeightedGraph V) (H : WeightedGraph W) (τ : ℝ)
    (u₁ w₁ u₂ w₂) :
    (cartesianProduct G H).evolve τ (u₁, w₁) (u₂, w₂)
      = (G.evolve τ) u₁ u₂ * (H.evolve τ) w₁ w₂ := by
  rw [evolve_cartesianProduct, Matrix.kronecker_apply]

/-! ## Step 5 : the PST-lifting headline theorem -/

/-- **Cartesian product preserves PST** (GGPT, arXiv:1009.1340, Cartesian case).

If `G` has perfect state transfer from `u₁` to `u₂` at time `τ`, and `H` is
*periodic at `w`* at the same time (`‖(evolve H τ) w w‖ = 1`, i.e. the walk on
`H` returns full amplitude to `w`), then the Cartesian product `G □ H` has
perfect state transfer from `(u₁, w)` to `(u₂, w)` at time `τ`.

The proof is the entrywise factorization (`evolve_cartesianProduct_apply`)
combined with `norm_mul`: the product amplitude has modulus
`‖(evolve G τ) u₁ u₂‖ · ‖(evolve H τ) w w‖ = 1 · 1 = 1`.

The periodicity hypothesis is the honest, minimal assumption: GGPT derive it for
regular `H` from a spectral lattice condition, but stated directly it makes this
the clean, fully-general transfer theorem.  Iterating it from the single edge
`K₂` (with `H = K₂^□(n-1)` periodic at any vertex) yields PST on the hypercube
`Q_n = K₂^□n`. -/
theorem cartesianProduct_pst (G : WeightedGraph V) (H : WeightedGraph W)
    {u₁ u₂ : V} {w : W} {τ : ℝ}
    (hG : IsPST G u₁ u₂ τ) (hH : ‖(H.evolve τ) w w‖ = 1) :
    IsPST (cartesianProduct G H) (u₁, w) (u₂, w) τ := by
  unfold IsPST at hG ⊢
  rw [evolve_cartesianProduct_apply, norm_mul, hG, hH, mul_one]

/-- A convenient repackaging: PST on `G` between `u₁` and `u₂` together with
periodicity of `H` at `w` gives PST on the product.  (Definitionally identical
to `cartesianProduct_pst`; provided as a named "periodicity" phrasing.) -/
theorem cartesianProduct_pst_of_periodic (G : WeightedGraph V) (H : WeightedGraph W)
    {u₁ u₂ : V} {w : W} {τ : ℝ}
    (hG : IsPST G u₁ u₂ τ) (hH : IsPST H w w τ ∨ ‖(H.evolve τ) w w‖ = 1) :
    IsPST (cartesianProduct G H) (u₁, w) (u₂, w) τ := by
  have hHw : ‖(H.evolve τ) w w‖ = 1 := hH.elim (fun h => h) (fun h => h)
  exact cartesianProduct_pst G H hG hHw

end ExpKronecker

end WeightedGraph

end Graphplay
