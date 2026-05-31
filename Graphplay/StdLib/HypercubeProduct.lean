/-
# Graphplay.StdLib.HypercubeProduct

**Perfect state transfer on the hypercube `Q_n`, via the iterated Cartesian
product `Q_n = K₂^□n`.**

Christandl, Datta, Ekert and Landahl (*Perfect State Transfer in Quantum Spin
Networks*, Phys. Rev. A 71 (2005) 032312) observed that the `n`-dimensional
hypercube admits perfect state transfer between antipodal vertices at time
`τ = π/2`.  The cleanest route to this is the structural identity

`Q_n = K₂ □ K₂ □ ⋯ □ K₂`  (`n` Cartesian factors),

together with the Kronecker-product factorization of the quantum-walk evolution
on a Cartesian product proven in `Graphplay.Product.PST`
(`evolve_cartesianProduct_apply`).  The antipodal transfer flips *all* `n`
coordinate bits simultaneously, so it is driven — at every level of the
recursion — by single-edge transfer on the `K₂` factor and antipodal transfer on
the smaller cube, *at the same time* `τ = π/2`.  The factorization preserves the
time, so the single common `τ = π/2` works at every level.

## Construction

* `cartesianProduct_pst_both` — the **both-factors** transfer lemma: if the walk
  on `G` transfers `u₁ → u₂` and the walk on `H` transfers `w₁ → w₂` at the *same*
  time `τ`, then `G □ H` transfers `(u₁,w₁) → (u₂,w₂)` at `τ`.  (This is the
  variant needed for antipodal transfer, where *both* coordinates change — as
  opposed to the fixed-fibre `cartesianProduct_pst` in `Graphplay.Product.PST`,
  which keeps the `H`-coordinate fixed.)
* `K2` — the single edge `K₂` on `Fin 2`, with adjacency the Pauli-`X` matrix
  `!![0,1;1,0]`.
* `isPST_K2` — `‖K2.evolve (π/2) 0 1‖ = 1`.  The `(0,1)` entry of
  `exp(-(iπ/2)·X)` is `sinh(-(iπ/2)) = -i·sin(π/2) = -i`, modulus `1`.  Proven by
  diagonalizing `X = U·diag(1,-1)·U⁻¹` (Hadamard-type `U = !![1,1;1,-1]`) and
  applying `Matrix.exp_conj` and `Matrix.exp_diagonal`.
* `hypercubeP n` — the hypercube as the iterated Cartesian product, on the
  inductive vertex type `Fin 2 × (Fin 2 × ⋯)`; defined recursively by
  `hypercubeP 0 = ` a single vertex and `hypercubeP (n+1) = K₂ □ hypercubeP n`.
* `antipode n` — the all-bits-flip map.
* `isPST_hypercubeP_antipode` — **the headline theorem**: `Q_n` has PST between
  every vertex and its antipode at `τ = π/2`, by induction using
  `cartesianProduct_pst_both` (`K₂` factor: `isPST_K2`; cube factor: the
  inductive hypothesis).

The bitwise representation `hypercube` in `Graphplay.PST.GodsilRatio` is a
separate (coordinate-indexed) model; its antipodal-PST theorem is left as an
honest `sorry` there, awaiting the recognition of that bitwise adjacency as this
iterated Kronecker sum.  Here we build the iterated-Cartesian model directly and
prove PST unconditionally.
-/

import Graphplay.Product.PST
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

open scoped Matrix Kronecker
open NormedSpace

namespace Graphplay

namespace StdLib

namespace HypercubeProduct

/-! ## Step 1 : the both-factors Cartesian transfer lemma -/

variable {V : Type*} {W : Type*}
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- **Both-factors Cartesian transfer.**  If the quantum walk on `G` carries full
amplitude from `u₁` to `u₂` and the walk on `H` carries full amplitude from `w₁`
to `w₂`, both at the *same* time `τ`, then the Cartesian product `G □ H` has
perfect state transfer from `(u₁, w₁)` to `(u₂, w₂)` at `τ`.

This is the variant of `WeightedGraph.cartesianProduct_pst` in which *both*
coordinates move (the diagonal/antipodal case), and it is even simpler: the
product amplitude factors entrywise (`evolve_cartesianProduct_apply`) and
`norm_mul` multiplies the two unit moduli, `1 · 1 = 1`. -/
theorem cartesianProduct_pst_both (G : WeightedGraph V) (H : WeightedGraph W)
    {u₁ u₂ : V} {w₁ w₂ : W} {τ : ℝ}
    (hG : ‖G.evolve τ u₁ u₂‖ = 1) (hH : ‖H.evolve τ w₁ w₂‖ = 1) :
    IsPST (WeightedGraph.cartesianProduct G H) (u₁, w₁) (u₂, w₂) τ := by
  unfold IsPST
  rw [WeightedGraph.evolve_cartesianProduct_apply, norm_mul, hG, hH, mul_one]

/-! ## Step 2 : the single edge `K₂` and its antipodal PST -/

/-- The single edge `K₂` on `Fin 2`, with Pauli-`X` adjacency `!![0,1;1,0]`. -/
noncomputable def K2 : WeightedGraph (Fin 2) where
  adj := !![0, 1; 1, 0]
  herm := by
    unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  loopless := by
    intro v
    fin_cases v <;> simp

@[simp] theorem K2_adj : K2.adj = !![0, 1; 1, 0] := rfl

/-- A `2×2` diagonal matrix written as an explicit matrix literal:
`diagonal ![a, b] = !![a, 0; 0, b]`. -/
private theorem diag_fin_two (a b : ℂ) :
    (Matrix.diagonal ![a, b]) = !![a, 0; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The diagonalizing (Hadamard-type) matrix `U = !![1,1;1,-1]`, satisfying
`U² = 2·1`, hence invertible with `U⁻¹ = (1/2)·U`. -/
private def hadU : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

/-- `(1/2)·U` is a two-sided inverse of `U`: `U · ((1/2)·U) = 1`. -/
private theorem hadU_mul_half : hadU * ((1/2 : ℂ) • hadU) = 1 := by
  unfold hadU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU_isUnit : IsUnit hadU := by
  refine ⟨⟨hadU, (1/2 : ℂ) • hadU, hadU_mul_half, ?_⟩, rfl⟩
  -- the other side: ((1/2)•U) · U = 1, by the same 2×2 computation
  unfold hadU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU_inv : hadU⁻¹ = (1/2 : ℂ) • hadU := by
  apply Matrix.inv_eq_right_inv
  exact hadU_mul_half

/-- `(1/2) • U = !![1/2, 1/2; 1/2, -(1/2)]`, an explicit literal for `U⁻¹`. -/
private theorem half_smul_hadU :
    ((1/2 : ℂ) • hadU) = !![(1:ℂ)/2, 1/2; 1/2, -(1/2)] := by
  unfold hadU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The Pauli-`X` matrix diagonalizes as `X = U · diag(1,-1) · U⁻¹`. -/
private theorem X_eq_conj_diag :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU * (Matrix.diagonal ![1, -1]) * hadU⁻¹ := by
  rw [hadU_inv, diag_fin_two, half_smul_hadU]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

section ExpK2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The scalar multiple of `X` also diagonalizes:
`s • X = U · diag(s, -s) · U⁻¹`. -/
private theorem smul_X_eq_conj_diag (s : ℂ) :
    s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU * (Matrix.diagonal ![s, -s]) * hadU⁻¹ := by
  have hd : (Matrix.diagonal ![s, -s] : Matrix (Fin 2) (Fin 2) ℂ)
      = s • Matrix.diagonal ![1, -1] := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext k
    fin_cases k <;> simp
  rw [X_eq_conj_diag, hd, mul_smul_comm, smul_mul_assoc]

/-- `exp(s • X) = U · diag(exp s, exp (-s)) · U⁻¹`. -/
private theorem exp_smul_X (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = hadU * (Matrix.diagonal ![NormedSpace.exp s, NormedSpace.exp (-s)]) * hadU⁻¹ := by
  rw [smul_X_eq_conj_diag, Matrix.exp_conj _ _ hadU_isUnit, Matrix.exp_diagonal]
  have : (fun i => NormedSpace.exp (![s, -s] i))
      = (![NormedSpace.exp s, NormedSpace.exp (-s)] : Fin 2 → ℂ) := by
    funext k; fin_cases k <;> simp
  rw [Pi.exp_def, this]

/-- `exp(s • X) = !![…]` fully expanded as a `2×2` literal: the conjugation
`U · diag(exp s, exp (-s)) · U⁻¹` computed out. -/
private theorem exp_smul_X_lit (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      = !![(NormedSpace.exp s + NormedSpace.exp (-s)) / 2,
            (NormedSpace.exp s - NormedSpace.exp (-s)) / 2;
           (NormedSpace.exp s - NormedSpace.exp (-s)) / 2,
            (NormedSpace.exp s + NormedSpace.exp (-s)) / 2] := by
  rw [exp_smul_X, hadU_inv, diag_fin_two, half_smul_hadU]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- The `(0,1)` entry of `exp(s • X)` is `(exp s - exp (-s))/2 = sinh s`. -/
private theorem exp_smul_X_entry01 (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)) 0 1
      = (NormedSpace.exp s - NormedSpace.exp (-s)) / 2 := by
  rw [exp_smul_X_lit]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The `(1,0)` entry of `exp(s • X)` is also `(exp s - exp (-s))/2 = sinh s`
(`X` is symmetric, so the off-diagonal entries agree). -/
private theorem exp_smul_X_entry10 (s : ℂ) :
    NormedSpace.exp (s • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)) 1 0
      = (NormedSpace.exp s - NormedSpace.exp (-s)) / 2 := by
  rw [exp_smul_X_lit]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- At `s = -(iπ/2)` the off-diagonal value `(exp s - exp (-s))/2` equals `-i`:
`exp s = cos(π/2) - i·sin(π/2) = -i` and `exp (-s) = cos(π/2) + i·sin(π/2) = i`,
so `(-i - i)/2 = -i`. -/
private theorem offdiag_value_at_pi_div_two :
    (NormedSpace.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)))
        - NormedSpace.exp (-(-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))))) / 2
      = -Complex.I := by
  set s : ℂ := -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) with hs
  have hexp_neg_s : NormedSpace.exp (-s) = Complex.I := by
    -- `-s = i·(π/2)`; `exp(i·(π/2)) = cos(π/2) + i sin(π/2) = i`.
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
  ring

/-- **`K₂` has antipodal PST at `τ = π/2`.**  The `(0,1)` entry of the evolution
`exp(-(iπ/2)·X)` is `sinh(-(iπ/2)) = -i·sin(π/2) = -i`, of modulus `1`.

Citation: Christandl, Datta, Ekert, Landahl, Phys. Rev. A 71 (2005) 032312. -/
theorem isPST_K2 : IsPST K2 0 1 (Real.pi / 2) := by
  unfold IsPST WeightedGraph.evolve
  rw [K2_adj, exp_smul_X_entry01, offdiag_value_at_pi_div_two, norm_neg, Complex.norm_I]

/-- The reverse single-edge transfer on `K₂`: `‖K₂.evolve (π/2) 1 0‖ = 1`.  By
symmetry of `X`, the `(1,0)` entry equals the `(0,1)` entry, namely `-i`. -/
theorem isPST_K2_symm : IsPST K2 1 0 (Real.pi / 2) := by
  unfold IsPST WeightedGraph.evolve
  rw [K2_adj, exp_smul_X_entry10, offdiag_value_at_pi_div_two, norm_neg, Complex.norm_I]

end ExpK2

/-! ## Step 3 : the hypercube as an iterated Cartesian product -/

/-- The vertex type of the iterated-Cartesian hypercube `Q_n`: an `n`-fold
nested product `Fin 2 × (Fin 2 × ⋯ × Fin 1)`.  Base case `Fin 1` (a single
vertex), step `Fin 2 × HCVert n`. -/
abbrev HCVert : ℕ → Type
  | 0 => Fin 1
  | (n + 1) => Fin 2 × HCVert n

instance instFintypeHCVert : ∀ n, Fintype (HCVert n)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | (n + 1) => haveI := instFintypeHCVert n; inferInstanceAs (Fintype (Fin 2 × HCVert n))

instance instDecidableEqHCVert : ∀ n, DecidableEq (HCVert n)
  | 0 => inferInstanceAs (DecidableEq (Fin 1))
  | (n + 1) => haveI := instDecidableEqHCVert n; inferInstanceAs (DecidableEq (Fin 2 × HCVert n))

/-- The single-vertex graph on `Fin 1` (empty adjacency): the base `Q_0`. -/
noncomputable def trivialGraph : WeightedGraph (Fin 1) where
  adj := 0
  herm := by simp [Matrix.IsHermitian]
  loopless := by intro v; rfl

/-- The hypercube `Q_n` as the iterated Cartesian product of `n` copies of `K₂`:
`Q_0` is a single vertex, `Q_{n+1} = K₂ □ Q_n`. -/
noncomputable def hypercubeP : ∀ n, WeightedGraph (HCVert n)
  | 0 => trivialGraph
  | (n + 1) => WeightedGraph.cartesianProduct K2 (hypercubeP n)

/-- The antipode (all-bits-flip) map on `Q_n`: flip every coordinate.
On `Q_0` it is the identity (only one vertex); on `Q_{n+1}` it swaps the leading
bit (`0 ↔ 1`) and recurses on the tail. -/
def antipode : ∀ n, HCVert n → HCVert n
  | 0 => id
  | (n + 1) => fun p => (if p.1 = 0 then 1 else 0, antipode n p.2)

/-! ## Step 4 : antipodal PST on the hypercube -/

/-- On the single vertex `Q_0`, the (trivial) evolution returns full amplitude:
`‖(trivialGraph.evolve τ) v v‖ = 1`.  Since the adjacency is `0`, the evolution
is the identity matrix, whose `(v,v)` entry is `1`. -/
private theorem trivialGraph_evolve_diag (τ : ℝ) (v : Fin 1) :
    ‖trivialGraph.evolve τ v v‖ = 1 := by
  unfold WeightedGraph.evolve trivialGraph
  simp only [smul_zero, NormedSpace.exp_zero, Matrix.one_apply_eq, norm_one]

/-- **Christandl–Datta–Ekert–Landahl (2005): antipodal PST on the hypercube.**
For every `n` and every vertex `u` of the iterated-Cartesian hypercube `Q_n`,
the continuous-time quantum walk exhibits perfect state transfer from `u` to its
antipode at time `τ = π/2`.

The proof is by induction on `n`.  The base case `Q_0` is a single vertex with
trivial (identity) evolution.  The step `Q_{n+1} = K₂ □ Q_n` combines
single-edge antipodal transfer on the `K₂` factor (`isPST_K2`, flipping the
leading bit) with antipodal transfer on `Q_n` (the inductive hypothesis), via
the both-factors product lemma `cartesianProduct_pst_both`.  The *same* time
`τ = π/2` works at every level because the Kronecker factorization preserves the
evolution time.

Citation: Christandl, Datta, Ekert, Landahl, *Perfect State Transfer in Quantum
Spin Networks*, Phys. Rev. A 71 (2005) 032312. -/
theorem isPST_hypercubeP_antipode :
    ∀ (n : ℕ) (u : HCVert n), IsPST (hypercubeP n) u (antipode n u) (Real.pi / 2)
  | 0, u => by
    -- `Q_0`: single vertex; antipode is the identity, evolution returns amplitude 1.
    unfold IsPST hypercubeP antipode
    simp only [id_eq]
    exact trivialGraph_evolve_diag _ u
  | (n + 1), u => by
    -- `Q_{n+1} = K₂ □ Q_n`.  Write `u = (b, t)`.
    obtain ⟨b, t⟩ := u
    show IsPST (WeightedGraph.cartesianProduct K2 (hypercubeP n)) (b, t)
      (antipode (n + 1) (b, t)) (Real.pi / 2)
    -- The antipode of `(b, t)` is `(flip b, antipode n t)`.
    show IsPST (WeightedGraph.cartesianProduct K2 (hypercubeP n)) (b, t)
      ((if b = 0 then 1 else 0), antipode n t) (Real.pi / 2)
    -- `K₂` transfers `b → flip b` (both `0→1` and `1→0` are antipodal PST).
    have hK2 : ‖K2.evolve (Real.pi / 2) b (if b = 0 then 1 else 0)‖ = 1 := by
      fin_cases b
      · -- `b = 0`: `0 → 1`, exactly `isPST_K2`.
        simpa using isPST_K2
      · -- `b = 1`: `1 → 0`, the symmetric transfer.
        exact isPST_K2_symm
    -- `Q_n` transfers `t → antipode n t` by the inductive hypothesis.
    have hQ : ‖(hypercubeP n).evolve (Real.pi / 2) t (antipode n t)‖ = 1 :=
      isPST_hypercubeP_antipode n t
    exact cartesianProduct_pst_both K2 (hypercubeP n) hK2 hQ

end HypercubeProduct

end StdLib

end Graphplay
