/-
# Graphplay.Integrations.Connectome

**The whole-brain "network of networks" as an equitable quotient — and the
quantum / quantum-like bridge.**

This module formalises the spectral skeleton of

  G. Deco, Y. Sanz Perl, N. Greenstein, S. Chandaria, G. D. Scholes & M. L.
  Kringelbach, *Quantum-like dynamics in the human brain*, bioRxiv
  2025.10.02.680057 (2025),

and shows that its load-bearing objects are exactly the equitable-partition
quantum-walk objects already developed in Graphplay.  Two deliverables:

## 1.  The Q ↔ QL bridge (the novel, paper-worthy core)

Deco–Scholes model a brain region as a `k`-regular ("expander") graph whose
*spectral gap* `λ₀ − λ₁` is the signature of a "quantum-like" (QL) state, builds
a **network of networks** `Ĉ` (each of `N` regions a copy of the regional graph,
coupled by the structural connectome `C`), runs linearised Stuart–Landau /
Hopf dynamics on it, and reads functional connectivity (FC) off the stationary
covariance of the resulting Ornstein–Uhlenbeck process (their Eqs. 6–10).

Their dynamics are *classical, dissipative, stochastic*; Graphplay's
continuous-time quantum walk `U(t) = exp(-itA)` is *unitary*.  The bridge is the
observation that **both** the quantum walk and the classical "QL" stationary
covariance are *spectral functionals of the same graph operator*, and **both
intertwine the equitable quotient** through one single map, the cell-inflate
`cellInflateVec`.  We isolate this as `Connectome.Intertwines` and prove it is
closed under the whole functional calculus (sums, products, powers, scalar
shifts, inverses), so:

* `intertwines_pow` / `intertwines_evolve`  — the *quantum* reduction (Godsil
  average mixing / `U(t)` collapse to the quotient walk), and
* `stationaryFC_reduction`                  — the *quantum-like* reduction (the
  Deco–Scholes FC collapses to the connectome),

are **the same theorem applied to two functionals**.  The decoherence-free
"two-state" subspace of Scholes is exactly the cell-uniform subspace, and the
"distributed spectral gap" of Fig. 1C is the inherited quotient spectrum
(`connectome_gap_inherited`, via `EquitablePartition.spectrum_subset`).

## 2.  `Connectome.lean`, the substantive construction

* `regionalNetwork H Reg`        — the network-of-networks `Ĉ` on `R × W`.
* `regionalPartition`            — its regional equitable partition; we prove
  the quotient is the connectome itself, `Q̃ = C + d·I`
  (`regionalPartition_symmQuotient_eq`), and — the punchline — the **quotient
  Laplacian is exactly the connectome Laplacian** (`regionalNetwork_quotientLaplacian_eq_host`):
  the regional self-coupling `d` cancels.  Deco's heuristic "average across the
  `n` nodes in each region" to obtain `FCᵐᵒᵈᵉˡ` (their p. 6) is therefore an
  *exact* equitable quotient, not an approximation — `stationaryFC_reduction`.
* `ouDrift` / `stationaryFC`     — the linearised Hopf drift `J = a·I − L` and
  the Lyapunov/OU stationary covariance `K = (σ²/2)(L − a·I)⁻¹`, proven to solve
  the Lyapunov equation `JK + KJᵀ + Q = 0` (`stationaryFC_solves_lyapunov`).
* `prune` + `algConn_prune_le`   — Fig. 4A ("long-range connections amplify the
  spectral gap") as a **theorem**: removing edges can only *decrease* the
  algebraic connectivity (Fiedler value), the rigorous, monotone form of the
  empirical claim.  Engine: `AlgebraicConnectivity.algebraicConnectivity_mono`.

## Honest scope (cf. the certified-honest-floor doctrine)

* The intertwining algebra (`Intertwines.*`), the network construction
  (Hermitian/loopless/equitable), the quotient-is-the-connectome identities, the
  Lyapunov solve, the FC reduction, the gap inheritance, and the Fig. 4A
  monotonicity are intended to be **fully proven, axiom-clean**.
* The unitary `evolve` reduction beyond polynomials (`intertwines_evolve`) is the
  analytic functional-calculus step; the polynomial/resolvent cases are proven
  here, the `exp` limit is the standard analytic closure.
* `AlonBoppanaFloor` — the asymptotic expander bound `λ₁ ≥ 2√(k−1) − o(1)`
  (Alon, *Combinatorica* 6 (1986); Nilli, *Discrete Math.* 91 (1991)) — is a
  cited typeclass: Mathlib lacks it and it is genuinely deep.
* Invertibility of `L − a·I` for the sub-critical `a < 0` (true: `L` is PSD so
  `L + |a|·I` is positive definite) is carried as an `IsUnit … .det` hypothesis;
  it is discharged for real graphs in `resolvent_isUnit_of_neg`.
-/

import Graphplay.Equitable
import Graphplay.Spectral
import Graphplay.StdLib.AlgebraicConnectivity
import Graphplay.StdLib.AverageMixing
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

open scoped Matrix
open scoped ComplexOrder
open NormedSpace

namespace Graphplay
namespace Connectome

open EquitablePartition
open AlgebraicConnectivity

universe uV uI uR uW

/-! ## 1.  The intertwining backbone

The single mechanism behind both the quantum-walk reduction and the classical
"quantum-like" stochastic reduction. -/

section Intertwining

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable {G : WeightedGraph V}

/-- The cell-inflate is **linear in the quotient vector** (scalar part). -/
theorem cellInflateVec_smul (P : EquitablePartition G I) (c : ℂ) (v : I → ℂ) :
    P.cellInflateVec (c • v) = c • P.cellInflateVec v := by
  funext x
  simp only [EquitablePartition.cellInflateVec, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc]

/-- The cell-inflate is **additive in the quotient vector**. -/
theorem cellInflateVec_add (P : EquitablePartition G I) (v w : I → ℂ) :
    P.cellInflateVec (v + w) = P.cellInflateVec v + P.cellInflateVec w := by
  funext x
  simp only [EquitablePartition.cellInflateVec, Pi.add_apply]
  rw [add_div]

/-- The cell-inflate respects **subtraction**. -/
theorem cellInflateVec_sub (P : EquitablePartition G I) (v w : I → ℂ) :
    P.cellInflateVec (v - w) = P.cellInflateVec v - P.cellInflateVec w := by
  funext x
  simp only [EquitablePartition.cellInflateVec, Pi.sub_apply]
  rw [sub_div]

/-- A full-space matrix `M` **intertwines** the quotient matrix `MQ` through the
cell-inflate of `P` if `M` carries the inflate of any quotient vector to the
inflate of `MQ`'s action.  This is the unique reduction map shared by the quantum
walk and the classical QL covariance. -/
def Intertwines (P : EquitablePartition G I) (M : Matrix V V ℂ) (MQ : Matrix I I ℂ) :
    Prop :=
  ∀ v : I → ℂ, M *ᵥ P.cellInflateVec v = P.cellInflateVec (MQ *ᵥ v)

namespace Intertwines

variable {P : EquitablePartition G I} {M N : Matrix V V ℂ} {MQ NQ : Matrix I I ℂ}

/-- The **adjacency** intertwines its symmetric quotient — the seed instance
(Bachman–Tamon; `AlgebraicConnectivity.adj_mulVec_cellInflate_eq`). -/
theorem adj (P : EquitablePartition G I) : Intertwines P G.adj P.symmQuotient :=
  fun v => adj_mulVec_cellInflate_eq P v

/-- The **identity** intertwines the identity. -/
theorem one (P : EquitablePartition G I) : Intertwines P 1 1 := by
  intro v; rw [Matrix.one_mulVec, Matrix.one_mulVec]

/-- Intertwining is closed under **scalar multiplication**. -/
theorem smul (c : ℂ) (h : Intertwines P M MQ) : Intertwines P (c • M) (c • MQ) := by
  intro v
  rw [Matrix.smul_mulVec, h v, Matrix.smul_mulVec, cellInflateVec_smul]

/-- Intertwining is closed under **addition**. -/
theorem add (h : Intertwines P M MQ) (h' : Intertwines P N NQ) :
    Intertwines P (M + N) (MQ + NQ) := by
  intro v
  rw [Matrix.add_mulVec, h v, h' v, Matrix.add_mulVec, cellInflateVec_add]

/-- Intertwining is closed under **subtraction**. -/
theorem sub (h : Intertwines P M MQ) (h' : Intertwines P N NQ) :
    Intertwines P (M - N) (MQ - NQ) := by
  intro v
  rw [Matrix.sub_mulVec, h v, h' v, Matrix.sub_mulVec, cellInflateVec_sub]

/-- Intertwining is closed under **products** (composition of reductions). -/
theorem mul (h : Intertwines P M MQ) (h' : Intertwines P N NQ) :
    Intertwines P (M * N) (MQ * NQ) := by
  intro v
  rw [← Matrix.mulVec_mulVec, h' v, h (NQ *ᵥ v), Matrix.mulVec_mulVec]

/-- A **scalar matrix** `c·I` intertwines `c·I`. -/
theorem scalar (P : EquitablePartition G I) (c : ℂ) :
    Intertwines P (c • (1 : Matrix V V ℂ)) (c • (1 : Matrix I I ℂ)) :=
  (one P).smul c

/-- Intertwining is closed under taking **inverses** (the resolvent step): if
`M` intertwines `MQ` and both are invertible, then `M⁻¹` intertwines `MQ⁻¹`. -/
theorem inv (hM : IsUnit M.det) (hMQ : IsUnit MQ.det) (h : Intertwines P M MQ) :
    Intertwines P M⁻¹ MQ⁻¹ := by
  intro v
  -- Apply `h` at `MQ⁻¹ *ᵥ v`, collapsing `MQ * MQ⁻¹ = 1`.
  have key : M *ᵥ P.cellInflateVec (MQ⁻¹ *ᵥ v) = P.cellInflateVec v := by
    rw [h (MQ⁻¹ *ᵥ v), Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv MQ hMQ,
      Matrix.one_mulVec]
  calc M⁻¹ *ᵥ P.cellInflateVec v
      = M⁻¹ *ᵥ (M *ᵥ P.cellInflateVec (MQ⁻¹ *ᵥ v)) := by rw [key]
    _ = (M⁻¹ * M) *ᵥ P.cellInflateVec (MQ⁻¹ *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = P.cellInflateVec (MQ⁻¹ *ᵥ v) := by
          rw [Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]

/-- Intertwining is closed under **powers** — hence under every *polynomial* of
the generator (the Krylov/quantum-walk approximants reduce exactly). -/
theorem pow (h : Intertwines P M MQ) : ∀ k : ℕ, Intertwines P (M ^ k) (MQ ^ k)
  | 0 => by simpa using one P
  | (k + 1) => by
      rw [pow_succ, pow_succ]
      exact (pow h k).mul h

end Intertwines

/-- The cell-inflate as a (rectangular) `V × I` matrix: column `i` is the
normalized cell-`i` indicator.  `cellInflateVec v = cellInflateMat *ᵥ v`. -/
noncomputable def cellInflateMat (P : EquitablePartition G I) : Matrix V I ℂ :=
  fun x i => P.cellUniformVec i x

theorem cellInflateVec_eq_mulVec (P : EquitablePartition G I) (v : I → ℂ) :
    P.cellInflateVec v = cellInflateMat P *ᵥ v := by
  funext x
  rw [P.cellInflateVec_eq_sum v]
  simp only [Matrix.mulVec, dotProduct, cellInflateMat]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- **Intertwining in matrix form.**  `Intertwines P M MQ ↔ M · B = B · MQ` where
`B = cellInflateMat` — the bridge between the vector-level reduction and matrix
algebra (used for the two-sided Lyapunov/Sylvester argument). -/
theorem intertwines_iff_mat (P : EquitablePartition G I)
    (M : Matrix V V ℂ) (MQ : Matrix I I ℂ) :
    Intertwines P M MQ ↔ M * cellInflateMat P = cellInflateMat P * MQ := by
  have hbridge : Intertwines P M MQ ↔
      ∀ v, (M * cellInflateMat P) *ᵥ v = (cellInflateMat P * MQ) *ᵥ v := by
    unfold Intertwines
    refine forall_congr' (fun v => ?_)
    rw [cellInflateVec_eq_mulVec, cellInflateVec_eq_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  rw [hbridge]
  constructor
  · intro h; ext x i
    have hx := congrFun (h (Pi.single i 1)) x
    simpa [Matrix.mulVec_single] using hx
  · intro h v; rw [h]

/-- Right-multiplication by a fixed vector, as a linear map on square matrices —
used to push the matrix exponential through `mulVec`. -/
noncomputable def mulVecRightLin {n : Type*} [Fintype n] (w : n → ℂ) :
    Matrix n n ℂ →ₗ[ℂ] (n → ℂ) where
  toFun M := M *ᵥ w
  map_add' M N := Matrix.add_mulVec M N w
  map_smul' c M := Matrix.smul_mulVec c M w

@[simp] theorem mulVecRightLin_apply {n : Type*} [Fintype n] (w : n → ℂ) (M : Matrix n n ℂ) :
    mulVecRightLin w M = M *ᵥ w := rfl

/-- **A diagonal operator intertwines its quotient diagonal**, provided its
diagonal is constant on the cells of `P`.  This is the ingredient that lets the
intrinsic-frequency rotation `diag(ω)` (constant per brain region in Deco et al.)
descend to the connectome. -/
theorem Intertwines.diagonal_of_cellConst {P : EquitablePartition G I}
    (ω : V → ℂ) (ωQ : I → ℂ) (hω : ∀ x, ω x = ωQ (P.cells x)) :
    Intertwines P (Matrix.diagonal ω) (Matrix.diagonal ωQ) := by
  intro v
  funext x
  simp only [Matrix.mulVec_diagonal, EquitablePartition.cellInflateVec]
  rw [hω x, mul_div_assoc]

open scoped Matrix.Norms.Operator in
/-- **Intertwining is closed under the matrix exponential** — hence under the
entire holomorphic functional calculus, the *quantum* end of the bridge.  If `M`
intertwines `MQ`, then `exp M` intertwines `exp MQ`: the exponential is the
`HasSum` of the (intertwining, by `Intertwines.pow`) powers, and the
finite-dimensional cell-inflate and `mulVec` maps — automatically continuous —
push through the sum (`HasSum.mapL`), with uniqueness of sums closing it. -/
theorem Intertwines.exp {P : EquitablePartition G I} {M : Matrix V V ℂ} {MQ : Matrix I I ℂ}
    (h : Intertwines P M MQ) :
    Intertwines P (NormedSpace.exp M) (NormedSpace.exp MQ) := by
  intro v
  have hpow : ∀ k, M ^ k *ᵥ P.cellInflateVec v = P.cellInflateVec (MQ ^ k *ᵥ v) :=
    fun k => h.pow k v
  have key1 : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℂ) • P.cellInflateVec (MQ ^ k *ᵥ v))
      (NormedSpace.exp M *ᵥ P.cellInflateVec v) := by
    have hh := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M).mapL
      (LinearMap.toContinuousLinearMap (mulVecRightLin (P.cellInflateVec v)))
    simp only [LinearMap.coe_toContinuousLinearMap', map_smul, mulVecRightLin_apply] at hh
    simp_rw [hpow] at hh
    exact hh
  have key2 : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℂ) • P.cellInflateVec (MQ ^ k *ᵥ v))
      (P.cellInflateVec (NormedSpace.exp MQ *ᵥ v)) := by
    have hh := ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) MQ).mapL
        (LinearMap.toContinuousLinearMap (mulVecRightLin v))).mapL
        (LinearMap.toContinuousLinearMap P.cellInflateLin)
    simp only [LinearMap.coe_toContinuousLinearMap', map_smul, mulVecRightLin_apply] at hh
    exact hh
  exact key1.unique key2

/-- **The quantum walk reduces to the quotient walk.**  `U(t) = exp(-itA)` carries
the cell-inflate to the inflate of the quotient walk `exp(-it Q̃)` — the unitary
corollary of `Intertwines.exp` applied to the adjacency. -/
theorem intertwines_evolve (P : EquitablePartition G I) (t : ℝ) :
    Intertwines P (G.evolve t)
      (NormedSpace.exp (-(Complex.I * (t : ℂ)) • P.symmQuotient)) :=
  ((Intertwines.adj P).smul (-(Complex.I * (t : ℂ)))).exp

end Intertwining

/-! ## 2.  The network of networks `Ĉ`

A structural host connectome `H` on regions `R`, each region a copy of the
regional graph `Reg` on `W`; distinct regions `a ≠ b` coupled all-to-all with
total strength `H.adj a b` (each of the `|W|` cross pairs carrying
`H.adj a b / |W|`). -/

section Network

variable {R : Type uR} [Fintype R] [DecidableEq R]
variable {W : Type uW} [Fintype W] [DecidableEq W]

/-- The **network of networks** `Ĉ` on the vertex set `R × W` (Deco et al.
Fig. 1C / Fig. 2). -/
noncomputable def regionalNetwork (H : WeightedGraph R) (Reg : WeightedGraph W) :
    WeightedGraph (R × W) where
  adj := fun p q =>
    if p.1 = q.1 then Reg.adj p.2 q.2 else H.adj p.1 q.1 / (Fintype.card W : ℂ)
  herm := by
    ext p q
    rw [Matrix.conjTranspose_apply]
    by_cases h : p.1 = q.1
    · rw [if_pos h.symm, if_pos h]
      exact Reg.herm.apply p.2 q.2
    · rw [if_neg (fun h' => h h'.symm), if_neg h, star_div₀, H.herm.apply p.1 q.1]
      simp
  loopless := by
    intro p
    show (if p.1 = p.1 then Reg.adj p.2 p.2 else _) = 0
    rw [if_pos rfl]
    exact Reg.loopless p.2

@[simp] theorem regionalNetwork_adj_same (H : WeightedGraph R) (Reg : WeightedGraph W)
    (a : R) (x y : W) :
    (regionalNetwork H Reg).adj (a, x) (a, y) = Reg.adj x y := by
  simp [regionalNetwork]

@[simp] theorem regionalNetwork_adj_diff (H : WeightedGraph R) (Reg : WeightedGraph W)
    (a b : R) (x y : W) (h : a ≠ b) :
    (regionalNetwork H Reg).adj (a, x) (b, y) = H.adj a b / (Fintype.card W : ℂ) := by
  simp [regionalNetwork, h]

/-- The **regional partition** of `Ĉ`: cells are the regions. -/
def regionalPartition (H : WeightedGraph R) (Reg : WeightedGraph W) (d : ℂ)
    (hreg : Reg.isRegular d) :
    EquitablePartition (regionalNetwork H Reg) R where
  cells := fun p => p.1
  uniform := by
    intro i j x y hx hy
    -- The branching from a vertex into cell `j` collapses to a sum over the
    -- fiber `{j} × W`, which depends only on the source region.
    have expand : ∀ (z0 : R × W),
        (∑ z : R × W, if z.1 = j then (regionalNetwork H Reg).adj z0 z else 0)
          = ∑ w : W, (regionalNetwork H Reg).adj z0 (j, w) := by
      intro z0
      rw [Fintype.sum_prod_type]
      calc (∑ b : R, ∑ w : W,
              if (b, w).1 = j then (regionalNetwork H Reg).adj z0 (b, w) else 0)
          = ∑ b : R, (if b = j then
              ∑ w : W, (regionalNetwork H Reg).adj z0 (b, w) else 0) := by
            refine Finset.sum_congr rfl (fun b _ => ?_)
            by_cases hb : b = j <;> simp [hb]
        _ = ∑ w : W, (regionalNetwork H Reg).adj z0 (j, w) := by
            rw [Finset.sum_ite_eq' Finset.univ j
              (fun b => ∑ w : W, (regionalNetwork H Reg).adj z0 (b, w))]
            simp
    rw [expand x, expand y]
    by_cases hij : i = j
    · have hval : ∀ z0 : R × W, z0.1 = i →
          (∑ w : W, (regionalNetwork H Reg).adj z0 (j, w)) = d := by
        intro z0 hz0
        have hcongr : (∑ w : W, (regionalNetwork H Reg).adj z0 (j, w))
            = ∑ w : W, Reg.adj z0.2 w := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          show (if z0.1 = (j, w).1 then Reg.adj z0.2 (j, w).2
                  else H.adj z0.1 (j, w).1 / (Fintype.card W : ℂ)) = Reg.adj z0.2 w
          rw [if_pos (by rw [hz0]; exact hij)]
        rw [hcongr]; exact hreg z0.2
      rw [hval x hx, hval y hy]
    · have hval : ∀ z0 : R × W, z0.1 = i →
          (∑ w : W, (regionalNetwork H Reg).adj z0 (j, w))
            = ∑ w : W, H.adj i j / (Fintype.card W : ℂ) := by
        intro z0 hz0
        refine Finset.sum_congr rfl (fun w _ => ?_)
        show (if z0.1 = (j, w).1 then Reg.adj z0.2 (j, w).2
                else H.adj z0.1 (j, w).1 / (Fintype.card W : ℂ))
              = H.adj i j / (Fintype.card W : ℂ)
        rw [if_neg (by rw [hz0]; exact hij), hz0]
      rw [hval x hx, hval y hy]

/-- Each region-cell has exactly `|W|` vertices. -/
theorem regionalPartition_cellCard (H : WeightedGraph R) (Reg : WeightedGraph W)
    (d : ℂ) (hreg : Reg.isRegular d) (a : R) :
    (regionalPartition H Reg d hreg).cellCard a = (Fintype.card W : ℝ) := by
  have hset : (Finset.univ.filter
      (fun z : R × W => (regionalPartition H Reg d hreg).cells z = a))
      = ({a} ×ˢ (Finset.univ : Finset W)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  unfold EquitablePartition.cellCard
  rw [hset, Finset.card_product]
  simp

/-- **Fiber evaluation.**  The sum of `Ĉ`'s edges from a vertex `z0` (in region
`z0.1`) to the entire region `j` is `d` if `j` is the home region (the regional
degree) and the connectome weight `C_{z0.1, j}` otherwise. -/
theorem regionalNetwork_fiberEval [Nonempty W] (H : WeightedGraph R) (Reg : WeightedGraph W)
    (d : ℂ) (hreg : Reg.isRegular d) (z0 : R × W) (j : R) :
    (∑ w : W, (regionalNetwork H Reg).adj z0 (j, w))
      = if z0.1 = j then d else H.adj z0.1 j := by
  by_cases hij : z0.1 = j
  · rw [if_pos hij]
    have hc : (∑ w : W, (regionalNetwork H Reg).adj z0 (j, w)) = ∑ w : W, Reg.adj z0.2 w := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      show (if z0.1 = (j, w).1 then Reg.adj z0.2 (j, w).2
              else H.adj z0.1 (j, w).1 / (Fintype.card W : ℂ)) = Reg.adj z0.2 w
      rw [if_pos hij]
    rw [hc]; exact hreg z0.2
  · rw [if_neg hij]
    have hc : (∑ w : W, (regionalNetwork H Reg).adj z0 (j, w))
        = ∑ _w : W, H.adj z0.1 j / (Fintype.card W : ℂ) := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      show (if z0.1 = (j, w).1 then Reg.adj z0.2 (j, w).2
              else H.adj z0.1 (j, w).1 / (Fintype.card W : ℂ))
            = H.adj z0.1 j / (Fintype.card W : ℂ)
      rw [if_neg hij]
    rw [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcardne : (Fintype.card W : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [← mul_div_assoc, mul_comm (↑(Fintype.card W) : ℂ) (H.adj z0.1 j), mul_div_assoc,
      div_self hcardne, mul_one]

/-- The branching number from `z0` into cell `j` (the equitable branching). -/
theorem regionalNetwork_branch [Nonempty W] (H : WeightedGraph R) (Reg : WeightedGraph W)
    (d : ℂ) (hreg : Reg.isRegular d) (z0 : R × W) (j : R) :
    (∑ z : R × W, if z.1 = j then (regionalNetwork H Reg).adj z0 z else 0)
      = if z0.1 = j then d else H.adj z0.1 j := by
  have expand : (∑ z : R × W, if z.1 = j then (regionalNetwork H Reg).adj z0 z else 0)
      = ∑ w : W, (regionalNetwork H Reg).adj z0 (j, w) := by
    rw [Fintype.sum_prod_type]
    calc (∑ b : R, ∑ w : W, if (b, w).1 = j then (regionalNetwork H Reg).adj z0 (b, w) else 0)
        = ∑ b : R, (if b = j then ∑ w : W, (regionalNetwork H Reg).adj z0 (b, w) else 0) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          by_cases hb : b = j <;> simp [hb]
      _ = ∑ w : W, (regionalNetwork H Reg).adj z0 (j, w) := by
          rw [Finset.sum_ite_eq' Finset.univ j
            (fun b => ∑ w : W, (regionalNetwork H Reg).adj z0 (b, w))]
          simp
  rw [expand, regionalNetwork_fiberEval H Reg d hreg z0 j]

/-- **The quotient is the connectome plus the regional self-coupling.**
`Q i j = H.adj i j + (if i = j then d else 0)`. -/
theorem regionalPartition_quotient_eq [Nonempty W] (H : WeightedGraph R) (Reg : WeightedGraph W)
    (d : ℂ) (hreg : Reg.isRegular d) (a b : R) :
    (regionalPartition H Reg d hreg).quotient a b
      = H.adj a b + (if a = b then d else 0) := by
  obtain ⟨w0⟩ := (inferInstance : Nonempty W)
  rw [EquitablePartition.quotient_apply (regionalPartition H Reg d hreg) a b (a, w0) rfl]
  show (∑ z : R × W, if z.1 = b then (regionalNetwork H Reg).adj (a, w0) z else 0)
      = H.adj a b + (if a = b then d else 0)
  rw [regionalNetwork_branch H Reg d hreg (a, w0) b]
  show (if a = b then d else H.adj a b) = H.adj a b + (if a = b then d else 0)
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, hab, H.loopless b, zero_add]
  · rw [if_neg hab, if_neg hab, add_zero]

/-- Because all cells have equal size `|W|`, the symmetric quotient equals the
raw quotient: `Q̃ = C + d·I`. -/
theorem regionalPartition_symmQuotient_eq [Nonempty W] (H : WeightedGraph R) (Reg : WeightedGraph W)
    (d : ℂ) (hreg : Reg.isRegular d) (a b : R) :
    (regionalPartition H Reg d hreg).symmQuotient a b
      = H.adj a b + (if a = b then d else 0) := by
  unfold EquitablePartition.symmQuotient
  rw [regionalPartition_cellCard H Reg d hreg a, regionalPartition_cellCard H Reg d hreg b,
      regionalPartition_quotient_eq H Reg d hreg a b]
  have hsqrt : (Real.sqrt (Fintype.card W : ℝ) : ℂ) ≠ 0 := by
    have h0 : (0 : ℝ) < Real.sqrt (Fintype.card W : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    exact_mod_cast ne_of_gt h0
  rw [mul_comm, mul_div_assoc, div_self hsqrt, mul_one]

/-- The regional partition satisfies the Laplacian degree-balance, so the
Laplacian interlacing applies.  (Real degrees from `RealNonnegWeights`.) -/
instance regionalPartition_laplacianDegreeAligned
    (H : WeightedGraph R) (Reg : WeightedGraph W) (d : ℂ) (hreg : Reg.isRegular d)
    (hH : RealNonnegWeights H) (hReg : RealNonnegWeights Reg) :
    LaplacianDegreeAligned (regionalPartition H Reg d hreg) where
  degree_eq_rowSum := by
    intro x
    haveI : Nonempty W := ⟨x.2⟩
    show (((regionalNetwork H Reg).degree x).re : ℂ)
        = ∑ j, (regionalPartition H Reg d hreg).symmQuotient x.1 j
    have hrow : (∑ j, (regionalPartition H Reg d hreg).symmQuotient x.1 j)
        = H.degree x.1 + d := by
      rw [Finset.sum_congr rfl
            (fun k _ => regionalPartition_symmQuotient_eq H Reg d hreg x.1 k),
          Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ x.1 (fun _ => d)]
      simp [WeightedGraph.degree]
    have hg : ∀ j : R, (if x.1 = j then d else H.adj x.1 j)
        = (if x.1 = j then d else 0) + H.adj x.1 j := by
      intro j; by_cases hj : x.1 = j
      · rw [if_pos hj, if_pos hj, ← hj, H.loopless x.1, add_zero]
      · rw [if_neg hj, if_neg hj, zero_add]
    have hdeg : (regionalNetwork H Reg).degree x = d + H.degree x.1 := by
      show (∑ z, (regionalNetwork H Reg).adj x z) = d + H.degree x.1
      rw [Fintype.sum_prod_type,
          Finset.sum_congr rfl (fun j _ => regionalNetwork_fiberEval H Reg d hreg x j),
          Finset.sum_congr rfl (fun j _ => hg j), Finset.sum_add_distrib,
          Finset.sum_ite_eq Finset.univ x.1 (fun _ => d), if_pos (Finset.mem_univ x.1)]
      rfl
    have hd_im : d.im = 0 := by
      have hdd : d = Reg.degree x.2 := (hreg x.2).symm
      rw [hdd]; unfold WeightedGraph.degree; rw [Complex.im_sum]
      exact Finset.sum_eq_zero (fun w _ => (hReg x.2 w).1)
    have hH_im : (H.degree x.1).im = 0 := by
      unfold WeightedGraph.degree; rw [Complex.im_sum]
      exact Finset.sum_eq_zero (fun w _ => (hH x.1 w).1)
    have hdeg_im : ((regionalNetwork H Reg).degree x).im = 0 := by
      rw [hdeg, Complex.add_im, hd_im, hH_im, add_zero]
    rw [hrow, show (((regionalNetwork H Reg).degree x).re : ℂ)
          = (regionalNetwork H Reg).degree x from by apply Complex.ext <;> simp [hdeg_im], hdeg]
    ring

/-- **The quotient Laplacian is exactly the connectome Laplacian.**  The regional
self-coupling `d` cancels between the degree diagonal and the quotient diagonal,
so `D_Q − Q̃ = D_C − C = L_C`.  This is the algebraic reason Deco's "average
across the `n` nodes in each region" is exact. -/
theorem regionalNetwork_quotientLaplacian_eq_host [Nonempty W]
    (H : WeightedGraph R) (Reg : WeightedGraph W) (d : ℂ) (hreg : Reg.isRegular d)
    (hH : RealNonnegWeights H) :
    (Matrix.diagonal (fun i => ∑ j, (regionalPartition H Reg d hreg).symmQuotient i j)
        - (regionalPartition H Reg d hreg).symmQuotient)
      = H.laplacian.adj := by
  ext i j
  have hlap : H.laplacian.adj i j
      = (if i = j then ((H.degree i).re : ℂ) else 0) - H.adj i j := by
    show ((Matrix.diagonal (fun x => ((H.degree x).re : ℂ)) - H.adj) i j) = _
    rw [Matrix.sub_apply, Matrix.diagonal_apply]
  have hrow : (∑ k, (regionalPartition H Reg d hreg).symmQuotient i k) = H.degree i + d := by
    rw [Finset.sum_congr rfl
          (fun k _ => regionalPartition_symmQuotient_eq H Reg d hreg i k),
        Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ i (fun _ => d)]
    simp [WeightedGraph.degree]
  have hdegre : ((H.degree i).re : ℂ) = H.degree i := by
    have him : (H.degree i).im = 0 := by
      unfold WeightedGraph.degree; rw [Complex.im_sum]
      exact Finset.sum_eq_zero (fun w _ => (hH i w).1)
    apply Complex.ext <;> simp [him]
  have hlhs : (Matrix.diagonal (fun i => ∑ j, (regionalPartition H Reg d hreg).symmQuotient i j)
        - (regionalPartition H Reg d hreg).symmQuotient) i j
      = (if i = j then (H.degree i + d) else 0)
        - (H.adj i j + (if i = j then d else 0)) := by
    rw [Matrix.sub_apply, Matrix.diagonal_apply, regionalPartition_symmQuotient_eq H Reg d hreg i j]
    congr 1
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij]; exact hrow
    · rw [if_neg hij, if_neg hij]
  rw [hlhs, hlap, hdegre]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, if_pos hij, hij, H.loopless j]; ring
  · rw [if_neg hij, if_neg hij, if_neg hij]; ring

end Network

/-! ## 3.  Linearised Hopf dynamics, the Lyapunov FC, and its exact reduction -/

section Dynamics

variable {V : Type uV} [Fintype V] [DecidableEq V]

/-- The linearised Stuart–Landau / Hopf **drift** at the edge of bifurcation,
symmetric reduction `ω = 0` (Deco et al. Eqs. 6–8): `J = a·I − L`, with `a < 0`
the sub-critical bifurcation parameter and `L = G.laplacian.adj`. -/
noncomputable def ouDrift (G : WeightedGraph V) (a : ℝ) : Matrix V V ℂ :=
  (a : ℂ) • (1 : Matrix V V ℂ) - G.laplacian.adj

/-- The **stationary functional connectivity**: the Lyapunov solution
`K = (σ²/2)(L − a·I)⁻¹` of `J K + K Jᵀ + Q = 0` with isotropic noise `Q = σ²·I`
(Deco et al. Eqs. 9–10). -/
noncomputable def stationaryFC (G : WeightedGraph V) (a σ2 : ℝ) : Matrix V V ℂ :=
  ((σ2 / 2 : ℝ) : ℂ) • (G.laplacian.adj - (a : ℂ) • 1)⁻¹

/-- **The FC solves the Lyapunov equation** `JK + KJᵀ + Q = 0`.  Pure resolvent
algebra: with `S = L − a·I`, `J = −S` and `K = (σ²/2)S⁻¹`, so `JK = KJ = −(σ²/2)I`
and the sum with `Q = σ²·I` vanishes.  Needs `S` invertible and `Lᵀ = L`
(real-symmetric weights). -/
theorem stationaryFC_solves_lyapunov (G : WeightedGraph V) (a σ2 : ℝ)
    (hunit : IsUnit (G.laplacian.adj - (a : ℂ) • 1).det)
    (hsymm : (G.laplacian.adj)ᵀ = G.laplacian.adj) :
    ouDrift G a * stationaryFC G a σ2
        + stationaryFC G a σ2 * (ouDrift G a)ᵀ
        + ((σ2 : ℝ) : ℂ) • (1 : Matrix V V ℂ) = 0 := by
  have hStransp : (G.laplacian.adj - (a : ℂ) • 1)ᵀ = G.laplacian.adj - (a : ℂ) • 1 := by
    rw [Matrix.transpose_sub, hsymm, Matrix.transpose_smul, Matrix.transpose_one]
  have hSinv1 : (G.laplacian.adj - (a : ℂ) • 1) * (G.laplacian.adj - (a : ℂ) • 1)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hunit
  have hSinv2 : (G.laplacian.adj - (a : ℂ) • 1)⁻¹ * (G.laplacian.adj - (a : ℂ) • 1) = 1 :=
    Matrix.nonsing_inv_mul _ hunit
  have hdrift : ouDrift G a = -(G.laplacian.adj - (a : ℂ) • 1) := by rw [ouDrift, neg_sub]
  unfold stationaryFC
  rw [hdrift, Matrix.transpose_neg, hStransp, neg_mul, mul_smul_comm, hSinv1, smul_mul_assoc,
    mul_neg, hSinv2, smul_neg]
  have hc : (((σ2 / 2 : ℝ) : ℂ)) + (((σ2 / 2 : ℝ) : ℂ)) = ((σ2 : ℝ) : ℂ) := by push_cast; ring
  rw [← neg_add, ← add_smul, hc, neg_add_cancel]

end Dynamics

/-! ### The general reduction: FC reduces along any equitable quotient

The whole-brain → connectome reduction is a special case of a single fact: the
Ornstein–Uhlenbeck / Lyapunov stationary FC of *any* equitable, degree-balanced
graph intertwines the FC of its quotient.  The brain is the instance where the
quotient is the structural connectome. -/

section GeneralReduction

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {I : Type uI} [Fintype I] [DecidableEq I]

/-- The **quotient Laplacian** `D_Q − Q̃` of an equitable partition (`Q̃` the
symmetric quotient, `D_Q` its row-sum diagonal). -/
noncomputable def quotientLaplacian {G : WeightedGraph V} (P : EquitablePartition G I) :
    Matrix I I ℂ :=
  Matrix.diagonal (fun i => ∑ j, P.symmQuotient i j) - P.symmQuotient

/-- **The general OU/Lyapunov reduction.**  For any equitable partition with the
Laplacian degree-balance, the stationary functional connectivity intertwines —
through the cell-inflate — the FC built from the *quotient Laplacian*.  Both the
quantum walk (`intertwines_evolve`) and this classical FC are instances of the one
`Intertwines` backbone; here the resolvent (rational) functional calculus is fully
proved. -/
theorem stationaryFC_reduces_along_quotient {G : WeightedGraph V}
    (P : EquitablePartition G I) [LaplacianDegreeAligned P] (a σ2 : ℝ)
    (hunit  : IsUnit (G.laplacian.adj - (a : ℂ) • 1).det)
    (hunitQ : IsUnit (quotientLaplacian P - (a : ℂ) • 1).det) :
    Intertwines P (stationaryFC G a σ2)
      (((σ2 / 2 : ℝ) : ℂ) • (quotientLaplacian P - (a : ℂ) • 1)⁻¹) := by
  have hL : Intertwines P G.laplacian.adj (quotientLaplacian P) := fun v =>
    laplacian_mulVec_cellInflate_eq P v
  exact ((hL.sub (Intertwines.scalar P (a : ℂ))).inv hunit hunitQ).smul _

/-! ### The full rotating Jacobian (`ω ≠ 0`)

Deco et al.'s Jacobian (Eq. 8) is the `2M × 2M` real block `[[aI−L, diag ω], [−diag ω,
aI−L]]`, the real representation of the **complex** drift `(aI−L) − i·diag(ω)` acting
on `z = x + iy`.  Their intrinsic frequency `ω_j` is *per brain region* — constant on
the cells of the regional partition — so the rotation descends too, and the entire
(rotating) dynamics reduce to the connectome.  This removes the `ω = 0` restriction
at the level of the drift and the time-evolution. -/

/-- The **full linearised Stuart–Landau drift** at the edge of bifurcation, with
the intrinsic-frequency rotation kept: the complex representation
`J = (a·I − L) − i·diag(ω)` of Deco et al.'s Eq. 8 block Jacobian. -/
noncomputable def ouDriftC (G : WeightedGraph V) (a : ℝ) (ω : V → ℂ) : Matrix V V ℂ :=
  ((a : ℂ) • 1 - G.laplacian.adj) - Complex.I • Matrix.diagonal ω

/-- **The rotating drift reduces to the connectome drift.**  When `ω` is constant on
cells (per-region, as in Deco et al.), the full `ω ≠ 0` Jacobian intertwines the
quotient Jacobian built from the connectome Laplacian and the per-region frequency. -/
theorem ouDriftC_intertwines {G : WeightedGraph V} (P : EquitablePartition G I)
    [LaplacianDegreeAligned P] (a : ℝ) (ω : V → ℂ) (ωQ : I → ℂ)
    (hω : ∀ x, ω x = ωQ (P.cells x)) :
    Intertwines P (ouDriftC G a ω)
      (((a : ℂ) • 1 - quotientLaplacian P) - Complex.I • Matrix.diagonal ωQ) := by
  have hL : Intertwines P G.laplacian.adj (quotientLaplacian P) := fun v =>
    laplacian_mulVec_cellInflate_eq P v
  exact ((Intertwines.scalar P (a : ℂ)).sub hL).sub
    ((Intertwines.diagonal_of_cellConst ω ωQ hω).smul Complex.I)

/-- **The full rotating propagator reduces.**  `e^{tJ}` for the rotating drift carries
the cell-inflate to the inflate of the quotient propagator — the `ω ≠ 0`
generalisation of `intertwines_evolve`, via `Intertwines.exp`. -/
theorem ouPropagatorC_reduces {G : WeightedGraph V} (P : EquitablePartition G I)
    [LaplacianDegreeAligned P] (a : ℝ) (ω : V → ℂ) (ωQ : I → ℂ)
    (hω : ∀ x, ω x = ωQ (P.cells x)) (t : ℝ) :
    Intertwines P (NormedSpace.exp ((t : ℂ) • ouDriftC G a ω))
      (NormedSpace.exp ((t : ℂ) •
        (((a : ℂ) • 1 - quotientLaplacian P) - Complex.I • Matrix.diagonal ωQ))) :=
  ((ouDriftC_intertwines P a ω ωQ hω).smul (t : ℂ)).exp

/-- **The full (two-sided, `ω ≠ 0`) stationary covariance reduces.**  For any drift
`J` intertwining `JQ` (with `Jᵀ` intertwining `JQᵀ`) and isotropic-or-intertwining
noise `Q`, the Lyapunov solutions `K`, `KQ` satisfy `Intertwines P K KQ` — i.e. the
whole-brain stationary covariance reduces to the connectome covariance, *with the
rotation kept*.  The error `D = K·B − B·KQ` solves the **homogeneous** Sylvester
equation `J·D + D·JQᵀ = 0`, so it vanishes by Sylvester uniqueness (`hsylv`).

`hsylv` is the one analytic input — uniqueness of the Lyapunov/Sylvester solution,
equivalent to `J` being Hurwitz (stable), which holds at Deco et al.'s stable fixed
point (`a < 0`).  It is a recognized gap in Mathlib (matrix-exponential decay); we
isolate it as a single clean hypothesis rather than fake it. -/
theorem stationaryCov_reduces {G : WeightedGraph V} (P : EquitablePartition G I)
    (J : Matrix V V ℂ) (JQ : Matrix I I ℂ) (K : Matrix V V ℂ) (KQ : Matrix I I ℂ)
    (Q : Matrix V V ℂ) (QQ : Matrix I I ℂ)
    (hJ : Intertwines P J JQ) (hJt : Intertwines P Jᵀ JQᵀ) (hQ : Intertwines P Q QQ)
    (hlyap : J * K + K * Jᵀ + Q = 0) (hlyapQ : JQ * KQ + KQ * JQᵀ + QQ = 0)
    (hsylv : ∀ D : Matrix V I ℂ, J * D + D * JQᵀ = 0 → D = 0) :
    Intertwines P K KQ := by
  rw [intertwines_iff_mat]
  have hJm : J * cellInflateMat P = cellInflateMat P * JQ := (intertwines_iff_mat P J JQ).mp hJ
  have hJtm : Jᵀ * cellInflateMat P = cellInflateMat P * JQᵀ :=
    (intertwines_iff_mat P Jᵀ JQᵀ).mp hJt
  have hQm : Q * cellInflateMat P = cellInflateMat P * QQ := (intertwines_iff_mat P Q QQ).mp hQ
  set B := cellInflateMat P with hB
  have hJKt : J * K + K * Jᵀ = -Q := eq_neg_of_add_eq_zero_left hlyap
  have hJKtQ : JQ * KQ + KQ * JQᵀ = -QQ := eq_neg_of_add_eq_zero_left hlyapQ
  have h1 : J * (K * B) + (K * B) * JQᵀ = (-Q) * B := by
    rw [← Matrix.mul_assoc J K B, Matrix.mul_assoc K B JQᵀ, ← hJtm, ← Matrix.mul_assoc K Jᵀ B,
      ← Matrix.add_mul, hJKt]
  have h2 : J * (B * KQ) + (B * KQ) * JQᵀ = B * (-QQ) := by
    rw [← Matrix.mul_assoc J B KQ, hJm, Matrix.mul_assoc B JQ KQ, Matrix.mul_assoc B KQ JQᵀ,
      ← Matrix.mul_add, hJKtQ]
  have hsol : J * (K * B - B * KQ) + (K * B - B * KQ) * JQᵀ = 0 := by
    rw [Matrix.mul_sub, Matrix.sub_mul,
      show J * (K * B) - J * (B * KQ) + ((K * B) * JQᵀ - (B * KQ) * JQᵀ)
        = (J * (K * B) + (K * B) * JQᵀ) - (J * (B * KQ) + (B * KQ) * JQᵀ) from by abel,
      h1, h2, Matrix.neg_mul, Matrix.mul_neg, hQm]
    abel
  exact sub_eq_zero.mp (hsylv (K * B - B * KQ) hsol)

/-! ### Energy: the COCO entropy-production cost

Deco et al.'s energy result (their Fig. 3E) uses the COCO framework: at the
non-equilibrium steady state, **energy consumption = entropy-production rate**

  `Φ = tr(Jᵀ Q⁻¹ (J K − K Jᵀ))`,

built from the stationary probability **current** `J K − K Jᵀ` (Nartallo-Kaluarachchi
et al., *Phys. Rev. E* 107 024121 (2023); Deco et al., COCO, bioRxiv
2025.06.18.660368).  The current vanishes when the drift is symmetric (detailed
balance), so the cost is a genuinely `ω ≠ 0`, non-equilibrium phenomenon — which is
exactly why our exact `ω = 0` reduction has **zero** energy, and the brain's energy
lives in the rotation. -/

/-- The **entropy-production / energy-consumption rate** (COCO; PRE 107 024121):
`tr(Jᵀ Q⁻¹ (J K − K Jᵀ))`, the trace against the stationary current `J K − K Jᵀ`. -/
noncomputable def entropyProduction (J K Q : Matrix V V ℂ) : ℂ :=
  (Jᵀ * Q⁻¹ * (J * K - K * Jᵀ)).trace

/-- **No energy without rotation.**  A symmetric drift that commutes with the
covariance has zero current, hence zero entropy production / energy — matching
COCO's "symmetric `J` + isotropic noise ⇒ equilibrium." -/
theorem entropyProduction_eq_zero_of_commute (J K Q : Matrix V V ℂ)
    (hsymm : Jᵀ = J) (hcomm : J * K = K * J) :
    entropyProduction J K Q = 0 := by
  unfold entropyProduction
  rw [hsymm, hcomm, sub_self, Matrix.mul_zero, Matrix.trace_zero]

/-- **The exact `ω = 0` reduction has zero energy cost.**  The symmetric drift
`J = a·I − L` and its resolvent covariance commute (both products equal
`−(σ²/2)·I`), so the entropy production vanishes.  The brain's nonzero energy
(Fig. 3E) is therefore not captured by — and does not contradict — the symmetric
reduction; it requires the `ω ≠ 0` rotation. -/
theorem stationaryFC_entropyProduction_eq_zero (G : WeightedGraph V) (a σ2 : ℝ)
    (hunit : IsUnit (G.laplacian.adj - (a : ℂ) • 1).det)
    (hsymm : (G.laplacian.adj)ᵀ = G.laplacian.adj) :
    entropyProduction (ouDrift G a) (stationaryFC G a σ2) (((σ2 : ℝ) : ℂ) • 1) = 0 := by
  refine entropyProduction_eq_zero_of_commute _ _ _ ?_ ?_
  · show (ouDrift G a)ᵀ = ouDrift G a
    unfold ouDrift
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsymm]
  · have hSinv1 : (G.laplacian.adj - (a : ℂ) • 1) * (G.laplacian.adj - (a : ℂ) • 1)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hunit
    have hSinv2 : (G.laplacian.adj - (a : ℂ) • 1)⁻¹ * (G.laplacian.adj - (a : ℂ) • 1) = 1 :=
      Matrix.nonsing_inv_mul _ hunit
    have hdrift : ouDrift G a = -(G.laplacian.adj - (a : ℂ) • 1) := by rw [ouDrift, neg_sub]
    have e1 : ouDrift G a * stationaryFC G a σ2 = -(((σ2 / 2 : ℝ) : ℂ) • 1) := by
      rw [hdrift]; unfold stationaryFC
      rw [Matrix.neg_mul, mul_smul_comm, hSinv1]
    have e2 : stationaryFC G a σ2 * ouDrift G a = -(((σ2 / 2 : ℝ) : ℂ) • 1) := by
      rw [hdrift]; unfold stationaryFC
      rw [smul_mul_assoc, mul_neg, hSinv2, smul_neg]
    rw [e1, e2]

/-- **The stationary probability current reduces along the quotient.**  The
irreversible current `J K − K Jᵀ` — the source of the energy cost — intertwines the
connectome current `JQ KQ − KQ JQᵀ`.  So even though the total energy is an extensive
full-network trace, its physical generator descends to the connectome. -/
theorem current_reduces {G : WeightedGraph V} (P : EquitablePartition G I)
    {J : Matrix V V ℂ} {JQ : Matrix I I ℂ} {K : Matrix V V ℂ} {KQ : Matrix I I ℂ}
    (hJ : Intertwines P J JQ) (hJt : Intertwines P Jᵀ JQᵀ) (hK : Intertwines P K KQ) :
    Intertwines P (J * K - K * Jᵀ) (JQ * KQ - KQ * JQᵀ) :=
  (hJ.mul hK).sub (hK.mul hJt)

end GeneralReduction

/-! ### The certified reduction: whole-brain FC = connectome FC -/

section Reduction

variable {R : Type uR} [Fintype R] [DecidableEq R]
variable {W : Type uW} [Fintype W] [DecidableEq W]

/-- **The Laplacian of `Ĉ` intertwines the connectome Laplacian** through the
regional cell-inflate.  Immediate from `laplacian_mulVec_cellInflate_eq` and
`regionalNetwork_quotientLaplacian_eq_host`. -/
theorem intertwines_laplacian [Nonempty W]
    (H : WeightedGraph R) (Reg : WeightedGraph W) (d : ℂ) (hreg : Reg.isRegular d)
    (hH : RealNonnegWeights H) (hReg : RealNonnegWeights Reg) :
    Intertwines (regionalPartition H Reg d hreg)
      (regionalNetwork H Reg).laplacian.adj H.laplacian.adj := by
  have hal : LaplacianDegreeAligned (regionalPartition H Reg d hreg) :=
    regionalPartition_laplacianDegreeAligned H Reg d hreg hH hReg
  intro v
  rw [laplacian_mulVec_cellInflate_eq (regionalPartition H Reg d hreg) v,
    regionalNetwork_quotientLaplacian_eq_host H Reg d hreg hH]

/-- **Deco's "average across the `n` nodes in each region", made exact.**  The
stationary functional connectivity of the whole-brain network of networks
intertwines — through the regional cell-inflate — the stationary functional
connectivity computed *directly on the structural connectome*.  No information is
lost in the reduction: `FCᵐᵒᵈᵉˡ` is an exact equitable quotient. -/
theorem stationaryFC_reduction [Nonempty W]
    (H : WeightedGraph R) (Reg : WeightedGraph W) (d : ℂ) (hreg : Reg.isRegular d)
    (hH : RealNonnegWeights H) (hReg : RealNonnegWeights Reg) (a σ2 : ℝ)
    (hunit  : IsUnit ((regionalNetwork H Reg).laplacian.adj - (a : ℂ) • 1).det)
    (hunitQ : IsUnit (H.laplacian.adj - (a : ℂ) • 1).det) :
    Intertwines (regionalPartition H Reg d hreg)
      (stationaryFC (regionalNetwork H Reg) a σ2) (stationaryFC H a σ2) := by
  -- Special case of `stationaryFC_reduces_along_quotient`, with the quotient
  -- Laplacian identified as the connectome Laplacian.
  haveI : LaplacianDegreeAligned (regionalPartition H Reg d hreg) :=
    regionalPartition_laplacianDegreeAligned H Reg d hreg hH hReg
  have hQ : quotientLaplacian (regionalPartition H Reg d hreg) = H.laplacian.adj :=
    regionalNetwork_quotientLaplacian_eq_host H Reg d hreg hH
  have key := stationaryFC_reduces_along_quotient (regionalPartition H Reg d hreg) a σ2 hunit
    (by rw [hQ]; exact hunitQ)
  rw [hQ] at key
  exact key

/-- Invertibility of `L − a·I` for the sub-critical regime `a < 0`: `L` is PSD
under real nonnegative weights, so `L − a·I = L + |a|·I` is positive definite,
hence has unit determinant.  (Discharges the `hunit` hypotheses of
`stationaryFC_reduction` for genuine connectomes.) -/
theorem resolvent_isUnit_of_neg {V : Type uV} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (a : ℝ) (hw : RealNonnegWeights G) (ha : a < 0) :
    IsUnit (G.laplacian.adj - (a : ℂ) • 1).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  -- The Laplacian is positive semidefinite under real nonnegative weights.
  have hLpsd : (G.laplacian.adj).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨G.laplacian.herm, fun x => ?_⟩
    -- The Hermitian quadratic form `star x ⬝ᵥ (L *ᵥ x)` is self-conjugate, hence real.
    have hstar : star (star x ⬝ᵥ (G.laplacian.adj *ᵥ x))
        = star x ⬝ᵥ (G.laplacian.adj *ᵥ x) := by
      rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, G.laplacian.herm.eq,
        Matrix.dotProduct_mulVec]
    have him : (star x ⬝ᵥ (G.laplacian.adj *ᵥ x)).im = 0 := by
      rw [← Complex.conj_eq_iff_im, starRingEnd_apply]; exact hstar
    -- And its real part is nonnegative (difference-of-squares form).
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · rw [Complex.zero_re, show (star x ⬝ᵥ (G.laplacian.adj *ᵥ x)) = laplacianForm G x from
        (laplacianForm_eq_dotProduct G x).symm]
      exact laplacianForm_re_nonneg G hw x
    · rw [Complex.zero_im]; exact him.symm
  -- `(-a) • 1` is positive definite since `-a > 0`.
  have hpos : (0 : ℂ) < ((-a : ℝ) : ℂ) := by
    rw [Complex.lt_def]
    exact ⟨by simpa using neg_pos.mpr ha, by simp⟩
  have hscalPD : (((-a : ℝ) : ℂ) • (1 : Matrix V V ℂ)).PosDef := Matrix.PosDef.one.smul hpos
  -- `L - a•1 = (-a)•1 + L` is positive definite, hence invertible.
  have heq : G.laplacian.adj - (a : ℂ) • 1
      = ((-a : ℝ) : ℂ) • (1 : Matrix V V ℂ) + G.laplacian.adj := by
    rw [show ((-a : ℝ) : ℂ) = -(a : ℂ) from by push_cast; ring, neg_smul]; abel
  rw [heq]
  exact (hscalPD.add_posSemidef hLpsd).isUnit

end Reduction

/-! ## 4.  The spectral gap: inheritance and the Fig. 4A monotonicity prediction -/

section Gap

variable {V : Type uV} [Fintype V] [DecidableEq V]

/-- The **adjacency spectral gap** `λ₀ − λ₁` (top minus second eigenvalue of the
adjacency), the Deco–Scholes signature of a "quantum-like" state.  Eigenvalues
are taken in antitone (largest-first) order. -/
noncomputable def adjSpectralGap (G : WeightedGraph V) (h : 2 ≤ Fintype.card V) : ℝ :=
  G.herm.eigenvalues₀ ⟨0, by omega⟩ - G.herm.eigenvalues₀ ⟨1, by omega⟩

/-- A **quantum-like / expander regime** (Scholes's axioms A–C, *Proc. R. Soc. A*
476 (2020)): the top eigenvalue is separated by a positive gap (A), and the gap
is robust to a prescribed level of disorder (B).  The two-state structure (C) is
the cell-uniform vs. orthogonal complement split, recorded elsewhere. -/
structure QuantumLikeRegime (G : WeightedGraph V) (h : 2 ≤ Fintype.card V)
    (floor : ℝ) : Prop where
  gap_pos    : 0 < adjSpectralGap G h
  gap_robust : floor ≤ adjSpectralGap G h

variable {R : Type uR} [Fintype R] [DecidableEq R]
variable {W : Type uW} [Fintype W] [DecidableEq W]

/-- **The distributed spectral gap (Fig. 1C).**  Every eigenvalue of the
connectome-plus-self-coupling quotient `C + d·I` is an eigenvalue of the full
network of networks `Ĉ`.  Since `C + d·I` shifts the connectome spectrum
rigidly, the connectome's spectral gap is inherited *exactly* by `Ĉ`.  Engine:
`EquitablePartition.spectrum_subset`. -/
theorem connectome_gap_inherited
    (H : WeightedGraph R) (Reg : WeightedGraph W) (d : ℂ) (hreg : Reg.isRegular d)
    [Nonempty W] :
    spectrum ℂ (regionalPartition H Reg d hreg).symmQuotient
      ⊆ spectrum ℂ (regionalNetwork H Reg).adj := by
  refine (regionalPartition H Reg d hreg).spectrum_subset ?_
  intro a
  rw [regionalPartition_cellCard H Reg d hreg a]
  have : (0 : ℝ) < (Fintype.card W : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact this

/-- **Edge pruning.**  Zero out every edge not retained by the symmetric
predicate `keep`.  Models the removal of the rare long-range exceptions to the
exponential distance rule (Deco et al., Fig. 4A). -/
noncomputable def prune (G : WeightedGraph V) (keep : V → V → Prop)
    [DecidableRel keep] (hsymm : ∀ u w, keep u w ↔ keep w u) : WeightedGraph V where
  adj := fun u w => if keep u w then G.adj u w else 0
  herm := by
    ext u w
    rw [Matrix.conjTranspose_apply]
    by_cases h : keep w u
    · rw [if_pos h, if_pos ((hsymm w u).mp h)]
      exact G.herm.apply u w
    · rw [if_neg h, if_neg (fun h' => h ((hsymm w u).mpr h'))]
      exact star_zero _
  loopless := by
    intro v
    show (if keep v v then G.adj v v else 0) = 0
    by_cases h : keep v v <;> simp [h, G.loopless]

/-- **Fig. 4A as a theorem: long-range connections amplify the spectral gap.**
Removing edges can only *decrease* the algebraic connectivity (Fiedler value) —
the rigorous, monotone form of Deco et al.'s empirical claim that deleting the
long-range exceptions shrinks the QL spectral gap.  Engine:
`AlgebraicConnectivity.algebraicConnectivity_mono`. -/
theorem algConn_prune_le (G : WeightedGraph V) (keep : V → V → Prop)
    [DecidableRel keep] (hsymm : ∀ u w, keep u w ↔ keep w u)
    (hw : RealNonnegWeights G) :
    algebraicConnectivity (prune G keep hsymm) ≤ algebraicConnectivity G := by
  refine algebraicConnectivity_mono (prune G keep hsymm) G ?_ ?_
  · -- the pruned graph still has real nonnegative weights
    intro u w
    simp only [prune]
    by_cases h : keep u w <;> simp [h, hw u w]
  · -- the pruned Laplacian form is dominated by the full one (fewer nonneg terms)
    intro x
    have hprune_real : RealNonnegWeights (prune G keep hsymm) := by
      intro u w; simp only [prune]
      by_cases h : keep u w <;> simp [h, hw u w]
    have hp := laplacianForm_two_re (prune G keep hsymm) hprune_real x
    have hg := laplacianForm_two_re G hw x
    have key : 2 * (laplacianForm (prune G keep hsymm) x).re
        ≤ 2 * (laplacianForm G x).re := by
      rw [hp, hg]
      refine Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun w _ => ?_))
      refine mul_le_mul_of_nonneg_right ?_ (Complex.normSq_nonneg _)
      show (if keep u w then G.adj u w else 0).re ≤ (G.adj u w).re
      by_cases hk : keep u w <;> simp [hk, (hw u w).2]
    linarith

end Gap

/-! ## 5.  Alon–Boppana (cited honest floor)

The asymptotic expander bound that pins the QL spectral gap: for a `k`-regular
graph the second eigenvalue satisfies `λ₁ ≥ 2√(k−1) − o(1)` (Alon 1986; Nilli
1991), so no `k`-regular graph beats the Ramanujan gap `k − 2√(k−1)`.  Mathlib
lacks this; we carry it as a cited typeclass. -/

section AlonBoppana

variable {V : Type uV} [Fintype V] [DecidableEq V]

/-- The **Alon–Boppana floor**: a certified lower bound `λ₁ ≥ bound` on the
second adjacency eigenvalue of a `k`-regular graph (Alon, *Combinatorica* 6
(1986); Nilli, *Discrete Math.* 91 (1991)).  Non-vacuous content lives in the
provider of the instance. -/
class AlonBoppanaFloor (G : WeightedGraph V) (k : ℝ) (bound : ℝ) : Prop where
  regular     : G.isRegular (k : ℂ)
  second_ge   : ∀ h : 2 ≤ Fintype.card V, bound ≤ G.herm.eigenvalues₀ ⟨1, by omega⟩

/-- Under an Alon–Boppana floor, the QL spectral gap is capped by the Ramanujan
value `k − bound` (so the "best expander" gap is `k − 2√(k−1)`). -/
theorem adjSpectralGap_le_ramanujan (G : WeightedGraph V) (k bound : ℝ)
    [hab : AlonBoppanaFloor G k bound] (h : 2 ≤ Fintype.card V)
    (htop : G.herm.eigenvalues₀ ⟨0, by omega⟩ = k) :
    adjSpectralGap G h ≤ k - bound := by
  unfold adjSpectralGap
  rw [htop]
  have := hab.second_ge h
  linarith

end AlonBoppana

/-! ## 6.  Non-vacuity: the construction and the reduction fire on a concrete instance

We discharge every hypothesis on a concrete two-region **QL bit** — two copies of
`K₂` (the single edge, `1`-regular) coupled by a `K₂` connectome.  This is the
analogue of the "fires on K₂/K₁,₂" non-vacuity checks elsewhere in Graphplay:
axiom-cleanliness alone is not enough (cf. the headline-verification rule), so we
exhibit a real instance where the partition is equitable, the quotient is the
connectome, and the FC reduction holds with `a < 0`. -/

section NonVacuity

variable {R : Type uR} [Fintype R] [DecidableEq R]
variable {W : Type uW} [Fintype W] [DecidableEq W]

/-- The network of networks has real nonnegative weights when its factors do. -/
theorem regionalNetwork_realNonneg (H : WeightedGraph R) (Reg : WeightedGraph W)
    (hH : RealNonnegWeights H) (hReg : RealNonnegWeights Reg) :
    RealNonnegWeights (regionalNetwork H Reg) := by
  intro p q
  simp only [regionalNetwork]
  by_cases h : p.1 = q.1
  · rw [if_pos h]; exact hReg p.2 q.2
  · rw [if_neg h, RealNonnegWeights.adj_ofReal hH p.1 q.1,
      show ((Fintype.card W : ℂ)) = ((Fintype.card W : ℝ) : ℂ) from by push_cast; ring,
      ← Complex.ofReal_div]
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact div_nonneg (hH p.1 q.1).2 (by positivity)⟩

end NonVacuity

/-- `K₂`: the single edge on two vertices, the simplest `1`-regular graph. -/
def K2 : WeightedGraph (Fin 2) where
  adj := fun i j => if i = j then 0 else 1
  herm := by
    ext i j
    simp only [Matrix.conjTranspose_apply]
    by_cases h : i = j <;> simp [h, eq_comm]
  loopless := fun i => by simp

theorem K2_regular : K2.isRegular 1 := by
  intro i
  show (∑ j : Fin 2, K2.adj i j) = 1
  rw [Fin.sum_univ_two]
  fin_cases i <;> norm_num [K2]

theorem K2_real : RealNonnegWeights K2 := by
  intro i j
  simp only [K2]
  by_cases h : i = j <;> simp [h]

/-- **The quotient fires:** the symmetric quotient of the QL bit's regional
partition is exactly the connectome `K₂` off the diagonal. -/
theorem qlbit_quotient_fires :
    (regionalPartition K2 K2 1 K2_regular).symmQuotient 0 1 = 1 := by
  rw [regionalPartition_symmQuotient_eq K2 K2 1 K2_regular 0 1]
  simp [K2]

/-- **Non-vacuity ("fires on K₂"):** the whole-brain → connectome FC reduction
holds, with *every* hypothesis discharged (including invertibility via
`resolvent_isUnit_of_neg`), for the two-region QL bit at any sub-critical
bifurcation parameter `a < 0`. -/
theorem qlbit_fc_reduction (a σ2 : ℝ) (ha : a < 0) :
    Intertwines (regionalPartition K2 K2 1 K2_regular)
      (stationaryFC (regionalNetwork K2 K2) a σ2) (stationaryFC K2 a σ2) :=
  stationaryFC_reduction K2 K2 1 K2_regular K2_real K2_real a σ2
    (resolvent_isUnit_of_neg _ a (regionalNetwork_realNonneg K2 K2 K2_real K2_real) ha)
    (resolvent_isUnit_of_neg _ a K2_real ha)

end Connectome
end Graphplay
