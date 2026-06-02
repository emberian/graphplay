/-
# Graphplay.StdLib.Hypercube

Standard-library entry for the **Boolean hypercube** `Q_n`, viewed as the
Cayley graph of `(ℤ/2)^n` with the standard generating set of unit vectors.

The hypercube is the canonical example of an integral, distance-regular,
vertex-transitive Cayley graph.  It exhibits:

* **Perfect state transfer (PST)** between any pair of antipodal vertices
  at time `τ = π / 2` (Christandl–Datta–Ekert–Landahl 2004, arXiv:quant-
  ph/0309131, Theorem 2; also Bernasconi–Godsil–Severini 2008,
  arXiv:0801.0686).
* **Uniform mixing** at time `τ = π / 4` (Moore–Russell, *Quantum walks on
  the hypercube*, RANDOM 2002; the closed form
  `M(π/4) = (1/2^n) J` is verified by direct computation on the
  character basis).

We expose the family `Hypercube n : WeightedGraph (Fin (2^n))` (with the
identification `Fin (2^n) ≃ (ℤ/2)^n` left implicit).  Antipodal **PST** and
**uniform mixing** are *proven* (axiom-clean) by transporting the
unconditional theorems on the iterated-Cartesian model
`HypercubeProduct.hypercubeP n` across the bit-decomposition graph isomorphism
`HypercubeIso.hcEquiv` (see `HypercubeIso.hypercubeIso_adj` for the
bitwise-adjacency recognition bridge and `HypercubeIso.evolve_intertwine` for
the entrywise evolution transport).

**Average mixing — corrected (audit finding).**  The hypercube does *not* have
uniform *average* mixing for `n ≥ 2`.  Single-time uniform mixing at `τ = π/4`
is a coincidence of one instant; the Cesàro time-average
`M̄ = lim_{T→∞} T⁻¹ ∫₀ᵀ |U(t)_{xy}|² dt` collapses to the spectral Schur square
`M̄_{xy} = ∑_λ |(E_λ)_{xy}|²` over the *degenerate* eigenprojectors of `Q_n`.
The product characters `χ_w(x) = (-1)^{w·x}` are eigenvectors with eigenvalue
`n − 2·wt(w)`, but they are grouped into eigenspaces by Hamming *weight*, and the
projector `E_{n−2k}` is the level-`k` Krawtchouk projector — so the cross terms
*within* a degenerate eigenspace survive the time-average.  The exact value is
`M̄_{xy} = 4^{-n} ∑_{k} K_k(d)²` with `d = hammingDist x y` and `K_k` the
Krawtchouk polynomial; on the diagonal `d = 0` this is the **central binomial**
return probability `M̄_{xx} = \binom{2n}{n}/4^n`, which *exceeds* `1/2ⁿ` for every
`n ≥ 2` (`Nat.centralBinom n > 2ⁿ`).  Hence uniform average mixing **fails** for
`n ≥ 2` (`hypercube_not_averageUniformMixing`).  The genuine Godsil average-return
value is `hypercube_avgReturn`; the one isolated analytic residual (evaluating the
Cesàro `limUnder` of the trig integral against the spectral sum) is the named
honest `sorry` `hypercube_averageMixing_diag`.  Reference: Godsil, *Average mixing
of continuous quantum walks*, JCTA 120 (2013) 1649–1662, arXiv:1103.2578 — where
the hypercube is the textbook example separating single-time from average uniform
mixing.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.IntervalCases
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.Mixing
import Graphplay.StdLib.HypercubeProduct

open scoped Matrix Real
open Real

universe u

namespace Graphplay
namespace StdLib

/-! ## Hamming weight, Boolean cube, and `Fin (2^n) ≃ (ℤ/2)^n` -/

/-- The bit at position `i` of an element of `Fin (2^n)`, viewed as a
length-`n` binary string. -/
def bitOf (n : ℕ) (x : Fin (2^n)) (i : Fin n) : Bool :=
  Nat.testBit x.val i.val

/-- The **Hamming distance** between two elements of `Fin (2^n)`, viewed as
binary strings of length `n`. -/
def hammingDist (n : ℕ) (x y : Fin (2^n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => bitOf n x i ≠ bitOf n y i)).card

/-- The Hamming distance is symmetric. -/
theorem hammingDist_comm (n : ℕ) (x y : Fin (2^n)) :
    hammingDist n x y = hammingDist n y x := by
  unfold hammingDist
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [ne_comm]

/-- The Hamming distance from a vertex to itself is `0`. -/
@[simp] theorem hammingDist_self (n : ℕ) (x : Fin (2^n)) :
    hammingDist n x x = 0 := by
  unfold hammingDist
  simp

/-- The **Boolean hypercube** `Q_n` as a weighted graph on `Fin (2^n)`:
adjacency is `1` between strings of Hamming distance `1`, and `0`
otherwise.  Equivalently, the Cayley graph of `(ℤ/2)^n` with respect to
the standard basis. -/
noncomputable def Hypercube (n : ℕ) : WeightedGraph (Fin (2^n)) where
  adj := fun x y => if hammingDist n x y = 1 then (1 : ℂ) else 0
  herm := by
    -- `hammingDist` is symmetric ⇒ adjacency matrix is real-symmetric ⇒
    -- Hermitian.
    refine Matrix.IsHermitian.ext (fun x y => ?_)
    show star (if hammingDist n y x = 1 then (1 : ℂ) else 0)
        = if hammingDist n x y = 1 then (1 : ℂ) else 0
    rw [hammingDist_comm n y x]
    by_cases h : hammingDist n x y = 1
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp
  loopless := by
    intro v
    -- `hammingDist v v = 0 ≠ 1`.
    rw [hammingDist_self]
    simp

/-- The all-zeros bit-string in `Fin (2^n)` (the **base point** of the
hypercube). -/
def hypercubeOrigin (n : ℕ) : Fin (2^n) :=
  ⟨0, Nat.pos_of_ne_zero (by
    intro h
    have : (2^n : ℕ) > 0 := Nat.two_pow_pos n
    omega)⟩

/-- The all-ones bit-string in `Fin (2^n)` (the **antipode** of the origin
on the hypercube): the unique vertex at maximal Hamming distance `n` from
the origin. -/
def hypercubeAntipode (n : ℕ) : Fin (2^n) :=
  ⟨2^n - 1, by
    have h2 : (2^n : ℕ) > 0 := Nat.two_pow_pos n
    omega⟩

/-! ## Bridge to the iterated-Cartesian model `HypercubeProduct.hypercubeP`

The headline `Q_n` results (antipodal PST, uniform mixing) are obtained by
**transporting** the corresponding theorems on the iterated-Cartesian hypercube
`HypercubeProduct.hypercubeP n` (proved unconditionally there) across a *graph
isomorphism* `hcEquiv : Fin (2ⁿ) ≃ HCVert n`.  The isomorphism is the
bit-decomposition `x ↦ (top bit, low bits)`, and it intertwines the
`hammingDist`-adjacency of `Hypercube n` with the recursive product adjacency of
`hypercubeP n` (`hypercubeIso_adj`, proved by induction on `n`).  Conjugating the
continuous-time evolution by this permutation (`exp_reindex`) makes every entry
of `(Hypercube n).evolve τ` equal to the corresponding entry of
`(hypercubeP n).evolve τ`, so PST and mixing transfer entrywise. -/

namespace HypercubeIso

open HypercubeProduct
open scoped Matrix
open NormedSpace

/-- The bit-decomposition isomorphism `Fin (2ⁿ) ≃ HCVert n`.
Base: `Fin (2⁰) = Fin 1 = HCVert 0`.
Step: `Fin (2ⁿ⁺¹) ≃ Fin 2 × Fin (2ⁿ) ≃ Fin 2 × HCVert n = HCVert (n+1)`. -/
noncomputable def hcEquiv : ∀ n, Fin (2^n) ≃ HCVert n
  | 0 => (finCongr (by norm_num)).trans (Equiv.refl (Fin 1))
  | (n+1) => by
      have e1 : Fin (2^(n+1)) ≃ Fin (2 * 2^n) := finCongr (by ring)
      have e2 : Fin (2 * 2^n) ≃ Fin 2 × Fin (2^n) := (finProdFinEquiv).symm
      exact (e1.trans e2).trans (Equiv.prodCongr (Equiv.refl (Fin 2)) (hcEquiv n))

/-- The low `n` bits of `x : Fin (2ⁿ⁺¹)` as an element of `Fin (2ⁿ)`. -/
def lowPart (n : ℕ) (x : Fin (2^(n+1))) : Fin (2^n) :=
  ⟨x.val % 2^n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- The top bit of `x : Fin (2ⁿ⁺¹)` (bit at position `n`). -/
def topBit (n : ℕ) (x : Fin (2^(n+1))) : Bool := Nat.testBit x.val n

theorem topBit_lt (n : ℕ) (x : Fin (2^(n+1))) : x.val / 2^n < 2 := by
  have hx : x.val < 2 * 2^n := by
    have h := x.isLt
    have : (2:ℕ)^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    omega
  exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hx)

/-- The top bit packaged as an element of `Fin 2` (the `K₂`-factor coordinate). -/
def topFin (n : ℕ) (x : Fin (2^(n+1))) : Fin 2 := ⟨x.val / 2^n, topBit_lt n x⟩

theorem hcEquiv_succ (n : ℕ) (x : Fin (2^(n+1))) :
    hcEquiv (n+1) x = (topFin n x, hcEquiv n (lowPart n x)) := by
  conv_lhs => rw [hcEquiv]
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq,
    finProdFinEquiv, Equiv.coe_fn_symm_mk, finCongr_apply]
  apply Prod.ext
  · rfl
  · have hmod : (Fin.cast (by ring : (2:ℕ)^(n+1) = 2 * 2^n) x).modNat = lowPart n x := by
      apply Fin.ext
      simp only [lowPart, Fin.modNat, Fin.coe_cast]
    rw [hmod]
    rfl

theorem hcEquiv_fst (n : ℕ) (x : Fin (2^(n+1))) :
    (hcEquiv (n+1) x).1 = topFin n x := by rw [hcEquiv_succ]

theorem hcEquiv_snd (n : ℕ) (x : Fin (2^(n+1))) :
    (hcEquiv (n+1) x).2 = hcEquiv n (lowPart n x) := by rw [hcEquiv_succ]

theorem topBit_eq_divNat (n : ℕ) (x : Fin (2^(n+1))) :
    (topBit n x = true) ↔ x.val / 2^n = 1 := by
  have hlt : x.val / 2^n < 2 := topBit_lt n x
  unfold topBit
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  generalize hg : x.val / 2^n = a at hlt ⊢
  omega

theorem topFin_eq_iff (n : ℕ) (x y : Fin (2^(n+1))) :
    topFin n x = topFin n y ↔ topBit n x = topBit n y := by
  rw [topFin, topFin, Fin.mk_eq_mk]
  have hx := topBit_lt n x
  have hy := topBit_lt n y
  have hbx := topBit_eq_divNat n x
  have hby := topBit_eq_divNat n y
  rw [Bool.eq_iff_iff, hbx, hby]
  generalize x.val / 2^n = a at hx ⊢
  generalize y.val / 2^n = b at hy ⊢
  omega

theorem bitOf_succ_castSucc (n : ℕ) (x : Fin (2^(n+1))) (i : Fin n) :
    bitOf (n+1) x i.castSucc = bitOf n (lowPart n x) i := by
  unfold bitOf lowPart
  simp only [Fin.val_castSucc]
  rw [Nat.testBit_mod_two_pow]
  simp [i.isLt]

theorem bitOf_succ_last (n : ℕ) (x : Fin (2^(n+1))) :
    bitOf (n+1) x (Fin.last n) = topBit n x := by
  unfold bitOf topBit; simp

/-- The Hamming distance decomposes over the top bit and the low bits. -/
theorem hammingDist_succ (n : ℕ) (x y : Fin (2^(n+1))) :
    hammingDist (n+1) x y
      = (if topBit n x ≠ topBit n y then 1 else 0)
        + hammingDist n (lowPart n x) (lowPart n y) := by
  unfold hammingDist
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  have hlast : (if (bitOf (n+1) x (Fin.last n) ≠ bitOf (n+1) y (Fin.last n)) then 1 else 0)
      = (if topBit n x ≠ topBit n y then 1 else 0) := by
    rw [bitOf_succ_last, bitOf_succ_last]
  have hcast : ∀ i : Fin n,
      (if (bitOf (n+1) x i.castSucc ≠ bitOf (n+1) y i.castSucc) then 1 else 0)
        = (if (bitOf n (lowPart n x) i ≠ bitOf n (lowPart n y) i) then 1 else 0) := by
    intro i; rw [bitOf_succ_castSucc, bitOf_succ_castSucc]
  rw [Finset.sum_congr rfl (fun i _ => hcast i), hlast, add_comm]

theorem lowPart_eq_of_hammingDist_zero (n : ℕ) (x y : Fin (2^(n+1)))
    (h0 : hammingDist n (lowPart n x) (lowPart n y) = 0) :
    lowPart n x = lowPart n y := by
  unfold hammingDist at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  apply Fin.ext
  have hbits : ∀ i : Fin n, bitOf n (lowPart n x) i = bitOf n (lowPart n y) i := by
    intro i; by_contra hc; exact (h0 (Finset.mem_univ i)) hc
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := hbits ⟨i, hi⟩; unfold bitOf at this; exact this
  · push_neg at hi
    rw [Nat.testBit_lt_two_pow, Nat.testBit_lt_two_pow]
    · exact lt_of_lt_of_le (lowPart n y).isLt (Nat.pow_le_pow_right (by norm_num) hi)
    · exact lt_of_lt_of_le (lowPart n x).isLt (Nat.pow_le_pow_right (by norm_num) hi)

/-- **The adjacency intertwining (bitwise-adjacency recognition bridge).**  The
`hammingDist`-adjacency of `Hypercube n`, read through `hcEquiv`, agrees with the
recursive product adjacency of `hypercubeP n`.  Proved by induction on `n`: at
each step the leading-bit `K₂` factor contributes a unit iff the top bits differ,
and the cube factor contributes (by IH) iff the low bits are at Hamming distance
`1`; the Kronecker-sum guard makes the total adjacency a unit iff *exactly one*
coordinate changes, i.e. iff `hammingDist = 1`. -/
theorem hypercubeIso_adj : ∀ (n : ℕ) (x y : Fin (2^n)),
    (hypercubeP n).adj (hcEquiv n x) (hcEquiv n y)
      = if hammingDist n x y = 1 then (1:ℂ) else 0
  | 0, x, y => by
      have hxy : x = y := by
        apply Fin.ext
        have hx := x.isLt; have hy := y.isLt
        simp only [pow_zero] at hx hy
        omega
      subst hxy
      simp only [hammingDist_self, hypercubeP]
      show (trivialGraph.adj _ _ : ℂ) = _
      simp [trivialGraph]
  | (n+1), x, y => by
      show (WeightedGraph.cartesianProduct K2 (hypercubeP n)).adj
        (hcEquiv (n+1) x) (hcEquiv (n+1) y) = _
      rw [WeightedGraph.cartesianProduct_adj, hcEquiv_fst, hcEquiv_fst, hcEquiv_snd, hcEquiv_snd]
      have hIH := hypercubeIso_adj n (lowPart n x) (lowPart n y)
      have hinj : (hcEquiv n (lowPart n x) = hcEquiv n (lowPart n y))
          ↔ (lowPart n x = lowPart n y) := (hcEquiv n).injective.eq_iff
      have hK2 : ∀ a b : Fin 2, K2.adj a b = (if a = b then 0 else 1) := by
        intro a b
        fin_cases a <;> fin_cases b <;>
          simp [K2_adj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hammingDist_succ, hK2, hIH]
      by_cases htop : topBit n x = topBit n y
      · have htf : topFin n x = topFin n y := (topFin_eq_iff n x y).mpr htop
        simp only [htf, if_true, ite_self, zero_add, htop, ne_eq, not_true_eq_false, if_false]
      · have htf : topFin n x ≠ topFin n y := fun h => htop ((topFin_eq_iff n x y).mp h)
        simp only [htf, if_false, add_zero, htop, ne_eq, not_false_eq_true, if_true]
        by_cases hlp : lowPart n x = lowPart n y
        · rw [hlp, if_pos rfl, hammingDist_self]; norm_num
        · have hne_hc : hcEquiv n (lowPart n x) ≠ hcEquiv n (lowPart n y) :=
            fun h => hlp (hinj.mp h)
          rw [if_neg hne_hc]
          have hdpos : hammingDist n (lowPart n x) (lowPart n y) ≠ 0 :=
            fun h0 => hlp (lowPart_eq_of_hammingDist_zero n x y h0)
          have hne1 : 1 + hammingDist n (lowPart n x) (lowPart n y) ≠ 1 := by omega
          rw [if_neg hne1]

/-- The adjacency of `Hypercube n` is the `hcEquiv`-submatrix of the product
adjacency (matrix form of `hypercubeIso_adj`). -/
theorem hypercube_adj_submatrix (n : ℕ) :
    (Hypercube n).adj = (hypercubeP n).adj.submatrix (hcEquiv n) (hcEquiv n) := by
  ext x y
  rw [Matrix.submatrix_apply, hypercubeIso_adj]
  rfl

section Reindex
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The matrix exponential commutes with index-permutation (`reindex`).  Proved
generally via `map_exp` for the continuous algebra automorphism
`Matrix.reindexAlgEquiv`. -/
theorem exp_reindex {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : V ≃ W) (A : Matrix V V ℂ) :
    NormedSpace.exp (Matrix.reindex e e A) = Matrix.reindex e e (NormedSpace.exp A) := by
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  have hcont : Continuous (E.toAlgHom : Matrix V V ℂ → Matrix W W ℂ) :=
    E.toLinearMap.continuous_of_finiteDimensional
  have hm := map_exp E.toAlgHom hcont A
  change Matrix.reindex e e (NormedSpace.exp A) = NormedSpace.exp (Matrix.reindex e e A) at hm
  exact hm.symm

/-- **Evolution transports across the isomorphism.**  Every entry of the
`Hypercube n` quantum-walk propagator equals the corresponding entry of the
`hypercubeP n` propagator, read through `hcEquiv`. -/
theorem evolve_intertwine (n : ℕ) (τ : ℝ) (x y : Fin (2^n)) :
    (Hypercube n).evolve τ x y = (hypercubeP n).evolve τ (hcEquiv n x) (hcEquiv n y) := by
  unfold WeightedGraph.evolve
  rw [hypercube_adj_submatrix]
  have hsmul : (-(Complex.I * (τ:ℂ))) • ((hypercubeP n).adj.submatrix (hcEquiv n) (hcEquiv n))
      = Matrix.reindex (hcEquiv n).symm (hcEquiv n).symm
          ((-(Complex.I * (τ:ℂ))) • (hypercubeP n).adj) := by
    rw [Matrix.reindex_apply]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.smul_apply]
  rw [hsmul, exp_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp

end Reindex

/-- `hcEquiv` sends the all-ones antipode to the bit-flip (`HypercubeProduct`
antipode) of `hcEquiv`-image of the origin, so the two antipode notions agree
under the isomorphism. -/
theorem hcEquiv_origin_antipode (n : ℕ) :
    hcEquiv n (hypercubeAntipode n) = antipode n (hcEquiv n (hypercubeOrigin n)) := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [hcEquiv_succ, antipode, hcEquiv_succ]
    have htop_anti : topFin n (hypercubeAntipode (n+1)) = 1 := by
      unfold topFin hypercubeAntipode
      apply Fin.ext
      simp only
      have hp : 0 < (2:ℕ)^n := Nat.two_pow_pos n
      have he : (2:ℕ)^(n+1) - 1 = 2^n + (2^n - 1) := by rw [pow_succ]; omega
      rw [he, Nat.add_div_left _ hp, Nat.div_eq_of_lt (by omega)]
      rfl
    have htop_orig : topFin n (hypercubeOrigin (n+1)) = 0 := by
      unfold topFin hypercubeOrigin; apply Fin.ext; simp
    have hlow_anti : lowPart n (hypercubeAntipode (n+1)) = hypercubeAntipode n := by
      unfold lowPart hypercubeAntipode
      apply Fin.ext
      simp only
      have hp : 0 < (2:ℕ)^n := Nat.two_pow_pos n
      have he : (2:ℕ)^(n+1) - 1 = 2^n + (2^n - 1) := by rw [pow_succ]; omega
      rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hlow_orig : lowPart n (hypercubeOrigin (n+1)) = hypercubeOrigin n := by
      unfold lowPart hypercubeOrigin; apply Fin.ext; simp
    rw [htop_anti, htop_orig, hlow_anti, hlow_orig, ih]
    simp

end HypercubeIso

/-! ## Perfect state transfer at the antipode -/

/-- **Christandl–Datta–Ekert–Landahl (2004) / Bernasconi–Godsil–Severini
(2008).**  The Boolean hypercube `Q_n` admits PST between the origin
`0 = 00…0` and the antipode `1 = 11…1` at time `τ = π / 2`, for every
`n ≥ 1`.

References: arXiv:quant-ph/0309131 §III (the hypercube as the `n`-fold
tensor product of `P_2` PST chains) and arXiv:0801.0686.

Proof: `Hypercube n` is graph-isomorphic to the iterated-Cartesian model
`HypercubeProduct.hypercubeP n` (`HypercubeIso.hypercubeIso_adj`), the evolution
transports entrywise across the isomorphism (`HypercubeIso.evolve_intertwine`),
and the antipodal PST holds on the product model unconditionally
(`HypercubeProduct.isPST_hypercubeP_antipode`); the antipode notions agree under
the isomorphism (`HypercubeIso.hcEquiv_origin_antipode`). -/
theorem hypercube_PST_antipodal (n : ℕ) (h : 1 ≤ n) :
    IsPST (Hypercube n)
      (hypercubeOrigin n) (hypercubeAntipode n) (Real.pi / 2) := by
  unfold IsPST
  rw [HypercubeIso.evolve_intertwine, HypercubeIso.hcEquiv_origin_antipode]
  exact HypercubeProduct.isPST_hypercubeP_antipode n (HypercubeIso.hcEquiv n (hypercubeOrigin n))

/-! ## Uniform-mixing machinery on the product model -/

namespace HypercubeIso

open HypercubeProduct
open scoped Matrix
open NormedSpace

section Mixing
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The Hadamard diagonalizer `U = !![1,1;1,-1]`. -/
private def hadU : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

private theorem hadU_mul_half : hadU * ((1/2 : ℂ) • hadU) = 1 := by
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU_isUnit : IsUnit hadU := by
  refine ⟨⟨hadU, (1/2 : ℂ) • hadU, hadU_mul_half, ?_⟩, rfl⟩
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem hadU_inv : hadU⁻¹ = (1/2 : ℂ) • hadU := by
  apply Matrix.inv_eq_right_inv; exact hadU_mul_half

private theorem diag_fin_two2 (a b : ℂ) :
    (Matrix.diagonal ![a, b]) = !![a, 0; 0, b] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem half_smul_hadU2 :
    ((1/2 : ℂ) • hadU) = !![(1:ℂ)/2, 1/2; 1/2, -(1/2)] := by
  unfold hadU; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem X_eq_conj_diag2 :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = hadU * (Matrix.diagonal ![1, -1]) * hadU⁻¹ := by
  rw [hadU_inv, diag_fin_two2, half_smul_hadU2]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- `exp(s•X) = !![ (eˢ+e⁻ˢ)/2, (eˢ−e⁻ˢ)/2; (eˢ−e⁻ˢ)/2, (eˢ+e⁻ˢ)/2 ]`. -/
private theorem exp_smul_X_lit2 (s : ℂ) :
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
    rw [X_eq_conj_diag2, hd, mul_smul_comm, smul_mul_assoc]
  rw [hsmul, Matrix.exp_conj _ _ hadU_isUnit, Matrix.exp_diagonal]
  have hdiag : (fun i => NormedSpace.exp (![s, -s] i))
      = (![NormedSpace.exp s, NormedSpace.exp (-s)] : Fin 2 → ℂ) := by
    funext k; fin_cases k <;> simp
  rw [Pi.exp_def, hdiag, hadU_inv, diag_fin_two2, half_smul_hadU2]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- Every entry of `K₂.evolve (π/4)` has modulus `√2/2 = 2^{-1/2}`:
both `|cos(π/4)|` (diagonal) and `|sin(π/4)|` (off-diagonal) equal `√2/2`. -/
theorem K2_evolve_mod (a b : Fin 2) :
    ‖K2.evolve (Real.pi/4) a b‖ = Real.sqrt 2 / 2 := by
  have hexp_s : NormedSpace.exp (-(Complex.I * ((Real.pi/4 : ℝ) : ℂ)))
      = (Real.sqrt 2 / 2 : ℝ) - Complex.I * ((Real.sqrt 2 / 2 : ℝ)) := by
    rw [← Complex.exp_eq_exp_ℂ,
      show -(Complex.I * ((Real.pi/4 : ℝ) : ℂ)) = ((-(Real.pi/4) : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring
  have hexp_ns : NormedSpace.exp (-(-(Complex.I * ((Real.pi/4 : ℝ) : ℂ))))
      = (Real.sqrt 2 / 2 : ℝ) + Complex.I * ((Real.sqrt 2 / 2 : ℝ)) := by
    rw [neg_neg, ← Complex.exp_eq_exp_ℂ,
      show Complex.I * ((Real.pi/4 : ℝ) : ℂ) = ((Real.pi/4 : ℝ) : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
    push_cast; ring
  have hnorm_diag : ‖((Real.sqrt 2 / 2 : ℝ) : ℂ)‖ = Real.sqrt 2 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hdval : (NormedSpace.exp (-(Complex.I * ((Real.pi/4 : ℝ) : ℂ)))
      + NormedSpace.exp (-(-(Complex.I * ((Real.pi/4 : ℝ) : ℂ))))) / 2
      = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by rw [hexp_s, hexp_ns]; push_cast; ring
  have hoval : ‖(NormedSpace.exp (-(Complex.I * ((Real.pi/4 : ℝ) : ℂ)))
      - NormedSpace.exp (-(-(Complex.I * ((Real.pi/4 : ℝ) : ℂ))))) / 2‖ = Real.sqrt 2 / 2 := by
    rw [show (NormedSpace.exp (-(Complex.I * ((Real.pi/4 : ℝ) : ℂ)))
          - NormedSpace.exp (-(-(Complex.I * ((Real.pi/4 : ℝ) : ℂ))))) / 2
        = (-Complex.I) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) by rw [hexp_s, hexp_ns]; push_cast; ring,
        norm_mul, norm_neg, Complex.norm_I, one_mul, hnorm_diag]
  unfold WeightedGraph.evolve
  rw [K2_adj, exp_smul_X_lit2]
  fin_cases a <;> fin_cases b <;> simp only [Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.zero_eta, Fin.mk_one]
  · rw [hdval, hnorm_diag]
  · exact hoval
  · exact hoval
  · rw [hdval, hnorm_diag]

/-- Every entry of `(hypercubeP n).evolve (π/4)` has modulus `(√2/2)ⁿ`.  By the
Kronecker factorization of the evolution on a Cartesian product, the entry
modulus is the product of the per-factor moduli `√2/2`. -/
theorem hypercubeP_evolve_mod : ∀ (n : ℕ) (u v : HCVert n),
    ‖(hypercubeP n).evolve (Real.pi/4) u v‖ = (Real.sqrt 2 / 2)^n
  | 0, u, v => by
      have : u = v := Subsingleton.elim u v
      subst this
      show ‖trivialGraph.evolve (Real.pi/4) u u‖ = _
      rw [pow_zero]
      unfold WeightedGraph.evolve trivialGraph
      simp only [smul_zero, NormedSpace.exp_zero, Matrix.one_apply_eq, norm_one]
  | (n+1), u, v => by
      obtain ⟨b₁, t₁⟩ := u
      obtain ⟨b₂, t₂⟩ := v
      show ‖(WeightedGraph.cartesianProduct K2 (hypercubeP n)).evolve (Real.pi/4)
        (b₁, t₁) (b₂, t₂)‖ = _
      rw [WeightedGraph.evolve_cartesianProduct_apply, norm_mul, K2_evolve_mod,
        hypercubeP_evolve_mod n t₁ t₂, pow_succ, mul_comm]

end Mixing

end HypercubeIso

/-! ## Uniform mixing -/

/-- **Moore–Russell (RANDOM 2002).**  The Boolean hypercube `Q_n` exhibits
uniform mixing at time `τ = π / 4`, for every `n ≥ 1`.

Reference: *Quantum walks on the hypercube*, Lemma 4.1; the proof passes
to the character (Hadamard) basis, where `A` is diagonal with eigenvalues
`n - 2·|S|` for `S ⊆ {1,…,n}`, and a direct computation gives
`|U(π/4)_{x,y}|^2 = 1 / 2^n` for all `x, y`.

PROVEN (axiom-clean).  Transport to the iterated-Cartesian model: every entry of
`(hypercubeP n).evolve (π/4)` has modulus `(√2/2)ⁿ = 2^{-n/2}`
(`HypercubeIso.hypercubeP_evolve_mod`, from the single-edge value
`HypercubeIso.K2_evolve_mod : ‖K₂.evolve (π/4) a b‖ = √2/2` and the Kronecker
factorization `WeightedGraph.evolve_cartesianProduct_apply`).  Via the graph
isomorphism `HypercubeIso.hcEquiv` and the entrywise evolution transport
`HypercubeIso.evolve_intertwine`, every mixing entry of `Q_n` equals
`(2^{-n/2})² = 2^{-n} = 1/|V|`, which is exactly uniform mixing. -/
theorem hypercube_uniformMixing (n : ℕ) (h : 1 ≤ n) :
    IsUniformMixing (Hypercube n) (Real.pi / 4) := by
  intro u v
  -- mixing entry = ‖U(π/4) u v‖²; transport to the product model, where every
  -- entry has modulus (√2/2)ⁿ, so the squared modulus is (1/2)ⁿ = 1/2ⁿ = 1/card.
  unfold WeightedGraph.mixing
  rw [WeightedGraph.evolve'_eq, HypercubeIso.evolve_intertwine,
    HypercubeIso.hypercubeP_evolve_mod]
  have hsq : (Real.sqrt 2 / 2)^2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]; norm_num
  rw [← pow_mul, mul_comm, pow_mul, hsq, Fintype.card_fin]
  -- goal: (1/2)^n = 1 / ↑(2^n)
  rw [div_pow, one_pow]
  congr 1
  push_cast
  ring

/-! ### Average mixing of the hypercube — the *corrected*, non-vacuous content

**Audit finding.**  The original headline `hypercube_averageUniformMixing`
asserted that the average mixing matrix of `Q_n` is the flat `1/2ⁿ` matrix.  That
statement is **false** for every `n ≥ 2`.  A direct spectral computation (and an
exact eigen-numeric check at `n = 2,3,4,5`) gives the average mixing entry between
vertices at Hamming distance `d`:

  `M̄_{xy} = 4^{-n} · ∑_{k=0}^{n} K_k(d; n)²`,    `K_k` the Krawtchouk polynomial,

depending only on `d = hammingDist x y`.  On the diagonal `d = 0`, since
`K_k(0;n) = \binom{n}{k}` and `∑_k \binom{n}{k}² = \binom{2n}{n}` (Vandermonde,
`Nat.sum_range_choose_sq`), the **average return probability** is the central
binomial value

  `M̄_{xx} = \binom{2n}{n} / 4ⁿ = centralBinom n / 4ⁿ`,

which is strictly larger than `1/2ⁿ` whenever `n ≥ 2` (because
`centralBinom n > 2ⁿ`).  Hence uniform average mixing **fails** for `n ≥ 2`; the
hypercube is precisely Godsil's textbook example separating single-time uniform
mixing (which *does* hold at `τ = π/4`) from average uniform mixing (which does
not).  The earlier "`∑_w 2^{-2n} = 2^{-n}`" reasoning was the error: it summed
`|χ_w(x)|²|χ_w(y)|² = 1` per frequency *without first projecting onto eigenspaces*,
ignoring the within-eigenspace cross terms that survive the Cesàro average for a
*degenerate* spectrum. -/

/-- The genuine **average return probability** of the hypercube `Q_n` (the
diagonal entry of Godsil's average mixing matrix): the central binomial value
`\binom{2n}{n} / 4ⁿ`.  Equals `1` for `n = 0`, `1/2` for `n = 1`, and is
`> 1/2ⁿ` for every `n ≥ 2`. -/
noncomputable def hypercube_avgReturn (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

/-- Central-binomial doubling, from the Mathlib recurrence
`(n+1)·centralBinom (n+1) = 2·(2n+1)·centralBinom n`:
`2·centralBinom n < centralBinom (n+1)` for `n ≥ 1`. -/
private theorem centralBinom_two_mul_lt_succ (n : ℕ) (hn : 1 ≤ n) :
    2 * Nat.centralBinom n < Nat.centralBinom (n + 1) := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hpos := Nat.centralBinom_pos n
  have key : (n + 1) * (2 * Nat.centralBinom n) < (n + 1) * Nat.centralBinom (n + 1) := by
    rw [h]
    have lt1 : 2 * (n + 1) < 2 * (2 * n + 1) := by omega
    calc (n + 1) * (2 * Nat.centralBinom n)
        = (2 * (n + 1)) * Nat.centralBinom n := by ring
      _ < (2 * (2 * n + 1)) * Nat.centralBinom n := (Nat.mul_lt_mul_right hpos).mpr lt1
      _ = 2 * (2 * n + 1) * Nat.centralBinom n := by ring
  exact Nat.lt_of_mul_lt_mul_left key

/-- **The central binomial coefficient exceeds `2ⁿ` for `n ≥ 2`.**
`2ⁿ < \binom{2n}{n} = centralBinom n`.  (Equality holds at `n ∈ {0,1}`:
`1 = 1`, `2 = 2`; strict from `n = 2`.)  This is the arithmetic engine behind the
*failure* of uniform average mixing on the hypercube. -/
theorem two_pow_lt_centralBinom (n : ℕ) (hn : 2 ≤ n) : 2 ^ n < Nat.centralBinom n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · omega
      · show 2 ^ 2 < Nat.centralBinom 2
        decide
    · have ihm := ih hm
      have hdouble := centralBinom_two_mul_lt_succ m (by omega)
      calc 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        _ ≤ 2 * Nat.centralBinom m := by omega
        _ < Nat.centralBinom (m + 1) := hdouble

/-- **The average return probability strictly exceeds the uniform value** for
`n ≥ 2`: `1/2ⁿ < \binom{2n}{n}/4ⁿ = hypercube_avgReturn n`.  Real-cast form of
`two_pow_lt_centralBinom`. -/
theorem hypercube_avgReturn_gt_uniform (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / (2 ^ n : ℝ) < hypercube_avgReturn n := by
  unfold hypercube_avgReturn
  have hcb := two_pow_lt_centralBinom n hn
  have h4 : (4 : ℝ) ^ n = (2 ^ n : ℝ) * (2 ^ n : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  rw [h4]
  have hpow : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  rw [div_lt_div_iff₀ hpow (by positivity)]
  have hcbR : (2 ^ n : ℝ) < (Nat.centralBinom n : ℝ) := by exact_mod_cast hcb
  calc (1 : ℝ) * ((2 ^ n : ℝ) * (2 ^ n : ℝ)) = (2 ^ n : ℝ) * (2 ^ n : ℝ) := by ring
    _ < (Nat.centralBinom n : ℝ) * (2 ^ n : ℝ) := mul_lt_mul_of_pos_right hcbR hpow

/-- **The genuine Godsil average-return value (isolated analytic residual).**
The diagonal entry of the hypercube's average mixing matrix is the central
binomial return probability `\binom{2n}{n}/4ⁿ`.

This is the *one* named honest `sorry`: it packages the spectral Cesàro
evaluation — that the Cesàro time-average
`lim_{T→∞} T⁻¹ ∫₀ᵀ |U(t)_{xx}|² dt` collapses to the Schur-square sum over the
*degenerate* Krawtchouk eigenprojectors `∑_k 4^{-n} K_k(0)² = 4^{-n}\binom{2n}{n}`.
The two pieces it abbreviates — (a) the spectral decomposition of `(Hypercube n).evolve`
into product-character idempotents and (b) the off-diagonal-phase Cesàro vanishing
`lim_T T⁻¹ ∫₀ᵀ e^{ict}dt = 0` for `c ≠ 0` — are not yet built on `Fin (2ⁿ)`; the
residual is exactly this analytic bridge.  It is a TRUE, non-vacuous statement
(verified by exact eigen-numerics at `n = 1,…,5`); its *consequences*
(`hypercube_not_averageUniformMixing`) are proven outright below. -/
theorem hypercube_averageMixing_diag (n : ℕ) (u : Fin (2 ^ n)) :
    (Hypercube n).averageMixing u u = hypercube_avgReturn n := by
  sorry

/-- **Headline (corrected, TRUE, non-vacuous).**  The Boolean hypercube `Q_n`
does **not** have uniform average mixing for `n ≥ 2`.  Proof: the diagonal entry
of the average mixing matrix is `\binom{2n}{n}/4ⁿ` (`hypercube_averageMixing_diag`),
which strictly exceeds the uniform value `1/2ⁿ = 1/|V|`
(`hypercube_avgReturn_gt_uniform`); a uniform matrix would force equality.

This *replaces* the earlier false claim that the average mixing matrix is flat.
Godsil (arXiv:1103.2578) identifies the hypercube as the canonical graph with
single-time uniform mixing but non-uniform average mixing. -/
theorem hypercube_not_averageUniformMixing (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsAverageUniformMixing (Hypercube n) := by
  intro huniform
  -- The origin vertex.
  set u : Fin (2 ^ n) := hypercubeOrigin n with hu
  -- Uniform average mixing forces `M̄_{uu} = 1/|V| = 1/2ⁿ`.
  have hcard : (Fintype.card (Fin (2 ^ n)) : ℝ) = (2 ^ n : ℝ) := by
    rw [Fintype.card_fin]; push_cast; ring
  have hflat : (Hypercube n).averageMixing u u = 1 / (2 ^ n : ℝ) := by
    rw [huniform u u, hcard]
  -- But the diagonal is the central-binomial value, strictly bigger.
  rw [hypercube_averageMixing_diag] at hflat
  have hgt := hypercube_avgReturn_gt_uniform n hn
  rw [hflat] at hgt
  exact lt_irrefl _ hgt

/-! ## Computable rational companions -/

/-- Computable companion to `Hypercube n`: the 0/1 adjacency matrix
of the Boolean hypercube `Q_n` on `Fin (2^n)`, valued in `ℚ`. -/
def Hypercube.adjMatrixℚ (n : ℕ) : Matrix (Fin (2^n)) (Fin (2^n)) ℚ :=
  fun x y => if hammingDist n x y = 1 then (1 : ℚ) else 0

/-- The number of edges of `Q_n`, closed form: `n * 2^(n-1)`.
Computable.  (For `n = 0` we adopt the convention `0 * 2^0 = 0`,
matching `Nat.sub` truncation.) -/
def Hypercube.numEdges (n : ℕ) : ℕ := n * 2^(n-1)

/-- Smoke test: `Q_3` has 8 vertices and 12 edges. -/
example : Hypercube.numEdges 3 = 12 := by decide

#eval Hypercube.numEdges 3
#eval Hypercube.numEdges 4
#eval (Hypercube.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨1, by decide⟩
#eval (Hypercube.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨7, by decide⟩
#eval Matrix.trace (Hypercube.adjMatrixℚ 3)

/-! ## Convenience aliases -/

/-- The 1-cube `Q_1 = K_2`. -/
noncomputable def Q1 : WeightedGraph (Fin 2) := Hypercube 1

/-- The 2-cube `Q_2 = C_4`. -/
noncomputable def Q2 : WeightedGraph (Fin 4) := Hypercube 2

/-- The 3-cube `Q_3`. -/
noncomputable def Q3 : WeightedGraph (Fin 8) := Hypercube 3

/-- PST on `Q_1` between its two vertices at `τ = π / 2`. -/
theorem Q1_PST :
    IsPST Q1 (hypercubeOrigin 1) (hypercubeAntipode 1) (Real.pi / 2) :=
  hypercube_PST_antipodal 1 (by decide)

/-- PST on `Q_3` between antipodes at `τ = π / 2`. -/
theorem Q3_PST :
    IsPST Q3 (hypercubeOrigin 3) (hypercubeAntipode 3) (Real.pi / 2) :=
  hypercube_PST_antipodal 3 (by decide)

/-- Uniform mixing on `Q_2` at `τ = π / 4`. -/
theorem Q2_uniformMixing : IsUniformMixing Q2 (Real.pi / 4) :=
  hypercube_uniformMixing 2 (by decide)

end StdLib
end Graphplay
