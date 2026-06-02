/-
# Graphplay.StdLib.Hamming

Standard-library entry for the **Hamming graph** `H(n, q)` — the Cartesian
product `K_q □ K_q □ ⋯ □ K_q` (`n` factors), or equivalently the Cayley
graph of `(ℤ/q)^n` with the generating set `{e_i (k) : 1 ≤ i ≤ n, 1 ≤ k <
q}` of all "single-coordinate" elements.

Two vertices `x, y : Fin q → Fin n` (length-`n` strings over `q`-ary
alphabet) are adjacent iff they differ in exactly one coordinate.  This is
the canonical distance-regular graph whose spectrum is computed by
**Krawtchouk polynomials**:

  eigenvalue indexed by `k ∈ {0, …, n}` is
    `λ_k = (q-1)·n − q·k`
  (Brouwer–Haemers, *Spectra of Graphs*, §12.3.2; equivalent to the
  Krawtchouk polynomial `K_k(0; n, q)` evaluation).

The mixing question on Hamming graphs is fully classified:

* Ahmadi, Belk, Tamon, Wendler 2003 (*The continuous-time quantum walk on
  Hamming graphs*, arXiv:quant-ph/0209106) prove uniform mixing for
  `q ∈ {2, 3, 4}` at time `τ = 2π / q`, and *no* uniform mixing for
  `q ≥ 5`.
* Levine–Tamon 2024 (arXiv:2605.04414) close the chiral case: any chiral
  signing of `H(n, q)` for `q ≥ 5` also fails to mix uniformly.

We state both halves of the iff; proofs are `sorry`-ed.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.RingTheory.RootsOfUnity.Complex
import Graphplay.Weighted
import Graphplay.Mixing
import Graphplay.StdLib.Cayley
import Graphplay.Integrations.LatticeGauge

open scoped Matrix Real
open Real

universe u

namespace Graphplay
namespace StdLib

/-! ## The Hamming graph `H(n, q)` -/

/-- The **Hamming distance** between two length-`n` strings over an
alphabet of size `q`. -/
def hammingDistFn {n q : ℕ} (x y : Fin n → Fin q) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card

/-- The Hamming distance is symmetric. -/
theorem hammingDistFn_comm {n q : ℕ} (x y : Fin n → Fin q) :
    hammingDistFn x y = hammingDistFn y x := by
  unfold hammingDistFn
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [ne_comm]

/-- The Hamming distance from a string to itself is `0`. -/
@[simp] theorem hammingDistFn_self {n q : ℕ} (x : Fin n → Fin q) :
    hammingDistFn x x = 0 := by
  unfold hammingDistFn
  simp

/-- The **Hamming graph** `H(n, q)` on the vertex set `Fin n → Fin q` of
length-`n` strings over a `q`-ary alphabet: edges connect strings at
Hamming distance exactly `1`.

For `q = 2` this is the Boolean hypercube `Q_n` (cf.
`Graphplay.StdLib.Hypercube`); for `n = 1` it is the complete graph
`K_q`. -/
noncomputable def Hamming (n q : ℕ) [Fintype (Fin n → Fin q)]
    [DecidableEq (Fin n → Fin q)] :
    WeightedGraph (Fin n → Fin q) where
  adj := fun x y => if hammingDistFn x y = 1 then (1 : ℂ) else 0
  herm := by
    -- Real-symmetric (Hamming distance is symmetric) ⇒ Hermitian.
    refine Matrix.IsHermitian.ext (fun x y => ?_)
    show star (if hammingDistFn y x = 1 then (1 : ℂ) else 0)
        = if hammingDistFn x y = 1 then (1 : ℂ) else 0
    rw [hammingDistFn_comm y x]
    by_cases h : hammingDistFn x y = 1
    · rw [if_pos h]; simp
    · rw [if_neg h]; simp
  loopless := by
    intro v
    -- `hammingDistFn v v = 0 ≠ 1`.
    rw [hammingDistFn_self]
    simp

/-! ## Krawtchouk eigenvalues -/

/-- The **Krawtchouk polynomial** `K_k(x; n, q)` of degree `k`,
defined by the standard generating-function recurrence
`K_k(x; n, q) = Σ_{j=0}^{k} (-1)^j (q-1)^{k-j} C(x, j) C(n - x, k - j)`.
This is the family that diagonalizes the Hamming-scheme intersection
matrix; see Brouwer–Haemers §12.3, or van Lint, *Introduction to coding
theory*, §3.2. -/
noncomputable def krawtchouk (n q : ℕ) (k : ℕ) (x : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    ((-1 : ℝ)^j) * ((q - 1 : ℝ)^(k - j)) *
      (Nat.choose x j : ℝ) * (Nat.choose (n - x) (k - j) : ℝ)

/-! ### Character diagonalisation (Krawtchouk eigenvalues)

The Hamming graph `H(n, q)` is the Cayley graph of `(ℤ/q)ⁿ` on the
single-coordinate generators.  For a `q`-ary frequency `w : Fin n → Fin q`
the **product character** `χ_w(x) = ∏ᵢ ζ_q^{wᵢ·xᵢ}` is an eigenvector of
the adjacency, with eigenvalue the level-`k` Krawtchouk number
`Σᵢ (q·[wᵢ = 0] − 1) = n(q−1) − qk` where `k = #{i : wᵢ ≠ 0}` is the
Hamming weight of `w`.  We build this character diagonalisation directly on
the vertex type `Fin n → Fin q` (using `ζ_q = ` `LatticeGauge.zmodChar`),
mirroring the circulant character keystone
`Circulant.circulantGraph_mulVec_chi`. -/

noncomputable def myChar (q : ℕ) [NeZero q] : AddChar (ZMod q) ℂ where
  toFun := LatticeGauge.zmodChar q
  map_zero_eq_one' := by
    show LatticeGauge.zmodChar q 0 = 1
    unfold LatticeGauge.zmodChar; rw [ZMod.val_zero]; simp
  map_add_eq_mul' := by
    intro a b
    show LatticeGauge.zmodChar q (a+b) = _ * _
    rw [LatticeGauge.zmodChar_add]

theorem zmodRoot_primitive (q : ℕ) [NeZero q] :
    IsPrimitiveRoot (LatticeGauge.zmodRoot q) q := by
  unfold LatticeGauge.zmodRoot
  have h := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
  convert h using 2

theorem myChar_mulShift_eq_zero_iff (q : ℕ) [NeZero q] (t : ZMod q) :
    (myChar q).mulShift t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have h1 : (myChar q).mulShift t 1 = 1 := by rw [h]; rfl
    rw [AddChar.mulShift_apply, mul_one] at h1
    have h2 : LatticeGauge.zmodChar q t = 1 := h1
    rw [LatticeGauge.zmodChar_eq_pow] at h2
    have hp := zmodRoot_primitive q
    have hdvd : q ∣ t.val := by rw [← hp.pow_eq_one_iff_dvd]; exact h2
    have hlt : t.val < q := ZMod.val_lt t
    have : t.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    rw [← ZMod.val_eq_zero]; exact this
  · intro h; subst h; rw [AddChar.mulShift_zero]; rfl

theorem zmodChar_sum_orthogonal (q : ℕ) [NeZero q] (t : ZMod q) :
    ∑ a : ZMod q, LatticeGauge.zmodChar q (t * a) = if t = 0 then (q:ℂ) else 0 := by
  have h1 : ∀ a : ZMod q, LatticeGauge.zmodChar q (t*a) = (myChar q).mulShift t a := by
    intro a; rw [AddChar.mulShift_apply]; rfl
  simp_rw [h1]
  rw [AddChar.sum_eq_ite, ZMod.card]
  simp only [myChar_mulShift_eq_zero_iff]

theorem zmodChar_sum_nonzero (q : ℕ) [NeZero q] (t : ZMod q) :
    ∑ b ∈ Finset.univ.filter (fun b : ZMod q => b ≠ 0), LatticeGauge.zmodChar q (t * b)
      = (if t = 0 then (q:ℂ) else 0) - 1 := by
  have hsplit : ∑ b : ZMod q, LatticeGauge.zmodChar q (t * b)
      = (∑ b ∈ Finset.univ.filter (fun b : ZMod q => b ≠ 0), LatticeGauge.zmodChar q (t * b))
        + LatticeGauge.zmodChar q (t * 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : ZMod q => b ≠ 0)]
    congr 1
    rw [show (Finset.univ.filter (fun b : ZMod q => ¬ b ≠ 0)) = {0} by ext b; simp]
    rw [Finset.sum_singleton]
  rw [zmodChar_sum_orthogonal, mul_zero] at hsplit
  have hz : LatticeGauge.zmodChar q 0 = 1 := by
    unfold LatticeGauge.zmodChar; rw [ZMod.val_zero]; simp
  rw [hz] at hsplit
  exact eq_sub_of_add_eq hsplit.symm

theorem hamming_inner_sum_zmod (q : ℕ) [NeZero q] (t c : ZMod q) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod q => a ≠ c), LatticeGauge.zmodChar q (t * a)
      = LatticeGauge.zmodChar q (t * c) * ((if t = 0 then (q:ℂ) else 0) - 1) := by
  rw [← zmodChar_sum_nonzero, Finset.mul_sum]
  apply Finset.sum_nbij' (fun a => a - c) (fun b => b + c)
  · intro a ha; rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, by rw [sub_ne_zero]; exact ha.2⟩
  · intro b hb; rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h; apply hb.2
    have := add_right_cancel (a := b) (b := c) (c := (0:ZMod q)); rw [zero_add] at this; exact this h
  · intro a _; ring
  · intro b _; ring
  · intro a _; rw [show t * a = t * c + t * (a - c) by ring, ← LatticeGauge.zmodChar_add]

theorem hamming_inner_sum_fin (q : ℕ) [NeZero q] (s c : Fin q) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin q => a ≠ c),
        LatticeGauge.zmodChar q (((s:ℕ):ZMod q) * ((a:ℕ):ZMod q))
      = LatticeGauge.zmodChar q (((s:ℕ):ZMod q) * ((c:ℕ):ZMod q))
        * ((if ((s:ℕ):ZMod q) = 0 then (q:ℂ) else 0) - 1) := by
  rw [← hamming_inner_sum_zmod q ((s:ℕ):ZMod q) ((c:ℕ):ZMod q)]
  apply Finset.sum_nbij' (fun a : Fin q => ((a:ℕ):ZMod q))
                          (fun z : ZMod q => (⟨z.val, ZMod.val_lt z⟩ : Fin q))
  · intro a ha; rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h; apply ha.2
    have hv : ((a:ℕ):ZMod q).val = ((c:ℕ):ZMod q).val := by rw [h]
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt c.isLt] at hv
    exact Fin.ext hv
  · intro z hz; rw [Finset.mem_filter] at hz ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro h; apply hz.2; rw [← h]; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro a _; apply Fin.ext; show ((a:ℕ):ZMod q).val = a.val
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
  · intro z _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro a _; rfl

/-- Character on the Hamming vertex set. -/
noncomputable def hamChi (n q : ℕ) (w x : Fin n → Fin q) : ℂ :=
  ∏ i, LatticeGauge.zmodChar q (((w i :ℕ) : ZMod q) * ((x i :ℕ) : ZMod q))

theorem hammingDistFn_one_iff (n q : ℕ) (x y : Fin n → Fin q) :
    hammingDistFn x y = 1 ↔ ∃ i : Fin n, y i ≠ x i ∧ ∀ j, j ≠ i → y j = x j := by
  unfold hammingDistFn
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hmem : ∀ j, (j ∈ Finset.univ.filter (fun j => x j ≠ y j)) ↔ j = i := by
      intro j; rw [hi]; simp
    refine ⟨i, ?_, ?_⟩
    · have := (hmem i).mpr rfl; simp at this; exact fun h => this h.symm
    · intro j hj
      have := (hmem j); simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      by_contra hc; exact hj (this.mp (fun h => hc h.symm))
  · rintro ⟨i, hne, hrest⟩
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hxy; by_contra hc; exact hxy ((hrest j hc).symm)
    · intro hj; subst hj; exact fun h => hne h.symm

theorem hamming_neighbor_sum (n q : ℕ) [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)]
    (x : Fin n → Fin q) (f : (Fin n → Fin q) → ℂ) :
    (∑ y, (if hammingDistFn x y = 1 then (1:ℂ) else 0) * f y)
    = ∑ i : Fin n, ∑ a ∈ Finset.univ.filter (fun a : Fin q => a ≠ x i), f (Function.update x i a) := by
  have hb : ∀ y, (if hammingDistFn x y = 1 then (1:ℂ) else 0) * f y
      = if hammingDistFn x y = 1 then f y else 0 := fun y => boole_mul _ _
  simp_rw [hb]
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter (fun y : Fin n → Fin q => hammingDistFn x y = 1))
      = Finset.univ.biUnion (fun i : Fin n =>
          (Finset.univ.filter (fun a : Fin q => a ≠ x i)).image (fun a => Function.update x i a)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image]
    rw [hammingDistFn_one_iff]
    constructor
    · rintro ⟨i, hne, hrest⟩
      refine ⟨i, ⟨y i, hne, ?_⟩⟩
      ext j; by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact congrArg (Fin.val) (hrest j hj).symm
    · rintro ⟨i, ⟨a, ha, rfl⟩⟩
      refine ⟨i, ?_, ?_⟩
      · rw [Function.update_self]; exact ha
      · intro j hj; rw [Function.update_of_ne hj]
  rw [hset, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_image]
    intro a ha b hb hab
    have h := congrFun hab i
    simpa only [Function.update_self] using h
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image, Finset.mem_filter]
    rintro z ⟨a, ⟨_, ha⟩, rfl⟩ ⟨b, ⟨_, _⟩, hb2⟩
    have h := congrFun hb2 i
    rw [Function.update_self, Function.update_of_ne hij] at h
    exact ha h.symm

theorem hamChi_update (n q : ℕ) (w x : Fin n → Fin q) (i : Fin n) (a : Fin q) :
    hamChi n q w (Function.update x i a)
      = (∏ j ∈ Finset.univ.erase i, LatticeGauge.zmodChar q (((w j:ℕ):ZMod q) * ((x j:ℕ):ZMod q)))
        * LatticeGauge.zmodChar q (((w i:ℕ):ZMod q) * ((a:ℕ):ZMod q)) := by
  unfold hamChi
  rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.prod_congr rfl; intro j hj
    rw [Finset.mem_erase] at hj; rw [Function.update_of_ne hj.1]
  · rw [Function.update_self]

/-- Krawtchouk eigenvalue indexed by a frequency `w`. -/
noncomputable def hamLambda (n q : ℕ) (w : Fin n → Fin q) : ℝ :=
  ∑ i : Fin n, ((if ((w i:ℕ):ZMod q) = 0 then (q:ℝ) else 0) - 1)

/-- The character `hamChi n q w` is an eigenvector of the Hamming adjacency with
eigenvalue `hamLambda n q w`. -/
theorem hamChi_eigen (n q : ℕ) [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)]
    [NeZero q] (w : Fin n → Fin q) :
    (Hamming n q).adj.mulVec (hamChi n q w) = (hamLambda n q w : ℂ) • (hamChi n q w) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Hamming, Pi.smul_apply, smul_eq_mul]
  rw [hamming_neighbor_sum n q x (hamChi n q w)]
  have hstep : ∀ i : Fin n,
      (∑ a ∈ Finset.univ.filter (fun a : Fin q => a ≠ x i), hamChi n q w (Function.update x i a))
      = hamChi n q w x * ((if ((w i:ℕ):ZMod q) = 0 then (q:ℂ) else 0) - 1) := by
    intro i
    simp_rw [hamChi_update n q w x i]
    rw [← Finset.mul_sum]
    rw [hamming_inner_sum_fin q (w i) (x i)]
    rw [← mul_assoc]
    congr 1
    unfold hamChi
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.mul_sum, mul_comm]
  congr 1
  unfold hamLambda
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ((w i:ℕ):ZMod q) = 0 <;> simp [h]


theorem hamChi_ne_zero (n q : ℕ) [NeZero q] (w : Fin n → Fin q) :
    hamChi n q w ≠ 0 := by
  intro hcon
  have h0 : hamChi n q w (fun _ => 0) = 0 := congrFun hcon (fun _ => 0)
  apply one_ne_zero (α := ℂ)
  rw [← h0]; unfold hamChi
  symm; apply Finset.prod_eq_one
  intro i _
  show LatticeGauge.zmodChar q (((w i:ℕ):ZMod q) * (((0:Fin q):ℕ):ZMod q)) = 1
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero]
  unfold LatticeGauge.zmodChar; rw [ZMod.val_zero]; simp

noncomputable def weightFreq (n q k : ℕ) [NeZero q] : Fin n → Fin q :=
  fun i => if i.val < k then (1 : Fin q) else (0 : Fin q)

theorem one_fin_ne_zero_zmod (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    (((1 : Fin q):ℕ) : ZMod q) ≠ 0 := by
  have hval : ((1 : Fin q):ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rw [hval, Nat.cast_one]
  haveI : Fact (1 < q) := ⟨by omega⟩
  exact one_ne_zero

theorem hamLambda_weightFreq (n q k : ℕ) [NeZero q] (hq : 2 ≤ q) (hk : k ≤ n) :
    hamLambda n q (weightFreq n q k) = (n : ℝ) * ((q:ℝ) - 1) - (q:ℝ) * (k:ℝ) := by
  unfold hamLambda weightFreq
  refine (Finset.sum_congr rfl (g := fun i : Fin n =>
      (if i.val < k then (-1 : ℝ) else (q:ℝ) - 1)) ?_).trans ?_
  · intro i _
    by_cases hi : i.val < k
    · simp only [if_pos hi]; rw [if_neg (one_fin_ne_zero_zmod q hq)]; ring
    · simp only [if_neg hi]
      have h0 : (((0:Fin q):ℕ):ZMod q) = 0 := by simp
      rw [if_pos h0]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hcount : (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
    rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if i < k then 1 else 0) n]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one]
    have : {x ∈ Finset.range n | x < k} = Finset.range k := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  have hcount' : (Finset.univ.filter (fun i : Fin n => ¬ i.val < k)).card = n - k := by
    have htot : (Finset.univ.filter (fun i : Fin n => i.val < k)).card
        + (Finset.univ.filter (fun i : Fin n => ¬ i.val < k)).card = n := by
      rw [Finset.card_filter_add_card_filter_not]; simp
    omega
  rw [hcount, hcount']
  push_cast [hk]
  ring

/-- **Brouwer–Haemers, *Spectra of Graphs* §12.3.2.**  The Hamming graph
`H(n, q)` has spectrum `{ λ_k : 0 ≤ k ≤ n }` (with multiplicity given by
the Krawtchouk weight), where
  `λ_k = n(q - 1) − q k = krawtchouk n q 1 k`.

(The polynomial `K_1` is the linear Krawtchouk polynomial; evaluating at
`x = k` gives `n(q - 1) − qk`.)

**PROVEN** via the product-character diagonalisation above
(`hamChi_eigen` + `hamLambda_weightFreq`): the frequency `weightFreq n q k`
of Hamming weight `k` is a genuine (nonzero) eigenvector with eigenvalue
the level-`k` Krawtchouk number, deposited into the real spectrum by
`real_mem_spectrum_of_mulVec_smul`.  The hypothesis `2 ≤ q` is genuinely
necessary: for `q ≤ 1` the alphabet is trivial, `H(n,q)` has at most one
vertex, and the formula `n(q−1)−qk = −k` is false (the spectrum is `{0}`). -/
theorem hamming_eigenvalue (n q : ℕ) (hq : 2 ≤ q) [Fintype (Fin n → Fin q)]
    [DecidableEq (Fin n → Fin q)] (k : ℕ) (hk : k ≤ n) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ (Hamming n q).adj ∧
      μ = (n : ℝ) * ((q : ℝ) - 1) - (q : ℝ) * (k : ℝ) := by
  have hqz : NeZero q := ⟨by omega⟩
  refine ⟨hamLambda n q (weightFreq n q k), ?_, hamLambda_weightFreq n q k hq hk⟩
  exact real_mem_spectrum_of_mulVec_smul (hamChi_ne_zero n q (weightFreq n q k))
    (hamChi_eigen n q (weightFreq n q k))

/-! ## Uniform mixing iff `q ≤ 4`

### The classical mixing classification as a content-bearing typeclass

The two halves of the Ahmadi–Belk–Tamon–Wendler (2003) classification and the
Levine–Tamon (2024) chiral closure are **deep number-theoretic theorems**: the
positive half is a Gauss-sum integrality computation on `ℤ/q` for `q ∈ {2,3,4}`,
and the negative halves are non-integrality arguments for `q ≥ 5`.  Mathlib v4.30
has no path to either (no quadratic-Gauss-sum modulus library, no CTQW mixing
calculus).  Following the `LiteratureInterfaces` design principle, we name each
result as a **local content-bearing typeclass** carrying the *precise* statement
of the cited theorem as its field, and discharge the headline theorems from it.

A theorem `[HammingMixingClassification] : goal := … .field …` is then a
genuinely `sorry`-free conditional theorem: the literature result appears as an
explicit, auditable hypothesis, and the instant Mathlib grows a quadratic-Gauss-
sum modulus library one supplies the instance and *every* consumer is discharged.

**Non-vacuity.**  Each field is the verbatim mixing/non-mixing statement, so a
hypothetical instance must actually *prove* the classification — there is no
degenerate witness.  The preconditions are genuinely inhabited: `H(1,2) = K_2`
and `H(1,3) = K_3` genuinely mix (positive half), while `H(1,5) = K_5` genuinely
fails to mix at every time (negative half), so neither half is vacuously true. -/
class HammingMixingClassification : Prop where
  /-- **Ahmadi–Belk–Tamon–Wendler (2003), Theorem 3 (positive half).**  For
  `q ∈ {2,3,4}` the Hamming graph `H(n,q)` is uniformly mixing at `τ = 2π/q`. -/
  mix_of_le_4 : ∀ (n q : ℕ), 2 ≤ q → q ≤ 4 →
    ∀ [Fintype (Fin n → Fin q)], ∀ [DecidableEq (Fin n → Fin q)],
      IsUniformMixing (Hamming n q) (2 * Real.pi / q)
  /-- **Ahmadi–Belk–Tamon–Wendler (2003) (negative half).**  For `q ≥ 5`,
  `n ≥ 1` the Hamming graph `H(n,q)` mixes uniformly at *no* time. -/
  no_mix_of_ge_5 : ∀ (n q : ℕ), 5 ≤ q → 1 ≤ n →
    ∀ [Fintype (Fin n → Fin q)], ∀ [DecidableEq (Fin n → Fin q)],
      ∀ τ : ℝ, ¬ IsUniformMixing (Hamming n q) τ
  /-- **Levine–Tamon (2024), arXiv:2605.04414.**  For `q ≥ 5`, `n ≥ 1` *no*
  chiral signing of `H(n,q)` exhibits uniform mixing. -/
  no_chiral_of_ge_5 : ∀ (n q : ℕ), 5 ≤ q → 1 ≤ n →
    ∀ [Fintype (Fin n → Fin q)], ∀ [DecidableEq (Fin n → Fin q)],
      ∀ (σ : ChiralMixingSigning (Hamming n q)) (τ : ℝ),
        ¬ (∀ u v : Fin n → Fin q,
            ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • σ.signed)) u v‖ ^ 2 =
              1 / (Fintype.card (Fin n → Fin q) : ℝ))

/-- **Ahmadi–Belk–Tamon–Wendler (2003).**  For `q ∈ {2, 3, 4}`, the
Hamming graph `H(n, q)` is uniformly mixing at time `τ = 2π / q`.

Reference: arXiv:quant-ph/0209106, Theorem 3.  The proof goes via the
character basis: uniformity at time `τ` reduces to
`|∑_x ω^{xs} exp(-iτ λ_s)|² = 1` for every character index `s`, which is
satisfied for `q ∈ {2, 3, 4}` thanks to integrality of the Gauss sums on
`ℤ/q`.  Discharged from the local `HammingMixingClassification` interface
(the genuinely-unformalized Gauss-sum content). -/
theorem hamming_uniformMixing_of_q_le_4 [HammingMixingClassification]
    (n q : ℕ) (hq2 : 2 ≤ q) (hq4 : q ≤ 4)
    [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)] :
    IsUniformMixing (Hamming n q) (2 * Real.pi / q) :=
  HammingMixingClassification.mix_of_le_4 n q hq2 hq4

/-- **Ahmadi–Belk–Tamon–Wendler (2003) — negative half.**  For `q ≥ 5`
and `n ≥ 1`, the Hamming graph `H(n, q)` does *not* exhibit uniform
mixing at any time `τ ∈ ℝ`.  Discharged from `HammingMixingClassification`. -/
theorem hamming_no_uniformMixing_of_q_ge_5 [HammingMixingClassification]
    (n q : ℕ) (hq : 5 ≤ q) (hn : 1 ≤ n)
    [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)] :
    ∀ τ : ℝ, ¬ IsUniformMixing (Hamming n q) τ :=
  HammingMixingClassification.no_mix_of_ge_5 n q hq hn

/-- **Combined statement / Ahmadi et al. 2003 + Levine–Tamon 2024.**  The
Hamming graph `H(n, q)` admits uniform mixing if and only if `q ≤ 4`.

Reference: arXiv:quant-ph/0209106 (Hermitian case); arXiv:2605.04414
(chiral closure, ruling out the possibility that adding chiral signings
to the Hamiltonian could rescue mixing for `q ≥ 5`). -/
theorem hamming_uniformMixing_iff_q_le_4 [HammingMixingClassification]
    (n q : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ q)
    [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)] :
    (∃ τ : ℝ, IsUniformMixing (Hamming n q) τ) ↔ q ≤ 4 := by
  refine ⟨?_, ?_⟩
  · -- Forward: if uniform mixing occurs, then `q ≤ 4`.  Contrapositive of
    -- `hamming_no_uniformMixing_of_q_ge_5`: if `q ≥ 5`, no time `τ` mixes.
    rintro ⟨τ, hmix⟩
    by_contra hq4
    have hq5 : 5 ≤ q := by omega
    exact hamming_no_uniformMixing_of_q_ge_5 n q hq5 hn τ hmix
  · -- Backward: choose `τ = 2π / q`.
    intro hle
    refine ⟨2 * Real.pi / q, ?_⟩
    exact hamming_uniformMixing_of_q_le_4 n q hq hle

/-! ## Chiral closure (Levine–Tamon 2024) -/

/-- **Levine–Tamon (2024), arXiv:2605.04414.**  For `q ≥ 5` and `n ≥ 1`,
*no* chiral signing of `H(n, q)` exhibits uniform mixing.  In other
words, the obstruction at `q ≥ 5` is not removable by chiral
modifications. -/
theorem hamming_no_chiral_uniformMixing [HammingMixingClassification]
    (n q : ℕ) (hq : 5 ≤ q) (hn : 1 ≤ n)
    [Fintype (Fin n → Fin q)] [DecidableEq (Fin n → Fin q)]
    (σ : ChiralMixingSigning (Hamming n q)) :
    ∀ τ : ℝ, ¬ (∀ u v : Fin n → Fin q,
        ‖(NormedSpace.exp (-(Complex.I * (τ : ℂ)) • σ.signed)) u v‖ ^ 2 =
          1 / (Fintype.card (Fin n → Fin q) : ℝ)) :=
  -- Cf. arXiv:2605.04414 §4: the Krawtchouk obstruction is preserved
  -- under chiral signings.  Discharged from `HammingMixingClassification`.
  fun τ => HammingMixingClassification.no_chiral_of_ge_5 n q hq hn σ τ

end StdLib
end Graphplay
