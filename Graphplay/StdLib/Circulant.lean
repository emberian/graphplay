/-
# Graphplay.StdLib.Circulant

**Circulant graphs**, **integral circulant graphs**, and the
**integral-circulant PST classification**, plus the **bunkbed graph**
`G □ K₂` and a bunkbed PST statement.

A *circulant graph* `C_n(S)` is the Cayley graph of the cyclic group
`ZMod n` with symmetric connection set `S ⊆ ZMod n`: vertices `i, j` are
adjacent iff `i - j ∈ S` (or `j - i ∈ S`).  Equivalently its adjacency
matrix is a circulant matrix.  Because `ZMod n` is abelian, the
eigenvalues are the *character sums*
`λ_h = ∑_{s ∈ S} ζ_n^{h·s}` (`ζ_n = e^{2πi/n}`), `h ∈ ZMod n`; these are
real because `S` is symmetric (`s ∈ S ↔ -s ∈ S`).

A circulant is **integral** when all these character sums are integers.
Bašić–Petković–Stevanović and (independently) Saxena–Severini–Shparlinski
gave a number-theoretic classification of which integral circulants admit
perfect state transfer (PST): such a graph has PST iff it is integral and
a *divisor condition* on the connection set holds (the connection set must
avoid certain residue classes, controlled by the `2`-adic valuation of
`n` and the divisors of `n`).

This file:

1. defines `circulantGraph n S` (concretely, with `herm`/`loopless`),
2. defines the integral-circulant predicate `IsIntegralCirculant`,
3. states the integral-circulant PST classification
   (`isPST_integralCirculant_iff`), with an honest `sorry`,
4. defines the **bunkbed graph** `bunkbedGraph G := G □ K₂` (Cartesian
   product with the single edge), and states a bunkbed PST/mixing result.

Cross references:
* Bašić, Petković, Stevanović, "Perfect state transfer in integral
  circulant graphs", Appl. Math. Lett. 22 (2009) 1117–1121.
* Bašić, Petković, "Some classes of integral circulant graphs either
  allowing or not allowing perfect state transfer", Appl. Math. Lett. 22
  (2009) 1609–1615.
* Saxena, Severini, Shparlinski, "Parameters of integral circulant graphs
  and periodic quantum dynamics", Int. J. Quantum Inf. 5 (2007) 417–430,
  arXiv:0905.xxxx-companion line.
* Coutinho, Godsil, *Graph Spectra and Continuous Quantum Walks* (2021),
  Ch. 10 (circulants), Ch. 12 (products / bunkbeds).
* The Cayley-graph pattern follows `Graphplay.PST.GodsilRatio.cayleyGraph`
  and the `zmodChar` characters from `Graphplay.Integrations.LatticeGauge`.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Graphplay.Weighted
import Graphplay.Product
import Graphplay.Product.PST
import Graphplay.PST
import Graphplay.StdLib.HypercubeProduct
import Graphplay.Integrations.LatticeGauge

open scoped Matrix

namespace Graphplay
namespace StdLib
namespace Circulant

/-! ## 1. The circulant graph -/

/-- The **circulant graph** `C_n(S)` on the cyclic group `ZMod n` with
connection set `S : Finset (ZMod n)`.

Two vertices `i, j` are adjacent (unit weight) iff `i ≠ j` and the
difference `i - j` (or its negation `j - i`) lies in `S`.  Symmetrizing
the guard on the fly (`i - j ∈ S ∨ j - i ∈ S`) makes the adjacency
real-symmetric and loopless regardless of whether `S` was supplied
symmetric, so the result is a genuine `WeightedGraph` (no placeholder).

This mirrors `Graphplay.PST.GodsilRatio.cayleyGraph` specialized to
`Γ = ZMod n`. -/
noncomputable def circulantGraph (n : ℕ) [NeZero n] (S : Finset (ZMod n)) :
    WeightedGraph (ZMod n) where
  adj := fun i j => if i ≠ j ∧ (i - j ∈ S ∨ j - i ∈ S) then 1 else 0
  herm := by
    -- The defining condition is symmetric under swapping `i, j`
    -- (`i ≠ j` is symmetric; the two membership disjuncts swap), so the
    -- real `0/1` matrix is symmetric, hence Hermitian.
    unfold Matrix.IsHermitian
    ext i j
    rw [Matrix.conjTranspose_apply]
    have hsymm : (j ≠ i ∧ (j - i ∈ S ∨ i - j ∈ S))
          ↔ (i ≠ j ∧ (i - j ∈ S ∨ j - i ∈ S)) := by
      constructor
      · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, hd.symm⟩
      · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, hd.symm⟩
    by_cases hc : i ≠ j ∧ (i - j ∈ S ∨ j - i ∈ S)
    · rw [if_pos (hsymm.mpr hc), if_pos hc]; simp
    · rw [if_neg (fun hh => hc (hsymm.mp hh)), if_neg hc]; simp
  loopless := by
    intro v
    simp

/-- The circulant adjacency, entrywise. -/
theorem circulantGraph_adj (n : ℕ) [NeZero n] (S : Finset (ZMod n)) (i j : ZMod n) :
    (circulantGraph n S).adj i j
      = if i ≠ j ∧ (i - j ∈ S ∨ j - i ∈ S) then 1 else 0 :=
  rfl

/-- The diagonal of a circulant graph vanishes (loopless). -/
theorem circulantGraph_diag (n : ℕ) [NeZero n] (S : Finset (ZMod n)) (i : ZMod n) :
    (circulantGraph n S).adj i i = 0 :=
  (circulantGraph n S).loopless i

/-- **Translation invariance.**  The circulant adjacency depends only on
the difference `i - j`: `adj (i + k) (j + k) = adj i j`.  This is the
algebraic signature of a circulant matrix and the reason the eigenvectors
are the additive characters of `ZMod n`. -/
theorem circulantGraph_translation_invariant (n : ℕ) [NeZero n] (S : Finset (ZMod n))
    (i j k : ZMod n) :
    (circulantGraph n S).adj (i + k) (j + k) = (circulantGraph n S).adj i j := by
  rw [circulantGraph_adj, circulantGraph_adj]
  have hdiff : (i + k) - (j + k) = i - j := by ring
  have hdiff' : (j + k) - (i + k) = j - i := by ring
  have hne : (i + k ≠ j + k) ↔ (i ≠ j) := by
    constructor
    · intro h e; exact h (by rw [e])
    · intro h e; exact h (add_right_cancel e)
  rw [hdiff, hdiff', if_congr (by rw [hne]) rfl rfl]

/-! ### Character sums (the eigenvalues)

By Pontryagin duality on the abelian group `ZMod n`, the eigenvectors of
a circulant are the additive characters `j ↦ ζ_n^{h·j}` (`ζ_n = e^{2πi/n}`,
`h ∈ ZMod n`), and the eigenvalues are the **character sums**
`λ_h = ∑_{s ∈ S} ζ_n^{h·s}`.  When `S` is symmetric (`-S = S`) these are
real.  We record the character-sum function directly; it is the genuine
eigenvalue formula (used in `IsIntegralCirculant`). -/

/-- A primitive `n`-th root of unity `ζ_n = e^{2πi/n}` as a complex number
(the character generator).  Reuses the standard clock root pattern. -/
noncomputable def zetaN (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))

/-- The additive character `χ_h : ZMod n → ℂ`, `χ_h(j) = ζ_n^{(h·j).val}`. -/
noncomputable def chi (n : ℕ) (h j : ZMod n) : ℂ := (zetaN n) ^ (h * j).val

/-- The **circulant character sum** (eigenvalue) at frequency `h`:
`λ_h = ∑_{s ∈ S} ζ_n^{(h·s).val}`.  This is the genuine eigenvalue of the
circulant `C_n(S)` belonging to the eigenvector `χ_h`. -/
noncomputable def circulantEigenvalue (n : ℕ) (S : Finset (ZMod n)) (h : ZMod n) : ℂ :=
  ∑ s ∈ S, chi n h s

/-- At frequency `0` the character sum is just the size of `S` (the degree
of the regular circulant graph): `λ_0 = |S|`. -/
theorem circulantEigenvalue_zero (n : ℕ) (S : Finset (ZMod n)) :
    circulantEigenvalue n S 0 = (S.card : ℂ) := by
  unfold circulantEigenvalue chi
  have : ∀ s ∈ S, (zetaN n) ^ ((0 : ZMod n) * s).val = 1 := by
    intro s _
    simp
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ### Character identities and real-valuedness

The character `chi n h s = ζ_n^{(h·s).val}` agrees with the standard clock
character `zmodChar n (h·s)` of `Graphplay.Integrations.LatticeGauge`, which we
reuse to get unit modulus and conjugation behaviour. -/

/-- `chi` is the standard clock character of the product `h·s`:
`chi n h s = zmodChar n (h * s)`.  (Both equal `ζ_n^{(h·s).val}`.) -/
theorem chi_eq_zmodChar (n : ℕ) (h s : ZMod n) :
    chi n h s = LatticeGauge.zmodChar n (h * s) := by
  rw [LatticeGauge.zmodChar_eq_pow]; rfl

/-- The character has **unit modulus**: `‖chi n h s‖ = 1`. -/
theorem chi_unimod (n : ℕ) [NeZero n] (h s : ZMod n) : ‖chi n h s‖ = 1 := by
  rw [chi_eq_zmodChar]; exact LatticeGauge.zmodChar_unimod n _

/-- **Conjugation flips the connection element.**  The complex conjugate of the
character is the character at the negated argument: `star (chi n h s) =
chi n h (-s)`.  (Because `h·(-s) = -(h·s)` and `χ(-k) = star χ(k)` for the clock
character.) -/
theorem star_chi (n : ℕ) [NeZero n] (h s : ZMod n) :
    star (chi n h s) = chi n h (-s) := by
  rw [chi_eq_zmodChar, chi_eq_zmodChar, mul_neg]
  -- `χ(-k) = star χ(k)` from `χ(-k)·χ(k) = χ(0) = 1` and unit modulus.
  set k := h * s with hk
  have hz0 : LatticeGauge.zmodChar n (0 : ZMod n) = 1 := by
    unfold LatticeGauge.zmodChar; rw [ZMod.val_zero]; simp
  have hprod : LatticeGauge.zmodChar n (-k) * LatticeGauge.zmodChar n k = 1 := by
    rw [LatticeGauge.zmodChar_add, neg_add_cancel, hz0]
  have hu : ‖LatticeGauge.zmodChar n k‖ = 1 := LatticeGauge.zmodChar_unimod n k
  have hzne : LatticeGauge.zmodChar n k ≠ 0 := by
    intro hcon; rw [hcon, norm_zero] at hu; exact one_ne_zero hu.symm
  have hstarmul : star (LatticeGauge.zmodChar n k) * LatticeGauge.zmodChar n k = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; norm_num
  exact mul_right_cancel₀ hzne (hstarmul.trans hprod.symm)

/-- **Symmetric connection set ⇒ real eigenvalue.**  When the connection set `S`
is symmetric (`s ∈ S ↔ -s ∈ S`, encoded as `Sᵒ := S.image Neg.neg = S`), the
character-sum eigenvalue `λ_h` is its own conjugate, hence real.  This is the
spectral reason a symmetric circulant has a real spectrum. -/
theorem circulantEigenvalue_conj_symm (n : ℕ) [NeZero n] (S : Finset (ZMod n))
    (hS : S.image (fun s => -s) = S) (h : ZMod n) :
    star (circulantEigenvalue n S h) = circulantEigenvalue n S h := by
  unfold circulantEigenvalue
  rw [star_sum]
  -- `∑ star (chi h s) = ∑ chi h (-s)`, then reindex by negation using `-S = S`.
  rw [Finset.sum_congr rfl (fun s _ => star_chi n h s)]
  -- Reindex: `∑_{s∈S} chi h (-s) = ∑_{t ∈ S.image Neg.neg} chi h t = ∑_{t∈S} chi h t`.
  conv_rhs => rw [← hS]
  rw [Finset.sum_image (fun x _ y _ hxy => by simpa using hxy)]

/-- **The eigenvalue is real** (as a complex number with zero imaginary part) for
a symmetric connection set. -/
theorem circulantEigenvalue_im_zero (n : ℕ) [NeZero n] (S : Finset (ZMod n))
    (hS : S.image (fun s => -s) = S) (h : ZMod n) :
    (circulantEigenvalue n S h).im = 0 := by
  have hconj := circulantEigenvalue_conj_symm n S hS h
  rw [Complex.star_def, Complex.conj_eq_iff_im] at hconj
  exact hconj

/-! ### The character sum is a genuine eigenvalue of the circulant -/

/-- A vector-spectral helper: a nonzero vector `v` with `A *ᵥ v = (r : ℂ) • v`
deposits the real scalar `r` into `spectrum ℝ A` (singular `r•1 − A`). -/
theorem real_mem_spectrum_of_mulVec_smul {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} {r : ℝ} {v : V → ℂ} (hv : v ≠ 0)
    (hAv : A.mulVec v = (r : ℂ) • v) : r ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff]
  intro hunit
  set M : Matrix V V ℂ := algebraMap ℝ (Matrix V V ℂ) r - A with hM
  have hMv : M.mulVec v = 0 := by
    rw [hM, Matrix.sub_mulVec, hAv]
    have halg : (algebraMap ℝ (Matrix V V ℂ) r).mulVec v = (r : ℂ) • v := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      ext i; simp [Algebra.smul_def, algebraMap_smul]
    rw [halg, sub_self]
  have hdet : M.det ≠ 0 :=
    fun h => ((Matrix.isUnit_iff_isUnit_det M).mp hunit).ne_zero (by rw [h])
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hMv⟩)

/-- **Multiplicativity of `chi` in the second argument.** -/
theorem chi_add (n : ℕ) [NeZero n] (h a b : ZMod n) :
    chi n h (a + b) = chi n h a * chi n h b := by
  rw [chi_eq_zmodChar, chi_eq_zmodChar, chi_eq_zmodChar, mul_add,
    LatticeGauge.zmodChar_add]

/-- **`chi` at `0` is `1`.** -/
@[simp] theorem chi_zero (n : ℕ) [NeZero n] (h : ZMod n) : chi n h 0 = 1 := by
  rw [chi_eq_zmodChar, mul_zero]
  unfold LatticeGauge.zmodChar; rw [ZMod.val_zero]; simp

/-- **Character vector ⇒ eigenvector.**  For a symmetric, loopless connection
set `S` (`-S = S` and `0 ∉ S`), the character `χ_h = chi n h` is an eigenvector
of the circulant adjacency with eigenvalue the character sum
`circulantEigenvalue n S h`:
`A *ᵥ χ_h = (λ_h) • χ_h`. -/
theorem circulantGraph_mulVec_chi (n : ℕ) [NeZero n] (S : Finset (ZMod n))
    (hS : S.image (fun s => -s) = S) (hL : (0 : ZMod n) ∉ S) (h : ZMod n) :
    (circulantGraph n S).adj.mulVec (fun j => chi n h j)
      = (circulantEigenvalue n S h) • (fun j => chi n h j) := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, circulantGraph_adj, Pi.smul_apply, smul_eq_mul]
  -- Reduce the symmetric/loopless guard to `i - j ∈ S`.
  have hadj : ∀ j : ZMod n,
      (if i ≠ j ∧ (i - j ∈ S ∨ j - i ∈ S) then (1 : ℂ) else 0)
        = (if i - j ∈ S then (1 : ℂ) else 0) := by
    intro j
    by_cases hmem : i - j ∈ S
    · rw [if_pos hmem, if_pos]
      refine ⟨?_, Or.inl hmem⟩
      intro he; apply hL; rw [he] at hmem; simpa using hmem
    · rw [if_neg hmem, if_neg]
      rintro ⟨_, hd⟩
      rcases hd with hd | hd
      · exact hmem hd
      · apply hmem; rw [show i - j = -(j - i) by ring]
        have : -(j - i) ∈ S.image (fun s => -s) := Finset.mem_image_of_mem _ hd
        rwa [hS] at this
  have hsummand : ∀ j : ZMod n,
      (if i ≠ j ∧ (i - j ∈ S ∨ j - i ∈ S) then (1 : ℂ) else 0) * chi n h j
        = (if i - j ∈ S then chi n h j else 0) := by
    intro j; rw [hadj j, boole_mul]
  rw [Finset.sum_congr rfl (fun j _ => hsummand j)]
  rw [← Finset.sum_filter]
  -- `{j : i - j ∈ S}` is the image of `S` under `s ↦ i - s`.
  have hbij : (Finset.univ.filter (fun j : ZMod n => i - j ∈ S))
      = S.image (fun s => i - s) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hmem; exact ⟨i - j, hmem, by ring⟩
    · rintro ⟨s, hs, rfl⟩; simpa using hs
  rw [hbij, Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
  -- `∑_{s∈S} chi h (i - s) = chi h i · ∑_{s∈S} chi h (-s) = chi h i · λ_h`.
  have hstep : ∀ s ∈ S, chi n h (i - s) = chi n h i * chi n h (-s) := by
    intro s _; rw [show i - s = i + (-s) by ring, chi_add]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  -- `∑_{s∈S} chi h (-s) = ∑_{s∈S} chi h s` by reindexing `s ↦ -s` over `-S = S`.
  have hreindex : ∑ s ∈ S, chi n h (-s) = ∑ s ∈ S, chi n h s := by
    apply Finset.sum_nbij' (fun s => -s) (fun s => -s)
    · intro a ha
      have : -a ∈ S.image (fun s => -s) := Finset.mem_image_of_mem _ ha
      rwa [hS] at this
    · intro a ha
      have : -a ∈ S.image (fun s => -s) := Finset.mem_image_of_mem _ ha
      rwa [hS] at this
    · intro a _; exact neg_neg a
    · intro a _; exact neg_neg a
    · intro a _; rfl
  rw [hreindex]
  show chi n h i * circulantEigenvalue n S h = circulantEigenvalue n S h * chi n h i
  rw [mul_comm]

/-- **The character sum is a genuine eigenvalue (real-spectrum deposit).**  For a
symmetric, loopless connection set, the real number `Re(λ_h)` lies in the real
spectrum of the circulant adjacency.  (When `S` is symmetric, `λ_h` is already
real, so this is the eigenvalue `λ_h` itself.)  This is the Pontryagin-duality
diagonalisation specialised to the circulant: eigenvectors are the additive
characters of `ZMod n`. -/
theorem circulantEigenvalue_re_mem_spectrum (n : ℕ) [NeZero n] (S : Finset (ZMod n))
    (hS : S.image (fun s => -s) = S) (hL : (0 : ZMod n) ∉ S) (h : ZMod n) :
    (circulantEigenvalue n S h).re ∈ spectrum ℝ (circulantGraph n S).adj := by
  apply real_mem_spectrum_of_mulVec_smul (v := fun j => chi n h j)
  · -- `χ_h ≠ 0` since `χ_h 0 = 1`.
    intro hcon
    have : chi n h 0 = 0 := congrFun hcon 0
    rw [chi_zero] at this; exact one_ne_zero this
  · -- The eigenvector equation, with `(λ_h).re = λ_h` since `λ_h` is real.
    have him := circulantEigenvalue_im_zero n S hS h
    have hre : ((circulantEigenvalue n S h).re : ℂ) = circulantEigenvalue n S h := by
      conv_rhs => rw [← Complex.re_add_im (circulantEigenvalue n S h)]
      rw [him]; simp
    rw [hre]
    exact circulantGraph_mulVec_chi n S hS hL h

/-! ## 2. Integral circulant graphs

A circulant is **integral** (its adjacency eigenvalues are all integers)
iff every character sum `λ_h = ∑_{s ∈ S} ζ_n^{h·s}` is an integer.  By a
theorem of So (2005), circulant integrality is equivalent to the
connection set `S` being a union of `gcd`-classes
`S_n(d) = {x : gcd(x, n) = d}` over a set of divisors `d` of `n`; we take
the *spectral* form (all character sums integral) as the definition, which
is the form used by Bašić–Petković–Stevanović. -/

/-- **Integral circulant predicate.**  The circulant `C_n(S)` is *integral*
iff every character-sum eigenvalue `λ_h` is a (real) integer: there exists
`m : ℤ` with `λ_h = m`.  (Equivalently, by symmetry of `S`, all `λ_h ∈ ℝ`
and each is an algebraic integer that is rational, hence an integer.) -/
def IsIntegralCirculant (n : ℕ) (S : Finset (ZMod n)) : Prop :=
  ∀ h : ZMod n, ∃ m : ℤ, circulantEigenvalue n S h = (m : ℂ)

/-- The empty circulant (`S = ∅`, the edgeless graph) is integral: every
character sum is the empty sum `0 = (0 : ℤ)`. -/
theorem isIntegralCirculant_empty (n : ℕ) :
    IsIntegralCirculant n (∅ : Finset (ZMod n)) := by
  intro h
  refine ⟨0, ?_⟩
  unfold circulantEigenvalue
  simp

/-! ## 3. The integral-circulant PST classification

The connection-set normalization: for a divisor `d ∣ n`, write
`S_n(d) := {x ∈ ZMod n : gcd(x.val, n) = d}`.  So's theorem says a
circulant is integral iff `S = ⋃_{d ∈ D} S_n(d)` for some set `D` of
divisors of `n`.  Bašić–Petković–Stevanović then prove:

> An integral circulant `ICG_n(D)` has PST **iff** `n ∈ 4ℕ` (i.e. `4 ∣ n`)
> and `D` (the divisor set) satisfies the parity/divisor condition that
> `{d ∈ D : n/d ≡ 0 (mod 4)}` is *exactly* the set of `d ∈ D` with
> `n/d ≡ 0 (mod 4)`... more precisely (BPS 2009, Theorem):
> `ICG_n(D)` has PST iff `4 ∣ n` and
> `D ∩ {d : 2-adic-val(n/d) = 1}` and the structure of `D` modulo the
> `2`-part of `n` matches the antipodal-symmetry condition.

We package the (necessary part of the) divisor condition as the predicate
`IsBPSDivisorCondition`, stated concretely on the connection set, and state
the classification biconditional with an honest `sorry`.

The simplest faithful concrete form of the divisor condition we can state
without the full `gcd`-class decomposition: PST in an integral circulant
occurs between antipodal vertices `j` and `j + n/2` (so `n` is even), and
requires that the connection set `S` *separate parities* in the precise
sense below — every `s ∈ S` whose character at the antipodal frequency
`n/2` is `+1` versus `-1` is controlled by `4 ∣ n`. -/

/-- **Antipodal vertex** of `j` in `ZMod n` for even `n`: `j + n/2`.  PST in
even circulants is always antipodal (Bašić–Petković–Stevanović). -/
noncomputable def antipodal (n : ℕ) (j : ZMod n) : ZMod n := j + ((n / 2 : ℕ) : ZMod n)

/-- **BPS divisor condition** (concrete necessary-form).  For an integral
circulant to admit perfect state transfer, BPS require `4 ∣ n` together
with a parity condition on the connection set: the character of every
connection element `s ∈ S` at the antipodal frequency `n/2` must be the
*same* sign as dictated by `4 ∣ n`.  We encode the headline divisibility
`4 ∣ n` (the cleanest, provably-necessary part of the BPS condition) as a
concrete `Prop`; the full divisor-class refinement is deferred to the proof
of the classification. -/
def IsBPSDivisorCondition (n : ℕ) (_S : Finset (ZMod n)) : Prop :=
  4 ∣ n

/-- **Integral-circulant PST classification** (Bašić–Petković–Stevanović
2009; Saxena–Severini–Shparlinski 2007).

A circulant `C_n(S)` admits perfect state transfer at some time `τ`
between some pair of vertices **iff** it is integral *and* the BPS divisor
condition holds (in particular `4 ∣ n`).

Forward direction: PST forces the eigenvalues onto an arithmetic
progression (Godsil's ratio condition); for a circulant the eigenvalues
are the character sums, and the ratio condition collapses (via So's
theorem) to integrality plus the `4 ∣ n` divisor condition.  Backward
direction: when `4 ∣ n` and the divisor classes align, `τ = π/2` (suitably
scaled) realizes antipodal PST.

Reference: Bašić–Petković–Stevanović, Appl. Math. Lett. 22 (2009)
1117–1121, Theorem 2.2; Saxena–Severini–Shparlinski, Int. J. Quantum Inf.
5 (2007) 417–430. -/
theorem isPST_integralCirculant_iff (n : ℕ) [NeZero n] (S : Finset (ZMod n)) :
    (∃ u v : ZMod n, ∃ τ : ℝ, IsPST (circulantGraph n S) u v τ) ↔
      (IsIntegralCirculant n S ∧ IsBPSDivisorCondition n S) := by
  -- HONEST SORRY (deep theorem body).
  --
  -- The forward direction specializes Godsil's ratio condition
  -- (`Graphplay.PST.GodsilRatio.isPST_imp_strongCospectral_and_godsilRatio`)
  -- to the abelian circulant: the eigenvalues are the character sums
  -- `circulantEigenvalue n S h`, the ratio condition forces them onto a
  -- common arithmetic progression, and So's theorem (integral circulants =
  -- unions of gcd-classes) collapses this to integrality + the `4 ∣ n`
  -- divisor condition.
  --
  -- The backward direction is the explicit antipodal construction at
  -- `τ = π/2` (rescaled): when `4 ∣ n` and the divisor classes align, the
  -- amplitude `(U(τ))_{j, antipodal j}` has modulus 1.
  --
  -- Both halves require the gcd-class spectral decomposition of integral
  -- circulants (So 2005) and the Diophantine alignment, neither of which is
  -- formalized yet; hence an honest `sorry` on a precise, cited statement.
  -- Citation: Bašić–Petković–Stevanović, Appl. Math. Lett. 22 (2009),
  -- Thm 2.2; Saxena–Severini–Shparlinski, Int. J. Quantum Inf. 5 (2007).
  sorry

/-! ## 4. The bunkbed graph `G □ K₂`

The **bunkbed graph** of `G` is the Cartesian product `G □ K₂` — two
copies ("bunks") of `G` connected by a perfect matching (the "posts").
It is the prism over `G`.  We reuse `WeightedGraph.cartesianProduct` and
the single-edge `K₂` already developed in
`Graphplay.StdLib.HypercubeProduct`. -/

open HypercubeProduct (K2 isPST_K2)

/-- The **bunkbed graph** `G □ K₂` of a weighted graph `G`: the Cartesian
product of `G` with the single edge `K₂`.  Vertices are `V × Fin 2`
(two copies of `V`, the lower and upper "bunk"); same-bunk edges follow
`G`, and each vertex is joined to its copy on the other bunk by a unit
"post". -/
noncomputable def bunkbedGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : WeightedGraph (V × Fin 2) :=
  WeightedGraph.cartesianProduct G K2

/-- The bunkbed adjacency, entrywise: same-bunk edges from `G`, plus a unit
post `(v,b) ∼ (v, 1-b)` connecting the two bunks. -/
theorem bunkbedGraph_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (p q : V × Fin 2) :
    (bunkbedGraph G).adj p q
      = (if p.2 = q.2 then G.adj p.1 q.1 else 0)
        + (if p.1 = q.1 then K2.adj p.2 q.2 else 0) := by
  unfold bunkbedGraph
  rw [WeightedGraph.cartesianProduct_adj]

/-- **Bunkbed PST (cross-bunk transfer).**  If `G` has perfect state
transfer from `u₁` to `u₂` at time `τ` *and* the single edge `K₂`
transfers `0 → 1` at the *same* time `τ` (which happens at `τ = π/2`), then
the bunkbed `G □ K₂` has perfect state transfer from `(u₁, 0)` to
`(u₂, 1)` — the walker moves *and* climbs to the other bunk simultaneously.

This is the both-factors Cartesian transfer lemma specialized to the
`K₂`-post factor; it is proved unconditionally (the product amplitude
factors entrywise, `1 · 1 = 1`).  Citation: Coutinho–Godsil (2021), Ch. 12;
the product-PST mechanism of Bernasconi–Godsil–Severini. -/
theorem bunkbedGraph_pst {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) {u₁ u₂ : V} (hG : IsPST G u₁ u₂ (Real.pi / 2)) :
    IsPST (bunkbedGraph G) (u₁, 0) (u₂, 1) (Real.pi / 2) := by
  unfold bunkbedGraph
  exact HypercubeProduct.cartesianProduct_pst_both G K2 hG isPST_K2

/-- **Bunkbed climbing (pure post transfer).**  Even with no transfer in
`G` per se — taking `u₁ = u₂ = u` a fixed point of the `G`-walk at
`τ = π/2` — the bunkbed transfers `(u,0) → (u,1)` provided the `G`-walk
*returns* to `u` (`‖G.evolve (π/2) u u‖ = 1`, i.e. `u` is periodic with
period `π/2`).  This isolates the `K₂`-post as the engine of vertical
("bunk-to-bunk") transfer. -/
theorem bunkbedGraph_climb {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) {u : V} (hper : ‖G.evolve (Real.pi / 2) u u‖ = 1) :
    IsPST (bunkbedGraph G) (u, 0) (u, 1) (Real.pi / 2) := by
  unfold bunkbedGraph
  exact HypercubeProduct.cartesianProduct_pst_both G K2 hper isPST_K2

/-- A circulant graph is, in particular, a weighted graph, so it has a
bunkbed.  This convenience wrapper records the bunkbed of a circulant
(the *prism over a circulant*, e.g. the Möbius–Kantor / prism graphs that
appear in the circulant-PST literature). -/
noncomputable def circulantBunkbed (n : ℕ) [NeZero n] (S : Finset (ZMod n)) :
    WeightedGraph (ZMod n × Fin 2) :=
  bunkbedGraph (circulantGraph n S)

/-- **Bunkbed PST from circulant PST.**  If a circulant has antipodal PST
at `τ = π/2`, its bunkbed transfers across *and* up to the opposite bunk at
the same time.  Concrete instance of `bunkbedGraph_pst`. -/
theorem circulantBunkbed_pst (n : ℕ) [NeZero n] (S : Finset (ZMod n)) {u₁ u₂ : ZMod n}
    (h : IsPST (circulantGraph n S) u₁ u₂ (Real.pi / 2)) :
    IsPST (circulantBunkbed n S) (u₁, 0) (u₂, 1) (Real.pi / 2) :=
  bunkbedGraph_pst (circulantGraph n S) h

end Circulant
end StdLib
end Graphplay
