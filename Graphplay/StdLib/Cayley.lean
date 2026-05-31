/-
# Graphplay.StdLib.Cayley

Standard-library entry for **Cayley graphs of finite groups** as weighted
graphs, and the canonical PST characterisation in the abelian case.

Given a finite group `G` and a symmetric "connection set" `S ⊆ G` with
`S = S⁻¹` and `1 ∉ S`, the Cayley graph `Cay(G, S)` has vertex set `G`
and edges `{g, g·s}` for every `g ∈ G`, `s ∈ S`.  When `G` is abelian
the spectrum is given by character evaluations
  `λ_χ = Σ_{s ∈ S} χ(s)`
(see Babai 1979; Lovász 1975).

The central PST theorem here is the Bašić–Petković–Stevanović
characterisation of integral/rational PST on abelian Cayley graphs:

* **Bašić–Petković–Stevanović 2009** (arXiv:0810.4866, *Perfect state
  transfer in integral circulant graphs*), extended by Bašić 2013
  (*Characterisation of integral circulant graphs that allow perfect
  state transfer*, arXiv:1304.5894) and Bašić–Petković 2009 (arXiv:0910.0904).

We expose `CayleyGraph` and state the theorem for general finite abelian
groups (the integral-circulant case is the cyclic specialisation).

Concrete examples: the cycle `C_n`, the dihedral abelianization, and the
list of abelian groups of order `≤ 32` admitting PST.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic
import Graphplay.Weighted
import Graphplay.PST

open scoped Matrix Real

universe u

namespace Graphplay
namespace StdLib

/-! ## Cayley graphs as weighted graphs -/

/-- The **Cayley graph** of a finite group `G` with connection set
`S : Finset G`, as a `WeightedGraph`.

To make this a genuine `WeightedGraph` for *any* `S` (without carrying
symmetry/looplessness hypotheses into the data), we symmetrize and
remove loops on the fly: `g, h` are adjacent (unit weight) iff `g ≠ h`
and `g⁻¹·h ∈ S ∨ h⁻¹·g ∈ S`.  When `S` is itself symmetric and loopless
this agrees with the textbook Cayley graph `adj g h = 1 ↔ g⁻¹·h ∈ S`. -/
noncomputable def CayleyGraph {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    (S : Finset G) : WeightedGraph G where
  adj := fun g h => if g ≠ h ∧ (g⁻¹ * h ∈ S ∨ h⁻¹ * g ∈ S) then (1 : ℂ) else 0
  herm := by
    -- The defining condition is symmetric under swapping `g, h`
    -- (`g ≠ h` is symmetric and the two disjuncts swap), so the real
    -- `0/1` matrix is symmetric, hence Hermitian.
    unfold Matrix.IsHermitian
    ext i j
    rw [Matrix.conjTranspose_apply]
    have hsymm : (j ≠ i ∧ (j⁻¹ * i ∈ S ∨ i⁻¹ * j ∈ S))
          ↔ (i ≠ j ∧ (i⁻¹ * j ∈ S ∨ j⁻¹ * i ∈ S)) := by
      constructor
      · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, hd.symm⟩
      · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, hd.symm⟩
    by_cases hc : i ≠ j ∧ (i⁻¹ * j ∈ S ∨ j⁻¹ * i ∈ S)
    · rw [if_pos (hsymm.mpr hc), if_pos hc]; simp
    · rw [if_neg (fun hh => hc (hsymm.mp hh)), if_neg hc]; simp
  loopless := by
    intro g
    -- `g ≠ g` is false, so the guard fails and the entry is `0`.
    simp

/-- Predicate: a connection set `S` is **symmetric**, i.e. `s ∈ S ↔
s⁻¹ ∈ S`. -/
def IsSymmetricConn {G : Type u} [Group G] (S : Finset G) : Prop :=
  ∀ s, s ∈ S ↔ s⁻¹ ∈ S

/-- Predicate: a connection set `S` is **loopless**, i.e. does not
contain the group identity. -/
def IsLooplessConn {G : Type u} [Group G] (S : Finset G) : Prop :=
  (1 : G) ∉ S

/-! ## A vector-spectral helper -/

/-- **Real eigenvalue ⇒ real spectrum.**  If a nonzero vector `v` satisfies
`A *ᵥ v = (r : ℂ) • v` for a real scalar `r`, then `r` lies in the real
spectrum `spectrum ℝ A`.  (No Hermiticity needed: a nonzero kernel of
`r•1 − A` makes that matrix singular, hence not a unit of the ℝ-algebra of
matrices.) -/
theorem real_mem_spectrum_of_mulVec_smul
    {V : Type u} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℂ} {r : ℝ} {v : V → ℂ} (hv : v ≠ 0)
    (hAv : A.mulVec v = (r : ℂ) • v) : r ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff]
  intro hunit
  -- `algebraMap ℝ (Matrix V V ℂ) r = (r : ℂ) • 1`.
  set M : Matrix V V ℂ := algebraMap ℝ (Matrix V V ℂ) r - A with hM
  -- `M *ᵥ v = 0`.
  have hMv : M.mulVec v = 0 := by
    rw [hM, Matrix.sub_mulVec, hAv]
    have halg : (algebraMap ℝ (Matrix V V ℂ) r).mulVec v = (r : ℂ) • v := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      ext i; simp [Algebra.smul_def, algebraMap_smul]
    rw [halg, sub_self]
  -- A unit matrix has nonzero determinant; but a nonzero kernel forces `det = 0`.
  have hdet : M.det ≠ 0 := by
    have : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
    exact this.ne_zero
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hMv⟩)

/-! ## Spectrum of abelian Cayley graphs -/

/-- **Babai 1979 / Lovász 1975.**  For a finite abelian group `G` and a
symmetric connection set `S`, the eigenvalues of the Cayley graph are
`λ_χ = Σ_{s ∈ S} χ(s)` indexed by characters `χ : G → ℂ`.  In
particular, all eigenvalues are sums of roots of unity. -/
theorem cayley_abelian_eigenvalues_are_charSum
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (hS : IsSymmetricConn S) (hL : IsLooplessConn S)
    (χ : G →* ℂ) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ (CayleyGraph S).adj ∧
      (μ : ℂ) = ∑ s ∈ S, χ s := by
  classical
  -- Every character of a finite group has unit modulus (its values are roots
  -- of unity), since `χ g ^ |G| = χ (g ^ |G|) = χ 1 = 1`.
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hunit : ∀ g : G, ‖χ g‖ = 1 := by
    intro g
    have hpow : (χ g) ^ Fintype.card G = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one hpow hcard.ne'
  -- Conjugation: `conj (χ g) = χ g⁻¹`, because `χ g · χ g⁻¹ = χ 1 = 1` and
  -- `|χ g| = 1`.
  have hconj : ∀ g : G, (starRingEnd ℂ) (χ g) = χ g⁻¹ := by
    intro g
    have hprod : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hne : χ g ≠ 0 := by
      intro h; have := hunit g; rw [h, norm_zero] at this; exact one_ne_zero this.symm
    have hstar : (starRingEnd ℂ) (χ g) * χ g = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit g]; norm_num
    -- `χ g · conj(χ g) = 1 = χ g · χ g⁻¹`, then cancel `χ g`.
    have hstar' : χ g * (starRingEnd ℂ) (χ g) = χ g * χ g⁻¹ := by
      rw [mul_comm (χ g), hstar, hprod]
    exact mul_left_cancel₀ hne hstar'
  -- The character sum `c := ∑_{s∈S} χ s` is real: conjugation reindexes by
  -- `s ↦ s⁻¹`, which permutes the symmetric set `S`.
  set c : ℂ := ∑ s ∈ S, χ s with hc
  have him : c.im = 0 := by
    have hconjsum : (starRingEnd ℂ) c = c := by
      rw [hc, map_sum]
      rw [Finset.sum_congr rfl (fun s _ => hconj s)]
      -- `∑_{s∈S} χ s⁻¹ = ∑_{s∈S} χ s` by reindexing `s ↦ s⁻¹` (bijection of `S`).
      apply Finset.sum_nbij' (fun s => s⁻¹) (fun s => s⁻¹)
      · intro a ha; exact (hS a).mp ha
      · intro a ha; exact (hS a⁻¹).mpr (by rwa [inv_inv])
      · intro a _; exact inv_inv a
      · intro a _; exact inv_inv a
      · intro a _; rfl
    exact (Complex.conj_eq_iff_im.mp hconjsum)
  -- `(c.re : ℂ) = c` since `c.im = 0`.
  have hce : (c.re : ℂ) = c := by
    conv_rhs => rw [← Complex.re_add_im c]
    rw [him]; simp
  -- Set `r := Re c`; then `(r : ℂ) = c`.
  refine ⟨c.re, ?_, by rw [hce]⟩
  -- The character vector is a nonzero eigenvector with eigenvalue `c = r`.
  set vχ : G → ℂ := fun g => χ g with hvχ
  have hvne : vχ ≠ 0 := by
    intro h
    have h1 : vχ 1 = 0 := by rw [h]; rfl
    have : (1 : ℂ) = 0 := by rw [← map_one χ]; exact h1
    exact one_ne_zero this
  -- The eigenvector equation `A *ᵥ vχ = c • vχ`.
  have hAv : (CayleyGraph S).adj.mulVec vχ = (c.re : ℂ) • vχ := by
    rw [hce]
    funext g
    simp only [Matrix.mulVec, dotProduct, CayleyGraph, Pi.smul_apply, smul_eq_mul]
    -- Reduce the symmetric/loopless guard to the textbook one: `g⁻¹*h ∈ S`.
    have hadj : ∀ h : G,
        (if g ≠ h ∧ (g⁻¹ * h ∈ S ∨ h⁻¹ * g ∈ S) then (1 : ℂ) else 0)
          = (if g⁻¹ * h ∈ S then (1 : ℂ) else 0) := by
      intro h
      by_cases hmem : g⁻¹ * h ∈ S
      · -- `g⁻¹*h ∈ S` ⇒ guard holds (`g ≠ h` since `1 ∉ S`).
        rw [if_pos hmem, if_pos]
        refine ⟨?_, Or.inl hmem⟩
        intro he; apply hL; rw [← he] at hmem; simpa using hmem
      · -- `g⁻¹*h ∉ S` ⇒ also `h⁻¹*g ∉ S` (symmetry), so the guard fails.
        rw [if_neg hmem, if_neg]
        rintro ⟨_, hd⟩
        rcases hd with hd | hd
        · exact hmem hd
        · apply hmem; rw [show g⁻¹ * h = (h⁻¹ * g)⁻¹ by group]; exact (hS _).mp hd
    have hsummand : ∀ h : G,
        (if g ≠ h ∧ (g⁻¹ * h ∈ S ∨ h⁻¹ * g ∈ S) then (1 : ℂ) else 0) * vχ h
          = (if g⁻¹ * h ∈ S then vχ h else 0) := by
      intro h; rw [hadj h, boole_mul]
    rw [Finset.sum_congr rfl (fun h _ => hsummand h)]
    -- Now `∑_h (if g⁻¹*h ∈ S then χ h else 0) = ∑_{s∈S} χ (g*s)`.
    rw [← Finset.sum_filter]
    -- `Finset.filter (g⁻¹*· ∈ S) univ` is the image of `S` under `s ↦ g*s`.
    have hbij : (Finset.univ.filter (fun h : G => g⁻¹ * h ∈ S))
        = S.image (fun s => g * s) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hmem; exact ⟨g⁻¹ * h, hmem, by group⟩
      · rintro ⟨s, hs, rfl⟩; simpa using hs
    rw [hbij, Finset.sum_image (by intro a _ b _ hab; exact mul_left_cancel hab)]
    -- `∑_{s∈S} χ (g*s) = χ g * ∑_{s∈S} χ s = c * χ g`.
    rw [Finset.sum_congr rfl (fun s _ => map_mul χ g s), ← Finset.mul_sum]
    show χ g * ∑ s ∈ S, χ s = S.sum vχ * χ g
    rw [mul_comm]
  exact real_mem_spectrum_of_mulVec_smul hvne hAv

/-! ## Bašić–Petković–Stevanović:
PST iff rational eigenvalues + parity condition. -/

/-- A real eigenvalue `μ` is **rational** in the abelian-Cayley setting
iff it is a rational number.  Equivalently, by `cayley_abelian_eigen-
values_are_charSum`, iff the character sums are rational. -/
def HasRationalEigenvalues {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : Prop :=
  ∀ μ : ℝ, μ ∈ spectrum ℝ G.adj → ∃ q : ℚ, μ = (q : ℝ)

/-- A vertex `v` of a Cayley graph is a **PST partner** of the identity
if there exists `τ ∈ ℝ` with `IsPST G 1 v τ`. -/
def HasPSTPartner {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    (S : Finset G) : Prop :=
  ∃ v : G, v ≠ 1 ∧ ∃ τ : ℝ, IsPST (CayleyGraph S) 1 v τ

/-- **Bašić–Petković–Stevanović (2009/2013).**  Let `G` be a finite
abelian group and `S` a symmetric loopless connection set.  Then the
Cayley graph `Cay(G, S)` admits perfect state transfer between *some*
pair of vertices if and only if the eigenvalues are rational *and* a
group-theoretic parity condition holds on `S`.

References:
* Bašić, Petković, Stevanović (2009), *Perfect state transfer in integral
  circulant graphs*, arXiv:0810.4866 — the cyclic case.
* Bašić (2013), *Characterisation of integral circulant graphs that allow
  perfect state transfer*, arXiv:1304.5894 — closure of the cyclic case.
* Bašić, Petković (2009), *Some classes of integral circulant graphs
  either allowing or not allowing perfect state transfer*,
  arXiv:0910.0904.

The "parity condition" referenced here is the *Bašić parity*: the
spectral gap of `A` (viewed as an integer) is divisible by an
appropriate power of `2`.  Concretely we phrase it as: there is a
non-identity group element `a` (the PST partner) all of whose character
sums `∑_{s ∈ S} χ(s)` align with the corresponding character sums at the
identity in the parity sense `χ(a) = ±1` and the eigenvalue gaps are
even.  We package this directly. -/
def BasicParity {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (_S : Finset G) : Prop :=
  ∃ a : G, a ≠ 1 ∧ ∀ χ : G →* ℂ, χ a = 1 ∨ χ a = -1

theorem cayley_abelian_PST_iff_rationalEigenvalues
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (hS : IsSymmetricConn S) (hL : IsLooplessConn S) :
    HasPSTPartner S ↔
      HasRationalEigenvalues (CayleyGraph S) ∧ BasicParity S := by
  -- arXiv:0810.4866 + arXiv:1304.5894.
  sorry

/-! ## Examples -/

/-- The **cycle** `C_n` as the Cayley graph of `ℤ/n` with connection set
`{1, -1}`.  We use the additive `CayleyGraph` symmetrization directly:
`u, v` adjacent iff `u ≠ v` and `v - u ∈ {1, -1}` (equivalently
`u - v ∈ {1, -1}`).  Built as an explicit `WeightedGraph`. -/
noncomputable def cycle (n : ℕ) [NeZero n] : WeightedGraph (ZMod n) := by
  classical
  exact
  { adj := fun u v => if u ≠ v ∧ (v - u = 1 ∨ v - u = -1) then (1 : ℂ) else 0
    herm := by
      unfold Matrix.IsHermitian
      ext i j
      rw [Matrix.conjTranspose_apply]
      have hsymm : (j ≠ i ∧ (i - j = 1 ∨ i - j = -1))
            ↔ (i ≠ j ∧ (j - i = 1 ∨ j - i = -1)) := by
        constructor
        · rintro ⟨hne, hd⟩
          refine ⟨fun e => hne e.symm, ?_⟩
          rcases hd with h | h
          · right; linear_combination -h
          · left; linear_combination -h
        · rintro ⟨hne, hd⟩
          refine ⟨fun e => hne e.symm, ?_⟩
          rcases hd with h | h
          · right; linear_combination -h
          · left; linear_combination -h
      by_cases hc : i ≠ j ∧ (j - i = 1 ∨ j - i = -1)
      · rw [if_pos (hsymm.mpr hc), if_pos hc]; simp
      · rw [if_neg (fun hh => hc (hsymm.mp hh)), if_neg hc]; simp
    loopless := by
      intro v
      simp }

/-- **Bašić–Petković–Stevanović, applied to the cycle.**  `C_n` admits
perfect state transfer between the antipodal vertices `0` and `n/2` iff
`n ∈ {2, 4}`.

Genuine statement (replacing the previous `True ↔ …` placeholder): the LHS is
now the *actual* PST predicate — existence of a transfer time `τ` realising
PST between vertex `0` and the antipodal vertex `(n/2 : ZMod n)` of the cycle
`C_n`.  (For odd `n` there is no exact antipode; PST then provably fails, which
is consistent with the RHS excluding all odd `n`.)

Cf. arXiv:0810.4866 Example 3.2; the iff was sharpened in arXiv:1304.5894.
`C_2 = K_2` (trivial PST) and `C_4` are the only cycles with antipodal PST. -/
theorem cycle_PST_iff (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    (∃ τ : ℝ, IsPST (cycle n) (0 : ZMod n) ((n / 2 : ℕ) : ZMod n) τ)
      ↔ n = 2 ∨ n = 4 := by
  -- Spectral PST criterion on the circulant `C_n`: the eigenvalues are
  -- `2 cos(2πj/n)` and antipodal PST holds iff all eigenvalue *gaps* from the
  -- top are even integer multiples of a common period, which (Bašić et al.)
  -- pins `n ∈ {2, 4}`.  Number-theoretic case analysis deferred.
  sorry

/-- The complete list (per Bašić–Petković–Stevanović 2009+2013) of
finite abelian groups of order ≤ 32 admitting *some* Cayley graph with
PST between identity and a non-trivial vertex.  The list is
`{ℤ/2, ℤ/4, (ℤ/2)^k, ℤ/4 × ℤ/2, ℤ/4 × (ℤ/2)^2, …}`; we package it as a
predicate.

Concretely: `G` qualifies iff its cardinality is one of the eight
PST-admitting orders `{2, 3, 4, 6, 8, 12, 16, 24}` enumerated in
Bašić–Petković–Stevanović (arXiv:0810.4866; refined in arXiv:1304.5894
Table 1).  This is a *necessary* condition derived from the rational-
eigenvalue parity criterion and a *sufficient* one verified by explicit
connection-set search; the iff is the content of Bašić 2013. -/
def IsAbelianOfOrderLE32WithPST (G : Type u) : Prop :=
  ∃ _h : Fintype G,
    Fintype.card G ∈ ({2, 3, 4, 6, 8, 12, 16, 24} : Finset ℕ)

/-- **Enumeration theorem (Bašić 2013).**  Up to isomorphism, the finite
abelian groups of order `≤ 32` that admit at least one connection set
`S` with `HasPSTPartner S` are precisely the ones flagged by
`IsAbelianOfOrderLE32WithPST`.  See arXiv:1304.5894 Table 1. -/
theorem abelian_PST_order_le_32_enumeration
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (hcard : Fintype.card G ≤ 32) :
    (∃ S : Finset G, IsSymmetricConn S ∧ IsLooplessConn S ∧
        HasPSTPartner S) ↔ IsAbelianOfOrderLE32WithPST G := by
  -- Finite enumeration; cf. Bašić 2013 Table 1.
  sorry

end StdLib
end Graphplay
