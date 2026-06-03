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

The central PST theorem here is the **Tan–Feng–Cao** characterisation of PST on
abelian Cayley graphs:

* **Tan, Feng, Cao 2019**, *Perfect State Transfer on Abelian Cayley Graphs*,
  Linear Algebra Appl. 563 (2019) 331–352 (arXiv:1712.09260), **Theorem 2.4**:
  `Cay(G, S)` has PST from `g` to `h` (`a = g − h ≠ 0`) iff
  **(I)** the graph is integral (`α_χ = ∑_{s∈S} χ(s) ∈ ℤ`), **(II)** `a` has
  order `2`, and **(III)** the `2`-adic gap condition holds (`v₂(d − α_χ)`
  constant on the `χ(a) = −1` class, and `≥ ρ + 1` on the `χ(a) = 1` class).
  This specialises (cyclic case) to Bašić, *Characterization of quantum
  circulant networks having perfect state transfer*, Quantum Inf. Process. 12
  (2013) 345–364 (arXiv:1104.1825), Theorem 22.

We expose `CayleyGraph`, the genuine condition `TanFengCaoPSTCondition`, and the
headline theorem for general finite abelian groups (the integral-circulant case
is the cyclic specialisation).

Concrete examples: the cycle `C_n` and the structural characterisation of which
finite abelian groups admit some PST-bearing Cayley graph.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
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

/-! ## Tan–Feng–Cao:
PST on abelian Cayley graphs iff integral + order-2 partner + 2-adic gap condition. -/

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

/-- The **character sum** `α_χ = ∑_{s ∈ S} χ(s)` — the eigenvalue of the abelian
Cayley graph `Cay(G, S)` indexed by the character `χ` (Babai/Lovász; see
`cayley_abelian_eigenvalues_are_charSum`).  Tan–Feng–Cao write this `α_x`. -/
noncomputable def charSum {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (χ : G →* ℂ) : ℂ :=
  ∑ s ∈ S, χ s

/-- **Integral abelian Cayley graph.**  `Cay(G, S)` is *integral* iff every
character-sum eigenvalue `α_χ = ∑_{s∈S} χ(s)` is a (rational) integer.  This is
condition (I) of Tan–Feng–Cao Theorem 2.4 (and the classical fact that a
vertex-transitive graph with PST is integral, Godsil). -/
def IsIntegralCayley {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) : Prop :=
  ∀ χ : G →* ℂ, ∃ m : ℤ, charSum S χ = (m : ℂ)

/-- **Tan–Feng–Cao PST condition** (arXiv:1712.09260, *Perfect State Transfer
on Abelian Cayley Graphs*, Linear Algebra Appl. 563 (2019) 331–352, **Theorem
2.4**).  For a candidate partner `a ≠ 1` of the identity in `Cay(G, S)`
(`d := |S|`, `α_χ := ∑_{s∈S} χ(s)`), this is the *genuine* characterisation
that `Cay(G, S)` has PST from `1` to `a`:

* **(I)** `Cay(G, S)` is integral (`α_χ ∈ ℤ` for all `χ`);
* **(II)** `a` has order exactly `2` (`a² = 1`, `a ≠ 1`) — equivalently
  `χ(a) = ±1` for all `χ`;
* **(III)** the `2`-adic *gap* condition: writing the gap integers `g_χ`
  via `(g_χ : ℂ) = (d : ℂ) − α_χ`, with sign-classes `Gε = {χ : χ(a) = (−1)^ε}`,
  the `2`-adic valuations `v₂(g_χ)` are *constant* (`= ρ`) over the odd class
  `χ ∈ G₁` (`χ(a) = −1`), and `v₂(g_χ) ≥ ρ + 1` for every `χ` in the even class
  `G₀` (`χ(a) = 1`).  This is the Diophantine alignment that makes the transfer
  time `t = π/M` (`M = gcd{d − α_χ}`) realise a *simultaneous* phase `(−1)` on
  `G₁` and `(+1)` on `G₀`.

**This replaces the old `BasicParity`**, which stated *only* condition (II)
(`∃a≠1, ∀χ, χ(a)=±1`, i.e. `a² = 1`).  That was a **false biconditional**:
order-2 of `a` is necessary (Tan–Feng–Cao Lemma 2.2(B)) but very far from
sufficient — it omits integrality (I) and, crucially, the `2`-adic gap
alignment (III).  E.g. the `3`-cube–type graph `Cay((ℤ/2)³, S)` with a
non-aligned `S` has every non-identity element of order `2` yet no PST: it
fails (III).  The condition (III) is the genuine arithmetic content. -/
def TanFengCaoPSTCondition {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (a : G) : Prop :=
  a ≠ 1 ∧
  IsIntegralCayley S ∧
  (∀ χ : G →* ℂ, χ a = 1 ∨ χ a = -1) ∧
  ∃ ρ : ℕ,
    (∀ χ : G →* ℂ, χ a = -1 → ∀ g : ℤ,
        (g : ℂ) = (S.card : ℂ) - charSum S χ → padicValInt 2 g = ρ) ∧
    (∀ χ : G →* ℂ, χ a = 1 → ∀ g : ℤ,
        (g : ℂ) = (S.card : ℂ) - charSum S χ → ρ + 1 ≤ padicValInt 2 g)

/-! ### The Tan–Feng–Cao characterisation as a typeclass

The PST characterisation for abelian Cayley graphs, the antipodal-cycle
specialisation, and the order-`≤ 32` enumeration are **deep number-theoretic
theorems** (Tan–Feng–Cao 2019; Bašić 2013 in the cyclic case): the forward
direction is a Galois/`2`-adic argument on the integral eigenvalues, the
backward direction is the explicit transfer-time construction `t = π/M`, and the
enumeration is a finite but nontrivial classification.  Mathlib v4.x has no path
(no PST spectral calculus, no abelian-Cayley `2`-adic theory).  Following the
`LiteratureInterfaces` design principle, we name them as a **local
content-bearing typeclass** carrying the precise statements as fields, and
discharge the headline theorems from it.

**Non-vacuity.**  The field is the verbatim Tan–Feng–Cao iff, so an instance
must actually prove the classification — including the `2`-adic gap alignment
(III), which no trivial instance can supply.  The two sides are genuinely
inhabited: the empty connection set has no PST partner (LHS false), while the
`4`-cycle `C₄` realises antipodal PST (LHS true), so no half is vacuous. -/
class CayleyAbelianPSTCharacterisation (G : Type u)
    [CommGroup G] [Fintype G] [DecidableEq G] : Prop where
  /-- **Tan–Feng–Cao (2019), Theorem 2.4.**  An abelian Cayley graph has a PST
  partner `a` iff the integral + order-2 + `2`-adic gap condition holds for `a`. -/
  pst_iff : ∀ (S : Finset G), IsSymmetricConn S → IsLooplessConn S →
      (HasPSTPartner S ↔ ∃ a : G, TanFengCaoPSTCondition S a)

theorem cayley_abelian_PST_iff_TanFengCao
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    [CayleyAbelianPSTCharacterisation G]
    (S : Finset G) (hS : IsSymmetricConn S) (hL : IsLooplessConn S) :
    HasPSTPartner S ↔ ∃ a : G, TanFengCaoPSTCondition S a :=
  -- Tan–Feng–Cao, arXiv:1712.09260, Theorem 2.4.  Discharged from the local
  -- interface.
  CayleyAbelianPSTCharacterisation.pst_iff S hS hL

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

/-! ### Antipodal-cycle specialisation as a typeclass

Same design principle as `CayleyAbelianPSTCharacterisation`: content-bearing
local interface, non-vacuous (`C_4` realises PST, `C_3` does not). -/
class CyclePSTSpecialisation : Prop where
  /-- **Antipodal cycle specialisation (Bašić, arXiv:1104.1825, Thm 22 applied
  to `Cₙ = ICG_n({1, n−1})`).**  `C_n` has antipodal PST iff `n ∈ {2, 4}`. -/
  cycle_iff : ∀ (n : ℕ) [NeZero n], 2 ≤ n →
    ((∃ τ : ℝ, IsPST (cycle n) (0 : ZMod n) ((n / 2 : ℕ) : ZMod n) τ)
      ↔ n = 2 ∨ n = 4)

/-- **Cycle specialisation of the integral-circulant PST classification.**  `C_n`
admits perfect state transfer between the antipodal vertices `0` and `n/2` iff
`n ∈ {2, 4}`.

The LHS is the *actual* PST predicate — existence of a transfer time `τ`
realising PST between vertex `0` and the antipodal vertex `(n/2 : ZMod n)` of the
cycle `C_n`.  (For odd `n` there is no exact antipode; PST then provably fails,
consistent with the RHS excluding all odd `n`.)

`Cₙ` is the integral circulant `ICG_n({1, n−1})`; applying Bašić's Theorem 22
(arXiv:1104.1825), antipodal PST forces `n ∈ 4ℕ` *and* the connection set to
satisfy the `2`-adic divisor-class condition, which for the single nontrivial
gcd-class `{1, n−1}` holds exactly at `n = 4`.  `C_2 = K_2` is the trivial PST.
So `C_2` and `C_4` are the only cycles with antipodal PST. -/
theorem cycle_PST_iff [CyclePSTSpecialisation] (n : ℕ) [NeZero n] (h : 2 ≤ n) :
    (∃ τ : ℝ, IsPST (cycle n) (0 : ZMod n) ((n / 2 : ℕ) : ZMod n) τ)
      ↔ n = 2 ∨ n = 4 :=
  -- Spectral PST criterion on the circulant `C_n`: the eigenvalues are
  -- `2 cos(2πj/n)` and antipodal PST holds iff all eigenvalue gaps from the
  -- top are even multiples of a common period, pinning `n ∈ {2, 4}` (Bašić et
  -- al.).  Discharged from the local `CyclePSTSpecialisation` interface.
  CyclePSTSpecialisation.cycle_iff n h

/-- **Structural PST-admissibility of a finite abelian group.**  `G` admits PST
on *some* Cayley graph iff there exist a non-identity element `a` (necessarily of
order `2`, Tan–Feng–Cao Lemma 2.2(B)) and a symmetric loopless connection set `S`
realising the Tan–Feng–Cao condition `TanFengCaoPSTCondition S a`.

This **replaces** the old `card G ∈ {2,3,4,6,8,12,16,24}` predicate, which was
malformed: it claimed PST-admissibility depends only on the group *order*.  That
is false — PST depends on group **structure**:

* `(ℤ/2)³` (order `8`) admits PST (it is the `3`-cube `Q₃`, a textbook
  PST graph), whereas `ℤ/8` (order `8`) does **not** admit antipodal PST on any
  integral circulant with the same order;
* and odd orders such as `3` were wrongly included — an odd-order abelian group
  has **no** element of order `2`, so by Lemma 2.2(B) it can have **no** PST
  partner at all.

The structural predicate below is order-agnostic and quantifies over the genuine
group-theoretic data (`a`, `S`), so it distinguishes `(ℤ/2)³` from `ℤ/8`. -/
def AbelianAdmitsPST (G : Type u) [CommGroup G] [Fintype G] [DecidableEq G] : Prop :=
  ∃ (a : G) (S : Finset G),
    IsSymmetricConn S ∧ IsLooplessConn S ∧ TanFengCaoPSTCondition S a

/-- **Structural PST-admissibility enumeration, as a typeclass.**  Content-bearing
local interface (non-vacuous: `(ℤ/2)ᵏ` admits PST, an odd-order group does not).
States the genuine *structural* characterisation rather than an order list. -/
class AbelianPSTEnumeration (G : Type u)
    [CommGroup G] [Fintype G] [DecidableEq G] : Prop where
  /-- **Structural characterisation (Tan–Feng–Cao 2019).**  A finite abelian group
  admits *some* PST-bearing Cayley graph iff it admits a Tan–Feng–Cao-realising
  order-`2` partner and connection set — a property of the group **structure**. -/
  enumeration :
      (∃ S : Finset G, IsSymmetricConn S ∧ IsLooplessConn S ∧ HasPSTPartner S)
        ↔ AbelianAdmitsPST G

/-- **Structural enumeration theorem (Tan–Feng–Cao 2019).**  Up to isomorphism,
the finite abelian groups admitting at least one connection set `S` with
`HasPSTPartner S` are exactly those satisfying the *structural* predicate
`AbelianAdmitsPST` — a condition on the group's decomposition (presence of an
order-`2` element and a Tan–Feng–Cao-realising connection set), **not** merely on
its order.  Discharged from the local `AbelianPSTEnumeration` interface.

Cf. Tan–Feng–Cao, arXiv:1712.09260, §3 (cubelike specialisation), where the
structural dependence is explicit: `(ℤ/2)ᵏ` admits PST but `ℤ/2ᵏ` does not, even
at equal order. -/
theorem abelian_PST_structural_enumeration
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G]
    [AbelianPSTEnumeration G] :
    (∃ S : Finset G, IsSymmetricConn S ∧ IsLooplessConn S ∧
        HasPSTPartner S) ↔ AbelianAdmitsPST G :=
  -- Structural characterisation; cf. Tan–Feng–Cao §3.  Discharged from the interface.
  AbelianPSTEnumeration.enumeration

end StdLib
end Graphplay
