/-
# Graphplay.PST.Universal

**Universal state transfer, multiple state transfer, switching automorphisms,
and the K-fractional-revival subset framework.**

Ordinary perfect state transfer (PST, `Graphplay.PST.IsPST`) routes a single
excitation from one vertex `u` to *one* target `v` at *one* time `τ`.  This file
models three stronger / richer transfer phenomena studied in the literature:

1. **Universal state transfer** (Cameron–Fallat–Godsil–Holmes–et al.,
   arXiv:1701.04145): from a fixed vertex `u`, PST is achievable to *every*
   other vertex at *some* (vertex-dependent) time.  This is an extremely rigid
   condition; the classification theorem says a connected graph admitting
   universal state transfer is essentially trivial (a single edge `K₂`, or a
   tightly constrained product).

2. **Multiple state transfer** and **switching maps**
   (Kay, arXiv:1310.3885): a single time `τ` and an *automorphism-like*
   involution that simultaneously transfers several pairs.  At the transfer
   time the PST unitary carries each source state, up to a global phase, to its
   target state — the operator-level *switching map* (`T = E₊ − E₋`).  Its
   upgrade to a genuine 0/1 vertex-permutation automorphism (the *switching
   automorphism* proper) holds only under the integer/simple-spectrum
   hypotheses of Kay 1310.3885 — PST hosts need not be vertex-transitive — so
   this file proves the unconditional *operator-level* content and keeps the
   permutation upgrade as a (separately-hypothesised) structure, never as a
   theorem from bare PST.

3. **K-fractional revival** (Chan–Coutinho–Tamon–et al., arXiv:2004.01129):
   the generalization where the excitation, initially on a *subset* `K ⊆ V`,
   returns to (a unitary scrambling within) `K` at time `τ` — the off-`K`
   amplitudes vanish.  The governing object is the **`D_K` periodicity matrix**
   (the `K × K` block of the evolution) together with an eigenvalue **ratio
   condition** identical in spirit to Godsil's.

Concrete content (sorry-free `def`/`structure`):
* `IsUniversalStateTransfer G u`, `IsMultipleStateTransfer G pairs τ`;
* `SwitchingUnitary G u v τ` — the *operator-level* switching map PST genuinely
  supplies (a unitary carrying the `u`-state to a unit-phase multiple of the
  `v`-state), with `switchingUnitary_of_isPST` proving its existence
  axiom-clean and unconditionally;
* `SwitchingAutomorphism G u v` — the genuine vertex-permutation upgrade, kept
  as a *hypothesis-bearing structure* (it is **not** produced from bare PST: in
  the complex-Hermitian generality of `WeightedGraph` a PST host need not be
  vertex-transitive — see the caveat on the structure, and the canonical
  sibling treatment `Graphplay.PST.Periodicity.{SwitchingUnitary,
  switchingUnitary_of_isPST}`);
* `periodicityBlock G K τ` (the `D_K` block), `IsKFractionalRevival G K τ`,
  and `IsKRatioCondition G K` (the ratio condition).

The classification theorem `globallyUniversal_classification` is fully proven
here (real-symmetric scope, where it is true — see its docstring for the chiral
Hermitian counterexample forcing that scope).  The necessity of the spectral
ratio condition for K-fractional revival lives downstream in
`Graphplay.PST.UniversalRatio` (it needs the periodicity extraction of
`Graphplay.PST.Periodicity`, and its honest general form is a residue-class
statement).

References:
* A. Kay, *The perfect state transfer graph limbo*, arXiv:1310.3885.
* S. Cameron, S. Fallat, C. Godsil, S. Holmes, et al., *Universal state
  transfer on graphs*, Linear Algebra Appl. 455 (2014) 115–142
  (arXiv:1701.04145).
* W.-C. Cheung, C. Godsil, *Perfect state transfer in cubelike graphs*,
  Linear Algebra Appl. 435 (2011) 2468–2474.
* A. Chan, G. Coutinho, C. Tamon, L. Vinet, H. Zhan, *Fundamentals of
  fractional revival in graphs* and *Quantum fractional revival on graphs*,
  arXiv:2004.01129 / Discrete Math. (2020).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.PST.GodsilRatio

open scoped Matrix
open NormedSpace

universe u v

namespace Graphplay
namespace PST

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## §1 Universal state transfer (Cameron et al. 1701.04145) -/

/-- **Universal state transfer.**  The graph `G` admits *universal* state
transfer *from* `u` if for every other vertex `v` there is a time `τ_v` with
perfect state transfer `u → v`.  The single excitation initially at `u` can be
routed with certainty to *any* chosen target.

This is the per-source predicate of Cameron–Fallat–Godsil–Holmes et al.
(arXiv:1701.04145); their "universal state transfer" graph is one for which this
holds (and, by symmetry of strong cospectrality, the relation is global). -/
def IsUniversalStateTransfer (G : WeightedGraph V) (u : V) : Prop :=
  ∀ v : V, v ≠ u → ∃ τ : ℝ, IsPST G u v τ

/-- **Global universal state transfer**: every ordered pair of distinct vertices
admits PST at some time.  (The strongest, fully symmetric form.) -/
def IsGloballyUniversalStateTransfer (G : WeightedGraph V) : Prop :=
  ∀ u v : V, v ≠ u → ∃ τ : ℝ, IsPST G u v τ

/-- Global universal transfer specializes to per-source universal transfer at
every vertex. -/
theorem isUniversalStateTransfer_of_global (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G) (u : V) :
    IsUniversalStateTransfer G u :=
  fun v hv => h u v hv

/-- **Universal transfer forces pairwise strong cospectrality.**  If `G` admits
universal state transfer from `u`, then `u` is strongly cospectral with every
other vertex — an immediate consequence of `isPST_imp_isStronglyCospectral`
applied to each target.  This is the spectral spine of the classification.

Reference: Cameron et al. (arXiv:1701.04145), §3; Godsil 2012 (necessity of
strong cospectrality). -/
theorem isStronglyCospectral_of_universal (G : WeightedGraph V) {u : V}
    (h : IsUniversalStateTransfer G u) (v : V) (hv : v ≠ u) :
    IsStronglyCospectral G u v := by
  obtain ⟨τ, hτ⟩ := h v hv
  exact isPST_imp_isStronglyCospectral G τ u v hτ

/-- **Globally universal ⇒ pairwise strong cospectrality.**  Under global
universal state transfer, *every* ordered pair of distinct vertices is strongly
cospectral.  (Reachable consequence of `isPST_imp_isStronglyCospectral`.) -/
theorem isStronglyCospectral_of_globallyUniversal (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G) (u v : V) (hv : v ≠ u) :
    IsStronglyCospectral G u v :=
  isStronglyCospectral_of_universal G (isUniversalStateTransfer_of_global G h u) v hv

/-- **Universal PST equalizes eigenvector-entry moduli (simple-spectrum, CLOSED).**
For a graph with simple spectrum (`G.herm.eigenvalues` injective), global
universal state transfer forces, for *every* eigenindex `i` and *every* pair of
vertices `u, v`, the equality of eigenvector-entry moduli
`‖(eigU)_{u,i}‖ = ‖(eigU)_{v,i}‖`.

This is the genuine, axiom-clean spectral precursor of the Cameron et al.
classification (and of PST "monogamy"): under PST `u → v`, Godsil's
cross-entry relation `(E_λ)_{u,v} = γ e^{iτλ} (E_λ)_{u,u}`
(`isPST_imp_cross_eq_phase_diag`) collapses, on a simple spectrum, to
`(eigU)_{u,i} · conj (eigU)_{v,i} = γ e^{iτλ_i} ‖(eigU)_{u,i}‖²`; taking moduli
gives `‖(eigU)_{u,i}‖·‖(eigU)_{v,i}‖ = ‖(eigU)_{u,i}‖²`, and the same relation in
the reverse PST direction `v → u` yields the two-sided modulus equality.

Reference: Cameron, Fallat, Godsil, Holmes et al., LAA 455 (2014) 115–142;
Coutinho–Godsil (2021), Ch. 8 (strong cospectrality / monogamy of PST). -/
theorem eigU_norm_eq_of_globallyUniversal (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G)
    (hsimple : Function.Injective G.herm.eigenvalues)
    (u v : V) (i : V) :
    ‖eigU G u i‖ = ‖eigU G v i‖ := by
  -- One PST direction `a → b` gives `‖eigU a i‖ · ‖eigU b i‖ = ‖eigU a i‖²`.
  have hdir : ∀ a b : V, a ≠ b →
      ‖eigU G a i‖ * ‖eigU G b i‖ = ‖eigU G a i‖ ^ 2 := by
    intro a b hab
    obtain ⟨τ, hτ⟩ := h a b (by exact fun hba => hab hba.symm)
    -- Unfold `IsPST` to the modulus equation so `simp` can use it as a rewrite.
    have hτ' : ‖G.evolve τ a b‖ = 1 := hτ
    have hmem : (G.herm.eigenvalues i) ∈ Set.range G.herm.eigenvalues := ⟨i, rfl⟩
    -- Godsil cross-entry relation at the simple eigenvalue `λ_i`.
    have hcross := isPST_imp_cross_eq_phase_diag G τ a b hτ' (G.herm.eigenvalues i) hmem
    rw [eigenProjEntryLocal_of_injective G hsimple i,
        eigenProjDiagLocal_of_injective G hsimple i] at hcross
    -- `‖e^{iτλ_i}‖ = 1` (purely-imaginary exponent).
    have hexp : ‖Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    -- Take moduli of both sides; `‖γ‖ = 1` (PST), `‖e^{iτλ}‖ = 1`, `‖↑(‖a‖²)‖ = ‖a‖²`.
    have hnorm := congrArg (‖·‖) hcross
    simp only [norm_mul, norm_star, hexp, hτ', Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (‖eigU G a i‖))] at hnorm
    -- `hnorm : ‖a‖·‖b‖ = 1·1·‖a‖²`; finish.
    rw [hnorm]; ring
  -- Symmetrize: `‖a‖² = ‖a‖·‖b‖ = ‖b‖²` when `u ≠ v`; trivial when `u = v`.
  by_cases huv : u = v
  · rw [huv]
  · have h1 := hdir u v huv
    have h2 := hdir v u (fun h => huv h.symm)
    -- `‖u‖² = ‖u‖‖v‖` and `‖v‖² = ‖v‖‖u‖`, so `‖u‖² = ‖v‖²`, hence `‖u‖ = ‖v‖`.
    have hsq : ‖eigU G u i‖ ^ 2 = ‖eigU G v i‖ ^ 2 := by
      rw [← h1, ← h2]; ring
    nlinarith [norm_nonneg (eigU G u i), norm_nonneg (eigU G v i), hsq]

/-- Each eigenvector column of `eigU` is a unit vector:
`∑_u ‖(eigU)_{u,i}‖² = 1` (the `(i,i)` diagonal of `Uᴴ U = 1`). -/
theorem eigU_col_normSq (G : WeightedGraph V) (i : V) :
    ∑ u : V, ‖eigU G u i‖ ^ 2 = 1 := by
  have h := conjTranspose_mul_eigU G
  have hii := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hii
  have hcast : (∑ x : V, (eigU G)ᴴ i x * eigU G x i)
      = ((∑ x : V, ‖eigU G x i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hcast] at hii
  exact_mod_cast hii

/-- **Global universal transfer flattens the eigenvector matrix.**  Under global
universal state transfer with simple spectrum, every entry of `eigU` has squared
modulus exactly `1/|V|` — the eigenvectors are *flat*.  This is the CFGH
flatness necessary condition (Cameron–Fallat–Godsil–Holmes et al., LAA 455
(2014)): combine the uniform-modulus equality
`eigU_norm_eq_of_globallyUniversal` down each column with the column
normalization `eigU_col_normSq`. -/
theorem eigU_normSq_eq_of_globallyUniversal (G : WeightedGraph V)
    (h : IsGloballyUniversalStateTransfer G)
    (hsimple : Function.Injective G.herm.eigenvalues) (u i : V) :
    ‖eigU G u i‖ ^ 2 = ((Fintype.card V : ℝ))⁻¹ := by
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨u⟩
  have hcol := eigU_col_normSq G i
  have hconst : ∀ x ∈ Finset.univ, ‖eigU G x i‖ ^ 2 = ‖eigU G u i‖ ^ 2 := fun x _ => by
    rw [eigU_norm_eq_of_globallyUniversal G h hsimple x u i]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hcol
  field_simp
  linear_combination hcol

/-- **Classification of universal state transfer (real-symmetric scope;
RESTATED and CLOSED).**  On a *real-symmetric* graph (`Aᵀ = A`, the classical
Godsil setting) with simple spectrum, global universal state transfer on `≥ 3`
vertices is impossible.  This is PST *monogamy*: a vertex can perform PST with
at most one partner, so three vertices mutually transferring contradict each
other.

**Scope note (why `Aᵀ = A` is required, not cosmetic).**  In the complex
Hermitian generality of `WeightedGraph` the statement is *false*: the "clock"
Hamiltonian `H = F·diag(-1,0,1)·Fᴴ` (DFT eigenvectors `F` on `n = 3` vertices;
a traceless circulant, hence zero-diagonal Hermitian) satisfies
`U(2π/3) = cyclic shift`, giving perfect transfer between *every* ordered pair
at times `2πk/3` — global universal transfer with simple spectrum.  Universal
state transfer on Hermitian matrices genuinely exists (this is the content of
the CFGH paper, which *characterizes* it: simple spectrum plus flat
eigenvectors); only the time-symmetric `Aᵀ = A` case collapses to `K₂`.

**Proof (the previously-missing Diophantine core, now closed).**  Flatness
(`eigU_normSq_eq_of_globallyUniversal`) makes every eigenvector entry nonzero
of squared modulus `1/n`.  For a symmetric PST pair `(a, b)` at time `τ`, the
two directions of Godsil's cross relation multiply to
`e^{2iτλ_k} = (γ_{ab}γ_{ba})⁻¹` for every eigenindex `k`, so
`τ(λ_i − λ_j) ∈ πℤ`: each PST time quantizes all spectral gaps into integers
`m_i` (base `i₀`).  Row orthogonality of `eigU` then forces the *signed* sums
`∑_i (-1)^{m_i} = 0`.  For three vertices `u, v, w` this gives integer families
`m` (pair `u,v`), `p` (pair `u,w`) measuring the *same* real gaps in two
lattices — hence proportional, `m_i = a·s_i`, `p_i = b·s_i` with `gcd(a,b)=1` —
plus three sign-balance equations (`u⊥v`, `u⊥w`, and the cross balance `v⊥w`
giving `∑(-1)^{p_i−m_i} = 0`).  Parity kills every case: `a` even forces
`∑(-1)^{m_i} = n ≠ 0`; `b` even forces `∑(-1)^{p_i} = n`; `a, b` both odd force
`∑(-1)^{p_i−m_i} = n`.

Reference: Cameron, Fallat, Godsil, Holmes et al., *Universal state transfer on
graphs*, LAA 455 (2014) 115–142; Kay, arXiv:1310.3885 (monogamy of PST for
time-symmetric Hamiltonians); Coutinho–Godsil (2021), Ch. 8. -/
theorem globallyUniversal_classification (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm)
    (h : IsGloballyUniversalStateTransfer G)
    (hsimple : Function.Injective G.herm.eigenvalues)
    (hcard : 3 ≤ Fintype.card V) :
    False := by
  classical
  have hnpos : 0 < Fintype.card V := by omega
  have hcardR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hnpos
  have hcc : (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  -- Every PST amplitude is nonzero (it has modulus 1).
  have hPSTne : ∀ (a b : V) (τ : ℝ), IsPST G a b τ → G.evolve τ a b ≠ 0 := by
    intro a b τ hpst h0
    have h1 : ‖G.evolve τ a b‖ = 1 := hpst
    rw [h0, norm_zero] at h1
    norm_num at h1
  -- Godsil's cross relation in flat form: under PST `a → b` at `τ`,
  -- `(eigU)_{a,i} · conj (eigU)_{b,i} = γ · e^{iτλ_i} / n`.
  have hcross : ∀ (a b : V) (τ : ℝ), IsPST G a b τ → ∀ i : V,
      eigU G a i * star (eigU G b i)
        = G.evolve τ a b
            * Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))
            * (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) := by
    intro a b τ hpst i
    have h1 := isPST_imp_cross_eq_phase_diag G τ a b hpst (G.herm.eigenvalues i) ⟨i, rfl⟩
    rwa [eigenProjEntryLocal_of_injective G hsimple i,
      eigenProjDiagLocal_of_injective G hsimple i,
      eigU_normSq_eq_of_globallyUniversal G h hsimple a i] at h1
  -- Flatness, product form: `(eigU)_{x,i} · conj (eigU)_{x,i} = 1/n`.
  have hflat : ∀ x i : V,
      eigU G x i * star (eigU G x i) = (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) := by
    intro x i
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      eigU_normSq_eq_of_globallyUniversal G h hsimple x i]
  -- Symmetry gives the reverse PST at the same time.
  have hrevPST : ∀ (a b : V) (τ : ℝ), IsPST G a b τ → IsPST G b a τ := by
    intro a b τ hpst
    show ‖G.evolve τ b a‖ = 1
    rw [evolve_symm_of_adjSymm G hsymm τ a b]
    exact hpst
  -- Phase quantization: a symmetric PST pair at `τ` forces `τ(λ_i − λ_j) ∈ πℤ`.
  have hquant : ∀ (a b : V) (τ : ℝ), IsPST G a b τ → ∀ i j : V,
      ∃ m : ℤ, τ * (G.herm.eigenvalues i - G.herm.eigenvalues j)
        = Real.pi * (m : ℝ) := by
    intro a b τ hpst i j
    have hba := hrevPST a b τ hpst
    have hγ1 := hPSTne a b τ hpst
    have hγ2 := hPSTne b a τ hba
    -- The doubled phase is constant across the spectrum.
    have hconst : ∀ k : V,
        G.evolve τ a b * G.evolve τ b a
          * Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues k : ℝ) : ℂ)) ^ 2
        = 1 := by
      intro k
      have e1 := hcross a b τ hpst k
      have e2 := hcross b a τ hba k
      have hlhs : (eigU G a k * star (eigU G b k)) * (eigU G b k * star (eigU G a k))
          = (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) * (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) := by
        calc (eigU G a k * star (eigU G b k)) * (eigU G b k * star (eigU G a k))
            = (eigU G a k * star (eigU G a k)) * (eigU G b k * star (eigU G b k)) := by
              ring
          _ = _ := by rw [hflat a k, hflat b k]
      rw [e1, e2] at hlhs
      have hexpand : (G.evolve τ a b * G.evolve τ b a
            * Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues k : ℝ) : ℂ)) ^ 2
            - 1)
          * ((((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) * (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ)) = 0 := by
        linear_combination hlhs
      rcases mul_eq_zero.mp hexpand with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd h0 (mul_ne_zero hcc hcc)
    have hEij : Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ)) ^ 2
        = Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues j : ℝ) : ℂ)) ^ 2 :=
      mul_left_cancel₀ (mul_ne_zero hγ1 hγ2)
        (by linear_combination (hconst i) - (hconst j))
    have hexp2 : Complex.exp (2 * (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ)))
        = Complex.exp (2 * (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues j : ℝ) : ℂ))) := by
      rw [two_mul, two_mul, Complex.exp_add, Complex.exp_add, ← sq, ← sq]
      exact hEij
    rw [Complex.exp_eq_exp_iff_exists_int] at hexp2
    obtain ⟨nn, hnn⟩ := hexp2
    refine ⟨nn, ?_⟩
    have him := congrArg Complex.im hnn
    simp [Complex.mul_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re] at him
    nlinarith [him]
  -- Row orthogonality of `eigU` (distinct vertices).
  have horth : ∀ a b : V, a ≠ b → ∑ i : V, eigU G a i * star (eigU G b i) = 0 := by
    intro a b hab
    have h1 := congrFun (congrFun (eigU_mul_conjTranspose G) a) b
    rw [Matrix.mul_apply, Matrix.one_apply_ne hab] at h1
    simpa [Matrix.conjTranspose_apply] using h1
  -- For a PST pair, the eigenphases sum to zero.
  have hphasesum : ∀ (a b : V), a ≠ b → ∀ (τ : ℝ), IsPST G a b τ →
      ∑ i : V, Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))
        = 0 := by
    intro a b hab τ hpst
    have h0 := horth a b hab
    rw [Finset.sum_congr rfl (fun i _ => hcross a b τ hpst i)] at h0
    have hpull : ∑ i : V, G.evolve τ a b
          * Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))
          * (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ)
        = G.evolve τ a b * (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ)
          * ∑ i : V, Complex.exp (Complex.I * (τ : ℂ)
              * ((G.herm.eigenvalues i : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hpull] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (mul_ne_zero (hPSTne a b τ hpst) hcc)
    · exact h1
  -- Base index for the integer gap coordinates.
  obtain ⟨i₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hnpos
  -- A vanishing phase sum plus quantized gaps yields a balanced sign sum.
  have hbalance : ∀ (τ : ℝ) (m : V → ℤ),
      (∀ i : V, τ * (G.herm.eigenvalues i - G.herm.eigenvalues i₀)
        = Real.pi * (m i : ℝ)) →
      (∑ i : V, Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))
        = 0) →
      ∑ i : V, ((-1 : ℂ)) ^ (m i) = 0 := by
    intro τ m hm hsum
    have hsplit : ∀ i : V,
        Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))
          = Complex.exp (Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i₀ : ℝ) : ℂ))
            * ((-1 : ℂ)) ^ (m i) := by
      intro i
      have hC : (τ : ℂ) * (((G.herm.eigenvalues i : ℝ) : ℂ)
            - ((G.herm.eigenvalues i₀ : ℝ) : ℂ))
          = ((Real.pi : ℝ) : ℂ) * ((m i : ℤ) : ℂ) := by
        exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (hm i)
      have harg : Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ)
          = Complex.I * (τ : ℂ) * ((G.herm.eigenvalues i₀ : ℝ) : ℂ)
            + ((m i : ℤ) : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I) := by
        linear_combination Complex.I * hC
      rw [harg, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.mul_sum] at hsum
    rcases mul_eq_zero.mp hsum with h1 | h1
    · exact absurd h1 (Complex.exp_ne_zero _)
    · exact h1
  -- Three distinct vertices.
  have hnontriv : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ ({u, v} : Finset V) := by
    by_contra hno
    push_neg at hno
    have hsub : (Finset.univ : Finset V) ⊆ {u, v} := fun x _ => hno x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, Finset.card_pair huv] at hle
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨hwu, hwv⟩ := hw
  -- PST times for the two base pairs.
  obtain ⟨τ₁, hτ₁⟩ := h u v (Ne.symm huv)
  obtain ⟨τ₂, hτ₂⟩ := h u w hwu
  -- Integer gap coordinates in the two PST lattices.
  choose m hm using fun i => hquant u v τ₁ hτ₁ i i₀
  choose p hp using fun i => hquant u w τ₂ hτ₂ i i₀
  have B1 : ∑ i : V, ((-1 : ℂ)) ^ (m i) = 0 :=
    hbalance τ₁ m hm (hphasesum u v huv τ₁ hτ₁)
  have B2 : ∑ i : V, ((-1 : ℂ)) ^ (p i) = 0 :=
    hbalance τ₂ p hp (hphasesum u w (Ne.symm hwu) τ₂ hτ₂)
  -- Cross balance from `v ⊥ w` (no PST between `v` and `w` is needed: both rows
  -- are phase modulations of row `u`).
  have hcrossSum : ∑ i : V,
      Complex.exp (Complex.I * ((τ₂ - τ₁ : ℝ) : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))
        = 0 := by
    have h0 := horth v w (fun hvw => hwv hvw.symm)
    have hterm : ∀ i : V,
        (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) * (eigU G v i * star (eigU G w i))
          = star (G.evolve τ₁ u v) * G.evolve τ₂ u w
              * ((((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) * (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ))
            * Complex.exp (Complex.I * ((τ₂ - τ₁ : ℝ) : ℂ)
                * ((G.herm.eigenvalues i : ℝ) : ℂ)) := by
      intro i
      have e1 := hcross u v τ₁ hτ₁ i
      have e2 := hcross u w τ₂ hτ₂ i
      -- Conjugate the `(u,v)` relation.
      have e1s : star (eigU G u i) * eigU G v i
          = star (G.evolve τ₁ u v)
              * Complex.exp (-(Complex.I * (τ₁ : ℂ)) * ((G.herm.eigenvalues i : ℝ) : ℂ))
              * (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) := by
        have hstar := congrArg star e1
        simp only [star_mul', star_star] at hstar
        rw [show star (Complex.exp (Complex.I * (τ₁ : ℂ)
              * ((G.herm.eigenvalues i : ℝ) : ℂ)))
            = Complex.exp (-(Complex.I * (τ₁ : ℂ)) * ((G.herm.eigenvalues i : ℝ) : ℂ))
          from by
            rw [Complex.star_def, ← Complex.exp_conj]
            congr 1
            simp [Complex.conj_ofReal]] at hstar
        rw [show star ((((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ)) = (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ)
          from by rw [Complex.star_def, Complex.conj_ofReal]] at hstar
        exact hstar
      -- Combine with the `(u,w)` relation through the flat diagonal.
      calc (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ) * (eigU G v i * star (eigU G w i))
          = (star (eigU G u i) * eigU G v i) * (eigU G u i * star (eigU G w i)) := by
            rw [show (star (eigU G u i) * eigU G v i) * (eigU G u i * star (eigU G w i))
                = (eigU G u i * star (eigU G u i)) * (eigU G v i * star (eigU G w i))
              from by ring, hflat u i]
        _ = _ := by
            rw [e1s, e2]
            rw [show Complex.exp (Complex.I * ((τ₂ - τ₁ : ℝ) : ℂ)
                  * ((G.herm.eigenvalues i : ℝ) : ℂ))
              = Complex.exp (-(Complex.I * (τ₁ : ℂ))
                  * ((G.herm.eigenvalues i : ℝ) : ℂ))
                * Complex.exp (Complex.I * (τ₂ : ℂ) * ((G.herm.eigenvalues i : ℝ) : ℂ))
              from by
                rw [← Complex.exp_add]
                congr 1
                push_cast
                ring]
            ring
    have h1 : (∑ i : V, (((Fintype.card V : ℝ)⁻¹ : ℝ) : ℂ)
          * (eigU G v i * star (eigU G w i))) = 0 := by
      rw [← Finset.mul_sum, h0, mul_zero]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (mul_ne_zero
        (mul_ne_zero (star_ne_zero.mpr (hPSTne u v τ₁ hτ₁)) (hPSTne u w τ₂ hτ₂))
        (mul_ne_zero hcc hcc))
    · exact h2
  have hq : ∀ i : V, (τ₂ - τ₁) * (G.herm.eigenvalues i - G.herm.eigenvalues i₀)
      = Real.pi * ((p i - m i : ℤ) : ℝ) := by
    intro i
    have h1 := hm i
    have h2 := hp i
    push_cast
    linear_combination h2 - h1
  have B3 : ∑ i : V, ((-1 : ℂ)) ^ (p i - m i) = 0 :=
    hbalance (τ₂ - τ₁) (fun i => p i - m i) hq hcrossSum
  -- The PST time `τ₁` is nonzero, so some gap coordinate is nonzero.
  have hτ₁0 : τ₁ ≠ 0 := by
    intro h0
    rw [h0] at hτ₁
    have h1 : ‖G.evolve 0 u v‖ = 1 := hτ₁
    rw [G.evolve_zero, Matrix.one_apply_ne huv] at h1
    simp at h1
  obtain ⟨i₁, hi₁ne⟩ : ∃ i₁ : V, i₁ ≠ i₀ := exists_ne i₀
  have hlamne : G.herm.eigenvalues i₁ - G.herm.eigenvalues i₀ ≠ 0 :=
    sub_ne_zero.mpr (fun hh => hi₁ne (hsimple hh))
  have hm₁ : m i₁ ≠ 0 := by
    intro h0
    have h1 : τ₁ * (G.herm.eigenvalues i₁ - G.herm.eigenvalues i₀) = 0 := by
      rw [hm i₁, h0]; simp
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hτ₁0 h2
    · exact hlamne h2
  -- The two integer families are proportional: `m_i · p_{i₁} = p_i · m_{i₁}`.
  have hcrossInt : ∀ i : V, m i * p i₁ = p i * m i₁ := by
    intro i
    have h1 : (Real.pi * (m i : ℝ)) * (Real.pi * (p i₁ : ℝ))
        = (Real.pi * (p i : ℝ)) * (Real.pi * (m i₁ : ℝ)) := by
      rw [← hm i, ← hp i₁, ← hp i, ← hm i₁]
      ring
    have h2 : Real.pi ^ 2 * ((m i : ℝ) * (p i₁ : ℝ))
        = Real.pi ^ 2 * ((p i : ℝ) * (m i₁ : ℝ)) := by linear_combination h1
    have h3 := mul_left_cancel₀ (pow_ne_zero 2 Real.pi_ne_zero) h2
    exact_mod_cast h3
  -- Extract the coprime direction `(a, b)` of `(m_{i₁}, p_{i₁})`.
  have hgcdpos : 0 < Int.gcd (m i₁) (p i₁) :=
    Int.gcd_pos_iff.mpr (Or.inl hm₁)
  obtain ⟨a, b, hab, hg⟩ :
      ∃ a b : ℤ, Int.gcd a b = 1 ∧ ∃ g : ℤ, g ≠ 0 ∧ m i₁ = a * g ∧ p i₁ = b * g := by
    obtain ⟨a, b, hab, hma, hpb⟩ := Int.exists_gcd_one hgcdpos
    exact ⟨a, b, hab, (Int.gcd (m i₁) (p i₁) : ℤ),
      by exact_mod_cast hgcdpos.ne', hma, hpb⟩
  obtain ⟨g, hgne, hma, hpb⟩ := hg
  have hane : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hma
    exact hm₁ hma
  -- Per-index decomposition `m_i = a·s_i`, `p_i = b·s_i`.
  have hdecomp : ∀ i : V, ∃ s : ℤ, m i = a * s ∧ p i = b * s := by
    intro i
    have h1 := hcrossInt i
    rw [hma, hpb] at h1
    have h2 : m i * b = p i * a :=
      mul_right_cancel₀ hgne (by linear_combination h1)
    have h3 : a ∣ m i * b := ⟨p i, by linear_combination h2⟩
    have h4 : a ∣ m i := Int.dvd_of_dvd_mul_left_of_gcd_one h3 hab
    obtain ⟨s, hs⟩ := h4
    refine ⟨s, hs, ?_⟩
    have h5 : a * (s * b) = a * p i := by
      rw [show a * (s * b) = (a * s) * b from by ring, ← hs]
      linear_combination h2
    have h6 := mul_left_cancel₀ hane h5
    linear_combination -h6
  choose s hsm hsp using hdecomp
  -- An all-even sign family sums to `n ≠ 0`, contradicting balance.
  have hcardC : ((Fintype.card V : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  have hone : ∀ (k : V → ℤ), (∀ i, Even (k i)) →
      ∑ i : V, ((-1 : ℂ)) ^ (k i) = ((Fintype.card V : ℕ) : ℂ) := by
    intro k hk
    rw [Finset.sum_congr rfl (fun i _ => Even.neg_one_zpow (hk i)), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
  rcases Int.even_or_odd a with hA | hA
  · exact hcardC ((hone m (fun i => by rw [hsm i]; exact hA.mul_right _)).symm.trans B1)
  rcases Int.even_or_odd b with hB | hB
  · exact hcardC ((hone p (fun i => by rw [hsp i]; exact hB.mul_right _)).symm.trans B2)
  · have heven : ∀ i, Even (p i - m i) := fun i => by
      rw [hsp i, hsm i, show b * s i - a * s i = (b - a) * s i from by ring]
      exact (Odd.sub_odd hB hA).mul_right _
    exact hcardC ((hone (fun i => p i - m i) heven).symm.trans B3)

/-! ## §2 Multiple state transfer and switching automorphisms (Kay 1310.3885) -/

/-- **Multiple state transfer at a single time.**  Given a list of source/target
`pairs : List (V × V)`, `G` exhibits multiple state transfer at the common time
`τ` if PST holds *simultaneously* for every listed pair `(u, v)` at that one `τ`.
This is the "single clock" strengthening of PST studied by Kay (1310.3885):
several excitations are routed at once. -/
def IsMultipleStateTransfer (G : WeightedGraph V) (pairs : List (V × V))
    (τ : ℝ) : Prop :=
  ∀ p ∈ pairs, IsPST G p.1 p.2 τ

/-- Multiple state transfer over a single pair is ordinary PST. -/
theorem isMultipleStateTransfer_singleton (G : WeightedGraph V) (u v : V)
    (τ : ℝ) :
    IsMultipleStateTransfer G [(u, v)] τ ↔ IsPST G u v τ := by
  constructor
  · intro h; exact h (u, v) (List.mem_singleton.mpr rfl)
  · intro h p hp
    rw [List.mem_singleton] at hp
    rw [hp]; exact h

/-- The empty list trivially has multiple state transfer (no pairs to route). -/
theorem isMultipleStateTransfer_nil (G : WeightedGraph V) (τ : ℝ) :
    IsMultipleStateTransfer G [] τ := by
  intro p hp; exact absurd hp (List.not_mem_nil)

/-- Multiple state transfer over a concatenation holds iff it holds over each
sublist. -/
theorem isMultipleStateTransfer_append (G : WeightedGraph V)
    (l₁ l₂ : List (V × V)) (τ : ℝ) :
    IsMultipleStateTransfer G (l₁ ++ l₂) τ ↔
      IsMultipleStateTransfer G l₁ τ ∧ IsMultipleStateTransfer G l₂ τ := by
  unfold IsMultipleStateTransfer
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append_left _ hp),
           fun p hp => h p (List.mem_append_right _ hp)⟩
  · rintro ⟨h₁, h₂⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h₁ p hp
    · exact h₂ p hp

/-- Multiple state transfer over `p :: rest` is PST of the head together with
multiple state transfer of the tail. -/
theorem isMultipleStateTransfer_cons (G : WeightedGraph V) (p : V × V)
    (rest : List (V × V)) (τ : ℝ) :
    IsMultipleStateTransfer G (p :: rest) τ ↔
      IsPST G p.1 p.2 τ ∧ IsMultipleStateTransfer G rest τ := by
  unfold IsMultipleStateTransfer
  constructor
  · intro h
    exact ⟨h p (List.mem_cons_self), fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
  · rintro ⟨hhead, htail⟩ q hq
    rcases List.mem_cons.mp hq with hq | hq
    · rw [hq]; exact hhead
    · exact htail q hq

/-- A **switching automorphism** of `G` exchanging `u` and `v`: a vertex
permutation `σ` that (i) swaps `u ↔ v` and (ii) is a graph automorphism
(preserves the weighted adjacency).  This is the *combinatorial* upgrade of
Kay's switching map — a genuine `Equiv.Perm V` adjacency automorphism.

**Caveat — this is a hypothesis, not a consequence of PST.**  Kay's switching
map `T = E₊ − E₋` (spectral idempotents split by the parity of `e^{−iτ θ_r}`)
is an *orthogonal involution commuting with `A`* sending the `u`-state to the
`v`-state, but it is a genuine 0/1 *permutation* matrix only under the
integer/simple-spectrum hypotheses of Kay 1310.3885.  In the complex-Hermitian
generality of `WeightedGraph` a PST host need **not** be vertex-transitive, so
no `SwitchingAutomorphism` (genuine vertex permutation) need exist.  The
unconditional, axiom-clean content PST *does* supply is the *operator-level*
`SwitchingUnitary` below (`switchingUnitary_of_isPST`); there is deliberately no
theorem deriving a `SwitchingAutomorphism` from bare PST.

Defined self-containedly here (deliberately *not* importing the sibling
`Graphplay.PST.Periodicity`, which may be under concurrent edit) so this module
never couples to that file.  The sibling carries the identical honest treatment
(`Graphplay.PST.Periodicity.{SwitchingAutomorphism, SwitchingUnitary,
switchingUnitary_of_isPST}`).

Reference: Kay, arXiv:1310.3885; Godsil's automorphism characterization of
PST. -/
structure SwitchingAutomorphism (G : WeightedGraph V) (u v : V) where
  /-- The underlying vertex permutation. -/
  perm : Equiv.Perm V
  /-- It swaps the two transfer endpoints. -/
  swaps_uv : perm u = v
  /-- And back. -/
  swaps_vu : perm v = u
  /-- It preserves the (Hermitian) adjacency matrix entrywise. -/
  preserves_adj : ∀ x y, G.adj (perm x) (perm y) = G.adj x y

namespace SwitchingAutomorphism

variable {G : WeightedGraph V} {u v : V}

/-- A switching automorphism is an involution on the endpoints: applying `perm`
twice to `u` returns `u`. -/
theorem perm_perm_left (φ : SwitchingAutomorphism G u v) :
    φ.perm (φ.perm u) = u := by
  rw [φ.swaps_uv, φ.swaps_vu]

/-- The **permutation matrix** of the switching automorphism on the vertex
space: `P_{x,y} = 1` iff `y = σ x`. -/
noncomputable def permMatrix (φ : SwitchingAutomorphism G u v) :
    Matrix V V ℂ :=
  fun x y => if y = φ.perm x then 1 else 0

end SwitchingAutomorphism

/-- A **switching unitary** of `G` at the pair `(u, v)` and time `τ`: the
*operator-level* content of Kay's switching map that PST genuinely supplies.  It
is a *unitary* `W` on the vertex Hilbert space that carries the `u`-basis state
to a unit-modulus phase multiple of the `v`-basis state — i.e. it swaps the two
endpoints *as states* (up to a global phase), the modulus-1 amplitude witnessing
perfect transfer.

This is exactly what `T = E₊ − E₋` does at the spectral level, *minus* the
upgrade (unprovable in this Hermitian generality) to a 0/1 permutation matrix.
The witness in `switchingUnitary_of_isPST` is the evolution `U(τ)` itself.

Mirrors the canonical `Graphplay.PST.Periodicity.SwitchingUnitary` (kept local
to avoid coupling to that possibly-under-edit sibling). -/
structure SwitchingUnitary (G : WeightedGraph V) (u v : V) (τ : ℝ) where
  /-- The underlying unitary on the vertex space. -/
  mat : Matrix V V ℂ
  /-- It is unitary: `Wᴴ W = 1`. -/
  unitary : mat.conjTranspose * mat = 1
  /-- The transfer phase (the `(u,v)` amplitude). -/
  phase : ℂ
  /-- The phase has unit modulus (perfect transfer). -/
  phase_unit : ‖phase‖ = 1
  /-- `W` sends the `u`-basis state to `phase · e_v`: the `u`-row of `W` is
  concentrated at `v` with amplitude `phase`. -/
  swaps_state : ∀ w : V, mat u w = if w = v then phase else 0

/-- **Kay's switching map, operator level (CLOSED).**  If `G` has PST between `u`
and `v` at time `τ`, then the evolution unitary `U(τ)` is a *switching unitary*:
a unitary on the vertex space carrying the `u`-state to a unit-modulus phase
multiple of the `v`-state.  This is the genuine, hypothesis-free content of Kay's
switching map `T = E₊ − E₋` at the operator level.

Axiom-clean, no `sorry`: unitarity is `WeightedGraph.evolve_unitary`, and the
state-swap is `evolve_eq_zero_of_isPST` (the `u`-row vanishes off `v`, the
surviving `(u,v)` entry having modulus 1) packaged as the explicit `u`-row of
`U(τ)`.

**Honest-relabel note (was `switchingAutomorphism_of_isPST`).**  The previous
statement claimed `Nonempty (SwitchingAutomorphism G u v)` — a genuine
`Equiv.Perm V` adjacency automorphism — from bare PST, behind a `sorry`.  That
is *false in this Hermitian generality*: PST hosts need not be vertex-transitive,
so `T = E₊ − E₋` need not be a 0/1 permutation matrix (it is only under the
integer/simple-spectrum hypotheses of Kay 1310.3885).  The conclusion is here
weakened to the operator-level switching unitary, which PST does supply
unconditionally, and the theorem is closed.  See the caveat on
`SwitchingAutomorphism` and the canonical sibling
`Graphplay.PST.Periodicity.switchingUnitary_of_isPST`.

Reference: Kay, *The perfect state transfer graph limbo* (arXiv:1310.3885);
Godsil's automorphism characterization of PST. -/
theorem switchingUnitary_of_isPST (G : WeightedGraph V) {u v : V} {τ : ℝ}
    (h : IsPST G u v τ) : Nonempty (SwitchingUnitary G u v τ) :=
  ⟨{ mat := G.evolve τ
     unitary := G.evolve_unitary τ
     phase := G.evolve τ u v
     phase_unit := h
     swaps_state := fun w => by
       by_cases hw : w = v
       · subst hw; simp
       · rw [if_neg hw]
         exact evolve_eq_zero_of_isPST G τ u v h w hw }⟩

/-- **Multiple state transfer ⇒ a common switching unitary.**  If `G` exhibits
multiple state transfer at a single time `τ` for a list of pairs, then the single
PST unitary `U(τ)` is, simultaneously, a switching unitary for *every* listed
pair (they all share the one `U(τ)`).  We package the witness for an arbitrary
member of the list.

This is the operator-level content of Kay's "multiple transfer" map.  (It is
*not* upgraded to a combinatorial graph automorphism: that upgrade needs the
integer/simple-spectrum hypotheses of Kay 1310.3885 — see the caveat on
`SwitchingAutomorphism`.)

Reference: Kay, arXiv:1310.3885, §IV (the "multiple transfer" map). -/
theorem switchingUnitary_of_multiple (G : WeightedGraph V)
    {pairs : List (V × V)} {τ : ℝ} {p : V × V}
    (hmem : p ∈ pairs) (h : IsMultipleStateTransfer G pairs τ) :
    Nonempty (SwitchingUnitary G p.1 p.2 τ) :=
  switchingUnitary_of_isPST G (h p hmem)

/-! ## §3 The K-fractional-revival subset framework (Chan–Coutinho–Tamon
et al., 2004.01129)

Fix a subset `K ⊆ V` (modelled as `K : Finset V`).  The **`D_K` periodicity
matrix** at time `τ` is the `V × V` matrix obtained from the evolution `U(τ)` by
keeping only the `K × K` block (zeroing all entries with an index outside `K`).
*K-fractional revival* at time `τ` is the condition that the excitation, started
anywhere inside `K`, stays inside `K`: `U(τ)` maps `span{e_k : k ∈ K}` into
itself, i.e. all "leak" amplitudes `U(τ)_{j,k}` with `k ∈ K`, `j ∉ K` vanish.

When `|K| = 1` this is *periodicity*; when `|K| = 2` it is *(pair) fractional
revival*; when additionally the `K`-block is anti-diagonal it is PST. -/

/-- The **`D_K` periodicity matrix**: the `K × K` block of the evolution `U(τ)`,
extended by zero outside `K × K`.  Entry `(i, j)` is `U(τ)_{i,j}` when both
`i, j ∈ K`, else `0`. -/
noncomputable def periodicityBlock (G : WeightedGraph V) (K : Finset V) (τ : ℝ) :
    Matrix V V ℂ :=
  fun i j => if i ∈ K ∧ j ∈ K then G.evolve τ i j else 0

/-- The periodicity block agrees with `U(τ)` on the `K × K` block. -/
theorem periodicityBlock_apply_mem (G : WeightedGraph V) (K : Finset V) (τ : ℝ)
    {i j : V} (hi : i ∈ K) (hj : j ∈ K) :
    periodicityBlock G K τ i j = G.evolve τ i j := by
  unfold periodicityBlock; rw [if_pos ⟨hi, hj⟩]

/-- Off the `K × K` block, the periodicity matrix is zero. -/
theorem periodicityBlock_apply_not_mem (G : WeightedGraph V) (K : Finset V)
    (τ : ℝ) {i j : V} (h : ¬ (i ∈ K ∧ j ∈ K)) :
    periodicityBlock G K τ i j = 0 := by
  unfold periodicityBlock; rw [if_neg h]

/-- **K-fractional revival.**  Started on the subset `K`, the excitation returns
to `K` with certainty at time `τ`: every "leak" amplitude `U(τ)_{j,k}` with
source `k ∈ K` and destination `j ∉ K` vanishes.  Equivalently the
`K`-supported subspace is invariant under `U(τ)`, so on that subspace `U(τ)`
acts by the (unitary) `D_K` block.

(`|K| = 1`: periodicity.  `|K| = 2`: pair fractional revival.  Anti-diagonal
`K`-block on `|K| = 2`: PST.)

Reference: Chan–Coutinho–Tamon–Vinet–Zhan, arXiv:2004.01129, Def. 2.1. -/
def IsKFractionalRevival (G : WeightedGraph V) (K : Finset V) (τ : ℝ) : Prop :=
  ∀ k ∈ K, ∀ j : V, j ∉ K → G.evolve τ j k = 0

/-- For a single-vertex subset, K-fractional revival is exactly the statement
that the off-`u` column of `U(τ)` vanishes — i.e. `U(τ)` concentrates the
`u`-excitation back on `u` (periodicity, up to phase). -/
theorem isKFractionalRevival_singleton (G : WeightedGraph V) (u : V) (τ : ℝ) :
    IsKFractionalRevival G {u} τ ↔ ∀ j : V, j ≠ u → G.evolve τ j u = 0 := by
  constructor
  · intro h j hj
    exact h u (Finset.mem_singleton.mpr rfl) j (by simpa [Finset.mem_singleton] using hj)
  · intro h k hk j hj
    rw [Finset.mem_singleton] at hk; subst hk
    exact h j (by simpa [Finset.mem_singleton] using hj)

/-- **The full vertex set always exhibits revival.**  Taking `K = univ` there is
no destination `j ∉ K`, so the leak condition is vacuous: `U(τ)` of course keeps
the (whole-space) excitation inside the whole space at every time. -/
theorem isKFractionalRevival_univ (G : WeightedGraph V) (τ : ℝ) :
    IsKFractionalRevival G Finset.univ τ := by
  intro k _ j hj
  exact absurd (Finset.mem_univ j) hj

/-- **Switching the source/target roles is symmetric in the leak condition.**  A
useful reformulation: `K`-fractional revival means every cross amplitude between
`K` and its complement (with source in `K`) vanishes; equivalently the off-block
entry of the periodicity matrix `D_K` agrees with `U(τ)` only inside the block.
We record that under revival the periodicity block reproduces the full evolution
on the `K`-rows: for `k ∈ K` and any `j`, `periodicityBlock G K τ j k = U(τ) j k`
when `j ∈ K`, and `= 0 = U(τ) j k` when `j ∉ K`. -/
theorem periodicityBlock_eq_evolve_of_revival (G : WeightedGraph V) (K : Finset V)
    (τ : ℝ) (hrev : IsKFractionalRevival G K τ) {k : V} (hk : k ∈ K) (j : V) :
    periodicityBlock G K τ j k = G.evolve τ j k := by
  by_cases hj : j ∈ K
  · exact periodicityBlock_apply_mem G K τ hj hk
  · rw [periodicityBlock_apply_not_mem G K τ (fun h => hj h.1)]
    exact (hrev k hk j hj).symm

/-- **The `K`-ratio condition** (the fractional-revival analogue of Godsil's
ratio condition).  Let `S_K := ⋃_{k ∈ K} EigenvalueSupport G k` be the joint
eigenvalue support of the subset `K`.  The ratio condition asks that all
supported eigenvalues lie in a common arithmetic progression: there are
`a > 0, b ∈ ℝ` so that every `λ ∈ S_K` is `b + a·m` for some integer `m`.

This is the spectral criterion that makes the phases `e^{-iτλ}` simultaneously
align so the off-`K` amplitudes can cancel.

Reference: Chan–Coutinho–Tamon–Vinet–Zhan, arXiv:2004.01129, §4; cf. Godsil's
`IsGodsilRatio`. -/
def IsKRatioCondition (G : WeightedGraph V) (K : Finset V) : Prop :=
  ∃ a b : ℝ, 0 < a ∧
    ∀ lam : ℝ, (∃ k ∈ K, lam ∈ EigenvalueSupport G k) →
      ∃ m : ℤ, lam = b + a * (m : ℝ)

/-- The `K`-ratio condition for a singleton `{u}` is Godsil's reflexive ratio
condition at `u` (the support arithmetic-progression condition). -/
theorem isKRatioCondition_singleton (G : WeightedGraph V) (u : V) :
    IsKRatioCondition G {u} ↔
      ∃ a b : ℝ, 0 < a ∧ ∀ lam ∈ EigenvalueSupport G u,
        ∃ m : ℤ, lam = b + a * (m : ℝ) := by
  unfold IsKRatioCondition
  constructor
  · rintro ⟨a, b, ha, h⟩
    refine ⟨a, b, ha, fun lam hlam => h lam ⟨u, Finset.mem_singleton.mpr rfl, hlam⟩⟩
  · rintro ⟨a, b, ha, h⟩
    refine ⟨a, b, ha, ?_⟩
    rintro lam ⟨k, hk, hlam⟩
    rw [Finset.mem_singleton] at hk; subst hk
    exact h lam hlam

/-! **Necessity of the spectral ratio condition for K-fractional revival** lives
in the downstream module `Graphplay.PST.UniversalRatio` (which imports both this
file and `Graphplay.PST.Periodicity`):

* `isKRatioClassCondition_of_fractionalRevival` — the honest general form:
  revival at `τ` confines the supported eigenvalues to at most `|K|` residue
  classes mod `(2π/τ)·ℤ`.  The previously stated single-progression conclusion
  `IsKRatioCondition G K` is *false* for `|K| ≥ 2`: `isKFractionalRevival_univ`
  above already exhibits revival at every `τ` on `K = univ` for every graph,
  while a generic spectrum lies in no arithmetic progression.
* `isKRatioCondition_of_fractionalRevival_singleton` — the `|K| = 1`
  specialization, where one class *is* a single progression: periodicity at `u`
  implies the ratio condition on `{u}`, exactly Godsil's necessity direction. -/

/-! ### Column concentration and real-symmetric revival -/

/-- **Column concentration from PST (pure unitarity).**  If `‖U(τ)_{u,v}‖ = 1`
then the entire `v`-column of `U(τ)` is supported at `u`: `U(τ)_{j,v} = 0` for
`j ≠ u`.  This is the column dual of `evolve_eq_zero_of_isPST` and follows from
`U(τ)ᴴ U(τ) = 1` (the `v`-column has unit `ℓ²`-norm, already saturated by the
`(u,v)` entry).  No symmetry needed. -/
theorem evolve_col_eq_zero_of_isPST (G : WeightedGraph V) (τ : ℝ) (u v : V)
    (hpst : ‖G.evolve τ u v‖ = 1) (j : V) (hj : j ≠ u) :
    G.evolve τ j v = 0 := by
  -- `v`-column unit `ℓ²`-norm from `U(τ)ᴴ U(τ) = 1`.
  have hU := G.evolve_unitary τ
  have hvv := congrFun (congrFun hU v) v
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hvv
  have key : ∑ w : V, (G.evolve τ)ᴴ v w * G.evolve τ w v
      = ((∑ w : V, ‖G.evolve τ w v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Matrix.conjTranspose_apply, mul_comm, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [key] at hvv
  have hsum : ∑ w : V, ‖G.evolve τ w v‖ ^ 2 = 1 := by exact_mod_cast hvv
  have hsplit : ‖G.evolve τ u v‖ ^ 2
      + ∑ w ∈ Finset.univ.erase u, ‖G.evolve τ w v‖ ^ 2 = 1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)] at hsum; linarith [hsum]
  rw [hpst] at hsplit; simp only [one_pow] at hsplit
  have hrest : ∑ w ∈ Finset.univ.erase u, ‖G.evolve τ w v‖ ^ 2 = 0 := by linarith
  have hmem : j ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
  have hz : ‖G.evolve τ j v‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg _)).mp hrest j hmem
  have : ‖G.evolve τ j v‖ = 0 := by nlinarith [norm_nonneg (G.evolve τ j v)]
  exact norm_eq_zero.mp this

/-- **The evolution is complex-symmetric when the adjacency is symmetric.**  For
a symmetric (real-weighted) adjacency `Aᵀ = A`, `U(τ)ᵀ = U(τ)`, hence
`U(τ)_{v,u} = U(τ)_{u,v}` entrywise. -/
theorem evolve_symm_of_isSymm (G : WeightedGraph V) (hsymm : G.adj.IsSymm)
    (τ : ℝ) (u v : V) : G.evolve τ v u = G.evolve τ u v := by
  have htr : (G.evolve τ)ᵀ = G.evolve τ := by
    unfold WeightedGraph.evolve
    rw [← Matrix.exp_transpose]
    congr 1
    rw [Matrix.transpose_smul, hsymm]
  have h := congrFun (congrFun htr u) v
  rwa [Matrix.transpose_apply] at h

/-- **PST is `K`-fractional revival on an antipodal pair (`|K| = 2`),
real-symmetric case (CLOSED).**  Perfect state transfer `u → v` at time `τ` on a
graph with *symmetric* adjacency (`Aᵀ = A`, the classical real-weighted Godsil
setting) implies fractional revival on `K = {u, v}` at time `τ`: the only nonzero
amplitudes out of `{u, v}` stay within `{u, v}`.

The `v`-leak (`U(τ)_{j,v} = 0`, `j ∉ {u,v}`) is pure unitarity
(`evolve_col_eq_zero_of_isPST`).  The `u`-leak (`U(τ)_{j,u} = 0`, `j ∉ {u,v}`)
uses symmetry: `‖U(τ)_{v,u}‖ = ‖U(τ)_{u,v}‖ = 1`, so the `u`-column concentrates
at `v`.  Axiom-clean.  (The fully-general Hermitian statement is genuinely false
without symmetry: `‖U(τ)_{·,u}‖ = 1` requires target-side `v → u`.) -/
theorem isKFractionalRevival_pair_of_isPST_of_isSymm (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm) {u v : V} {τ : ℝ} (_huv : u ≠ v) (h : IsPST G u v τ) :
    IsKFractionalRevival G {u, v} τ := by
  have hUV : ‖G.evolve τ u v‖ = 1 := h
  -- `‖U(τ)_{v,u}‖ = 1` from symmetry.
  have hVU : ‖G.evolve τ v u‖ = 1 := by rw [evolve_symm_of_isSymm G hsymm τ u v]; exact hUV
  intro k hk j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  have hju : j ≠ u := fun hju => hj (by simp [hju])
  have hjv : j ≠ v := fun hjv => hj (by simp [hjv])
  rcases hk with hk | hk
  · -- `k = u`: column `u` concentrates at `v` (using `‖U(τ)_{v,u}‖ = 1`).
    rw [hk]
    exact evolve_col_eq_zero_of_isPST G τ v u hVU j hjv
  · -- `k = v`: column `v` concentrates at `u` (pure unitarity).
    rw [hk]
    exact evolve_col_eq_zero_of_isPST G τ u v hUV j hju

/-- **PST is `K`-fractional revival on an antipodal pair (`|K| = 2`), for a
real-symmetric graph.**  For `G` with `Aᵀ = A`, perfect state transfer `u → v` at
time `τ` implies fractional revival on `K = {u, v}` at time `τ`: the only nonzero
amplitudes out of `{u, v}` stay within `{u, v}`.

The `IsSymm` hypothesis is essential, not cosmetic: for general non-symmetric
Hermitian `A` the `k = u` leak is genuinely possible — a directed triangle
`u → v → w → u` realizes `‖U_{u,v}‖ = 1` yet leaks `‖U_{w,u}‖ = 1` with
`w ∉ {u, v}`.  So this is the correct, true statement; it delegates to the
axiom-clean `isKFractionalRevival_pair_of_isPST_of_isSymm`.

Reference: Chan et al., arXiv:2004.01129 (PST as fractional revival). -/
theorem isKFractionalRevival_pair_of_isPST (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm) {u v : V} {τ : ℝ} (huv : u ≠ v) (h : IsPST G u v τ) :
    IsKFractionalRevival G {u, v} τ :=
  isKFractionalRevival_pair_of_isPST_of_isSymm G hsymm huv h

/-- **Pair fractional revival from Godsil's PST-ready alignment (sufficiency),
explicit time `π/a`, CLOSED and axiom-clean.**  On a real-symmetric graph, if the
pair `(u, v)` carries Godsil's PST-ready spectral data — arithmetic alignment of
the support (`λ = b + a·(kof λ)`, `a > 0`) with the parity-matched cross-projector
structure `(E_λ)_{u,v} = (-1)^{kof λ}(E_λ)_{u,u}` — then fractional revival occurs
on the antipodal pair `K = {u, v}` at the **explicit time `τ = π/a`**.

This is the *backward* (existence) content reachable from the rebuilt
exact-period bridge: the alignment yields PST `u → v` at `τ = π/a`
(`isPST_of_aligned_paritySigned`, no Diophantine approximation), and PST on a
symmetric graph is fractional revival on the pair
(`isKFractionalRevival_pair_of_isPST`).  Together with the necessity direction
(`Graphplay.PST.UniversalRatio.isKRatioClassCondition_of_fractionalRevival`)
this closes the *sufficiency* half of the CCTVZ `|K| = 2` revival/ratio circle.

**Honest-restatement note (was an unprovable `Classical.choose` pin).**  The prior
form took the bundled `h : IsGodsilPSTReady G u v` and concluded revival at
`π / (Classical.choose h)`.  That is a LANDMINE: `Classical.choose h` extracts the
gap `a` from the *opaque* existential witness, and is **not** defeq to the `a`
obtained by `obtain`-destructuring `h`, so the bridging `Classical.choose h = a`
was an unprovable `sorry`.  We restate with the alignment data `(a, b, kof)`
*unbundled* as explicit hypotheses, which (i) is the faithful "`τ = π/a`" content
the docstring always advertised and (ii) is fully provable.  The bundled-`h`
existential-time form is recorded as the corollary below.

Reference: Chan–Coutinho–Tamon–Vinet–Zhan, arXiv:2004.01129; Godsil 2012. -/
theorem isKFractionalRevival_pair_of_aligned_paritySigned (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm) {u v : V} (huv : u ≠ v)
    (a b : ℝ) (ha : 0 < a) (kof : ℝ → ℤ)
    (halign : ∀ lam ∈ Finset.univ.image G.herm.eigenvalues,
        lam = b + a * (kof lam : ℝ))
    (hsign : ∀ lam ∈ Finset.univ.image G.herm.eigenvalues,
        eigenProjEntryLocal G lam u v
          = ((-1 : ℂ) ^ (kof lam)) * (eigenProjDiagLocal G lam u : ℂ)) :
    IsKFractionalRevival G {u, v} (Real.pi / a) :=
  isKFractionalRevival_pair_of_isPST G hsymm huv
    (isPST_of_aligned_paritySigned G u v a b ha kof halign hsign)

/-- **Pair fractional revival from Godsil's PST-ready data (sufficiency, bundled
existential time), CLOSED and axiom-clean.**  On a real-symmetric graph, if the
pair `(u, v)` carries Godsil's PST-ready spectral data `IsGodsilPSTReady G u v`,
then fractional revival occurs on `K = {u, v}` at *some* positive time.  This is
the bundled-hypothesis companion of
`isKFractionalRevival_pair_of_aligned_paritySigned`; the witnessing time is the
`π/a` of the alignment gap.  Reference: CCTVZ arXiv:2004.01129; Godsil 2012. -/
theorem isKFractionalRevival_pair_of_isGodsilPSTReady (G : WeightedGraph V)
    (hsymm : G.adj.IsSymm) {u v : V} (huv : u ≠ v)
    (h : IsGodsilPSTReady G u v) :
    ∃ τ : ℝ, 0 < τ ∧ IsKFractionalRevival G {u, v} τ := by
  obtain ⟨a, b, kof, ha, halign, hsign⟩ := h
  exact ⟨Real.pi / a, by positivity,
    isKFractionalRevival_pair_of_aligned_paritySigned G hsymm huv a b ha kof halign hsign⟩

end PST
end Graphplay
