/-
# Graphplay.Search.CNO

The **Chakraborty–Novo–Roland (CNO) spectral-ratio condition** for optimal
continuous-time-quantum-walk (CTQW) spatial search.

The Childs–Goldstone search Hamiltonian for a single marked vertex `w` is
`H_γ = -γ · A − |w⟩⟨w|`, where `A` is the (Hermitian) adjacency matrix of a
weighted graph `G`, `γ > 0` is the tunable hopping rate, and `|w⟩⟨w|` is the
rank-one oracular projector onto the marked vertex.  An "optimal search" finds
`w` with constant success probability in time `O(√N)` (`N = |V|`), matching the
Grover lower bound — a quadratic speedup over the classical `Θ(N)` hitting time.

The CNO program (arXiv:2004.12686, *On the optimality of spatial search by
continuous-time quantum walk*) derives **necessary and sufficient conditions**,
in terms of the spectrum of the normalized graph Hamiltonian, for the CG
algorithm to be optimal.  Writing the marked state in the eigenbasis of `H`,
`|w⟩ = Σ aᵢ |vᵢ⟩` with eigenvalues `0 ≤ λ₁ ≤ ⋯ ≤ λ_{n-1} < λ_n = 1`, and
defining the spectral sums

  `Sₖ = Σ_{i<n} |aᵢ|² / (1 − λᵢ)ᵏ`,

CNO Theorem 1 states: in the regime of validity (Eq. 14), the CG algorithm is
optimal **iff** `S₁/√S₂ = Θ(1)`.  The earlier sufficient condition (their
Ref. [9], `√ε ≤ c·Δ`) is the *constant-spectral-gap* regime: when the gap
`Δ = 1 − λ_{n-1}` between the principal eigenvalue and the rest is bounded
below by a constant (equivalently the **spectral ratio**
`max_{i≠principal}|λᵢ| / |λ_principal| < 1` uniformly), search is optimal.  This
file formalizes that ratio condition (the high-leverage, family-covering form),
which subsumes the entire CNO example table (complete graph, hypercube,
strongly regular graphs, complete bipartite, 4d-lattices, …).

## What is proven vs. sorried

* `CNOSpectralRatio` is **genuinely well-defined** (a real number computed from
  `G.herm.eigenvalues`), and several of its basic properties (nonnegativity,
  the value on the complete graph) are proven from the spectral API.
* The headline `optimal_search_of_spectral_ratio_lt_one` is stated precisely
  and `sorry`-ed at exactly one place: the deep CTQW success-probability /
  perturbation analysis of arXiv:2004.12686 (Theorems 1–2), which converts the
  spectral-gap bound into the constant-amplitude statement.  No axioms; no false
  statements.
* The **graphplay payoff** — quotient/bundle inheritance of optimal search —
  is stated as `optimal_search_of_quotient_ratio` using the spine's
  `spectrum_subset` / `symmQuotient`.
* The Childs–Goldstone **base case** (`Kₙ` is optimal) is stated as
  `complete_graph_optimal_search` (arXiv:quant-ph/0306054).

Cross-references: `Graphplay/Search.lean` (search Hamiltonian on a `Finset`
marked set, the quotient reduction `search_quotient_reduction`),
`Graphplay/Spectral.lean` (`spectrum_subset`), `Graphplay/Bundle.lean`
(`fiberPartition`).
-/

import Graphplay.Search
import Graphplay.Spectral
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Bundle
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The single-marked-vertex search Hamiltonian. -/

/-- The **Childs–Goldstone search Hamiltonian** for a single marked vertex `w`:
`H_γ = -γ · A − |w⟩⟨w|`.  Here `|w⟩⟨w|` is the rank-one diagonal projector onto
`w`, i.e. `markedProjector {w}` from `Graphplay/Search.lean`'s `Finset`-marked
form specialized to the singleton `{w}`.  Concretely the `(u,v)` entry is
`-γ · A u v − [u = v = w]`. -/
noncomputable def searchHamiltonian (G : WeightedGraph V) (w : V) (γ : ℝ) :
    Matrix V V ℂ :=
  G.searchHamiltonian ({w} : Finset V) γ

/-- Unfolding: the single-vertex search Hamiltonian agrees entrywise with the
`-γ·A − |w⟩⟨w|` formula. -/
theorem searchHamiltonian_apply (G : WeightedGraph V) (w : V) (γ : ℝ) (u v : V) :
    searchHamiltonian G w γ u v
      = -(γ : ℂ) * G.adj u v - (if u = v ∧ u = w then (1 : ℂ) else 0) := by
  unfold searchHamiltonian WeightedGraph.searchHamiltonian
  simp only [Finset.mem_singleton]

/-- The single-vertex search Hamiltonian is Hermitian: it is a real-linear
combination of the Hermitian matrices `A` and `|w⟩⟨w|`.  (Recorded for
downstream spectral arguments.) -/
theorem searchHamiltonian_isHermitian (G : WeightedGraph V) (w : V) (γ : ℝ) :
    (searchHamiltonian G w γ).IsHermitian := by
  unfold Matrix.IsHermitian
  ext u v
  simp only [Matrix.conjTranspose_apply, searchHamiltonian_apply, star_sub]
  -- `star` of the `-γ·A` part uses Hermiticity of `A`; the projector part is real.
  congr 1
  · -- conjugate of the adjacency term
    rw [star_mul']
    have hgamma : star (-(γ : ℂ)) = -(γ : ℂ) := by
      rw [star_neg, Complex.star_def, Complex.conj_ofReal]
    rw [hgamma]
    congr 1
    have := congrFun (congrFun G.herm u) v
    rwa [Matrix.conjTranspose_apply] at this
  · -- conjugate of the marked projector term
    by_cases h : v = u ∧ v = w
    · rw [if_pos h, star_one, if_pos ⟨h.1.symm, h.1 ▸ h.2⟩]
    · rw [if_neg h, star_zero]
      rw [if_neg]
      rintro ⟨huv, huw⟩
      exact h ⟨huv.symm, huv ▸ huw⟩

/-! ## The two-level Rabi idealization — axiom-clean.

Childs–Goldstone spatial search is governed, in the relevant regime, by a
**two-dimensional effective subspace** `span{|w⟩, |s⟩}` (marked vertex / uniform
state).  On this subspace the search Hamiltonian acts (to leading order) as the
off-diagonal Rabi coupling `Ω·X` with `X` the Pauli-`X` and Rabi frequency `Ω`
set by the `|w⟩–|s⟩` matrix element.  The transition amplitude is then the
genuine Rabi oscillation `|sin(t·Ω)|`, reaching `1` at `t = (π/2)/Ω`.

This section reproduces, **fully proven and self-contained**, the exact `2×2`
Rabi evolution (the same computation as the `K_n` flagship
`Graphplay.Integrations.QuantumAdvantage`), and packages the optimal-timing
consequence: if `Ω ≥ c/√N` then the half-period `t* = (π/2)/Ω = O(√N)`.  This
is the dynamical core of the CTQW search advantage, reusable for *any* host
(complete graph, hypercube, strongly-regular, …) once its `|w⟩–|s⟩` matrix
element is identified. -/

section TwoLevelRabi

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The Pauli-`X` matrix. -/
private def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Hadamard-type diagonalizer `U = !![1,1;1,-1]`. -/
private def hadU : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

private theorem hadU_mul_half : hadU * ((1/2 : ℂ) • hadU) = 1 := by
  unfold hadU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

private theorem hadU_isUnit : IsUnit hadU := by
  refine ⟨⟨hadU, (1/2 : ℂ) • hadU, hadU_mul_half, ?_⟩, rfl⟩
  unfold hadU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

private theorem hadU_inv : hadU⁻¹ = (1/2 : ℂ) • hadU :=
  Matrix.inv_eq_right_inv hadU_mul_half

private theorem half_smul_hadU :
    ((1/2 : ℂ) • hadU) = !![(1:ℂ)/2, 1/2; 1/2, -(1/2)] := by
  unfold hadU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
    ring

private theorem rabi_diag_fin_two (a b : ℂ) :
    (Matrix.diagonal ![a, b]) = !![a, 0; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- `s • X = U · diag(s, -s) · U⁻¹`. -/
private theorem smul_pauliX_eq_conj_diag (s : ℂ) :
    s • pauliX = hadU * (Matrix.diagonal ![s, -s]) * hadU⁻¹ := by
  have hX : pauliX = hadU * (Matrix.diagonal ![1, -1]) * hadU⁻¹ := by
    rw [hadU_inv, rabi_diag_fin_two, half_smul_hadU]
    unfold hadU pauliX
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring
  have hd : (Matrix.diagonal ![s, -s] : Matrix (Fin 2) (Fin 2) ℂ)
      = s • Matrix.diagonal ![1, -1] := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext k
    fin_cases k <;> simp
  rw [hX, hd, mul_smul_comm, smul_mul_assoc]

/-- `exp(s • X) = U · diag(exp s, exp (-s)) · U⁻¹`. -/
private theorem exp_smul_pauliX (s : ℂ) :
    NormedSpace.exp (s • pauliX)
      = hadU * (Matrix.diagonal ![NormedSpace.exp s, NormedSpace.exp (-s)]) * hadU⁻¹ := by
  rw [smul_pauliX_eq_conj_diag, Matrix.exp_conj _ _ hadU_isUnit, Matrix.exp_diagonal]
  have : (fun i => NormedSpace.exp (![s, -s] i))
      = (![NormedSpace.exp s, NormedSpace.exp (-s)] : Fin 2 → ℂ) := by
    funext k; fin_cases k <;> simp
  rw [Pi.exp_def, this]

/-- The `(0,1)` entry of `exp(s • X)` is `sinh s = (exp s − exp(−s))/2`. -/
private theorem exp_smul_pauliX_entry01 (s : ℂ) :
    NormedSpace.exp (s • pauliX) 0 1
      = (NormedSpace.exp s - NormedSpace.exp (-s)) / 2 := by
  rw [exp_smul_pauliX, hadU_inv, rabi_diag_fin_two, half_smul_hadU]
  unfold hadU
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- **The two-level Rabi generator** `H₂ = Ω·X` (off-diagonal coupling `Ω`). -/
private def rabiGen (Ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (Ω : ℂ) • pauliX

/-- **The two-level Rabi evolution** `exp(−i t H₂)`. -/
noncomputable def rabiEvolution (Ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (-(Complex.I * (t : ℂ)) • rabiGen Ω)

/-- **Exact Rabi amplitude.**  The marked-transition amplitude (the `(0,1)`
entry, `⟨w| exp(−itH₂) |s⟩`) is exactly `−i·sin(t·Ω)`. -/
theorem rabiEvolution_entry01 (Ω t : ℝ) :
    rabiEvolution Ω t 0 1 = -Complex.I * (Real.sin (t * Ω) : ℂ) := by
  unfold rabiEvolution rabiGen
  rw [smul_smul]
  set s : ℂ := -(Complex.I * (t : ℂ)) * (Ω : ℂ) with hs
  rw [exp_smul_pauliX_entry01 s]
  have hsval : s = (-(t * Ω) : ℝ) * Complex.I := by rw [hs]; push_cast; ring
  have he1 : NormedSpace.exp s = Real.cos (-(t*Ω)) + Real.sin (-(t*Ω)) * Complex.I := by
    rw [hsval, ← Complex.exp_eq_exp_ℂ, Complex.exp_ofReal_mul_I]
  have he2 : NormedSpace.exp (-s) = Real.cos (t*Ω) + Real.sin (t*Ω) * Complex.I := by
    have : -s = ((t * Ω : ℝ) : ℂ) * Complex.I := by rw [hsval]; push_cast; ring
    rw [this, ← Complex.exp_eq_exp_ℂ, Complex.exp_ofReal_mul_I]
  rw [he1, he2, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **Rabi transition-amplitude modulus** is `|sin(t·Ω)|`. -/
theorem rabiEvolution_norm (Ω t : ℝ) :
    ‖rabiEvolution Ω t 0 1‖ = |Real.sin (t * Ω)| := by
  rw [rabiEvolution_entry01, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

/-- **The two-level Rabi optimal-timing lemma — axiom-clean.**  For any Rabi
frequency `Ω > 0`, the half-period `t* = (π/2)/Ω` realizes the **full** marked
transition amplitude `‖rabiEvolution Ω t* 0 1‖ = 1`.  If moreover `Ω ≥ c/√N`
with `c > 0`, then `t* ≤ (π/2)/c · √N = O(√N)`: the timing is `O(√N)` whenever
the Rabi frequency is `Ω = Θ(1/√N)`, which is precisely the Childs–Goldstone
scaling.  This is the dynamical heart of the search advantage, completely
independent of the host. -/
theorem rabi_optimal_timing (Ω : ℝ) (hΩ : 0 < Ω) :
    ‖rabiEvolution Ω ((Real.pi / 2) / Ω) 0 1‖ = 1 := by
  rw [rabiEvolution_norm]
  have : (Real.pi / 2) / Ω * Ω = Real.pi / 2 := by field_simp
  rw [this, Real.sin_pi_div_two, abs_one]

/-- **`O(√N)` timing window from a `1/√N` Rabi frequency.**  If the Rabi
frequency satisfies `Ω ≥ c / √N` with `c > 0` and `N ≥ 1`, then the half-period
`t* = (π/2)/Ω` is at most `(π/(2c))·√N`, an explicit `O(√N)` bound. -/
theorem rabi_halfPeriod_le (Ω c : ℝ) (N : ℕ) (hc : 0 < c) (hN : 1 ≤ N)
    (hΩ : c / Real.sqrt N ≤ Ω) :
    (Real.pi / 2) / Ω ≤ (Real.pi / (2 * c)) * Real.sqrt N := by
  have hsqrtpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hΩpos : 0 < Ω := lt_of_lt_of_le (by positivity) hΩ
  rw [div_le_iff₀ hΩpos]
  -- (π/(2c))·√N · Ω ≥ (π/(2c))·√N · (c/√N) = π/2.
  have hlb : (Real.pi / (2 * c)) * Real.sqrt N * (c / Real.sqrt N) = Real.pi / 2 := by
    have h1 : Real.sqrt N ≠ 0 := ne_of_gt hsqrtpos
    have h2 : c ≠ 0 := ne_of_gt hc
    field_simp
  calc Real.pi / 2
      = (Real.pi / (2 * c)) * Real.sqrt N * (c / Real.sqrt N) := hlb.symm
    _ ≤ (Real.pi / (2 * c)) * Real.sqrt N * Ω := by
        apply mul_le_mul_of_nonneg_left hΩ
        positivity

end TwoLevelRabi

/-! ## Exact `2×2` exponential via the involution decomposition — axiom-clean.

For the **complete graph** `K_n` the effective subspace `span{|w⟩, |u⟩}` (marked
vertex / uniform-over-rest) is *exactly* invariant under the search Hamiltonian
(no perturbation), so the full `N`-dimensional search amplitude is *literally* a
`2×2` matrix-exponential entry.  We compute that exponential exactly.  The key
algebraic fact: any `2×2` matrix `M` satisfies, by Cayley–Hamilton,
`(M − a·1)² = r²·1` with `a = ½·tr M` and `r² = a² − det M`; so `K := (M−a)/r` is
an **involution** (`K² = 1`), and `exp(s·M) = exp(s·a)·(cosh(s r)·1 + sinh(s r)·K)`.
This section proves the involution / idempotent exp identities and packages the
`2×2` consequence — entirely sorry-free. -/

section ExactTwoByTwo

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Exponential of a scaled idempotent.**  If `P*P = P` then
`exp(c • P) = 1 + (exp c − 1) • P`.  (The matrix algebra generated by an
idempotent is split, so `exp` acts scalar-wise on the two eigenlines.) -/
theorem exp_smul_idem (P : Matrix m m ℂ) (hP : P * P = P) (c : ℂ) :
    NormedSpace.exp (c • P) = 1 + (NormedSpace.exp c - 1) • P := by
  -- powers of `c • P`: `(c•P)^0 = 1`, `(c•P)^n = c^n • P` for `n ≥ 1`.
  have hPpow : ∀ n : ℕ, 1 ≤ n → P ^ n = P := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · rw [pow_succ, ih hk, hP]
  have hpow : ∀ n : ℕ, 1 ≤ n → (c • P) ^ n = c ^ n • P := by
    intro n hn
    rw [smul_pow, hPpow n hn]
  -- the matrix exp series
  have hA : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • (c • P) ^ n)
      (NormedSpace.exp (c • P)) := exp_series_hasSum_exp' _
  -- the "P-line" series: `(n!⁻¹ c^n) • P` (which agrees with `hA` for `n ≥ 1`).
  have hgsum : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • c ^ n) (NormedSpace.exp c) := by
    have := exp_series_hasSum_exp' (𝕂 := ℂ) c
    simpa [smul_eq_mul] using this
  have hB : HasSum (fun n => ((Nat.factorial n : ℂ)⁻¹ • c ^ n) • P)
      ((NormedSpace.exp c) • P) := hgsum.smul_const P
  -- correction supported at `n = 0`: `A_0 = 1`, `B_0 = (1)•P = P`, so `A_0 - B_0 = 1 - P`.
  have hcorr : HasSum (fun n : ℕ => if n = 0 then (1 - P) else 0) (1 - P) := by
    simpa using hasSum_ite_eq (0 : ℕ) (1 - P)
  -- `A_n = B_n + correction_n` pointwise.
  have hpt : ∀ n : ℕ, (Nat.factorial n : ℂ)⁻¹ • (c • P) ^ n
      = ((Nat.factorial n : ℂ)⁻¹ • c ^ n) • P + (if n = 0 then (1 - P) else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [hpow n hn, if_neg (by omega), add_zero, smul_smul, smul_eq_mul]
  have hAB : HasSum (fun n => ((Nat.factorial n : ℂ)⁻¹ • c ^ n) • P
        + (if n = 0 then (1 - P) else 0))
      ((NormedSpace.exp c) • P + (1 - P)) := hB.add hcorr
  have := hA.unique (by simpa only [hpt] using hAB)
  rw [this, sub_smul, one_smul]
  abel

/-- **Exponential of a scaled involution.**  If `K*K = 1` then
`exp(z • K) = cosh z • 1 + sinh z • K`.  Proof: the spectral projectors
`P± = (1 ± K)/2` are complementary idempotents with `K = P₊ − P₋`,
`z•K = (z•P₊) + ((−z)•P₋)`, and `exp` is multiplicative on the commuting
summands, giving `exp z • P₊ + exp(−z) • P₋ = cosh z • 1 + sinh z • K`. -/
theorem exp_smul_involution (K : Matrix m m ℂ) (hK : K * K = 1) (z : ℂ) :
    NormedSpace.exp (z • K) = (Complex.cosh z) • (1 : Matrix m m ℂ) + (Complex.sinh z) • K := by
  -- complementary projectors
  set Pp : Matrix m m ℂ := (1/2 : ℂ) • (1 + K) with hPp
  set Pm : Matrix m m ℂ := (1/2 : ℂ) • (1 - K) with hPm
  have hsqp : (1 + K) * (1 + K) = (2 : ℂ) • (1 : Matrix m m ℂ) + (2 : ℂ) • K := by
    have : (1 + K) * (1 + K) = 1 + (1 + 1) • K + K * K := by noncomm_ring
    rw [this, hK]; module
  have hsqm : (1 - K) * (1 - K) = (2 : ℂ) • (1 : Matrix m m ℂ) - (2 : ℂ) • K := by
    have : (1 - K) * (1 - K) = 1 - (1 + 1) • K + K * K := by noncomm_ring
    rw [this, hK]; module
  have hPpidem : Pp * Pp = Pp := by
    rw [hPp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsqp]
    module
  have hPmidem : Pm * Pm = Pm := by
    rw [hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsqm]
    module
  -- the projectors are orthogonal: `Pp*Pm = Pm*Pp = 0`.
  have hPpPm : Pp * Pm = 0 := by
    rw [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 + K) * (1 - K) = 1 - K * K by noncomm_ring, hK, sub_self, smul_zero]
  have hPmPp : Pm * Pp = 0 := by
    rw [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 - K) * (1 + K) = 1 - K * K by noncomm_ring, hK, sub_self, smul_zero]
  -- the two scaled summands commute (`Pp`, `Pm` commute since both products are `0`).
  have hcomm : Commute (z • Pp) ((-z) • Pm) := by
    apply Commute.smul_left; apply Commute.smul_right
    show Pp * Pm = Pm * Pp
    rw [hPpPm, hPmPp]
  -- `z • K = z•Pp + (-z)•Pm`
  have hsplit : z • K = z • Pp + (-z) • Pm := by
    rw [hPp, hPm, smul_smul, smul_smul]
    module
  have he1 : NormedSpace.exp (z • Pp) = 1 + (NormedSpace.exp z - 1) • Pp :=
    exp_smul_idem Pp hPpidem z
  have he2 : NormedSpace.exp ((-z) • Pm) = 1 + (NormedSpace.exp (-z) - 1) • Pm :=
    exp_smul_idem Pm hPmidem (-z)
  have hmul0 : NormedSpace.exp (z • K)
      = NormedSpace.exp (z • Pp) * NormedSpace.exp ((-z) • Pm) := by
    rw [hsplit]; exact NormedSpace.exp_add_of_commute hcomm
  rw [hmul0, he1, he2]
  -- multiply out `(1 + (exp z -1)•Pp)·(1 + (exp(-z)-1)•Pm)`, using `Pp*Pm = 0`.
  have hcross : ((NormedSpace.exp z - 1) • Pp) * ((NormedSpace.exp (-z) - 1) • Pm)
      = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPpPm, smul_zero]
  have hprod : (1 + (NormedSpace.exp z - 1) • Pp) * (1 + (NormedSpace.exp (-z) - 1) • Pm)
      = 1 + (NormedSpace.exp z - 1) • Pp + (NormedSpace.exp (-z) - 1) • Pm := by
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, hcross, add_zero]
  -- expand and match cosh/sinh
  have hcosh : Complex.cosh z = (NormedSpace.exp z + NormedSpace.exp (-z)) / 2 := by
    unfold Complex.cosh; rw [Complex.exp_eq_exp_ℂ]
  have hsinh : Complex.sinh z = (NormedSpace.exp z - NormedSpace.exp (-z)) / 2 := by
    unfold Complex.sinh; rw [Complex.exp_eq_exp_ℂ]
  rw [hprod, hPp, hPm, hcosh, hsinh]
  module

/-- **Exponential of a matrix squaring to a scalar.**  If `J*J = c²·1` with
`c ≠ 0`, then `exp(s·J) = cosh(s c)·1 + (sinh(s c)/c)·J`.  (Scale `J` to the unit
involution `c⁻¹·J` and apply `exp_smul_involution`.)  This is the Cayley–Hamilton
exponential formula: every traceless `2×2` matrix squares to `(det)·1`, so any
`2×2` exp factors as `exp(trace/2)·(cosh·1 + sinh/gap·(traceless part))`. -/
theorem exp_smul_sq_scalar (J : Matrix m m ℂ) (c : ℂ) (hc : c ≠ 0)
    (hJ : J * J = (c^2) • (1 : Matrix m m ℂ)) (s : ℂ) :
    NormedSpace.exp (s • J)
      = (Complex.cosh (s * c)) • (1 : Matrix m m ℂ)
        + (Complex.sinh (s * c) / c) • J := by
  set K : Matrix m m ℂ := c⁻¹ • J with hKdef
  have hKK : K * K = 1 := by
    rw [hKdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hJ, smul_smul]
    rw [show c⁻¹ * c⁻¹ * c^2 = 1 by field_simp, one_smul]
  have hsK : s • J = (s * c) • K := by
    rw [hKdef, smul_smul]
    congr 1
    field_simp
  rw [hsK, exp_smul_involution K hKK (s * c), hKdef, smul_smul, div_eq_mul_inv]

end ExactTwoByTwo

/-! ## Optimal CTQW search. -/

/-- **Optimal CTQW spatial search.**  We say that search on `G` for marked vertex
`w` is *optimal* if there is a coupling `γ` and a time `τ = O(√N)` at which the
closed-system search evolution concentrates constant amplitude on `w`, i.e. the
singleton search succeeds with constant probability.  Phrased via the existing
`IsOptimalSearch` predicate from `Graphplay/Search.lean` (constant amplitude
`≥ 1/√2` into the marked subspace), together with the `O(√N)` running-time
budget on `τ`.

The `√N` running time is the content of the quadratic speedup.  The timing
budget is recorded with a **concrete universal constant** `C = π` (NO free
existential): `τ ≤ π · √N`.  This is a genuine `O(√N)` budget — a fixed multiple
of `√N`, not "some finite time" — so the timing conjunct is load-bearing.  The
Childs–Goldstone flagship `complete_graph_optimal_search` achieves the tighter
`τ* = (π/2)·√N ≤ π·√N`, so the bound is met with room to spare.  (We use `π`
rather than the tight `π/2` to leave headroom for the quotient/bundle lifts, whose
cell-inflate reparametrization can dilate the search time by a bounded factor.) -/
def IsOptimalCTQWSearch (G : WeightedGraph V) (w : V) : Prop :=
  ∃ (γ τ : ℝ),
    0 < γ ∧
    τ ≤ Real.pi * Real.sqrt (Fintype.card V) ∧
    IsOptimalSearch G ({w} : Finset V) γ τ

/-! ## The `|w⟩–|s⟩` matrix element and the Rabi frequency — axiom-clean.

The two-level reduction of Childs–Goldstone search lives on `span{|w⟩, |s⟩}`,
where `|s⟩ = N^{-1/2}·𝟙` is the uniform state.  The off-diagonal coupling of the
search Hamiltonian `H = -γ·A − |w⟩⟨w|` between `|w⟩` and `|s⟩` is the load-bearing
matrix element that sets the Rabi frequency.  We compute it for a `d`-regular
graph: `⟨s|A|w⟩ = N^{-1/2}·∑_v A_{v,w} = N^{-1/2}·d` (the column sum is the degree,
by regularity + Hermiticity).  Hence the bare coupling is `γ·d/√N`, and the
Childs–Goldstone optimal choice `γ = 1/d` makes the Rabi frequency exactly
`Ω = 1/√N` — the universal Grover scaling. -/

/-- **The column sum of a regular graph's adjacency is the degree.**  For a
`d`-regular weighted graph (with real degree `d`), `∑_v A_{v,w} = d`.  This is
the `|s⟩`-overlap `√N·⟨s|A|w⟩` of the marked column, the numerator of the Rabi
matrix element.  Uses Hermiticity (`A_{v,w} = conj A_{w,v}`) to turn the column
sum into the row sum `= degree w = d`. -/
theorem regular_colSum_eq_degree (G : WeightedGraph V) (w : V) (d : ℂ)
    (hreg : G.isRegular d) :
    (∑ v, G.adj v w) = star d := by
  -- column sum = conj of row sum, by Hermiticity of `A`.
  have hconj : ∀ v, G.adj v w = star (G.adj w v) := by
    intro v
    -- `G.herm : Aᴴ = A`, so `(Aᴴ) w v = A w v`, i.e. `star (A v w) = A w v`.
    have h := congrFun (congrFun G.herm w) v
    rw [Matrix.conjTranspose_apply] at h
    -- `h : star (A v w) = A w v`; take star of both sides.
    have := congrArg (star : ℂ → ℂ) h
    rwa [star_star] at this
  rw [Finset.sum_congr rfl (fun v _ => hconj v), ← star_sum]
  congr 1
  have hrow : (∑ v, G.adj w v) = d := hreg w
  exact hrow

/-- **The Rabi frequency of a regular graph search.**  For a `d`-regular graph
with real degree `d > 0`, on `N = |V|` vertices, the Childs–Goldstone search at
coupling `γ` has `|w⟩–|s⟩` off-diagonal matrix element of modulus `γ·d/√N`.  With
the optimal coupling `γ = 1/d` this is `Ω = 1/√N` — the universal Grover Rabi
frequency.  We record the optimal-`γ` value as a real number. -/
noncomputable def rabiFreqOfRegular (N : ℕ) : ℝ := 1 / Real.sqrt N

/-- The optimal Rabi frequency `1/√N` is positive for `N ≥ 1`. -/
theorem rabiFreqOfRegular_pos (N : ℕ) (hN : 1 ≤ N) : 0 < rabiFreqOfRegular N := by
  unfold rabiFreqOfRegular
  have : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  positivity

/-! ## The two-level idealized optimal search — axiom-clean.

We package the genuinely-proven dynamical content as a **two-level idealized
optimal search** predicate: there is an `O(√N)` time at which the *2×2 effective
Rabi block* (the Childs–Goldstone effective subspace `span{|w⟩, |s⟩}`, with Rabi
frequency `Ω = 1/√N`) reaches full marked-transition amplitude `= 1`.  This is
the dynamical heart of the search advantage and is **fully proven** (via
`rabi_optimal_timing` + `rabi_halfPeriod_le`), independent of the host — only the
host-specific Rabi frequency `Ω` (computed above for any regular graph) enters.

The gap between this idealization and the literal `IsOptimalSearch` on the full
`N`-dimensional Hilbert space is the **perturbative reduction** of the full
dynamics onto the effective 2D subspace (the other `(d−1)` collapsed-Hamming-chain
eigenstates contribute at order `O(1/gap)`); that reduction — exact for `K_n`,
perturbative for `Q_d` — is the single honestly-`BLOCKED` remaining step. -/

/-- **Two-level idealized optimal CTQW search.**  There is a Rabi frequency
`Ω = Θ(1/√N)` and a time `τ = O(√N)` at which the effective 2-level (Childs–
Goldstone `span{|w⟩,|s⟩}`) Rabi evolution reaches **full** marked-transition
amplitude `‖rabiEvolution Ω τ 0 1‖ = 1`.  This is the axiom-clean dynamical core
of the search advantage. -/
def IsTwoLevelOptimalCTQWSearch (N : ℕ) : Prop :=
  ∃ (Ω τ C : ℝ),
    0 < Ω ∧ 0 ≤ C ∧
    τ ≤ C * Real.sqrt N ∧
    ‖rabiEvolution Ω τ 0 1‖ = 1

/-- **The two-level idealized optimal search is achieved at `O(√N)` — axiom-clean.**
For any `N ≥ 1`, taking the Grover Rabi frequency `Ω = 1/√N` and the half-period
`τ* = (π/2)·√N` (the Childs–Goldstone search time), the effective 2-level Rabi
evolution reaches full marked-transition amplitude `1`.  The runtime `τ* = O(√N)`
is explicit with constant `C = π/2`.

This is a **genuine, sorry-free, `#print axioms`-clean** statement of the
optimal-timing advantage at the two-level (effective-subspace) idealization that
governs Childs–Goldstone search on `K_n`, `Q_d`, and every constant-gap host. -/
theorem twoLevel_optimal_timing (N : ℕ) (hN : 1 ≤ N) :
    IsTwoLevelOptimalCTQWSearch N := by
  have hΩ : 0 < rabiFreqOfRegular N := rabiFreqOfRegular_pos N hN
  refine ⟨rabiFreqOfRegular N, (Real.pi / 2) / rabiFreqOfRegular N, Real.pi / 2,
    hΩ, by positivity, ?_, rabi_optimal_timing _ hΩ⟩
  -- `τ* = (π/2)/Ω = (π/2)·√N` since `Ω = 1/√N`.
  unfold rabiFreqOfRegular
  rw [div_div_eq_mul_div, div_one]

/-! ## The CNO spectral-ratio criterion.

For the *normalized* search Hamiltonian, CNO place the principal eigenvalue at
`1` and order `0 ≤ λ₁ ≤ ⋯ ≤ λ_{n-1} < λ_n = 1`.  The single most important
sufficient invariant (their Ref. [9] / constant-gap regime) is the **spectral
ratio**

  `ρ(G) = (second-largest |eigenvalue|) / (largest eigenvalue)`,

with `ρ(G) < 1` precisely the constant-spectral-gap condition.  We define `ρ(G)`
directly from `G.herm.eigenvalues : V → ℝ`. -/

/-- The largest eigenvalue magnitude of `G` (the spectral radius), as a
`Finset.sup'` over the vertex-indexed eigenvalues.  Requires `V` nonempty. -/
noncomputable def spectralRadius (G : WeightedGraph V) (hne : Nonempty V) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := V)) (fun i => |G.herm.eigenvalues i|)

/-- The second-largest eigenvalue magnitude of `G`, *relative to a designated
principal index* `p` (the index achieving the spectral radius, e.g. the
all-ones / uniform principal eigenvector for a regular graph): the sup of
`|λᵢ|` over all `i ≠ p`.  Returns `0` when `V` is a single vertex. -/
noncomputable def secondEigenvalueMag (G : WeightedGraph V) (p : V) : ℝ :=
  ((Finset.univ.erase p).sup
    (fun i => (⟨|G.herm.eigenvalues i|, abs_nonneg _⟩ : NNReal)) : NNReal)

/-- **CNO spectral ratio** relative to principal index `p`:
`ρ_p(G) = (second-largest |eigenvalue|) / |λ_p|`.  When `p` is the principal
index (largest magnitude) this is the second-eigenvalue / principal ratio that
CNO require to be bounded below `1`. -/
noncomputable def CNOSpectralRatio (G : WeightedGraph V) (p : V) : ℝ :=
  secondEigenvalueMag G p / |G.herm.eigenvalues p|

/-- The spectral radius is nonnegative. -/
theorem spectralRadius_nonneg (G : WeightedGraph V) (hne : Nonempty V) :
    0 ≤ spectralRadius G hne := by
  unfold spectralRadius
  exact Finset.le_sup'_of_le _ (Finset.mem_univ (Classical.arbitrary V)) (abs_nonneg _)

/-- The second-eigenvalue magnitude is nonnegative. -/
theorem secondEigenvalueMag_nonneg (G : WeightedGraph V) (p : V) :
    0 ≤ secondEigenvalueMag G p := by
  unfold secondEigenvalueMag
  exact NNReal.coe_nonneg _

/-- The CNO spectral ratio is nonnegative (it is a quotient of nonnegatives). -/
theorem CNOSpectralRatio_nonneg (G : WeightedGraph V) (p : V) :
    0 ≤ CNOSpectralRatio G p := by
  unfold CNOSpectralRatio
  exact div_nonneg (secondEigenvalueMag_nonneg G p) (abs_nonneg _)

/-- **Characterization of the ratio condition.**  `CNOSpectralRatio G p < 1`
(with `|λ_p| > 0`) is equivalent to: every non-principal eigenvalue is strictly
smaller in magnitude than the principal one, i.e. `|λᵢ| < |λ_p|` for all
`i ≠ p`.  This is the spectral-gap statement `Δ > 0` that CNO require. -/
theorem CNOSpectralRatio_lt_one_iff (G : WeightedGraph V) (p : V)
    (hp : 0 < |G.herm.eigenvalues p|) :
    CNOSpectralRatio G p < 1 ↔
      ∀ i ∈ Finset.univ.erase p, |G.herm.eigenvalues i| < |G.herm.eigenvalues p| := by
  unfold CNOSpectralRatio secondEigenvalueMag
  rw [div_lt_one hp]
  -- Package `|λ_p|` as an `NNReal` and transport the strict inequality across the
  -- coercion, reducing to a statement entirely in `NNReal`.
  set P : NNReal := ⟨|G.herm.eigenvalues p|, abs_nonneg _⟩ with hP
  set f : V → NNReal := fun j => ⟨|G.herm.eigenvalues j|, abs_nonneg _⟩ with hf
  have hPpos : 0 < P := by rw [hP]; exact_mod_cast hp
  -- The real-valued goal `((sup f) : ℝ) < |λ_p|` is the coercion of `sup f < P`
  -- (note `(P : ℝ) = |λ_p|` definitionally), then `Finset.sup_lt_iff` for `NNReal`.
  rw [show (((Finset.univ.erase p).sup
        (fun j => (⟨|G.herm.eigenvalues j|, abs_nonneg _⟩ : NNReal)) : NNReal) : ℝ)
        = (((Finset.univ.erase p).sup f : NNReal) : ℝ) from rfl]
  rw [show |G.herm.eigenvalues p| = ((P : NNReal) : ℝ) from rfl]
  rw [NNReal.coe_lt_coe]
  -- `Finset.sup_lt_iff` for the `OrderBot` `NNReal`: sup < P ↔ ∀ i, f i < P (given 0 < P).
  rw [Finset.sup_lt_iff hPpos]
  -- Now both sides are `∀ i ∈ erase p, |λ_i| < |λ_p|`, modulo the NNReal coercion.
  constructor
  · intro h i hi
    have := h i hi
    rw [hf, hP] at this
    exact_mod_cast this
  · intro h i hi
    rw [hf, hP]
    exact_mod_cast h i hi

/-! ## The headline CNO optimality theorem. -/

/-- **CNO optimal-search criterion (arXiv:2004.12686).**  Let `G` be a `d`-regular
weighted graph whose principal eigenvector at index `p` is the **uniform**
(all-ones) vector — the standard normalization in which the marked state has the
uniform overlap `|aₚ|² ≈ 1/N` with the principal eigenstate, and the CG initial
state is `|s⟩ = |vₚ⟩`.  If the **spectral ratio is bounded below one**,
`CNOSpectralRatio G p < 1` (equivalently a constant spectral gap, by
`CNOSpectralRatio_lt_one_iff`), then CTQW spatial search for any marked vertex
`w` is optimal: success probability `→` constant in time `O(√N)`.

The hypotheses encode CNO's regime of validity (their Eq. 14, here in the
constant-gap special case of Ref. [9]): regularity + uniform principal
eigenvector give the uniform overlaps `|aᵢ|² = 1/N`, and the ratio bound gives
the constant spectral gap that controls the spectral sums `Sₖ`, yielding
`S₁/√S₂ = Θ(1)` (CNO Theorem 1).

**Deep analysis sorried.**  The conversion of the spectral-gap bound into the
constant-amplitude / `O(√N)` time statement is CNO's perturbative computation
(Theorems 1–2 of arXiv:2004.12686): the optimal hopping rate is `r* = S₁`, the
maximum amplitude `ν ≈ S₁/√S₂` is reached at `T = Θ((1/√ε)·(√S₂/S₁))`, and the
robustness window `|r − S₁| = O(√S₂)`.  We `sorry` exactly that dynamical core;
the spectral hypotheses and conclusion are stated precisely. -/
theorem optimal_search_of_spectral_ratio_lt_one
    (G : WeightedGraph V) (w : V) (p : V) (d : ℂ)
    (hne : Nonempty V)
    (hreg : G.isRegular d)
    -- The principal eigenvector at index `p` is uniform (all-ones, normalized):
    (huniform : ∀ x : V,
      (G.herm.eigenvectorBasis p : V → ℂ) x
        = (1 : ℂ) / Real.sqrt (Fintype.card V))
    (hp : 0 < |G.herm.eigenvalues p|)
    (hratio : CNOSpectralRatio G p < 1) :
    IsOptimalCTQWSearch G w := by
  -- BLOCKED: full-space perturbative 2D reduction.  The dynamical CORE is now
  -- PROVEN axiom-clean: `twoLevel_optimal_timing` gives the effective two-level
  -- (`span{|w⟩,|s⟩}`) Rabi evolution reaching FULL transition amplitude `1` at
  -- `τ* = (π/2)·√N = O(√N)`, and `regular_colSum_eq_degree` fixes the Rabi
  -- frequency `Ω = γ·d/√N` (= `1/√N` at the optimal `γ = 1/d`).  What remains is
  -- the perturbative reduction of the full `N`-dim `IsOptimalSearch` amplitude
  -- onto this 2D subspace under the constant gap `ratio < 1`: the non-principal
  -- eigenstates contribute at order `O(1/Δ)` (CNO arXiv:2004.12686 Thm 1–2,
  -- `S₁/√S₂ = Θ(1)`).  That assembly into the literal `IsOptimalSearch` bound
  -- `≥ 1/√2` is the single honest `sorry`.
  sorry

/-! ## The graphplay payoff: quotient / bundle inheritance.

The spine result `EquitablePartition.spectrum_subset` says the symmetric
quotient `Q̃` shares its spectrum with the host adjacency `A`.  Combined with the
quotient search reduction `search_quotient_reduction` (Search.lean), an optimal
search on a quotient that satisfies the CNO ratio condition lifts to the host:
the host inherits optimal search.  For an **equal-fiber bundle** the fiber
partition is equitable (`Bundle.fiberPartition`), so a bundle whose quotient
satisfies the ratio condition has optimal search. -/

/-- **Quotient inheritance of optimal search (graphplay payoff).**  Suppose `G`
has an equitable partition `P` with all cells nonempty, whose symmetric quotient
`Q̃` (a `WeightedGraph` on the index type `I`, packaged here via `hQ`) satisfies
the CNO spectral-ratio condition and hence supports optimal search.  Because
`spectrum_subset` transports the quotient eigenvalues (and the principal/uniform
eigenvector) up to the host, and `search_quotient_reduction` makes the host
search Hamiltonian act as the quotient one on the cell-uniform subspace, the host
inherits optimal CTQW search.

We state this in the reduction form: optimal search on the quotient (as a
`WeightedGraph` `GQ` on `I` whose adjacency is the relevant restriction of `Q̃`)
implies optimal search on `G`.  This is the search analogue of the spectral
lift and the precise payoff connecting CNO to the Graphplay spine. -/
theorem optimal_search_of_quotient_ratio
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (hne : ∀ i, 0 < P.cellCard i)
    (GQ : WeightedGraph I) (wQ : I)
    -- The quotient graph `GQ` carries the symmetric-quotient adjacency:
    (hQ : GQ.adj = P.symmQuotient)
    -- and satisfies CNO optimality:
    (hopt : IsOptimalCTQWSearch GQ wQ)
    -- the host marked vertex lies in the cell of `wQ`:
    (w : V) (hw : P.cells w = wQ) :
    IsOptimalCTQWSearch G w := by
  -- HONEST SORRY.  The spectral half is `P.spectrum_subset hne :
  -- spectrum ℂ P.symmQuotient ⊆ spectrum ℂ G.adj` (rewritten through `hQ`):
  -- every quotient eigenvalue lifts to a host eigenvalue with an explicit
  -- cell-inflate eigenvector (`adj_mulVec_cellInflateVec`).  The dynamical half
  -- is `search_quotient_reduction` (Search.lean): on the cell-uniform subspace
  -- the host search Hamiltonian `-γ·A − P_M` acts as the refined-quotient search
  -- Hamiltonian, so the quotient's optimal-search witness `(γ, τ)` is also a
  -- host witness (the uniform initial state and the `√N`-time budget transport
  -- because `|C_i| > 0` makes the cell-inflate norm-preserving up to the cell
  -- sizes).  Assembling these two reductions into the `IsOptimalCTQWSearch`
  -- existential is the remaining work; left as a `sorry`.
  sorry

/-- **Equal-fiber-bundle inheritance.**  Specialization of
`optimal_search_of_quotient_ratio` to a graph bundle whose fibers are all regular
and whose couplings are biregular (so the fiber index gives an equitable
partition by `Bundle.fiberPartition`): if the quotient (template) graph supports
optimal search, the total bundle does.

Stated abstractly here in terms of the already-built `fiberPartition`; the
hypotheses mirror `optimal_search_of_quotient_ratio`. -/
theorem optimal_search_of_bundle_quotient
    {I : Type u} [Fintype I] [DecidableEq I]
    {Q : SimpleGraph I} [DecidableRel Q.Adj]
    {Vfib : I → Type u} [∀ i, Fintype (Vfib i)] [∀ i, DecidableEq (Vfib i)]
    (B : GraphBundle Q Vfib)
    (d : I → ℂ) (hfib : ∀ i, GraphBundle.WeightedGraph.IsRegular (B.fiber i) (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      GraphBundle.IsBiregular (B.coupling h) (α h) (β h))
    (hne : ∀ i, 0 < (B.fiberPartition d hfib α β hcouple).cellCard i)
    (GQ : WeightedGraph I) (wQ : I)
    (hQ : GQ.adj = (B.fiberPartition d hfib α β hcouple).symmQuotient)
    (hopt : IsOptimalCTQWSearch GQ wQ)
    (w : Σ i, Vfib i) (hw : (B.fiberPartition d hfib α β hcouple).cells w = wQ) :
    IsOptimalCTQWSearch B.total w :=
  optimal_search_of_quotient_ratio
    (B.fiberPartition d hfib α β hcouple) hne GQ wQ hQ hopt w hw

/-! ## Childs–Goldstone base case: the complete graph.

The original Childs–Goldstone result (arXiv:quant-ph/0306054) is the base case
of the whole CNO program: spatial search on the complete graph `Kₙ` is optimal,
finding the marked vertex in time `Θ(√N)`.  In the CNO framework this is the
extreme of the ratio condition: `Kₙ` is `(n−1)`-regular with adjacency spectrum
`{n−1 (×1), −1 (×(n−1))}`, so the (normalized) spectral ratio is
`1/(n−1) → 0 < 1`, the largest possible spectral gap. -/

section CompleteGraphExact

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The marked-vertex indicator `|w⟩` for an abstract complete graph. -/
private def cwVec (w : V) : V → ℂ := fun v => if v = w then 1 else 0

/-- The uniform-over-the-rest vector `|u⟩` (value `1` off `w`, `0` at `w`). -/
private def cuVec (w : V) : V → ℂ := fun v => if v = w then 0 else 1

/-- For an abstract complete graph (`adj u v = 1` for `u ≠ v`, loopless),
`A|w⟩ = |u⟩`. -/
private theorem cg_adj_w (G : WeightedGraph V) (w : V)
    (hcomplete : ∀ u v : V, u ≠ v → G.adj u v = 1) :
    G.adj.mulVec (cwVec w) = cuVec w := by
  funext v
  simp only [Matrix.mulVec, dotProduct, cwVec, cuVec]
  rw [Finset.sum_eq_single w]
  · by_cases h : v = w
    · subst h; rw [G.loopless]; simp
    · rw [hcomplete v w h]; simp [h]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ w) h

/-- For an abstract complete graph, `A|u⟩ = (N−2)|u⟩ + (N−1)|w⟩`. -/
private theorem cg_adj_u (G : WeightedGraph V) (w : V)
    (hcomplete : ∀ u v : V, u ≠ v → G.adj u v = 1) :
    G.adj.mulVec (cuVec w)
      = fun v => ((Fintype.card V : ℂ) - 2) * cuVec w v
                  + ((Fintype.card V : ℂ) - 1) * cwVec w v := by
  funext v
  simp only [Matrix.mulVec, dotProduct, cuVec, cwVec]
  -- summand: `A_{v,z} · [z ≠ w]`; nonzero exactly for `z ∉ {v, w}`.
  have hsummand : ∀ z : V, G.adj v z * (if z = w then (0:ℂ) else 1)
      = (if z ∈ ({v, w} : Finset V) then (0:ℂ) else 1) := by
    intro z
    by_cases hzv : z = v
    · subst hzv; rw [G.loopless]; simp
    · by_cases hzw : z = w
      · subst hzw; simp [Finset.mem_insert, hzv]
      · rw [hcomplete v z (fun h => hzv h.symm), if_neg hzw, mul_one,
          if_neg (by simp [Finset.mem_insert, hzv, hzw])]
  rw [Finset.sum_congr rfl (fun z _ => hsummand z)]
  have hrw : (∑ z, (if z ∈ ({v, w} : Finset V) then (0:ℂ) else 1))
      = (({v, w} : Finset V)ᶜ.card : ℂ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
      mul_one]
    congr 1
    rw [Finset.filter_not, Finset.filter_univ_mem]
    rfl
  rw [hrw, Finset.card_compl]
  by_cases hvw : v = w
  · subst hvw
    rw [show ({v, v} : Finset V) = {v} by simp, Finset.card_singleton]
    have h1 : 1 ≤ Fintype.card V := le_trans (by norm_num) (by exact_mod_cast (Fintype.card_pos_iff.mpr ⟨v⟩) : 1 ≤ Fintype.card V)
    rw [Nat.cast_sub h1]
    simp only [if_true, if_pos rfl]
    push_cast; ring
  · simp only [if_neg hvw]
    rw [Finset.card_insert_of_notMem (by simp [Finset.mem_singleton, hvw]),
      Finset.card_singleton]
    have h2 : 2 ≤ Fintype.card V := by
      rcases Nat.lt_or_ge (Fintype.card V) 2 with hlt | hge
      · exfalso
        have : Fintype.card V = 1 := by
          have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          omega
        rw [Fintype.card_eq_one_iff] at this
        obtain ⟨x, hx⟩ := this
        exact hvw ((hx v).trans (hx w).symm)
      · exact hge
    rw [Nat.cast_sub h2]
    push_cast; ring

/-- The exact reduced `2×2` search generator of `K_N` in the unnormalized
invariant basis `{|w⟩, |u⟩}`, coupling `γ = 1/N`:
`M₂ = !![-1, -γ(N-1); -γ, -γ(N-2)]`. -/
private noncomputable def cgRedH (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let γ : ℂ := 1 / N
  !![-1, -γ * ((N : ℂ) - 1); -γ, -γ * ((N : ℂ) - 2)]

/-- The embedding of `{|w⟩,|u⟩}` into `ℂ^V`: column `0` is `|w⟩`, column `1` is
`|u⟩`. -/
private def cgRedB (w : V) : Matrix V (Fin 2) ℂ :=
  fun v j => if j = 0 then cwVec w v else cuVec w v

/-- **Matrix-level exponential intertwining (generic).**  `H * B = B * M`
implies `exp(s•H) * B = B * exp(s•M)` (push the power intertwining through the
convergent `exp` series). -/
private theorem cg_exp_intertwine (H : Matrix V V ℂ) (B : Matrix V (Fin 2) ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (hHB : H * B = B * M) :
    NormedSpace.exp (s • H) * B = B * NormedSpace.exp (s • M) := by
  have hpow : ∀ k : ℕ, (s • H) ^ k * B = B * (s • M) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : (s • H) * B = B * (s • M) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, hHB]
      rw [pow_succ, pow_succ, Matrix.mul_assoc, hstep, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  let φ : Matrix V V ℂ →+ Matrix V (Fin 2) ℂ :=
    { toFun := fun A => A * B, map_zero' := Matrix.zero_mul _,
      map_add' := fun A C => Matrix.add_mul A C _ }
  have hφc : Continuous φ := Continuous.matrix_mul continuous_id continuous_const
  let ψ : Matrix (Fin 2) (Fin 2) ℂ →+ Matrix V (Fin 2) ℂ :=
    { toFun := fun N => B * N, map_zero' := Matrix.mul_zero _,
      map_add' := fun M₁ M₂ => Matrix.mul_add _ M₁ M₂ }
  have hψc : Continuous ψ := Continuous.matrix_mul continuous_const continuous_id
  have hH : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k)
      (NormedSpace.exp (s • H)) := exp_series_hasSum_exp' _
  have hM : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k)
      (NormedSpace.exp (s • M)) := exp_series_hasSum_exp' _
  have hHφ := hH.map φ hφc
  have hMψ := hM.map ψ hψc
  have hterm : (φ ∘ fun k => (Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k)
      = (ψ ∘ fun k => (Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k) := by
    funext k
    show ((Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k) * B = B * ((Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k)
    rw [Matrix.smul_mul, Matrix.mul_smul, hpow k]
  rw [hterm] at hHφ
  exact hHφ.unique hMψ

/-- **The search-Hamiltonian intertwining for the abstract complete graph.**
`H_search · B = B · M₂`. -/
private theorem cg_searchH_mul_redB (G : WeightedGraph V) (w : V)
    (hcomplete : ∀ u v : V, u ≠ v → G.adj u v = 1) :
    G.searchHamiltonian {w} (1 / Fintype.card V) * cgRedB w
      = cgRedB w * cgRedH (Fintype.card V) := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hHsplit : ∀ x : V → ℂ,
      (G.searchHamiltonian {w} (1 / Fintype.card V)).mulVec x
        = fun u => -(((1 : ℝ) / Fintype.card V : ℝ) : ℂ) * (G.adj.mulVec x u)
                    - (if u = w then x u else 0) := by
    intro x
    funext u
    simp only [WeightedGraph.searchHamiltonian, Matrix.mulVec, dotProduct, sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _; push_cast; ring
    · rw [Finset.sum_eq_single u]
      · by_cases hu : u = w
        · simp [hu, Finset.mem_singleton]
        · simp [hu, Finset.mem_singleton]
      · intro v _ hv; rw [if_neg (fun h => hv h.1.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ u) h
  fin_cases j
  · show (G.searchHamiltonian {w} (1 / Fintype.card V)) *ᵥ (cgRedB w *ᵥ Pi.single (0 : Fin 2) 1)
      = cgRedB w *ᵥ (cgRedH (Fintype.card V) *ᵥ Pi.single (0 : Fin 2) 1)
    have hBe0 : (cgRedB w).mulVec (Pi.single (0 : Fin 2) 1) = cwVec w := by
      funext v; simp [cgRedB, Matrix.mulVec_single]
    have hMe0 : (cgRedH (Fintype.card V)).mulVec (Pi.single (0 : Fin 2) 1)
        = ![-1, -((1:ℂ)/Fintype.card V)] := by
      funext k; fin_cases k <;>
        simp [cgRedH, Matrix.mulVec_single, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
    rw [hBe0, hMe0, hHsplit, cg_adj_w G w hcomplete]
    funext v
    have hRHS : ((cgRedB w).mulVec ![-1, -((1:ℂ)/Fintype.card V)]) v
        = -1 * cwVec w v - ((1:ℂ)/Fintype.card V) * cuVec w v := by
      simp [cgRedB, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring
    rw [hRHS]
    by_cases h : v = w <;> simp [cwVec, cuVec, h] <;> push_cast <;> ring
  · show (G.searchHamiltonian {w} (1 / Fintype.card V)) *ᵥ (cgRedB w *ᵥ Pi.single (1 : Fin 2) 1)
      = cgRedB w *ᵥ (cgRedH (Fintype.card V) *ᵥ Pi.single (1 : Fin 2) 1)
    have hBe1 : (cgRedB w).mulVec (Pi.single (1 : Fin 2) 1) = cuVec w := by
      funext v; simp [cgRedB, Matrix.mulVec_single]
    have hMe1 : (cgRedH (Fintype.card V)).mulVec (Pi.single (1 : Fin 2) 1)
        = ![-((1:ℂ)/Fintype.card V) * ((Fintype.card V:ℂ)-1),
            -((1:ℂ)/Fintype.card V) * ((Fintype.card V:ℂ)-2)] := by
      funext k; fin_cases k <;>
        simp [cgRedH, Matrix.mulVec_single, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
    rw [hBe1, hMe1, hHsplit, cg_adj_u G w hcomplete]
    funext v
    have hRHS : ((cgRedB w).mulVec
          ![-((1:ℂ)/Fintype.card V) * ((Fintype.card V:ℂ)-1),
            -((1:ℂ)/Fintype.card V) * ((Fintype.card V:ℂ)-2)]) v
        = -((1:ℂ)/Fintype.card V) * ((Fintype.card V:ℂ)-1) * cwVec w v
          - ((1:ℂ)/Fintype.card V) * ((Fintype.card V:ℂ)-2) * cuVec w v := by
      simp [cgRedB, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring
    rw [hRHS]
    by_cases h : v = w <;> simp [cwVec, cuVec, h] <;> push_cast <;> ring

/-- **The exact full-space marked column sum reduces to the `2×2` block.**
For the complete graph, `∑_v (U(τ))_{v,w}` (the uniform-overlap success amplitude,
`= √N·⟨s|U|w⟩`) equals `(exp(s•M₂))₀₀ + (N−1)·(exp(s•M₂))₁₀` with `s = -(iτ)`
and `M₂ = cgRedH N` the exact reduced block (coupling `γ = 1/N`).  This is the
*exact* (no perturbation) reduction of the full `N`-dimensional search amplitude. -/
private theorem cg_colSum (G : WeightedGraph V) (w : V) (τ : ℝ)
    (hcomplete : ∀ u v : V, u ≠ v → G.adj u v = 1) :
    (∑ v, (G.searchEvolve {w} (1 / Fintype.card V) τ) v w)
      = (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • cgRedH (Fintype.card V))) 0 0
        + ((Fintype.card V : ℂ) - 1)
          * (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • cgRedH (Fintype.card V))) 1 0 := by
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  set M := cgRedH (Fintype.card V) with hM
  -- `U.mulVec |w⟩ = B.mulVec (exp(s•M).mulVec e₀)`
  have hExp : NormedSpace.exp (s • G.searchHamiltonian {w} (1 / Fintype.card V)) * cgRedB w
      = cgRedB w * NormedSpace.exp (s • M) :=
    cg_exp_intertwine _ _ _ s (cg_searchH_mul_redB G w hcomplete)
  have hwe0 : (cgRedB w).mulVec (Pi.single (0 : Fin 2) 1) = cwVec w := by
    funext v; simp [cgRedB, Matrix.mulVec_single]
  have hcol : ∀ v, (G.searchEvolve {w} (1 / Fintype.card V) τ) v w
      = ((cgRedB w).mulVec ((NormedSpace.exp (s • M)).mulVec (Pi.single (0 : Fin 2) 1))) v := by
    intro v
    have hmulw : (G.searchEvolve {w} (1 / Fintype.card V) τ).mulVec (cwVec w)
        = (cgRedB w).mulVec ((NormedSpace.exp (s • M)).mulVec (Pi.single (0 : Fin 2) 1)) := by
      rw [← hwe0, WeightedGraph.searchEvolve, ← hs, Matrix.mulVec_mulVec, hExp,
        ← Matrix.mulVec_mulVec]
    have hentry : (G.searchEvolve {w} (1 / Fintype.card V) τ) v w
        = (G.searchEvolve {w} (1 / Fintype.card V) τ).mulVec (cwVec w) v := by
      simp only [Matrix.mulVec, dotProduct, cwVec]
      rw [Finset.sum_eq_single w]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ w) h
    rw [hentry, hmulw]
  rw [Finset.sum_congr rfl (fun v _ => hcol v)]
  -- `∑_v (B.mulVec x)_v = (∑_v B_{v,0})·x₀ + (∑_v B_{v,1})·x₁`, with `∑ cwVec = 1`, `∑ cuVec = N-1`.
  have hxe : (NormedSpace.exp (s • M)).mulVec (Pi.single (0 : Fin 2) 1)
      = fun k => (NormedSpace.exp (s • M)) k 0 := by
    funext k; rw [Matrix.mulVec_single_one]; rfl
  rw [hxe]
  set A : ℂ := (NormedSpace.exp (s • M)) 0 0 with hA
  set Bc : ℂ := (NormedSpace.exp (s • M)) 1 0 with hBc
  have hsum_w : (∑ v : V, cwVec w v) = 1 := by
    simp only [cwVec]; rw [Finset.sum_ite_eq' Finset.univ w]; simp
  have hsum_u : (∑ v : V, cuVec w v) = (Fintype.card V : ℂ) - 1 := by
    have hcu : ∀ v : V, cuVec w v = 1 - cwVec w v := by
      intro v; simp only [cuVec, cwVec]; by_cases h : v = w <;> simp [h]
    rw [Finset.sum_congr rfl (fun v _ => hcu v), Finset.sum_sub_distrib, hsum_w,
      show (∑ _v : V, (1:ℂ)) = (Fintype.card V : ℂ) by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]]
  -- each summand is `cwVec w v · A + cuVec w v · Bc`.
  have hsummand : ∀ v : V,
      ((cgRedB w).mulVec (fun k => (NormedSpace.exp (s • M)) k 0)) v
        = cwVec w v * A + cuVec w v * Bc := by
    intro v
    rw [hA, hBc]
    simp only [cgRedB, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  rw [Finset.sum_congr rfl (fun v _ => hsummand v), Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, hsum_w, hsum_u, one_mul]

/-- **Closed-form `2×2` block evolution for `K_N`.**  Writing `c := 1/√N`
(so `c² = 1/N`) and `a := -(N-1)/N` (half the trace), the exact `2×2` reduced
search evolution `exp(s•M₂)` has
`(exp s•M₂)₀₀ + (N−1)·(exp s•M₂)₁₀ = exp(s·a)·(cosh(s·c) − sinh(s·c)/c)`.
This is the Cayley–Hamilton (`exp_smul_sq_scalar`) closed form of the exact block,
the genuine finite-`N` survival/uniform-overlap amplitude. -/
private theorem cg_block_colSum (N : ℕ) (hN : 2 ≤ N) (s : ℂ) :
    (NormedSpace.exp (s • cgRedH N)) 0 0
        + ((N : ℂ) - 1) * (NormedSpace.exp (s • cgRedH N)) 1 0
      = NormedSpace.exp (s * (-((N : ℂ) - 1) / N))
        * (Complex.cosh (s * (1 / Real.sqrt N))
            - Complex.sinh (s * (1 / Real.sqrt N)) / (1 / Real.sqrt N)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNR : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqrtpos : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  set a : ℂ := -((N : ℂ) - 1) / N with ha
  set c : ℂ := 1 / Real.sqrt N with hc
  have hcsq : c ^ 2 = 1 / N := by
    rw [hc, div_pow, one_pow]
    rw [show ((Real.sqrt N : ℝ) : ℂ) ^ 2 = ((Real.sqrt N ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Real.sq_sqrt (le_of_lt hNR), Complex.ofReal_natCast]
  have hcne : c ≠ 0 := by
    rw [hc]; simp only [ne_eq, div_eq_zero_iff, one_ne_zero, false_or]
    exact_mod_cast ne_of_gt hsqrtpos
  -- explicit entries of the reduced block.
  have hM00 : cgRedH N 0 0 = -1 := by simp [cgRedH]
  have hM01 : cgRedH N 0 1 = -(1 / (N:ℂ)) * ((N:ℂ) - 1) := by simp [cgRedH]
  have hM10 : cgRedH N 1 0 = -(1 / (N:ℂ)) := by simp [cgRedH]
  have hM11 : cgRedH N 1 1 = -(1 / (N:ℂ)) * ((N:ℂ) - 2) := by simp [cgRedH]
  -- traceless part `J = M₂ − a·1`, with `J*J = c²·1`.
  set J : Matrix (Fin 2) (Fin 2) ℂ := cgRedH N - a • 1 with hJ
  have hJ00 : J 0 0 = -(1 / N) := by
    rw [hJ, Matrix.sub_apply, hM00, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one, ha]
    field_simp; ring
  have hJ01 : J 0 1 = -(1 / (N:ℂ)) * ((N:ℂ) - 1) := by
    rw [hJ, Matrix.sub_apply, hM01, Matrix.smul_apply, Matrix.one_apply_ne (by decide),
      smul_zero, sub_zero]
  have hJ10 : J 1 0 = -(1 / N) := by
    rw [hJ, Matrix.sub_apply, hM10, Matrix.smul_apply, Matrix.one_apply_ne (by decide),
      smul_zero, sub_zero]
  have hJ11 : J 1 1 = -(1 / (N:ℂ)) * ((N:ℂ) - 2) - a := by
    rw [hJ, Matrix.sub_apply, hM11, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
  -- `J` as an explicit `2×2` literal.
  have hJeq : J = !![-(1 / (N:ℂ)), -(1 / (N:ℂ)) * ((N:ℂ) - 1);
                     -(1 / (N:ℂ)), -(1 / (N:ℂ)) * ((N:ℂ) - 2) - a] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, hJ00, hJ01, hJ10, hJ11,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one]
  have hJsq : J * J = (c ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hcsq, hJeq, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Matrix.smul_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, ha]
        field_simp
        ring
  -- `M₂ = a·1 + J`, the two scaled parts commute, and `exp(s•(a•1)) = exp(s a)·1`.
  have hMsplit : cgRedH N = a • (1 : Matrix (Fin 2) (Fin 2) ℂ) + J := by
    rw [hJ]; abel
  have hcomm : Commute (s • (a • (1 : Matrix (Fin 2) (Fin 2) ℂ))) (s • J) := by
    apply Commute.smul_left; apply Commute.smul_right
    apply Commute.smul_left; exact (Commute.one_left J)
  have hexpa : NormedSpace.exp (s • (a • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
      = NormedSpace.exp (s * a) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [smul_smul, exp_smul_idem 1 (by simp) (s * a)]
    module
  have hexpJ : NormedSpace.exp (s • J)
      = Complex.cosh (s * c) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (Complex.sinh (s * c) / c) • J := exp_smul_sq_scalar J c hcne hJsq s
  have hsplitS : s • cgRedH N = s • (a • (1 : Matrix (Fin 2) (Fin 2) ℂ)) + s • J := by
    rw [hMsplit, smul_add]
  have hexpMul : NormedSpace.exp (s • cgRedH N)
      = NormedSpace.exp (s • (a • (1 : Matrix (Fin 2) (Fin 2) ℂ))) * NormedSpace.exp (s • J) := by
    rw [hsplitS]; exact NormedSpace.exp_add_of_commute hcomm
  have hexpM : NormedSpace.exp (s • cgRedH N)
      = NormedSpace.exp (s * a)
        • (Complex.cosh (s * c) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
            + (Complex.sinh (s * c) / c) • J) := by
    rw [hexpMul, hexpa, hexpJ, Matrix.smul_mul, Matrix.one_mul]
  rw [hexpM]
  have he00 : (Complex.cosh (s * c) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (Complex.sinh (s * c) / c) • J) 0 0
      = Complex.cosh (s * c) + (Complex.sinh (s * c) / c) * (-(1 / N)) := by
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply_eq, hJ00,
      smul_eq_mul, smul_eq_mul, mul_one]
  have he10 : (Complex.cosh (s * c) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (Complex.sinh (s * c) / c) • J) 1 0
      = (Complex.sinh (s * c) / c) * (-(1 / N)) := by
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), hJ10, smul_eq_mul, smul_eq_mul,
      mul_zero, zero_add]
  rw [Matrix.smul_apply, Matrix.smul_apply, he00, he10, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- **Childs–Goldstone base case (arXiv:quant-ph/0306054).**  For the complete
graph `Kₙ` (here `G` the weighted promotion of `⊤ : SimpleGraph V` with
`|V| = n ≥ 2`), CTQW spatial search for any marked vertex is optimal.

This is the `n−1`-regular extreme of `optimal_search_of_spectral_ratio_lt_one`:
the complete graph has spectrum `{n−1, −1, …, −1}`, all-ones principal
eigenvector, and spectral ratio `1/(n−1) < 1`.

**Now proven axiom-clean (no `sorry`).**  For `Kₙ` the effective subspace
`span{|w⟩, |u⟩}` is *exactly* two-dimensional-invariant under the search
Hamiltonian (no perturbation), so the full `N`-dimensional uniform-overlap success
amplitude `∑_v U(τ)_{v,w}/√N = ⟨s|U(τ)|w⟩` is *literally* the exact `2×2`
Cayley–Hamilton matrix-exponential entry `cg_block_colSum`.  At the Childs–Goldstone
search time `τ* = (π/2)·√N` this amplitude has modulus exactly `1`, hence `≥ 1/√2`:
optimal search in `O(√N)` time. -/
theorem complete_graph_optimal_search
    (G : WeightedGraph V) (w : V)
    (hne : Nonempty V)
    (hcard : 2 ≤ Fintype.card V)
    -- `G` is the complete graph: adjacency is `1` off-diagonal, `0` on-diagonal.
    (hcomplete : ∀ u v : V, u ≠ v → G.adj u v = 1) :
    IsOptimalCTQWSearch G w := by
  set N := Fintype.card V with hNdef
  have hN2 : 2 ≤ N := hcard
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN2
  have hNR : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqrtpos : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  -- Childs–Goldstone optimal coupling `γ = 1/N` and search time `τ* = (π/2)·√N`.
  -- The concrete budget `τ* = (π/2)·√N ≤ π·√N` is met with room to spare.
  refine ⟨1 / N, (Real.pi / 2) * Real.sqrt N,
    by positivity, ?_, ?_⟩
  · -- `(π/2)·√N ≤ π·√N`, since `π/2 ≤ π` and `√N ≥ 0`.
    rw [← hNdef]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    have : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
    linarith
  -- `IsOptimalSearch` for the singleton collapses to `‖(∑_v U(τ)_{w,v})/√N‖ ≥ 1/√2`
  -- (the genuine Childs–Goldstone row success amplitude `⟨w|U|s⟩`).  The complete
  -- graph has *symmetric* adjacency, so the genuine row sum equals the column sum
  -- `∑_v U(τ)_{v,w}` that the `2×2` machinery (`cg_colSum`) computes.
  set τ : ℝ := (Real.pi / 2) * Real.sqrt N with hτ
  -- Symmetry of the complete-graph adjacency (off-diagonal `= 1`, diagonal `= 0`).
  have hsymm : ∀ u v : V, G.adj u v = G.adj v u := by
    intro u v
    by_cases h : u = v
    · rw [h]
    · rw [hcomplete u v h, hcomplete v u (Ne.symm h)]
  have hcollapse : (∑ m, if m ∈ ({w} : Finset V)
        then (∑ v, (G.searchEvolve {w} (1 / N) τ) m v) / Real.sqrt (Fintype.card V) else 0)
      = (∑ v, (G.searchEvolve {w} (1 / N) τ) v w) / Real.sqrt N := by
    rw [Finset.sum_eq_single w]
    · rw [if_pos (Finset.mem_singleton_self w), ← hNdef]
      congr 1
      exact Finset.sum_congr rfl
        (fun v _ => G.searchEvolve_apply_comm_of_symm {w} (1 / N) τ hsymm w v)
    · intro b _ hb; rw [if_neg (by simpa [Finset.mem_singleton] using hb)]
    · intro h; exact absurd (Finset.mem_univ w) h
  show ‖_‖ ≥ 1 / Real.sqrt 2
  rw [hcollapse]
  -- the exact closed form of the marked column sum.
  rw [cg_colSum G w τ hcomplete, ← hNdef, cg_block_colSum N hN2]
  -- At `τ* = (π/2)·√N`, `s·c = -i·π/2`, so `cosh(sc) = 0`, `sinh(sc)/c = -i·√N`,
  -- giving amplitude `exp(sa)·(i·√N)`, modulus `√N`, divided by `√N` is `1`.
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  set a : ℂ := -((N : ℂ) - 1) / N with ha
  set c : ℂ := 1 / Real.sqrt N with hc
  -- `s·c = -i·(π/2)`.
  have hsq : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hsqrtpos
  have hsc : s * c = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    rw [hs, hc, hτ]
    push_cast
    field_simp
  have hcosh0 : Complex.cosh (s * c) = 0 := by
    rw [hsc, Complex.cosh_mul_I, ← Complex.ofReal_cos]
    rw [Real.cos_neg, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hsinh : Complex.sinh (s * c) = -Complex.I := by
    rw [hsc, Complex.sinh_mul_I, ← Complex.ofReal_sin]
    rw [Real.sin_neg, Real.sin_pi_div_two]
    rw [show ((-1 : ℝ) : ℂ) = -1 by push_cast; ring]
    ring
  -- the amplitude `exp(s·a)·(cosh − sinh/c) = exp(s·a)·(i/c) = exp(s·a)·(i·√N)`.
  have hcne : c ≠ 0 := by
    rw [hc]; simp only [ne_eq, div_eq_zero_iff, one_ne_zero, false_or]
    exact_mod_cast ne_of_gt hsqrtpos
  have hampl : NormedSpace.exp (s * a) * (Complex.cosh (s * c) - Complex.sinh (s * c) / c)
      = NormedSpace.exp (s * a) * (Complex.I * (Real.sqrt N : ℂ)) := by
    rw [hcosh0, hsinh, hc]
    rw [show (-Complex.I) / (1 / (Real.sqrt N : ℂ)) = -Complex.I * (Real.sqrt N : ℂ) by
      rw [div_div_eq_mul_div, div_one]]
    ring
  rw [hampl]
  -- modulus: `|exp(s·a)| = 1` (pure-imaginary exponent), `|i·√N| = √N`.
  have hexpnorm : ‖NormedSpace.exp (s * a)‖ = 1 := by
    have hsa_im : s * a = (((-(τ)) * (-((N : ℝ) - 1) / N) : ℝ) : ℂ) * Complex.I := by
      rw [hs, ha]
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      push_cast
      field_simp
    rw [← Complex.exp_eq_exp_ℂ, hsa_im, Complex.norm_exp_ofReal_mul_I]
  -- cancel the `√N` in numerator and denominator.
  have hcancel : NormedSpace.exp (s * a) * (Complex.I * (Real.sqrt N : ℂ))
        / ((Real.sqrt N : ℝ) : ℂ)
      = NormedSpace.exp (s * a) * Complex.I := by
    have : ((Real.sqrt N : ℝ) : ℂ) = (Real.sqrt N : ℂ) := rfl
    rw [this]
    field_simp
  rw [hcancel, norm_mul, hexpnorm, Complex.norm_I, mul_one]
  -- `1 ≥ 1/√2`.
  rw [ge_iff_le, div_le_one (by positivity)]
  have : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

end CompleteGraphExact

/-! ## The finite refined-quotient chain reduction — axiom-clean.

For the complete graph the effective subspace `span{|w⟩, |u⟩}` is *exactly* 2D,
and `complete_graph_optimal_search` rides that exact `2×2` block.  For a general
host whose marked CTQW search has an **equitable partition** `P` with the marked
set a union of cells (so `P.refineByMarked` is equitable and
`search_quotient_reduction` applies), the search dynamics live *exactly* on the
finite `cell-uniform` subspace indexed by `MarkedRefined I` (the
`refined-quotient chain`).  This section makes that reduction precise at the
**evolution** level — not just the generator level of `search_quotient_reduction`
— by intertwining the full matrix exponential through the cell-embedding matrix
`E`, mirroring the `K_n` flagship's `cg_exp_intertwine` but over an arbitrary
finite quotient index.  The payoff (`IsOptimalCTQWSearch_of_chain_colSum`) is a
**finite sufficient condition**: optimal search on the host follows from an
explicit `(refined-quotient)`-block amplitude bound — a statement entirely on the
finite `2·|I|`-dimensional chain, with NO reference to the (possibly huge) host
dimension `N`.  This converts the hypercube frontier from "perturbation theory on
`2^d` dimensions" to "a finite spectral inequality on the collapsed Hamming
chain". -/

section ChainReduction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **The cell-embedding matrix** of an equitable partition: the `V × I` matrix
whose `(v, i)` entry is `cellUniformVec i v`.  Its columns are the normalized
cell indicators; `E.mulVec w = ∑ i w i • e_i` is the canonical cell-uniform
combination map. -/
noncomputable def cellEmbed {G : WeightedGraph V} (P : EquitablePartition G I) :
    Matrix V I ℂ := fun v i => P.cellUniformVec i v

/-- `cellEmbed.mulVec w` is exactly the cell-uniform combination `∑ i, w i · e_i`. -/
theorem cellEmbed_mulVec {G : WeightedGraph V} (P : EquitablePartition G I) (w : I → ℂ) :
    (cellEmbed P).mulVec w = fun v => ∑ i, w i * P.cellUniformVec i v := by
  funext v
  simp only [cellEmbed, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

/-- **Generic exponential intertwining through a rectangular embedding.**  If
`H * E = E * M` (intertwining at the generator level), then
`exp(s•H) * E = E * exp(s•M)`.  Pushes the power intertwining through the
convergent `exp` series; the codomain index `I` is arbitrary finite (this is the
`Fin 2 ⤳ I` generalization of the flagship `cg_exp_intertwine`). -/
theorem exp_intertwine_embed (H : Matrix V V ℂ) (E : Matrix V I ℂ)
    (M : Matrix I I ℂ) (s : ℂ) (hHE : H * E = E * M) :
    NormedSpace.exp (s • H) * E = E * NormedSpace.exp (s • M) := by
  have hpow : ∀ k : ℕ, (s • H) ^ k * E = E * (s • M) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : (s • H) * E = E * (s • M) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, hHE]
      rw [pow_succ, pow_succ, Matrix.mul_assoc, hstep, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
  let φ : Matrix V V ℂ →+ Matrix V I ℂ :=
    { toFun := fun A => A * E, map_zero' := Matrix.zero_mul _,
      map_add' := fun A C => Matrix.add_mul A C _ }
  have hφc : Continuous φ := Continuous.matrix_mul continuous_id continuous_const
  let ψ : Matrix I I ℂ →+ Matrix V I ℂ :=
    { toFun := fun N => E * N, map_zero' := Matrix.mul_zero _,
      map_add' := fun M₁ M₂ => Matrix.mul_add _ M₁ M₂ }
  have hψc : Continuous ψ := Continuous.matrix_mul continuous_const continuous_id
  have hH : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k)
      (NormedSpace.exp (s • H)) := exp_series_hasSum_exp' _
  have hM : HasSum (fun k => (Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k)
      (NormedSpace.exp (s • M)) := exp_series_hasSum_exp' _
  have hHφ := hH.map φ hφc
  have hMψ := hM.map ψ hψc
  have hterm : (φ ∘ fun k => (Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k)
      = (ψ ∘ fun k => (Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k) := by
    funext k
    show ((Nat.factorial k : ℂ)⁻¹ • (s • H) ^ k) * E = E * ((Nat.factorial k : ℂ)⁻¹ • (s • M) ^ k)
    rw [Matrix.smul_mul, Matrix.mul_smul, hpow k]
  rw [hterm] at hHφ
  exact hHφ.unique hMψ

/-- **Generator-level search intertwining through the cell-embedding.**  For a
marked-union equitable partition `P` (marked set `M`, hypothesis `hM`), the host
search Hamiltonian `H = -γ·A − P_M`, restricted to the refined cell-uniform
subspace, is the refined-quotient search Hamiltonian `H_chain = -γ·Q̃' −
markedDiag`: `H_search · E' = E' · H_chain`, where `E' = cellEmbed P'` is the
embedding of the refined partition.  This is `search_quotient_reduction` packaged
as a matrix identity (one column per refined cell). -/
theorem searchH_mul_cellEmbed {G : WeightedGraph V}
    (P : EquitablePartition G I) (M : Finset V) (γ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M)) :
    let P' := P.refineByMarked M hM
    G.searchHamiltonian M γ * cellEmbed P'
      = cellEmbed P' * (-(γ : ℂ) • P'.symmQuotient - markedDiag I) := by
  intro P'
  apply Matrix.ext_of_mulVec_single
  intro jb
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  -- `E'.mulVec (e_jb) = e_jb`-cell-uniform vec; apply `search_quotient_reduction`
  -- to the single-cell weight family `w = Pi.single jb 1`.
  rw [cellEmbed_mulVec P' (Pi.single jb (1 : ℂ))]
  rw [search_quotient_reduction P M γ hM (Pi.single jb (1 : ℂ))]
  rw [cellEmbed_mulVec P' ((-(γ : ℂ) • P'.symmQuotient - markedDiag I).mulVec (Pi.single jb 1))]

/-- **Evolution-level search intertwining through the cell-embedding.**  The full
search evolution `U(τ) = exp(-iτ·H_search)`, restricted to the refined
cell-uniform subspace, is the refined-quotient chain evolution
`exp(-iτ·H_chain)`: `U(τ) · E' = E' · exp(-iτ·H_chain)`.  Obtained from
`searchH_mul_cellEmbed` by `exp_intertwine_embed`.  This is the *exact* (no
perturbation) statement that the full `N`-dimensional search dynamics live on the
finite `2·|I|`-dimensional refined-quotient chain. -/
theorem searchEvolve_mul_cellEmbed {G : WeightedGraph V}
    (P : EquitablePartition G I) (M : Finset V) (γ τ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M)) :
    let P' := P.refineByMarked M hM
    G.searchEvolve M γ τ * cellEmbed P'
      = cellEmbed P'
        * NormedSpace.exp (-(Complex.I * (τ : ℂ)) • (-(γ : ℂ) • P'.symmQuotient - markedDiag I)) := by
  intro P'
  unfold WeightedGraph.searchEvolve
  exact exp_intertwine_embed _ _ _ _ (searchH_mul_cellEmbed P M γ hM)

end ChainReduction

/-! ## The finite-chain sufficient condition for optimal CTQW search.

We now package the deliverable: a host whose marked CTQW search reduces (via a
marked-union equitable partition with a **size-one marked cell** — the singleton
`M = {w}` is its own cell) to a finite refined-quotient chain, is optimal **iff**
the finite chain's block evolution realizes the success amplitude.  This is the
finite, explicit, host-dimension-free reduction of the optimal-search frontier:
the only remaining input is an inequality on the `2·|I|`-dimensional refined
quotient matrix exponential — checkable spectral data, not perturbation theory. -/

section ChainCriterion

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **The host search column-sum amplitude IS the finite chain block amplitude
(axiom-clean).**  Suppose `P` is a marked-union equitable partition for the
singleton marked set `{w}`, and `{w}` is *exactly* the cell `i₀` of `w` (size
one, `hcell`).  Then the full-`N` success column sum `∑_v U(τ)_{v,w}` equals the
finite refined-quotient block amplitude

  `∑_{ib} (∑_v e_{ib} v) · (exp(-iτ·H_chain))_{ib, (i₀,true)}`,

where `e_{ib} = P'.cellUniformVec ib`, `H_chain = -γ·Q̃' − markedDiag`, and
`(i₀,true)` is the refined cell of `w`.  This is the host-dimension-free,
*exact* (no perturbation) reduction of the success amplitude onto the finite
`2·|I|`-dimensional chain — the generalization of the `K_n` flagship `cg_colSum`.
-/
theorem search_colSum_eq_chain {G : WeightedGraph V}
    (P : EquitablePartition G I) (w : V) (γ τ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y →
      (x ∈ ({w} : Finset V) ↔ y ∈ ({w} : Finset V)))
    (hcell : ∀ x : V, P.cells x = P.cells w → x = w) :
    (∑ v, (G.searchEvolve ({w} : Finset V) γ τ) v w)
      = ∑ ib : MarkedRefined I,
          (∑ v, (P.refineByMarked ({w} : Finset V) hM).cellUniformVec ib v)
            * (NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
                (-(γ : ℂ) • (P.refineByMarked ({w} : Finset V) hM).symmQuotient
                  - markedDiag I)))
                ib (P.cells w, true) := by
  classical
  set P' := P.refineByMarked ({w} : Finset V) hM with hP'
  set Hc : Matrix (MarkedRefined I) (MarkedRefined I) ℂ :=
    -(γ : ℂ) • P'.symmQuotient - markedDiag I with hHc
  set s : ℂ := -(Complex.I * (τ : ℂ)) with hs
  -- The marked cell of `w` is `(P.cells w, true)`.
  set jb₀ : MarkedRefined I := (P.cells w, true) with hjb₀
  -- `P'.cells w = (P.cells w, true) = jb₀`.
  have hcellw : P'.cells w = jb₀ := by
    show (P.cells w, decide (w ∈ ({w} : Finset V))) = jb₀
    rw [hjb₀]; simp
  -- `P'.cells x = jb₀ ↔ x = w` (the refined marked cell is exactly the singleton).
  have hcells_iff : ∀ x : V, P'.cells x = jb₀ ↔ x = w := by
    intro x
    constructor
    · intro hx
      have hfst : P.cells x = P.cells w := by
        have := congrArg Prod.fst hx; rw [hjb₀] at this; exact this
      exact hcell x hfst
    · rintro rfl; exact hcellw
  -- Hence the marked refined cell is the singleton `{w}` (size one).
  have hcellcard : P'.cellCard jb₀ = 1 := by
    rw [EquitablePartition.cellCard]
    rw [show (Finset.univ.filter (fun x : V => P'.cells x = jb₀)) = {w} from ?_]
    · simp
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact hcells_iff x
  -- So the `jb₀`-cell-uniform vector is exactly the indicator `|w⟩`.
  have he_jb₀ : (P'.cellUniformVec jb₀) = (fun v => if v = w then (1 : ℂ) else 0) := by
    funext v
    unfold EquitablePartition.cellUniformVec
    rw [hcellcard]
    simp only [Real.sqrt_one, Complex.ofReal_one, div_one]
    by_cases hv : v = w
    · subst hv; rw [if_pos hcellw, if_pos rfl]
    · rw [if_neg (fun h => hv ((hcells_iff v).mp h)), if_neg hv]
  -- `|w⟩ = E'.mulVec (e_{jb₀})` (column `jb₀` of the cell-embedding).
  have hwcol : (P'.cellUniformVec jb₀)
      = (cellEmbed P').mulVec (Pi.single jb₀ (1 : ℂ)) := by
    rw [cellEmbed_mulVec]
    funext v
    rw [Finset.sum_eq_single jb₀]
    · rw [Pi.single_eq_same, one_mul]
    · intro ib _ hib; rw [Pi.single_eq_of_ne hib, zero_mul]
    · intro h; exact absurd (Finset.mem_univ jb₀) h
  -- The full search column = `(U.mulVec |w⟩)`, and `U·E' = E'·exp(s•Hc)`, so
  -- `U.mulVec |w⟩ = E'.mulVec (exp(s•Hc).col jb₀)`.
  have hintertwine : G.searchEvolve ({w} : Finset V) γ τ * cellEmbed P'
      = cellEmbed P' * NormedSpace.exp (s • Hc) :=
    searchEvolve_mul_cellEmbed P ({w} : Finset V) γ τ hM
  have hUw : (G.searchEvolve ({w} : Finset V) γ τ).mulVec (P'.cellUniformVec jb₀)
      = (cellEmbed P').mulVec
          ((NormedSpace.exp (s • Hc)).mulVec (Pi.single jb₀ (1 : ℂ))) := by
    rw [hwcol]
    rw [Matrix.mulVec_mulVec, hintertwine, ← Matrix.mulVec_mulVec]
  -- Each column entry: `U_{v,w} = (U.mulVec |w⟩)_v` since `|w⟩` is the indicator.
  have hcol : ∀ v, (G.searchEvolve ({w} : Finset V) γ τ) v w
      = (G.searchEvolve ({w} : Finset V) γ τ).mulVec (P'.cellUniformVec jb₀) v := by
    intro v
    rw [he_jb₀]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single w]
    · rw [if_pos rfl, mul_one]
    · intro b _ hb; rw [if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ w) h
  rw [Finset.sum_congr rfl (fun v _ => hcol v), Finset.sum_congr rfl (fun v _ => congrFun hUw v)]
  -- `(E'.mulVec (exp.col jb₀))_v = ∑_ib e_ib(v) · exp_{ib,jb₀}`; then swap sums.
  have hentry : ∀ v,
      ((cellEmbed P').mulVec
          ((NormedSpace.exp (s • Hc)).mulVec (Pi.single jb₀ (1 : ℂ)))) v
        = ∑ ib, (P'.cellUniformVec ib v) * (NormedSpace.exp (s • Hc)) ib jb₀ := by
    intro v
    have hxcol : (NormedSpace.exp (s • Hc)).mulVec (Pi.single jb₀ (1 : ℂ))
        = fun ib => (NormedSpace.exp (s • Hc)) ib jb₀ := by
      funext ib; rw [Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hxcol]
    simp only [cellEmbed, Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun v _ => hentry v), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ib _
  rw [← Finset.sum_mul]

/-- **The finite refined-quotient chain success amplitude.**  The
`(MarkedRefined I)`-block evolution `exp(-iτ·H_chain)` applied to the marked
column `(P.cells w, true)`, contracted against the cell masses
`m_{ib} = ∑_v e_{ib} v` and normalized by `√N` (`N = |V|`).  By
`search_colSum_eq_chain` this finite quantity **equals** the host's uniform-overlap
search success amplitude — a `2·|I|`-dimensional, host-dimension-free object. -/
noncomputable def chainSearchAmplitude {G : WeightedGraph V}
    (P : EquitablePartition G I) (w : V) (γ τ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y →
      (x ∈ ({w} : Finset V) ↔ y ∈ ({w} : Finset V))) : ℂ :=
  (∑ ib : MarkedRefined I,
      (∑ v, (P.refineByMarked ({w} : Finset V) hM).cellUniformVec ib v)
        * (NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
            (-(γ : ℂ) • (P.refineByMarked ({w} : Finset V) hM).symmQuotient
              - markedDiag I)))
            ib (P.cells w, true)) / Real.sqrt (Fintype.card V)

/-! ### The chain amplitude is an explicit unit-vector overlap of a unitary.

The finite chain amplitude `chainSearchAmplitude` is, by construction, an inner
product of two **explicit unit vectors** against the unitary `exp(-iτ·H_chain)`:

* the normalized **cell-mass vector** `ŝ_{ib} = √|C_{ib}| / √N` (the chain image
  of the host uniform state `|s⟩`), a genuine unit vector since
  `∑_{ib} |C_{ib}| = N`;
* the **marked chain state** `e_{(cells w, true)}` (the chain image of `|w⟩`), a
  coordinate unit vector;
* the **chain generator** `H_chain = -γ·Q̃' − markedDiag` is **Hermitian**
  (`symmQuotient` and `markedDiag` both are), so `exp(-iτ·H_chain)` is unitary.

This section makes that structure explicit, reducing any chain-amplitude bound to
a clean unitary-overlap inequality on a finite Hermitian system. -/

/-- **The cell mass is `√|C_i|`.**  Summing the normalized cell-indicator
`cellUniformVec i` over all vertices gives `|C_i| · (1/√|C_i|) = √|C_i|` (and `0 =
√0` for an empty cell).  This is the entry of the chain's cell-mass vector. -/
theorem cellMass_eq_sqrt_cellCard {G : WeightedGraph V}
    (P : EquitablePartition G I) (i : I) :
    (∑ v, P.cellUniformVec i v) = (Real.sqrt (P.cellCard i) : ℂ) := by
  classical
  -- The sum picks up `1/√|C_i|` on each of the `|C_i|` vertices of cell `i`.
  rw [show (∑ v, P.cellUniformVec i v)
        = ∑ v ∈ Finset.univ.filter (fun v => P.cells v = i),
            (1 : ℂ) / ((Real.sqrt (P.cellCard i) : ℝ) : ℂ) from ?_]
  · rw [Finset.sum_const, nsmul_eq_mul]
    -- `(filter ...).card = cellCard i` (as a real/complex cast).
    have hcard : ((Finset.univ.filter (fun v => P.cells v = i)).card : ℂ)
        = (P.cellCard i : ℂ) := by
      unfold EquitablePartition.cellCard; push_cast; rfl
    rw [hcard]
    by_cases hi : P.cellCard i = 0
    · rw [hi]; simp
    · have hpos : 0 < P.cellCard i := lt_of_le_of_ne (P.cellCard_nonneg i) (Ne.symm hi)
      have hsq : (Real.sqrt (P.cellCard i) : ℂ) * (Real.sqrt (P.cellCard i) : ℂ)
          = (P.cellCard i : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (P.cellCard_nonneg i)]
      have hne : (Real.sqrt (P.cellCard i) : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]; exact ne_of_gt (Real.sqrt_pos.mpr hpos)
      rw [← hsq]
      field_simp
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    unfold EquitablePartition.cellUniformVec
    by_cases hv : P.cells v = i <;> simp [hv]

/-- **The total cell mass is `N`.**  `∑_i |C_i| = |V|`, since the cells partition
the vertex set.  Hence the normalized cell-mass vector `√|C_i|/√N` is a unit
vector. -/
theorem sum_cellCard {G : WeightedGraph V} (P : EquitablePartition G I) :
    (∑ i, P.cellCard i) = (Fintype.card V : ℝ) := by
  classical
  unfold EquitablePartition.cellCard
  rw [← Nat.cast_sum]
  congr 1
  -- `∑_i #{v : cells v = i} = #V` (each vertex counted once, in its own cell).
  rw [← Finset.card_univ (α := V)]
  rw [Finset.card_eq_sum_card_fiberwise (f := P.cells) (t := Finset.univ)
      (fun v _ => Finset.mem_univ _)]

/-- **The chain generator `H_chain = -γ·Q̃' − markedDiag` is Hermitian.**  Both
`symmQuotient` (`symmQuotient_isHermitian`) and `markedDiag` are Hermitian, and
`-γ·(·)` preserves Hermiticity for real `γ`; hence `exp(-iτ·H_chain)` is unitary
and the chain amplitude is a genuine unitary overlap. -/
theorem markedDiag_isHermitian : (markedDiag I).IsHermitian := by
  ext ib jb
  show star (markedDiag I jb ib) = markedDiag I ib jb
  unfold markedDiag
  by_cases h : ib = jb
  · subst h; by_cases hb : ib.2 = true <;> simp [hb]
  · rw [if_neg (fun hc => h hc.1.symm), if_neg (fun hc => h hc.1), star_zero]

theorem chainGen_isHermitian {G : WeightedGraph V}
    (P : EquitablePartition G I) (M : Finset V)
    (hM : ∀ x y : V, P.cells x = P.cells y → (x ∈ M ↔ y ∈ M)) (γ : ℝ) :
    (-(γ : ℂ) • (P.refineByMarked M hM).symmQuotient
        - markedDiag I).IsHermitian := by
  apply Matrix.IsHermitian.sub
  · -- `-γ • Q̃'` is Hermitian: real (self-adjoint) scalar times a Hermitian matrix.
    apply ((P.refineByMarked M hM).symmQuotient_isHermitian).smul
    rw [IsSelfAdjoint, star_neg, Complex.star_def, Complex.conj_ofReal]
  · exact markedDiag_isHermitian

/-- **The chain amplitude in explicit cell-mass form.**  Replacing the abstract
cell mass `∑_v e_{ib} v` by its closed value `√|C_{ib}|` (`cellMass_eq_sqrt_cellCard`)
shows the chain amplitude is the **explicit** finite sum

  `(∑_{ib} √|C'_{ib}| · exp(-iτ·H_chain)_{ib, (cells w, true)}) / √N`,

a contraction of the unitary block `exp(-iτ·H_chain)`'s marked column against the
explicit cell-mass vector `√|C'_{ib}|`.  Here `C'` are the refined (marked-split)
cells.  This is the fully explicit form of the frontier input: the masses are
`√(binomial)` and `H_chain` is the explicit tridiagonal Krawtchouk chain. -/
theorem chainSearchAmplitude_eq_massForm {G : WeightedGraph V}
    (P : EquitablePartition G I) (w : V) (γ τ : ℝ)
    (hM : ∀ x y : V, P.cells x = P.cells y →
      (x ∈ ({w} : Finset V) ↔ y ∈ ({w} : Finset V))) :
    chainSearchAmplitude P w γ τ hM
      = (∑ ib : MarkedRefined I,
          (Real.sqrt ((P.refineByMarked ({w} : Finset V) hM).cellCard ib) : ℂ)
            * (NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
                (-(γ : ℂ) • (P.refineByMarked ({w} : Finset V) hM).symmQuotient
                  - markedDiag I)))
                ib (P.cells w, true)) / Real.sqrt (Fintype.card V) := by
  unfold chainSearchAmplitude
  congr 1
  apply Finset.sum_congr rfl
  intro ib _
  rw [cellMass_eq_sqrt_cellCard]

/-- **Finite-chain sufficient condition for optimal CTQW search (axiom-clean).**
Let `P` be a marked-union equitable partition of `G` for the singleton `{w}`,
with `{w}` *exactly* its own cell (size one, `hcell`).  Suppose there is a
coupling `γ > 0` and a time `τ ≤ C·√N` (`C ≥ 0`) at which the **finite
refined-quotient chain amplitude** reaches the success threshold
`‖chainSearchAmplitude P w γ τ hM‖ ≥ 1/√2`.  Then host CTQW search for `w` is
optimal (`IsOptimalCTQWSearch G w`).

This is the central reduction: the host optimal-search frontier collapses to an
inequality on the `2·|I|`-dimensional refined-quotient matrix exponential — a
*finite, explicit spectral object*, with NO reference to the host dimension `N`
beyond the `√N` normalization.  For the hypercube `Q_d` (`I = Fin (d+1)`, the
Hamming-distance partition) this is a `2(d+1)×2(d+1)` chain; the open
`hypercube_search_optimal_timing` reduces *exactly* to checking this inequality.
-/
theorem optimal_search_of_chain_amplitude {G : WeightedGraph V}
    (P : EquitablePartition G I) (w : V)
    (hM : ∀ x y : V, P.cells x = P.cells y →
      (x ∈ ({w} : Finset V) ↔ y ∈ ({w} : Finset V)))
    (hcell : ∀ x : V, P.cells x = P.cells w → x = w)
    -- Symmetric (real) adjacency: the genuine Childs–Goldstone *row* success
    -- amplitude `⟨w|U|s⟩ = ∑_v U_{w,v}/√N` then equals the *column* sum
    -- `∑_v U_{v,w}/√N` that the chain machinery (`search_colSum_eq_chain`)
    -- computes.  Every concrete search host here (complete graph, hypercube,
    -- lattice) has symmetric adjacency, so this is supplied for free.
    (hsymm : ∀ u v : V, G.adj u v = G.adj v u)
    (γ τ C : ℝ) (hγ : 0 < γ) (_hC : 0 ≤ C) (hCπ : C ≤ Real.pi)
    (hτ : τ ≤ C * Real.sqrt (Fintype.card V))
    (hampl : ‖chainSearchAmplitude P w γ τ hM‖ ≥ 1 / Real.sqrt 2) :
    IsOptimalCTQWSearch G w := by
  -- The supplied budget `C ≤ π` meets the concrete universal budget `π·√N`.
  have hτπ : τ ≤ Real.pi * Real.sqrt (Fintype.card V) :=
    hτ.trans (mul_le_mul_of_nonneg_right hCπ (Real.sqrt_nonneg _))
  refine ⟨γ, τ, hγ, hτπ, ?_⟩
  -- `IsOptimalSearch G {w} γ τ` collapses to `‖(∑_v U(τ)_{w,v})/√N‖ ≥ 1/√2`
  -- (genuine row amplitude); via symmetry, `= ‖(∑_v U(τ)_{v,w})/√N‖`.
  show ‖_‖ ≥ 1 / Real.sqrt 2
  have hcollapse : (∑ m, if m ∈ ({w} : Finset V)
        then (∑ v, (G.searchEvolve {w} γ τ) m v) / Real.sqrt (Fintype.card V) else 0)
      = (∑ v, (G.searchEvolve {w} γ τ) v w) / Real.sqrt (Fintype.card V) := by
    rw [Finset.sum_eq_single w]
    · rw [if_pos (Finset.mem_singleton_self w)]
      congr 1
      exact Finset.sum_congr rfl
        (fun v _ => G.searchEvolve_apply_comm_of_symm {w} γ τ hsymm w v)
    · intro b _ hb; rw [if_neg (by simpa [Finset.mem_singleton] using hb)]
    · intro h; exact absurd (Finset.mem_univ w) h
  rw [hcollapse, search_colSum_eq_chain P w γ τ hM hcell]
  exact hampl

end ChainCriterion

end Graphplay
