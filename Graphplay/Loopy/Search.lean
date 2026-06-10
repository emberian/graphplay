/-
# Graphplay.Loopy.Search

**Diagonal-shift invariance of continuous-time-quantum-walk (CTQW) spatial
search, on the loopy Hermitian layer.**

The Childs–Goldstone spatial-search Hamiltonian for a single marked vertex `w`
on a graph with movement matrix `M` (the adjacency `A`, the Laplacian `L`, or a
self-loop-augmented `A + ℓ•1`) is

  `H_γ(M) = γ • M + |w⟩⟨w|`            (`|w⟩⟨w| = Matrix.single w w 1`),

and the search evolves by `U(τ) = exp(-iτ H_γ(M))`.  The headline structural
fact, proved here and reused throughout the corpus, is that **adding a uniform
diagonal `d•1` (real `d`) to the movement matrix is invisible to every search
amplitude**: it shifts the Hamiltonian by `γd•1`, a pure global phase
`e^{-iτγd}` of unit modulus, which factors out of the whole evolution operator.

Concretely:

* `searchHamiltonian_add_smul_one` — the algebraic shift identity
  `H_γ(M + d•1) = H_γ(M) + (γd)•1`.
* `norm_searchEvolve_shift_eq` — every entry modulus of the search evolution is
  unchanged by the `d•1` shift (the engine `norm_exp_shifted_entry_eq`).
* `searchSuccess_shift_eq` — the full success amplitude
  `‖(1/√n)·Σ_v U(τ) w v‖` is unchanged (the global phase pulls out of the sum).

Two corpus-relevant corollaries:

* **Lackadaisical search** (Wong arXiv:1706.06939): a uniform self-loop
  `A + ℓ•1` gives the *same* search success amplitude as `A` (the self-loop is a
  global phase).  `searchSuccess_addSelfLoop_eq`.
* **Laplacian search on regular graphs** (arXiv:1409.5840): for a `d`-regular
  graph `L = D − A = (d.re)•1 − A`, so the Laplacian search amplitude equals the
  search amplitude of the *negated* adjacency `−A` (a time reversal of the walk),
  up to the unit-modulus shift phase.  `norm_searchEvolve_laplacian_eq_of_regular`.

For the "optimal search time" claim the file delivers two things.  First, a
**machine-checked refutation** of the gap-only form: an eigenvalue-magnitude gap
alone does *not* imply constant search amplitude
(`not_searchSuccess_optimal_time_of_gap_only` — witness `A = diag(0,0,2)`, whose
search Hamiltonian is diagonal and never moves amplitude, so every `(γ, τ)`
yields exactly `1/√3 < 1/√2`).  The CNO analysis needs the start
state aligned with the principal eigenvector.  Second, the **CNO
statement** — uniform principal eigenvector (= regularity) *plus* the spectral
gap — `searchSuccess_optimal_time`, demoted to the cited interface
`CNOLoopyOptimalSearch` (arXiv:2004.12686 Thms 1–2), with hypothesis-side
inhabitation (`cnoLoopy_hypotheses_inhabited`) and a proven `Fin 1` instance.

References: Childs–Goldstone (quant-ph/0306054); CNO (arXiv:2004.12686);
Laplacian-walk search (arXiv:1409.5840); lackadaisical walk Wong
(arXiv:1706.06939); the diagonal-shift global-phase engine is
`Graphplay.PST.DiagonalShift.norm_exp_shifted_entry_eq` / `exp_add_smul_one`.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Data.Matrix.Basis
import Graphplay.Loopy
import Graphplay.Loopy.Laplacian
import Graphplay.PST.DiagonalShift

open scoped Matrix
open NormedSpace

universe u

namespace Graphplay
namespace LoopySearch

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## 1. The search Hamiltonian on an arbitrary movement matrix. -/

/-- **Spatial-search Hamiltonian** with movement matrix `M : Matrix V V ℂ`,
marked vertex `w`, oracle strength `γ : ℝ`:

  `H_γ(M) = γ • M + |w⟩⟨w|`,   `|w⟩⟨w| = Matrix.single w w 1`.

`M` is allowed to be any Hermitian matrix — the adjacency, the Laplacian, or a
self-loop-augmented adjacency — matching the `searchHamiltonian` of
`Graphplay.StdLib.CompleteMultipartite` (which is the `M = G.adj` case). -/
noncomputable def searchHamiltonian (M : Matrix V V ℂ) (w : V) (γ : ℝ) :
    Matrix V V ℂ :=
  (γ : ℂ) • M + Matrix.single w w (1 : ℂ)

/-- Continuous-time search evolution at time `τ`: `U(τ) = exp(-iτ H_γ(M))`. -/
noncomputable def searchEvolve (M : Matrix V V ℂ) (w : V) (γ τ : ℝ) :
    Matrix V V ℂ :=
  NormedSpace.exp (-(Complex.I * (τ : ℂ)) • searchHamiltonian M w γ)

/-- The CTQW spatial-search **success amplitude** from the uniform
superposition `|s⟩ = (1/√n) Σ_v |v⟩` to the marked vertex `w` at time `τ` and
oracle strength `γ`:

  `‖⟨w| U(τ) |s⟩‖ = ‖(1/√n) Σ_v U(τ) w v‖`.

This matches the `searchSuccessAmplitude` convention of
`Graphplay.StdLib.CompleteMultipartite`. -/
noncomputable def searchSuccess (M : Matrix V V ℂ) (w : V) (γ τ : ℝ) : ℝ :=
  let U := searchEvolve M w γ τ
  let n := (Fintype.card V : ℝ)
  ‖(1 / Real.sqrt n : ℂ) * ∑ v, U w v‖

/-! ## 2. Diagonal-shift invariance — the headline. -/

omit [Fintype V] in
/-- **Search Hamiltonian shift identity.**  Adding a uniform diagonal `d•1`
(real `d`) to the movement matrix shifts the search Hamiltonian by exactly
`(γd)•1`:

  `H_γ(M + d•1) = H_γ(M) + (γd)•1`.

The oracle term `|w⟩⟨w|` is untouched; only the scaled movement term picks up
the shift. -/
theorem searchHamiltonian_add_smul_one (M : Matrix V V ℂ) (w : V) (γ d : ℝ) :
    searchHamiltonian (M + (d : ℂ) • (1 : Matrix V V ℂ)) w γ
      = searchHamiltonian M w γ + ((γ : ℂ) * (d : ℂ)) • (1 : Matrix V V ℂ) := by
  unfold searchHamiltonian
  rw [smul_add, smul_smul]
  abel

/-- **Diagonal-shift modulus invariance (entrywise).**  For real `d`, every
entry modulus of the search evolution is unchanged when the movement matrix is
shifted by `d•1`:

  `‖searchEvolve (M + d•1) w γ τ j i‖ = ‖searchEvolve M w γ τ j i‖`.

The shift contributes only the global phase `e^{-iτγd}` of unit modulus; this is
a direct application of `norm_exp_shifted_entry_eq`. -/
theorem norm_searchEvolve_shift_eq (M : Matrix V V ℂ) (w : V) (γ d τ : ℝ)
    (i j : V) :
    ‖searchEvolve (M + (d : ℂ) • (1 : Matrix V V ℂ)) w γ τ j i‖
      = ‖searchEvolve M w γ τ j i‖ := by
  unfold searchEvolve
  rw [searchHamiltonian_add_smul_one M w γ d]
  -- `H_γ(M+d•1) = H_γ(M) + (γd)•1`; strip the `(γd)•1` global phase.
  have hrw : searchHamiltonian M w γ + ((γ : ℂ) * (d : ℂ)) • (1 : Matrix V V ℂ)
      = searchHamiltonian M w γ + ((γ * d : ℝ) : ℂ) • (1 : Matrix V V ℂ) := by
    push_cast; ring_nf
  rw [hrw]
  exact norm_exp_shifted_entry_eq (searchHamiltonian M w γ) τ (γ * d) i j

/-- **Diagonal-shift success-amplitude invariance — THE headline.**  For real
`d`, shifting the movement matrix by a uniform diagonal `d•1` leaves the entire
search **success amplitude** unchanged:

  `searchSuccess (M + d•1) w γ τ = searchSuccess M w γ τ`.

The shift is a pure global phase `e^{-iτγd}` (unit modulus), which factors out of
the whole evolution operator and hence out of the row-sum `Σ_v U w v`; taking the
modulus removes it.  This is the structural reason a uniform diagonal is
invisible to spatial search. -/
theorem searchSuccess_shift_eq (M : Matrix V V ℂ) (w : V) (γ d τ : ℝ) :
    searchSuccess (M + (d : ℂ) • (1 : Matrix V V ℂ)) w γ τ
      = searchSuccess M w γ τ := by
  unfold searchSuccess searchEvolve
  rw [searchHamiltonian_add_smul_one M w γ d]
  -- Realign the shift to the `(c : ℝ) • 1` form expected by `exp_add_smul_one`.
  have hrw : searchHamiltonian M w γ + ((γ : ℂ) * (d : ℂ)) • (1 : Matrix V V ℂ)
      = searchHamiltonian M w γ + ((γ * d : ℝ) : ℂ) • (1 : Matrix V V ℂ) := by
    push_cast; ring_nf
  rw [hrw]
  -- Factor the shifted exponential as `phase • (unshifted exponential)`.
  set phase : ℂ := NormedSpace.exp (-(Complex.I * (τ : ℂ) * ((γ * d : ℝ) : ℂ)))
    with hphase
  have hfac :
      NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
          (searchHamiltonian M w γ + ((γ * d : ℝ) : ℂ) • (1 : Matrix V V ℂ)))
        = phase • NormedSpace.exp (-(Complex.I * (τ : ℂ)) • searchHamiltonian M w γ) :=
    exp_add_smul_one (searchHamiltonian M w γ) ((γ * d : ℝ) : ℂ) (τ : ℂ)
  -- Each `(w, v)` entry of the shifted evolution is `phase * (unshifted entry)`.
  have hentry : ∀ v : V,
      (NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
          (searchHamiltonian M w γ + ((γ * d : ℝ) : ℂ) • (1 : Matrix V V ℂ)))) w v
        = phase * (NormedSpace.exp (-(Complex.I * (τ : ℂ)) • searchHamiltonian M w γ)) w v := by
    intro v
    rw [hfac, Matrix.smul_apply, smul_eq_mul]
  -- Pull the phase out of the row-sum and out of the leading scalar.
  simp only [hentry, ← Finset.mul_sum]
  rw [show (1 / Real.sqrt (Fintype.card V : ℝ) : ℂ) *
        (phase * ∑ v, (NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
            searchHamiltonian M w γ)) w v)
      = phase * ((1 / Real.sqrt (Fintype.card V : ℝ) : ℂ) *
            ∑ v, (NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
              searchHamiltonian M w γ)) w v) by ring]
  rw [norm_mul]
  -- `‖phase‖ = 1`.
  have hph : ‖phase‖ = 1 := by
    rw [hphase]
    have := norm_exp_neg_I_mul τ (γ * d)
    -- `norm_exp_neg_I_mul τ c : ‖exp(-(I·τ·c))‖ = 1`.
    simpa using this
  rw [hph, one_mul]

/-! ## 3. Lackadaisical search (Wong arXiv:1706.06939).

A uniform self-loop weight `ℓ : ℝ` augments the movement matrix to `A + ℓ•1`.
By §2 this is a pure global phase, invisible to the search success amplitude:
the lackadaisical CTQW spatial search has exactly the same success profile as
the loopless one. -/

/-- **Lackadaisical-search amplitude invariance (Wong arXiv:1706.06939).**  A
uniform self-loop of (real) weight `ℓ` leaves the spatial-search success
amplitude unchanged:

  `searchSuccess (A + ℓ•1) w γ τ = searchSuccess A w γ τ`.

A direct corollary of `searchSuccess_shift_eq` with `M = A`, `d = ℓ`. -/
theorem searchSuccess_addSelfLoop_eq (A : Matrix V V ℂ) (w : V) (γ ℓ τ : ℝ) :
    searchSuccess (A + (ℓ : ℂ) • (1 : Matrix V V ℂ)) w γ τ
      = searchSuccess A w γ τ :=
  searchSuccess_shift_eq A w γ ℓ τ

/-! ## 4. Laplacian search on regular graphs (arXiv:1409.5840).

For a `d`-regular weighted graph `G`, the Laplacian is `L = D − A = (d.re)•1 − A`
(`laplacian_adj_eq_of_regular`).  Hence the Laplacian search Hamiltonian is the
search Hamiltonian of the *negated* adjacency `−A`, shifted by `(d.re)•1`:

  `H_γ(L) = H_γ(−A) + (γ·d.re)•1`.

So by §2 the Laplacian search evolution has the same entry moduli as the search
evolution of `−A`.  The `−A` is a **time reversal** of the adjacency
walk — it is `−A`, not `A`; the modulus equality is stated
against `searchEvolve (−A.adj)`. -/

/-- The Laplacian movement matrix of a `d`-regular graph is the negated
adjacency shifted by `(d.re)•1`:  `L = (−A) + (d.re)•1`.  (Restated from
`laplacian_adj_eq_neg_add_of_regular` for use as a `searchEvolve` movement
matrix.) -/
theorem laplacian_movement_eq_of_regular (G : WeightedGraph V) (d : ℂ)
    (hreg : G.isRegular d) :
    (WeightedGraph.laplacian G).adj
      = (-G.adj) + ((d.re : ℝ) : ℂ) • (1 : Matrix V V ℂ) :=
  laplacian_adj_eq_neg_add_of_regular G d hreg

/-- **Laplacian-search modulus equality (regular case, arXiv:1409.5840).**  For
a `d`-regular weighted graph, every entry modulus of the *Laplacian* search
evolution equals the corresponding entry modulus of the *negated-adjacency*
search evolution:

  `‖searchEvolve L w γ τ j i‖ = ‖searchEvolve (−A) w γ τ j i‖`.

The `−A` is the time-reversed adjacency walk; the `(d.re)•1` Laplacian shift
contributes only a unit-modulus global phase (stripped via §2).  We do **not**
identify `−A` with `A`: the sign is a time reversal, exactly as documented in
`Graphplay.Loopy.Laplacian`. -/
theorem norm_searchEvolve_laplacian_eq_of_regular (G : WeightedGraph V) (d : ℂ)
    (hreg : G.isRegular d) (w : V) (γ τ : ℝ) (i j : V) :
    ‖searchEvolve (WeightedGraph.laplacian G).adj w γ τ j i‖
      = ‖searchEvolve (-G.adj) w γ τ j i‖ := by
  rw [laplacian_movement_eq_of_regular G d hreg]
  exact norm_searchEvolve_shift_eq (-G.adj) w γ d.re τ i j

/-- **Laplacian-search success-amplitude equality (regular case).**  For a
`d`-regular weighted graph the Laplacian search success amplitude equals the
negated-adjacency search success amplitude:

  `searchSuccess L w γ τ = searchSuccess (−A) w γ τ`.

The Laplacian `(d.re)•1` shift is a pure global phase; the residual `−A` is the
time-reversed adjacency walk. -/
theorem searchSuccess_laplacian_eq_of_regular (G : WeightedGraph V) (d : ℂ)
    (hreg : G.isRegular d) (w : V) (γ τ : ℝ) :
    searchSuccess (WeightedGraph.laplacian G).adj w γ τ
      = searchSuccess (-G.adj) w γ τ := by
  rw [laplacian_movement_eq_of_regular G d hreg]
  exact searchSuccess_shift_eq (-G.adj) w γ d.re τ

/-! ## 5. The gap-only optimal-search claim is FALSE: a machine-checked
counterexample.

A tempting strengthening of the CNO theorem reads: `A` Hermitian with an
eigenvalue-*magnitude* gap (`∀ i ≠ p, |λᵢ| < |λ_p|`) suffices for
`searchSuccess ≥ 1/√2` at some `(γ, τ)`.  It is false: the gap constrains only eigen-
**values**, while the Childs–Goldstone / CNO analysis fundamentally requires the
**start state** (the uniform superposition in `searchSuccess`) to be aligned
with the **principal eigenvector**.  Witness: `A = diag(0, 0, 2)` on three
vertices is Hermitian with spectrum `{0, 0, 2}` and a strictly dominant
principal eigenvalue, but its principal eigenvector is a *standard basis*
vector, orthogonal to nothing useful — and since both `A` and the oracle
`|w⟩⟨w|` are diagonal, the search Hamiltonian is diagonal, the evolution is a
diagonal phase matrix, and **no amplitude ever moves**: every `(γ, τ)` gives
`searchSuccess = 1/√3 < 1/√2`. -/

section GapOnlyCounterexample

/-- The diagonal entries `(0, 0, 2)` of the counterexample movement matrix. -/
private def cexD : Fin 3 → ℂ := ![0, 0, 2]

/-- The counterexample movement matrix `A = diag(0, 0, 2)`: Hermitian, strictly
dominant principal eigenvalue `2`, principal eigenvector a standard basis
vector (not uniform). -/
private def cexA : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal cexD

private theorem cexA_isHermitian : cexA.IsHermitian := by
  refine Matrix.isHermitian_diagonal_iff.mpr fun i => ?_
  fin_cases i <;> simp [cexD, IsSelfAdjoint]

/-- Every eigenvalue of `diag(0,0,2)` is `0` or `2` (membership in the spectrum
`= Set.range cexD`, transported from `ℂ` to `ℝ` along the algebra map). -/
private theorem cexA_eigenvalues_mem (i : Fin 3) :
    cexA_isHermitian.eigenvalues i = 0 ∨ cexA_isHermitian.eigenvalues i = 2 := by
  have hmem : cexA_isHermitian.eigenvalues i ∈ spectrum ℝ cexA :=
    cexA_isHermitian.eigenvalues_mem_spectrum_real i
  have hmemC : ((cexA_isHermitian.eigenvalues i : ℝ) : ℂ) ∈ spectrum ℂ cexA :=
    (spectrum.algebraMap_mem_iff ℂ).mpr hmem
  have hrange : spectrum ℂ cexA = Set.range cexD := spectrum_diagonal cexD
  rw [hrange] at hmemC
  obtain ⟨j, hj⟩ := hmemC
  fin_cases j
  · left
    have h0 : ((cexA_isHermitian.eigenvalues i : ℝ) : ℂ) = 0 := by
      rw [← hj]; simp [cexD]
    exact_mod_cast h0
  · left
    have h0 : ((cexA_isHermitian.eigenvalues i : ℝ) : ℂ) = 0 := by
      rw [← hj]; simp [cexD]
    exact_mod_cast h0
  · right
    have h2 : ((cexA_isHermitian.eigenvalues i : ℝ) : ℂ) = 2 := by
      rw [← hj]; simp [cexD]
    exact_mod_cast h2

/-- The eigenvalues of `diag(0,0,2)` sum to its trace `2`. -/
private theorem cexA_sum_eigenvalues :
    cexA_isHermitian.eigenvalues 0 + cexA_isHermitian.eigenvalues 1
      + cexA_isHermitian.eigenvalues 2 = 2 := by
  have htr := cexA_isHermitian.trace_eq_sum_eigenvalues
  have htrace : cexA.trace = (2 : ℂ) := by
    rw [show cexA = Matrix.diagonal cexD from rfl, Matrix.trace_diagonal]
    simp [cexD, Fin.sum_univ_three]
  rw [htrace, Fin.sum_univ_three] at htr
  exact Complex.ofReal_inj.mp (by push_cast; exact htr.symm)

/-- `diag(0,0,2)` **satisfies the gap hypothesis**: there is a principal index
`p` whose eigenvalue strictly dominates all others in magnitude (the unique
index carrying the eigenvalue `2`; each eigenvalue is `0` or `2` and they sum
to `2`, so exactly one equals `2`). -/
private theorem cexA_exists_principal :
    ∃ p : Fin 3, ∀ i, i ≠ p →
      |cexA_isHermitian.eigenvalues i| < |cexA_isHermitian.eigenvalues p| := by
  have h0 := cexA_eigenvalues_mem 0
  have h1 := cexA_eigenvalues_mem 1
  have h2 := cexA_eigenvalues_mem 2
  have hsum := cexA_sum_eigenvalues
  rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2
  · exact absurd hsum (by rw [e0, e1, e2]; norm_num)
  · exact ⟨2, fun i hi => by fin_cases i <;> simp_all [abs_of_nonneg]⟩
  · exact ⟨1, fun i hi => by fin_cases i <;> simp_all [abs_of_nonneg]⟩
  · exact absurd hsum (by rw [e0, e1, e2]; norm_num)
  · exact ⟨0, fun i hi => by fin_cases i <;> simp_all [abs_of_nonneg]⟩
  · exact absurd hsum (by rw [e0, e1, e2]; norm_num)
  · exact absurd hsum (by rw [e0, e1, e2]; norm_num)
  · exact absurd hsum (by rw [e0, e1, e2]; norm_num)

/-- The search Hamiltonian of the diagonal counterexample is **diagonal**: both
the movement matrix and the oracle `|0⟩⟨0|` are. -/
private theorem cexA_searchHamiltonian (γ : ℝ) :
    searchHamiltonian cexA 0 γ
      = Matrix.diagonal
          (fun i => (γ : ℂ) * cexD i + if i = (0 : Fin 3) then 1 else 0) := by
  unfold searchHamiltonian cexA
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp [Matrix.diagonal_apply_eq, Matrix.single_apply, eq_comm]
  · have hne : ¬((0 : Fin 3) = i ∧ (0 : Fin 3) = j) := by
      rintro ⟨rfl, rfl⟩; exact h rfl
    simp [Matrix.diagonal_apply_ne _ h, hne]

/-- **The counterexample's search success amplitude is exactly `1/√3`, for ALL
`(γ, τ)`.**  The search Hamiltonian is diagonal, so the evolution is a diagonal
matrix of unit-modulus phases: the only nonzero term in the row sum is the
diagonal entry `exp(-iτ(γ·A₀₀+1))`, of modulus `1`. -/
private theorem cexA_searchSuccess (γ τ : ℝ) :
    searchSuccess cexA 0 γ τ = 1 / Real.sqrt 3 := by
  have hdiag : -(Complex.I * (τ : ℂ)) • searchHamiltonian cexA 0 γ
      = Matrix.diagonal (fun i => -(Complex.I * (τ : ℂ)) *
          ((γ : ℂ) * cexD i + if i = (0 : Fin 3) then 1 else 0)) := by
    rw [cexA_searchHamiltonian γ, ← Matrix.diagonal_smul]
    congr 1
  have hexp : searchEvolve cexA 0 γ τ
      = Matrix.diagonal (fun i => NormedSpace.exp (-(Complex.I * (τ : ℂ)) *
          ((γ : ℂ) * cexD i + if i = (0 : Fin 3) then 1 else 0))) := by
    unfold searchEvolve
    rw [hdiag, Matrix.exp_diagonal, Pi.exp_def]
  have hsum : (∑ v, searchEvolve cexA 0 γ τ 0 v)
      = NormedSpace.exp (-(Complex.I * (τ : ℂ) * ((1 : ℝ) : ℂ))) := by
    rw [hexp, Finset.sum_eq_single (0 : Fin 3)]
    · rw [Matrix.diagonal_apply_eq]
      congr 1
      simp [cexD]
    · intro b _ hb
      exact Matrix.diagonal_apply_ne _ (Ne.symm hb)
    · intro h; exact absurd (Finset.mem_univ _) h
  show ‖(1 / Real.sqrt ((Fintype.card (Fin 3) : ℝ)) : ℂ)
      * ∑ v, searchEvolve cexA 0 γ τ 0 v‖ = 1 / Real.sqrt 3
  rw [hsum, norm_mul, norm_exp_neg_I_mul τ 1, mul_one]
  rw [Fintype.card_fin]
  rw [norm_div, norm_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  norm_num

/-- **REFUTATION of the gap-only optimal-search-time claim.**  The statement
"every Hermitian `A` with a strictly dominant eigenvalue magnitude at some
index `p` admits `(γ, τ)` with `searchSuccess A w γ τ ≥ 1/√2`" is **false**.
Witness:
`A = diag(0,0,2)` on `Fin 3`, marked vertex `0`.  The gap hypothesis holds
(spectrum `{0,0,2}`), but the success amplitude is `1/√3 < 1/√2` for *every*
`(γ, τ)`: the principal eigenvector of `A` is a standard basis vector, not the
uniform start state, and the diagonal search Hamiltonian moves no amplitude at
all.  This is exactly why the CNO regime (arXiv:2004.12686) demands the
**uniform principal eigenvector** hypothesis in addition to the spectral gap. -/
theorem not_searchSuccess_optimal_time_of_gap_only :
    ¬ (∀ (A : Matrix (Fin 3) (Fin 3) ℂ) (w : Fin 3) (hA : A.IsHermitian)
        (p : Fin 3),
        (∀ i, i ≠ p → |hA.eigenvalues i| < |hA.eigenvalues p|) →
        ∃ γ τ : ℝ, searchSuccess A w γ τ ≥ 1 / Real.sqrt 2) := by
  intro h
  obtain ⟨p, hp⟩ := cexA_exists_principal
  obtain ⟨γ, τ, hge⟩ := h cexA 0 cexA_isHermitian p hp
  rw [cexA_searchSuccess γ τ] at hge
  have h23 : Real.sqrt 2 < Real.sqrt 3 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have : (1 : ℝ) / Real.sqrt 3 < 1 / Real.sqrt 2 :=
    one_div_lt_one_div_of_lt h2pos h23
  linarith

end GapOnlyCounterexample

/-! ## 6. The optimal-search-time statement (CNO interface).

The content of spatial-search optimality — constant success amplitude
in time `O(√N)` — is the spectral/perturbation analysis of Chakraborty–Novo–
Roland (arXiv:2004.12686, Thms 1–2; the constant-gap regime of Childs–Goldstone
quant-ph/0306054).  Section 5 shows the eigenvalue gap alone is **not enough**;
the analysis consumes, exactly as in `Graphplay.Search.CNO`:

1. **uniform principal eigenvector / regularity** — the all-ones vector is an
   eigenvector of `A` (equivalently, all row sums equal `lam`; this is the
   start-state/principal-eigenvector alignment the counterexample violates), and
2. **the spectral gap** — every other spectrum point is strictly smaller in
   magnitude than `lam` (the `CNOSpectralRatio < 1` condition, here phrased
   choice-free via `spectrum ℝ A` rather than an eigenvalue-indexing function).

Following the repo's cited-typeclass pattern (`CCTVZBoseMesnerFR`,
`CNOOptimalSearch`), the deep dynamical bound is carried as a `Prop`-valued
interface whose single field is the verbatim cited implication. -/

/-- **CNO optimal-search dynamics as a cited interface** (Chakraborty–Novo–
Roland arXiv:2004.12686 Thms 1–2; Childs–Goldstone quant-ph/0306054), in the
loopy-layer convention `H_γ = γA + |w⟩⟨w|` (the time reversal of CNO's
`-γA - |w⟩⟨w|`; success amplitudes are moduli, invariant under `H ↦ -H` up to
the Hermitian transpose, so the cited analysis covers both signs).

The field is *exactly* the cited implication: a Hermitian movement matrix whose
**uniform vector is an eigenvector** with **strictly dominant** eigenvalue
magnitude (the constant-gap regime) supports search reaching amplitude `≥ 1/√2`
at some coupling `γ > 0` within the `O(√N)` budget `τ ≤ π√N`.

Scope of the interface: (i) the hypothesis side is inhabited where the
conclusion is not free: `cnoLoopy_hypotheses_inhabited` exhibits the all-ones
matrix on `Fin 3` (uniform eigenvector, eigenvalue `3`, spectrum `{0, 3}`),
where the bare start overlap is only `1/√3 < 1/√2`.  (ii) The interface is
satisfiable: a proven `Fin 1` instance is provided below.  (iii) The dropped
gap-only hypothesis is *necessary*: `not_searchSuccess_optimal_time_of_gap_only`.
(iv) The repo's fully proven `K_n` flagships
(`Graphplay.complete_graph_optimal_search` in `Graphplay.Search.CNO`,
`quantum_search_quadratic_advantage` in
`Graphplay.Integrations.QuantumAdvantage`) machine-check the corresponding
statement in the `-γA - |w⟩⟨w|` convention, reduced there to a `2×2` Rabi
block. -/
class CNOLoopyOptimalSearch (V : Type u) [Fintype V] [DecidableEq V] : Prop where
  /-- Verbatim CNO arXiv:2004.12686 Thms 1–2 (constant-gap regime), loopy
  convention: uniform principal eigenvector + spectral gap ⟹ optimal-time
  constant-amplitude search. -/
  optimal_time_of_uniform_principal :
    ∀ (A : Matrix V V ℂ) (w : V) (lam : ℝ),
      A.IsHermitian →
      A *ᵥ (fun _ => (1 : ℂ)) = (lam : ℂ) • (fun _ => (1 : ℂ)) →
      0 < |lam| →
      (∀ μ ∈ spectrum ℝ A, μ ≠ lam → |μ| < |lam|) →
      ∃ γ τ : ℝ, 0 < γ ∧ τ ≤ Real.pi * Real.sqrt (Fintype.card V) ∧
        1 / Real.sqrt 2 ≤ searchSuccess A w γ τ

/-- **Optimal search time (CNO statement, via the cited
interface).**  Let `A` be Hermitian such that the uniform vector is an
eigenvector with eigenvalue `lam` (regularity / start-state–principal-
eigenvector alignment) and every other spectrum point is strictly dominated in
magnitude (the CNO constant-gap condition).  Then some coupling `γ > 0` and
time `τ ≤ π√N` reach success amplitude `≥ 1/√2`.

Both hypotheses are load-bearing: dropping the alignment hypothesis makes the
statement **false** (`not_searchSuccess_optimal_time_of_gap_only`), and
dropping the gap makes it false already for `A = 0` (pure oracle, no mixing).
The quantitative dynamical content is CNO arXiv:2004.12686 Thms 1–2, carried by
`[CNOLoopyOptimalSearch V]`; the theorem is its direct discharge. -/
theorem searchSuccess_optimal_time [CNOLoopyOptimalSearch V]
    (A : Matrix V V ℂ) (w : V) (lam : ℝ)
    (hA : A.IsHermitian)
    (huniform : A *ᵥ (fun _ => (1 : ℂ)) = (lam : ℂ) • (fun _ => (1 : ℂ)))
    (hlam : 0 < |lam|)
    (hgap : ∀ μ ∈ spectrum ℝ A, μ ≠ lam → |μ| < |lam|) :
    ∃ γ τ : ℝ, 0 < γ ∧ τ ≤ Real.pi * Real.sqrt (Fintype.card V) ∧
      1 / Real.sqrt 2 ≤ searchSuccess A w γ τ :=
  CNOLoopyOptimalSearch.optimal_time_of_uniform_principal A w lam hA huniform
    hlam hgap

/-- **Hypothesis-side inhabitation on a host where the conclusion is not
free.**  The all-ones matrix `J` on `Fin 3` satisfies every hypothesis of
`searchSuccess_optimal_time`: it is Hermitian, the uniform vector is an
eigenvector with eigenvalue `lam = 3`, and the rest of the spectrum (`{0}`,
read off from `det(μ·1 − J) = μ²(μ−3)`) is strictly dominated.  Since the bare
`τ = 0` start overlap on three vertices is `1/√3 < 1/√2`, the conditional
theorem demands dynamics there: neither hypothesis nor conclusion is
degenerate. -/
theorem cnoLoopy_hypotheses_inhabited :
    ∃ (A : Matrix (Fin 3) (Fin 3) ℂ) (lam : ℝ),
      A.IsHermitian ∧
      A *ᵥ (fun _ => (1 : ℂ)) = (lam : ℂ) • (fun _ => (1 : ℂ)) ∧
      0 < |lam| ∧
      (∀ μ ∈ spectrum ℝ A, μ ≠ lam → |μ| < |lam|) := by
  refine ⟨Matrix.of (fun _ _ => (1 : ℂ)), 3, ?_, ?_, by norm_num, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · funext v
    simp [Matrix.mulVec, dotProduct]
  · intro μ hμ hne
    have hμC : ((μ : ℝ) : ℂ) ∈ spectrum ℂ (Matrix.of (fun _ _ => (1 : ℂ)) :
        Matrix (Fin 3) (Fin 3) ℂ) :=
      (spectrum.algebraMap_mem_iff ℂ).mpr hμ
    rw [spectrum.mem_iff] at hμC
    have hdet : (algebraMap ℂ (Matrix (Fin 3) (Fin 3) ℂ) ((μ : ℝ) : ℂ)
        - Matrix.of (fun _ _ => (1 : ℂ))).det = 0 := by
      by_contra hne0
      exact hμC ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr hne0))
    have hpoly : ((μ : ℂ)) ^ 2 * ((μ : ℂ) - 3) = 0 := by
      rw [Matrix.det_fin_three] at hdet
      simp [Matrix.sub_apply, Matrix.algebraMap_matrix_apply,
        Matrix.of_apply] at hdet
      linear_combination hdet
    rcases mul_eq_zero.mp hpoly with h | h
    · have h0 : (μ : ℂ) = 0 := by
        exact pow_eq_zero_iff (by norm_num) |>.mp h
      have : μ = 0 := by exact_mod_cast h0
      rw [this]
      norm_num
    · exact absurd (by exact_mod_cast sub_eq_zero.mp h : μ = 3) hne

/-- **Satisfiability of the interface: the one-vertex instance.**  On a single
vertex the uniform state *is* the marked vertex; the evolution at `τ = 0` is
the identity and the success amplitude is `1 ≥ 1/√2` within the budget
`0 ≤ π√1`.  The class is provably consistent. -/
instance : CNOLoopyOptimalSearch (Fin 1) where
  optimal_time_of_uniform_principal := by
    intro A w lam _ _ _ _
    refine ⟨1, 0, one_pos, by positivity, ?_⟩
    have hev : searchEvolve A w 1 0 = 1 := by
      unfold searchEvolve
      rw [show -(Complex.I * ((0 : ℝ) : ℂ)) = (0 : ℂ) by simp, zero_smul,
        NormedSpace.exp_zero]
    have hsum : (∑ v, searchEvolve A w 1 0 w v) = 1 := by
      rw [hev, Fin.sum_univ_one]
      have hw : w = 0 := Subsingleton.elim _ _
      rw [hw]
      exact Matrix.one_apply_eq 0
    show 1 / Real.sqrt 2 ≤
      ‖(1 / Real.sqrt ((Fintype.card (Fin 1) : ℝ)) : ℂ)
        * ∑ v, searchEvolve A w 1 0 w v‖
    rw [hsum, mul_one, Fintype.card_fin]
    rw [norm_div, norm_one, Complex.norm_real, Nat.cast_one, Real.sqrt_one,
      norm_one, div_one]
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [div_le_one h2pos]
    exact h2

end LoopySearch
end Graphplay
