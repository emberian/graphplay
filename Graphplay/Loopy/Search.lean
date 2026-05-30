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

The genuinely deep "optimal search time" claim (the spectral / perturbation
analysis converting a spectral-gap bound into a constant-amplitude statement) is
left as an honest `sorry` — `searchSuccess_optimal_time` — flagged as such.

References: Childs–Goldstone (quant-ph/0306054); CNO (arXiv:2004.12686);
Laplacian-walk search (arXiv:1409.5840); lackadaisical walk Wong
(arXiv:1706.06939); the diagonal-shift global-phase engine is
`Graphplay.PST.DiagonalShift.norm_exp_shifted_entry_eq` / `exp_add_smul_one`.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
evolution of `−A`.  The `−A` is a genuine **time reversal** of the adjacency
walk — we are honest that this is `−A`, not `A`; the modulus equality is stated
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
contributes only a unit-modulus global phase (stripped via §2).  This is the
precise, provable form — we do **not** silently identify `−A` with `A` (the sign
is a real time reversal, exactly as documented in `Graphplay.Loopy.Laplacian`). -/
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
time-reversed adjacency walk.  Again, the `−A` is kept honest. -/
theorem searchSuccess_laplacian_eq_of_regular (G : WeightedGraph V) (d : ℂ)
    (hreg : G.isRegular d) (w : V) (γ τ : ℝ) :
    searchSuccess (WeightedGraph.laplacian G).adj w γ τ
      = searchSuccess (-G.adj) w γ τ := by
  rw [laplacian_movement_eq_of_regular G d hreg]
  exact searchSuccess_shift_eq (-G.adj) w γ d.re τ

/-! ## 5. The deep optimal-search-time claim (honest `sorry`). -/

/-- **Optimal search time (deep, honest `sorry`).**  The genuine content of
spatial-search optimality — that there exist tuning parameters `(γ, τ)` with
`τ = O(√(n/|marked|))` achieving constant success amplitude — requires the
spectral / perturbation analysis of the CNO program (arXiv:2004.12686) and is
**not** a consequence of the diagonal-shift machinery above.  We state it
precisely and leave it as an honest `sorry`; the diagonal-shift results in §§2–4
are genuinely closed and are exactly the structural facts this would consume
(they reduce the Laplacian / lackadaisical cases to the adjacency case).

Note on hypotheses: the conclusion is **false** without a spectral hypothesis
(e.g. for `A = 0` the search Hamiltonian is the pure oracle `|w⟩⟨w|`, whose
walk from the uniform state does *not* reach amplitude `1/√2` for large `n`).
We therefore require `A` Hermitian together with the CNO constant-spectral-gap
regime, packaged as the hypothesis `hgap`: every non-principal eigenvalue of `A`
is strictly smaller in magnitude than the principal one at index `p` (the
all-ones eigenvector index for a regular graph).  This is precisely the
`CNOSpectralRatio < 1` condition of `Graphplay.Search.CNO`, and is what the
deferred perturbation analysis consumes. -/
theorem searchSuccess_optimal_time (A : Matrix V V ℂ) (w : V)
    (hA : A.IsHermitian) (p : V)
    (hgap : ∀ i, i ≠ p → |hA.eigenvalues i| < |hA.eigenvalues p|) :
    ∃ γ τ : ℝ, searchSuccess A w γ τ ≥ 1 / Real.sqrt 2 := by
  sorry

end LoopySearch
end Graphplay
