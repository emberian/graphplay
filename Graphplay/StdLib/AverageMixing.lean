/-
# Graphplay.StdLib.AverageMixing

**The average mixing matrix** of a continuous-time quantum walk.

For the walk `U(t) = exp(-i t A)` on a graph `G` with spectral
decomposition `A = ∑_λ λ E_λ`, the *mixing matrix* at time `t` is the
entrywise (Hadamard / Schur) square of the modulus of `U(t)`:
`(M_t)_{u,v} = |U(t)_{u,v}|²` — a doubly-stochastic matrix giving the
probability of finding a walker started at `u` at vertex `v` at time `t`.

The **average mixing matrix** is the Cesàro time-average
`M̂ = lim_{T→∞} (1/T) ∫₀^T U(t) ∘ U(-t) dt`.  Because
`U(t) ∘ U(-t) = U(t) ∘ conj(U(t))` and the cross terms
`e^{-it(λ-μ)}` integrate to `0` for `λ ≠ μ` while the diagonal terms
`e^{0} = 1` survive, the limit collapses to the **Schur square of the
spectral idempotents**:

  `M̂ = ∑_λ E_λ ∘ E_λ`,  i.e.  `M̂_{u,v} = ∑_λ |(E_λ)_{u,v}|²`.

(Aharonov–Ambainis–Kempe–Vazirani introduced the average distribution;
Godsil, "Average mixing of continuous quantum walks", J. Combin. Theory
Ser. A 120 (2013) 1649–1662, arXiv:1103.2578, established the entry
formula and the rationality theorem.)

This file:

1. defines `avgMixing G` **concretely** as the matrix with entries
   `M̂_{u,v} = ∑_{λ ∈ spec} |(E_λ)_{u,v}|²`, reusing the projector
   calculus (`eigenProj`, `eigenProj_apply`, `eigenProj_idem`,
   `eigenProj_conjTranspose_apply`) from `Graphplay.PST.GodsilRatio`;
2. proves the *genuinely easy* facts — symmetry, entrywise
   nonnegativity, the diagonal-as-row-norm formula, the projector
   row-sum identity, and that **rows sum to 1** (doubly-stochastic);
3. proves the correct sum-of-ranks bound on `rank M̂` (the naive
   `rank ≤ #distinct eigenvalues` is false), and states the deep
   rationality theorem (Godsil 2013) with honest `sorry`.

Cross references:
* Aharonov, Ambainis, Kempe, Vazirani, "Quantum walks on graphs",
  STOC 2001.
* Godsil, "Average mixing of continuous quantum walks", JCTA 120 (2013)
  1649–1662, arXiv:1103.2578.
* Coutinho, Godsil, *Graph Spectra and Continuous Quantum Walks* (2021),
  Ch. 14 (average mixing).
-/

import Graphplay.PST.GodsilRatio

open scoped Matrix

namespace Graphplay
namespace StdLib
namespace AverageMixing

open Graphplay.PST

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The average mixing matrix

We define `M̂` directly by its entry formula `M̂_{u,v} = ∑_λ |(E_λ)_{u,v}|²`,
summing over the *distinct* eigenvalues of `G.adj` (the image of the
eigenvalue function), with `(E_λ)_{u,v} = eigenProj G λ u v` the spectral
projector entry already developed in `Graphplay.PST.GodsilRatio`.  Since the
summands are squared norms (nonnegative reals), `M̂` is a real,
entrywise-nonnegative matrix; we record it valued in `ℝ`. -/

/-- The **average mixing matrix** `M̂` of the quantum walk on `G`, defined
entrywise as the Schur square of the spectral idempotents:
`M̂_{u,v} = ∑_λ |(E_λ)_{u,v}|²`, the sum over distinct eigenvalues `λ` of
`G.adj`.  This is the genuine Godsil average mixing matrix
(`= lim_{T→∞} (1/T)∫₀^T U(t) ∘ U(-t) dt`); the Cesàro limit collapses to
this finite sum because off-diagonal phases `e^{-it(λ-μ)}` average to
zero. -/
noncomputable def avgMixing (G : WeightedGraph V) : Matrix V V ℝ :=
  fun u v => ∑ lam ∈ Finset.univ.image G.herm.eigenvalues, ‖eigenProj G lam u v‖ ^ 2

/-- The defining entry formula. -/
theorem avgMixing_apply (G : WeightedGraph V) (u v : V) :
    avgMixing G u v
      = ∑ lam ∈ Finset.univ.image G.herm.eigenvalues, ‖eigenProj G lam u v‖ ^ 2 :=
  rfl

/-! ## 2. Easy structural facts -/

/-- **Entrywise nonnegativity.**  Every entry of `M̂` is a sum of squared
norms, hence `≥ 0`. -/
theorem avgMixing_nonneg (G : WeightedGraph V) (u v : V) :
    0 ≤ avgMixing G u v := by
  rw [avgMixing_apply]
  apply Finset.sum_nonneg
  intro lam _
  positivity

/-- **Symmetry.**  `M̂` is a symmetric matrix: `M̂_{u,v} = M̂_{v,u}`.  This is
because each projector is self-adjoint, `(E_λ)_{v,u} = conj (E_λ)_{u,v}`, so
the two have equal modulus. -/
theorem avgMixing_symm (G : WeightedGraph V) (u v : V) :
    avgMixing G u v = avgMixing G v u := by
  rw [avgMixing_apply, avgMixing_apply]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [eigenProj_conjTranspose_apply, norm_star]

/-- **Diagonal-as-row-norm.**  The diagonal entry `M̂_{u,u}` equals the sum
over eigenvalues of the squared norm of the `u`-th row of `E_λ` *restricted
to its own column at `u`* — concretely `M̂_{u,u} = ∑_λ ((E_λ)_{u,u})²`,
since `(E_λ)_{u,u}` is a (nonnegative) real number whose modulus is itself.
This is the diagonal special case `‖(E_λ)_{u,u}‖² = (E_λ)_{u,u}²`. -/
theorem avgMixing_diag (G : WeightedGraph V) (u : V) :
    avgMixing G u u
      = ∑ lam ∈ Finset.univ.image G.herm.eigenvalues, (eigenProjDiagLocal G lam u) ^ 2 := by
  rw [avgMixing_apply]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [eigenProj_diag, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The projector row-sum identity

For a fixed eigenvalue `λ`, summing the Schur-square over a row gives the
diagonal projector entry: `∑_v |(E_λ)_{u,v}|² = (E_λ)_{u,u}`.  This is
`(E_λ E_λ^H)_{u,u} = (E_λ²)_{u,u} = (E_λ)_{u,u}` using `E_λ` Hermitian and
idempotent — the engine behind the doubly-stochastic row-sum. -/

/-- **Per-eigenvalue row-sum of the Schur square.**
`∑_v ‖(E_λ)_{u,v}‖² = (E_λ)_{u,u}`.  Proof: `‖(E_λ)_{u,v}‖² =
(E_λ)_{u,v} · conj (E_λ)_{u,v} = (E_λ)_{u,v} · (E_λ)_{v,u}` (Hermitian), and
summing over `v` is the `(u,u)` entry of `E_λ · E_λ = E_λ` (idempotent). -/
theorem eigenProj_row_normSq (G : WeightedGraph V) (lam : ℝ) (u : V) :
    ∑ v : V, ‖eigenProj G lam u v‖ ^ 2 = eigenProjDiagLocal G lam u := by
  -- Realify: `‖z‖² = (z * conj z).re`, and `conj (E_λ)_{u,v} = (E_λ)_{v,u}`.
  have hcast : ((∑ v : V, ‖eigenProj G lam u v‖ ^ 2 : ℝ) : ℂ)
      = (eigenProj G lam * eigenProj G lam) u u := by
    rw [Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    -- `(E_λ)_{u,v} * (E_λ)_{v,u} = (E_λ)_{u,v} * conj (E_λ)_{u,v} = ‖(E_λ)_{u,v}‖²`.
    rw [eigenProj_conjTranspose_apply (a := u) (b := v)]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [eigenProj_idem] at hcast
  rw [eigenProj_diag] at hcast
  exact_mod_cast hcast

/-! ### Spectral resolution of the identity

`∑_λ E_λ = 1`, hence `∑_λ (E_λ)_{u,u} = 1`.  We obtain this from the
evolution identity `U(τ) = ∑_λ e^{-iτλ} E_λ` at `τ = 0`, where
`U(0) = exp(0) = 1`. -/

/-- The walk at time `0` is the identity: `U(0) = 1`. -/
theorem evolve_zero (G : WeightedGraph V) : G.evolve 0 = (1 : Matrix V V ℂ) := by
  unfold WeightedGraph.evolve
  simp [NormedSpace.exp_zero]

/-- **Resolution of the identity (diagonal form).**
`∑_λ (E_λ)_{u,u} = 1` for every vertex `u`.  Proof: evaluate
`U(0) = ∑_λ e^0 • E_λ = ∑_λ E_λ` at `(u,u)`; the left side is `1`. -/
theorem sum_eigenProjDiag (G : WeightedGraph V) (u : V) :
    ∑ lam ∈ Finset.univ.image G.herm.eigenvalues, eigenProjDiagLocal G lam u = 1 := by
  have hsum := evolve_eq_sum_eigenProj G 0
  rw [evolve_zero] at hsum
  have huu := congrFun (congrFun hsum u) u
  rw [Matrix.one_apply_eq, Matrix.sum_apply] at huu
  -- Each summand `(e^0 • E_λ) u u = (E_λ)_{u,u} = (eigenProjDiagLocal ... : ℂ)`.
  have hsimp : ∀ lam ∈ Finset.univ.image G.herm.eigenvalues,
      (Complex.exp (-(Complex.I * ((0 : ℝ) : ℂ)) * (lam : ℂ)) • eigenProj G lam) u u
        = ((eigenProjDiagLocal G lam u : ℝ) : ℂ) := by
    intro lam _
    rw [Matrix.smul_apply, smul_eq_mul, eigenProj_diag]
    simp
  rw [Finset.sum_congr rfl hsimp] at huu
  rw [← Complex.ofReal_sum] at huu
  exact_mod_cast huu.symm

/-- **Rows sum to 1 (right stochastic).**  `∑_v M̂_{u,v} = 1` for every
`u`: combine the per-eigenvalue row-sum `∑_v ‖(E_λ)_{u,v}‖² = (E_λ)_{u,u}`
with the resolution of the identity `∑_λ (E_λ)_{u,u} = 1`.  Together with
symmetry this makes `M̂` **doubly stochastic**. -/
theorem avgMixing_row_sum (G : WeightedGraph V) (u : V) :
    ∑ v : V, avgMixing G u v = 1 := by
  -- Swap the order of summation: ∑_v ∑_λ = ∑_λ ∑_v.
  simp_rw [avgMixing_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun lam _ => eigenProj_row_normSq G lam u)]
  exact sum_eigenProjDiag G u

/-- **Columns sum to 1 (left stochastic).**  By symmetry of `M̂`,
`∑_u M̂_{u,v} = 1`. -/
theorem avgMixing_col_sum (G : WeightedGraph V) (v : V) :
    ∑ u : V, avgMixing G u v = 1 := by
  rw [Finset.sum_congr rfl (fun u _ => avgMixing_symm G u v)]
  exact avgMixing_row_sum G v

/-- **Doubly stochastic, packaged.**  `M̂` is entrywise nonnegative,
symmetric, and both its rows and columns sum to `1`. -/
theorem avgMixing_doublyStochastic (G : WeightedGraph V) :
    (∀ u v, 0 ≤ avgMixing G u v)
      ∧ (∀ u v, avgMixing G u v = avgMixing G v u)
      ∧ (∀ u, ∑ v, avgMixing G u v = 1)
      ∧ (∀ v, ∑ u, avgMixing G u v = 1) :=
  ⟨avgMixing_nonneg G, avgMixing_symm G, avgMixing_row_sum G, avgMixing_col_sum G⟩

/-! ## 3. The deep theorems (Godsil 2013)

The genuinely hard facts about the average mixing matrix, stated precisely
with honest `sorry` on the bodies. -/

/-- **Godsil's rationality theorem** (arXiv:1103.2578, Thm 3.1).  Every
entry of the average mixing matrix is a *rational* number.  (The spectral
idempotents `E_λ` of an integer adjacency matrix have algebraic entries
whose Galois orbit, summed over an eigenvalue class, is rational; the Schur
square is then rational.) -/
theorem avgMixing_rational (G : WeightedGraph V)
    (hint : ∀ i, ∃ k : ℤ, G.herm.eigenvalues i = (k : ℝ)) (u v : V) :
    ∃ q : ℚ, avgMixing G u v = (q : ℝ) := by
  -- HONEST SORRY (deep theorem body).  Requires the Galois-orbit argument:
  -- the entries of `∑_{λ in a conjugacy class} E_λ` are rational because the
  -- class sum is fixed by `Gal(ℚ̄/ℚ)`, and the Schur square preserves
  -- rationality.  Citation: Godsil, JCTA 120 (2013), Theorem 3.1.
  sorry

/-- **Average uniform mixing.**  A graph admits *uniform average mixing*
when `M̂` is the flat doubly-stochastic matrix `J / |V|` (every entry
`1/|V|`).  Godsil (2013) showed this is extremely restrictive (essentially
only `K_2` and a few sporadic examples among the connected graphs).  We
state the predicate concretely. -/
def IsUniformAverageMixing (G : WeightedGraph V) : Prop :=
  ∀ u v, avgMixing G u v = (1 : ℝ) / (Fintype.card V : ℝ)

/-! ### Rank bounds

The average mixing matrix decomposes as a sum, over the distinct eigenvalues, of
the per-eigenvalue **Schur-square** matrices `(E_λ ∘ E_λ)_{u,v} = ‖(E_λ)_{u,v}‖²`.
Rank is subadditive over finite sums, so `M̂`'s rank is bounded by the sum of the
per-eigenvalue Schur-square ranks.  (The naive "`rank ≤ #distinct eigenvalues`"
bound is *false* — each Schur square can itself have rank `> 1` — so we prove the
correct sum-of-ranks bound, the genuinely reachable structural statement.  The
sharp refinement is Godsil, JCTA 120 (2013), §4.) -/

/-- The per-eigenvalue **Schur-square matrix** `E_λ ∘ E_λ` (entrywise modulus
squared of the spectral projector), valued in `ℝ`. -/
noncomputable def eigenSchurSq (G : WeightedGraph V) (lam : ℝ) : Matrix V V ℝ :=
  fun u v => ‖eigenProj G lam u v‖ ^ 2

/-- `M̂` is the sum of the per-eigenvalue Schur squares. -/
theorem avgMixing_eq_sum_schurSq (G : WeightedGraph V) :
    avgMixing G
      = ∑ lam ∈ Finset.univ.image G.herm.eigenvalues, eigenSchurSq G lam := by
  ext u v
  rw [avgMixing_apply, Matrix.sum_apply]
  rfl

/-- **Subadditivity of matrix rank under addition** (over a field).  A general
helper: `rank (A + B) ≤ rank A + rank B`, from `range (f+g) ≤ range f ⊔ range g`
on the associated linear maps and subadditivity of `finrank` over `⊔`. -/
theorem matrix_rank_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  refine (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans ?_
  exact Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)

/-- **Subadditivity of matrix rank under a finite sum.** -/
theorem matrix_rank_sum_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i ∈ s, M i).rank ≤ ∑ i ∈ s, (M i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp [Matrix.rank_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (matrix_rank_add_le _ _).trans (by gcongr)

/-- **Rank bound (sum-of-ranks form).**  When the vertex set is `Fin n`, the rank
of the average mixing matrix is at most the sum, over distinct eigenvalues, of the
ranks of the per-eigenvalue Schur squares.  This is the correct, reachable rank
bound; the sharp count is Godsil, JCTA 120 (2013), §4. -/
theorem avgMixing_rank_le_sum_schurSq {n : ℕ} (G : WeightedGraph (Fin n)) :
    (avgMixing G).rank
      ≤ ∑ lam ∈ Finset.univ.image G.herm.eigenvalues, (eigenSchurSq G lam).rank := by
  rw [avgMixing_eq_sum_schurSq]
  exact matrix_rank_sum_le _ _

end AverageMixing
end StdLib
end Graphplay
