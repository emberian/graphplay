/-
# Graphplay.PST.Cospectrality

**Strong cospectrality** of vertex pairs in a Hermitian-weighted graph: the
spectral-linear-algebra prerequisite for the existence of perfect state
transfer (PST) between two vertices.

Two vertices `u, v` of a weighted graph `G` are **strongly cospectral** iff
for every eigenspace `E_λ` of `G.adj`, the projections `π_λ |u⟩` and
`π_λ |v⟩` are parallel.  In the real (orthogonal) case, parallel means equal
up to a sign `±1`; in the complex / chiral case, parallel means equal up to a
unit-modulus complex phase.

The classical algebraic-graph-theoretic source for this notion is

* Godsil, Royle, *Algebraic Graph Theory* (Springer GTM 207, 2001), Chap. 8;
* Coutinho, Godsil, *Perfect State Transfer on Graphs*, 2016 (graduate
  monograph, see esp. Chapters 3-4);
* Bachman, Tamon, et al., "Perfect state transfer on quotient graphs"
  (arXiv:1108.0339);
* Christandl, Datta, Ekert, Landahl, "Perfect state transfer in quantum
  spin networks" (Phys. Rev. Lett. 92 187902, 2004), where strong
  cospectrality for endpoints of `P_n` is implicit in the Chebyshev
  eigenstructure.

The deliverables of this file are:

1. `IsStronglyCospectral`: parallelism of all eigenspace projections.
2. `isStronglyCospectral_iff_of_cospectral`: under cospectrality, the
   equivalence with the textbook "matched off-diagonal entry" characterization
   familiar from Godsil-Royle / Coutinho-Godsil.
3. `IsStronglyCospectral.isPST_iff_godsilRatio`: the PST-existence
   characterization combining strong cospectrality with the Godsil ratio
   condition on eigenvalues (proof tagged for sibling L2).
4. `Hom.preserves_stronglyCospectral`: equitable-partition functoriality:
   an equitable partition whose cell map separates `u` and `v` lifts
   strong cospectrality from `u, v` upstairs to `cells u, cells v`
   downstairs on `P.quotient`.
5. Concrete examples: the endpoint pair of a path graph `P_n` is strongly
   cospectral (Chebyshev / Christandl-Datta-Ekert-Landahl).
6. `IsPhantomSymmetric`: strong cospectrality without an underlying graph
   automorphism witnessing it; the existence theorem due to Bachman-Tamon
   (arXiv:1108.0339).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.NumberTheory.Niven
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST
import Graphplay.PST.GodsilRatio

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Eigenspace projections of a Hermitian adjacency matrix

For a Hermitian matrix `A = G.adj`, Mathlib gives us an orthonormal eigenvector
basis via `Matrix.IsHermitian.eigenvectorBasis`.  For each (real) eigenvalue
`λ ∈ Set.range hA.eigenvalues`, the **spectral projector** `P_λ` onto the
eigenspace `E_λ` is the rank-one (or higher) projector summing the outer
products `|ψ_i⟩⟨ψ_i|` over those basis indices `i` with `hA.eigenvalues i = λ`.

We package the `(u, v)`-matrix entry of the projector — the data that matters
for cospectrality — as `eigenProjEntry`.
-/

/-- The `(u, v)`-entry of the spectral projector onto the `λ`-eigenspace of
`G.adj`, expressed in the eigenvector basis of Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`.  Concretely, this is

  `∑_{i : hA.eigenvalues i = λ} ⟨e_u, ψ_i⟩ ⟨ψ_i, e_v⟩`,

equivalently the `(u, v)`-entry of the matrix `∑_i [eigenvalues i = λ] · π_i`,
where `π_i = |ψ_i⟩⟨ψ_i|`. -/
noncomputable def eigenProjEntry (G : WeightedGraph V) (lam : ℝ) (u v : V) : ℂ :=
  ∑ i : V, if G.herm.eigenvalues i = lam
    then (G.herm.eigenvectorBasis i) u * star ((G.herm.eigenvectorBasis i) v)
    else 0

/-- Specialization of `eigenProjEntry` to the diagonal: the squared length of
the projection of `|u⟩` onto the `λ`-eigenspace, equivalently
`⟨u, P_λ u⟩`. -/
noncomputable def eigenProjDiag (G : WeightedGraph V) (lam : ℝ) (u : V) : ℝ :=
  ((eigenProjEntry G lam u u).re)

/-! ### Elementary algebra of `eigenProjEntry`

The spectral projectors `E_λ` of a Hermitian matrix are self-adjoint
idempotents, so their matrix entries satisfy the Gram identities used
throughout Coutinho's Chapter 2.  We record the two we need directly from the
defining sum: conjugate-symmetry `(E_λ)_{v,u} = conj (E_λ)_{u,v}`, and the fact
that the diagonal entry `(E_λ)_{u,u} = ∑_i |ψ_i(u)|²` is a nonnegative real. -/

/-- **Conjugate symmetry of the projector entries** (`E_λ` is Hermitian):
`(E_λ)_{v,u} = conj (E_λ)_{u,v}`. -/
theorem eigenProjEntry_conj_symm (G : WeightedGraph V) (lam : ℝ) (u v : V) :
    eigenProjEntry G lam v u = star (eigenProjEntry G lam u v) := by
  unfold eigenProjEntry
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : G.herm.eigenvalues i = lam
  · simp only [h, if_true]
    rw [star_mul', star_star, mul_comm]
  · simp only [h, if_false, star_zero]

/-- The diagonal projector entry is its own real part as a complex number:
`(E_λ)_{u,u} = ((E_λ)_{u,u}.re : ℂ)`, because `(E_λ)_{u,u} = ∑_i |ψ_i(u)|²` is
a nonnegative real. -/
theorem eigenProjEntry_diag_eq_ofReal (G : WeightedGraph V) (lam : ℝ) (u : V) :
    eigenProjEntry G lam u u = (eigenProjDiag G lam u : ℂ) := by
  have hself : eigenProjEntry G lam u u = star (eigenProjEntry G lam u u) :=
    eigenProjEntry_conj_symm G lam u u
  -- a complex number equal to its own conjugate is real
  have : (eigenProjEntry G lam u u).im = 0 := by
    have := hself
    rw [Complex.ext_iff] at this
    have him := this.2
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith [him]
  unfold eigenProjDiag
  apply Complex.ext
  · simp
  · simp [this]

/-- The diagonal projector entry is nonnegative: `(E_λ)_{u,u} = ∑_i |ψ_i(u)|² ≥ 0`. -/
theorem eigenProjDiag_nonneg (G : WeightedGraph V) (lam : ℝ) (u : V) :
    0 ≤ eigenProjDiag G lam u := by
  unfold eigenProjDiag eigenProjEntry
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  by_cases h : G.herm.eigenvalues i = lam
  · simp only [h, if_true]
    -- `ψ_i(u) * conj (ψ_i(u)) = |ψ_i(u)|² ≥ 0`
    rw [Complex.star_def, Complex.mul_conj]
    simp only [Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · simp only [h, if_false, Complex.zero_re, le_refl]

/-! ## Strong cospectrality

The clean definition is "the two projected rays coincide as one-dimensional
complex subspaces, for every eigenspace".  Equivalently, the vectors
`(P_λ u, P_λ v)` are linearly dependent for every `λ`.  Equivalently
(by Cauchy-Schwarz / equality in `|⟨a, b⟩|^2 ≤ ⟨a, a⟩ ⟨b, b⟩`), there exists a
unit-modulus complex scalar `ε_λ` such that the off-diagonal projector entry
`⟨u, P_λ v⟩` equals `ε_λ √(⟨u, P_λ u⟩ ⟨v, P_λ v⟩)`.

In the real / orthogonal case the phase `ε_λ` is constrained to `±1`; in the
complex / chiral case it ranges over the unit circle.  We give both the
abstract "parallelism" definition and the explicit diagonal-and-phase
characterization.
-/

/-- `u` and `v` are **strongly cospectral** in `G` if, for every eigenvalue
`λ` of `G.adj` (real, since `G.adj` is Hermitian), the projections of `|u⟩`
and `|v⟩` onto the `λ`-eigenspace are parallel as complex vectors:
the cross entry `⟨u, P_λ v⟩` is, up to a unit-modulus phase, the geometric
mean of the diagonal entries `⟨u, P_λ u⟩` and `⟨v, P_λ v⟩`.

This is the spectral characterization underlying *all* PST-existence
theorems for continuous-time quantum walks on Hermitian-weighted graphs:
see Godsil-Royle (Algebraic Graph Theory) Chap. 8 and Coutinho-Godsil
(*PST on graphs*, 2016) for the real-symmetric version, and the chiral
extension in Bachman-Tamon (arXiv:1108.0339). -/
def IsStronglyCospectral (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
    ∃ ε : ℂ, ‖ε‖ = 1 ∧
      eigenProjEntry G lam u v
        = ε * Complex.ofReal
            (Real.sqrt (eigenProjDiag G lam u * eigenProjDiag G lam v))

/-! ### Bridge to the `eigU`-coordinate projector (sibling `GodsilRatio`)

The projector entries here, defined through Mathlib's `eigenvectorBasis`,
coincide with the `eigU`-coordinate entries of the sibling module
`Graphplay.PST.GodsilRatio`, because `eigenvectorUnitary i j = eigenvectorBasis
j i` definitionally.  This lets us transport the *unconditional* forward
extraction `PST ⇒ strong cospectrality` (proven there via the spectral-projector
algebra) into this module's `eigenProjEntry`/`eigenProjDiag` language. -/

/-- The projector entry of this module equals the `eigU`-coordinate entry of
`GodsilRatio`. -/
theorem eigenProjEntry_eq_local (G : WeightedGraph V) (lam : ℝ) (u v : V) :
    eigenProjEntry G lam u v = Graphplay.PST.eigenProjEntryLocal G lam u v := by
  unfold eigenProjEntry Graphplay.PST.eigenProjEntryLocal Graphplay.PST.eigU
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1

/-- The diagonal projector entry of this module equals the `GodsilRatio` one. -/
theorem eigenProjDiag_eq_local (G : WeightedGraph V) (lam : ℝ) (u : V) :
    eigenProjDiag G lam u = Graphplay.PST.eigenProjDiagLocal G lam u := by
  unfold eigenProjDiag
  rw [eigenProjEntry_eq_local, Graphplay.PST.eigenProjEntryLocal_self, Complex.ofReal_re]

/-- This module's `IsStronglyCospectral` is propositionally equal to the
`GodsilRatio` one (the definitions differ only by the bridged projector
entries). -/
theorem isStronglyCospectral_iff_local (G : WeightedGraph V) (u v : V) :
    IsStronglyCospectral G u v ↔ Graphplay.PST.IsStronglyCospectral G u v := by
  unfold IsStronglyCospectral Graphplay.PST.IsStronglyCospectral
  refine forall_congr' (fun lam => imp_congr_right (fun _ => ?_))
  rw [eigenProjEntry_eq_local, eigenProjDiag_eq_local, eigenProjDiag_eq_local]

/-- **PST implies strong cospectrality** (necessary condition, Godsil 2012,
Thm 2.1; here in this module's projector language).  Proven *unconditionally
and axiom-cleanly* by transporting the sibling `GodsilRatio` extraction
`Graphplay.PST.isPST_imp_isStronglyCospectral` through the projector bridge. -/
theorem isStronglyCospectral_of_isPST (G : WeightedGraph V) (u v : V) (τ : ℝ)
    (h : IsPST G u v τ) : IsStronglyCospectral G u v :=
  (isStronglyCospectral_iff_local G u v).mpr
    (Graphplay.PST.isPST_imp_isStronglyCospectral G τ u v h)

/-- The **real (orthogonal) variant**: strong cospectrality with phases
restricted to `±1`.  This is the original Godsil-Royle definition for
ordinary (real, symmetric) adjacency matrices.  The chiral version above
relaxes the phase constraint to the unit circle.

For real-weighted graphs (`G.adj` with real entries), the two definitions
coincide because the projector entries `⟨u, P_λ v⟩` are real. -/
def IsRealStronglyCospectral (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      eigenProjEntry G lam u v
        = (ε : ℂ) * Complex.ofReal
            (Real.sqrt (eigenProjDiag G lam u * eigenProjDiag G lam v))

/-! ## The classical "diagonal + matched off-diagonal" characterization

The textbook way to state strong cospectrality (Godsil-Royle Chap. 8,
Coutinho-Godsil 2016) is:

* `u, v` are **cospectral** iff for every `λ`, `⟨u, P_λ u⟩ = ⟨v, P_λ v⟩`,
* and **strongly cospectral** iff additionally for every `λ` there exists a
  sign / unit phase `ε_λ` with `⟨u, P_λ v⟩ = ε_λ ⟨u, P_λ u⟩`.

The two definitions are equivalent (modulo the geometric-mean substitution,
which is automatic once the diagonal entries are equal). -/

/-- Vertices are **cospectral** iff every eigenspace projector has the same
diagonal entry at `u` and `v`.  (Equivalently, all spectral moments
`⟨u, A^k u⟩ = ⟨v, A^k v⟩` agree.) -/
def IsCospectral (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
    eigenProjDiag G lam u = eigenProjDiag G lam v

/-- **A graph automorphism gives cospectrality** (Godsil-Royle Lemma 8.2.1,
the cospectral half).  If `σ` is an automorphism of `G` with `σ u = v`, then
`u` and `v` are cospectral: every spectral projector has equal diagonal entries
`(E_λ)_{u,u} = (E_λ)_{v,v}`.

Proven axiom-cleanly via the sibling `eigenProj_aut_invariant`: an automorphism's
permutation matrix commutes with `G.adj`, hence with the (unique) spectral
projectors, so `(E_λ)_{σ u, σ u} = (E_λ)_{u,u}`.

NOTE.  Cospectrality is *all* that a bare automorphism `σ u = v` yields: full
strong cospectrality (parallelism of the projected rays) does **not** follow
from the swap alone — in a vertex-transitive graph every pair admits such a `σ`
yet most pairs are not strongly cospectral.  The extra input is that `σ` act as
a scalar `±1` on each `λ`-eigenspace (as the path-flip does). -/
theorem isCospectral_of_aut (G : WeightedGraph V) (u v : V)
    (σ : V ≃ V) (hσ : ∀ x y, G.adj (σ x) (σ y) = G.adj x y) (huv : σ u = v) :
    IsCospectral G u v := by
  intro lam hlam
  -- Bridge both diagonals to the `GodsilRatio` projector matrix, then use
  -- automorphism invariance `(E_λ)_{σ u, σ u} = (E_λ)_{u,u}` at `σ u = v`.
  have hinv := Graphplay.PST.eigenProj_aut_invariant G σ hσ lam hlam u u
  rw [huv] at hinv
  -- `(E_λ)_{v,v} = (E_λ)_{u,u}` as complex numbers; both are the (real) diagonals.
  have hu : (Graphplay.PST.eigenProj G lam u u) = (eigenProjDiag G lam u : ℂ) := by
    rw [Graphplay.PST.eigenProj_diag, ← eigenProjDiag_eq_local]
  have hv : (Graphplay.PST.eigenProj G lam v v) = (eigenProjDiag G lam v : ℂ) := by
    rw [Graphplay.PST.eigenProj_diag, ← eigenProjDiag_eq_local]
  rw [hu, hv] at hinv
  exact_mod_cast hinv.symm

/-- **Reverse direction of the classical equivalence (Coutinho Cor. 2.5.2,
`←`).** If `u, v` are cospectral and the off-diagonal projector entry matches
a unit phase times the common diagonal entry, then `u, v` are strongly
cospectral in the geometric-mean sense.

This is the honest, unconditional half: once `(E_λ)_{u,u} = (E_λ)_{v,v} =: d`
with `d ≥ 0`, the geometric mean collapses, `√(d·d) = d`, so the matched form
`(E_λ)_{u,v} = ε d` is literally the geometric-mean form. -/
theorem isStronglyCospectral_of_cospectral_matched (G : WeightedGraph V)
    (u v : V) (hcosp : IsCospectral G u v)
    (hmatch : ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
      ∃ ε : ℂ, ‖ε‖ = 1 ∧
        eigenProjEntry G lam u v = ε * Complex.ofReal (eigenProjDiag G lam u)) :
    IsStronglyCospectral G u v := by
  intro lam hlam
  obtain ⟨ε, hε, heq⟩ := hmatch lam hlam
  refine ⟨ε, hε, ?_⟩
  rw [heq]
  congr 2
  -- `diag u = √(diag u * diag v)`: use cospectrality `diag u = diag v`
  -- and `√(d * d) = d` for `d = diag u ≥ 0`.
  rw [← hcosp lam hlam, Real.sqrt_mul_self (eigenProjDiag_nonneg G lam u)]

/-- **Classical equivalence (Godsil-Royle / Coutinho-Godsil 2016), under
cospectrality (CLOSED).**  *Given* that `u, v` are cospectral, the geometric-mean
form of strong cospectrality is equivalent to the textbook "matched off-diagonal"
form: for every eigenvalue `λ` the off-diagonal projector entry `⟨u, P_λ v⟩`
equals a unit-modulus phase `ε_λ` times the common diagonal entry
`⟨u, P_λ u⟩ = ⟨v, P_λ v⟩`.

The cospectrality hypothesis is *necessary*, not cosmetic: without it the `→`
direction is genuinely false for the geometric-mean encoding used here.  Indeed
a simple-spectrum graph makes *every* pair strongly cospectral
(`isStronglyCospectral_of_simple_spectrum`) — the cross entry
`(E_λ)_{u,v} = (eigU)_{u,i}\overline{(eigU)_{v,i}}` always saturates
`|(E_λ)_{u,v}| = √((E_λ)_{u,u}(E_λ)_{v,v})` (parallelism) — yet the diagonals
`(E_λ)_{u,u} = ‖(eigU)_{u,i}‖²` and `(E_λ)_{v,v} = ‖(eigU)_{v,i}‖²` differ for
most pairs.  Parallelism does **not** imply cospectrality (Coutinho 2.5.2 lists
them as independent hypotheses), so the honest equivalence is *conditional* on
cospectrality, under which `√(d·d) = d` collapses both forms onto each other.

This is the form used in the proof of the PST existence criterion
(Coutinho-Godsil §2-3, Bachman-Tamon arXiv:1108.0339). -/
theorem isStronglyCospectral_iff_of_cospectral (G : WeightedGraph V) (u v : V)
    (hcosp : IsCospectral G u v) :
    IsStronglyCospectral G u v ↔
        ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
          ∃ ε : ℂ, ‖ε‖ = 1 ∧
            eigenProjEntry G lam u v
              = ε * Complex.ofReal (eigenProjDiag G lam u) := by
  constructor
  · -- `→`: under cospectrality `d_u = d_v`, the geometric mean `√(d_u d_v)`
    -- collapses to `d_u`, so the geometric-mean form *is* the matched form.
    intro hsc lam hlam
    obtain ⟨ε, hε, heq⟩ := hsc lam hlam
    refine ⟨ε, hε, ?_⟩
    rw [heq]
    congr 2
    -- `√(d_u * d_v) = d_u` via `d_u = d_v` (cospectrality) and `√(d·d) = d`.
    rw [← hcosp lam hlam, Real.sqrt_mul_self (eigenProjDiag_nonneg G lam u)]
  · -- `←`: cospectral + matched off-diagonal ⇒ geometric-mean form.
    intro hmatch
    exact isStronglyCospectral_of_cospectral_matched G u v hcosp hmatch

/-! ## The PST existence criterion (Godsil ratio condition)

The full PST existence criterion combines strong cospectrality with a
number-theoretic condition on the eigenvalues called the **Godsil ratio
condition**: for every two eigenvalues `λ, μ` in the **eigenvalue support** of
`u` (i.e. those `λ` with `⟨u, P_λ u⟩ ≠ 0`), the ratio `(λ - μ_0)/(μ - μ_0)`
is rational with respect to a fixed reference eigenvalue `μ_0`.

The full theorem (Coutinho-Godsil 2016 Theorem 4.1.1, packaging Godsil's
1990s lemmas): *PST exists between `u` and `v` at some time `τ > 0` if and
only if `u, v` are strongly cospectral and the Godsil ratio condition holds
on their common eigenvalue support.* -/

/-- The **eigenvalue support** of `u` in `G`: the eigenvalues `λ` such that
the projection of `|u⟩` onto `E_λ` is nonzero.  Equivalently, the support of
the spectral measure of `|u⟩` under `G.adj`. -/
def eigenSupport (G : WeightedGraph V) (u : V) : Set ℝ :=
  {lam : ℝ | lam ∈ Set.range G.herm.eigenvalues ∧ eigenProjDiag G lam u ≠ 0}

/-- The eigenvalue support is contained in the (real) eigenvalue range,
hence in `spectrum ℝ G.adj`: every eigenvalue in the support is, in
particular, an eigenvalue.  This is the elementary half of Mathlib's
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`. -/
theorem eigenSupport_subset_range (G : WeightedGraph V) (u : V) :
    eigenSupport G u ⊆ Set.range G.herm.eigenvalues :=
  fun _ h => h.1

/-- Every eigenvalue in the support of `u` lies in the real spectrum of
`G.adj`.  Reduces `eigenSupport` to Mathlib's Hermitian spectral API
(`eigenvalues_mem_spectrum_real`). -/
theorem eigenSupport_subset_spectrum (G : WeightedGraph V) (u : V) :
    eigenSupport G u ⊆ spectrum ℝ G.adj := by
  rintro lam ⟨⟨i, rfl⟩, _⟩
  exact G.herm.eigenvalues_mem_spectrum_real i

/-- A point off the eigenvalue range carries trivial spectral mass:
`eigenProjDiag G lam u = 0` whenever `lam` is not an eigenvalue, because the
defining sum is empty (every `if`-guard fails). -/
theorem eigenProjDiag_eq_zero_of_not_mem_range (G : WeightedGraph V) (lam : ℝ)
    (u : V) (h : lam ∉ Set.range G.herm.eigenvalues) :
    eigenProjDiag G lam u = 0 := by
  unfold eigenProjDiag eigenProjEntry
  rw [Complex.re_sum]
  apply Finset.sum_eq_zero
  intro i _
  have : G.herm.eigenvalues i ≠ lam := by
    intro he; exact h ⟨i, he⟩
  simp only [this, if_false, Complex.zero_re]

/-- The **Godsil ratio condition** on the eigenvalue support of a pair
`(u, v)`: pick any reference eigenvalue `μ_0` in the support; then every
ratio `(λ - μ_0)/(μ - μ_0)` over `λ, μ` in the joint support is rational.
This is the Galois/Kronecker-style obstruction to recurrence on the unit
circle for the phases `exp(-i τ λ)`. -/
def GodsilRatioCondition (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam mu mu0 : ℝ,
    lam ∈ eigenSupport G u → mu ∈ eigenSupport G u → mu0 ∈ eigenSupport G u →
    lam ∈ eigenSupport G v → mu ∈ eigenSupport G v → mu0 ∈ eigenSupport G v →
    mu ≠ mu0 →
    ∃ q : ℚ, (lam - mu0) = (q : ℝ) * (mu - mu0)

/-- **Strong cospectrality + Godsil ratio iff PST exists at some time.**

This is the load-bearing PST existence theorem of Coutinho-Godsil 2016
(Theorem 4.1.1), originally folklore in Godsil's earlier papers
(see arXiv:0806.2074 and the references in Bachman-Tamon arXiv:1108.0339).
The proof factors through:

* `IsStronglyCospectral` → off-diagonal evolution entry equals a
  trigonometric sum of products `ε_λ exp(-i τ λ) · diag`;
* `GodsilRatioCondition` → simultaneous Diophantine approximation of all
  phases yields a τ at which all `ε_λ exp(-i τ λ)` coincide on the unit
  circle (so the modulus saturates `1`).

The proof is tagged for sibling agent **L2** (see `tools/agent_swarm/manifest`
or equivalent) to complete; here we only state the iff.
-/
theorem IsStronglyCospectral.isPST_iff_godsilRatio
    (G : WeightedGraph V) (u v : V) :
    (∃ τ : ℝ, 0 < τ ∧ IsPST G u v τ) ↔
      IsStronglyCospectral G u v ∧ GodsilRatioCondition G u v := by
  -- Tag for L2: full proof via Kronecker simultaneous approximation
  -- (Coutinho-Godsil 2016, §4.1).  Direction `→` is "PST implies strong
  -- cospectrality + Godsil ratio" (Godsil, AGT-style derivation);
  -- direction `←` is "Diophantine approximation closes the τ".
  -- BLOCKED: GodsilRatioCondition half needs Kronecker simultaneous
  -- Diophantine approximation on AddCircle (not developed).
  sorry

/-! ## Functoriality under equitable partitions

When `P` is an equitable partition of `G` whose cell map separates `u` and
`v` (i.e. `P.cells u ≠ P.cells v`), strong cospectrality of `(u, v)` upstairs
in `G` lifts to strong cospectrality of `(P.cells u, P.cells v)` downstairs
in `P.quotient`.

The mechanism is the eigenvector lift of `Graphplay.Spectral`
(`adj_mulVec_cellInflateVec`): a quotient eigenvector `w` with eigenvalue
`λ` inflates to a graph eigenvector with the same eigenvalue, and the
cell-uniform isometry preserves inner products up to the cardinality
factor `√|C_i|`.
-/

/-- A bundle morphism record for the quotient direction: an equitable
partition that sends `u, v` to *distinct* cells. -/
structure CellSeparating
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (u v : V) : Prop where
  /-- The cell separation hypothesis. -/
  separates : P.cells u ≠ P.cells v

/-- **Functoriality: strong cospectrality descends along a cell-separating
equitable partition.**

If `P` is equitable, `P.cells u = i`, `P.cells v = j`, `i ≠ j`, then
*upstairs* strong cospectrality `IsStronglyCospectral G u v` lifts to
*downstairs* strong cospectrality of the quotient
`IsStronglyCospectralQuot P i j`.

The converse (descending → ascending) requires that the cells of `u, v` be
singletons (else the cell-uniform vector is a non-trivial average).
-/
theorem Hom.preserves_stronglyCospectral
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (u v : V) (h : CellSeparating P u v)
    (Gq : WeightedGraph I) (hQ : Gq.adj = P.symmQuotient)
    (hsc : IsStronglyCospectral G u v) :
    -- Genuine downstairs conclusion: the cells `P.cells u` and `P.cells v`
    -- (distinct, by `h.separates`) are *strongly cospectral as vertices of the
    -- quotient graph `Gq`* (whose adjacency is the symmetric quotient).
    IsStronglyCospectral Gq (P.cells u) (P.cells v) := by
  -- HONEST SORRY.  The previous formulation concluded only `∀ lam, ∃ ε, ‖ε‖ = 1`
  -- — a vacuous statement (`ε = 1` always works, independent of `hsc`).  The
  -- genuine content is strong cospectrality of the cells *in the quotient*:
  -- transport each phase witness `ε_λ` from `hsc` through the `cellInflate`
  -- isometry (`Graphplay.Spectral.cellInflateLin`, injective on nonempty cells),
  -- which embeds the quotient `λ`-eigenspaces isometrically into the
  -- `G.adj`-invariant cell-uniform host subspace (`cellUniformSubspace_invariant`)
  -- so the spectral projectors commute with the embedding.  This eigenbasis
  -- transport lemma is the same one the sibling
  -- `Graphplay.PST.QuotientIff.stronglyCospectral_cellUniform_iff_quotient`
  -- carries as an honest `sorry`; assembling it here is left likewise.
  -- BLOCKED: needs cellInflate eigenbasis-transport lemma relating quotient
  -- spectral projectors to G.adj projectors (sibling QuotientIff, also sorry).
  sorry

/-- **Simple spectrum ⟹ strong cospectrality of every pair** (Coutinho–Godsil
2021, Cor. 8.2).  If the eigenvalues of `G.adj` are pairwise distinct (each
eigenspace is one-dimensional), then *any* two vertices are strongly cospectral,
since each `λ`-eigenspace is a single ray and the two projected vectors are
automatically parallel.  This is the structural mechanism behind path-endpoint
strong cospectrality (the path `P_n` has the simple spectrum `2cos(kπ/(n+1))`).

Proven axiom-cleanly by transporting the sibling
`Graphplay.PST.isStronglyCospectral_of_injective_eigenvalues` through the
projector bridge `isStronglyCospectral_iff_local`. -/
theorem isStronglyCospectral_of_simple_spectrum (G : WeightedGraph V)
    (hinj : Function.Injective G.herm.eigenvalues) (u v : V) :
    IsStronglyCospectral G u v :=
  (isStronglyCospectral_iff_local G u v).mpr
    (Graphplay.PST.isStronglyCospectral_of_injective_eigenvalues G hinj u v)

/-! ## Path eigenvalue distinctness (Chebyshev / Niven)

The eigenvalues of the path adjacency matrix `A(P_n)` are
`2cos(kπ/(n+1))` for `k = 1, …, n` (Christandl-Datta-Ekert-Landahl 2004; the
characteristic polynomial is the Chebyshev `U_n`).  The **distinctness** of
these eigenvalues — the sole missing input to path-endpoint strong
cospectrality — is a self-contained real-analysis fact: the angles
`kπ/(n+1)` for `k = 1, …, n` all lie in the open interval `(0, π)`, on which
`Real.cos` is strictly anti-monotone (`Real.strictAntiOn_cos`,
`Real.injOn_cos`).  We prove it here as a reusable helper. -/

/-- The map `k ↦ 2cos(kπ/(n+1))` for `k : Fin n` (i.e. `k = 0, …, n-1`,
representing the path eigenvalue indices `k+1 = 1, …, n`).  This is the
explicit eigenvalue list of `A(P_n)`. -/
noncomputable def pathEigenvalue (n : ℕ) (k : Fin n) : ℝ :=
  2 * Real.cos ((((k : ℝ) + 1) * Real.pi) / ((n : ℝ) + 1))

/-- For `k : Fin n`, the angle `(k+1)π/(n+1)` lies in `[0, π]` (in fact in the
open interval `(0, π)`): `0 < k+1 ≤ n < n+1` so `0 < (k+1)/(n+1) < 1`. -/
theorem pathAngle_mem_Icc (n : ℕ) (k : Fin n) :
    (((k : ℝ) + 1) * Real.pi) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) Real.pi := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk_lt : ((k : ℝ) + 1) < (n : ℝ) + 1 := by
    have : (k : ℕ) < n := k.2
    have : ((k : ℝ)) < (n : ℝ) := by exact_mod_cast this
    linarith
  have hk_pos : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  constructor
  · -- `0 ≤ ((k+1)π)/(n+1)`
    apply div_nonneg
    · positivity
    · exact hn1.le
  · -- `((k+1)π)/(n+1) ≤ π`: since `(k+1) ≤ (n+1)`, `(k+1)/(n+1) ≤ 1`.
    rw [div_le_iff₀ hn1]
    calc ((k : ℝ) + 1) * Real.pi
        ≤ ((n : ℝ) + 1) * Real.pi := by
          apply mul_le_mul_of_nonneg_right hk_lt.le hpi
      _ = Real.pi * ((n : ℝ) + 1) := by ring

/-- **Path eigenvalue distinctness** (Niven / Chebyshev).  The map
`k ↦ 2cos((k+1)π/(n+1))`, `k : Fin n`, is injective: distinct indices give
distinct path eigenvalues.  Argument: the angles `(k+1)π/(n+1)` all lie in
`[0, π]`, where `Real.cos` is injective (`Real.injOn_cos`); the factor `2`
and the strictly-increasing affine reindex `k ↦ (k+1)π/(n+1)` preserve
injectivity.  This is the sole explicit-eigenvalue fact behind path-endpoint
strong cospectrality (Mathlib has no path eigenstructure). -/
theorem pathEigenvalue_injective (n : ℕ) :
    Function.Injective (pathEigenvalue n) := by
  intro k k' hkk'
  -- Strip the factor `2` and apply `Real.injOn_cos` on `[0, π]`.
  unfold pathEigenvalue at hkk'
  have hcos : Real.cos ((((k : ℝ) + 1) * Real.pi) / ((n : ℝ) + 1))
      = Real.cos ((((k' : ℝ) + 1) * Real.pi) / ((n : ℝ) + 1)) :=
    mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hkk'
  -- Injectivity of `cos` on `[0, π]` gives equal angles.
  have hang := Real.injOn_cos (pathAngle_mem_Icc n k) (pathAngle_mem_Icc n k') hcos
  -- The affine map `k ↦ (k+1)π/(n+1)` is injective (π/(n+1) > 0).
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Equal fractions with equal nonzero denominators ⇒ equal numerators.
  have hmul : ((k : ℝ) + 1) * Real.pi = ((k' : ℝ) + 1) * Real.pi := by
    have hcongr := congrArg (· * ((n : ℝ) + 1)) hang
    simp only [div_mul_cancel₀ _ hn1] at hcongr
    exact hcongr
  have hk_eq : ((k : ℝ) + 1) = ((k' : ℝ) + 1) :=
    mul_right_cancel₀ (ne_of_gt hpi) hmul
  have hkR : (k : ℝ) = (k' : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast hkR)

/-! ### Niven irrationality of `cos(kπ/N)` and the path Diophantine obstruction

The forward direction of the path-PST classification (`n ∈ {2,3}` only) bottoms
out on a purely number-theoretic fact: the path eigenvalues `2cos(kπ/(n+1))`,
`k = 1,…,n`, do **not** lie on a common arithmetic progression once `n ≥ 4`.
This is the Godsil-ratio obstruction, and its kernel is **Niven's theorem**
(Mathlib `irrational_cos_rat_mul_pi` / `niven_angle_div_pi_eq`): the only rational
values of `cos(rπ)` at rational `r ∈ [0,1]` are at `r ∈ {0, 1/3, 1/2, 2/3, 1}`,
so `cos(π/N)` is irrational for every `N ≥ 4`.

We build the obstruction reusably here:
* `irrational_cos_rat_of_mem`: the generic Niven contrapositive,
* `irrational_cos_pi_div`: `cos(π/N)` irrational for `N ≥ 4`,
* `pathEigenvalue_rec`: the Chebyshev three-term recurrence on the eigenvalues,
* `pathEigenvalue_not_arithmeticProgression`: for `n ≥ 4`, the path eigenvalues
  admit no arithmetic progression — the genuine, axiom-clean Diophantine residual. -/

/-- **Generic Niven contrapositive.**  If `r ∈ [0,1] ∩ ℚ` is none of
`{0, 1/3, 1/2, 2/3, 1}`, then `cos(rπ)` is irrational.  Direct from Mathlib's
`niven_angle_div_pi_eq`. -/
theorem irrational_cos_rat_of_mem (r : ℚ) (hr : r ∈ Set.Icc (0 : ℚ) 1)
    (hne : r ≠ 0 ∧ r ≠ 1/3 ∧ r ≠ 1/2 ∧ r ≠ 2/3 ∧ r ≠ 1) :
    Irrational (Real.cos ((r : ℝ) * Real.pi)) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hcos
  have hmem := niven_angle_div_pi_eq (r := r) ⟨a/b, by push_cast at hcos ⊢; rw [hcos]⟩ hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  obtain ⟨h0, h13, h12, h23, h1⟩ := hne
  rcases hmem with h | h | h | h | h
  · exact h0 h
  · exact h13 h
  · exact h12 h
  · exact h23 h
  · exact h1 h

/-- **`cos(π/N)` is irrational for `N ≥ 4`** (Niven).  Specialization of
`irrational_cos_rat_of_mem` at `r = 1/N`: for `N ≥ 4` the reduced fraction
`1/N ∉ {0, 1/3, 1/2, 2/3, 1}`.  This is the kernel of the path-PST obstruction:
the smallest path angle `π/N` has irrational cosine exactly when `N ∉ {1,2,3}`. -/
theorem irrational_cos_pi_div (N : ℕ) (hN : 4 ≤ N) :
    Irrational (Real.cos (Real.pi / N)) := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  have key : Irrational (Real.cos ((((1 : ℚ)/N : ℚ) : ℝ) * Real.pi)) := by
    apply irrational_cos_rat_of_mem ((1 : ℚ)/N)
    · refine ⟨by positivity, ?_⟩
      rw [div_le_one hN0]; exact_mod_cast (by omega : (1 : ℕ) ≤ N)
    · have hNne : (N : ℚ) ≠ 0 := ne_of_gt hN0
      have hN4 : (4 : ℚ) ≤ N := by exact_mod_cast hN
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
        (rw [div_eq_iff hNne] at h; nlinarith [h, hN0, hN4])
  have heq : ((((1 : ℚ)/N : ℚ) : ℝ) * Real.pi) = Real.pi / N := by push_cast; ring
  rwa [heq] at key

/-- **Three-term recurrence on the path eigenvalues.**  Writing
`θ_k = 2cos((k+1)π/(n+1))`, the Chebyshev recurrence reads
`θ_{k+1} + θ_{k-1} = 2cos(π/(n+1)) · θ_k` for `k ≥ 1`.  (Indices over `ℕ`; the
`pathEigenvalue` indices `k+1` are shifted by one.)  Pure trig:
`cos(α+β) + cos(α-β) = 2cosα cosβ`. -/
theorem pathEigenvalue_rec (n : ℕ) (k : ℕ) (hk : 1 ≤ k) :
    2 * Real.cos (((k : ℝ)+1+1) * Real.pi / ((n:ℝ)+1))
      + 2 * Real.cos (((k : ℝ)-1+1) * Real.pi / ((n:ℝ)+1))
      = 2 * Real.cos (Real.pi / ((n:ℝ)+1))
          * (2 * Real.cos (((k : ℝ)+1) * Real.pi / ((n:ℝ)+1))) := by
  set N : ℝ := (n:ℝ)+1 with hN
  set θ : ℝ := Real.pi / N with hθ
  have e1 : ((k:ℝ)+1+1) * Real.pi / N = ((k:ℝ)+1) * θ + θ := by rw [hθ]; ring
  have e2 : ((k:ℝ)-1+1) * Real.pi / N = ((k:ℝ)+1) * θ - θ := by rw [hθ]; ring
  have e3 : (((k:ℝ)+1) * Real.pi / N) = ((k:ℝ)+1) * θ := by rw [hθ]; ring
  rw [e1, e2, e3, Real.cos_add, Real.cos_sub]; ring

/-- **The path eigenvalues do not lie on an arithmetic progression, for `n ≥ 4`**
(the Godsil ratio obstruction, via Niven).

Concretely: there are **no** reals `a > 0, b` with `2cos((k+1)π/(n+1)) = b + a·m_k`
for integers `m_k`, `k = 0,…,n-1`.  This is the precise number-theoretic content
behind "`P_n` has endpoint PST only for `n ∈ {2,3}`": strong cospectrality of the
endpoints always holds (`isStronglyCospectral_pathEndpoints`), so the sole
obstruction is the Godsil ratio condition, which *is* arithmetic-progression
membership of the support eigenvalues — and that fails here.

PROOF (axiom-clean, Niven).  Use the three-term recurrence at indices `k = 1, 2`
(all of `0,1,2,3` are valid eigenvalue indices since `n ≥ 4`):
`θ_2 + θ_0 = 2c·θ_1` and `θ_3 + θ_1 = 2c·θ_2`, where `c = cos(π/(n+1))`.
Subtracting, `(θ_2+θ_0) - (θ_3+θ_1) = 2c·(θ_1 - θ_2)`.  If every `θ_k = b + a·m_k`,
the offset `b` cancels (each side has zero net coefficient), leaving
`2c = a·(integer) / a·(integer)`, a *rational*; the denominator `θ_1-θ_2 ≠ 0` by
eigenvalue distinctness (`pathEigenvalue_injective`).  But `c = cos(π/(n+1))` is
**irrational** for `n+1 ≥ 5` by Niven (`irrational_cos_pi_div`) — contradiction. -/
theorem pathEigenvalue_not_arithmeticProgression (n : ℕ) (hn : 4 ≤ n) :
    ¬ ∃ a b : ℝ, 0 < a ∧ ∀ k : Fin n, ∃ m : ℤ, pathEigenvalue n k = b + a * (m : ℝ) := by
  rintro ⟨a, b, ha, hAP⟩
  -- Local index helper: `pathEigenvalue n ⟨k, _⟩ = 2cos((k+1)π/(n+1))`.
  have hpev : ∀ k : Fin n, pathEigenvalue n k
      = 2 * Real.cos (((k : ℝ)+1) * Real.pi / ((n:ℝ)+1)) := by
    intro k; rfl
  set c : ℝ := Real.cos (Real.pi / ((n:ℝ)+1)) with hc
  -- The four eigenvalue indices we use, as `Fin n` (valid since `n ≥ 4`).
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  -- recurrences at k = 1 and k = 2.
  have r1 : pathEigenvalue n i2 + pathEigenvalue n i0
      = 2 * c * pathEigenvalue n i1 := by
    rw [hpev, hpev, hpev, hc]
    have := pathEigenvalue_rec n 1 (by omega)
    simp only [Nat.cast_one] at this ⊢
    convert this using 3 <;> norm_num
  have r2 : pathEigenvalue n i3 + pathEigenvalue n i1
      = 2 * c * pathEigenvalue n i2 := by
    rw [hpev, hpev, hpev, hc]
    have := pathEigenvalue_rec n 2 (by omega)
    simp only [Nat.cast_ofNat] at this ⊢
    convert this using 3 <;> norm_num
  -- AP witnesses.
  obtain ⟨m0, h0⟩ := hAP i0
  obtain ⟨m1, h1⟩ := hAP i1
  obtain ⟨m2, h2⟩ := hAP i2
  obtain ⟨m3, h3⟩ := hAP i3
  -- (θ_2+θ_0) - (θ_3+θ_1) = 2c (θ_1 - θ_2); offset `b` cancels on the LHS.
  have hsub : (pathEigenvalue n i2 + pathEigenvalue n i0)
      - (pathEigenvalue n i3 + pathEigenvalue n i1)
      = 2 * c * (pathEigenvalue n i1 - pathEigenvalue n i2) := by
    rw [r1, r2]; ring
  have hnum : (pathEigenvalue n i2 + pathEigenvalue n i0)
      - (pathEigenvalue n i3 + pathEigenvalue n i1)
      = a * (((m2 + m0) - (m3 + m1) : ℤ) : ℝ) := by
    rw [h0, h1, h2, h3]; push_cast; ring
  have hden : pathEigenvalue n i1 - pathEigenvalue n i2
      = a * ((m1 - m2 : ℤ) : ℝ) := by
    rw [h1, h2]; push_cast; ring
  -- distinctness ⇒ denominator nonzero.
  have hpevne : pathEigenvalue n i1 ≠ pathEigenvalue n i2 := by
    intro he
    have := pathEigenvalue_injective n he
    have hval : (i1 : Fin n).val = (i2 : Fin n).val := congrArg Fin.val this
    simp only [i1, i2] at hval
    omega
  have hane : a ≠ 0 := ne_of_gt ha
  have hdenne : ((m1 - m2 : ℤ) : ℝ) ≠ 0 := by
    intro hz; apply hpevne
    have : pathEigenvalue n i1 - pathEigenvalue n i2 = 0 := by rw [hden, hz, mul_zero]
    linarith
  -- `2c` equals a rational, so `2c` is rational.
  have hkey : 2 * c * (a * ((m1 - m2 : ℤ) : ℝ)) = a * (((m2 + m0) - (m3 + m1) : ℤ) : ℝ) := by
    rw [← hden, ← hsub, hnum]
  have h2c : 2 * c = (((m2 + m0) - (m3 + m1) : ℤ) : ℝ) / ((m1 - m2 : ℤ) : ℝ) := by
    rw [eq_div_iff hdenne]
    have hk := hkey
    field_simp at hk
    nlinarith [hk, ha, sq_nonneg a]
  -- but `c = cos(π/(n+1))` is irrational by Niven, hence so is `2c`.
  have hcirr : Irrational c := by
    rw [hc, show Real.cos (Real.pi / ((n:ℝ)+1))
        = Real.cos (Real.pi / ((n+1:ℕ):ℝ)) by push_cast; ring_nf]
    exact irrational_cos_pi_div (n+1) (by omega)
  have h2cirr : Irrational (2 * c) := by
    rw [show (2 * c) = ((2 : ℚ) : ℝ) * c by push_cast; ring]
    exact hcirr.ratCast_mul (by norm_num)
  rw [h2c, show (((m2 + m0) - (m3 + m1) : ℤ) : ℝ) / ((m1 - m2 : ℤ) : ℝ)
        = ((((((m2 + m0) - (m3 + m1) : ℤ) : ℚ) / ((m1 - m2 : ℤ) : ℚ)) : ℚ) : ℝ) by
        push_cast; ring] at h2cirr
  exact (Rat.not_irrational _) h2cirr

/-- **Nodup charpoly roots ⟹ simple spectrum.**  A generic axiom-clean bridge:
if the characteristic polynomial of a Hermitian-weighted graph `G` has no
repeated roots, then Mathlib's eigenvalue function `G.herm.eigenvalues` is
injective.  Via `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`
(`charpoly.roots = map (ofReal ∘ eigenvalues) univ.val`), a nodup root multiset
forces `ofReal ∘ eigenvalues` injective on `univ`, and `Complex.ofReal` is
injective.

This isolates path-graph simple spectrum to the *single* algebraic fact that
`A(P_n)`'s characteristic polynomial (the Chebyshev `U_n`) is squarefree —
equivalently that its roots `2cos(kπ/(n+1))` are distinct, which is
`pathEigenvalue_injective`. -/
theorem injective_eigenvalues_of_charpoly_roots_nodup (G : WeightedGraph V)
    (hnd : (G.adj.charpoly).roots.Nodup) :
    Function.Injective G.herm.eigenvalues := by
  -- `roots = map (ofReal ∘ eigenvalues) univ.val`; nodup ⇒ inj on univ.
  have hroots := G.herm.roots_charpoly_eq_eigenvalues
  rw [hroots] at hnd
  have hmem : ∀ x : V, x ∈ (Finset.univ : Finset V).val :=
    fun x => Finset.mem_val.mpr (Finset.mem_univ x)
  have hinj_comp : Function.Injective
      (fun x : V => (RCLike.ofReal (G.herm.eigenvalues x) : ℂ)) := by
    intro x y hxy
    exact Multiset.inj_on_of_nodup_map hnd x (hmem x) y (hmem y) hxy
  intro x y hxy
  apply hinj_comp
  exact congrArg (fun r : ℝ => (RCLike.ofReal r : ℂ)) hxy

/-! ## Concrete examples

The textbook example of strong cospectrality is the endpoint pair of a path
graph `P_n`: the explicit Chebyshev eigenvector basis

  `ψ_k(j) = √(2/(n+1)) · sin(jkπ/(n+1))`

has the symmetry `ψ_k(1) = ±ψ_k(n)`, so every projector entry between the
endpoints is `±` the diagonal entry — i.e. the real (orthogonal) version of
strong cospectrality holds.  This is the spectral content of the original
Christandl-Datta-Ekert-Landahl spin-chain PST proposal (PRL 92 187902, 2004),
which goes on to engineer the *Krawtchouk* weighting that fixes the Godsil
ratio condition and gives genuine PST. -/

/-- The path graph `P_n` (unweighted).  We package only the underlying
`WeightedGraph`; the explicit construction is left abstract here for
modularity. -/
noncomputable def pathWeightedGraph (n : ℕ) : WeightedGraph (Fin n) :=
  -- Promote `SimpleGraph.pathGraph n` (the Hasse diagram of `Fin n`) via the
  -- `SimpleGraph.toWeighted` bridge.  The adjacency relation is decidable via
  -- classical choice (only the underlying matrix needs to be computed).
  letI : DecidableRel (SimpleGraph.pathGraph n).Adj := Classical.decRel _
  SimpleGraph.toWeighted (SimpleGraph.pathGraph n)

/-! ## Path characteristic polynomial = Chebyshev `U_n(X/2)` (tridiagonal recurrence)

The adjacency matrix of `P_n` is tridiagonal (1 on the off-diagonals).  Its
characteristic matrix `X·I − A` has determinant satisfying the three-term
recurrence `p_{n+2} = X·p_{n+1} − p_n`, which is exactly the (monic, scaled)
Chebyshev polynomial of the second kind `U_n(X/2)`.  Mathlib's
`Polynomial.Chebyshev.roots_U_real`-style result gives the `n` distinct roots
`2cos((k+1)π/(n+1))`, so the characteristic polynomial is squarefree and the
path has *simple spectrum* — the sole input needed to close path-endpoint strong
cospectrality. -/

namespace PathChebyshev

open Polynomial Matrix

/-- The path characteristic matrix: tridiagonal with `X` on the diagonal and
`-1` on the two off-diagonals, over `ℂ[X]`. -/
noncomputable def pathCharM (n : ℕ) : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
  fun i j =>
    if i = j then X
    else if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then -1
    else 0

lemma pathCharM_apply (n : ℕ) (i j : Fin n) :
    pathCharM n i j =
      if i.val = j.val then X
      else if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then -1 else 0 := by
  simp only [pathCharM, Fin.ext_iff]

@[simp] lemma pathCharM_diag (n : ℕ) (i : Fin n) : pathCharM n i i = X := by
  simp [pathCharM]

/-- Value of the path char-matrix purely in terms of `Nat` row/column indices. -/
lemma pathCharM_val (n : ℕ) (i j : Fin n) (a b : ℕ) (ha : i.val = a) (hb : j.val = b) :
    pathCharM n i j =
      if a = b then X else if (a + 1 = b ∨ b + 1 = a) then -1 else 0 := by
  rw [pathCharM_apply, ha, hb]

/-- Removing row 0 and column 0 from `pathCharM (n+1)` gives `pathCharM n`. -/
lemma pathCharM_sub00 (n : ℕ) :
    (pathCharM (n + 1)).submatrix Fin.succ ((0 : Fin (n+1)).succAbove) = pathCharM n := by
  funext i j
  rw [Matrix.submatrix_apply, Fin.zero_succAbove,
    pathCharM_val (n+1) i.succ j.succ (i.val + 1) (j.val + 1) (Fin.val_succ i) (Fin.val_succ j),
    pathCharM_apply]
  split_ifs <;> first | rfl | omega

/-- Expanding the column-1-deleted minor of `pathCharM (n+2)` gives
`-(pathCharM n).det`. -/
lemma pathCharM_sub01_det (n : ℕ) :
    ((pathCharM (n + 2)).submatrix Fin.succ ((1 : Fin (n+2)).succAbove)).det
      = - (pathCharM n).det := by
  rw [Matrix.det_succ_column_zero]
  set M := (pathCharM (n + 2)).submatrix Fin.succ ((1 : Fin (n+2)).succAbove) with hM
  rw [Finset.sum_eq_single (0 : Fin (n+1))]
  · -- surviving `i = 0` term
    have hentry : M 0 0 = (-1 : Polynomial ℂ) := by
      rw [hM, Matrix.submatrix_apply, Fin.one_succAbove_zero,
        pathCharM_val (n+2) (Fin.succ (0 : Fin (n+1))) 0 1 0
          (by rw [Fin.val_succ]; rfl) rfl]
      norm_num
    have hminor : (M.submatrix ((0 : Fin (n+1)).succAbove) Fin.succ) = pathCharM n := by
      funext i j
      rw [hM, Matrix.submatrix_apply, Matrix.submatrix_apply, Fin.zero_succAbove,
        Fin.one_succAbove_succ,
        pathCharM_val (n+2) (Fin.succ i.succ) (Fin.succ j.succ) (i.val + 2) (j.val + 2)
          (by rw [Fin.val_succ, Fin.val_succ]) (by rw [Fin.val_succ, Fin.val_succ]),
        pathCharM_apply]
      split_ifs <;> first | rfl | omega
    rw [Fin.val_zero, pow_zero, one_mul, hentry, hminor]; ring
  · -- `i ≠ 0` rows: column-0 entry is 0
    intro i _ hi0
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
    have hzero : M i'.succ 0 = 0 := by
      rw [hM, Matrix.submatrix_apply, Fin.one_succAbove_zero,
        pathCharM_val (n+2) (Fin.succ i'.succ) 0 (i'.val + 2) 0
          (by rw [Fin.val_succ, Fin.val_succ]) rfl]
      rw [if_neg (by omega), if_neg (by omega)]
    rw [hzero]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The three-term recurrence for the path char-matrix determinant:
`p_{n+2} = X · p_{n+1} − p_n`. -/
theorem pathCharM_det_rec (n : ℕ) :
    (pathCharM (n + 2)).det
      = X * (pathCharM (n + 1)).det - (pathCharM n).det := by
  rw [Matrix.det_succ_row_zero]
  -- only columns `0` and `1` of row 0 are nonzero
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  -- columns `≥ 2` vanish
  have htail : ∀ j : Fin n,
      (-1 : Polynomial ℂ) ^ (j.succ.succ : ℕ)
        * (pathCharM (n + 2)) 0 j.succ.succ
        * ((pathCharM (n + 2)).submatrix Fin.succ j.succ.succ.succAbove).det = 0 := by
    intro j
    have hz : (pathCharM (n + 2)) 0 j.succ.succ = 0 := by
      rw [pathCharM_val (n+2) 0 j.succ.succ 0 (j.val + 2) rfl
        (by rw [Fin.val_succ, Fin.val_succ])]
      rw [if_neg (by omega), if_neg (by omega)]
    rw [hz]; ring
  rw [Finset.sum_eq_zero (fun j _ => htail j), add_zero]
  -- column-0 term: `(+1)·X·det(pathCharM (n+1))`
  have h00 : (pathCharM (n + 2)) 0 0 = X := pathCharM_diag _ _
  have hsub0 : (pathCharM (n + 2)).submatrix Fin.succ ((0 : Fin (n+2)).succAbove)
      = pathCharM (n + 1) := pathCharM_sub00 (n + 1)
  -- column-1 term: `(-1)·(-1)·det(minor)`, minor det `= -(pathCharM n).det`
  have h01 : (pathCharM (n + 2)) 0 (Fin.succ 0) = -1 := by
    rw [pathCharM_val (n+2) 0 (Fin.succ 0) 0 1 rfl (by rw [Fin.val_succ]; rfl)]
    norm_num
  have hsub1 := pathCharM_sub01_det n
  rw [Fin.val_zero, pow_zero, one_mul, h00, hsub0, Fin.val_succ, Fin.val_zero,
    zero_add, pow_one, h01, Fin.succ_zero_eq_one, hsub1]
  ring

@[simp] lemma pathCharM_det_zero : (pathCharM 0).det = 1 := by
  simp

@[simp] lemma pathCharM_det_one : (pathCharM 1).det = X := by
  rw [Matrix.det_fin_one]; simp [pathCharM]

/-- The scaled Chebyshev polynomial of the second kind, `U_n(X/2)`, which is
monic of degree `n` and whose roots are `2cos((k+1)π/(n+1))`. -/
noncomputable def chebyScaled (n : ℕ) : Polynomial ℂ :=
  (Chebyshev.U ℂ (n : ℤ)).comp (C 2⁻¹ * X)

lemma chebyScaled_zero : chebyScaled 0 = 1 := by
  simp [chebyScaled, Chebyshev.U_zero]

/-- The key scaling identity: `2 · (X/2) = X`, i.e. `2 · (C 2⁻¹ · X) = X`. -/
lemma two_mul_half_X : (2 : Polynomial ℂ) * (C 2⁻¹ * X) = X := by
  rw [show (2 : Polynomial ℂ) = C 2 from (C_ofNat 2).symm, ← mul_assoc, ← C_mul]
  norm_num

lemma chebyScaled_one : chebyScaled 1 = X := by
  rw [chebyScaled, Nat.cast_one, Chebyshev.U_one]
  rw [mul_comp, ofNat_comp, X_comp]
  exact two_mul_half_X

lemma chebyScaled_rec (n : ℕ) :
    chebyScaled (n + 2) = X * chebyScaled (n + 1) - chebyScaled n := by
  have h : Chebyshev.U ℂ ((n : ℤ) + 2)
      = 2 * X * Chebyshev.U ℂ ((n : ℤ) + 1) - Chebyshev.U ℂ (n : ℤ) :=
    Chebyshev.U_add_two ℂ (n : ℤ)
  have hcast2 : ((n : ℕ) + 2 : ℕ) = ((n : ℤ) + 2) := by push_cast; ring
  have hcast1 : ((n : ℕ) + 1 : ℕ) = ((n : ℤ) + 1) := by push_cast; ring
  simp only [chebyScaled]
  rw [show ((↑(n + 2) : ℤ)) = (n : ℤ) + 2 by push_cast; ring,
      show ((↑(n + 1) : ℤ)) = (n : ℤ) + 1 by push_cast; ring, h]
  rw [sub_comp, mul_comp, mul_comp, X_comp]
  have h2 : (2 : Polynomial ℂ).comp (C 2⁻¹ * X) = 2 := by
    rw [show (2 : Polynomial ℂ) = C 2 from (C_ofNat 2).symm, C_comp]
  rw [h2]
  linear_combination ((Chebyshev.U ℂ ((n:ℤ)+1)).comp (C 2⁻¹ * X)) * two_mul_half_X

/-- The path char-matrix determinant equals the scaled Chebyshev polynomial. -/
theorem pathCharM_det_eq_cheby (n : ℕ) : (pathCharM n).det = chebyScaled n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [pathCharM_det_zero, chebyScaled_zero]
    | 1 => rw [pathCharM_det_one, chebyScaled_one]
    | (k + 2) =>
      rw [pathCharM_det_rec, chebyScaled_rec, ih (k + 1) (by omega), ih k (by omega)]

open Real in
/-- Evaluating `chebyScaled n` at `2·cos θ` strips the scaling and lands on
`(U ℂ n).eval (cos θ)`. -/
lemma chebyScaled_eval_two_cos (n : ℕ) (θ : ℝ) :
    (chebyScaled n).eval ((2 * Real.cos θ : ℝ) : ℂ)
      = (Chebyshev.U ℂ (n : ℤ)).eval ((Real.cos θ : ℝ) : ℂ) := by
  rw [chebyScaled, eval_comp]
  congr 1
  push_cast
  rw [eval_mul, eval_C, eval_X]
  ring

open Real in
/-- `chebyScaled n` vanishes at every `2·cos((k+1)π/(n+1))`. -/
lemma chebyScaled_eval_root (n k : ℕ) (hk : k < n) :
    (chebyScaled n).eval ((2 * Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) : ℝ) : ℂ) = 0 := by
  set θ : ℝ := ((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) with hθ
  rw [chebyScaled_eval_two_cos]
  have hsin_ne : Real.sin θ ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [hθ]; positivity
    · rw [hθ, div_lt_iff₀ (by positivity)]
      have : ((k : ℝ) + 1) < (n : ℝ) + 1 := by
        have : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk
        linarith
      nlinarith [Real.pi_pos]
  rw [Complex.ofReal_cos]
  have key := Chebyshev.U_complex_cos ((θ : ℝ) : ℂ) (n : ℤ)
  have hsinθ : Complex.sin ((θ : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hsin_ne
  -- `sin((n+1)θ) = 0` since `(n+1)θ = (k+1)π`
  have hangle : (((n : ℤ) : ℂ) + 1) * ((θ : ℝ) : ℂ) = ((((k : ℝ) + 1) * Real.pi : ℝ) : ℂ) := by
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [hθ]
    push_cast
    field_simp
  have hrhs : Complex.sin ((((n : ℤ) : ℂ) + 1) * ((θ : ℝ) : ℂ)) = 0 := by
    rw [hangle, ← Complex.ofReal_sin]
    have : Real.sin (((k : ℝ) + 1) * Real.pi) = 0 := by
      rw [show ((k : ℝ) + 1) * Real.pi = ((k : ℕ) + 1 : ℕ) * Real.pi by push_cast; ring]
      exact Real.sin_nat_mul_pi (k + 1)
    rw [this]; simp
  rw [hrhs] at key
  exact (mul_eq_zero.mp key).resolve_right hsinθ

/-- `chebyScaled n` is nonzero (it is monic of degree `n`). -/
lemma chebyScaled_ne_zero (n : ℕ) : chebyScaled n ≠ 0 := by
  rw [chebyScaled]
  intro h
  have hU : Chebyshev.U ℂ (n : ℤ) ≠ 0 :=
    Chebyshev.U_ne_zero ℂ (n : ℤ) (by omega)
  -- if `U_n.comp(C 2⁻¹ X) = 0`, compose with `C 2 * X` (the inverse scaling) to get `U_n = 0`
  have hlin : (C (2⁻¹ : ℂ) * X).comp (C (2 : ℂ) * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul,
      show (2⁻¹ : ℂ) * 2 = 1 by norm_num, map_one, one_mul]
  have hcomp : ((Chebyshev.U ℂ (n : ℤ)).comp (C (2⁻¹ : ℂ) * X)).comp (C (2 : ℂ) * X)
      = Chebyshev.U ℂ (n : ℤ) := by
    rw [comp_assoc, hlin, comp_X]
  rw [h, zero_comp] at hcomp
  exact hU hcomp.symm

/-- The degree of `chebyScaled n` is at most `n`. -/
lemma chebyScaled_natDegree_le (n : ℕ) : (chebyScaled n).natDegree ≤ n := by
  rw [chebyScaled]
  have h2 : (C (2⁻¹ : ℂ) * X).natDegree ≤ 1 := by
    calc (C (2⁻¹ : ℂ) * X).natDegree ≤ (C (2⁻¹ : ℂ)).natDegree + X.natDegree := natDegree_mul_le
      _ = 0 + 1 := by rw [natDegree_C, natDegree_X]
      _ = 1 := by ring
  have h3 : (Chebyshev.U ℂ (n : ℤ)).natDegree = n := Chebyshev.natDegree_U_natCast ℂ n
  calc ((Chebyshev.U ℂ (n : ℤ)).comp (C (2⁻¹ : ℂ) * X)).natDegree
      ≤ (Chebyshev.U ℂ (n : ℤ)).natDegree * (C (2⁻¹ : ℂ) * X).natDegree := natDegree_comp_le
    _ ≤ n * 1 := by rw [h3]; gcongr
    _ = n := by ring

/-- The `n` path-eigenvalue points `2·cos((k+1)π/(n+1))`, `k ∈ range n`, as a
finset of `ℂ`. -/
noncomputable def chebyRootFinset (n : ℕ) : Finset ℂ :=
  (Finset.range n).image
    (fun k : ℕ => ((2 * Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) : ℝ) : ℂ))

lemma chebyRootFinset_card (n : ℕ) : (chebyRootFinset n).card = n := by
  rw [chebyRootFinset, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [] at hab
  -- `ofReal` injective + cos-angle injectivity on `[0,π]`
  have hreal : 2 * Real.cos (((a : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))
      = 2 * Real.cos (((b : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) :=
    Complex.ofReal_inj.mp hab
  have hcos : Real.cos (((a : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))
      = Real.cos (((b : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) := by linarith
  have hmemI : ∀ m : ℕ, m < n →
      (((m : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) ∈ Set.Icc (0 : ℝ) Real.pi := by
    intro m hm
    refine Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) < (n : ℝ) := by exact_mod_cast hm
      linarith
    nlinarith [Real.pi_pos]
  have ha' : a < n := Finset.mem_range.mp ha
  have hb' : b < n := Finset.mem_range.mp hb
  have hang := Real.injOn_cos (hmemI a ha') (hmemI b hb') hcos
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have : ((a : ℝ) + 1) * Real.pi = ((b : ℝ) + 1) * Real.pi := by
    have := congrArg (· * ((n : ℝ) + 1)) hang
    simpa [div_mul_cancel₀, hn1] using this
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have : ((a : ℝ) + 1) = ((b : ℝ) + 1) := mul_right_cancel₀ (ne_of_gt hpi) this
  have : (a : ℝ) = (b : ℝ) := by linarith
  exact_mod_cast this

/-- **The roots of `chebyScaled n` are exactly the `n` distinct path eigenvalues.** -/
theorem chebyScaled_roots_eq (n : ℕ) :
    (chebyScaled n).roots = (chebyRootFinset n).val := by
  apply roots_eq_of_degree_le_card_of_ne_zero
  · intro x hx
    rw [chebyRootFinset, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact chebyScaled_eval_root n k (Finset.mem_range.mp hk)
  · rw [chebyRootFinset_card]
    exact le_trans degree_le_natDegree (by exact_mod_cast chebyScaled_natDegree_le n)
  · exact chebyScaled_ne_zero n

/-- **The roots of `chebyScaled n` are squarefree (nodup).** -/
theorem chebyScaled_roots_nodup (n : ℕ) : (chebyScaled n).roots.Nodup := by
  rw [chebyScaled_roots_eq]
  exact (chebyRootFinset n).nodup

/-- The characteristic matrix of the path adjacency matrix is `pathCharM`. -/
theorem charmatrix_pathGraph_adjMatrix (n : ℕ) :
    haveI : DecidableRel (SimpleGraph.pathGraph n).Adj := Classical.decRel _
    charmatrix ((SimpleGraph.pathGraph n).adjMatrix ℂ) = pathCharM n := by
  classical
  funext i j
  by_cases hij : i = j
  · subst hij
    rw [charmatrix_apply_eq, SimpleGraph.adjMatrix_apply, pathCharM_diag,
      if_neg (SimpleGraph.irrefl _)]
    simp
  · rw [charmatrix_apply_ne _ _ _ hij, SimpleGraph.adjMatrix_apply, pathCharM_apply,
      if_neg (fun h => hij (Fin.ext h))]
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [if_pos hadj]
      have hA : (SimpleGraph.pathGraph n).Adj i j := by
        rw [SimpleGraph.pathGraph_adj]; omega
      rw [if_pos hA]; simp
    · rw [if_neg hadj]
      have hA : ¬ (SimpleGraph.pathGraph n).Adj i j := by
        rw [SimpleGraph.pathGraph_adj]; omega
      rw [if_neg hA]; simp

/-- The characteristic polynomial of the path adjacency matrix equals
`chebyScaled n = U_n(X/2)`. -/
theorem charpoly_pathGraph_eq_cheby (n : ℕ) :
    haveI : DecidableRel (SimpleGraph.pathGraph n).Adj := Classical.decRel _
    ((SimpleGraph.pathGraph n).adjMatrix ℂ).charpoly = chebyScaled n := by
  classical
  rw [Matrix.charpoly, charmatrix_pathGraph_adjMatrix, pathCharM_det_eq_cheby]

/-- **The characteristic polynomial of the path adjacency matrix has nodup
(squarefree) roots** — the simple-spectrum fact for `P_n`. -/
theorem charpoly_pathGraph_roots_nodup (n : ℕ) :
    haveI : DecidableRel (SimpleGraph.pathGraph n).Adj := Classical.decRel _
    (((SimpleGraph.pathGraph n).adjMatrix ℂ).charpoly).roots.Nodup := by
  classical
  rw [charpoly_pathGraph_eq_cheby]
  exact chebyScaled_roots_nodup n


end PathChebyshev

/-- The adjacency matrix of `pathWeightedGraph n` is the path adjacency matrix
`A(P_n)` valued in `ℂ` (definitionally, via `toWeighted`). -/
theorem pathWeightedGraph_adj (n : ℕ) :
    haveI : DecidableRel (SimpleGraph.pathGraph n).Adj := Classical.decRel _
    (pathWeightedGraph n).adj = (SimpleGraph.pathGraph n).adjMatrix ℂ := rfl

/-- **Path characteristic polynomial has squarefree roots ⟹ the path eigenvalues
are pairwise distinct (simple spectrum).**  Axiom-clean, via the
tridiagonal-determinant / Chebyshev identity
`charpoly(A(P_n)) = U_n(X/2)` (`PathChebyshev.charpoly_pathGraph_roots_nodup`) fed
through `injective_eigenvalues_of_charpoly_roots_nodup`. -/
theorem pathWeightedGraph_eigenvalues_injective (n : ℕ) :
    Function.Injective (pathWeightedGraph n).herm.eigenvalues := by
  classical
  apply injective_eigenvalues_of_charpoly_roots_nodup
  rw [pathWeightedGraph_adj]
  exact PathChebyshev.charpoly_pathGraph_roots_nodup n

/-- **Endpoints of `P_n` are strongly cospectral** (real / orthogonal sense).

This is the Chebyshev-eigenstructure observation: in the eigenvector basis
`ψ_k(j) = √(2/(n+1)) sin(jkπ/(n+1))`, one has `ψ_k(n) = (-1)^(k-1) ψ_k(1)`,
so every off-diagonal projector entry between endpoints `1` and `n` is
`±` the diagonal entry.

Reference: Christandl, Datta, Ekert, Landahl, *Perfect state transfer in
quantum spin networks*, Phys. Rev. Lett. 92 187902 (2004), §III; restated
in Coutinho-Godsil 2016, Example 3.4.6. -/
theorem isStronglyCospectral_pathEndpoints (n : ℕ) (hn : 2 ≤ n) :
    IsStronglyCospectral (pathWeightedGraph n)
      ⟨0, by omega⟩ ⟨n - 1, by omega⟩ :=
  -- CLOSED.  The path `P_n` has *simple spectrum*: its characteristic polynomial
  -- is the scaled Chebyshev polynomial `U_n(X/2)` (proven above via the
  -- tridiagonal-determinant three-term recurrence, `PathChebyshev`), whose `n`
  -- roots `2cos((k+1)π/(n+1))` are pairwise distinct.  Hence
  -- `pathWeightedGraph_eigenvalues_injective`, and every pair — in particular the
  -- endpoints — is strongly cospectral in the chiral (unit-phase) sense by
  -- `isStronglyCospectral_of_simple_spectrum`.
  isStronglyCospectral_of_simple_spectrum (pathWeightedGraph n)
    (pathWeightedGraph_eigenvalues_injective n) _ _

/-- **Chiral path-endpoint strong cospectrality, conditional on simple spectrum.**
The genuinely-reachable content of `isStronglyCospectral_pathEndpoints`: *given*
that the path eigenvalues are distinct (`Function.Injective (pathWeightedGraph
n).herm.eigenvalues`, the explicit Chebyshev fact `2cos(kπ/(n+1))` distinct for
`k = 1..n`), the endpoints — indeed *every* pair — are strongly cospectral in
the chiral (unit-phase) sense.  Proven axiom-cleanly by
`isStronglyCospectral_of_simple_spectrum`; isolates the path eigenvalue
distinctness as the sole remaining input. -/
theorem isStronglyCospectral_pathEndpoints_of_simpleSpectrum (n : ℕ) (hn : 2 ≤ n)
    (hinj : Function.Injective (pathWeightedGraph n).herm.eigenvalues) :
    IsStronglyCospectral (pathWeightedGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ :=
  isStronglyCospectral_of_simple_spectrum (pathWeightedGraph n) hinj _ _

/-- **Endpoints of `P_n` PST iff `n ∈ {2, 3}`** (Christandl-Datta-Ekert-Landahl
2004).  This is the corollary of `IsStronglyCospectral.isPST_iff_godsilRatio`
specialized to `P_n`: strong cospectrality always holds at endpoints
(`isStronglyCospectral_pathEndpoints`), but the Godsil ratio condition on the
eigenvalues `2 cos(kπ/(n+1))` only holds for `n = 2, 3`.

Note: the famous "PST in spin chains" *with* engineered weights (Krawtchouk,
arXiv:quant-ph/0309131) modifies the Godsil ratio condition by changing the
eigenvalues — it does not modify strong cospectrality, which is purely a
structural symmetry of the graph. -/
theorem pathEndpoints_isPST_iff (n : ℕ) (hn : 2 ≤ n) :
    (∃ τ : ℝ, 0 < τ ∧
      IsPST (pathWeightedGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ τ) ↔
    (n = 2 ∨ n = 3) := by
  -- STATUS.  The two structural inputs are now BUILT and axiom-clean:
  --  • strong cospectrality at the endpoints holds for *all* `n`
  --    (`isStronglyCospectral_pathEndpoints`, simple Chebyshev spectrum), and
  --  • the FORWARD number-theoretic obstruction — the Godsil ratio condition,
  --    i.e. arithmetic-progression membership of the support eigenvalues
  --    `2cos(kπ/(n+1))`, FAILS for every `n ≥ 4` — is now PROVEN via Niven as
  --    `pathEigenvalue_not_arithmeticProgression` (axiom-clean; the kernel is
  --    `irrational_cos_pi_div`, Mathlib `niven_angle_div_pi_eq`).
  -- RESIDUAL (one named lemma).  Assembling these into the PST biconditional
  -- still routes through the Godsil existence bridge
  -- `IsStronglyCospectral.isPST_iff_godsilRatio` (PST ⟺ strong cospectrality ∧
  -- Godsil ratio), whose proof is the deep Kronecker/Dirichlet simultaneous-
  -- approximation half and remains an honest `sorry` in that single lemma.
  -- Once that bridge lands, the forward `n ≥ 4 → ¬PST` direction is exactly
  -- `pathEigenvalue_not_arithmeticProgression`, and the backward `n ∈ {2,3} → PST`
  -- direction is the finite `K_2`/`P_3` exponential.
  -- BLOCKED ON: IsStronglyCospectral.isPST_iff_godsilRatio (Diophantine bridge).
  sorry

/-! ## Phantom symmetry (Bachman-Tamon 1108.0339)

A pair `(u, v)` is **phantom symmetric** if it is strongly cospectral but
*not* witnessed by any graph automorphism.  When a non-trivial automorphism
swapping `u ↔ v` exists, strong cospectrality is automatic by the
representation-theoretic argument (the swap is in the centralizer of the
adjacency action).  Phantom-symmetric pairs are the *genuinely new* PST
candidates: their existence shows that PST cannot be detected by symmetry
alone, and is the central observation of Bachman-Tamon (arXiv:1108.0339).
-/

/-- A pair `(u, v)` is **phantom symmetric** in `G` if it is strongly
cospectral but no graph automorphism of `G` swaps `u` and `v`.

In particular phantom-symmetric pairs cannot be detected by group-theoretic
methods; their existence is the algebraic-graph-theoretic content of
Bachman-Tamon (arXiv:1108.0339). -/
def IsPhantomSymmetric (G : WeightedGraph V) (u v : V) : Prop :=
  IsStronglyCospectral G u v ∧
    ¬ ∃ σ : V ≃ V,
      (∀ x y, G.adj (σ x) (σ y) = G.adj x y) ∧ σ u = v

/-- **Existence of phantom-symmetric pairs** (Bachman-Tamon arXiv:1108.0339).

There exist Hermitian-weighted graphs `G` with phantom-symmetric vertex pairs
exhibiting PST.  Concretely, Bachman-Tamon construct quotient graphs (via
equitable partitions of vertex-transitive graphs) where the quotient admits
PST between cells whose preimages are *not* swapped by any automorphism of the
original graph.

This is the *raison d'être* of the equitable-partition lift theory in
`Graphplay.Spectral` / `Graphplay.PST`: phantom symmetry is "explained by"
the equitable quotient, even when it is invisible to the automorphism group
of the parent graph. -/
theorem exists_phantomSymmetric_isPST :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : WeightedGraph V) (u v : V) (τ : ℝ),
      0 < τ ∧ IsPhantomSymmetric G u v ∧ IsPST G u v τ := by
  -- Bachman-Tamon construction: take a vertex-transitive parent graph G',
  -- pick an equitable partition P', the quotient G = P'.quotient gives the
  -- phantom-symmetric pair (cell_i, cell_j) when no automorphism of G'
  -- exchanges the preimage cells while every automorphism of G does (or
  -- vice versa).  Detailed construction punted.
  -- BLOCKED: needs an explicit Bachman-Tamon witness graph with computed
  -- evolution exhibiting PST (no concrete construction available).
  sorry

/-! ## Convenience consequences -/

/-- Strong cospectrality is symmetric in `u, v`. -/
theorem IsStronglyCospectral.symm {G : WeightedGraph V} {u v : V}
    (h : IsStronglyCospectral G u v) : IsStronglyCospectral G v u := by
  intro lam hlam
  obtain ⟨ε, hε, heq⟩ := h lam hlam
  refine ⟨star ε, ?_, ?_⟩
  · simpa using hε
  · -- `eigenProjEntry G lam v u = star (eigenProjEntry G lam u v)`, and the
    -- product `ε * √(diag u · diag v)` becomes `star ε * √(diag v · diag u)`
    -- under conjugation.
    rw [eigenProjEntry_conj_symm, heq]
    -- `star (ε * √(diag u · diag v)) = star ε * √(diag v · diag u)`
    rw [star_mul']
    congr 1
    -- the geometric-mean factor is a real coercion, fixed by `star`, and the
    -- product under the root is symmetric in `u, v`
    rw [mul_comm (eigenProjDiag G lam v) (eigenProjDiag G lam u)]
    rw [Complex.star_def, Complex.conj_ofReal]

/-- Strong cospectrality is reflexive: every vertex is strongly cospectral
with itself (with trivial phase). -/
theorem IsStronglyCospectral.refl (G : WeightedGraph V) (u : V) :
    IsStronglyCospectral G u u := by
  intro lam _
  refine ⟨1, by simp, ?_⟩
  -- `eigenProjEntry G lam u u = diag G lam u` and `√(diag · diag) = diag`.
  rw [eigenProjEntry_diag_eq_ofReal, one_mul]
  congr 1
  -- `diag = √(diag * diag)` because `diag ≥ 0`
  rw [Real.sqrt_mul_self (eigenProjDiag_nonneg G lam u)]

/-- A graph automorphism swapping `u, v`, **together with a simple spectrum**,
implies strong cospectrality.

HONEST CORRECTION.  A bare automorphism `σ u = v` does **not** suffice for strong
cospectrality (in a vertex-transitive graph every pair admits such a `σ`, yet
strong cospectrality is rare); the swap alone yields only *cospectrality*
(`isCospectral_of_aut`, proven axiom-cleanly above).  The extra input that makes
the conclusion true is that each eigenspace be one-dimensional, so that the
automorphism — which commutes with every spectral projector — acts as a scalar
on it (the path-flip is exactly this case).  Under `hinj`, the conclusion is
*independent* of the automorphism (simple spectrum already forces every pair to
be strongly cospectral, `isStronglyCospectral_of_simple_spectrum`); we keep the
automorphism hypothesis for the Godsil-Royle 8.2.1 reading.

Proven axiom-cleanly via the spectral-projector uniqueness developed in the
sibling `GodsilRatio` (`eigenProj_aut_invariant`,
`isStronglyCospectral_of_injective_eigenvalues`). -/
theorem IsStronglyCospectral.of_aut
    (G : WeightedGraph V) (u v : V)
    (σ : V ≃ V) (_hσ : ∀ x y, G.adj (σ x) (σ y) = G.adj x y) (_huv : σ u = v)
    (hinj : Function.Injective G.herm.eigenvalues) :
    IsStronglyCospectral G u v :=
  isStronglyCospectral_of_simple_spectrum G hinj u v

end Graphplay

