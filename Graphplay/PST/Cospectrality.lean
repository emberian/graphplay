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
2. `isStronglyCospectral_iff`: the equivalent "diagonal-of-projector and
   matched off-diagonal entry" characterization familiar from
   Godsil-Royle / Coutinho-Godsil.
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
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
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

/-- **Classical equivalence (Godsil-Royle / Coutinho-Godsil 2016).**
`u, v` are strongly cospectral iff they are cospectral *and* for every
eigenvalue `λ` the off-diagonal projector entry `⟨u, P_λ v⟩` equals a phase
`ε_λ` of unit modulus times the (common) diagonal entry
`⟨u, P_λ u⟩ = ⟨v, P_λ v⟩`.

This is the form used in the proof of the PST existence criterion
(Coutinho-Godsil §2-3, Bachman-Tamon arXiv:1108.0339). -/
theorem isStronglyCospectral_iff (G : WeightedGraph V) (u v : V) :
    IsStronglyCospectral G u v ↔
      IsCospectral G u v ∧
        ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
          ∃ ε : ℂ, ‖ε‖ = 1 ∧
            eigenProjEntry G lam u v
              = ε * Complex.ofReal (eigenProjDiag G lam u) := by
  -- The proof packages Cauchy-Schwarz equality (parallelism iff |cross|
  -- saturates the geometric-mean bound) with the cospectrality identity
  -- `diag u = diag v`.  Citation: Godsil-Royle AGT §8.2; Coutinho-Godsil
  -- 2016 Theorem 3.4.1 / Corollary 2.5.2.
  --
  -- HONEST STATUS.  Only the `←` direction is unconditionally true for the
  -- *geometric-mean* encoding of `IsStronglyCospectral` used here; it is
  -- discharged by `isStronglyCospectral_of_cospectral_matched` below.  The
  -- `→` direction is the genuinely deep half: the saturation
  -- `|(E_λ)_{u,v}| = √((E_λ)_{u,u}(E_λ)_{v,v})` is exactly Cauchy-Schwarz
  -- equality, i.e. *parallelism* `P_λ e_u ∥ P_λ e_v` (Coutinho's "parallel"),
  -- which by Corollary 2.5.2 yields strong cospectrality only *together with*
  -- cospectrality `(E_λ)_{u,u} = (E_λ)_{v,v}`.  Cospectrality does not follow
  -- from parallelism alone (Coutinho 2.5.2 states them as independent
  -- hypotheses), so `→` needs the idempotency/Gram input `(E_λ)_{u,v} =
  -- ⟨P_λ e_u, P_λ e_v⟩` plus the cospectrality argument and is left sorried.
  refine ⟨?_, ?_⟩
  · -- `→`: parallelism ⇏ cospectrality without the extra Gram input. Deep.
    -- BLOCKED: geometric-mean encoding loses cospectrality (E_λ)_{u,u}=(E_λ)_{v,v};
    -- needs Gram identity (E_λ)_{u,v}=⟨P_λ e_u,P_λ e_v⟩, not in this def.
    sorry
  · -- `←`: cospectral + matched off-diagonal ⇒ geometric-mean form. Honest.
    rintro ⟨hcosp, hmatch⟩
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

/-- **Endpoints of `P_n` are strongly cospectral** (real / orthogonal sense).

This is the Chebyshev-eigenstructure observation: in the eigenvector basis
`ψ_k(j) = √(2/(n+1)) sin(jkπ/(n+1))`, one has `ψ_k(n) = (-1)^(k-1) ψ_k(1)`,
so every off-diagonal projector entry between endpoints `1` and `n` is
`±` the diagonal entry.

Reference: Christandl, Datta, Ekert, Landahl, *Perfect state transfer in
quantum spin networks*, Phys. Rev. Lett. 92 187902 (2004), §III; restated
in Coutinho-Godsil 2016, Example 3.4.6. -/
theorem isStronglyCospectral_pathEndpoints (n : ℕ) (hn : 2 ≤ n) :
    IsRealStronglyCospectral (pathWeightedGraph n)
      ⟨0, by omega⟩ ⟨n - 1, by omega⟩ := by
  -- Direct computation in the Chebyshev basis; cite Christandl et al.
  -- ISOLATED REMAINDER.  The chiral (unit-phase) strong cospectrality of *any*
  -- pair now reduces, axiom-cleanly, to *simple spectrum* via
  -- `isStronglyCospectral_of_simple_spectrum` — see the chiral corollary
  -- `isStronglyCospectral_pathEndpoints_of_simpleSpectrum` below.  Two honest
  -- inputs remain to land the REAL (±1) version stated here:
  --   (i) injectivity of `(pathWeightedGraph n).herm.eigenvalues` — the
  --       distinctness of the path eigenvalues `2cos(kπ/(n+1))`, `k=1..n`,
  --       which is the genuinely missing explicit-eigenvalue fact (Mathlib has
  --       no path eigenstructure);
  --   (ii) realness of the eigenvector entries (true since `P_n` is real
  --        symmetric) to upgrade the unit phase to a sign `±1`.
  -- BLOCKED on (i): the Niven/Chebyshev distinctness of `2cos(kπ/(n+1))`.
  sorry

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
  -- Combine `isStronglyCospectral_pathEndpoints` with the eigenvalue
  -- analysis of `2 cos(kπ/(n+1))`.  Punted.
  -- BLOCKED: needs path-graph eigenvalues 2cos(kπ/(n+1)) and the Godsil-ratio
  -- arithmetic that holds only for n∈{2,3} (depends on isPST_iff_godsilRatio).
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

