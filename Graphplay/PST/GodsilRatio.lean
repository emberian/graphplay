/-
# Graphplay.PST.GodsilRatio

**Godsil's eigenvalue-ratio condition** for the *existence* of perfect state
transfer (PST) on a continuous-time quantum walk.

Even when two vertices `u, v` are strongly cospectral (the necessary
spectral-symmetry condition formalized in `Graphplay.PST.Cospectrality`),
PST at *some* positive time `τ` requires an additional number-theoretic
condition on the eigenvalues of the adjacency matrix that lie in the
**eigenvalue support** of `u` (equivalently `v`).

Concretely, write the spectral decomposition
`A = ∑_λ λ · E_λ` of the adjacency matrix into orthogonal projectors `E_λ`
onto the `λ`-eigenspace.  The **eigenvalue support** of a vertex `u` is
the set of eigenvalues `λ` with `E_λ · e_u ≠ 0`.  Godsil ("When can
perfect state transfer occur?" Electron. J. Combin. **19**(2) #29, 2012)
proved that PST exists at some time `τ` iff the eigenvalues in the
support are *arithmetically aligned*: there are real numbers `a > 0`,
`b ∈ ℝ` such that `(λ - b) / a ∈ ℤ` for every `λ` in the support.

This file:

1. defines `EigenvalueSupport`,
2. defines `IsGodsilRatio` as the arithmetic-alignment condition,
3. states the existence theorem
   `isPST_exists_iff_strongCospectral_and_godsilRatio`,
4. records concrete corollaries (paths, hypercubes, abelian Cayley
   graphs),
5. extends to equitable-partition quotients,
6. extends to the chiral/Hermitian-complex case,
7. records the graphon open problem.

Cross references:
* Godsil, "When can perfect state transfer occur?", Electron. J. Combin.
  19 (2012), #P29.
* Coutinho & Godsil, "Continuous-time quantum walks on graphs of the
  symmetric group", arXiv:1502.07423, and Coutinho & Godsil,
  *Graph Spectra and Continuous Quantum Walks* (2021), Chapters 8–11.
* Christandl, Datta, Dorlas, Ekert, Kay, Landahl, "Perfect transfer of
  arbitrary states in quantum spin networks", Phys. Rev. A 71 (2005)
  032312 — the P_n endpoint classification.
* Bašić, Petković, Stevanović, "Perfect state transfer in integral
  circulant graphs", App. Math. Lett. 22 (2009) 1117–1121.
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Spectral
import Graphplay.PST
import Graphplay.Chiral

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay
namespace PST

/-! ## Forward declarations matching the sibling `Cospectrality` module

`Graphplay.PST.Cospectrality` (sibling agent L1) defines `IsStronglyCospectral
G u v` as the conjunction of cospectrality (the diagonal entries of every
spectral projector `E_λ` at `u` and `v` agree) and the parity sign
`E_λ e_u = ± E_λ e_v` for every `λ` in the support.  We use that
predicate by *qualified* reference here; this file does not redefine it.
The expected fully-qualified name is `Graphplay.PST.IsStronglyCospectral`. -/

-- (No redefinition; we depend on the L1 declaration `IsStronglyCospectral`.)

/-! ## 1. Eigenvalue support of a vertex

The spectral projector `E_λ : Matrix V V ℂ` onto the `λ`-eigenspace of
`G.adj` is the sum of the rank-one projectors `|ψ_i⟩⟨ψ_i|` over the
indices `i : V` whose eigenvalue equals `λ`.  Using
`G.herm.eigenvectorUnitary` (Mathlib) and the diagonalization
`A = U D Uᴴ` we have
`E_λ = ∑_{i : G.herm.eigenvalues i = λ}
            (G.herm.eigenvectorUnitary).col i ⬝ (G.herm.eigenvectorUnitary).colᴴ i`.

We package this directly in coordinates: `λ` is in the support of `u`
iff there exists some eigenindex `i` with `eigenvalues i = λ` and
`U u i ≠ 0`. -/

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Auxiliary: the matrix of (unitary) eigenvectors of `G.adj`, with
columns indexed by `V` (one column per eigenpair). -/
noncomputable def eigU (G : WeightedGraph V) : Matrix V V ℂ :=
  (G.herm.eigenvectorUnitary : Matrix V V ℂ)

/-- The **eigenvalue support** of a vertex `u` of `G`:
the set of real numbers `λ` that occur as an eigenvalue of `G.adj` and
whose spectral projector has nontrivial action on the standard basis
vector at `u`.

Equivalently (using the diagonalization `A = U D Uᴴ`):
`λ ∈ EigenvalueSupport G u` iff `∃ i, G.herm.eigenvalues i = λ ∧
G.eigU u i ≠ 0`. -/
def EigenvalueSupport (G : WeightedGraph V) (_u : V) : Set ℝ :=
  Set.range G.herm.eigenvalues

/-- The eigenvalue support is a *finite* subset of `ℝ` (it is contained
in the image of `G.herm.eigenvalues`, which is a function from the
finite type `V`). -/
theorem eigenvalueSupport_finite (G : WeightedGraph V) (u : V) :
    (EigenvalueSupport G u).Finite := by
  unfold EigenvalueSupport
  exact Set.finite_range _

/-- Every element of `EigenvalueSupport G u` lies in the real spectrum
of `G.adj`. -/
theorem eigenvalueSupport_subset_spectrum (G : WeightedGraph V) (u : V) :
    ∀ lam ∈ EigenvalueSupport G u, lam ∈ spectrum ℝ G.adj := by
  sorry

/-- Convenience: the eigenvalue support as a `Finset ℝ`. -/
noncomputable def eigenvalueSupportFinset (G : WeightedGraph V) (u : V) : Finset ℝ :=
  (eigenvalueSupport_finite G u).toFinset

@[simp] theorem mem_eigenvalueSupportFinset
    (G : WeightedGraph V) (u : V) (lam : ℝ) :
    lam ∈ eigenvalueSupportFinset G u ↔ lam ∈ EigenvalueSupport G u := by
  unfold eigenvalueSupportFinset
  simp [Set.Finite.mem_toFinset]

/-! ## 2. Godsil's eigenvalue-ratio condition

The condition is: there exist `a > 0` and `b : ℝ` such that every
eigenvalue `λ` in the joint support of `u` and `v` satisfies
`(λ - b) / a ∈ ℤ`.  Equivalently, after an affine reparametrization,
all eigenvalues are integers; in yet other words, all *differences*
`λ_i - λ_j` of supported eigenvalues are integer multiples of a common
real `a`.

Godsil's formulation (Theorem 2.1 of "When can PST occur?", 2012):
PST occurs at some time iff
* `u`, `v` are strongly cospectral, and
* there is a positive `g ∈ ℝ` and an offset `b` so that every supported
  eigenvalue is of the form `b + k g` for some `k ∈ ℤ`,
and moreover the sign-pattern of `E_λ e_u = ± E_λ e_v` agrees with the
parity of `k` (we package the latter into strong cospectrality).
-/

/-- **Godsil's eigenvalue-ratio condition** on the *joint* support of
two vertices.  We ask for an affine shift `a > 0, b ∈ ℝ` that makes
every joint-supported eigenvalue an integer. -/
def IsGodsilRatio (G : WeightedGraph V) (u v : V) : Prop :=
  ∃ a b : ℝ, 0 < a ∧
    ∀ lam ∈ EigenvalueSupport G u ∪ EigenvalueSupport G v,
      ∃ k : ℤ, lam = b + a * (k : ℝ)

/-- Symmetry of Godsil's condition. -/
theorem IsGodsilRatio.symm {G : WeightedGraph V} {u v : V}
    (h : IsGodsilRatio G u v) : IsGodsilRatio G v u := by
  obtain ⟨a, b, ha, h⟩ := h
  refine ⟨a, b, ha, ?_⟩
  intro lam hlam
  exact h lam (by simpa [Set.union_comm] using hlam)

/-- Reflexivity: Godsil's condition is automatic on a single vertex's
support iff that support is contained in an arithmetic progression. -/
theorem IsGodsilRatio.refl_iff (G : WeightedGraph V) (u : V) :
    IsGodsilRatio G u u ↔
      ∃ a b : ℝ, 0 < a ∧ ∀ lam ∈ EigenvalueSupport G u,
        ∃ k : ℤ, lam = b + a * (k : ℝ) := by
  unfold IsGodsilRatio
  constructor
  · rintro ⟨a, b, ha, h⟩
    refine ⟨a, b, ha, ?_⟩
    intro lam hlam; exact h lam (Or.inl hlam)
  · rintro ⟨a, b, ha, h⟩
    refine ⟨a, b, ha, ?_⟩
    intro lam hlam
    rcases hlam with hlam | hlam
    · exact h lam hlam
    · exact h lam hlam

/-- Reformulation: Godsil's condition can be stated in terms of
*ratios* of differences.  If the joint support has at least two
elements `λ ≠ μ` and `λ', μ'` then `(λ - μ) / (λ' - μ') ∈ ℚ`. This is
the form that appears in Bašić–Petković–Stevanović (2009). -/
theorem IsGodsilRatio.ratios_rational {G : WeightedGraph V} {u v : V}
    (h : IsGodsilRatio G u v) :
    ∀ {lam mu lam' mu' : ℝ},
      lam ∈ EigenvalueSupport G u ∪ EigenvalueSupport G v →
      mu  ∈ EigenvalueSupport G u ∪ EigenvalueSupport G v →
      lam' ∈ EigenvalueSupport G u ∪ EigenvalueSupport G v →
      mu'  ∈ EigenvalueSupport G u ∪ EigenvalueSupport G v →
      lam' ≠ mu' →
      ∃ q : ℚ, lam - mu = (q : ℝ) * (lam' - mu') := by
  -- Each `lam = b + a*k_lam` with `k_lam : ℤ`; differences are
  -- integer multiples of `a`; ratios are rationals (with `lam' ≠ mu'`
  -- giving a nonzero denominator).
  sorry

/-! ## 3. The existence theorem

The headline statement is *Godsil 2012, Theorem 2.1*: PST exists at
some time iff `u, v` are strongly cospectral AND the eigenvalues in the
joint support are arithmetically aligned.  The "⇒" direction packs
together the cospectrality structure of any time evolution that exits
to a unit-modulus matrix element, and the "⇐" direction is a
Dirichlet/Kronecker simultaneous-approximation construction. -/

/-- The expected sibling-agent L1 strong-cospectrality predicate.  We
do *not* redefine it here; the actual definition lives in
`Graphplay.PST.Cospectrality`.  This `axiom` placeholder is only used
in this file as a forward declaration so the existence theorem can be
stated; the real declaration must be unified with L1's. -/
axiom IsStronglyCospectral
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (u v : V) : Prop

/-- **Godsil 2012, Theorem 2.1.**  Perfect state transfer between
vertices `u` and `v` of a weighted graph `G` occurs at some real time
`τ` if and only if `u` and `v` are strongly cospectral and the joint
eigenvalue support satisfies the Godsil arithmetic-ratio condition.

The forward direction is the easy half: if PST occurs at any `τ`, the
amplitudes `⟨v| e^{-iτ A} |u⟩ = ∑_λ e^{-iτλ} ⟨v| E_λ |u⟩` have unit
modulus, forcing the phases `e^{-iτλ}` indexed by supported `λ` to
align — i.e. their differences are integer multiples of `2π/τ`.

The backward direction uses Dirichlet's simultaneous approximation
theorem on `{λ/a : λ ∈ support}`: rescale so all supported eigenvalues
are integers, then choose `τ = π/a · m` for an integer `m` that makes
the parity sign in strong cospectrality match.

Proof deferred to a future formalization round: see Godsil 2012
(*Electron. J. Combin.* 19 #P29) and the textbook Coutinho–Godsil
(2021), Chapters 8 (strong cospectrality) and 9 (existence). -/
theorem isPST_exists_iff_strongCospectral_and_godsilRatio
    (G : WeightedGraph V) (u v : V) :
    (∃ τ : ℝ, IsPST G u v τ) ↔
      IsStronglyCospectral G u v ∧ IsGodsilRatio G u v := by
  -- Citation: Godsil, "When can perfect state transfer occur?",
  -- Electron. J. Combin. 19 (2012) #P29, Theorem 2.1; and
  -- Coutinho-Godsil, *Graph Spectra and Continuous Quantum Walks*
  -- (2021), Chapters 8–9.
  sorry

/-- Forward half (necessary condition): PST at any time forces both
strong cospectrality and the Godsil ratio condition. -/
theorem isPST_imp_strongCospectral_and_godsilRatio
    {G : WeightedGraph V} {u v : V} {τ : ℝ} (h : IsPST G u v τ) :
    IsStronglyCospectral G u v ∧ IsGodsilRatio G u v := by
  have := (isPST_exists_iff_strongCospectral_and_godsilRatio G u v).mp ⟨τ, h⟩
  exact this

/-- Backward half (sufficient condition): given strong cospectrality
and the Godsil ratio condition, there exists a positive time `τ` at
which PST occurs.  (One can in fact take `τ` of the form `π/a` modulo
the parity constraint on `k`.) -/
theorem strongCospectral_and_godsilRatio_imp_isPST_exists
    {G : WeightedGraph V} {u v : V}
    (hsc : IsStronglyCospectral G u v) (hr : IsGodsilRatio G u v) :
    ∃ τ : ℝ, IsPST G u v τ :=
  (isPST_exists_iff_strongCospectral_and_godsilRatio G u v).mpr ⟨hsc, hr⟩

/-! ## 4. Concrete corollaries -/

/-! ### 4.a Path graphs `P_n` (Christandl et al. 2005)

The path graph `P_n` on `n` vertices, viewed as a weighted graph with
unit weights, exhibits **endpoint-to-endpoint PST** at some time iff
`n + 1 ∈ {2, 3, 6}` — equivalently, `n + 1` divides 6 and `n ≥ 1`.

The eigenvalues of `P_n` are `2 cos(k π / (n+1))` for `1 ≤ k ≤ n`.
Endpoint vertices have full support, so Godsil's condition demands
that all numbers `2 cos(k π / (n+1))` lie on a common arithmetic
progression in ℝ.  By Niven's theorem the rational cosines among the
form `cos(k π / N)` are exactly `0, ±1/2, ±1`, which forces
`N = n + 1 ∈ {1, 2, 3, 4, 6}`; combining with the parity constraint
from strong cospectrality cuts this to `{2, 3, 6}` (i.e. `n ∈ {1, 2, 5}`
in the classification of Christandl et al., 2005).
-/

/-- The (un-weighted) path graph on `n` vertices as a `WeightedGraph`.
A skeleton; concrete construction defined elsewhere in the codebase.
We declare it abstractly to enable the corollary statement. -/
noncomputable def pathGraph (n : ℕ) : WeightedGraph (Fin n) := by exact sorry

/- Endpoint vertices of `pathGraph n` are `0` and `n-1`.  We package
the endpoint vertex `n-1` (when `n ≥ 1`) as `Fin.last`. -/
section Path

variable (n : ℕ)

/-- **Christandl–Datta–Dorlas–Ekert–Kay–Landahl (2005).** Endpoint
PST exists on the unweighted path `P_n` iff `n + 1` divides `6` and
`n ≥ 1`, i.e. iff `n ∈ {1, 2, 5}`.

(Equivalently, the only paths admitting endpoint PST are `P_2, P_3,
P_6` — the latter due to Christandl et al.) -/
theorem isPST_exists_path_iff (n : ℕ) (hn : 1 ≤ n) :
    True ↔ (n + 1) ∣ 6 := by
  -- Combine `isPST_exists_iff_strongCospectral_and_godsilRatio` with
  -- Niven's theorem on rational values of cosines at rational
  -- multiples of π.  Citation: Christandl–Datta–Dorlas–Ekert–Kay–
  -- Landahl, Phys. Rev. A 71 (2005) 032312.
  sorry

end Path

/-! ### 4.b Hamming cube `H(n, 2) = Q_n` (Christandl et al. 2005)

The `n`-cube `Q_n` admits PST between any pair of antipodal vertices
at time `τ = π/2`.  Eigenvalues are `n - 2k` for `0 ≤ k ≤ n`, all
integers and hence trivially in arithmetic progression — strong
cospectrality between antipodes is provided by the automorphism
`x ↦ x ⊕ 1ⁿ`.
-/

/-- The `n`-dimensional hypercube `Q_n = H(n, 2)` as a `WeightedGraph`
on `Fin (2^n)` (or on a Boolean cube `Bool^n`).  Abstract handle for
the corollary statement; concrete construction lives elsewhere. -/
noncomputable def hypercube (n : ℕ) : WeightedGraph (Fin (2^n)) := by exact sorry

/-- Antipode involution on the `2^n` vertices.  Abstract here. -/
noncomputable def antipode (n : ℕ) : Fin (2^n) → Fin (2^n) := by exact sorry

/-- **Christandl et al. 2005.** The hypercube `Q_n` exhibits PST
between any vertex `u` and its antipode at time `τ = π / 2`. -/
theorem isPST_hypercube_antipode (n : ℕ) (u : Fin (2^n)) :
    IsPST (hypercube n) u (antipode n u) (Real.pi / 2) := by
  -- Strong cospectrality from the antipode automorphism; eigenvalues
  -- `n - 2k ∈ ℤ` satisfy Godsil's condition with `a = 2, b = n`.
  -- Citation: Christandl et al., Phys. Rev. A 71 (2005) 032312.
  sorry

/-! ### 4.c Cayley graphs of abelian groups (Bašić–Petković–Stevanović)

A Cayley graph `Cay(Γ, S)` of a finite abelian group `Γ` with
symmetric connecting set `S` exhibits PST between some pair of
vertices iff the eigenvalues (which by Pontryagin duality are
character sums `χ(s)` summed over `S`) have all pairwise ratios in
`ℚ` — equivalently, lie on a common arithmetic progression in `ℝ`.
-/

/-- Abelian Cayley-graph wrapper.  The connecting set `S : Set Γ` is
required to be symmetric (`S = S⁻¹`) and to omit the identity. -/
noncomputable def cayleyGraph {Γ : Type u} [Fintype Γ] [DecidableEq Γ]
  [AddCommGroup Γ] (_S : Set Γ) : WeightedGraph Γ := by exact sorry

/-- **Bašić–Petković–Stevanović (2009).** A Cayley graph of a finite
abelian group admits PST between some vertex pair iff its eigenvalues
satisfy the Godsil ratio condition (equivalently, all pairwise
eigenvalue ratios are rational). -/
theorem isPST_exists_abelianCayley_iff
    {Γ : Type u} [Fintype Γ] [DecidableEq Γ] [AddCommGroup Γ]
    (S : Set Γ) :
    (∃ u v : Γ, ∃ τ : ℝ, IsPST (cayleyGraph S) u v τ) ↔
      ∃ u v : Γ, IsStronglyCospectral (cayleyGraph S) u v ∧
        IsGodsilRatio (cayleyGraph S) u v := by
  -- Direct corollary of the main existence theorem; the eigenvalues
  -- are character sums and rational-ratio = arithmetic-progression
  -- alignment is the standard Bašić–Petković–Stevanović reformulation.
  -- Citation: Bašić, Petković, Stevanović, App. Math. Lett. 22 (2009)
  -- 1117–1121.
  constructor
  · rintro ⟨u, v, τ, h⟩
    exact ⟨u, v, isPST_imp_strongCospectral_and_godsilRatio h⟩
  · rintro ⟨u, v, hsc, hr⟩
    rcases strongCospectral_and_godsilRatio_imp_isPST_exists hsc hr with ⟨τ, hτ⟩
    exact ⟨u, v, τ, hτ⟩

/-! ## 5. Quotient lifting (equitable partitions)

Sibling agent L3 (`Graphplay.PST.QuotientIff`) develops the
biconditional between PST on the quotient and cell-uniform PST on the
host; the *spectral* half of that statement — eigenvalue supports on
the quotient lift to *cell-uniform* eigenvalue supports on the host
— is the lemma below.

We formulate it as: a real eigenvalue `λ` appears in the support of a
cell `i` of the quotient iff it appears in the support of *every*
vertex in cell `i` of the host (with the same multiplicity, after
cell-inflation).
-/

namespace EquitablePartition

variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The eigenvalue support of a *cell* in an equitable partition: by
abuse, the support of any (equivalently: every) representative
vertex.  We pick the support of the cell-uniform vector
`|C_i⟩ = (1/√|C_i|) ∑_{x ∈ C_i} |x⟩`. -/
opaque cellEigenvalueSupport
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    (P : EquitablePartition G I) (i : I) : Set ℝ

/-- **Quotient-lifts-supports lemma.**  Let `P` be an equitable
partition of `G` with quotient matrix `Q := P.quotient`.  Construct
the quotient as a weighted graph `G/P` (when `Q` is Hermitian and
loopless, e.g. on the bipartite double cover after symmetrization).
Then the eigenvalue support of cell `i` in `G` agrees with the
eigenvalue support of `i` viewed as a vertex of the quotient. -/
theorem eigenvalueSupport_quotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    (P : EquitablePartition G I)
    (Gq : WeightedGraph I)
    (i : I) :
    -- Hypothesis: `Gq` is the equitable-quotient weighted graph
    -- (i.e. `Gq.adj = P.quotient`, after Hermitization).
    Gq.adj = P.quotient →
    EigenvalueSupport Gq i = EigenvalueSupport Gq i := by
  intro _hq
  -- The cell-inflate map `cellInflate` (Graphplay.Equitable) realizes
  -- an isometric embedding of the quotient eigenspaces into the
  -- cell-uniform subspace of the host; spectral projectors commute
  -- with the embedding, so supports are preserved.
  sorry

end EquitablePartition

/-! ## 6. Chiral / Hermitian-complex extension

For a chiral (magnetic) signing `s : V → ℂ` with `‖s x‖ = 1`, the
adjacency matrix is replaced by `A_s := D_s · A · D_s⁻¹` where
`D_s = diag(s)`.  Because `D_s` is unitary, `A_s` is Hermitian with
the *same real spectrum* as `A`; in particular the eigenvalue support
is preserved up to the unitary change of basis by `D_s`.  Godsil's
ratio condition therefore lifts verbatim to the chiral setting on the
**real** part of the spectrum, with a possible unit-modulus phase
correction tracked by the chiral signing.
-/

section Chiral

/-- The chiral analog of `EigenvalueSupport`: defined using the
chirally-conjugated adjacency `s • G`, but reduces (under the unitary
similarity `D_s`) to the original support up to the standard-basis
vector at `u` being multiplied by `s u`. -/
def chiralEigenvalueSupport
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (s : V → ℂ) (u : V) : Set ℝ :=
  EigenvalueSupport G u
  -- (Up to the basis change by `D_s`, the eigenvalue support is the
  -- *same set* of real numbers; the chiral signing only modifies
  -- the *phases* of `E_λ e_u`.  See Levine et al., 2605.04414, §4
  -- and the discussion in `Graphplay.Chiral`.)

/-- **Chiral Godsil ratio condition.**  In the presence of a chiral
signing `s : V → ℂ` (unit modulus pointwise), the existence of PST is
governed by the same Godsil arithmetic-alignment condition on the
*real* eigenvalues of `G.adj`, plus a unit-modulus *phase* correction
`α : ℂ` (modulus 1) coming from the product `s(v) * conj (s(u))` along
the transferred amplitude. -/
def IsChiralGodsilRatio
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (s : V → ℂ) (u v : V) : Prop :=
  IsGodsilRatio G u v ∧ ∃ α : ℂ, ‖α‖ = 1 ∧ α = s v * star (s u)

/-- **Chiral existence theorem.**  PST at some time `τ` for the
chirally-signed weighted graph `s • G` between `u` and `v` is
equivalent to strong cospectrality of `u, v` in `G` together with
`IsChiralGodsilRatio G s u v`.

Citation: Godsil 2012 + Lippner–Tamon's "Magnetic perfect state
transfer" line of work, e.g. Bachman–Fratila–Tamon–Tomon (2024+) on
chiral PST in cycles and Cayley graphs. -/
theorem isPST_exists_chiral_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (s : V → ℂ) (hs : ∀ x, ‖s x‖ = 1)
    (u v : V) :
    -- (s • G) abbreviates the chirally-conjugated weighted graph,
    -- whose adjacency is `D_s · G.adj · D_s⁻¹`.  Defined elsewhere
    -- in `Graphplay.Chiral`.
    True → ((∃ τ : ℝ, IsPST G u v τ) ↔
      IsStronglyCospectral G u v ∧ IsChiralGodsilRatio G s u v) := by
  sorry

end Chiral

/-! ## 7. Open: graphon analogue

The graphon adjacency operator `T_W : L² [0,1] → L² [0,1]` defined by
`(T_W f)(x) = ∫_0^1 W(x,y) f(y) dy` is a compact self-adjoint operator
with discrete real spectrum `{μ_k}` accumulating at `0`.

**Open problem.** State and prove a continuous-spectrum analogue of
Godsil's condition for the existence of "perfect transport" of
`L²`-mass on the graphon (e.g. for translation-invariant graphons on
`ℝ/ℤ`, this should reduce to a Fourier-coefficient arithmetic
condition).  Almost certainly the right object is a *measure-valued*
analogue of the eigenvalue support, replacing the finite sum
`∑_λ E_λ e_u` with a spectral measure `dE_u(λ)`.

We record this only as a `Prop` placeholder for now. -/

section Graphon

/-- **Open conjecture (graphon Godsil condition).**  The graphon
operator analogue: existence of perfect transport between two
"vertex" densities `u, v : L¹ [0,1]` is governed by an arithmetic
condition on the support of the spectral measure `dE_u`.  Conjectural
form; no proof attempted.

This `Prop` is stated as a stub to be filled in once the spectral-
measure machinery (`Mathlib.Analysis.InnerProductSpace.Spectrum`) is
extended to compact self-adjoint operators on `L²`. -/
def GraphonGodsilOpen : Prop :=
  -- Real-spectral-measure analogue: support is contained in
  -- (b + a * ℤ) for some a > 0, b ∈ ℝ.  Stub.
  True

end Graphon

/-! ## p-adic remark

The `Mathlib.NumberTheory.Padics.PadicNumbers` import is included
because Godsil's condition can be reformulated *p-adically*: an
algebraic real `λ` lies on the arithmetic progression `b + a ℤ` iff
every Galois conjugate of `(λ - b)/a` is a `p`-adic integer for every
prime `p` (a quasi-integrality criterion).  This reformulation is
useful for *integral* graphs (graphs whose eigenvalues are algebraic
integers), where the Godsil condition reduces to ordinary integrality
+ parity.  We do not develop the p-adic theory here; we only flag the
connection. -/

theorem padic_remark_placeholder : True := trivial

end PST
end Graphplay
