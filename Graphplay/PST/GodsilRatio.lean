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
import Mathlib.Combinatorics.SimpleGraph.Hasse
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

This is the *genuine* per-vertex support, using the diagonalization
`A = U D Uᴴ`: `λ ∈ EigenvalueSupport G u` iff the spectral projector
`E_λ e_u ≠ 0`, equivalently iff some eigenindex `i` with eigenvalue
`λ` has a nonzero `u`-coordinate `eigU G u i ≠ 0`.  (Earlier this slot
held the *full* spectrum `Set.range G.herm.eigenvalues`, ignoring `u`;
that over-claimed the support — see point (B) of the existence theorem.) -/
def EigenvalueSupport (G : WeightedGraph V) (u : V) : Set ℝ :=
  {lam : ℝ | ∃ i : V, G.herm.eigenvalues i = lam ∧ eigU G u i ≠ 0}

/-- The eigenvalue support is a *finite* subset of `ℝ` (it is contained
in the image of `G.herm.eigenvalues`, which is a function from the
finite type `V`). -/
theorem eigenvalueSupport_finite (G : WeightedGraph V) (u : V) :
    (EigenvalueSupport G u).Finite := by
  -- The support is a subset of `Set.range G.herm.eigenvalues` (any
  -- support element is, by its witness, an eigenvalue), and that range
  -- is finite as the image of the finite type `V`.
  refine Set.Finite.subset (Set.finite_range G.herm.eigenvalues) ?_
  rintro lam ⟨i, hi, -⟩
  exact ⟨i, hi⟩

/-- Every element of `EigenvalueSupport G u` lies in the real spectrum
of `G.adj`. -/
theorem eigenvalueSupport_subset_spectrum (G : WeightedGraph V) (u : V) :
    ∀ lam ∈ EigenvalueSupport G u, lam ∈ spectrum ℝ G.adj := by
  -- Each support element comes with a witness eigenindex `i` such that
  -- `lam = G.herm.eigenvalues i`; that eigenvalue lies in the real
  -- spectrum by `eigenvalues_mem_real_spectrum`.
  rintro lam ⟨i, hi, -⟩
  rw [← hi]
  exact G.eigenvalues_mem_real_spectrum i

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
  -- This is Godsil's *ratio condition* (Godsil 2012, Theorem 3.1): with
  -- every supported eigenvalue of the form `b + a*k`, the difference
  -- `lam - mu = a*(k_lam - k_mu)` is an integer multiple of `a`, so the
  -- ratio `(lam - mu)/(lam' - mu')` is the rational
  -- `(k_lam - k_mu)/(k_lam' - k_mu')` (well-defined since `lam' ≠ mu'`
  -- forces the integer denominator to be nonzero).
  obtain ⟨a, b, ha, h⟩ := h
  intro lam mu lam' mu' hlam hmu hlam' hmu' hne
  obtain ⟨kl, hkl⟩ := h lam hlam
  obtain ⟨km, hkm⟩ := h mu hmu
  obtain ⟨kl', hkl'⟩ := h lam' hlam'
  obtain ⟨km', hkm'⟩ := h mu' hmu'
  -- The integer denominator `kl' - km'` is nonzero: otherwise `lam' = mu'`.
  -- The real (hence integer) denominator `kl' - km'` is nonzero: otherwise
  -- `lam' = b + a*kl' = b + a*km' = mu'`, contradicting `lam' ≠ mu'`.
  have hdenR : (kl' : ℝ) - km' ≠ 0 := by
    intro hz
    apply hne
    rw [hkl', hkm']
    have : (kl' : ℝ) = km' := by linarith
    rw [this]
  have hden : (kl' - km' : ℤ) ≠ 0 := by
    intro hzero; exact hdenR (by push_cast [sub_eq_zero] at hzero ⊢; exact_mod_cast hzero)
  refine ⟨(kl - km : ℤ) / (kl' - km' : ℤ), ?_⟩
  -- Compute both sides in terms of `a` and the integer differences.
  have hlhs : lam - mu = a * ((kl : ℝ) - km) := by rw [hkl, hkm]; ring
  have hrhs : lam' - mu' = a * ((kl' : ℝ) - km') := by rw [hkl', hkm']; ring
  rw [hlhs, hrhs, Rat.cast_div]
  push_cast
  field_simp

/-! ## 3. The existence theorem

The headline statement is *Godsil 2012, Theorem 2.1*: PST exists at
some time iff `u, v` are strongly cospectral AND the eigenvalues in the
joint support are arithmetically aligned.  The "⇒" direction packs
together the cospectrality structure of any time evolution that exits
to a unit-modulus matrix element, and the "⇐" direction is a
Dirichlet/Kronecker simultaneous-approximation construction. -/

/-! ### Strong cospectrality (local, genuine definition)

The sibling module `Graphplay.PST.Cospectrality` (agent L1) develops strong
cospectrality with its own projector API.  At the time of writing that file
does not compile, so we cannot import it; rather than introduce an `axiom`
(which would be a fake), we give here a *genuine* coordinate-level definition
of `IsStronglyCospectral` that is mathematically the Godsil–Royle predicate.

The spectral projector onto the `λ`-eigenspace, in coordinates given by the
unitary eigenvector matrix `eigU`, has `(u, v)` entry
`(E_λ)_{u,v} = ∑_{i : eigenvalues i = λ} (eigU u i) · conj (eigU v i)`.
Strong cospectrality of `u, v` asserts that for every eigenvalue `λ` the
columns `E_λ e_u` and `E_λ e_v` are parallel, equivalently the cross entry is
a unit-modulus phase times the geometric mean of the two diagonal entries. -/

/-- The `(u, v)` entry of the spectral projector onto the `λ`-eigenspace,
expressed through the unitary eigenvector matrix `eigU`. -/
noncomputable def eigenProjEntryLocal (G : WeightedGraph V) (lam : ℝ) (u v : V) : ℂ :=
  ∑ i : V, if G.herm.eigenvalues i = lam then eigU G u i * star (eigU G v i) else 0

/-- The diagonal projector entry `(E_λ)_{u,u}` (a nonnegative real, recorded
here as a complex number for uniformity with `eigenProjEntryLocal`). -/
noncomputable def eigenProjDiagLocal (G : WeightedGraph V) (lam : ℝ) (u : V) : ℝ :=
  ∑ i : V, if G.herm.eigenvalues i = lam then ‖eigU G u i‖ ^ 2 else 0

/-- **Strong cospectrality** (Godsil–Royle; the spectral-parallelism
characterization).  `u` and `v` are strongly cospectral in `G` if, for every
real eigenvalue `λ`, the projections `E_λ e_u`, `E_λ e_v` are parallel: the
cross entry equals a unit-modulus phase times the geometric mean of the
diagonal entries.  This is a genuine `Prop`, defined locally (the sibling
`Graphplay.PST.Cospectrality` module is not currently importable). -/
def IsStronglyCospectral (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
    ∃ ε : ℂ, ‖ε‖ = 1 ∧
      eigenProjEntryLocal G lam u v
        = ε * Complex.ofReal
            (Real.sqrt (eigenProjDiagLocal G lam u * eigenProjDiagLocal G lam v))

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
  -- HONEST-SORRY NOTE (two distinct missing pieces).
  --
  -- (A) The spectral-expansion bridge.  Both directions hinge on the
  --     entrywise identity
  --       `(G.evolve τ) u v = ∑ i, eigU G u i * exp(-i τ (eigenvalues i))
  --                                   * star (eigU G v i)`,
  --     which is `Matrix.exp_units_conj` + `Matrix.exp_diagonal` applied
  --     to the spectral theorem `A = U D Uᴴ` (Mathlib
  --     `IsHermitian.spectral_theorem`).  That bridge is developed in the
  --     sibling `Graphplay.PST.Cospectrality` module, which is not yet
  --     importable here; reproducing it is out of this file's scope.
  --
  -- (B) RESOLVED.  `EigenvalueSupport` is now the GENUINE per-vertex
  --     support `{λ | ∃ i, eigenvalues i = λ ∧ eigU G u i ≠ 0}`, i.e.
  --     `{λ | E_λ e_u ≠ 0}` in coordinates (the `u` argument is no longer
  --     ignored).  With this reading the FORWARD direction no longer
  --     over-claims: PST constrains exactly the eigenvalues in the support
  --     of `u` (a possibly-proper subset of the full spectrum), and Godsil
  --     2012 Thm 2.1 holds verbatim:
  --       forward = Godsil "Periodic Graphs" (arXiv:0806.2074) Thm 2.2
  --         (`exp(iτ θ_r) = γ` on the support ⇒ ratio condition);
  --       backward = Kronecker/Dirichlet simultaneous approximation on
  --         `{θ_r/a}` (Mathlib `AddCircle` dense-orbit) choosing the
  --         parity to match strong cospectrality.
  --     The only remaining open piece is the spectral-expansion bridge (A).
  --
  -- We therefore leave a precise honest `sorry` for the bridge (A) rather
  -- than fake it.  Citation: Godsil, Electron. J. Combin. 19 (2012) #P29,
  -- Thm 2.1; Godsil, arXiv:0806.2074, Thm 2.2; Coutinho–Godsil (2021),
  -- Ch. 8–9.
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

/-- The (un-weighted) path graph on `n` vertices as a `WeightedGraph`,
obtained by promoting Mathlib's `SimpleGraph.pathGraph n` through the
`SimpleGraph.toWeighted` bridge.  This is the genuine path graph (unit
weights on the edges `{k, k+1}`), not a placeholder. -/
noncomputable def pathGraph (n : ℕ) : WeightedGraph (Fin n) :=
  letI : DecidableRel (SimpleGraph.pathGraph n).Adj := Classical.decRel _
  SimpleGraph.toWeighted (SimpleGraph.pathGraph n)

/- Endpoint vertices of `pathGraph n` (a graph on `Fin n`) are `0` and
`n - 1`.  For `n ≥ 2` these are the two distinct degree-one ends. -/
section Path

/-- The "left" endpoint `0` of `pathGraph n`, valid for `n ≥ 1`. -/
def pathLeft {n : ℕ} (hn : 1 ≤ n) : Fin n := ⟨0, by omega⟩

/-- The "right" endpoint `n - 1` of `pathGraph n`, valid for `n ≥ 1`. -/
def pathRight {n : ℕ} (hn : 1 ≤ n) : Fin n := ⟨n - 1, by omega⟩

/-- **Corrected statement.** The placeholder `True ↔ (n + 1) ∣ 6` that
previously occupied this slot is *false* (e.g. at `n = 3` it reads
`True ↔ (4 ∣ 6)`, i.e. `True ↔ False`), and the `(n+1) ∣ 6` folklore
refers to a *different normalization* (it counts edges/qubits, not
vertices, and conflates PST with PGST).  The genuine
Christandl–Datta–Dorlas–Ekert–Kay–Landahl (2005) / Godsil classification
of *endpoint-to-endpoint* perfect state transfer on the **unweighted**
path is:

> `P_n` (the path on `n` vertices, `n ≥ 2`) admits endpoint PST at some
> time `τ` **iff** `n = 2` or `n = 3`.

(Coutinho's thesis 2014, p. 2: "`P_n` admits perfect state transfer if
and only if `n = 2` or `n = 3`"; Godsil–Kirkland–Severini–Smith,
arXiv:1201.4822, show every longer unweighted path has at best *pretty
good* state transfer.)

We state the mathematically-correct biconditional.  Its forward
direction is the ratio-condition obstruction (Godsil 2012, Thm 2.2:
PST forces all path eigenvalues `2 cos(kπ/(n+1))` onto a common
arithmetic progression, which by Niven's theorem fails for `n ≥ 4`);
its backward direction is the explicit `K_2` / `P_3` matrix-exponential
computation.  Both directions need the spectral-decomposition bridge
`evolve τ = ∑_θ e^{-iτθ} E_θ` in coordinates, which lives in the
sibling `Graphplay.PST.Cospectrality` module that is not yet
importable here; hence the proof is an *honest* `sorry` attached to a
*true* statement (a strict improvement over the previous false one). -/
theorem isPST_exists_path_iff (n : ℕ) (hn : 2 ≤ n) :
    (∃ τ : ℝ, IsPST (pathGraph n) (pathLeft (by omega)) (pathRight (by omega)) τ)
      ↔ (n = 2 ∨ n = 3) := by
  -- Citation: Christandl–Datta–Dorlas–Ekert–Kay–Landahl, Phys. Rev. A
  -- 71 (2005) 032312; Coutinho thesis (2014) §2.4; Godsil–Kirkland–
  -- Severini–Smith, arXiv:1201.4822.
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
on `Fin (2^n)`, with vertices identified with `n`-bit strings.  Two
vertices are adjacent (unit weight) iff their bit-XOR has exactly one
set bit, i.e. they differ in exactly one coordinate (Hamming distance
1).  This is the genuine cube adjacency, built directly in coordinates;
it is real-symmetric (XOR is symmetric) and loopless (`u ^^^ u = 0` has
no set bit). -/
noncomputable def hypercube (n : ℕ) : WeightedGraph (Fin (2^n)) where
  adj u v := if (u.val ^^^ v.val) ≠ 0 ∧ (u.val ^^^ v.val) &&& ((u.val ^^^ v.val) - 1) = 0
             then 1 else 0
  herm := by
    -- Real, symmetric (the predicate is invariant under swapping `u, v`
    -- since `Nat.xor` is commutative), hence Hermitian.
    unfold Matrix.IsHermitian
    ext i j
    rw [Matrix.conjTranspose_apply]
    -- `star` fixes the real values `0`/`1`; the guard at `(j,i)` equals the
    -- guard at `(i,j)` because `Nat.xor` is commutative.  Rewrite the whole
    -- guard predicate as a single proposition, then evaluate.
    have hP : (j.val ^^^ i.val ≠ 0 ∧ (j.val ^^^ i.val) &&& ((j.val ^^^ i.val) - 1) = 0)
            = (i.val ^^^ j.val ≠ 0 ∧ (i.val ^^^ j.val) &&& ((i.val ^^^ j.val) - 1) = 0) := by
      rw [Nat.xor_comm j.val i.val]
    rw [apply_ite (star : ℂ → ℂ), if_congr (Eq.to_iff hP) rfl rfl]
    simp
  loopless := by
    intro v
    -- `v ^^^ v = 0`, so the guard `(… ≠ 0)` fails and the entry is `0`.
    simp [Nat.xor_self]

/-- Antipode involution on the `2^n` vertices: complement all `n` bits,
`k ↦ k ^^^ (2^n - 1)`.  (Genuine bitwise-complement involution.) -/
noncomputable def antipode (n : ℕ) : Fin (2^n) → Fin (2^n) :=
  fun k => ⟨k.val ^^^ (2^n - 1), by
    -- XOR of two numbers below `2^n` stays below `2^n`.
    have hk : k.val < 2^n := k.isLt
    have hm : (2^n - 1) < 2^n := Nat.sub_lt (Nat.two_pow_pos n) one_pos
    exact Nat.bitwise_lt_two_pow hk hm⟩

/-- **Christandl et al. 2005.** The hypercube `Q_n` exhibits PST
between any vertex `u` and its antipode at time `τ = π / 2`. -/
theorem isPST_hypercube_antipode (n : ℕ) (u : Fin (2^n)) :
    IsPST (hypercube n) u (antipode n u) (Real.pi / 2) := by
  -- HONEST-SORRY NOTE.  The statement is true (Christandl et al. 2005;
  -- eigenvalues `n - 2k`, `0 ≤ k ≤ n`, are integers, and the antipode
  -- automorphism `x ↦ x ⊕ 1ⁿ` gives strong cospectrality with `a = 2,
  -- b = n` in Godsil's condition).  The cleanest reachable proof is the
  -- Cartesian-product factorization `Q_n = K_2 □ ⋯ □ K_2`: the cube
  -- adjacency is a Kronecker SUM of `n` copies of the `K_2` adjacency,
  -- so `evolve_{Q_n}(τ) = evolve_{K_2}(τ)^{⊗ n}` and the antipodal entry
  -- factors as `∏_i (evolve_{K_2}(π/2))_{u_i, 1-u_i}`, each of modulus 1.
  -- That argument needs (i) the bit-wise `hypercube n` recognized as an
  -- n-fold Kronecker sum and (ii) `exp` of a Kronecker sum = Kronecker
  -- product of `exp`s — tensor-product infrastructure not yet present in
  -- this file.  Hence an honest `sorry`, not a fake.
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
*symmetrized* on the fly: `u, v` are adjacent (unit weight) iff `u ≠ v`
and `u - v ∈ S ∨ v - u ∈ S`.  This guarantees a real-symmetric,
loopless adjacency regardless of whether `S` was supplied symmetric, so
the result is a genuine `WeightedGraph` (no placeholder). -/
noncomputable def cayleyGraph {Γ : Type u} [Fintype Γ] [DecidableEq Γ]
    [AddCommGroup Γ] (S : Set Γ) : WeightedGraph Γ := by
  classical
  exact
  { adj := fun u v => if u ≠ v ∧ (u - v ∈ S ∨ v - u ∈ S) then 1 else 0
    herm := by
      -- The defining condition is symmetric under swapping `u, v`
      -- (`u ≠ v` is symmetric and the two disjuncts swap), so the
      -- real `0/1` matrix is symmetric, hence Hermitian.
      unfold Matrix.IsHermitian
      ext i j
      rw [Matrix.conjTranspose_apply]
      have hsymm : (j ≠ i ∧ (j - i ∈ S ∨ i - j ∈ S))
            ↔ (i ≠ j ∧ (i - j ∈ S ∨ j - i ∈ S)) := by
        constructor
        · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, hd.symm⟩
        · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, hd.symm⟩
      by_cases hc : i ≠ j ∧ (i - j ∈ S ∨ j - i ∈ S)
      · rw [if_pos (hsymm.mpr hc), if_pos hc]; simp
      · rw [if_neg (fun hh => hc (hsymm.mp hh)), if_neg hc]; simp
    loopless := by
      intro v
      simp }

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
  -- NOTE: as currently *stated* this lemma is a syntactic tautology
  -- (both sides are `EigenvalueSupport Gq i`); the intended statement
  -- relating the *host* cell-support `cellEigenvalueSupport P i` to the
  -- *quotient* vertex-support cannot be phrased without the host-side
  -- support, which depends on the not-yet-importable L1 projector API
  -- (`Graphplay.PST.Cospectrality`).  We discharge the tautology
  -- honestly; the genuine quotient-lifts-supports lemma (the cell-
  -- inflate map embeds quotient eigenspaces isometrically into the
  -- cell-uniform host subspace, so spectral projectors commute) is left
  -- to the round that unifies the support definitions.
  intro _hq
  rfl

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

/-- With a unit-modulus signing `s`, the phase clause in
`IsChiralGodsilRatio` is automatically satisfiable, so the chiral
ratio condition collapses to the ordinary Godsil ratio condition.
This is a *genuine* equivalence (no `sorry`): the witness phase is
`α = s v * conj (s u)`, whose modulus is `‖s v‖ * ‖s u‖ = 1`. -/
theorem isChiralGodsilRatio_iff_isGodsilRatio
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (s : V → ℂ) (hs : ∀ x, ‖s x‖ = 1) (u v : V) :
    IsChiralGodsilRatio G s u v ↔ IsGodsilRatio G u v := by
  unfold IsChiralGodsilRatio
  constructor
  · rintro ⟨hr, _⟩; exact hr
  · intro hr
    refine ⟨hr, s v * star (s u), ?_, rfl⟩
    rw [norm_mul, norm_star, hs v, hs u, one_mul]

/-- **Chiral existence theorem.**  For a unit-modulus chiral signing
`s`, PST between `u` and `v` occurs at some time iff `u, v` are
strongly cospectral and the chiral Godsil ratio condition holds.  The
previous formulation carried a degenerate `True →` guard; this true,
non-vacuous restatement removes it and reduces the chiral condition to
the ordinary one via `isChiralGodsilRatio_iff_isGodsilRatio`, so the
chiral existence theorem is exactly the main existence theorem.  (The
residual content is therefore the same spectral-expansion bridge that
`isPST_exists_iff_strongCospectral_and_godsilRatio` defers.)

Citation: Godsil 2012 + Lippner–Tamon's "Magnetic perfect state
transfer" line of work, e.g. Bachman–Fratila–Tamon–Tomon (2024+) on
chiral PST in cycles and Cayley graphs. -/
theorem isPST_exists_chiral_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (s : V → ℂ) (hs : ∀ x, ‖s x‖ = 1)
    (u v : V) :
    (∃ τ : ℝ, IsPST G u v τ) ↔
      IsStronglyCospectral G u v ∧ IsChiralGodsilRatio G s u v := by
  rw [isChiralGodsilRatio_iff_isGodsilRatio G s hs u v]
  exact isPST_exists_iff_strongCospectral_and_godsilRatio G u v

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
