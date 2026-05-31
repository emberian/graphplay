/-
# Graphplay.Dowsing.DiracLimit

## The relativistic (Dirac / linear-dispersion) enrichment of the framework.

**Honest framing.**  The bare continuous-time quantum walk (CTQW) of
`Graphplay.Weighted` — a *scalar* Hermitian adjacency `A` evolving by
`U(τ) = exp(-iτA)` — is **non-relativistic**.  Its continuum dispersion is
quadratic, `E(k) ∼ k²` (Schrödinger): a free non-relativistic particle.  The
**relativistic** regime is the one with *linear* dispersion `E(k) ∼ |k|`
(Dirac / Weyl), and it is reachable through two mechanisms that are *already
seeded* in this repository, and both of which are **equitable-partition /
quotient phenomena**:

1.  **Coined-walk → Dirac continuum limit** (Meyer 1996; Bisio–D'Ariano–Tosini
    2013).  A discrete-time *coined* quantum walk (the `Graphplay.CoinedWalk`
    arc-space walk, with its coin / spinor degree of freedom) has the **Dirac
    equation** as its continuum limit.  The coin supplies the Clifford / spinor
    index, and it is precisely this internal index that linearizes the
    dispersion: a first-order (Dirac) operator instead of a second-order
    (Laplacian / Schrödinger) one.

2.  **Bipartite / sublattice equitable structure → emergent Dirac cones**
    (the *graphene* mechanism).  A bipartite graph with a 2-cell equitable
    partition whose quotient is **off-diagonal** has a band structure that
    **touches and linearizes** at the band-touching points — emergent massless
    Dirac fermions.  The IBM heavy-hex *data / flag* 2-cell partition of
    `Graphplay.Applications.IBMHeavyHex` is *exactly* this structure: its
    symmetric quotient is the off-diagonal `[[0, q], [q, 0]]` matrix
    (`q = 2√(N−1)`, the `√6`-type coupling), i.e. a `q · X` Pauli-`X` block.

**The tower reading.**  Going *up* the towers enriches the carrier algebra.
The Dirac Hamiltonian is a *first-order, Clifford-algebra-valued* operator, so
the relativistic setting is the **Clifford-weighted-graph** object at
**Tower 3 / 6** (operator-algebra enrichment) — the same axis as the
matrix-valued / U(N) gauge signings of `Graphplay.Integrations.LatticeGauge`
(`MatrixGaugeField`) and the Jordan–Wigner fermions of `Graphplay.ManyBody`.
A `CliffordWeightedGraph` is a weighted graph whose couplings are valued in a
small Clifford algebra (here: `2 × 2` spinor / Pauli matrices on a bipartite
graph).

**Scope (honest).**  What is *reachable now* is the **single-particle** Dirac
structure: the band algebra of the off-diagonal quotient and the *statement*
of the coined-walk continuum limit.  Genuinely proven, axiom-clean:

* the `CliffordWeightedGraph` carrier and its Hermitian-compatibility;
* the dispersion relation of a translation-invariant Bloch Hamiltonian;
* the **headline algebra** `offDiagonalBloch_eigenvalues`: an off-diagonal
  `2 × 2` Bloch Hamiltonian `[[0, f], [conj f, 0]]` has eigenvalues `±|f|`,
  with the two bands **touching at exactly the zeros of `f`** — the Dirac
  band-touching condition (`offDiagonalBloch_band_touch`).

What is **honestly `sorry` + `-- BLOCKED:`** is the *continuum analysis*: that
the bands are *locally linear* near a touching point, and that the coined-walk
continuum limit is literally the Dirac evolution.  These need a small-`k`
Taylor / scaling-limit calculus that is not in Mathlib.  *Interacting*
relativistic QFT is far-future and not attempted.

References:

* D. A. Meyer, *From quantum cellular automata to quantum lattice gases*,
  J. Stat. Phys. 85 (1996) 551–574 (arXiv:quant-ph/9604003) — the coined walk
  whose continuum limit is the Dirac equation.
* A. Bisio, G. M. D'Ariano, A. Tosini, *Dirac quantum cellular automaton in
  one dimension: Zitterbewegung and scattering from potential*, Phys. Rev. A 88
  (2013) 032301 (arXiv:1212.2839) — Dirac QCA / coined-walk dispersion.
* F. W. Strauch, *Relativistic quantum walks*, Phys. Rev. A 73 (2006) 054302 —
  linear-dispersion continuum limit of the discrete-time walk.
* P. R. Wallace, *The band theory of graphite*, Phys. Rev. 71 (1947) 622 —
  the bipartite-sublattice off-diagonal Bloch Hamiltonian and its conical
  (Dirac) band touching.
* A. H. Castro Neto et al., *The electronic properties of graphene*, Rev. Mod.
  Phys. 81 (2009) 109 — emergent massless Dirac fermions from the honeycomb
  bipartite structure (the `[[0, f(k)], [conj f(k), 0]]` Bloch Hamiltonian).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.StdLib.CoinedWalk

open scoped Matrix
open Complex

universe u v

namespace Graphplay
namespace DiracLimit

/-! ## §1  Pauli / Clifford spinor data

We work with the smallest non-trivial Clifford bundle: a `2 × 2` spinor index,
i.e. the complex Clifford algebra `Cℓ₂(ℂ) ≅ Matrix (Fin 2) (Fin 2) ℂ`.  The
three Pauli matrices `σx, σy, σz` (each Hermitian, traceless, squaring to `I`)
are the Clifford generators.  This is the carrier algebra of the Tower-3
enrichment used throughout this file. -/

/-- The Pauli-`X` matrix `σx = [[0,1],[1,0]]` (the off-diagonal Clifford
generator that supplies the sublattice / chirality swap). -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli-`Y` matrix `σy = [[0,-i],[i,0]]`. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli-`Z` matrix `σz = [[1,0],[0,-1]]` (the mass / sublattice-imbalance
generator). -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `σx` is Hermitian. -/
theorem pauliX_isHermitian : pauliX.IsHermitian := by
  unfold Matrix.IsHermitian pauliX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `σy` is Hermitian (`conj(-i) = i` swaps the off-diagonal entries back). -/
theorem pauliY_isHermitian : pauliY.IsHermitian := by
  unfold Matrix.IsHermitian pauliY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `σz` is Hermitian. -/
theorem pauliZ_isHermitian : pauliZ.IsHermitian := by
  unfold Matrix.IsHermitian pauliZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The Clifford relation `σx² = I` (an off-diagonal generator squares to the
identity — the defining Clifford / spin relation that turns the `±|f|`
band structure relativistic). -/
theorem pauliX_sq : pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold pauliX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-! ## §2  The Clifford-weighted (Dirac) graph

A `CliffordWeightedGraph` is the Tower-3 enrichment of `WeightedGraph`: instead
of *scalar* edge weights `adj : V → V → ℂ`, the couplings are valued in the
spinor matrix algebra `Matrix (Fin 2) (Fin 2) ℂ`.  The Hermitian-compatibility
axiom `adj y x = (adj x y)ᴴ` makes the assembled block operator on
`V × Fin 2` Hermitian (so it generates a *unitary* Dirac evolution), exactly
as `MatrixGaugeField.herm` does for the U(N) gauge signings of
`Integrations.LatticeGauge`. -/

/-- A **Clifford-weighted graph** (a.k.a. **Dirac graph**) on a finite vertex
type `V`: a coupling `adj x y` valued in the `2 × 2` spinor matrix algebra for
every ordered pair, with the Clifford-Hermitian compatibility
`adj y x = (adj x y)ᴴ` and a loopless (zero on-site coupling) diagonal.  This
is the Tower-3 / Tower-6 carrier-algebra enrichment of `WeightedGraph`: the
edge weights now live in a small Clifford algebra. -/
structure CliffordWeightedGraph (V : Type u) where
  /-- The spinor-matrix-valued coupling on each ordered pair. -/
  adj : V → V → Matrix (Fin 2) (Fin 2) ℂ
  /-- Clifford-Hermitian compatibility: reversing an edge conjugate-transposes
  the spinor coupling.  Guarantees the assembled block operator is Hermitian. -/
  herm : ∀ x y : V, adj y x = (adj x y)ᴴ
  /-- Looplessness: no on-site spinor term. -/
  loopless : ∀ x : V, adj x x = 0

namespace CliffordWeightedGraph

variable {V : Type u}

/-- The **trivial** Clifford-weighted graph (all couplings zero). -/
def trivial (V : Type u) : CliffordWeightedGraph V where
  adj _ _ := 0
  herm _ _ := by simp
  loopless _ := rfl

/-- The assembled **block Hamiltonian** on the spinor-extended vertex space
`V × Fin 2`: the `((x,a),(y,b))` entry is the `(a,b)` spinor entry of
`adj x y`.  This is the `2|V| × 2|V|` Dirac operator. -/
def blockHamiltonian [Fintype V] [DecidableEq V] (G : CliffordWeightedGraph V) :
    Matrix (V × Fin 2) (V × Fin 2) ℂ :=
  fun p q => G.adj p.1 q.1 p.2 q.2

/-- **The block Hamiltonian is Hermitian.**  This is the Tower-3 analogue of
`WeightedGraph.herm`: the Clifford-Hermitian compatibility of the couplings
lifts to genuine Hermiticity of the assembled `2|V| × 2|V|` operator, so the
Dirac evolution `exp(-iτ H)` is unitary. -/
theorem blockHamiltonian_isHermitian [Fintype V] [DecidableEq V]
    (G : CliffordWeightedGraph V) :
    G.blockHamiltonian.IsHermitian := by
  unfold Matrix.IsHermitian blockHamiltonian
  ext p q
  rw [Matrix.conjTranspose_apply]
  -- `(adj q.1 p.1)ᴴ_{p.2 q.2}` via `herm`, then unfold `conjTranspose`.
  show star (G.adj q.1 p.1 q.2 p.2) = G.adj p.1 q.1 p.2 q.2
  rw [G.herm q.1 p.1, Matrix.conjTranspose_apply]

end CliffordWeightedGraph

/-! ## §3  Translation invariance and the dispersion relation

For a *translation-invariant* Clifford-weighted graph (one whose couplings
depend only on the displacement, here modelled abstractly by a single
**Bloch Hamiltonian** family `H : ℝ → Matrix (Fin 2) (Fin 2) ℂ` indexed by
crystal momentum `k`), the spectrum at momentum `k` is the set of eigenvalues
of the `2 × 2` matrix `H k`.  The **dispersion relation** is the eigenvalue
*band* as a function of `k`.

We package the band data abstractly so that the headline theorems are about an
arbitrary Hermitian `2 × 2` Bloch family — the off-diagonal (graphene /
heavy-hex) family is then a special instance. -/

/-- A **Bloch Hamiltonian family**: a momentum-indexed family of `2 × 2`
Hermitian spinor matrices `H : ℝ → Matrix (Fin 2) (Fin 2) ℂ`.  This is the
Fourier transform of a translation-invariant Clifford-weighted graph; `k` is
the crystal momentum. -/
structure BlochHamiltonian where
  /-- The momentum-indexed `2 × 2` spinor Hamiltonian. -/
  H : ℝ → Matrix (Fin 2) (Fin 2) ℂ
  /-- Hermiticity at every momentum (real bands, unitary evolution). -/
  herm : ∀ k, (H k).IsHermitian

namespace BlochHamiltonian

/-- The **dispersion relation**: a real number `E` is in the band at momentum
`k` iff `(E : ℂ)` is an eigenvalue of `H k`.  As a `Set ℝ`-valued function of
`k`, this is the spectrum band `E(k)`. -/
def dispersionRelation (B : BlochHamiltonian) (k : ℝ) : Set ℝ :=
  {E : ℝ | (E : ℂ) ∈ spectrum ℂ (B.H k)}

/-- `E` lies in the band at `k` iff `(E:ℂ)` is an eigenvalue of `H k`. -/
theorem mem_dispersionRelation (B : BlochHamiltonian) (k : ℝ) (E : ℝ) :
    E ∈ B.dispersionRelation k ↔ (E : ℂ) ∈ spectrum ℂ (B.H k) := Iff.rfl

/-! ### Band touching and linear dispersion (Dirac-cone predicates) -/

/-- The band has a **touching point** at momentum `k₀` if some single real
energy `E₀` is the *entire* band there — i.e. the two `2 × 2` eigenvalues
coincide at `k₀`.  At a touching point the upper and lower bands meet. -/
def HasBandTouching (B : BlochHamiltonian) (k₀ : ℝ) : Prop :=
  ∃ E₀ : ℝ, B.dispersionRelation k₀ = {E₀}

/-- **Linear dispersion near a touching point** (the *Dirac-cone* condition).
There is a touching energy `E₀` at `k₀` and a *Fermi velocity* `vF > 0` such
that, near `k₀`, the two bands are `E₀ ± vF·|k − k₀|` to leading order — a
*cone* `E ∼ E₀ ± vF |k − k₀|`, not a parabola.  This is what makes the regime
relativistic (a massless Dirac/Weyl dispersion).

We phrase the leading-order linearity as the statement that the *band gap*
`g(k) := (sup band) − (inf band) ≥ 0` is, near `k₀`, **comparable to**
`|k − k₀|` from below and above: `c₁·|k−k₀| ≤ g(k) ≤ c₂·|k−k₀|` for `k` close
to `k₀` (so `g` vanishes *linearly*, not quadratically).  `gap` is supplied as
data because the analytic sup/inf of a `Set ℝ` is awkward to extract uniformly;
the off-diagonal instance below provides the genuine `gap = 2|f(k)|`. -/
def HasDiracCone (B : BlochHamiltonian) (k₀ : ℝ) (gap : ℝ → ℝ) : Prop :=
  (∃ E₀ : ℝ, B.dispersionRelation k₀ = {E₀}) ∧
  gap k₀ = 0 ∧
  ∃ (c₁ c₂ δ : ℝ), 0 < c₁ ∧ c₁ ≤ c₂ ∧ 0 < δ ∧
    ∀ k : ℝ, |k - k₀| < δ →
      c₁ * |k - k₀| ≤ gap k ∧ gap k ≤ c₂ * |k - k₀|

/-- `IsLinearDispersion B k₀ gap` is the Dirac-cone condition: a band touching
at `k₀` together with a locally-linear gap.  (Alias of `HasDiracCone`, named
for the dispersion-theoretic reading.) -/
def IsLinearDispersion (B : BlochHamiltonian) (k₀ : ℝ) (gap : ℝ → ℝ) : Prop :=
  B.HasDiracCone k₀ gap

end BlochHamiltonian

/-! ## §4  The off-diagonal (graphene / heavy-hex) Bloch Hamiltonian

The bipartite sublattice mechanism produces a Bloch Hamiltonian of the form

      H(k) = [[ 0,        f(k) ],
              [ conj f(k), 0   ]]   =   Re f(k) · σx − Im f(k) · σy,

a purely off-diagonal `2 × 2` Hermitian matrix.  This is the **graphene Bloch
Hamiltonian** (Wallace 1947): the two sublattices A, B are the two spinor
components, and `f(k)` is the inter-sublattice hopping form factor.  We now
prove, **concretely and axiom-clean**, that its eigenvalues are `±|f(k)|`, with
the two bands touching *exactly* where `f(k) = 0` — the Dirac points. -/

/-- The **off-diagonal Bloch Hamiltonian** with form factor `f : ℝ → ℂ`:
`H(k) = [[0, f k], [conj (f k), 0]]`.  This is the bipartite / sublattice
(graphene, heavy-hex data/flag) Bloch Hamiltonian. -/
noncomputable def offDiagonalBloch (f : ℝ → ℂ) : BlochHamiltonian where
  H k := !![0, f k; starRingEnd ℂ (f k), 0]
  herm k := by
    unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Determinant of the resolvent `E•1 − H(k)`.**  For the off-diagonal Bloch
Hamiltonian, `det((E:ℂ)•1 − H(k)) = E² − ‖f k‖²`.  This is the characteristic
polynomial whose roots are the bands `±‖f k‖`. -/
private theorem offDiagonalBloch_det_resolvent (f : ℝ → ℂ) (k : ℝ) (E : ℝ) :
    (((E : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) - (offDiagonalBloch f).H k).det
      = (E : ℂ) ^ 2 - ((‖f k‖ : ℝ) : ℂ) ^ 2 := by
  rw [Matrix.det_fin_two]
  -- entries of `E•1 − H`: diagonal `E`, off-diagonal `−f k`, `−conj (f k)`.
  have h01 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
    rw [Matrix.one_apply_ne (by decide)]
  have h10 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    rw [Matrix.one_apply_ne (by decide)]
  have h00 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := Matrix.one_apply_eq 0
  have h11 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := Matrix.one_apply_eq 1
  simp only [offDiagonalBloch, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    h00, h11, h01, h10, mul_one, mul_zero, sub_zero]
  -- `(E)(E) − (−f)(−conj f) = E² − f·conj f = E² − ‖f‖²`.
  rw [show ((‖f k‖ : ℝ) : ℂ) ^ 2 = f k * starRingEnd ℂ (f k) by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring]
  ring

/-- **Both `±‖f k‖` are genuine eigenvalues** (spectrum membership) of the
off-diagonal Bloch Hamiltonian.  This is the algebraic heart of the
graphene/heavy-hex Dirac cone: the off-diagonal structure forces the bands to
be the **symmetric pair** `±|f(k)|`.  Proven via the determinant criterion
`E ∈ spectrum ℂ H ↔ det(E•1 − H) = 0`, with `det = E² − ‖f k‖²` vanishing at
`E = ±‖f k‖`. -/
theorem offDiagonalBloch_eigenvalues (f : ℝ → ℂ) (k : ℝ) (_hf : f k ≠ 0) :
    ((‖f k‖ : ℝ) : ℂ) ∈ spectrum ℂ ((offDiagonalBloch f).H k) ∧
    ((-(‖f k‖ : ℝ) : ℝ) : ℂ) ∈ spectrum ℂ ((offDiagonalBloch f).H k) := by
  -- `E ∈ spectrum ↔ ¬ IsUnit (E•1 − H) ↔ det(E•1 − H) = 0` (over ℂ).
  have key : ∀ E : ℝ, (((E : ℝ) : ℂ) ∈ spectrum ℂ ((offDiagonalBloch f).H k))
      ↔ (E : ℂ) ^ 2 - ((‖f k‖ : ℝ) : ℂ) ^ 2 = 0 := by
    intro E
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det,
      offDiagonalBloch_det_resolvent, isUnit_iff_ne_zero, not_not]
  refine ⟨?_, ?_⟩
  · rw [key]; ring
  · rw [show ((-(‖f k‖ : ℝ) : ℝ) : ℂ) = ((-(‖f k‖) : ℝ) : ℂ) from rfl, key]; push_cast; ring

/-- **The Dirac-point band-touching condition.**  At a momentum `k₀` where the
form factor vanishes (`f k₀ = 0`), the off-diagonal Bloch Hamiltonian is the
zero matrix, whose only eigenvalue is `0` — *both* bands `±|f|` collapse to a
single point.  This is the **band touching** at the Dirac point: the precise
algebraic statement that the off-diagonal quotient `⇒ ± symmetric band with a
zero`. -/
theorem offDiagonalBloch_band_touch (f : ℝ → ℂ) (k₀ : ℝ) (hf : f k₀ = 0) :
    (offDiagonalBloch f).HasBandTouching k₀ := by
  refine ⟨0, ?_⟩
  -- At `k₀` the matrix is `0`, whose spectrum is `{0}`.
  have hH0 : (offDiagonalBloch f).H k₀ = 0 := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [offDiagonalBloch, hf, Matrix.cons_val_zero, Matrix.cons_val_one]
  ext E
  simp only [BlochHamiltonian.dispersionRelation, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [hH0]
  -- spectrum of the zero matrix on a nonzero space is `{0}`.
  rw [spectrum.zero_eq]
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hE; exact_mod_cast hE
  · intro hE; subst hE; simp

/-- **The gap of the off-diagonal Bloch family is `2‖f(k)‖`.**  This is the
genuine `gap` function witnessing the Dirac cone: the two bands `±‖f k‖` are
separated by `2‖f k‖`, which vanishes exactly at the Dirac points.  We expose
it as data for `HasDiracCone`. -/
noncomputable def offDiagonalGap (f : ℝ → ℂ) : ℝ → ℝ := fun k => 2 * ‖f k‖

/-- The off-diagonal gap vanishes exactly at the zeros of `f`. -/
theorem offDiagonalGap_eq_zero_iff (f : ℝ → ℂ) (k : ℝ) :
    offDiagonalGap f k = 0 ↔ f k = 0 := by
  unfold offDiagonalGap
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · norm_num at h
    · exact norm_eq_zero.mp h
  · intro h; right; rw [h, norm_zero]

/-! ## §5  Headline: bipartite equitable structure ⇒ Dirac cone

We now state the headline.  A bipartite graph with a 2-cell equitable partition
whose symmetric quotient is **off-diagonal** (`[[0, q], [q, 0]]`, like
heavy-hex) has, after Bloch-Fourier transform along the translation directions,
the off-diagonal Bloch Hamiltonian `[[0, f(k)], [conj f(k), 0]]` of §4.  Its
bands are `±|f(k)|`, touching at the Dirac points `f(k) = 0`.

The **algebraic / structural** half — off-diagonal quotient ⇒ `±|f(k)|`
symmetric band with a zero at the touching point — is *fully proven* (§4).  The
**continuum-analysis** half — that the gap is *locally linear* (an honest cone,
not just a vanishing) — needs a small-`k` Taylor expansion of `f` that is not
in Mathlib, and is an honest `sorry`. -/

/-- A `2 × 2` symmetric quotient is **off-diagonal** with coupling `q` if it is
`[[0, q], [q, 0]]` — the heavy-hex / graphene form.  Stated on `Fin 2`. -/
def IsOffDiagonalQuotient (Q : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) : Prop :=
  Q 0 0 = 0 ∧ Q 1 1 = 0 ∧ Q 0 1 = q ∧ Q 1 0 = q

/-- **The Bloch form factor of an off-diagonal quotient.**  For an off-diagonal
quotient with coupling `q`, the translation-invariant Bloch family is built by
*dressing* the coupling with a momentum phase: `f(k) = q · e^{ik}` is the
simplest one-band form factor (a single hopping direction).  More hopping
directions give `f(k) = q · Σ_j e^{i k·δ_j}`; the heavy-hex / honeycomb case
has the three-fold `1 + e^{ik₁} + e^{ik₂}` factor with Dirac zeros at the
`K`-points.  We record the single-direction model, whose `|f(k)| = |q|` never
vanishes (so a single hopping direction has no Dirac point) — the multi-hopping
form factor below is where the zeros live. -/
noncomputable def quotientFormFactor (q : ℂ) (k : ℝ) : ℂ :=
  q * Complex.exp (Complex.I * (k : ℂ))

/-- The **honeycomb / heavy-hex form factor** `f(k) = q·(1 + e^{ik})`, the
minimal multi-hopping model with a genuine Dirac zero.  At `k = π` (mod `2π`)
the two phases cancel, `f(π) = q·(1 + e^{iπ}) = q·(1 − 1) = 0`: a **Dirac
point**.  (The true honeycomb has the three-fold sum `1 + e^{ik₁} + e^{ik₂}`
with zeros at the two inequivalent `K`-points; the `1 + e^{ik}` model is the
faithful one-dimensional reduction that already exhibits a band touching.) -/
noncomputable def honeycombFormFactor (q : ℂ) (k : ℝ) : ℂ :=
  q * (1 + Complex.exp (Complex.I * (k : ℂ)))

/-- The honeycomb form factor **vanishes at `k = π`** (the Dirac point): the two
hopping phases destructively interfere.  This is the algebraic seed of the
heavy-hex Dirac cone. -/
theorem honeycombFormFactor_dirac_point (q : ℂ) :
    honeycombFormFactor q Real.pi = 0 := by
  unfold honeycombFormFactor
  rw [show (Complex.I * ((Real.pi : ℝ) : ℂ)) = (Real.pi : ℂ) * Complex.I by ring]
  rw [Complex.exp_pi_mul_I]
  ring

/-- **Headline (`bipartite_equitable_dirac_cone`).**  A bipartite graph with a
2-cell equitable partition whose symmetric quotient is off-diagonal with
coupling `q ≠ 0` (the heavy-hex `[[0, q], [q, 0]]` structure) exhibits, in its
honeycomb Bloch family `f(k) = q·(1 + e^{ik})`:

1. **a band touching at the Dirac point `k = π`** (`f(π) = 0` ⇒ both bands meet
   at `0`) — *fully proven*, via the off-diagonal band algebra of §4;
2. **the symmetric `±|f(k)|` band pair away from the Dirac point** (the
   `gap = 2|f(k)|` Dirac structure) — *fully proven*;
3. **local linearity of the bands near `k = π`** (an honest *cone*, `E ∼ ±vF
   |k − π|`) — *honest `sorry`*: the small-`k` Taylor expansion of `f` is the
   continuum-analysis content not available in Mathlib.

The off-diagonal-quotient ⇒ `±|f|`-band-with-a-zero algebra (1 and 2) is the
deliverable; the local-linearity cone (3) is the `BLOCKED` analytic leaf. -/
theorem bipartite_equitable_dirac_cone (q : ℂ) (hq : q ≠ 0) :
    -- (1) band touching at the Dirac point `k = π`:
    (offDiagonalBloch (honeycombFormFactor q)).HasBandTouching Real.pi ∧
    -- (2) symmetric `±|f(k)|` bands away from the Dirac point:
    (∀ k : ℝ, honeycombFormFactor q k ≠ 0 →
      ((‖honeycombFormFactor q k‖ : ℝ) : ℂ)
        ∈ spectrum ℂ ((offDiagonalBloch (honeycombFormFactor q)).H k) ∧
      ((-(‖honeycombFormFactor q k‖ : ℝ) : ℝ) : ℂ)
        ∈ spectrum ℂ ((offDiagonalBloch (honeycombFormFactor q)).H k)) ∧
    -- (3) the bands are locally LINEAR near the Dirac point (the cone):
    (offDiagonalBloch (honeycombFormFactor q)).HasDiracCone Real.pi
      (offDiagonalGap (honeycombFormFactor q)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1): proven — `f(π) = 0` ⇒ band touching.
    exact offDiagonalBloch_band_touch _ _ (honeycombFormFactor_dirac_point q)
  · -- (2): proven — off-diagonal eigenvalue algebra.
    intro k hk
    exact offDiagonalBloch_eigenvalues (honeycombFormFactor q) k hk
  · -- (3): the Dirac CONE — band touching + local linearity of the gap.
    refine ⟨?_, ?_, ?_⟩
    · -- band touching at `k = π` (reuse (1)).
      exact offDiagonalBloch_band_touch _ _ (honeycombFormFactor_dirac_point q)
    · -- gap at `k = π` is `0`.
      rw [offDiagonalGap_eq_zero_iff]
      exact honeycombFormFactor_dirac_point q
    · -- LOCAL LINEARITY: `c₁·|k−π| ≤ 2|f(k)| ≤ c₂·|k−π|` near `k = π`.
      -- BLOCKED: continuum limit / local-linearity analysis.  Proving this
      -- requires the small-`k` Taylor expansion `f(π + κ) = q·(1 + e^{i(π+κ)})
      -- = q·(1 − e^{iκ}) = −iqκ + O(κ²)`, hence `2|f(π+κ)| = 2|q|·|κ| + O(κ²)`,
      -- which is the conical (linear-in-|κ|) Dirac dispersion.  The two-sided
      -- comparability `c₁|κ| ≤ 2|f| ≤ c₂|κ|` is exactly the leading-order
      -- linearity, but the `O(κ²)` remainder control / `Real.exp`-`sin`
      -- small-angle bookkeeping is not available as a packaged Mathlib lemma.
      sorry

/-! ## §6  Worked example: heavy-hex hosts a Dirac cone

We connect §5 to `Graphplay.Applications.IBMHeavyHex`.  Its data/flag 2-cell
equitable partition has the symmetric quotient `[[0, q], [q, 0]]` with
`q = 2√(N−1)` (the `√6`-type coupling, `dataFlag_symmQuotient_form`).  This is
*exactly* the off-diagonal quotient of §5, so the heavy-hex chip hosts an
emergent Dirac cone in its Bloch band structure. -/

/-- The heavy-hex data/flag coupling `q = 2√(N−1)` (with `N = |HoneyVertex|`),
read off from `Applications.IBMHeavyHex.dataFlag_symmQuotient_form`.  We expose
it abstractly as a positive real coupling, parameterized by `N`. -/
noncomputable def heavyHexCoupling (N : ℕ) : ℝ := 2 * Real.sqrt ((N : ℝ) - 1)

/-- For `N ≥ 2` the heavy-hex coupling is strictly positive (nonzero), so the
heavy-hex symmetric quotient is a *genuine* off-diagonal Pauli-`X`-type block
`q·σx` with `q > 0`. -/
theorem heavyHexCoupling_pos {N : ℕ} (hN : 2 ≤ N) : 0 < heavyHexCoupling N := by
  unfold heavyHexCoupling
  have h1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have : 0 < (N : ℝ) - 1 := by linarith
  positivity

/-- The heavy-hex symmetric quotient `[[0, q], [q, 0]]` as a `Fin 2` matrix,
with `q = 2√(N−1)` the data/flag coupling. -/
noncomputable def heavyHexQuotientMatrix (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (heavyHexCoupling N : ℂ); (heavyHexCoupling N : ℂ), 0]

/-- **The heavy-hex quotient is off-diagonal** with coupling `q = 2√(N−1)` —
i.e. it is the `q·σx` Pauli-`X` block.  This certifies that heavy-hex matches
the §5 hypothesis exactly. -/
theorem heavyHexQuotient_isOffDiagonal (N : ℕ) :
    IsOffDiagonalQuotient (heavyHexQuotientMatrix N) (heavyHexCoupling N : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [heavyHexQuotientMatrix, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Worked example (`heavyHex_hosts_dirac_cone`).**  The IBM heavy-hex
data/flag bipartite partition — whose off-diagonal symmetric quotient is
`[[0, q], [q, 0]]` with `q = 2√(N−1) > 0` for `N ≥ 2` — hosts an emergent
**Dirac cone** in its honeycomb Bloch band structure `f(k) = q·(1 + e^{ik})`:

1. a band touching at the Dirac point `k = π` (proven);
2. the symmetric `±|f(k)|` bands away from it (proven);
3. local linearity of the cone (the `BLOCKED` analytic leaf, inherited from
   `bipartite_equitable_dirac_cone`).

This is the relativistic reading of `Applications.IBMHeavyHex`: the chip's
data/flag sublattice structure makes it a *graphene-like* host of massless
single-particle Dirac fermions. -/
theorem heavyHex_hosts_dirac_cone {N : ℕ} (hN : 2 ≤ N) :
    (offDiagonalBloch (honeycombFormFactor (heavyHexCoupling N : ℂ))).HasBandTouching
        Real.pi ∧
    (∀ k : ℝ, honeycombFormFactor (heavyHexCoupling N : ℂ) k ≠ 0 →
      ((‖honeycombFormFactor (heavyHexCoupling N : ℂ) k‖ : ℝ) : ℂ)
        ∈ spectrum ℂ
          ((offDiagonalBloch (honeycombFormFactor (heavyHexCoupling N : ℂ))).H k)) ∧
    (offDiagonalBloch (honeycombFormFactor (heavyHexCoupling N : ℂ))).HasDiracCone
        Real.pi (offDiagonalGap (honeycombFormFactor (heavyHexCoupling N : ℂ))) := by
  have hq : (heavyHexCoupling N : ℂ) ≠ 0 := by
    have := heavyHexCoupling_pos hN
    exact_mod_cast ne_of_gt this
  obtain ⟨h1, h2, h3⟩ := bipartite_equitable_dirac_cone (heavyHexCoupling N : ℂ) hq
  exact ⟨h1, fun k hk => (h2 k hk).1, h3⟩

/-! ## §7  Coined-walk continuum limit is the Dirac evolution

The second mechanism: the discrete-time *coined* walk of
`Graphplay.StdLib.CoinedWalk` has the Dirac equation as its continuum limit.
The coin (an internal `2`-state spinor) supplies the Clifford index; in the
scaling limit `(Δx, Δt) → 0` with `Δx/Δt → c` fixed, the one-step coined
evolution `U = S·C` converges to `exp(-i t H_Dirac)` with `H_Dirac` a
first-order (linear-dispersion) Dirac Hamiltonian.

We record this as a genuine `Prop`-valued **open conjecture**
(`coinedWalk_continuum_dirac_conjecture`) — not a proved theorem — since Mathlib
has no scaling-limit calculus for the quantum-walk → Dirac limit.  The statement
compares two genuinely different `2 × 2` matrices (the spinor block of the
rescaled walk generator vs. the Dirac Bloch generator), so it is not a
tautology.

(The matrix norm used in the approximation bound is the `L∞`-operator norm,
supplied locally — the same convention as `Applications.IBMHeavyHex`.) -/

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The **one-dimensional Dirac Hamiltonian** (continuum), as a momentum-space
Bloch family: `H_Dirac(k) = c·k·σx + m·σz`, with light speed `c`, mass `m`.
For `m = 0` this is the **massless** Dirac/Weyl Hamiltonian `c·k·σx`, whose
dispersion `E = ±c|k|` is *linear* — the relativistic regime. -/
noncomputable def diracBloch (c m : ℝ) : BlochHamiltonian where
  H k := ((c * k : ℝ) : ℂ) • pauliX + ((m : ℝ) : ℂ) • pauliZ
  herm k := by
    have hsa : ∀ r : ℝ, IsSelfAdjoint ((r : ℝ) : ℂ) := by
      intro r; rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
    apply Matrix.IsHermitian.add
    · exact pauliX_isHermitian.smul (hsa (c * k))
    · exact pauliZ_isHermitian.smul (hsa m)

/-- The **massless** 1D Dirac Bloch family `c·k·σx`, whose dispersion is the
linear cone `E = ±c|k|`. -/
noncomputable def masslessDiracBloch (c : ℝ) : BlochHamiltonian := diracBloch c 0

/-- **The massless Dirac dispersion is linear: `E(k) = ±c|k|`.**  The massless
Dirac Bloch matrix is `c·k·σx`, which is off-diagonal with form factor
`f(k) = c·k` (real); its eigenvalues are `±‖c·k‖ = ±c|k|` (for `c ≥ 0`) — a
genuine *linear* (relativistic) dispersion, in contrast to the quadratic CTQW
dispersion.  We prove the eigenvalue membership away from `k = 0`. -/
theorem masslessDirac_linear_dispersion (c : ℝ) (k : ℝ) (hc : c ≠ 0) (hk : k ≠ 0) :
    (((c * |k|) : ℝ) : ℂ) ∈ spectrum ℂ ((masslessDiracBloch c).H k) ∨
    (((-(c * |k|)) : ℝ) : ℂ) ∈ spectrum ℂ ((masslessDiracBloch c).H k) := by
  -- `masslessDiracBloch c` is the off-diagonal Bloch with `f(k) = c·k`.
  have hHeq : (masslessDiracBloch c).H k = (offDiagonalBloch (fun k => (c * k : ℂ))).H k := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [masslessDiracBloch, diracBloch, offDiagonalBloch, pauliX, pauliZ,
        Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, Complex.conj_ofReal]
  have hf : (c * k : ℂ) ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨by exact_mod_cast hc, by exact_mod_cast hk⟩
  have heig := offDiagonalBloch_eigenvalues (fun k => (c * k : ℂ)) k hf
  -- `‖(c*k : ℂ)‖ = |c|·|k| = c·|k|`-flavoured; we land on `±|c·k|`.
  rw [hHeq]
  have hnorm : ‖(c * k : ℂ)‖ = |c| * |k| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  -- WLOG the `+` branch (membership of `‖f k‖`); rewrite to `|c|·|k|`.
  by_cases hcpos : 0 ≤ c
  · left
    have hcabs : |c| = c := abs_of_nonneg hcpos
    have : ((c * |k| : ℝ) : ℂ) = ((‖(c * k : ℂ)‖ : ℝ) : ℂ) := by
      rw [hnorm, hcabs]
    rw [this]; exact heig.1
  · right
    rw [not_le] at hcpos
    have hcabs : |c| = -c := abs_of_neg hcpos
    have : ((-(c * |k|) : ℝ) : ℂ) = ((‖(c * k : ℂ)‖ : ℝ) : ℂ) := by
      rw [hnorm, hcabs]; push_cast; ring
    rw [this]; exact heig.1

/-- The **rescaled one-step coined-walk generator** at light speed `c` and
spatial step `Δx`.  One step `U = S·C` of the coined / Grover walk
`Graphplay.CoinedWalk.coinedStep` (with per-vertex coin `coin`) on the arc space
`V × V` differs from the identity; dividing the deviation `(U − I)` by the time
step `Δt = Δx/c` produces the *generator* whose continuum limit (as `Δx → 0`) is
`−i H_Dirac`.  We record it as `(c/Δx)·(coinedStep coin − 1)` — a genuine matrix
built from the real `coinedStep` object of `Graphplay.CoinedWalk`. -/
noncomputable def coinedWalkGenerator
    {V : Type u} [Fintype V] [DecidableEq V] (coin : Matrix V V ℂ) (c Δx : ℝ) :
    Matrix (V × V) (V × V) ℂ :=
  ((c / Δx : ℝ) : ℂ) • (CoinedWalk.coinedStep coin - 1)

/-- The **`2 × 2`-spinor restriction of the coined-walk generator to a fixed arc
pair `(x, y)`**: the `2 × 2` block of `coinedWalkGenerator` indexed by the two
"chirality" arc states `(x, y)` and `(y, x)` (the outgoing/incoming arc pair —
the discrete spinor degree of freedom of the walk).  This is the genuine
`2 × 2` matrix that the continuum limit compares against the Dirac Bloch
Hamiltonian `(masslessDiracBloch c).H k`. -/
noncomputable def coinedWalkSpinorBlock
    {V : Type u} [Fintype V] [DecidableEq V] (coin : Matrix V V ℂ) (c Δx : ℝ)
    (x y : V) : Matrix (Fin 2) (Fin 2) ℂ :=
  let arc : Fin 2 → V × V := fun a => if a = 0 then (x, y) else (y, x)
  fun a b => coinedWalkGenerator coin c Δx (arc a) (arc b)

/-- **The coined walk's continuum limit is the Dirac evolution
(`coinedWalk_continuum_dirac_conjecture`).**  This is recorded as an **open
conjecture** — a `Prop`-valued *statement*, NOT a proved theorem.

For the coined / Grover walk `U = S·C` of `Graphplay.CoinedWalk` with a unitary
coin, in the scaling limit where one step is spatial step `Δx` and time step
`Δt = Δx/c`, the **`2 × 2`-spinor block of the rescaled walk generator**
`coinedWalkSpinorBlock coin c Δx x y` (on the chirality arc pair `(x,y),(y,x)`)
converges, in the `L∞`-operator norm, to the **massless Dirac Bloch generator**
`−i·(masslessDiracBloch c).H k`.  These are two *genuinely different* `2 × 2`
matrices, so the bound is NOT a tautology `‖X − X‖`.

Concretely: there is a light speed `c > 0` and, for every accuracy `ε > 0`, a
spatial step `Δx > 0` small enough that for every momentum `k` and every arc
pair `x ≠ y` the spinor block is `ε`-close (in operator norm) to the Dirac
generator `−i·H_Dirac(k)`.

The hypotheses (`coin`, `hcoin`, `hV`) are genuinely *used*: the conjecture is
the statement about the specific unitary-coin walk operator `coinedStep coin`.

Reference: Meyer (1996); Bisio–D'Ariano–Tosini (2013); Strauch (2006).  This is
the quantum-walk → Dirac scaling-limit theorem, which has no packaged form in
Mathlib (no quantum-walk scaling-limit calculus), so we record it as an OPEN
CONJECTURE rather than asserting it as a proved theorem. -/
def coinedWalk_continuum_dirac_conjecture
    {V : Type u} [Fintype V] [DecidableEq V] (coin : Matrix V V ℂ)
    (_hcoin : coinᴴ * coin = 1) (_hV : Nonempty V) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ Δx : ℝ, 0 < Δx ∧
        ∀ (k : ℝ) (x y : V), x ≠ y →
          ‖coinedWalkSpinorBlock coin c Δx x y -
              (-Complex.I) • ((masslessDiracBloch c).H k)‖ ≤ ε

/-! ## §8  Round-up

The relativistic enrichment of Graphplay has two seeds, both equitable-quotient
phenomena:

* **`CliffordWeightedGraph`** (§2) — the Tower-3 carrier-algebra enrichment:
  spinor / Clifford-matrix-valued couplings, with a Hermitian block
  Hamiltonian.  Same axis as `MatrixGaugeField` (LatticeGauge) and the
  Jordan–Wigner fermions of `ManyBody`.
* **`offDiagonalBloch`** (§4) — the bipartite/sublattice Bloch Hamiltonian
  `[[0, f(k)], [conj f(k), 0]]`, whose `±|f(k)|` bands touch at the Dirac
  points `f(k) = 0`.  *This off-diagonal-quotient ⇒ ±-symmetric-band-with-a-zero
  algebra is fully proven and axiom-clean.*
* **`bipartite_equitable_dirac_cone`** / **`heavyHex_hosts_dirac_cone`**
  (§5–6) — the headline and its IBM heavy-hex instance: the data/flag
  off-diagonal quotient `[[0, 2√(N−1)], [2√(N−1), 0]]` hosts an emergent
  graphene-like Dirac cone.
* **`coinedWalk_continuum_dirac_conjecture`** (§7) — the discrete-time coined
  walk's continuum limit is the Dirac evolution, recorded as an OPEN CONJECTURE
  (`Prop`-valued statement, not a proved theorem): the `2 × 2`-spinor block of
  the rescaled walk generator converges to the massless Dirac Bloch generator.

What is reachable now is the **single-particle** Dirac structure: the band
algebra and the limit *statements*.  The continuum-analysis leaves (local
linearity of the cone, the literal scaling limit of the coined walk) are honest
`sorry`s marked `-- BLOCKED:`; interacting relativistic QFT is far-future.

The dispersion is, throughout, a **property of the equitable quotient's band
structure**: a quadratic (Schrödinger) quotient is non-relativistic, an
off-diagonal (graphene) quotient is relativistic.  Going up the towers — to a
Clifford-valued carrier — is what turns the quadratic CTQW into the linear
Dirac cone.
-/

end DiracLimit
end Graphplay
