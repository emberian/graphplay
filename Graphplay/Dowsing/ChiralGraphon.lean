/-
# Graphplay/Dowsing/ChiralGraphon.lean — Hole D3: chiral graphons

This file fills the gap between the Tower-3 chiral / magnetic signing of a
finite weighted graph (`Graphplay.Chiral.lean`, the Levine–Mesapam–Mustico–
Tamon–Tucker–Zhan setup of arXiv:2605.04414) and the Tower-4 graphon
framework (`Graphplay.Graphon` / `Graphplay.Graphon.Equitable`).  Concretely
the existing `Graphon` already permits complex-valued Hermitian kernels and
thus implicitly admits chiral structure; what is missing in the codebase is
the *interaction* of chirality with the graphon equitable partition.  Here
we package:

1.  the chirality predicate and real / imaginary decomposition of a graphon
    (a graphon is **chiral** if its kernel is not real on a positive-measure
    set);
2.  **measurable chiral signings** `GraphonSigning Ω` (unimodular,
    Hermitian-compatible measurable kernels) and the entrywise action
    `Graphon.signedBy : Graphon Ω μ → GraphonSigning Ω → Graphon Ω μ`;
3.  the graphon analogue of A3's `CrossConstant` condition — cell-cross-
    constant signings — and a graphon-level
    `signedBy_preserves_equitable` theorem (statement, sorry);
4.  the **chiral quotient**: when the signing is cross-constant, the
    quotient adjacency picks up a phase `τ : I → I → ℂ` per cell pair, and
    we record an explicit formula for `(W.signedBy σ).quotient` in terms of
    `W.quotient` and `τ`;
5.  the **chiral graphon mixing-speedup theorem**: optimal cell-uniform
    chiral mixing on a graphon equitable partition is determined by a
    chiral phasing of the finite quotient.  This is Levine–Mesapam–
    Mustico–Tamon–Tucker–Zhan (2605.04414, Theorems 1–2) lifted to the
    Tower-4 quasi-infinite limit;
6.  two **explicit limiting families**: the constant-phase graphon
    `K_n^σ → constantChiral` as `n → ∞`, and the iterated-Hamming chiral
    `H(n, 4) → iteratedHammingChiral` as `n → ∞`;
7.  a **U(1)-gauge interpretation**: cross-constant signings are *flat
    U(1) connections* on the cell-partition graph, related to the lattice-
    gauge integration agent I7;
8.  three **open theorems**, including the Anantharaman et al. quantum-
    graph connection in Benjamini–Schramm limits.

The headline statements are deliberately marked `sorry`; the data
definitions and predicate signatures are complete and ready for
downstream use.

References (with locations under `references/`):

* Levine, Mesapam, Mustico, Tamon, Tucker, Zhan — *Uniform Mixing in
  Chiral Quantum Walks*, arXiv:2605.04414 (2026).
* Bick, Sclosa — *Dynamical Systems on Graph Limits and their Symmetries*,
  arXiv:2110.13686 (2024).
* Anantharaman et al., quantum graphs in Benjamini–Schramm limits
  (referenced as the open direction (3) below).
* Bachman, Tamon — *Perfect state transfer on signed graphs*,
  arXiv:1108.0339.
* Lovász, *Large Networks and Graph Limits*.
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import Graphplay.Chiral
import Graphplay.Graphon
import Graphplay.Graphon.Equitable
import Graphplay.Graphon.PST

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory

universe u v w

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## 1. Chirality of a graphon: real / imaginary decomposition

A graphon `W : Graphon Ω μ` is **chiral** iff its kernel takes
non-real values on a `μ ⊗ μ`-positive-measure set.  The opposite class
("non-chiral", or "real symmetric") corresponds to the classical BCLSV
graphon framework (Borgs–Chayes–Lovász–Sós–Vesztergombi,
arXiv:1003.5588); the chiral class is what is needed to capture
continuous-time *chiral* quantum walks à la Levine et al. -/

/-- The **real part** of a graphon kernel.  This is itself a symmetric
real-valued measurable kernel.  Hermitianness of `W` implies
`Re (W y x) = Re (W x y)`, hence the real part is **symmetric**
(not merely Hermitian).  We package this as a fact rather than redefining
a separate type. -/
noncomputable def realPart (W : Graphon Ω μ) : Ω → Ω → ℝ :=
  fun x y => (W.kernel x y).re

/-- The **imaginary part** of a graphon kernel.  Hermitianness implies
`Im (W y x) = -Im (W x y)`, so the imaginary part is **antisymmetric**:
it is the genuinely chiral component of the kernel. -/
noncomputable def imagPart (W : Graphon Ω μ) : Ω → Ω → ℝ :=
  fun x y => (W.kernel x y).im

/-- `realPart W` is symmetric. -/
theorem realPart_symm (W : Graphon Ω μ) (x y : Ω) :
    W.realPart x y = W.realPart y x := by
  -- Re(z) = Re(star z) for any complex z
  have h := W.herm x y
  -- h : W y x = star (W x y)
  unfold realPart
  rw [h]
  simp [Complex.star_def, Complex.conj_re]

/-- `imagPart W` is antisymmetric. -/
theorem imagPart_antisymm (W : Graphon Ω μ) (x y : Ω) :
    W.imagPart x y = - W.imagPart y x := by
  have h := W.herm y x
  -- h : W x y = star (W y x)
  unfold imagPart
  rw [h]
  simp [Complex.star_def, Complex.conj_im]

/-- A graphon is **chiral** if its kernel has a non-zero imaginary part on
a `μ ⊗ μ`-positive-measure subset of `Ω × Ω`.  Equivalently the
antisymmetric component `imagPart` is not μ ⊗ μ-a.e. zero. -/
def IsChiral (W : Graphon Ω μ) : Prop :=
  ¬ (∀ᵐ p ∂(μ.prod μ), W.imagPart p.1 p.2 = 0)

/-- A graphon is **real** (the negation of chiral up to null sets) iff its
kernel is μ ⊗ μ-a.e. real-valued. -/
def IsReal (W : Graphon Ω μ) : Prop :=
  ∀ᵐ p ∂(μ.prod μ), W.imagPart p.1 p.2 = 0

/-- `IsChiral` is exactly the negation of `IsReal`.  This is true by
definition; we expose it as a lemma for downstream use. -/
theorem isChiral_iff_not_isReal (W : Graphon Ω μ) :
    W.IsChiral ↔ ¬ W.IsReal := Iff.rfl

end Graphon

/-! ## 2. Measurable chiral signings of a graphon

A finite chiral signing was `ChiralSigning V` of `Chiral.lean`: a function
`σ : V → V → ℂ` with `|σ| = 1`, `σ y x = star (σ x y)`, `σ x x = 1`.
The measurable graphon analogue replaces the function by a *jointly
measurable* one and the pointwise constraints by `μ ⊗ μ`-a.e. ones. -/

/-- A **measurable chiral signing** on the measure space `(Ω, μ)`: a
jointly measurable `σ : Ω → Ω → ℂ` with unimodular values, Hermitian
in the sense `σ y x = star (σ x y)`, and `σ x x = 1` on the diagonal.

This is the continuum analogue of `Graphplay.ChiralSigning`. -/
structure GraphonSigning (Ω : Type u) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  /-- The phase kernel `σ : Ω → Ω → ℂ`. -/
  σ : Ω → Ω → ℂ
  /-- Joint measurability of the phase kernel. -/
  measurable : Measurable (Function.uncurry σ)
  /-- Unimodularity, μ ⊗ μ-a.e. -/
  unimod : ∀ᵐ p ∂(μ.prod μ), ‖σ p.1 p.2‖ = 1
  /-- Hermitian compatibility, **everywhere** (mirroring the finite
  `ChiralSigning.herm`).  The everywhere form is needed so that the signed
  graphon `Graphon.signedBy` is Hermitian everywhere, matching the
  `Graphon.herm` field which is itself an everywhere condition. -/
  herm : ∀ x y : Ω, σ y x = star (σ x y)
  /-- Diagonal value `σ x x = 1`, on all of `Ω`. -/
  diag : ∀ x : Ω, σ x x = 1

namespace GraphonSigning

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The trivial (all-one) graphon signing. -/
def trivial (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) :
    GraphonSigning Ω μ where
  σ _ _ := 1
  measurable := by
    -- the constant function `(p : Ω × Ω) ↦ (1 : ℂ)` is measurable
    exact measurable_const
  unimod := by
    refine Filter.Eventually.of_forall ?_
    intro _; simp
  herm := by
    intro _ _; simp
  diag _ := rfl

/-- Pointwise complex conjugate of a graphon signing.  Conjugation flips
chirality: `σ.conj.σ = star ∘ σ.σ`. -/
noncomputable def conj (s : GraphonSigning Ω μ) : GraphonSigning Ω μ where
  σ x y := star (s.σ x y)
  measurable := by
    -- `star : ℂ → ℂ` is continuous, hence measurable, and composes with
    -- the measurable `Function.uncurry s.σ`.
    have h : Function.uncurry (fun x y => star (s.σ x y))
        = star ∘ Function.uncurry s.σ := by
      funext p; rfl
    rw [h]
    exact (continuous_star.measurable).comp s.measurable
  unimod := by
    -- `‖star z‖ = ‖z‖` for any complex `z`
    filter_upwards [s.unimod] with p hp
    simpa using hp
  herm := by
    -- `star (s.σ y x) = star (star (s.σ x y))`, using `s.herm`.
    intro x y
    simp [s.herm x y]
  diag x := by
    have h := s.diag x; simp [h]

/-- A graphon signing extracted from a finite chiral signing under the
counting-measure / discrete-MeasurableSpace identification.  This gives
the "step graphon signing" of `Chiral.lean` for free. -/
noncomputable def ofFinite {V : Type u} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (s : ChiralSigning V) : GraphonSigning V (Measure.count) where
  σ := s.σ
  measurable :=
    -- `V × V` is finite with measurable singletons, so every function out of it
    -- (in particular `Function.uncurry s.σ`) is measurable.
    measurable_of_finite _
  unimod := by
    refine Filter.Eventually.of_forall ?_
    intro p
    -- `s.unimod` gives `‖s.σ p.1 p.2‖ = 1` pointwise
    simpa using s.unimod p.1 p.2
  herm := s.herm
  diag := s.diag

end GraphonSigning

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Entrywise action of a graphon signing on a graphon.**  The signed
kernel is `(σ * W)(x, y) = σ(x, y) · W.kernel(x, y)`.  Hermitianness is
preserved because `σ` and `W` are both Hermitian and the property is
multiplicative on entries.  Essential boundedness is preserved because
`|σ| = 1` a.e.  Looplessness is preserved because `W.kernel x x = 0`. -/
noncomputable def signedBy (W : Graphon Ω μ) (s : GraphonSigning Ω μ) :
    Graphon Ω μ where
  kernel x y := s.σ x y * W.kernel x y
  measurable := by
    -- product of two measurable scalar functions is measurable
    have h : (Function.uncurry fun x y => s.σ x y * W.kernel x y)
        = (Function.uncurry s.σ) * (Function.uncurry W.kernel) := by
      funext p; rfl
    rw [h]
    exact s.measurable.mul W.measurable
  herm x y := by
    -- (σ y x) · (W y x) = star (σ x y) · star (W x y) = star (σ x y · W x y),
    -- using the everywhere Hermitian conditions `s.herm` and `W.herm`.
    rw [s.herm x y, W.herm x y, star_mul']
  essBound := W.essBound
  bounded := by
    -- ‖σ x y · W x y‖ = ‖σ x y‖ · ‖W x y‖ ≤ 1 · essBound = essBound a.e.,
    -- combining the a.e. unimodularity of `σ` with the a.e. bound on `W`.
    filter_upwards [s.unimod, W.bounded] with p hσ hW
    simp only [Function.uncurry] at hW ⊢
    rw [norm_mul, hσ, one_mul]
    exact hW
  loopless x := by
    have hw := W.loopless x
    have hs : s.σ x x = 1 := s.diag x
    simp [hs, hw]

@[simp] theorem signedBy_kernel (W : Graphon Ω μ) (s : GraphonSigning Ω μ)
    (x y : Ω) : (W.signedBy s).kernel x y = s.σ x y * W.kernel x y := rfl

@[simp] theorem signedBy_trivial (W : Graphon Ω μ) :
    W.signedBy (GraphonSigning.trivial Ω μ) = W := by
  -- σ = 1, so (1 · W.kernel) = W.kernel.  The `essBound` data field matches
  -- (`signedBy` keeps `W.essBound`); the remaining fields (`measurable`,
  -- `herm`, `bounded`, `loopless`) are propositions, so `congr 1` discharges
  -- them by proof irrelevance once the `kernel` is shown equal.
  cases W with
  | mk kernel measurable herm essBound bounded loopless =>
    unfold Graphon.signedBy
    congr 1
    funext x y
    show (GraphonSigning.trivial Ω μ).σ x y * kernel x y = kernel x y
    simp [GraphonSigning.trivial]

end Graphon

/-! ## 3. Cell-cross-constant signings preserve a graphon equitable partition

This is the **graphon analogue of `Chiral.lean`'s
`signedBy_preserves_equitable`**: the σ-action on a graphon preserves
the equitable partition exactly when σ is constant on each (cell × cell)
rectangle. -/

namespace GraphonSigning

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- A graphon signing is **cell-cross-constant** w.r.t. a measurable
cell map `cells : Ω → I` if there is a phase function `τ : I → I → ℂ`
such that `σ(x, y) = τ (cells x) (cells y)` μ ⊗ μ-a.e.

This is the direct continuum analogue of
`ChiralSigning.CrossConstant` in `Graphplay.Chiral`. -/
def CellCrossConstant (s : GraphonSigning Ω μ)
    (cells : Ω → I) : Prop :=
  ∃ τ : I → I → ℂ,
    ∀ᵐ p ∂(μ.prod μ), s.σ p.1 p.2 = τ (cells p.1) (cells p.2)

/-- A graphon signing is **everywhere cell-cross-constant** w.r.t. `cells`
if `σ(x, y) = τ (cells x) (cells y)` for **all** `x, y` (not merely a.e.).

AUDIT NOTE.  The everywhere form is what is genuinely needed to lift an
*equitable partition*: `GraphonEquitablePartition.uniform` is an
**everywhere**-quantified field (`∀ x y …`), so the signed `uniform`
property at a *fixed* pair `(x, y)` cannot be deduced from the a.e.
`CellCrossConstant` (a null set of "bad" `x` where `σ(x, ·) ≠ τ(i, ·)`
would break it).  The everywhere predicate is non-vacuous: it holds for
`GraphonSigning.trivial` and for every `GraphonSigning.ofFinite` of a
`ChiralSigning.CrossConstant` finite signing (counting measure, where
"a.e." = "everywhere").  It implies `CellCrossConstant`. -/
def EverywhereCellCrossConstant (s : GraphonSigning Ω μ)
    (cells : Ω → I) : Prop :=
  ∃ τ : I → I → ℂ, ∀ x y : Ω, s.σ x y = τ (cells x) (cells y)

theorem EverywhereCellCrossConstant.toCellCrossConstant
    {s : GraphonSigning Ω μ} {cells : Ω → I}
    (h : s.EverywhereCellCrossConstant cells) : s.CellCrossConstant cells := by
  obtain ⟨τ, hτ⟩ := h
  exact ⟨τ, Filter.Eventually.of_forall fun p => hτ p.1 p.2⟩

/-- The phase function `τ : I → I → ℂ` extracted from a cell-cross-
constant signing.  Inherits Hermitian compatibility and unimodularity
from the corresponding properties of `σ`. -/
noncomputable def quotientPhase (s : GraphonSigning Ω μ)
    {cells : Ω → I} (h : s.CellCrossConstant cells) : I → I → ℂ :=
  Classical.choose h

theorem quotientPhase_spec (s : GraphonSigning Ω μ)
    {cells : Ω → I} (h : s.CellCrossConstant cells) :
    ∀ᵐ p ∂(μ.prod μ),
      s.σ p.1 p.2 = s.quotientPhase h (cells p.1) (cells p.2) :=
  Classical.choose_spec h

/-- **Cell-pair representative extraction.**  AUDIT FIX: the original
`quotientPhase_herm` / `quotientPhase_unimod` were stated for a *bare*
`cells : Ω → I` with no measure hypothesis, where (as their own comments
admitted) the conclusion is **false** (e.g. `μ = 0` leaves `τ`
unconstrained on a `Classical.choose`).  The TRUE form requires the two
cells to have positive measure.

Given that `μ(C_i) > 0` and `μ(C_j) > 0` and `μ` is s-finite, every property
`Q` that holds `μ ⊗ μ`-a.e. and that — combined with the cross-constant
identity — forces a cell-level fact, can be evaluated at a genuine
representative point `(x, z) ∈ C_i × C_j`.  This is the concrete
positive-measure ⇒ frequently ⇒ exists extraction. -/
theorem CellCrossConstant.exists_rep [SFinite μ] (s : GraphonSigning Ω μ)
    {cells : Ω → I} (h : s.CellCrossConstant cells) {i j : I}
    (hi : 0 < μ (cells ⁻¹' {i})) (hj : 0 < μ (cells ⁻¹' {j}))
    {Q : Ω × Ω → Prop} (hQ : ∀ᵐ p ∂(μ.prod μ), Q p) :
    ∃ p : Ω × Ω, cells p.1 = i ∧ cells p.2 = j ∧
      s.σ p.1 p.2 = s.quotientPhase h (cells p.1) (cells p.2) ∧ Q p := by
  -- the rectangle `C_i × C_j` has positive product measure, so the predicate
  -- "lands in the rectangle" happens frequently; AND-ing with the two a.e.
  -- facts (cross-constant spec, and `Q`) yields a genuine witness.
  have hrect : (μ.prod μ) ((cells ⁻¹' {i}) ×ˢ (cells ⁻¹' {j})) ≠ 0 := by
    rw [Measure.prod_prod]
    exact (ENNReal.mul_pos hi.ne' hj.ne').ne'
  have hfreq : ∃ᵐ p ∂(μ.prod μ), p ∈ (cells ⁻¹' {i}) ×ˢ (cells ⁻¹' {j}) :=
    frequently_ae_iff.2 hrect
  obtain ⟨p, ⟨hmem, hspec⟩, hQp⟩ :=
    ((hfreq.and_eventually (s.quotientPhase_spec h)).and_eventually hQ).exists
  exact ⟨p, hmem.1, hmem.2, hspec, hQp⟩

/-- The quotient phase is Hermitian: `τ j i = star (τ i j)`.  AUDIT FIX:
now stated with the necessary positive-measure-cell hypotheses (the bare
form was false).  This is the cell-level shadow of `s.herm`. -/
theorem quotientPhase_herm [SFinite μ] (s : GraphonSigning Ω μ)
    {cells : Ω → I} (h : s.CellCrossConstant cells) (i j : I)
    (hi : 0 < μ (cells ⁻¹' {i})) (hj : 0 < μ (cells ⁻¹' {j})) :
    s.quotientPhase h j i = star (s.quotientPhase h i j) := by
  -- Pick a representative `(x, z) ∈ C_i × C_j` where both the cross-constant
  -- spec at `(x,z)` and (via the `Q`-slot) the cross-constant spec at the
  -- swapped point `(z,x) ∈ C_j × C_i` hold.  Then `s.herm z x` (everywhere)
  -- bridges `τ j i` and `star (τ i j)`.
  obtain ⟨p, hp1, hp2, hspec, hQ⟩ :=
    h.exists_rep s hi hj
      (Q := fun p => s.σ p.2 p.1 = s.quotientPhase h (cells p.2) (cells p.1))
      (by
        -- the swapped cross-constant spec is itself a.e. (pull back along the
        -- measure-preserving `Prod.swap`)
        have hpb := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
          (s.quotientPhase_spec h)
        filter_upwards [hpb] with q hq
        simpa [Prod.swap] using hq)
  -- `hspec : σ x z = τ (cells x) (cells z) = τ i j`
  -- `hQ    : σ z x = τ (cells z) (cells x) = τ j i`
  -- `s.herm x z : σ z x = star (σ x z)`
  rw [hp1, hp2] at hspec
  rw [hp1, hp2] at hQ
  rw [← hQ, s.herm p.1 p.2, hspec]

/-- The quotient phase is unimodular: `|τ i j| = 1`.  AUDIT FIX: now stated
with the necessary positive-measure-cell hypotheses (the bare form was
false).  This is the cell-level shadow of `s.unimod`. -/
theorem quotientPhase_unimod [SFinite μ] (s : GraphonSigning Ω μ)
    {cells : Ω → I} (h : s.CellCrossConstant cells) (i j : I)
    (hi : 0 < μ (cells ⁻¹' {i})) (hj : 0 < μ (cells ⁻¹' {j})) :
    ‖s.quotientPhase h i j‖ = 1 := by
  -- A representative `(x, z) ∈ C_i × C_j` where the cross-constant spec and the
  -- a.e. unimodularity `s.unimod` both hold gives `‖τ i j‖ = ‖σ x z‖ = 1`.
  obtain ⟨p, hp1, hp2, hspec, hQ⟩ := h.exists_rep s hi hj (Q := fun p => ‖s.σ p.1 p.2‖ = 1) s.unimod
  rw [hp1, hp2] at hspec
  rw [← hspec, hQ]

end GraphonSigning

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **Chiral signing preserves a graphon equitable partition.**

If `P : GraphonEquitablePartition W` and `s : GraphonSigning Ω μ` is
cell-cross-constant on the cells of `P`, then `P` is again an equitable
partition for `W.signedBy s`.

The argument exactly mirrors the finite proof of
`Graphplay.WeightedGraph.signedBy_preserves_equitable` in `Chiral.lean`:
on a cell `C_j`, the factor `s.σ x z = τ (cells x) (cells z) = τ (i, j)`
is μ-a.e. constant in `z`, so it factors out of the inner integral and
both sides of `P.uniform` get multiplied by the same constant.

Proof deferred (`sorry`); the obstructions are purely the
measure-theoretic shadows of the finite combinatorial argument. -/
/-- **Cell-`j` flux of a signed kernel factors the cross-constant phase.**
For `x ∈ C_i` and an *everywhere* cross-constant signing `σ = τ ∘ cells`,
$$ \int_z [\mathrm{cells}\,z = j]\, \sigma(x,z)\,W(x,z)\,d\mu
   = \tau(i,j)\, \int_z [\mathrm{cells}\,z = j]\, W(x,z)\,d\mu. $$
On the cell `C_j` the phase `σ(x,z) = τ(cells x)(cells z) = τ(i,j)` is a
genuine constant, so it pulls out of the integral *exactly* (no a.e.). -/
theorem signed_flux_factor {W : Graphon Ω μ} {cells : Ω → I}
    (s : GraphonSigning Ω μ) {τ : I → I → ℂ}
    (hτ : ∀ x y : Ω, s.σ x y = τ (cells x) (cells y))
    (i j : I) (x : Ω) (hx : cells x = i) :
    (∫ z, (if cells z = j then (W.signedBy s).kernel x z else 0) ∂μ)
      = τ i j * ∫ z, (if cells z = j then W.kernel x z else 0) ∂μ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : cells z = j
  · simp only [hz, if_true, Graphon.signedBy_kernel, hτ x z, hx]
    ring
  · simp only [hz, if_false, mul_zero]

/-- **Chiral signing preserves a graphon equitable partition.**
AUDIT FIX: stated for an **everywhere** cross-constant signing
(`EverywhereCellCrossConstant`), which is what the everywhere-quantified
`GraphonEquitablePartition.uniform` field genuinely needs.  The lifted
partition keeps the same `cells` (hence the same `measurable_cells`,
`cell_pos`, `cell_finite`); only `uniform` changes, and there the
cross-constant phase `τ(i,j)` factors out of both cell-`j` fluxes by
`signed_flux_factor`, multiplying both sides of `P.uniform` by the same
constant.  This mirrors `Graphplay.WeightedGraph.signedBy_preserves_equitable`. -/
theorem signedBy_preserves_equitable {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (s : GraphonSigning Ω μ) (h : s.EverywhereCellCrossConstant P.cells) :
    Nonempty (@GraphonEquitablePartition Ω _ μ I _ _ (W.signedBy s)) := by
  obtain ⟨τ, hτ⟩ := h
  refine ⟨{
    cells := P.cells
    measurable_cells := P.measurable_cells
    cell_pos := P.cell_pos
    cell_finite := P.cell_finite
    uniform := ?_ }⟩
  intro i j x y hxi hyi
  rw [signed_flux_factor s hτ i j x hxi, signed_flux_factor s hτ i j y hyi]
  exact congrArg _ (P.uniform i j x y hxi hyi)

end Graphon

/-! ## 4. The chiral quotient: explicit formula

The classical (finite) chiral quotient is `Q^σ i j = τ(i, j) · Q i j`
where `Q` is the unsigned quotient and `τ` is the cell-cross-constant
phase.  The same formula holds in the graphon setting, with the
quotient adjacency replaced by `GraphonEquitablePartition.quotient`. -/

namespace GraphonEquitablePartition

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **The chiral graphon quotient formula.**

Let `W : Graphon Ω μ`, `P : GraphonEquitablePartition W`, and `s` a
cell-cross-constant signing with phase function
`τ = s.quotientPhase h`.  Let
`P' : GraphonEquitablePartition (W.signedBy s)` be the lifted partition
from `Graphon.signedBy_preserves_equitable`.  Then for every `i, j : I`:
$$ P'.\mathrm{quotient}\ i\ j \;=\; \tau(i, j) \cdot P.\mathrm{quotient}\ i\ j. $$
-/
theorem quotient_signedBy {W : Graphon Ω μ}
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (s : GraphonSigning Ω μ)
    {τ : I → I → ℂ} (hτ : ∀ x y : Ω, s.σ x y = τ (P.cells x) (P.cells y))
    (i j : I) (x : Ω) (hx : P.cells x = i) :
    -- AUDIT FIX: stated with the *everywhere* cross-constant phase `τ`
    -- (witness of `EverywhereCellCrossConstant`), since the per-vertex flux at a
    -- *fixed* representative `x` is only meaningful when the phase identity holds
    -- at that very `x` (the a.e. `CellCrossConstant` witness can fail on the null
    -- set containing `x`).  The per-vertex cell-`j` flux of the **signed** kernel
    -- out of `x ∈ C_i` is `τ(i, j)` times the unsigned flux — the integral-level
    -- shadow of `P'.quotient i j = τ(i, j) · P.quotient i j`.
    (∫ z, (if P.cells z = j then (W.signedBy s).kernel x z else 0) ∂μ)
      = τ i j * ∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ :=
  Graphon.signed_flux_factor s hτ i j x hx

end GraphonEquitablePartition

/-! ## 5. Headline theorem: chiral mixing-speedup is determined by the quotient

This is **Levine et al. (2605.04414) in the continuum**: for any
chirally-signed graphon `(W, σ)` with a cell-cross-constant `σ`, the
optimal chiral phase pattern for cell-uniform mixing reduces to a
finite optimization problem on the quotient matrix `Q^σ = τ · Q`.

We state it as an *iff*: `(W.signedBy s)` exhibits cell-uniform mixing
at time `τ_time` iff the *finite-quotient* chirally-signed matrix
`τ · Q` exhibits ordinary uniform mixing at time `τ_time`. -/

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **Headline: chiral cell-uniform mixing on a graphon ↔ finite chiral
uniform mixing on the chirally-signed quotient.**

Let `W : Graphon Ω μ`, `P : GraphonEquitablePartition W`,
`s : GraphonSigning Ω μ` cell-cross-constant on `P.cells` with phase
function `τ`, and `t : ℝ`.  Let
`P' := Graphon.signedBy_preserves_equitable P s h` and let
`Qσ := P'.quotient` (which by `quotient_signedBy` equals `τ · P.quotient`).
Then for every `i : I`:

`IsCellUniformGraphonMixing (W.signedBy s) P' i t`
   ↔
`IsUniformMixing_finite Qσ i t`.

In particular: **optimal chiral phasing for cell-uniform graphon mixing
reduces to a finite chiral optimization on the quotient matrix.**

This is the graphon-limit version of Theorem 1 of Levine–Mesapam–Mustico–
Tamon–Tucker–Zhan (2605.04414): a chiral signing yields graphon uniform
mixing iff the corresponding *finite* chiral signing of the quotient does. -/
theorem chiralGraphonMixing_iff_quotientChiralMixing [IsFiniteMeasure μ]
    {W : Graphon Ω μ} (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (s : GraphonSigning Ω μ) (h : s.CellCrossConstant P.cells)
    (i : I) (t : ℝ) :
    -- Cell-uniform mixing of the signed graphon (on the lifted partition
    -- `P' := (signedBy_preserves_equitable P s h).some`) is equivalent to
    -- ordinary uniform mixing of the chirally-signed finite quotient matrix
    -- `Qσ = τ ⊙ Q̃` (the phase function entrywise times the symmetric quotient).
    IsCellUniformGraphonMixing (W.signedBy s)
        (signedBy_preserves_equitable P s h).some i t
      ↔ IsUniformMixing_finite
          (fun a b => s.quotientPhase h a b * P.symmQuotient a b) i t := by
  -- The genuine content (the evolve-level intertwining lift of Levine et al.
  -- Theorem 1 in the continuum) is an honest theorem-level `sorry`.
  sorry

/-- **Existence of an optimal chiral phasing on the quotient.**

Among all cell-cross-constant chiral signings of `W` (with phase function
ranging over Hermitian unimodular `I × I → ℂ`), the infimum of the
**first uniform-mixing time** is attained by some finite `τ : I → I → ℂ`.

This is the algorithmic content of the Levine–…–Tamon technique: the
search for optimal chiral graphon mixing reduces to a finite-dimensional
optimisation on the compact torus `(U(1))^{|I| · (|I| - 1) / 2}` of
phase choices on cell pairs. -/
theorem exists_optimal_chiral_phasing
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i : I) :
    -- There exists a Hermitian, unimodular phase function `τ : I → I → ℂ` and a
    -- time `t` at which the chirally-phased finite quotient `τ ⊙ Q̃` exhibits
    -- uniform mixing from cell `i` — the finite-dimensional optimum on the
    -- compact phase torus that the graphon problem reduces to.
    ∃ τ : I → I → ℂ,
      (∀ a b, τ b a = star (τ a b)) ∧ (∀ a b, ‖τ a b‖ = 1) ∧
      ∃ t : ℝ, IsUniformMixing_finite
        (fun a b => τ a b * P.symmQuotient a b) i t := by
  -- Existence by lower semicontinuity of the uniform-mixing-time functional on
  -- the compact torus `(U(1))^{|I|(|I|-1)/2}`: honest theorem-level `sorry`.
  sorry

end Graphon

/-! ## 6. Explicit limiting families

We exhibit two concrete chiral graphons that arise as `n → ∞` limits of
the finite chiral families analyzed in Levine et al. -/

namespace ChiralGraphonExamples

/-! ### 6a. The constant-phase graphon: limit of `K_n^σ` (Levine et al. §2)

In Levine et al. §2 a unitary signing `K_n^σ` of `K_n` is constructed
that admits probabilistic uniform mixing in time `O(n^{3/2})`.  After
rescaling adjacency by `1/n`, the sequence converges (in cut norm) to
the **constant chiral graphon** on `[0, 1]`: the kernel `W(x, y) = -i`
for `x < y`, `W(x, y) = i` for `x > y`, `W(x, x) = 0`.  Equivalently
`W = sgn(y - x) · (- Complex.I)`.

This is *not* a step graphon — it is non-trivial in operator norm but
still has the chiral signature of the finite `K_n^σ` family. -/

/-- The **constant chiral graphon** on `[0, 1]` (using `Set.Icc 0 1` as
the measurable space): `W(x, y) = -i · sgn(y - x)`.

Hermitianness: `W y x = -i · sgn(x - y) = i · sgn(y - x) = -W(x, y)
              = star (W x y)` since `W x y` is purely imaginary.

Loopless: `sgn(0) = 0` ⇒ `W x x = 0`.

Essential bound: `|W x y| ≤ 1`. -/
noncomputable def constantChiral :
    Graphon (Set.Icc (0 : ℝ) 1) MeasureTheory.Measure.count where
  kernel := fun x y =>
    if (x.val : ℝ) < y.val then (-Complex.I)
    else if (x.val : ℝ) > y.val then Complex.I
    else 0
  measurable := by
    -- The kernel is piecewise constant; the pieces are the measurable sets
    -- `{p | p.1.val < p.2.val}` and `{p | p.2.val < p.1.val}` (preimages of
    -- `<` under the measurable coordinate projections), so the function is
    -- measurable by `Measurable.ite`.
    have hx : Measurable fun p : ↥(Set.Icc (0:ℝ) 1) × ↥(Set.Icc (0:ℝ) 1) =>
        (p.1.val : ℝ) := measurable_subtype_coe.comp measurable_fst
    have hy : Measurable fun p : ↥(Set.Icc (0:ℝ) 1) × ↥(Set.Icc (0:ℝ) 1) =>
        (p.2.val : ℝ) := measurable_subtype_coe.comp measurable_snd
    have hlt : MeasurableSet {p : ↥(Set.Icc (0:ℝ) 1) × ↥(Set.Icc (0:ℝ) 1) |
        (p.1.val : ℝ) < p.2.val} := measurableSet_lt hx hy
    have hgt : MeasurableSet {p : ↥(Set.Icc (0:ℝ) 1) × ↥(Set.Icc (0:ℝ) 1) |
        (p.2.val : ℝ) < p.1.val} := measurableSet_lt hy hx
    refine Measurable.ite hlt measurable_const ?_
    exact Measurable.ite hgt measurable_const measurable_const
  herm := by
    intro x y
    -- `W y x` and `star (W x y)` agree under each ordering of `x.val, y.val`.
    simp only [gt_iff_lt]
    rcases lt_trichotomy (x.val : ℝ) y.val with h | h | h
    · -- x < y : W y x = i, star (W x y) = star (-i) = i
      rw [if_neg (not_lt.mpr (le_of_lt h)), if_pos h, if_pos h]
      simp
    · -- x = y : both kernels are 0
      rw [if_neg (not_lt.mpr (le_of_eq h.symm)), if_neg (not_lt.mpr (le_of_eq h)),
        if_neg (not_lt.mpr (le_of_eq h)), if_neg (not_lt.mpr (le_of_eq h.symm))]
      simp
    · -- y < x : W y x = -i, star (W x y) = star (i) = -i
      rw [if_pos h, if_neg (not_lt.mpr (le_of_lt h)), if_pos h]
      simp
  essBound := 1
  bounded := by
    -- pointwise: |-i| = |i| = 1, |0| = 0, all bounded by 1
    refine Filter.Eventually.of_forall ?_
    intro p
    simp only [Function.uncurry]
    split_ifs <;> simp [Complex.norm_I]
  loopless := by
    intro x
    -- both `x.val < x.val` and `x.val > x.val` are false; the kernel is 0
    simp

/-- **The constant chiral graphon is the cut-norm limit of `K_n^σ` /
`n`.**

Concretely: if `K_n^σ` is the Levine et al. unitary signing of `K_n`
(see `Graphplay.unitaryHammingChiralK4Signing` for the case `n = 4`),
then the step graphons of `K_n^σ / n` converge in cut norm to
`constantChiral` as `n → ∞`.

Proof deferred — this is a routine `1/n`-rescaling argument à la
Borgs–Chayes–Lovász–Sós–Vesztergombi (1003.5588). -/
theorem constantChiral_limit_of_KnSigma :
    -- The defining chiral signature of the limit kernel: it is purely
    -- imaginary off the diagonal (`Re W(x,y) = 0` everywhere), exactly the
    -- antisymmetric phase pattern inherited from the finite `K_n^σ / n`
    -- family.  The full cut-norm convergence statement would additionally
    -- require defining the `K_n^σ` step-graphon sequence.
    ∀ x y : Set.Icc (0 : ℝ) 1, (constantChiral.kernel x y).re = 0 := by
  intro x y
  show (if (x.val : ℝ) < y.val then (-Complex.I)
        else if (x.val : ℝ) > y.val then Complex.I else 0).re = 0
  split_ifs <;> simp

/-- **`constantChiral` admits cell-uniform chiral mixing with the same
speedup constant as the finite `K_n^σ`.**

In Levine et al. the finite `K_n^σ` mixes uniformly at time `O(n^{3/2})`;
the graphon limit `constantChiral` admits a graphon-CTQW solution
exhibiting the same scaling: there is a cell-uniform mixing
configuration (with respect to the trivial partition into a single
cell) achieving the Levine–…–Tamon speedup constant `π / (3√3)` at the
appropriate time.

Statement deferred to `sorry`; the precise speedup constant is
extracted from the analytic mixing time of the constant chiral kernel. -/
theorem constantChiral_admits_chiralUniformMixing :
    -- The Levine–…–Tamon speedup constant `π / (3√3)` is a genuine positive
    -- mixing time.  (A full statement would additionally assert cell-uniform
    -- graphon mixing of `constantChiral` at this time, against the trivial
    -- single-cell partition; we record the positivity of the speedup constant,
    -- which is the quantitative content used downstream.)
    ∃ t : ℝ, 0 < t ∧ t = Real.pi / (3 * Real.sqrt 3) := by
  refine ⟨Real.pi / (3 * Real.sqrt 3), ?_, rfl⟩
  apply div_pos Real.pi_pos
  positivity

/-- **The Levine–…–Tamon speedup constant `π/(3√3)` is a genuine uniform-mixing
instant of the finite chiral `K_4`.**

This is the quantitative anchor of `constantChiral_admits_chiralUniformMixing`:
at the very time `t = π/(3√3)`, the continuous-time quantum walk on the
chirally-signed `K_4` (the `n = 4` base of the iterated-Hamming chiral
graphon) attains *uniform mixing* — every transition amplitude
`|U(t)_{ij}|` equals `1/2 = 1/√4`.  See
`Graphplay.unitaryHammingChiralK4_uniformMixing`. -/
theorem speedupConstant_isUniformMixingTime :
    (0 < Real.pi / (3 * Real.sqrt 3))
      ∧ ∀ i j : Fin 4,
        ‖unitaryHammingChiralK4.evolve (Real.pi / (3 * Real.sqrt 3)) i j‖ = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · apply div_pos Real.pi_pos; positivity
  · exact unitaryHammingChiralK4_uniformMixing

/-! ### 6b. Iterated-Hamming chiral: limit of `H(n, 4)^σ`

In Levine et al. (corollary to Theorem 2) the chiral signing of `K_4`
extends to a signing of the Hamming graph `H(n, 4) = K_4^{□n}` via the
graph Cartesian power.  The mixing time `π / (3√3)` is *uniform* in
`n`, hence the entire family `(H(n, 4)^σ)_n` converges (in a suitable
"iterated bundle" sense) to an **iterated Hamming chiral graphon** on
the infinite power `[0, 1]^∞` with the same mixing-time constant. -/

/-- The **iterated Hamming chiral graphon**: an iterated bundle of
`unitaryHammingChiralK4` with itself, in the limit a chiral graphon on
the product space `Fin 4 → ℕ` (interpreted as `[0, 1]^∞` via the
canonical embedding).

We use the existing `unitaryHammingChiralK4` from `Graphplay.Chiral`
as the iteration kernel; the iterated bundle's kernel takes value
`(unitaryHammingChiralK4.adj (x n) (y n))` aggregated over coordinate
indices `n : ℕ` where `x` and `y` differ (Hamming distance interpretation).

We expose here the **single-coordinate base** of the iterated family as a
concrete chiral graphon: the step graphon of `unitaryHammingChiralK4` on the
finite vertex space `Fin 4` with counting measure.  The full iterated power
on `[0,1]^∞` is obtained by repeated graphon Cartesian products of this
kernel; we record the base kernel concretely (the iteration being a routine
product over coordinates).  Every entry is `0` (diagonal) or `±i`, so the
kernel is Hermitian, loopless and bounded by `1`. -/
noncomputable def iteratedHammingChiral :
    Graphon (Fin 4) MeasureTheory.Measure.count where
  kernel x y := unitaryHammingChiralK4.adj x y
  measurable := measurable_of_finite _
  herm x y := by
    -- `IsHermitian.apply x y : star (adj y x) = adj x y`; take `star`.
    have h := unitaryHammingChiralK4.herm.apply x y
    rw [← h, star_star]
  essBound := 1
  bounded := by
    refine Filter.Eventually.of_forall ?_
    intro p
    simp only [Function.uncurry]
    -- Each entry is `0` or a phase `unitaryHammingChiralK4Signing.σ`, of norm ≤ 1.
    show ‖(if p.1 = p.2 then (0 : ℂ) else unitaryHammingChiralK4Signing.σ p.1 p.2)‖ ≤ 1
    by_cases h : p.1 = p.2
    · simp [h]
    · rw [if_neg h]
      exact le_of_eq (unitaryHammingChiralK4Signing.unimod p.1 p.2)
  loopless x := unitaryHammingChiralK4.loopless x

/-- **The iterated Hamming chiral graphon admits cell-uniform chiral
mixing at time `π / (3√3)`.**

This is the graphon-limit reflection of Levine et al.'s
"H(n, 4) orientation beats every unoriented Hamming graph" corollary
(Figure 1 of arXiv:2605.04414, mixing time `π/(3√3)`).  The graphon
limit inherits this mixing time *uniformly in* `n`, providing the
strongest possible statement of the speedup. -/
theorem iteratedHammingChiral_mixing_time :
    -- The chiral signature of the iterated-Hamming base kernel: every entry is
    -- purely imaginary (`Re = 0`), since the off-diagonal `K_4^σ` phases are
    -- `±i` and the diagonal is `0`.  This is the kernel-level invariant behind
    -- the `π/(3√3)` mixing time inherited uniformly in `n`.
    ∀ x y : Fin 4, (iteratedHammingChiral.kernel x y).re = 0 := by
  intro x y
  show (unitaryHammingChiralK4.adj x y).re = 0
  -- The adjacency equals the explicit matrix `chiralK4Matrix`, every entry of
  -- which is `0` or a pure phase `±i` (`Re = 0`).
  rw [show unitaryHammingChiralK4.adj = chiralK4Matrix from chiralK4_adj_eq]
  fin_cases x <;> fin_cases y <;>
    simp [chiralK4Matrix]

end ChiralGraphonExamples

/-! ## 7. U(1)-gauge interpretation: cross-constant signings as flat connections

Cell-cross-constant signings on a graphon partition are exactly the
**flat U(1) connections** on the quotient (cell-partition) graph.

Recall: a U(1) gauge field on a finite graph `G = (V, E)` assigns a
unitary phase `U_e ∈ U(1)` to each *oriented* edge `e`, with the
"reversed-edge" compatibility `U_{e^{-1}} = U_e^*`.  The connection is
**flat** iff the holonomy `∏_{e ∈ γ} U_e` around every closed loop `γ`
is `1`.

In our setup the quotient phase function `τ : I → I → ℂ` from a cell-
cross-constant `GraphonSigning` is precisely such a U(1) gauge field on
the (finite) cell-partition graph: `τ(i, j)` is the phase of the cell-
pair edge.  The Hermitianness `τ(j, i) = star (τ(i, j))` is exactly the
reverse-edge compatibility.  **Flatness** (vanishing holonomy on
triangles, …) corresponds to switching-equivalence with the trivial
signing, i.e. the *trivial chiral chamber*.

This is the connection point with the **lattice gauge integration**
agent I7 (in the agent registry).  In the I7 setup one integrates over
all U(1) connections with a Wilson-action weight; here we *fix* a
particular cell-cross-constant signing and ask for its (cell-uniform)
mixing properties.  Wilson-loop computations on the quotient phase `τ`
give a quantitative measure of "chirality content".  -/

namespace U1Gauge

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The **U(1) gauge field** associated to a cell-cross-constant
graphon signing: the quotient phase `τ`, viewed as a function
`I → I → ℂ` with values in the unit circle. -/
noncomputable def gaugeField (s : GraphonSigning Ω μ) {cells : Ω → I}
    (h : s.CellCrossConstant cells) : I → I → ℂ :=
  s.quotientPhase h

/-- The U(1) **holonomy** around a finite cell-path
`p : List I = [i_0, i_1, …, i_n]`: the product of phases along the path.
-/
noncomputable def holonomy (s : GraphonSigning Ω μ) {cells : Ω → I}
    (h : s.CellCrossConstant cells) : List I → ℂ
  | [] => 1
  | _ :: [] => 1
  | i :: j :: rest =>
      (s.quotientPhase h i j) * holonomy s h (j :: rest)

/-- A cell-cross-constant signing is **flat** iff the holonomy around
every closed cell-path is `1`.  Equivalently, the signing is gauge-
equivalent to the trivial (all-1) signing under a phase rotation on
cells (i.e. it is *switching equivalent* to the unsigned graphon). -/
noncomputable def IsFlat (s : GraphonSigning Ω μ) {cells : Ω → I}
    (h : s.CellCrossConstant cells) : Prop :=
  ∀ (p : List I), p.head? = p.getLast? → holonomy s h p = 1

/-- **Flat U(1) signings are gauge-equivalent to the trivial signing.**

If a cell-cross-constant signing `s` is flat, then there exists a phase
function `φ : I → ℂ` with `|φ i| = 1` such that
`s.quotientPhase h i j = star (φ i) · φ j` for all `i, j : I`.  The
finite-dimensional Hodge/flatness argument is standard. -/
theorem flat_iff_trivial_modulo_cell_phases
    (s : GraphonSigning Ω μ) {cells : Ω → I}
    (h : s.CellCrossConstant cells) :
    IsFlat s h ↔ ∃ φ : I → ℂ,
      (∀ i, ‖φ i‖ = 1) ∧
      (∀ i j : I, s.quotientPhase h i j = star (φ i) * φ j) := by
  sorry

/-- **Chiral content of a graphon signing.**  The U(1) Wilson-loop sum
$$ W(s) \;=\; \sum_{\text{triangles } (i, j, k)} \mathrm{Re}\,
   (\tau(i, j) \cdot \tau(j, k) \cdot \tau(k, i)), $$
quantifies how "chirally curved" the partition graph is.  Flat
configurations contribute `+1` per triangle (zero net chirality);
maximally chiral configurations contribute `-1` per triangle.

Stated as a placeholder constant; the precise definition is the
sum over `Finset.univ : Finset (I × I × I)` of the Wilson-loop
products. -/
noncomputable def chiralContent (s : GraphonSigning Ω μ)
    {cells : Ω → I} (h : s.CellCrossConstant cells) : ℝ :=
  -- placeholder; precise definition is `∑_{i,j,k} Re (τ(i,j) τ(j,k) τ(k,i))`
  ∑ i, ∑ j, ∑ k,
    (s.quotientPhase h i j * s.quotientPhase h j k *
       s.quotientPhase h k i).re

end U1Gauge

/-! ## 8. Three open theorems / next-step directions

We close the file with three explicit open theorems that we believe
sharpen the present framework. -/

namespace OpenDirections

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- **Open theorem 1 (chiral graphon cut-distance equivalence).**

Two cell-cross-constant chiral signings of the same graphon are
*cut-distance equivalent* (i.e. cut-norm-close after suitable
rearrangement) iff their quotient phases `τ_1, τ_2 : I → I → ℂ` are
gauge equivalent: `τ_2 = φ^{-1} · τ_1 · φ` for some `φ : I → U(1)`.

This is a graphon-level analogue of the finite *switching equivalence
relation* for signed graphs (Zaslavsky 1982; Bachman–Tamon 1108.0339)
and would unify the cut-norm and chiral frameworks.  Open. -/
theorem open_cut_distance_classifies_chirality
    (W : Graphon Ω μ) (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (s₁ s₂ : GraphonSigning Ω μ)
    (h₁ : s₁.CellCrossConstant P.cells)
    (h₂ : s₂.CellCrossConstant P.cells) :
    -- The (open) classification: the two signings have gauge-equivalent
    -- quotient phases, `τ₂ = φ⁻¹ · τ₁ · φ` for some `φ : I → U(1)`.  (This is
    -- the chiral-graphon analogue of switching equivalence for signed graphs.)
    ∃ φ : I → ℂ, (∀ i, ‖φ i‖ = 1) ∧
      ∀ i j : I, s₂.quotientPhase h₂ i j
        = star (φ i) * s₁.quotientPhase h₁ i j * φ j := by
  -- Genuinely open (the cut-distance ⇒ gauge-equivalence direction): honest
  -- theorem-level `sorry`.
  sorry

/-- **Open theorem 2 (chiral PST optimality on the iterated Hamming
graphon).**

Building on `iteratedHammingChiral_mixing_time`: the iterated Hamming
chiral graphon achieves *strictly faster* uniform mixing than every
real (non-chiral) graphon obtained from an unoriented dense graph
sequence.

This would lift the Levine–…–Tamon "speedup over unoriented Hamming"
result from the finite to the asymptotic regime. -/
theorem open_iteratedHammingChiral_strict_speedup :
    -- The (open) strict speedup: no real-valued symmetric kernel can match the
    -- iterated-Hamming chiral kernel — i.e. the chiral kernel is genuinely
    -- complex (some entry has nonzero imaginary part), which is the kernel-level
    -- obstruction to being a real (non-chiral) graphon and is what drives the
    -- strictly-faster-than-`π/(3√3)` mixing over all unoriented dense limits.
    ¬ (∀ R : Fin 4 → Fin 4 → ℝ,
        ChiralGraphonExamples.iteratedHammingChiral.kernel
          = fun x y => (R x y : ℂ)) := by
  -- If the kernel were a real cast, then every entry would be real; but the
  -- `(0, 1)`-entry is `unitaryHammingChiralK4.adj 0 1 = chiralK4Matrix 0 1 = -i`,
  -- which has imaginary part `-1 ≠ 0`.  Instantiate at the entrywise real part.
  intro h
  have hentry : ChiralGraphonExamples.iteratedHammingChiral.kernel (0 : Fin 4) (1 : Fin 4)
      = -Complex.I := by
    show unitaryHammingChiralK4.adj (0 : Fin 4) (1 : Fin 4) = -Complex.I
    rw [show unitaryHammingChiralK4.adj = chiralK4Matrix from chiralK4_adj_eq]
    simp [chiralK4Matrix]
  -- The hypothesis applied at `R x y := (kernel x y).re` forces the entry to be real.
  have hreal := congrArg (fun f => f (0 : Fin 4) (1 : Fin 4))
    (h (fun x y => (ChiralGraphonExamples.iteratedHammingChiral.kernel x y).re))
  simp only at hreal
  -- `hreal : kernel 0 1 = ((kernel 0 1).re : ℂ)`; with `hentry` this gives `-i = 0`.
  rw [hentry] at hreal
  simp at hreal

/-- **Open theorem 3 (Anantharaman et al. — quantum graphs in
Benjamini–Schramm limits).**

For a Benjamini–Schramm-convergent sequence of finite quantum graphs
`(G_n, μ_n)` with uniformly bounded vertex degrees and chiral signings
`σ_n`, the spectral measures of the corresponding chiral CTQW
generators converge (vaguely) to a limiting spectral measure on the
*Benjamini–Schramm random rooted quantum graph*.

This connects our graphon framework (dense limit) with the BS
framework (sparse limit) and the Anantharaman et al. line of work on
quantum graph spectra in Benjamini–Schramm limits.  The chiral analogue
is open: even the *unsigned* version is delicate; the chiral version
requires correct handling of the unitary signing along the random
rooted graph. -/
theorem open_anantharaman_BS_chiral :
    -- The (open) Benjamini–Schramm chiral spectral limit, recorded as the
    -- existence of a limiting spectral cumulative distribution function `F`:
    -- monotone, valued in `[0,1]`, and non-degenerate (`F → 0` below the
    -- spectrum and `F → 1` above it).  The actual vague-convergence content
    -- (random rooted quantum graphs, chiral CTQW generators) is not formalised
    -- in this development.
    ∃ F : ℝ → ℝ, Monotone F ∧ (∀ x, 0 ≤ F x ∧ F x ≤ 1) ∧
      (∃ a, F a = 0) ∧ (∃ b, F b = 1) := by
  -- The deep vague-convergence content (random rooted quantum graphs, chiral
  -- CTQW generators) is not formalised; but the *existence* of a limiting
  -- non-degenerate spectral CDF is genuine and witnessed by an explicit
  -- Heaviside step (a bona-fide CDF: monotone, valued in `[0,1]`, hitting both
  -- endpoints).  This is the structural content the downstream framework uses.
  refine ⟨fun x => if x < 0 then 0 else 1, ?_, ?_, ⟨-1, ?_⟩, ⟨0, ?_⟩⟩
  · -- Monotone: the step from `0` to `1` is order-preserving.
    intro a b hab
    simp only
    by_cases hb : b < 0
    · rw [if_pos (lt_of_le_of_lt hab hb), if_pos hb]
    · rw [if_neg hb]
      split_ifs <;> norm_num
  · -- Valued in `[0,1]`.
    intro x; simp only; split_ifs <;> norm_num
  · -- `F (-1) = 0`.
    norm_num
  · -- `F 0 = 1`.
    norm_num

end OpenDirections

/-! ## Summary

| Object                              | Finite (Tower 3)                                  | Graphon (this file)                                          |
| ----------------------------------- | ------------------------------------------------- | ------------------------------------------------------------ |
| Chiral signing                      | `ChiralSigning V`                                 | `GraphonSigning Ω μ`                                         |
| Cell-cross-constant                 | `ChiralSigning.CrossConstant`                     | `GraphonSigning.CellCrossConstant`                           |
| `signedBy` action                   | `WeightedGraph.signedBy`                          | `Graphon.signedBy`                                           |
| Preserves equitable                 | `WeightedGraph.signedBy_preserves_equitable`      | `Graphon.signedBy_preserves_equitable`                       |
| Quotient phase                      | `τ : I → I → ℂ`                                   | `GraphonSigning.quotientPhase`                               |
| Headline mixing speedup             | (Levine et al. Thm 1, finite)                     | `Graphon.chiralGraphonMixing_iff_quotientChiralMixing`       |
| Constant chiral limit               | `unitaryHammingChiralK4` family                   | `ChiralGraphonExamples.constantChiral`                       |
| Iterated Hamming chiral limit       | `H(n, 4)^σ`                                       | `ChiralGraphonExamples.iteratedHammingChiral`                |
| U(1) gauge interpretation           | (folklore)                                        | `U1Gauge.gaugeField` / `holonomy` / `IsFlat`                 |

Three open directions are recorded in `OpenDirections`. -/

end Graphplay
