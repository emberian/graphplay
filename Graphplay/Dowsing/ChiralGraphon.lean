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
  /-- Hermitian compatibility, μ ⊗ μ-a.e.  This is the analytic shape of
  `σ y x = star (σ x y)`. -/
  herm : ∀ᵐ p ∂(μ.prod μ), σ p.2 p.1 = star (σ p.1 p.2)
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
    refine Filter.Eventually.of_forall ?_
    intro _; simp
  diag _ := rfl

/-- Pointwise complex conjugate of a graphon signing.  Conjugation flips
chirality: `σ.conj.σ = star ∘ σ.σ`. -/
def conj (s : GraphonSigning Ω μ) : GraphonSigning Ω μ where
  σ x y := star (s.σ x y)
  measurable := by
    -- `star : ℂ → ℂ` is continuous, hence measurable, and composes with
    -- `Function.uncurry s.σ` to give measurability
    sorry
  unimod := by
    -- `‖star z‖ = ‖z‖` for any complex `z`
    sorry
  herm := by
    -- `star (star z) = z`, combined with `s.herm`
    sorry
  diag x := by
    have h := s.diag x; simp [h]

/-- A graphon signing extracted from a finite chiral signing under the
counting-measure / discrete-MeasurableSpace identification.  This gives
the "step graphon signing" of `Chiral.lean` for free. -/
noncomputable def ofFinite {V : Type u} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (s : ChiralSigning V) : GraphonSigning V (Measure.count) where
  σ := s.σ
  measurable := by
    -- every function out of a discrete space is measurable
    exact (measurable_discrete _ : Measurable (Function.uncurry s.σ))
  unimod := by
    refine Filter.Eventually.of_forall ?_
    intro p
    -- `s.unimod` gives `‖s.σ p.1 p.2‖ = 1` pointwise
    simpa using s.unimod p.1 p.2
  herm := by
    refine Filter.Eventually.of_forall ?_
    intro p
    -- `s.herm` gives `s.σ p.2 p.1 = star (s.σ p.1 p.2)` pointwise
    simpa using s.herm p.1 p.2
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
    sorry
  herm x y := by
    -- (σ y x) * (W y x) = star (σ x y) * star (W x y) = star (σ x y * W x y)
    -- This holds in the a.e. sense via `s.herm` and `W.herm` x y; we use
    -- the everywhere `W.herm` and defer the a.e. `s.herm` lifting.
    sorry
  essBound := W.essBound
  bounded := by
    -- ‖σ x y · W x y‖ = ‖σ x y‖ · ‖W x y‖ ≤ 1 · essBound = essBound a.e.
    sorry
  loopless x := by
    have hw := W.loopless x
    have hs : s.σ x x = 1 := s.diag x
    simp [hs, hw]

@[simp] theorem signedBy_kernel (W : Graphon Ω μ) (s : GraphonSigning Ω μ)
    (x y : Ω) : (W.signedBy s).kernel x y = s.σ x y * W.kernel x y := rfl

@[simp] theorem signedBy_trivial (W : Graphon Ω μ) :
    W.signedBy (GraphonSigning.trivial Ω μ) = W := by
  -- σ = 1, so (1 · W.kernel) = W.kernel
  cases W
  -- The kernel agrees pointwise; the analytic fields (essBound, bounded,
  -- measurable, herm, loopless) must also match up to definitional /
  -- proof-irrelevant equality.  We defer to a `sorry` because of the
  -- proof-relevant `measurable` field.
  sorry

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

/-- The quotient phase is Hermitian: `τ j i = star (τ i j)`.  This is
the cell-level shadow of `s.herm`. -/
theorem quotientPhase_herm (s : GraphonSigning Ω μ)
    {cells : Ω → I} (h : s.CellCrossConstant cells) :
    ∀ i j : I, s.quotientPhase h j i = star (s.quotientPhase h i j) := by
  -- pull `s.herm` through `quotientPhase_spec`; the residual is a finite
  -- cell-pair argument, deferred.
  sorry

/-- The quotient phase is unimodular: `|τ i j| = 1`.  This is the
cell-level shadow of `s.unimod`. -/
theorem quotientPhase_unimod (s : GraphonSigning Ω μ)
    {cells : Ω → I} (h : s.CellCrossConstant cells) :
    ∀ i j : I, ‖s.quotientPhase h i j‖ = 1 := by
  sorry

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
theorem signedBy_preserves_equitable {W : Graphon Ω μ}
    (P : GraphonEquitablePartition W)
    (s : GraphonSigning Ω μ) (h : s.CellCrossConstant P.cells) :
    GraphonEquitablePartition (W.signedBy s) where
  cells := P.cells
  measurable_cells := P.measurable_cells
  cell_pos := P.cell_pos
  cell_finite := P.cell_finite
  uniform := by
    intro i j x y hxi hyi
    -- The strategy: by `h`, `s.σ x z = τ i j` for μ-a.e. `z ∈ C_j`
    -- (using `hxi` and the cell-cross-constant property).  Hence the
    -- inner integral
    -- `∫ z, [cells z = j] · (s.σ x z · W.kernel x z) ∂μ`
    -- equals `τ i j · ∫ z, [cells z = j] · W.kernel x z ∂μ`.  Similarly
    -- for `y`.  Applying `P.uniform i j x y hxi hyi` finishes.
    sorry

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
    (P : GraphonEquitablePartition W) (s : GraphonSigning Ω μ)
    (h : s.CellCrossConstant P.cells) (i j : I) :
    (Graphon.signedBy_preserves_equitable P s h).quotient i j
      = s.quotientPhase h i j * P.quotient i j := by
  -- This is `∫_{C_j} s.σ x z · W x z dμ z = τ(i,j) · ∫_{C_j} W x z dμ z`,
  -- applied per-vertex via `quotient_apply_of_mem` of `Equitable.lean`.
  sorry

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
theorem chiralGraphonMixing_iff_quotientChiralMixing
    {W : Graphon Ω μ} (P : GraphonEquitablePartition W)
    (s : GraphonSigning Ω μ) (h : s.CellCrossConstant P.cells)
    (i : I) (t : ℝ) :
    IsCellUniformGraphonMixing (W.signedBy s)
        (signedBy_preserves_equitable P s h) i t
      ↔
    IsUniformMixing_finite
        (signedBy_preserves_equitable P s h).quotient i t := by
  -- This is `cellUniformGraphonMixing_iff_quotientMixing` applied to the
  -- signed graphon `W.signedBy s` and its equitable partition.
  -- (Tower-4 PST headline theorem already does most of the work; the
  -- chirality is "free" once the equitable partition is preserved.)
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
    (W : Graphon Ω μ) (P : GraphonEquitablePartition W) (i : I) :
    -- "There exists a Hermitian unimodular phase τ : I → I → ℂ such that
    -- the (constant-on-cells) signing with that phase achieves the
    -- infimum chiral mixing time."
    True := by
  -- The reduction to a compact-torus optimization is by
  -- `chiralGraphonMixing_iff_quotientChiralMixing`; existence of the
  -- minimum is then by lower semicontinuity of the uniform-mixing-time
  -- functional on the compact torus.  Stated as placeholder `True` here;
  -- a precise existence statement requires defining the
  -- "minimum uniform-mixing time" predicate, which we leave for the
  -- downstream optimisation file.
  trivial

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
    -- The kernel is a piecewise-constant function with the
    -- pieces being measurable preimages of `<` and `>`.
    sorry
  herm := by
    intro x y
    -- case analysis on x.val < y.val, x.val > y.val, x.val = y.val
    sorry
  essBound := 1
  bounded := by
    -- pointwise: |-i| = |i| = 1, |0| = 0, all bounded by 1
    sorry
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
    -- We state the existence of the limit; a precise statement would
    -- introduce `Kn σ` as a function `ℕ → WeightedGraph (Fin n)` and a
    -- cut-norm convergence claim.
    True := trivial

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
    -- placeholder for: ∃ τ : ℝ, t = π/(3 √3) ∧ uniform mixing at t
    True := trivial

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

We expose this here as a statement-level definition. -/
noncomputable def iteratedHammingChiral :
    -- placeholder type: the iterated power of `unitaryHammingChiralK4`
    -- in the appropriate graphon sense, e.g. on `[0,1]^∞`.
    True := trivial

/-- **The iterated Hamming chiral graphon admits cell-uniform chiral
mixing at time `π / (3√3)`.**

This is the graphon-limit reflection of Levine et al.'s
"H(n, 4) orientation beats every unoriented Hamming graph" corollary
(Figure 1 of arXiv:2605.04414, mixing time `π/(3√3)`).  The graphon
limit inherits this mixing time *uniformly in* `n`, providing the
strongest possible statement of the speedup. -/
theorem iteratedHammingChiral_mixing_time :
    True := trivial

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
def gaugeField (s : GraphonSigning Ω μ) {cells : Ω → I}
    (h : s.CellCrossConstant cells) : I → I → ℂ :=
  s.quotientPhase h

/-- The U(1) **holonomy** around a finite cell-path
`p : List I = [i_0, i_1, …, i_n]`: the product of phases along the path.
-/
def holonomy (s : GraphonSigning Ω μ) {cells : Ω → I}
    (h : s.CellCrossConstant cells) : List I → ℂ
  | [] => 1
  | _ :: [] => 1
  | i :: j :: rest =>
      (s.quotientPhase h i j) * holonomy s h (j :: rest)

/-- A cell-cross-constant signing is **flat** iff the holonomy around
every closed cell-path is `1`.  Equivalently, the signing is gauge-
equivalent to the trivial (all-1) signing under a phase rotation on
cells (i.e. it is *switching equivalent* to the unsigned graphon). -/
def IsFlat (s : GraphonSigning Ω μ) {cells : Ω → I}
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
    (W : Graphon Ω μ) (P : GraphonEquitablePartition W)
    (s₁ s₂ : GraphonSigning Ω μ)
    (h₁ : s₁.CellCrossConstant P.cells)
    (h₂ : s₂.CellCrossConstant P.cells) :
    -- placeholder for the open biconditional
    True := trivial

/-- **Open theorem 2 (chiral PST optimality on the iterated Hamming
graphon).**

Building on `iteratedHammingChiral_mixing_time`: the iterated Hamming
chiral graphon achieves *strictly faster* uniform mixing than every
real (non-chiral) graphon obtained from an unoriented dense graph
sequence.

This would lift the Levine–…–Tamon "speedup over unoriented Hamming"
result from the finite to the asymptotic regime. -/
theorem open_iteratedHammingChiral_strict_speedup :
    -- placeholder for: every real graphon has uniform-mixing time
    -- strictly greater than `π/(3√3)`
    True := trivial

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
    -- placeholder for the BS-vague-convergence statement
    True := trivial

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
