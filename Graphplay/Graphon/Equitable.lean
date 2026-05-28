/-
# Graphon/Equitable.lean — the headline definition

This file contains what we believe is the **genuinely unpublished** core of
Graphplay: a definition of **equitable partition** for a graphon `W` on a
measure space `(Ω, μ)`, together with the statement of a **lifting theorem**
that identifies the restriction of the graphon transition operator `W.op` to
the "cell-uniform" subspace of `L²(μ)` with a finite Hermitian matrix — the
**quotient adjacency** induced by the partition.

This is the graphon-level analogue of the classical finite equitable-partition
theorem (Godsil–Royle, *Algebraic Graph Theory*, §9.3) and of the ODE
equitable-partition theorem for continuous dynamical systems
(Gerlach–von der Gönna, arXiv:2110.13686, Thm. 4.4).  We have not been able to
locate this theorem in the graphon literature; the closest ancestors are:

* the BCLSV graphon framework (cut-norm convergence, but no equitable
  partitions of the kernel), arXiv:1003.5588;
* the BCLSV stepping operator (the *uniform-partition* projection),
  arXiv:1003.5588 §3;
* the Bachman–Tamon analysis of perfect state transfer for finite graphs with
  an equitable partition (arXiv:1108.0339);
* the Gao–Caines graphon LQR control framework (arXiv:2004.00677), which uses
  graphon operators but does not invoke equitable partitions.

The headline operator-level lift theorem is stated as
`Graphon.cellUniformSubspaceInvariant` and its corollary
`Graphon.opRestrict_eq_quotient` below.  The cell-uniform subspace
`Graphon.cellUniformSubspace` is the closed subspace of `L²(μ; ℂ)` of functions
that are constant on each cell.  The quotient adjacency
`GraphonEquitablePartition.quotient` is a Hermitian matrix on the (finite)
index type of cells; its operator on `L²(I, counting)` is **unitarily
equivalent** to the restriction of `W.op` to the cell-uniform subspace.

Notation:

* `Ω` ambient measure space, `μ` the measure;
* `I` finite index type for cells;
* `W : Graphon Ω μ` the kernel;
* `P : GraphonEquitablePartition W` an equitable partition;
* `C_i := P.cells ⁻¹' {i}` the cell of `i ∈ I`;
* `μ_i := μ (C_i)` the cell mass.

We always assume `0 < μ_i < ∞` for every `i`, since otherwise the cell is
degenerate (we restate this as the hypothesis `cells_finite_pos`).
-/

import Graphplay.Graphon

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory

universe u v

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The headline definition.**  A **graphon equitable partition** of a
graphon `W` on `(Ω, μ)` is a finite measurable partition `cells : Ω → I` of
`Ω` together with the **uniform-row-sum** property: for any pair of cells
`i, j ∈ I` and any two `x, y` in the same cell `i`, the *cell-restricted
column sums* are equal:
$$ \int_{C_j} W(x, z)\, d\mu(z) = \int_{C_j} W(y, z)\, d\mu(z). $$

This is the graphon analogue of the finite-graph notion (each vertex in cell
`i` has the same number of neighbours in cell `j`).

Auxiliary fields: positive finite cell mass, so that we can normalise
indicator vectors.

Reference for the closest classical statement: Godsil–Royle, *Algebraic Graph
Theory*, §9.3 (finite graphs).  The graphon-level version appears to be new. -/
structure _root_.Graphplay.GraphonEquitablePartition
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {I : Type v} [Fintype I] [DecidableEq I]
    (W : Graphon Ω μ) where
  /-- The cell-membership function `Ω → I`. -/
  cells : Ω → I
  /-- The cell map is measurable. -/
  measurable_cells : Measurable cells
  /-- Each cell has finite positive measure. -/
  cell_pos : ∀ i : I, 0 < μ (cells ⁻¹' {i})
  cell_finite : ∀ i : I, μ (cells ⁻¹' {i}) < ∞
  /-- **Uniform property** — for any two points `x, y` in the same cell, and
  any other cell `j`, the kernel restricted-and-integrated against the cell
  `j` is the same.

  This is the analytic shape of the equitable-partition condition. -/
  uniform : ∀ (i j : I) (x y : Ω),
    cells x = i → cells y = i →
    ∫ z, (if cells z = j then W.kernel x z else 0) ∂μ
      = ∫ z, (if cells z = j then W.kernel y z else 0) ∂μ

end Graphon

namespace GraphonEquitablePartition

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {W : Graphon Ω μ}

/-- The cell `C_i := cells ⁻¹' {i}`. -/
def cell (P : GraphonEquitablePartition W) (i : I) : Set Ω :=
  P.cells ⁻¹' {i}

/-- The mass of the cell `C_i`, as an `ℝ`. -/
noncomputable def cellMass (P : GraphonEquitablePartition W) (i : I) : ℝ :=
  (μ (P.cell i)).toReal

theorem cellMass_pos (P : GraphonEquitablePartition W) (i : I) :
    0 < P.cellMass i := by
  simp [cellMass]
  exact ENNReal.toReal_pos (ne_of_gt (P.cell_pos i)) (ne_of_lt (P.cell_finite i))

/-- The cell is measurable. -/
theorem measurableSet_cell (P : GraphonEquitablePartition W) (i : I) :
    MeasurableSet (P.cell i) :=
  P.measurable_cells (measurableSet_singleton i)

/-! ### The quotient adjacency matrix

The **quotient adjacency** `P.quotient` is the `I × I` Hermitian complex matrix
whose `(i, j)` entry is
$$ B_{i j} \;=\; \frac{1}{\mu(C_i)} \int_{C_i \times C_j} W(x, z)\, d(\mu \otimes \mu).$$
Equivalently, for any fixed `x ∈ C_i`,
$$ B_{i j} = \int_{C_j} W(x, z)\, d\mu(z), $$
by the uniform property.  This is the **per-vertex** flux from cell `i` to
cell `j`.

We define it as an integral over `Ω`, picking out the cell-`j` part using a
characteristic function, and dividing by `μ(C_i)`.  The well-definedness
(independence on the choice of `x ∈ C_i`) is exactly `P.uniform`. -/

/-- The quotient adjacency matrix `B : I × I → ℂ`.  Defined as a "per-vertex"
cell-`j` flux from an arbitrary `x ∈ C_i`; the result is independent of the
choice of `x` by `P.uniform`. -/
noncomputable def quotient (P : GraphonEquitablePartition W) : Matrix I I ℂ :=
  fun i j =>
    -- pick a representative of `C_i`; we use the cellMass-normalized integral
    -- to make the choice independent of the representative
    (P.cellMass i)⁻¹ • ∫ x in P.cell i,
      ∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ ∂μ

/-- The quotient adjacency, evaluated cell-by-cell, equals the per-vertex flux
out of any representative `x ∈ C_i`. -/
theorem quotient_apply_of_mem (P : GraphonEquitablePartition W) (i j : I)
    {x : Ω} (hx : x ∈ P.cell i) :
    P.quotient i j = ∫ z, (if P.cells z = j then W.kernel x z else 0) ∂μ := by
  -- by `P.uniform`, the inner integral is constant on `C_i`, so dividing by
  -- `P.cellMass i` gives that constant
  sorry

/-- The quotient adjacency is Hermitian.  Translates Hermitianness of the
graphon kernel: `B_{j i} = star B_{i j}`. -/
theorem quotient_isHermitian (P : GraphonEquitablePartition W) :
    P.quotient.IsHermitian := by
  -- pointwise: `B_{j i} = (1/μ_j) ∫_{C_j} ∫ 1_{C_i}(z) W(x,z) dz dx`
  --          = star ((1/μ_i) ∫_{C_i} ∫ 1_{C_j}(z) W(y,z) dz dy)
  -- by Fubini + W.herm
  sorry

/-- The quotient adjacency has zero diagonal **on average**: the per-vertex
self-flux is the integral of the loopless kernel `W x z` for `z ∈ C_i`, which
need not vanish in general because the cell `C_i` is not a single point.

We therefore do **not** assert `P.quotient i i = 0`.  It is the
*off-diagonal* part of the quotient that captures cell-to-cell transitions. -/
example : True := trivial

end GraphonEquitablePartition

namespace Graphon

/-! ### The cell-uniform subspace

The subspace of `L²(μ; ℂ)` of functions that are (μ-a.e.) constant on each
cell `C_i` is naturally isometric to `ℂ^I` with the weighted inner product
`⟨v, w⟩_w := Σ_i μ(C_i) · star (v i) · w i` — equivalently, isometric to
`L²(I, μ_count)` where the counting measure is replaced by the **cell-mass
measure** `i ↦ μ(C_i)`.

We **state** this subspace and the isometry to the finite Hilbert space; the
actual construction touches Mathlib's `Lp` quotient subtleties and we defer
the details to `sorry`. -/

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {W : Graphon Ω μ}

/-- The **cell-uniform subspace** of `L²(μ; ℂ)` for an equitable partition
`P`: the closed subspace of functions that are a.e. constant on each cell. -/
noncomputable def cellUniformSubspace (P : GraphonEquitablePartition W) :
    Submodule ℂ (Lp ℂ 2 μ) := by
  -- the closed subspace spanned by the indicator functions `1_{C_i}`
  classical
  exact sorry

/-- The cell-uniform subspace is closed in `L²(μ; ℂ)`. -/
theorem cellUniformSubspace_isClosed (P : GraphonEquitablePartition W) :
    IsClosed (P.cellUniformSubspace : Set (Lp ℂ 2 μ)) := by
  sorry

/-- The **normalised cell indicator** `e_i ∈ L²(μ; ℂ)`:
`e_i = (1/√μ(C_i)) · 1_{C_i}`.  This is a unit vector in `L²(μ; ℂ)` and
together with the other `e_j` (`j ∈ I`) forms an orthonormal basis of the
cell-uniform subspace. -/
noncomputable def cellIndicator (P : GraphonEquitablePartition W) (i : I) :
    Lp ℂ 2 μ := by
  classical
  exact sorry

/-- The cell indicators are orthonormal: `⟨e_i, e_j⟩ = [i = j]`. -/
theorem cellIndicator_orthonormal (P : GraphonEquitablePartition W) :
    Orthonormal ℂ (fun i : I => P.cellIndicator i) := by
  sorry

/-- The **cell-uniform isometry**: the unitary map
`L²(I, counting; ℂ) → cellUniformSubspace ⊂ L²(μ; ℂ)`
sending the `i`-th basis vector to the normalised cell indicator `e_i`.

In Mathlib terms this is a `LinearIsometry` between `EuclideanSpace ℂ I` and
the closed subspace `cellUniformSubspace`. -/
noncomputable def cellUniformIsometry (P : GraphonEquitablePartition W) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] (Lp ℂ 2 μ) := by
  classical
  exact sorry

/-- The image of the cell-uniform isometry is exactly the cell-uniform
subspace. -/
theorem range_cellUniformIsometry (P : GraphonEquitablePartition W) :
    (LinearMap.range (P.cellUniformIsometry.toLinearMap)) =
      P.cellUniformSubspace := by
  sorry

/-! ### **THE HEADLINE LIFTING THEOREM**

The cell-uniform subspace is **invariant** under the graphon operator `W.op`,
and the restriction of `W.op` to that subspace, **transported across the
cell-uniform isometry**, equals the finite matrix `P.quotient` acting on
`EuclideanSpace ℂ I`.

Statement form, in pseudo-LaTeX:
$$
  \Big(\;W.\mathrm{op}\big|_{\mathrm{cellUniform}}\;\Big)
  \;\;\cong\;\;
  P.\mathrm{quotient}\ \text{as an operator on}\ \mathbb{C}^I.
$$
-/

/-- **Headline lifting theorem (invariance).**  The cell-uniform subspace is
invariant under the graphon operator `W.op`:
$$ W.\mathrm{op}\big( \mathrm{cellUniformSubspace} \big) \subseteq
   \mathrm{cellUniformSubspace}. $$ -/
theorem cellUniformSubspaceInvariant (P : GraphonEquitablePartition W) :
    ∀ f ∈ P.cellUniformSubspace, W.op f ∈ P.cellUniformSubspace := by
  -- "for x in cell i, (W.op f)(x) = ∫ W(x, z) · f(z) dz; if f is constant
  -- c_j on each cell C_j, this is Σ_j c_j · ∫_{C_j} W(x, z) dz, which by
  -- `P.uniform` depends only on the cell i of x — hence (W.op f) is itself
  -- constant on cells."
  sorry

/-- **Headline lifting theorem (operator identification).**
Transporting the restriction of `W.op` to `cellUniformSubspace` across the
cell-uniform isometry yields the matrix-operator induced by `P.quotient`
acting on `EuclideanSpace ℂ I`:
$$ \big(W.\mathrm{op}\big|_{\mathrm{cellUniform}}\big)^{\sharp}
    = P.\mathrm{quotient}\ \text{(as a matrix on}\ \mathbb{C}^I\text{)}. $$

Here `(·)^{\sharp}` is the unitary conjugation by `cellUniformIsometry`, and
the right-hand side is `Matrix.toEuclideanLin P.quotient`.

This is the central theorem of Tower 4.  Its proof reduces to:

1. Compute `W.op (cellIndicator i)` for each `i`.
2. By `P.uniform`, this is `Σ_j (P.quotient i j) · cellIndicator j / √μ(C_j) · √μ(C_i)`
   — i.e. the quotient matrix entries weighted by cell masses.
3. The orthonormal-basis change to `cellIndicator` corrects the weights so the
   resulting matrix is exactly `P.quotient`.

Statement only; proof deferred. -/
theorem op_restrict_eq_quotient (P : GraphonEquitablePartition W) :
    ∀ (v : EuclideanSpace ℂ I),
      W.op (P.cellUniformIsometry v) =
        P.cellUniformIsometry (Matrix.toEuclideanLin P.quotient v) := by
  -- this is the operator identity `W.op|_{cellUniform} = P.quotient` after
  -- the unitary isomorphism `cellUniformIsometry`
  sorry

/-- **Spectral corollary.**  The spectrum of the matrix `P.quotient` is
contained in the spectrum of `W.op`.  Equivalently, every eigenvalue of the
quotient matrix is an eigenvalue of the (bounded self-adjoint) graphon
operator.

This is the graphon-level version of the classical "quotient eigenvalues are
graph eigenvalues" fact. -/
theorem spectrum_quotient_subset_spectrum_op (P : GraphonEquitablePartition W) :
    spectrum ℂ (Matrix.toEuclideanLin P.quotient) ⊆ spectrum ℂ W.op := by
  -- follows from `op_restrict_eq_quotient` and invariance of spectra under
  -- restriction to invariant subspaces (for self-adjoint operators, the
  -- inclusion is automatic via the unitary equivalence)
  sorry

/-- **Evolution corollary.**  The graphon CTQW restricted to the cell-uniform
subspace is unitarily equivalent to the finite CTQW driven by `P.quotient`.

Concretely:
$$ W.\mathrm{evolve}(t)\big|_{\mathrm{cellUniform}}
    \;=\; \exp\!\big(-i\,t \,\cdot\, P.\mathrm{quotient}\big)
    \text{ as an operator on}\ \mathbb{C}^I, $$
under `cellUniformIsometry`. -/
theorem evolve_restrict_eq_finite_evolve (P : GraphonEquitablePartition W)
    (t : ℝ) :
    ∀ (v : EuclideanSpace ℂ I),
      W.evolve t (P.cellUniformIsometry v) =
        P.cellUniformIsometry
          (NormedSpace.exp ℂ
             (((-Complex.I) * (t : ℂ)) • Matrix.toEuclideanLin P.quotient) v) := by
  -- exp commutes with restriction to an invariant subspace for a bounded
  -- self-adjoint operator
  sorry

end Graphon

end Graphplay
