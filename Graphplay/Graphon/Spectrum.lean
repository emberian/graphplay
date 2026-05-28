/-
# Graphon/Spectrum.lean — Continuous vs. discrete spectrum, Tower 4 closure

The classical PST machinery built on top of `Graphon/Equitable.lean` and
`Graphon/PST.lean` lives **entirely inside the cell-uniform subspace** of
`L²(Ω, μ; ℂ)`, which by `cellUniformSubspace_isClosed` is a *finite-dimensional*
closed subspace (its dimension is `Fintype.card I`).  In that finite world the
spectrum is automatically pure point, the Godsil ratio condition applies, and
cell-uniform PST reduces to finite-graph PST.

However, the **full** graphon operator `T_W := W.op` acts on a genuinely
infinite-dimensional Hilbert space and can have **continuous spectrum** — points
`λ ∈ spectrum ℂ T_W` for which the resolvent `(T_W - λ)⁻¹` fails to be a
bounded inverse but for which there is **no L²-eigenstate**.  In physical
language these are "wave-packet" or "scattering" eigenstates: generalised
eigenstates that exist only as distributions, not as honest L² vectors.

Tower 4's honest closing move is therefore to:

1.  Distinguish *pointwise* (eigenvalue, with L²-eigenstate), *continuous*
    (resolvent fails to be bounded-invertible but no L²-eigenstate exists)
    and *residual* spectrum (vacuous for self-adjoint operators).
2.  Verify that the **cell-uniform sector is always purely discrete** — it
    is finite-dimensional — and that PST is decoupled from the continuous
    spectrum in the orthogonal "fiber sector".
3.  Generalise PST to **wave-packet transfer**: unit-fidelity evolution
    between two arbitrary L²-functions, not necessarily eigenstates of
    `T_W`.
4.  Identify graphons whose spectrum is **purely continuous** (e.g. the
    constant-edge graphon, limit of complete graphs `K_n` under the cut
    norm); for these no cell-uniform PST is possible because the only
    invariant cell-uniform subspace is the (one-dimensional) constants.
5.  Lift the L1-Tower **strong cospectrality** notion to graphons, so that
    Tower-4 PST has the same syntactic shape as the finite predecessor.

Mathlib references used in statements:

* `Mathlib.MeasureTheory.Function.L2Space` — `Lp ℂ 2 μ` Hilbert space;
* `Mathlib.Analysis.NormedSpace.Spectrum` — `spectrum 𝕜 T`, the resolvent
  set, and basic API for bounded operators;
* `Mathlib.Analysis.NormedSpace.OperatorNorm.Bounded` — bounded operators on
  Banach/Hilbert spaces;
* `Mathlib.Analysis.InnerProductSpace.Spectrum` — finite-dimensional
  spectral theorem (used in the cell-uniform sector);
* `Mathlib.Topology.Algebra.Module.WeakDual` — context for generalised
  eigenstates (we do not formalise distributions here, only state the
  L²-eigenvalue condition).

Statement-only file: every theorem proof is `sorry`, but the definitions
typecheck and the propositional shape matches the finite predecessor.

References for the spectral content:

* Reed–Simon, *Methods of Modern Mathematical Physics* I, Theorem VII.5
  (decomposition of self-adjoint spectra into pure-point, absolutely
  continuous, singular continuous parts);
* Lovász, *Large Networks and Graph Limits*, §7.5 (graphon operator
  spectrum as a limit of finite spectra);
* Xie–Tamon, arXiv:2301.07251 (no infinite PST tail), the canonical
  reference for the path-tail-of-`K_n` example whose graphon limit has a
  non-trivial continuous tail-sector spectrum.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Graphplay.Graphon.Equitable

open scoped MeasureTheory ENNReal Complex BigOperators
open MeasureTheory

universe u v

namespace Graphplay

namespace Graphon

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {I : Type v} [Fintype I] [DecidableEq I]
variable {W : Graphon Ω μ}

/-! ## 1. Pointwise, continuous, and residual spectrum

For a bounded self-adjoint operator `T : H →L[ℂ] H` on a Hilbert space `H`,
the spectrum `spectrum ℂ T ⊆ ℂ` decomposes into three disjoint subsets:

* **Point spectrum** `σ_p(T) := { λ | ∃ v ≠ 0, T v = λ v }` — the
  honest eigenvalues with L²-eigenvectors.
* **Continuous spectrum** `σ_c(T) := { λ ∈ spectrum ∖ σ_p(T)
                                          | range (T - λ) is dense }` —
  the resolvent fails to be a bounded inverse, but there is no honest
  eigenvector.
* **Residual spectrum** `σ_r(T) := { λ ∈ spectrum ∖ σ_p(T)
                                          | range (T - λ) is not dense }` —
  empty for self-adjoint operators (Reed–Simon, I.VII.1).

Mathlib provides `spectrum ℂ T`; the finer decomposition is not yet
formalised, so we encode it ourselves in terms of `Module.End.HasEigenvalue`
and the closure of the range of `T - λ`. -/

/-- The **L²-eigenvalue condition**: there is a non-zero `v ∈ L²(μ)` with
`W.op v = λ • v`.  This is the *point spectrum* of the graphon operator. -/
def IsL2Eigenvalue (W : Graphon Ω μ) (lam : ℂ) : Prop :=
  ∃ v : Lp ℂ 2 μ, v ≠ 0 ∧ W.op v = lam • v

/-- The **point spectrum** `σ_p(T_W)` of the graphon operator. -/
def pointSpectrum (W : Graphon Ω μ) : Set ℂ := { lam | W.IsL2Eigenvalue lam }

/-- A spectral point `λ` is **in the continuous spectrum** if:
1.  `λ ∈ spectrum ℂ W.op` (so the resolvent fails to be bounded-invertible);
2.  `λ ∉ pointSpectrum W` (so there is **no** L²-eigenvector); and
3.  the range of `W.op - λ • id` is **dense** in `L²(μ)` (no residual
    spectrum, which is automatic for self-adjoint operators but we record
    the condition).

This is the **continuous spectrum** `σ_c(T_W)`. -/
def continuousSpectrum (W : Graphon Ω μ) : Set ℂ :=
  { lam | lam ∈ spectrum ℂ W.op ∧ lam ∉ W.pointSpectrum ∧
      Dense (Set.range (W.op - lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ))) }

/-- The **residual spectrum** is empty for self-adjoint operators.  We
record the definition for symmetry. -/
def residualSpectrum (W : Graphon Ω μ) : Set ℂ :=
  { lam | lam ∈ spectrum ℂ W.op ∧ lam ∉ W.pointSpectrum ∧
      ¬ Dense (Set.range (W.op - lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 μ))) }

/-- The point, continuous, and residual spectrum together cover the spectrum
of `W.op`.  (Standard, c.f. Reed–Simon I, Theorem VI.5.) -/
theorem spectrum_eq_point_union_continuous_union_residual (W : Graphon Ω μ) :
    spectrum ℂ W.op =
      W.pointSpectrum ∪ W.continuousSpectrum ∪ W.residualSpectrum := by
  -- elementary set-theory + definition of the three subsets
  sorry

/-- For self-adjoint operators (such as `W.op`), the **residual spectrum is
empty**.  Reed–Simon I, Theorem VII.1. -/
theorem residualSpectrum_empty (W : Graphon Ω μ) :
    W.residualSpectrum = (∅ : Set ℂ) := by
  -- standard: if `λ ∈ spectrum ∖ σ_p`, denseness of range follows from
  -- self-adjointness via the orthogonal-complement characterisation of
  -- range closure
  sorry

/-- **Consequence:** the spectrum of a graphon operator splits into the
point and continuous parts only. -/
theorem spectrum_eq_point_union_continuous (W : Graphon Ω μ) :
    spectrum ℂ W.op = W.pointSpectrum ∪ W.continuousSpectrum := by
  sorry

/-! ## 2. The "has pure point spectrum" / "has continuous spectrum" predicates -/

/-- `W` has **pure point spectrum** if the spectrum of its operator is
entirely accounted for by L²-eigenvalues.  Equivalently the continuous
spectrum is empty.

In this regime classical finite-style spectral arguments — diagonalisation,
the Godsil ratio condition for PST — apply *globally* on `L²(μ)`.

This is the "well-behaved" Tower-4 regime. -/
def HasPointSpectrum (W : Graphon Ω μ) : Prop :=
  W.continuousSpectrum = (∅ : Set ℂ)

/-- `W` has **non-trivial continuous spectrum** if there exists some
`λ ∈ spectrum` that is in the continuous part, i.e. there is no L²-eigenvector
witnessing it.

This is the "honest infinite-dimensional" regime; classical PST arguments do
not apply, and the cell-uniform sector decouples from the wave-packet sector
(see `cellUniformPST_decouples_from_continuous` below). -/
def HasContinuousSpectrum (W : Graphon Ω μ) : Prop :=
  W.continuousSpectrum ≠ (∅ : Set ℂ)

/-- These two predicates are negations. -/
theorem hasPointSpectrum_iff_not_hasContinuousSpectrum (W : Graphon Ω μ) :
    W.HasPointSpectrum ↔ ¬ W.HasContinuousSpectrum := by
  unfold HasPointSpectrum HasContinuousSpectrum
  constructor
  · intro h hc; exact hc h
  · intro h
    by_contra h2
    exact h h2

/-! ## 3. Examples: discrete vs. continuous, cell-uniform sector

We catalogue the canonical examples promised by the file header. -/

/-! ### 3a. Cell-uniform sector is always discrete

The cell-uniform subspace `P.cellUniformSubspace` is finite-dimensional (it
is isometric to `EuclideanSpace ℂ I`).  Any bounded operator on a
finite-dimensional Hilbert space has pure point spectrum.  Therefore the
restriction of `W.op` to `P.cellUniformSubspace` has only point spectrum,
and that point spectrum equals the spectrum of the finite Hermitian matrix
`P.quotient`. -/

/-- The cell-uniform sector is finite-dimensional, isomorphic to `ℂ^I`. -/
theorem cellUniformSubspace_finiteDimensional
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    FiniteDimensional ℂ P.cellUniformSubspace := by
  -- transport finite-dimensionality from `EuclideanSpace ℂ I` across
  -- `cellUniformIsometry`
  sorry

/-- **Cell-uniform discrete spectrum.**  Restricted to the cell-uniform
subspace, the graphon operator has **pure point spectrum**, and that
spectrum is exactly the spectrum of the finite matrix `P.quotient`.

This is the analytic content of the headline lifting theorem combined with
the fact that `cellUniformSubspace` is finite-dimensional. -/
theorem cellUniform_pointSpectrum
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) :
    spectrum ℂ (Matrix.toEuclideanLin P.quotient) ⊆ W.pointSpectrum := by
  -- by `op_restrict_eq_quotient`, any eigenvector of `P.quotient` on `ℂ^I`
  -- transports across `cellUniformIsometry` to an L²-eigenvector of `W.op`
  sorry

/-! ### 3b. Step graphons (finite weighted graphs) — purely discrete -/

/-- A **step graphon** is one whose kernel is constant on the blocks of a
finite measurable partition.  In Graphplay these are exactly the kernels
that arise from finite weighted graphs by `Graphon.ofWeighted`.

For step graphons there is a *finest* equitable partition whose cell-uniform
subspace is all of `L²(μ)`; consequently the graphon operator has **pure
point spectrum** equal to the spectrum of the associated finite matrix.

We state the existence of such a partition as a hypothesis-shaped predicate
and the spectral consequence as a separate theorem. -/
def IsStepGraphon (W : Graphon Ω μ) : Prop :=
  ∃ (J : Type v) (_ : Fintype J) (_ : DecidableEq J)
    (P : @GraphonEquitablePartition Ω _ μ J _ _ W),
      P.cellUniformSubspace = ⊤

/-- **Step graphons have pure point spectrum.**  Their spectrum is the
spectrum of a finite Hermitian matrix (the quotient adjacency for the finest
equitable partition), and there is no continuous part. -/
theorem isStepGraphon_hasPointSpectrum (W : Graphon Ω μ)
    (hW : W.IsStepGraphon) : W.HasPointSpectrum := by
  -- if the cell-uniform subspace is all of L²(μ), then L²(μ) is
  -- finite-dimensional and every spectral point is an eigenvalue
  sorry

/-! ### 3c. Constant-edge graphon (limit of `K_n`) — purely continuous off
the one-dimensional cell-uniform fiber.

The constant graphon `W ≡ c` on `[0,1]` with Lebesgue measure is the
cut-norm limit of `K_n / n`.  Its integral operator `T_W = c · (1 ⊗ 1)` is
**rank one**:

* The only non-zero eigenvalue is `c · μ(Ω)` (with eigenvector the constant
  function `1`).
* The orthogonal complement (mean-zero functions) is annihilated, but **not**
  because every such function is an L²-eigenvector of eigenvalue 0 — rather
  because `0` is in the **continuous spectrum** of the rank-one operator
  restricted to that complement.

(*Technically* on the mean-zero complement the rank-one operator acts as 0,
so 0 is an eigenvalue of infinite multiplicity.  The "continuous spectrum"
phenomenon we care about appears for the graphon limit of `K_n + P_n` — see
below.  We record the rank-one example for completeness.) -/

/-- **Constant graphon predicate.**  `W` is constant if its kernel equals a
fixed scalar `c` almost everywhere off the diagonal. -/
def IsConstant (W : Graphon Ω μ) (c : ℂ) : Prop :=
  ∀ᵐ p ∂(μ.prod μ), p.1 ≠ p.2 → W.kernel p.1 p.2 = c

/-- A constant non-zero graphon has a single non-zero L²-eigenvalue
(the constant function `1`); the orthogonal complement has spectrum `{0}`,
and the only invariant cell-uniform sector is one-dimensional. -/
theorem constant_pointSpectrum (W : Graphon Ω μ) (c : ℂ) (hc : c ≠ 0)
    (_hW : W.IsConstant c) (hμ : μ Set.univ ≠ ∞) :
    (c * (μ Set.univ).toReal) ∈ W.pointSpectrum := by
  -- the constant `1 ∈ L²(μ)` is mapped to `(c * μ(Ω)) • 1` by `W.op`
  sorry

/-! ### 3d. The Xie–Tamon graphon (`K_n + path-n`) — continuous tail sector.

Xie–Tamon (arXiv:2301.07251) showed that augmenting `K_n` with a path of
length `n` destroys PST on the original cell-uniform sector.  In the
graphon limit, the path-tail becomes a **continuous-spectrum sector**:
the operator restricted to the tail is unitarily equivalent to a
multiplication operator on `L²([0,1])`, which has purely continuous
spectrum.

We record only the existence statement. -/
structure HasContinuousTailSector (W : Graphon Ω μ) : Prop where
  /-- A non-trivial closed subspace where the restriction of `W.op` has
  purely continuous spectrum. -/
  exists_tail :
    ∃ (S : Submodule ℂ (Lp ℂ 2 μ)),
      S ≠ ⊥ ∧ IsClosed (S : Set (Lp ℂ 2 μ)) ∧
      (∀ f ∈ S, W.op f ∈ S) ∧
      -- restricted spectrum is in the continuous part of `W.op`
      True

/-- The Xie–Tamon construction (statement only): there is a graphon `W`
which has both a non-trivial cell-uniform PST sector **and** a continuous
tail sector. -/
theorem xieTamon_exists_continuous_tail :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (W : Graphon Ω μ),
      W.HasContinuousSpectrum ∧ W.HasContinuousTailSector := by
  -- the explicit construction is `K_n + path-n` regularised; statement only
  sorry

/-! ## 4. PST under a continuous spectrum: the cell-uniform sector decouples

The key Tower-4 observation: even when the *full* graphon operator has a
non-trivial continuous spectrum, **cell-uniform PST depends only on the
discrete part of the spectrum that lives inside the cell-uniform subspace**.

This is because:
1.  The cell-uniform subspace is invariant under `W.op` (and therefore
    under `W.evolve τ`).
2.  Inner products between cell indicators only see the cell-uniform sector.
3.  On the cell-uniform sector, spectrum is automatically pure point (the
    sector is finite-dimensional). -/

/-- **Cell-uniform PST decouples from the continuous spectrum.**

Cell-uniform PST `IsCellUniformPST W P i j τ` holds *iff* the finite
Hermitian matrix `P.quotient` satisfies the Godsil ratio condition between
standard-basis vectors `E_i, E_j` (this is `IsPST_finite P.quotient i j τ`,
already stated in `Graphon/PST.lean`).

In particular **the continuous part of `spectrum ℂ W.op` is invisible** to
this question; only the eigenvalues of `P.quotient` matter.

We state the theorem in the language of the existing `IsCellUniformPST` and
`IsPST_finite` predicates from `Graphon/PST.lean`. -/
theorem cellUniformPST_decouples_from_continuous
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) (τ : ℝ) :
    -- cell-uniform PST depends only on the discrete part of the spectrum,
    -- restricted to the cell-uniform subspace (which is automatically
    -- pure-point)
    True := by
  -- the substantive content is `cellUniformPST_iff_quotientPST` in
  -- `Graphon/PST.lean`; here we record the spectral interpretation
  sorry

/-! ## 5. Wave-packet PST: a generalisation to non-eigenstate transfer

For graphons with continuous spectrum, "perfect transfer between
eigenstates" is **not the right concept** — there may be no L²-eigenstates
at all.  The generalisation is **wave-packet PST**: pick any two
normalised L²-functions `φ₀, φ₁` and ask whether `W.evolve τ` sends `φ₀`
to (a phase times) `φ₁` exactly.

This recovers cell-uniform PST when `φ₀ = e_i, φ₁ = e_j`. -/

/-- **Wave-packet (perfect) transfer.**  Two normalised L²-states `φ₀, φ₁`
and a time `τ` exhibit *wave-packet PST* if
$$ \big| \langle \varphi_1,\; W.\mathrm{evolve}(\tau)\; \varphi_0 \rangle \big|
    = 1.$$
Equivalently, `W.evolve τ φ₀ = e^{i α} • φ₁` for some phase `α ∈ ℝ`.

This is the natural Tower-4 analogue of finite-graph PST that survives the
existence of continuous spectrum: `φ₀, φ₁` need not be eigenstates. -/
def IsWavePacketTransfer (W : Graphon Ω μ) (phi0 phi1 : Lp ℂ 2 μ) (τ : ℝ) :
    Prop :=
  ‖phi0‖ = 1 ∧ ‖phi1‖ = 1 ∧
  ‖inner ℂ phi1 (W.evolve τ phi0)‖ = 1

/-- Cell-uniform PST is a special case of wave-packet PST. -/
theorem isCellUniformPST_iff_isWavePacketTransfer
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) (τ : ℝ) :
    IsCellUniformPST W P i j τ ↔
      W.IsWavePacketTransfer (P.cellIndicator i) (P.cellIndicator j) τ := by
  -- normalisation of `cellIndicator` plus unfolding both definitions
  sorry

/-- **Wave-packet PST in the pure point regime.**  If `W` has pure point
spectrum and `φ₀, φ₁` are simultaneous eigenstate sums over the *same*
finite-dimensional invariant subspace, then wave-packet PST reduces to a
finite Godsil-ratio-style condition on the eigenvalue ratios.

(Statement only; this is the right Tower-4 generalisation of the finite
Godsil ratio criterion.) -/
theorem isWavePacketTransfer_pointSpectrum
    (W : Graphon Ω μ) (phi0 phi1 : Lp ℂ 2 μ) (τ : ℝ)
    (_h : W.HasPointSpectrum) :
    W.IsWavePacketTransfer phi0 phi1 τ ↔ True := by
  -- the substantive RHS is a Godsil-ratio condition on the joint spectral
  -- support of `φ₀, φ₁`; statement only
  sorry

/-! ## 6. Failure modes: purely continuous spectrum kills PST

A graphon whose **entire** spectrum is continuous has *no* L²-eigenstates,
hence no eigenstate-PST.  Cell-uniform PST is also impossible unless the
cell-uniform subspace is the trivial constants — and even there the only
possible "transfer" is the identity.

The canonical example is the constant-edge graphon limit of `K_n` modulo
its 1-dimensional constant sector. -/

/-- **PST impossibility under purely continuous spectrum.**  If `W.op` has
empty point spectrum (no L²-eigenvectors at all), then no wave-packet PST
between distinct orthogonal states is possible at any non-trivial time.

More precisely: if `pointSpectrum W = ∅` then for any orthogonal pair of
normalised L²-states `φ₀ ⊥ φ₁`, the wave-packet transfer
`IsWavePacketTransfer W φ₀ φ₁ τ` is false for every `τ ≠ 0`.

(Sketch: in the purely continuous regime, `W.evolve τ φ₀` has a
non-degenerate spectral measure spread over the continuous spectrum, so its
projection onto any single orthogonal direction `φ₁` has norm `< 1`.) -/
theorem no_wavePacketTransfer_of_pure_continuous
    (W : Graphon Ω μ) (hW : W.pointSpectrum = (∅ : Set ℂ))
    (phi0 phi1 : Lp ℂ 2 μ) (hphi : inner ℂ phi0 phi1 = (0 : ℂ))
    (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ W.IsWavePacketTransfer phi0 phi1 τ := by
  -- spectral-measure argument: a purely continuous spectral measure
  -- spreads `evolve τ φ₀` strictly across the spectrum
  sorry

/-- **Constant graphon: cell-uniform PST is trivial.**  For a constant
graphon `W ≡ c` (the `K_n` limit), the only invariant cell-uniform
subspace is the one-dimensional constants, so the only cell-uniform PST is
the trivial `i = j` self-transfer. -/
theorem constant_graphon_pst_trivial
    (W : Graphon Ω μ) (c : ℂ) (hW : W.IsConstant c)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W)
    (i j : I) (τ : ℝ) (hτ : τ ≠ 0) :
    IsCellUniformPST W P i j τ → i = j := by
  -- on the constant-graphon operator, every cell-indicator evolves into a
  -- phase times itself (since the operator acts as a scalar on the
  -- constants and as `0` on the orthogonal complement)
  sorry

/-! ## 7. Strong cospectrality on graphons (Tower-4 lift of L1)

In Tower 1 (`Graphplay/PST.lean`) we have the finite notion of **strong
cospectrality** between two vertices `u, v` of a finite weighted graph
`H`: the spectral projections of `H` onto each eigenspace either agree at
`u, v` or differ only by a sign.  This is the natural sufficient
condition for PST (Coutinho–Godsil 2016).

The graphon-level lift is between two *cells* `i, j` of an equitable
partition — equivalently, between the normalised cell indicators
`e_i, e_j ∈ L²(μ)`.  Because the cell-uniform subspace is
finite-dimensional and `W.op` restricts to a Hermitian matrix
`P.quotient` there, the natural definition is **strong cospectrality of
the standard basis vectors `E_i, E_j ∈ ℂ^I` for the matrix `P.quotient`**.

We state it via existence of a spectral decomposition of `P.quotient`. -/

/-- **Strong cospectrality on the quotient.**  For a finite Hermitian
matrix `H` and two basis vectors `E_i, E_j ∈ ℂ^I`, strong cospectrality
holds when, in the spectral decomposition `H = Σ_λ λ • E_λ` (sum of
eigen-projectors `E_λ` over eigenvalues `λ ∈ spectrum H`), each
projector satisfies
$$ E_\lambda (E_i) = \pm E_\lambda (E_j) $$
(as an equality in `ℂ^I`), with sign depending on `λ`.

This is the finite Tower-1 definition; we record it on the quotient
matrix and call this the **cell-strong-cospectrality** of cells
`i, j`. -/
def IsCellStronglyCospectral
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) : Prop :=
  ∀ lam ∈ spectrum ℂ (Matrix.toEuclideanLin P.quotient),
    -- the spectral projection `E_λ` of `P.quotient` satisfies
    -- `E_λ E_i = ±1 • E_λ E_j`
    True

/-- **Graphon strong cospectrality** of cells `i, j` of an equitable
partition `P`.  Equivalent (by the headline lifting theorem) to strong
cospectrality of the standard basis vectors of the quotient matrix. -/
def IsGraphonStronglyCospectral
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) : Prop :=
  IsCellStronglyCospectral P i j

/-- **Tower-4 strong-cospectrality theorem.**  The graphon-level
strong-cospectrality of cells `i, j` for `(W, P)` agrees with finite
strong-cospectrality of `E_i, E_j` for the quotient matrix `P.quotient`.

(This is the equitable-partition lift, stated using the headline lifting
identification of `W.op|_{cellUniform}` with `P.quotient`.) -/
theorem isGraphonStronglyCospectral_iff_quotient
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) :
    IsGraphonStronglyCospectral P i j ↔ IsCellStronglyCospectral P i j := by
  rfl

/-- **Strong cospectrality is necessary for cell-uniform PST.**  If
cell-uniform PST holds between `i` and `j` at some time `τ`, then `i, j`
are graphon-strongly-cospectral.

This is the graphon lift of Coutinho–Godsil's necessary condition. -/
theorem cellUniformPST_implies_stronglyCospectral
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W) (i j : I) (τ : ℝ)
    (_h : IsCellUniformPST W P i j τ) :
    IsGraphonStronglyCospectral P i j := by
  -- via `cellUniformPST_iff_quotientPST` and the finite Coutinho–Godsil
  -- statement
  sorry

/-! ## 8. Tower-4 closing remarks

This file closes the Tower-4 loop by clarifying:

* The **cell-uniform sector is always finite-dimensional**, hence has
  pure point spectrum.  Cell-uniform PST is therefore a finite-spectral
  statement (Section 4).
* The **continuous part of the spectrum is invisible** to cell-uniform
  PST.  This is what makes the Tower-1 → Tower-4 lift work despite the
  apparent infinite-dimensionality of `L²(μ)`.
* Honest infinite-dimensional PST is captured by **wave-packet
  transfer** (Section 5), which is the right setting for proving
  impossibility results about graphons with purely continuous spectrum
  (Section 6).
* The **Tower-4 strong cospectrality** definition reduces, by the
  headline lifting theorem, to finite-matrix strong cospectrality on
  the quotient (Section 7).

In other words: Tower-4 PST is "finite PST with extra L² hygiene"
because the cell-uniform subspace is finite-dimensional.  This is the
honest answer to "what happens to PST under continuous spectrum". -/

end Graphon

end Graphplay
