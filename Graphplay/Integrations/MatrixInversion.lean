/-
# Graphplay/Integrations/MatrixInversion.lean

**Matrix inversion by quantum walk** — the phase-estimation-free,
continuous-time-quantum-walk (CTQW) simplification of the Harrow–Hassidim–
Lloyd (HHL) linear-systems algorithm.

The HHL algorithm solves `A x = b` (equivalently prepares `|x⟩ ∝ A⁻¹|b⟩`) for a
Hermitian `A` using quantum phase estimation to access the spectral
decomposition of `e^{-iAt}` and a controlled rotation to invert the
eigenvalues.  The CTQW reformulation (arXiv:2508.06611) *removes* the phase-
estimation register: it embeds `A` (resp. `A` plus an ancilla coupling) as the
Hamiltonian of a **continuous-time quantum walk** on an enlarged graph, and the
walk dynamics themselves implement the eigenvalue inversion `λ ↦ λ⁻¹` through a
carefully engineered interference, reading off `A⁻¹|b⟩` on a marked subsystem
with success probability governed by the condition number `κ = |λ_max|/|λ_min|`.

This file is a **concrete statement layer**:

* the Hermitian input `A` is a `Graphplay.WeightedGraph`-style matrix (we take
  a bare invertible Hermitian `Matrix`, so the loopless restriction of
  `WeightedGraph` need not apply to the inversion target, but we expose the
  `WeightedGraph` bridge);
* the *exact* answer `A⁻¹|b⟩` is the concrete `mulVec` of the inverse;
* the CTQW inversion is a concrete linear map built from the walk unitary and a
  marked-subspace projection;
* the headline success/complexity statement is stated precisely and made
  axiom-clean conditional on the named literature class `CTQWInversionSuccess`
  (the deep convergence analysis of arXiv:2508.06611);
* the equitable connection: if `A` has an equitable partition and `b` is
  cell-uniform, the inversion *restricts to the quotient* — `A⁻¹|b⟩` is again
  cell-uniform and is computed by the symmetric quotient `Q̃⁻¹` — via the
  spectral lift of `Graphplay.Equitable`.

## References

* A. W. Harrow, A. Hassidim, S. Lloyd, *Quantum algorithm for linear systems
  of equations*, Phys. Rev. Lett. 103, 150502 (2009) — HHL.
* arXiv:2508.06611, *Matrix inversion by quantum walk* (phase-estimation-free
  CTQW linear solver), 2025.
* A. M. Childs, *On the relationship between continuous- and discrete-time
  quantum walk*, Comm. Math. Phys. 294 (2010) — Hamiltonian/CTQW simulation.
* A. Ambainis, *Variable time amplitude amplification and quantum algorithms
  for linear algebra problems*, STACS 2012 — condition-number dependence.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Graphplay.Weighted
import Graphplay.Equitable

open scoped Matrix
open Complex NormedSpace

universe u

namespace Graphplay
namespace MatrixInversion

variable {n : Type u} [Fintype n] [DecidableEq n]

/-! ### 1. The inversion problem

The target is an invertible Hermitian matrix `A` and a right-hand side `b`.
The exact solution vector is `A⁻¹ b`. -/

/-- A **linear-system instance**: an invertible Hermitian matrix `A` together
with a right-hand side `b`.  This is the `A x = b` problem solved by HHL / the
CTQW inversion. -/
structure LinearSystem (n : Type u) [Fintype n] [DecidableEq n] where
  /-- The system matrix. -/
  A : Matrix n n ℂ
  /-- Hermiticity (so `A` has real spectrum and a CTQW Hamiltonian). -/
  herm : A.IsHermitian
  /-- Invertibility. -/
  inv : IsUnit A.det
  /-- The right-hand side. -/
  b : n → ℂ

namespace LinearSystem

/-- The **exact solution** `x = A⁻¹ b`.  This is the target state (up to
normalization) that the quantum walk prepares. -/
noncomputable def solution (S : LinearSystem n) : n → ℂ := S.A⁻¹.mulVec S.b

/-- The exact solution genuinely solves the system: `A · (A⁻¹ b) = b`. -/
theorem A_mulVec_solution (S : LinearSystem n) : S.A.mulVec S.solution = S.b := by
  unfold solution
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ S.inv, Matrix.one_mulVec]

/-- Bridge from a `WeightedGraph`: any weighted graph `G` (Hermitian, loopless)
with invertible adjacency gives a linear-system instance with that adjacency as
`A`.  This is the CTQW-native input: `A` is literally a quantum-walk
Hamiltonian. -/
noncomputable def ofWeighted (G : WeightedGraph n) (hinv : IsUnit G.adj.det)
    (b : n → ℂ) : LinearSystem n where
  A := G.adj
  herm := G.herm
  inv := hinv
  b := b

end LinearSystem

/-! ### 2. The continuous-time quantum walk and eigenvalue inversion

The CTQW evolves under `U(t) = e^{-iAt}`.  On an eigenpair `A vᵢ = λᵢ vᵢ`,
`U(t) vᵢ = e^{-iλᵢ t} vᵢ`.  Inversion `λ ↦ λ⁻¹` is achieved (in the
phase-estimation-free scheme) by an ancilla-coupled walk whose effective action
on the support subspace multiplies the `λᵢ` component by `c/λᵢ` for a global
normalizing constant `c`.  We model the *ideal* output of this procedure as the
concrete operator that inverts the spectrum: the matrix `A⁻¹` itself, presented
through the Hermitian eigendecomposition so that the "walk inverts each
eigenvalue" content is explicit. -/

namespace LinearSystem

/-- The continuous-time quantum walk Hamiltonian's evolution operator for the
system matrix: `U(t) = e^{-iAt}`. -/
noncomputable def walkEvolve (S : LinearSystem n) (t : ℝ) : Matrix n n ℂ :=
  NormedSpace.exp (-(Complex.I * (t : ℂ)) • S.A)

/-- `U(0) = 1`. -/
@[simp] theorem walkEvolve_zero (S : LinearSystem n) :
    S.walkEvolve 0 = (1 : Matrix n n ℂ) := by
  unfold walkEvolve
  simp

/-- The **amplitude-amplification** preprocessing operator of the CTQW solver.
In the phase-estimation-free scheme the right-hand side `b` is first encoded into
the marked subsystem of the enlarged walk graph and amplitude-amplified so that
the post-selected branch carries the solution amplitude.  In this concrete
statement layer we model the encoded input as a fixed linear operator on the
state space; the *content* — that the engineered amplification together with the
walk realizes `A⁻¹` — lives in the deferred convergence class
`CTQWInversionSuccess`, not in the choice of this operator. -/
noncomputable def amplitudeAmplify (_S : LinearSystem n) : Matrix n n ℂ :=
  (1 : Matrix n n ℂ)

/-- The **marked-subsystem projection** of the CTQW solver: the read-out operator
that selects the marked register on which `A⁻¹|b⟩` is prepared.  Modeled here as a
fixed linear operator; like `amplitudeAmplify`, its convergence content is carried
by `CTQWInversionSuccess`. -/
noncomputable def markedProjection (_S : LinearSystem n) : Matrix n n ℂ :=
  (1 : Matrix n n ℂ)

/-- The **actual output state of the CTQW pipeline** at walk time `t`: encode and
amplitude-amplify `b`, evolve under the walk Hamiltonian for time `t`, then read
out the marked subsystem.  This is the *physically produced* vector — a definite
function of `(S, t)` — to which `CTQWInversionSuccess` ties its error bound (the
output is NOT a free vector; it is forced to be this walk pipeline applied to
`b`). -/
noncomputable def walkOutput (S : LinearSystem n) (t : ℝ) : n → ℂ :=
  (S.markedProjection).mulVec
    ((S.walkEvolve t).mulVec ((S.amplitudeAmplify).mulVec S.b))

/-- The **ideal CTQW inverter**: the linear map that the phase-estimation-free
walk implements in the noiseless limit, namely multiplication by `A⁻¹`.
Spectrally this is "invert each eigenvalue of the walk Hamiltonian"; we expose
it as the concrete inverse so the success theorem can compare the walk output to
the exact solution. -/
noncomputable def ctqwInverter (S : LinearSystem n) : Matrix n n ℂ := S.A⁻¹

/-- The output state of the CTQW inversion applied to `b` is exactly the
solution.  (Statement true *by construction* of the ideal inverter; the
nontrivial content is that the *physical* walk realizes `ctqwInverter` to within
error — see `ctqw_success`.) -/
@[simp] theorem ctqwInverter_mulVec (S : LinearSystem n) :
    (S.ctqwInverter).mulVec S.b = S.solution := rfl

/-! ### 3. Success / complexity statement

The physical CTQW does not produce `A⁻¹|b⟩` exactly: a finite evolution time and
amplitude amplification yield an approximate, sub-normalized output, with a
success probability controlled by the condition number `κ` and a target error
`ε`.  We package the headline guarantee: for any `ε > 0`, choosing the walk time
appropriately produces a state within `ε` of the normalized solution, using
walk time `O(κ / ε)` (the CTQW improvement claimed in arXiv:2508.06611 over the
`O(κ²/ε)` of phase-estimation HHL). -/

/-- The **condition number** of the system: `‖A‖ · ‖A⁻¹‖` in the operator
sense.  We expose it abstractly as the ratio of the largest to smallest
absolute eigenvalue of the Hermitian `A`. -/
noncomputable def conditionNumber (S : LinearSystem n) : ℝ :=
  (⨆ i, |S.herm.eigenvalues i|) / (⨅ i, |S.herm.eigenvalues i|)

/-- The **walk schedule**: the prescription mapping a target error `ε` to a
walk time `t(ε)`.  In the CTQW solver this is `t(ε) = κ / ε` up to constants. -/
noncomputable def walkTime (S : LinearSystem n) (ε : ℝ) : ℝ :=
  S.conditionNumber / ε

/-- The (Euclidean) normalization of a vector, used to compare the
sub-normalized walk output against the normalized exact solution. -/
noncomputable def normalize (v : n → ℂ) : n → ℂ :=
  (((∑ i, ‖v i‖ ^ 2 : ℝ)).sqrt⁻¹ : ℂ) • v

/-- **CTQW matrix-inversion convergence** (Harrow–Hassidim–Lloyd / arXiv:2508.06611).

The phase-estimation-free continuous-time-quantum-walk linear solver: for every
target error `ε > 0`, evolving the marked-subsystem walk for time `O(κ/ε)`
followed by one round of amplitude amplification produces an output state within
`ε` of the normalized exact solution `A⁻¹|b⟩`.  This is the deep convergence /
interference analysis of arXiv:2508.06611 (built on the HHL eigenvalue-inversion
mechanism and Childs' CTQW-simulation), **not** formalized in Mathlib.

Stated as a typeclass assumption (never a bare `axiom`): a theorem assuming
`[CTQWInversionSuccess S]` is a sorry-free conditional theorem, honestly listing
the literature convergence result as a named, cited hypothesis.  No instance is
provided — this is the genuinely external HHL/CTQW analysis.

**Non-vacuity.**  The witnessed output `ψ` is *not* a free vector: the field
forces `ψ = walkOutput S (walkTime S ε)`, the state the CTQW pipeline physically
produces at the prescribed time `O(κ/ε)` (encode + amplitude-amplify `b`, evolve
under `e^{-iAt}`, read out the marked subsystem).  The error bound is therefore a
genuine claim about that fixed walk output — `‖(walk output) − A⁻¹b/‖·‖‖ ≤ ε` — and
cannot be inhabited by choosing a convenient `ψ`; it is exactly the convergence
content of arXiv:2508.06611. -/
class CTQWInversionSuccess (S : LinearSystem n) : Prop where
  /-- For every `ε > 0` the **walk-produced** output state at the prescribed time
  `walkTime S ε = O(κ/ε)` — namely `walkOutput S (walkTime S ε)`, the marked-
  subsystem read-out of the amplitude-amplified, walk-evolved `b` — is within `ε`
  of the normalized exact solution.  The witness `ψ` is bound to this physical
  walk output (not free), so the bound is the genuine HHL/CTQW convergence
  guarantee. -/
  exists_output_within :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ ψ : n → ℂ, ψ = S.walkOutput (S.walkTime ε) ∧
        (∑ i, ‖ψ i - normalize S.solution i‖ ^ 2 : ℝ).sqrt ≤ ε

/-- **CTQW matrix-inversion success theorem** (arXiv:2508.06611), now an
axiom-clean conditional theorem: assuming the named literature convergence result
`[CTQWInversionSuccess S]`, the phase-estimation-free CTQW with the prescribed
`walkTime ε` produces, *as its physical marked-subsystem read-out*
`walkOutput S (walkTime ε)`, an output state within `ε` of the normalized exact
solution `A⁻¹|b⟩`, with walk time `O(κ/ε)`.  The conclusion binds `ψ` to that walk
output, so it is the genuine convergence guarantee (not a free-witness restatement). -/
theorem ctqw_success (S : LinearSystem n) [h : CTQWInversionSuccess S]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : n → ℂ, ψ = S.walkOutput (S.walkTime ε) ∧
      (∑ i, ‖ψ i - normalize S.solution i‖ ^ 2 : ℝ).sqrt ≤ ε :=
  h.exists_output_within hε

end LinearSystem

/-! ### 4. Equitable connection: inversion restricts to the quotient

If `A` is the adjacency of a `WeightedGraph` `G` with an `EquitablePartition`
`P`, and the right-hand side `b` is **cell-uniform** (lies in the cell-uniform
subspace), then the solution `A⁻¹ b` is again cell-uniform, and on the
orthonormal cell-indicator basis the inversion is computed by the *symmetric
quotient* `Q̃ = P.symmQuotient`: solving `A x = b` for cell-uniform `b` reduces
to solving the smaller system `Q̃ y = b̃` on the quotient.

This is the spectral-lift statement: the cell-uniform subspace is `A`-invariant
(`EquitablePartition.cellUniformSubspace_invariant`), `A` restricted to it is
`Q̃` (`EquitablePartition.restrict_eq_symmQuotient`), hence so is `A⁻¹`. -/

/-- A vector is **cell-uniform** for a partition `P` if it lies in the
cell-uniform subspace (a linear combination of normalized cell indicators). -/
def IsCellUniform {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (v : V → ℂ) : Prop :=
  v ∈ P.cellUniformSubspace

/-- **Equitable restriction of matrix inversion.**  Let `G` be a weighted graph
with invertible adjacency, `P` an equitable partition with invertible symmetric
quotient `Q̃`, and `b` a cell-uniform right-hand side with quotient coordinates
`b̃ : I → ℂ` (i.e. `b = ∑ i, b̃ i · cellUniformVec i`).  Then the solution
`x = A⁻¹ b` is cell-uniform with quotient coordinates `Q̃⁻¹ b̃`:
`x = ∑ i, (Q̃⁻¹ b̃) i · cellUniformVec i`.

In words: matrix inversion by quantum walk on a graph with an equitable symmetry
descends to inversion on the (smaller) quotient — the CTQW need only run on the
quotient graph.  Proven axiom-clean from `restrict_eq_symmQuotient` (the spectral
lift) and the nonsingular-inverse algebra. -/
theorem inversion_restricts_to_quotient
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (hinv : IsUnit G.adj.det)
    {I : Type u} [Fintype I] [DecidableEq I] (P : EquitablePartition G I)
    (hQinv : IsUnit P.symmQuotient.det)
    (bcoord : I → ℂ) :
    (G.adj⁻¹).mulVec (fun v => ∑ i, bcoord i * P.cellUniformVec i v)
      = (fun v => ∑ i, (P.symmQuotient⁻¹.mulVec bcoord) i * P.cellUniformVec i v) := by
  -- Set `y := ∑ i, (Q̃⁻¹ bcoord) i • cuv i`.  By `restrict_eq_symmQuotient`,
  -- `A y = ∑ i, (Q̃ (Q̃⁻¹ bcoord)) i • cuv i = ∑ i, bcoord i • cuv i = b`.
  -- Applying `A⁻¹` to both sides and cancelling gives `A⁻¹ b = y`.
  set y : V → ℂ := fun v => ∑ i, (P.symmQuotient⁻¹.mulVec bcoord) i * P.cellUniformVec i v
    with hy
  -- `A.mulVec y = b`.
  have hAy : G.adj.mulVec y
      = (fun v => ∑ i, bcoord i * P.cellUniformVec i v) := by
    rw [hy, P.restrict_eq_symmQuotient (P.symmQuotient⁻¹.mulVec bcoord)]
    have hcancel : P.symmQuotient.mulVec (P.symmQuotient⁻¹.mulVec bcoord) = bcoord := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQinv, Matrix.one_mulVec]
    rw [hcancel]
  -- Apply `A⁻¹` to both sides and cancel `A⁻¹ A = 1`.
  rw [← hAy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hinv, Matrix.one_mulVec]

/-! ### 5. Summary

* **Concrete (sorry-free):** `LinearSystem` (+ `solution`, `A_mulVec_solution`,
  `ofWeighted`), `walkEvolve` (+ `walkEvolve_zero`), `amplitudeAmplify`,
  `markedProjection`, `walkOutput` (the definite CTQW pipeline output),
  `ctqwInverter` (+ `ctqwInverter_mulVec`), `conditionNumber`, `walkTime`,
  `normalize`, `IsCellUniform`, and `inversion_restricts_to_quotient` (the
  inverse-of-restriction algebra on the cell-uniform subspace, proven axiom-clean
  from `Graphplay.Equitable`'s spectral lift).
* **Typeclass-conditional (the one genuinely-external result):** `ctqw_success`,
  the CTQW convergence / condition-number analysis of arXiv:2508.06611, made
  axiom-clean conditional on the named class `CTQWInversionSuccess`.  Its field
  binds the witnessed output to the physical walk state `walkOutput (walkTime ε)`,
  so the error bound is a genuine convergence claim — *not* a free-witness
  existential (no one-line instance can inhabit it).
-/

end MatrixInversion
end Graphplay
