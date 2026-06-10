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
* a machine-checked **refutation** (`naive_pipeline_fails`) showing the walk on
  the system register alone can never invert — the orbit `t ↦ e^{-iAt}b` is
  norm-preserving — so the enlarged graph of the cited solver is essential;
* the headline success/complexity statement is stated precisely and made
  axiom-clean conditional on the named literature class
  `CTQW2508MatrixInversion` (the convergence analysis of arXiv:2508.06611,
  with the enlarged walk space quantified inside the cited field);
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
import Mathlib.Analysis.SpecialFunctions.Exponential
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

/-- The **naive walk pipeline**: evolve `b` directly under the system walk
`U(t) = e^{-iAt}`, with no enlarged graph, no ancilla coupling, no
post-selection.  This is *not* the arXiv:2508.06611 solver — it is the strawman
obtained by deleting the enlarged system from it.  It cannot invert anything:
`U(t)` is unitary, so the orbit `t ↦ U(t)b` stays on the sphere `‖·‖ = ‖b‖`
and revisits phases forever instead of converging (`naive_pipeline_fails`).
The enlarged graph and the marked-register measurement are where the inversion
actually happens; they live inside `CTQW2508MatrixInversion`. -/
noncomputable def naiveWalkOutput (S : LinearSystem n) (t : ℝ) : n → ℂ :=
  (S.walkEvolve t).mulVec S.b

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

The physical CTQW does not produce `A⁻¹|b⟩` exactly: a finite evolution time on
the enlarged walk graph yields an approximate output, with error controlled by
the condition number `κ` and the walk time.  Two statements live here:

* a machine-checked **refutation** that the *un-enlarged* walk (evolve `b`
  under `e^{-iAt}` and read it back) can never meet the guarantee — unitarity
  pins the orbit to the sphere `‖·‖ = ‖b‖` (`naive_pipeline_fails`);
* the cited guarantee (`CTQW2508MatrixInversion`): an **enlarged** walk, whose
  Hamiltonian is `A` plus an ancilla coupling, inverts to within `ε` in walk
  time `O(κ/ε)` — the CTQW improvement claimed in arXiv:2508.06611 over the
  `O(κ²/ε)` of phase-estimation HHL. -/

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

/-- The success predicate the **naive** (un-enlarged) pipeline would need: for
every `ε > 0`, the bare walk orbit at the prescribed time `walkTime ε = κ/ε` is
`ε`-close to the normalized solution.  `naive_pipeline_fails` refutes it on a
1 × 1 system: no walk on the system register alone can invert, because the
orbit is confined to the sphere `‖·‖ = ‖b‖` and keeps rotating.  This is *why*
the cited solver (`CTQW2508MatrixInversion`) must enlarge the system. -/
def NaiveCTQWSuccess (S : LinearSystem n) : Prop :=
  ∀ {ε : ℝ}, 0 < ε →
    ∃ ψ : n → ℂ, ψ = S.naiveWalkOutput (S.walkTime ε) ∧
      (∑ i, ‖ψ i - normalize S.solution i‖ ^ 2 : ℝ).sqrt ≤ ε

end LinearSystem

/-! #### The naive pipeline cannot invert: a machine-checked refutation

On the system `A = (2)`, `b = (1)` the bare walk orbit is the unit-modulus
scalar `t ↦ e^{-2it}`, while the normalized solution is the constant `1`.
The orbit passes through `-1`, at distance `2` from the target — so the
demanded bound fails at any `ε < 2` whose schedule lands there. -/

/-- The 1 × 1 refutation system: `A = (2)`, `b = (1)`.  Solution `1/2`,
normalized solution `1`, condition number `1`, walk schedule `t(ε) = 1/ε`. -/
noncomputable def refutationSystem : LinearSystem (Fin 1) where
  A := Matrix.diagonal fun _ => (2 : ℂ)
  herm := Matrix.isHermitian_diagonal_iff.mpr fun _ => by
    rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofNat]
  inv := by
    rw [Matrix.det_diagonal, Fin.prod_univ_one]
    exact isUnit_iff_ne_zero.mpr two_ne_zero
  b := fun _ => 1

/-- `A·v` is entrywise doubling for the refutation system. -/
theorem refutationSystem_A_mulVec (v : Fin 1 → ℂ) (i : Fin 1) :
    refutationSystem.A.mulVec v i = 2 * v i := by
  show (Matrix.diagonal fun _ => (2 : ℂ)).mulVec v i = 2 * v i
  rw [Matrix.mulVec_diagonal]

/-- The single eigenvalue of the refutation system is `2` (from the trace). -/
theorem refutationSystem_eigenvalues (i : Fin 1) :
    refutationSystem.herm.eigenvalues i = 2 := by
  have htr := refutationSystem.herm.trace_eq_sum_eigenvalues
  rw [Fin.sum_univ_one] at htr
  have h2 : refutationSystem.A.trace = (2 : ℂ) := by
    show (Matrix.diagonal fun _ => (2 : ℂ)).trace = 2
    rw [Matrix.trace_diagonal, Fin.sum_univ_one]
  rw [h2] at htr
  rw [Fin.eq_zero i]
  have h := htr.symm
  rw [show (2 : ℂ) = RCLike.ofReal (2 : ℝ) by norm_num] at h
  exact RCLike.ofReal_inj.mp h

/-- The refutation system is perfectly conditioned: `κ = 1`. -/
theorem refutationSystem_conditionNumber :
    refutationSystem.conditionNumber = 1 := by
  unfold LinearSystem.conditionNumber
  rw [ciSup_unique, ciInf_unique, refutationSystem_eigenvalues]
  norm_num

/-- The exact solution of `2x = 1` is `1/2`. -/
theorem refutationSystem_solution (i : Fin 1) :
    refutationSystem.solution i = 1 / 2 := by
  have h0 := congrFun refutationSystem.A_mulVec_solution i
  rw [refutationSystem_A_mulVec] at h0
  have hb : refutationSystem.b i = 1 := rfl
  rw [hb] at h0
  -- h0 : 2 * solution i = 1
  rw [eq_div_iff (two_ne_zero (α := ℂ))]
  linear_combination h0

/-- The normalized solution of the refutation system is the constant `1`. -/
theorem refutationSystem_normalize_solution (i : Fin 1) :
    LinearSystem.normalize refutationSystem.solution i = 1 := by
  unfold LinearSystem.normalize
  rw [Pi.smul_apply, Fin.sum_univ_one, refutationSystem_solution,
    refutationSystem_solution]
  have hnorm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_ofNat]
  rw [hnorm]
  have hsqrt : Real.sqrt ((1 / 2) ^ 2) = 1 / 2 := Real.sqrt_sq (by norm_num)
  rw [hsqrt]
  norm_num

/-- At walk time `π/2` the refutation walk sits at `U(π/2) = (-1)`:
`e^{-i·(π/2)·2} = e^{-iπ} = -1`. -/
theorem refutationSystem_walkEvolve_pi_div_two :
    refutationSystem.walkEvolve (Real.pi / 2)
      = Matrix.diagonal fun _ => (-1 : ℂ) := by
  unfold LinearSystem.walkEvolve
  have hsm : (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) • refutationSystem.A
      = Matrix.diagonal fun _ => -(Real.pi * Complex.I) := by
    show _ • Matrix.diagonal (fun _ => (2 : ℂ)) = _
    rw [← Matrix.diagonal_smul]
    congr 1
    funext _
    show -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) * 2 = -(Real.pi * Complex.I)
    push_cast
    ring
  rw [hsm, Matrix.exp_diagonal]
  congr 1
  funext _
  rw [Pi.exp_def]
  show NormedSpace.exp (-((Real.pi : ℂ) * Complex.I)) = -1
  rw [← Complex.exp_eq_exp_ℂ, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **The naive pipeline cannot invert** — machine-checked emptiness.  For the
1 × 1 system `2x = 1` the bare walk orbit `t ↦ e^{-2it}·b` is unit-modulus, and
at `ε = 2/π` the schedule `t = κ/ε = π/2` parks it at `-1`, distance `2 > 2/π`
from the normalized solution `1`.  So `NaiveCTQWSuccess` is unsatisfiable here:
a class demanding it for every system would be **empty**, and any theorem
conditioned on it vacuous.  The enlarged graph + marked-register measurement of
arXiv:2508.06611 are therefore not packaging: they are where the eigenvalue
inversion happens, which is why `CTQW2508MatrixInversion` quantifies over an
enlarged walk space. -/
theorem naive_pipeline_fails :
    ¬ LinearSystem.NaiveCTQWSuccess refutationSystem := by
  intro h
  have hπ : (1 : ℝ) < Real.pi := by linarith [Real.two_le_pi]
  have hε : (0 : ℝ) < 2 / Real.pi := by positivity
  obtain ⟨ψ, hψ, hbound⟩ := h hε
  -- The schedule: `walkTime (2/π) = κ/(2/π) = π/2`.
  have ht : refutationSystem.walkTime (2 / Real.pi) = Real.pi / 2 := by
    unfold LinearSystem.walkTime
    rw [refutationSystem_conditionNumber]
    field_simp
  rw [ht] at hψ
  -- The orbit value: `ψ = (-1)`.
  have hψval : ψ = fun _ : Fin 1 => (-1 : ℂ) := by
    rw [hψ]
    funext i
    unfold LinearSystem.naiveWalkOutput
    rw [refutationSystem_walkEvolve_pi_div_two, Matrix.mulVec_diagonal]
    show (-1 : ℂ) * (1 : ℂ) = -1
    ring
  -- The distance: `‖(-1) - 1‖ = 2`.
  have hdist : (∑ i, ‖ψ i - LinearSystem.normalize refutationSystem.solution i‖ ^ 2
      : ℝ).sqrt = 2 := by
    rw [hψval, Fin.sum_univ_one, refutationSystem_normalize_solution]
    have : ‖(-1 : ℂ) - 1‖ = 2 := by
      have : (-1 : ℂ) - 1 = -2 := by ring
      rw [this, norm_neg, Complex.norm_ofNat]
    rw [this]
    rw [show ((2 : ℝ) ^ 2) = 4 by norm_num]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hdist] at hbound
  -- But `2 ≤ 2/π` forces `π ≤ 1`.
  have : 2 / Real.pi < 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **CTQW matrix inversion** (arXiv:2508.06611, *Matrix inversion by quantum
walk*) — the cited result, verbatim.  For every linear-system instance
`(A, b)` there is a constant `c > 0` such that for every target error `ε > 0`
there exist

* an **enlarged walk space** `n ⊕ Fin k` (the system register plus `k`
  ancilla vertices — the enlarged graph is quantified existentially *inside*
  the field: its construction is part of the cited content);
* a Hermitian walk Hamiltonian `H` on it whose system block is **exactly
  `A`** (`H = A` plus an ancilla coupling — the defining feature of the
  phase-estimation-free scheme: the walk runs on the input matrix itself);
* a walk time `|t| ≤ c·κ/ε`,

such that the normalized system-register read-out of `e^{-iHt}` applied to
`b` (encoded on the system register, `0` on the ancillas) is within `ε` of
the normalized exact solution `A⁻¹b/‖A⁻¹b‖`.

The system-block constraint `H(inl i, inl i') = A(i, i')` pins the walk
generator to the input.  Without it the field would be cheatable: any unitary
carrying the encoded `b` to the embedded solution is `e^{-iH}` for *some*
Hermitian `H`, so an unconstrained `H` could be reverse-engineered from
`A⁻¹b` with no inversion mechanism at all.  Conversely `naive_pipeline_fails`
shows `k = 0` ancillas cannot suffice — the two constraints together leave
exactly the content of the cited theorem.

Stated as a typeclass (never a bare `axiom`): theorems assuming
`[CTQW2508MatrixInversion]` are sorry-free conditional theorems citing the
convergence / interference analysis of arXiv:2508.06611 (built on HHL,
Phys. Rev. Lett. 103, 150502, and Childs' CTQW simulation), which is not in
Mathlib.  No instance is provided. -/
class CTQW2508MatrixInversion : Prop where
  /-- Verbatim headline of arXiv:2508.06611: an `A`-coupled enlarged walk
  whose normalized marked-register read-out `ε`-approximates the normalized
  solution in walk time `O(κ/ε)`. -/
  ctqw_inverts :
    ∀ {n : Type u} [Fintype n] [DecidableEq n] (S : LinearSystem n),
      ∃ c : ℝ, 0 < c ∧
        ∀ {ε : ℝ}, 0 < ε →
          ∃ (k : ℕ) (H : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℂ) (t : ℝ),
            H.IsHermitian ∧
            (∀ i i', H (Sum.inl i) (Sum.inl i') = S.A i i') ∧
            |t| ≤ c * S.conditionNumber / ε ∧
            (∑ i, ‖LinearSystem.normalize
                (fun i' => (NormedSpace.exp (-(Complex.I * (t : ℂ)) • H)).mulVec
                  (Sum.elim S.b fun _ => 0) (Sum.inl i')) i
              - LinearSystem.normalize S.solution i‖ ^ 2 : ℝ).sqrt ≤ ε

namespace LinearSystem

/-- **CTQW matrix-inversion success** (arXiv:2508.06611), an axiom-clean
conditional theorem: assuming the cited class, every linear system admits, for
every `ε > 0`, an enlarged walk graph extending `A` (Hermitian `H` on
`n ⊕ Fin k` with system block `A`) and a walk time `O(κ/ε)` whose normalized
system-register read-out is within `ε` of the normalized exact solution.  The
output is bound to the walk read-out of the encoded `b` — not a free witness —
and the walk generator is bound to `A`, so this is the genuine convergence
guarantee. -/
theorem ctqw_success [CTQW2508MatrixInversion.{u}] (S : LinearSystem n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℝ) (k : ℕ) (H : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℂ) (t : ℝ),
      0 < c ∧
      H.IsHermitian ∧
      (∀ i i', H (Sum.inl i) (Sum.inl i') = S.A i i') ∧
      |t| ≤ c * S.conditionNumber / ε ∧
      (∑ i, ‖normalize
          (fun i' => (NormedSpace.exp (-(Complex.I * (t : ℂ)) • H)).mulVec
            (Sum.elim S.b fun _ => 0) (Sum.inl i')) i
        - normalize S.solution i‖ ^ 2 : ℝ).sqrt ≤ ε := by
  obtain ⟨c, hc, hwalk⟩ := CTQW2508MatrixInversion.ctqw_inverts S
  obtain ⟨k, H, t, hH⟩ := hwalk hε
  exact ⟨c, k, H, t, hc, hH⟩

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
  `ofWeighted`), `walkEvolve` (+ `walkEvolve_zero`), `naiveWalkOutput`,
  `ctqwInverter` (+ `ctqwInverter_mulVec`), `conditionNumber`, `walkTime`,
  `normalize`, `IsCellUniform`, and `inversion_restricts_to_quotient` (the
  inverse-of-restriction algebra on the cell-uniform subspace, proven from
  `Graphplay.Equitable`'s spectral lift).
* **Refutation (machine-checked):** `naive_pipeline_fails` — the un-enlarged
  walk pipeline cannot meet the `ε`-convergence demand even on the 1 × 1 system
  `2x = 1`; the predicate `NaiveCTQWSuccess` is unsatisfiable there.  This is
  why the cited interface quantifies over an enlarged walk space rather than
  reusing the system register.
* **Typeclass-conditional (the one genuinely-external result):**
  `ctqw_success`, conditional on `CTQW2508MatrixInversion` — the arXiv:2508.06611
  guarantee, with the enlarged space `n ⊕ Fin k`, the `A`-block constraint on
  the walk Hamiltonian, the `O(κ/ε)` time bound, and the bound output read-out
  all inside the single cited field.
-/

end MatrixInversion
end Graphplay
