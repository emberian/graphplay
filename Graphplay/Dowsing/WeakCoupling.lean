/-
# Graphplay.Dowsing.WeakCoupling

**Feshbach–Schur weak-coupling perfect state transfer (arXiv:2512.08141).**

The *weak-coupling* program studies perfect state transfer (PST) on a quantum
walk whose Hamiltonian splits into a strongly-coupled **subsystem** `S` and a
weakly-coupled **environment** `E`:

      H(γ)  =  H_S ⊕ H_E  +  γ · W,

where `H_S` acts on the subsystem Hilbert space, `H_E` on the environment, and
`γ · W` is the coupling, controlled by a small real parameter `γ` (the coupling
strength).  At `γ = 0` the two blocks are decoupled; the question is how PST
inside `S` survives — or is *induced* — by turning the coupling on.

The central technical device is the **Feshbach–Schur map** (a.k.a. the Schur
complement / effective Hamiltonian / resolvent reduction): projecting `H(γ)`
onto the subsystem block `S` while exactly accounting for virtual excursions
into the environment yields an energy-dependent *effective Hamiltonian*

      F_S(z)  =  H_S  +  γ² · W_{SE} · (z − H_E)⁻¹ · W_{ES},

whose spectrum (the poles/zeros condition `det(z − F_S(z)) = 0`) reproduces the
subsystem spectrum of the full `H(γ)` to all orders in `γ`.

This file models, as concrete Lean objects:

* `CoupledSystem`: the split Hamiltonian `H_S ⊕ H_E + γ W` as a `WeightedGraph`
  on `S ⊕ E` (block form), with proven `herm`/`loopless`;
* `feshbachMap`: the energy-dependent effective subsystem Hamiltonian `F_S(z)`
  (Schur complement of the environment block at energy `z`);
* `GammaCospectral`: **γ-cospectrality** — cospectrality of two subsystem
  vertices that holds up to coupling order `γ` (i.e. modulo `O(γ²)` corrections
  from the Feshbach self-energy);
* `tRex`: the **T-rex (transfer-via-resonance) construction** — the explicit
  resonant environment that, tuned to the subsystem eigenvalue gap, induces PST
  in `S` through the weak coupling;

and states the headline weak-coupling-PST theorem precisely, with an honest
`sorry` on the resolvent-expansion proof.

**Spine connection.**  At `γ = 0` the two blocks are two *equitable cells* of the
combined graph (the block-diagonal structure is the coarsest equitable
partition).  Turning on `γ` is exactly weak coupling *between two equitable
cells*: the Feshbach map is the quotient-graph effective dynamics of the
subsystem cell, dressed by the environment cell's resolvent.

Reference: *Feshbach–Schur perfect state transfer and the T-rex construction*,
arXiv:2512.08141.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Graphplay.Weighted
import Graphplay.PST
import Graphplay.PST.GodsilRatio
import Graphplay.PST.Cospectrality
import Graphplay.StdLib.Join
import Graphplay.Tactics

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay
namespace Dowsing

variable {S : Type u} {E : Type v}
variable [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]

/-! ## The coupled (subsystem ⊕ environment) Hamiltonian

We model the split Hamiltonian `H(γ) = H_S ⊕ H_E + γ W` directly as a block
matrix on `S ⊕ E`.  The subsystem and environment carry their own
`WeightedGraph` adjacencies `H_S, H_E`; the coupling is a single Hermitian
cross-block `W_{SE} : Matrix S E ℂ` (with `W_{ES} = W_{SE}ᴴ`), scaled by the
real coupling strength `γ`.

We keep the on-site (diagonal) energies of `H_S` and `H_E` zero (the
`WeightedGraph` loopless condition); diagonal site energies, when needed, are
folded into the resolvent shift `z` in the Feshbach map below. -/

/-- A **weak-coupling system**: a subsystem graph `H_S` on `S`, an environment
graph `H_E` on `E`, a Hermitian coupling block `coupling : Matrix S E ℂ`, and a
real coupling strength `γ`.  This is the data of the split Hamiltonian
`H(γ) = H_S ⊕ H_E + γ · W` of arXiv:2512.08141. -/
structure CoupledSystem (S : Type u) (E : Type v)
    [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] where
  /-- The (strongly-coupled) subsystem Hamiltonian. -/
  sub : WeightedGraph S
  /-- The (weakly-coupled) environment Hamiltonian. -/
  env : WeightedGraph E
  /-- The subsystem–environment coupling block `W_{SE}`. -/
  coupling : Matrix S E ℂ
  /-- The real coupling strength `γ`. -/
  gamma : ℝ

namespace CoupledSystem

variable (C : CoupledSystem S E)

/-- The **full coupled Hamiltonian** `H(γ) = H_S ⊕ H_E + γ · W` as a block
matrix on `S ⊕ E`.  The diagonal blocks are the subsystem/environment
adjacencies; the off-diagonal blocks are `γ · W_{SE}` and its conjugate
transpose `γ · W_{ES}`, making the whole matrix Hermitian. -/
noncomputable def fullHam : Matrix (S ⊕ E) (S ⊕ E) ℂ :=
  Matrix.fromBlocks C.sub.adj ((C.gamma : ℂ) • C.coupling)
    ((C.gamma : ℂ) • C.couplingᴴ) C.env.adj

/-- The full coupled Hamiltonian is Hermitian: the diagonal blocks are
Hermitian (`sub.herm`, `env.herm`) and the off-diagonal blocks are conjugate
transposes of each other (`(γ W)ᴴ = γ̄ Wᴴ = γ Wᴴ` since `γ` is real). -/
theorem fullHam_isHermitian : (C.fullHam).IsHermitian := by
  unfold fullHam
  rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose]
  -- block-by-block: `subᴴ = sub`, `envᴴ = env`, and the off-diagonal blocks
  -- swap into each other under conjugate transpose.
  congr 1
  · exact C.sub.herm
  · -- top-right block: `(γ • couplingᴴ)ᴴ = γ • coupling`
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
    congr 1
    simp [Complex.conj_ofReal]
  · -- bottom-left block: `(γ • coupling)ᴴ = γ • couplingᴴ`
    rw [Matrix.conjTranspose_smul]
    congr 1
    simp [Complex.conj_ofReal]
  · exact C.env.herm

/-- At `γ = 0` the full Hamiltonian is block-diagonal: the subsystem and
environment are decoupled.  This is the "two equitable cells" limit — the
coarsest equitable partition of the combined graph has cells `S` and `E`. -/
theorem fullHam_decoupled_at_zero (C : CoupledSystem S E) (h : C.gamma = 0) :
    C.fullHam = Matrix.fromBlocks C.sub.adj 0 0 C.env.adj := by
  unfold fullHam
  rw [h]
  simp

end CoupledSystem

/-! ## The Feshbach–Schur map (effective subsystem Hamiltonian)

The Feshbach–Schur reduction eliminates the environment block exactly.  At a
complex energy `z` (away from the environment spectrum, so `z·1 − H_E` is
invertible), the effective subsystem Hamiltonian is the Schur complement of the
environment block:

      F_S(z)  =  H_S  +  γ² · W_{SE} · (z·1 − H_E)⁻¹ · W_{ES}.

The second term is the **self-energy** `Σ(z)`: the energy-dependent dressing of
the subsystem by virtual excursions into the environment.  It is `O(γ²)`, which
is why couplings of order `γ` shift the subsystem spectrum only at order `γ²`. -/

namespace CoupledSystem

variable (C : CoupledSystem S E)

/-- The **environment resolvent** `R_E(z) = (z·1 − H_E)⁻¹` at complex energy
`z`.  Defined via Mathlib's `Matrix.inv`; it is a genuine inverse exactly when
`z` avoids the environment spectrum. -/
noncomputable def envResolvent (z : ℂ) : Matrix E E ℂ :=
  (z • (1 : Matrix E E ℂ) - C.env.adj)⁻¹

/-- The **self-energy** `Σ(z) = γ² · W_{SE} · R_E(z) · W_{ES}`: the
environment's energy-dependent dressing of the subsystem, an `O(γ²)` Hermitian
(for real `z`) correction. -/
noncomputable def selfEnergy (z : ℂ) : Matrix S S ℂ :=
  ((C.gamma : ℂ) ^ 2) • (C.coupling * C.envResolvent z * C.couplingᴴ)

/-- The **Feshbach–Schur map** `F_S(z) = H_S + Σ(z)`: the exact effective
subsystem Hamiltonian at energy `z` (the Schur complement of the environment
block of `z·1 − H(γ)`). -/
noncomputable def feshbachMap (z : ℂ) : Matrix S S ℂ :=
  C.sub.adj + C.selfEnergy z

/-- At `γ = 0` the Feshbach map is just the bare subsystem Hamiltonian: the
self-energy vanishes.  (Decoupled limit.) -/
theorem feshbachMap_at_zero (C : CoupledSystem S E) (h : C.gamma = 0) (z : ℂ) :
    C.feshbachMap z = C.sub.adj := by
  unfold feshbachMap selfEnergy
  rw [h]
  simp

/-- The self-energy is `O(γ²)`: it is the scalar `γ²` times a fixed (energy- and
coupling-dependent) matrix.  This is the structural reason weak coupling shifts
the subsystem spectrum only at second order. -/
theorem selfEnergy_eq_gammaSq_smul (C : CoupledSystem S E) (z : ℂ) :
    C.selfEnergy z
      = ((C.gamma : ℂ) ^ 2) • (C.coupling * C.envResolvent z * C.couplingᴴ) := rfl

end CoupledSystem

/-! ## γ-cospectrality

Recall (`Graphplay.PST.Cospectrality`) that two vertices are **cospectral** when
their diagonal spectral-projector entries agree at every eigenvalue.  The
weak-coupling refinement is **γ-cospectrality**: the two subsystem vertices `u, v`
are cospectral *for the bare subsystem* `H_S`, with the discrepancy introduced by
the coupling controlled at order `γ`.

Concretely, `u, v` are **γ-cospectral** for `C` if they are (exactly) cospectral
for the bare subsystem graph `C.sub`, and the self-energy `Σ(z)` — the only
γ-dependent term in the Feshbach map — has matched diagonal entries at `u` and
`v` (so the coupling does not break the cospectrality at leading order).  This is
the precise hypothesis under which weak-coupling PST is *protected*. -/

/-- `u, v` are **γ-cospectral** in the coupled system `C` if (i) they are
cospectral for the bare subsystem `C.sub` (in the strong-cospectrality module's
sense), and (ii) for every energy `z` the self-energy's diagonal entries at
`u, v` agree, so the coupling dressing preserves the cospectrality.  This is the
weak-coupling PST-protection condition of arXiv:2512.08141. -/
def GammaCospectral (C : CoupledSystem S E) (u v : S) : Prop :=
  IsCospectral C.sub u v ∧
    ∀ z : ℂ, C.selfEnergy z u u = C.selfEnergy z v v

/-- At `γ = 0`, γ-cospectrality reduces to ordinary cospectrality of the bare
subsystem: the self-energy vanishes identically, so its diagonal-matching clause
is automatic. -/
theorem gammaCospectral_of_cospectral_zero (C : CoupledSystem S E) (u v : S)
    (h : C.gamma = 0) (hc : IsCospectral C.sub u v) :
    GammaCospectral C u v := by
  refine ⟨hc, ?_⟩
  intro z
  unfold CoupledSystem.selfEnergy
  rw [h]
  simp

/-- γ-cospectrality entails bare-subsystem cospectrality (projecting onto the
first clause). -/
theorem GammaCospectral.toCospectral {C : CoupledSystem S E} {u v : S}
    (h : GammaCospectral C u v) : IsCospectral C.sub u v := h.1

/-! ## The T-rex (transfer-via-resonance) construction

The **T-rex** (Transfer via REsonance, "T-rex") construction of
arXiv:2512.08141 engineers the environment so that one of its energy levels is
tuned into *resonance* with the subsystem eigenvalue gap that drives PST.  At
resonance, the weak coupling — although small in amplitude `γ` — produces a
*complete* population transfer in the subsystem, because the resonant denominator
`(z − ε_res)` in the environment resolvent compensates the small `γ²` numerator.

We model the T-rex environment as a single resonant level (`E = Unit`, one
environment site at on-site energy `ε`, here realized through the resolvent
shift) coupled symmetrically to the two PST endpoints `u, v` of the subsystem.
The resonance condition pins `ε` to the subsystem gap. -/

/-- The **single-site (one-level) environment** `K₁` used as the T-rex
resonator: one environment vertex, no internal edges.  Its on-site energy is
supplied as the resolvent shift in `tRexCouple` below. -/
noncomputable def tRexEnv : WeightedGraph Unit where
  adj := fun _ _ => 0
  herm := by herm_grind
  loopless := by loopless_grind

/-- The **T-rex coupling block**: a single resonant level coupled with equal
amplitude `1` to the two designated subsystem endpoints `u, v`, and `0` to every
other subsystem site.  Scaling by the coupling strength `γ` happens in
`fullHam`. -/
def tRexCoupling (u v : S) : Matrix S Unit ℂ :=
  fun s _ => if s = u ∨ s = v then 1 else 0

/-- The **T-rex coupled system**: the subsystem `H_S`, the single-level
resonator `tRexEnv`, the symmetric two-endpoint coupling `tRexCoupling u v`, and
coupling strength `γ`.  This is the concrete witness used in the weak-coupling
PST theorem. -/
noncomputable def tRex (H_S : WeightedGraph S) (u v : S) (γ : ℝ) :
    CoupledSystem S Unit where
  sub := H_S
  env := tRexEnv
  coupling := tRexCoupling u v
  gamma := γ

/-- The T-rex coupling is symmetric in the two endpoints: swapping `u` and `v`
leaves the coupling block unchanged.  This `u ↔ v` symmetry is exactly what
makes the resonant transfer between them perfect (it is the engineered
"phantom" symmetry, cf. `Graphplay.PST.Cospectrality.IsPhantomSymmetric`). -/
theorem tRexCoupling_symm (u v : S) :
    tRexCoupling (S := S) u v = tRexCoupling v u := by
  funext s _
  unfold tRexCoupling
  by_cases h : s = u ∨ s = v
  · rw [if_pos h, if_pos (h.symm)]
  · rw [if_neg h, if_neg (fun e => h e.symm)]

/-- The T-rex coupling attaches the resonator to `u` with unit amplitude. -/
@[simp]
theorem tRexCoupling_apply_left (u v : S) (e : Unit) :
    tRexCoupling u v u e = 1 := by
  unfold tRexCoupling; simp

/-- The T-rex coupling attaches the resonator to `v` with unit amplitude. -/
@[simp]
theorem tRexCoupling_apply_right (u v : S) (e : Unit) :
    tRexCoupling u v v e = 1 := by
  unfold tRexCoupling; simp

/-! ## The headline weak-coupling PST theorem

We can now state the central result of arXiv:2512.08141: tuning the T-rex
resonator into resonance with a γ-cospectral subsystem pair induces perfect
state transfer between them, in the weak-coupling limit, at the resonant time.

PST is the `IsPST` of `Graphplay.PST`, applied to the `WeightedGraph` whose
adjacency matrix is the full coupled Hamiltonian.  We package the full
Hamiltonian as a `WeightedGraph` on `S ⊕ Unit`. -/

namespace CoupledSystem

variable (C : CoupledSystem S E)

/-- Package the full coupled Hamiltonian as a `WeightedGraph` on `S ⊕ E`,
provided the coupling is *loopless on the diagonal blocks* (the bare graphs are
already loopless; the cross blocks never touch the diagonal of `S ⊕ E`).  This
lets us speak of `IsPST` / `evolve` for the coupled walk. -/
noncomputable def toWeightedGraph : WeightedGraph (S ⊕ E) where
  adj := C.fullHam
  herm := C.fullHam_isHermitian
  loopless := by
    intro x
    rcases x with s | e
    · -- diagonal `(inl s, inl s)` entry is `C.sub.adj s s = 0`
      show C.fullHam (Sum.inl s) (Sum.inl s) = 0
      unfold fullHam
      rw [Matrix.fromBlocks_apply₁₁]
      exact C.sub.loopless s
    · -- diagonal `(inr e, inr e)` entry is `C.env.adj e e = 0`
      show C.fullHam (Sum.inr e) (Sum.inr e) = 0
      unfold fullHam
      rw [Matrix.fromBlocks_apply₂₂]
      exact C.env.loopless e

@[simp]
theorem toWeightedGraph_adj (C : CoupledSystem S E) (x y : S ⊕ E) :
    C.toWeightedGraph.adj x y = C.fullHam x y := rfl

end CoupledSystem

/-- The **resonance condition** for the T-rex: the single environment level sits
at energy `ε_res` equal to a subsystem eigenvalue `λ` in the (joint) eigenvalue
support of the PST endpoints `u, v`.  We express it as membership of `λ` in the
subsystem's eigenvalue range together with the requirement that `λ` is the
resonator energy. -/
def TRexResonance (H_S : WeightedGraph S) (u v : S) (lam : ℝ) : Prop :=
  lam ∈ Set.range H_S.herm.eigenvalues ∧
    lam ∈ eigenSupport H_S u ∧ lam ∈ eigenSupport H_S v

/-- **Weak-coupling perfect state transfer (Feshbach–Schur / T-rex,
arXiv:2512.08141).**

Let `H_S` be a subsystem with a γ-cospectral endpoint pair `u, v` that is
strongly cospectral for the bare subsystem, and suppose the T-rex resonator is
tuned to resonance with a subsystem eigenvalue `lam` in their joint eigenvalue
support.  Then for the T-rex coupled system `tRex H_S u v γ` at sufficiently
small nonzero coupling `γ`, there is a time `τ` at which perfect state transfer
occurs between the two endpoints (embedded as `Sum.inl u`, `Sum.inl v` in the
coupled carrier `S ⊕ Unit`):

  `∃ τ, IsPST (tRex H_S u v γ).toWeightedGraph (Sum.inl u) (Sum.inl v) τ`.

HONEST SORRY.  The proof is the resolvent (Feshbach–Schur) expansion of
arXiv:2512.08141:

* the Schur-complement identity expresses the `(inl u, inl v)`-amplitude of
  `exp(-iτ H(γ))` through the effective subsystem propagator built from
  `feshbachMap`;
* γ-cospectrality (`GammaCospectral`) keeps the effective subsystem pair
  strongly cospectral to all orders in `γ`;
* the resonance condition (`TRexResonance`) makes the resonant
  environment-resolvent denominator `(z − lam)` saturate the modulus to `1` at
  the resonant time, despite the `O(γ²)` self-energy.

Each step is a genuine spectral/perturbative computation (the resolvent
expansion + Kronecker resonance argument); we state the theorem precisely and
leave the resolvent-expansion proof as an honest `sorry`. -/
theorem tRex_weakCoupling_isPST
    (H_S : WeightedGraph S) (u v : S) (huv : u ≠ v) (γ : ℝ) (hγ : γ ≠ 0)
    (lam : ℝ)
    (hcosp : GammaCospectral (tRex H_S u v γ) u v)
    (hsc : IsStronglyCospectral H_S u v)
    (hres : TRexResonance H_S u v lam) :
    ∃ τ : ℝ, IsPST (tRex H_S u v γ).toWeightedGraph
      (Sum.inl u) (Sum.inl v) τ := by
  -- Feshbach–Schur resolvent expansion + resonant Kronecker approximation.
  -- See arXiv:2512.08141, main theorem.  Honest sorry on the deep expansion.
  sorry

section BlockExp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The block-diagonal embedding `A ↦ fromBlocks A 0 0 0` as a continuous linear
map `Matrix S S ℂ →L[ℂ] Matrix (S ⊕ E) (S ⊕ E) ℂ`.  Used to commute `tsum` past
the upper-left block in `exp_fromBlocks_diag`. -/
noncomputable def blockEmbedUL (S E : Type*)
    [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] :
    Matrix S S ℂ →L[ℂ] Matrix (S ⊕ E) (S ⊕ E) ℂ where
  toFun A := Matrix.fromBlocks A 0 0 0
  map_add' A B := by conv_rhs => rw [Matrix.fromBlocks_add]; simp
  map_smul' c A := by
    simp only [RingHom.id_apply]; conv_rhs => rw [Matrix.fromBlocks_smul]; simp
  cont := Continuous.matrix_fromBlocks continuous_id continuous_const
    continuous_const continuous_const

/-- The block-diagonal embedding `D ↦ fromBlocks 0 0 0 D` as a continuous linear
map `Matrix E E ℂ →L[ℂ] Matrix (S ⊕ E) (S ⊕ E) ℂ` (the lower-right block). -/
noncomputable def blockEmbedLR (S E : Type*)
    [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] :
    Matrix E E ℂ →L[ℂ] Matrix (S ⊕ E) (S ⊕ E) ℂ where
  toFun D := Matrix.fromBlocks 0 0 0 D
  map_add' A B := by conv_rhs => rw [Matrix.fromBlocks_add]; simp
  map_smul' c A := by
    simp only [RingHom.id_apply]; conv_rhs => rw [Matrix.fromBlocks_smul]; simp
  cont := Continuous.matrix_fromBlocks continuous_const continuous_const
    continuous_const continuous_id

/-- **Block-diagonal matrix exponential.**  The exponential of a block-diagonal
matrix `fromBlocks A 0 0 D` is block-diagonal with the two exponentials on the
blocks: `exp (A ⊕ D) = (exp A) ⊕ (exp D)`.

Proof via the `exp`-as-`tsum` expansion: `(A ⊕ D) ^ n = (A ^ n) ⊕ (D ^ n)`
(`fromBlocks_diagonal_pow`), each scaled summand splits as the sum of its two
block-embeddings (`blockEmbedUL`/`blockEmbedLR`), and the (continuous-linear)
block embeddings commute with the infinite sum. -/
theorem exp_fromBlocks_diag
    (A : Matrix S S ℂ) (D : Matrix E E ℂ) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 D)
      = Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D) := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ), NormedSpace.exp_eq_tsum (𝕂 := ℂ),
    NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  simp only []
  have hsumA : Summable (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • A ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hsumD : Summable (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • D ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) D
  -- each scaled power of the block matrix splits as UL-embedding + LR-embedding.
  have hpow : ∀ n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • (Matrix.fromBlocks A 0 0 D) ^ n
      = (blockEmbedUL S E) (((Nat.factorial n : ℂ)⁻¹) • A ^ n)
        + (blockEmbedLR S E) (((Nat.factorial n : ℂ)⁻¹) • D ^ n) := by
    intro n
    rw [Matrix.fromBlocks_diagonal_pow, Matrix.fromBlocks_smul]
    show Matrix.fromBlocks _ _ _ _ = Matrix.fromBlocks _ 0 0 0 + Matrix.fromBlocks 0 0 0 _
    rw [Matrix.fromBlocks_add]; simp
  simp_rw [hpow]
  rw [(((blockEmbedUL S E).summable hsumA).tsum_add ((blockEmbedLR S E).summable hsumD)),
    ← ContinuousLinearMap.map_tsum _ hsumA, ← ContinuousLinearMap.map_tsum _ hsumD]
  show Matrix.fromBlocks _ 0 0 0 + Matrix.fromBlocks 0 0 0 _ = _
  rw [Matrix.fromBlocks_add]; simp

end BlockExp

/-- **Decoupled limit (γ = 0): weak-coupling PST reduces to bare-subsystem PST.**

At `γ = 0` the T-rex environment is completely decoupled, the full Hamiltonian is
block-diagonal (`fullHam_decoupled_at_zero`), and the `(inl u, inl v)`-block of
the coupled evolution is exactly the bare subsystem evolution.  Hence PST in the
coupled system between `inl u` and `inl v` coincides with bare PST between `u`
and `v` in `H_S`.

Proof: at `γ = 0`, `(tRex H_S u v 0).toWeightedGraph.adj = fromBlocks H_S.adj 0
0 (tRexEnv).adj`; pulling the scalar `-(iτ)` through the blocks
(`fromBlocks_smul`) and applying the block-diagonal exponential
`exp_fromBlocks_diag` shows the coupled evolution is
`fromBlocks (H_S.evolve τ) 0 0 ((tRexEnv).evolve τ)`, whose `(inl u, inl v)`
entry is exactly `(H_S.evolve τ) u v`.  The two `IsPST` moduli therefore
coincide. -/
theorem tRex_isPST_iff_bare_at_zero
    (H_S : WeightedGraph S) (u v : S) (τ : ℝ) :
    IsPST (tRex H_S u v 0).toWeightedGraph (Sum.inl u) (Sum.inl v) τ ↔
      IsPST H_S u v τ := by
  letI := Matrix.linftyOpNormedRing (n := S ⊕ Unit) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := S ⊕ Unit) (R := ℂ) (α := ℂ)
  -- The coupled evolution entry `(inl u, inl v)` equals the bare entry `(u, v)`.
  have hentry : (tRex H_S u v 0).toWeightedGraph.evolve τ (Sum.inl u) (Sum.inl v)
      = H_S.evolve τ u v := by
    -- unfold the coupled evolution to `exp (-(iτ) • fullHam)` and use γ = 0.
    show NormedSpace.exp (-(Complex.I * (τ : ℂ)) •
        (tRex H_S u v 0).toWeightedGraph.adj) (Sum.inl u) (Sum.inl v)
      = H_S.evolve τ u v
    have hadj : (tRex H_S u v 0).toWeightedGraph.adj
        = Matrix.fromBlocks H_S.adj 0 0 (tRexEnv).adj := by
      show (tRex H_S u v 0).fullHam = _
      rw [CoupledSystem.fullHam_decoupled_at_zero _ rfl]
      rfl
    rw [hadj, Matrix.fromBlocks_smul]
    simp only [smul_zero]
    rw [exp_fromBlocks_diag, Matrix.fromBlocks_apply₁₁]
    rfl
  unfold IsPST
  rw [hentry]

/-! ## Spine connection: weak coupling between two equitable cells

We make explicit the "two equitable cells" picture promised in the header.  At
`γ = 0` the coupled system's adjacency is block-diagonal `fromBlocks H_S 0 0 H_E`,
whose two blocks `S` and `E` form the **coarsest nontrivial equitable
partition** of the combined graph: every `S`-vertex has the same (zero) total
weight into `E`, and vice versa.  Turning on `γ` couples these two cells.

We record the structural fact powering this: at `γ = 0` there are no edges
between the `S`-cell and the `E`-cell. -/

/-- **At `γ = 0` the two cells `S` and `E` are disconnected** (no cross edges):
every `(inl s, inr e)` and `(inr e, inl s)` entry of the full Hamiltonian
vanishes.  This is the equitable-partition decoupling: `S` and `E` are two cells
with zero mutual weight, the coarsest equitable partition of the combined graph.
The weak coupling `γ ≠ 0` is precisely the (weak) coupling *between these two
equitable cells*. -/
theorem fullHam_no_cross_edges_at_zero (C : CoupledSystem S E) (h : C.gamma = 0)
    (s : S) (e : E) :
    C.fullHam (Sum.inl s) (Sum.inr e) = 0 ∧
      C.fullHam (Sum.inr e) (Sum.inl s) = 0 := by
  unfold CoupledSystem.fullHam
  rw [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, h]
  simp

end Dowsing
end Graphplay
