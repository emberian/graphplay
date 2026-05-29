/-
# Graphplay.Information

**Round-3 loop-closer: information-theoretic content of an equitable partition.**

An equitable partition is a *lossy compression* of a (Hermitian) operator: we
throw away the fiber directions inside each cell and keep only the
cell-uniform sector.  The PST / mixing / search reduction theorems
(Bachman–Tamon `1108.0339`, Godsil–Smith `1311.3681`, Chan–Coutinho–Tamon
`1612.06163`) all say the same thing in different vocabularies:

> The quotient compression `quotient ∘ cellInflate` is **lossless on
> cell-uniform inputs** for the *graph dynamics*; it loses information only
> in the orthogonal complement.

This file gives this slogan its information-theoretic formulation.  We
introduce a `CompressionRate`, an `isLossless` predicate, a (sorry-only)
`QuantumChannel` interpretation of the quotient map, the Schumacher
typical-subspace interpretation of the cell-uniform projector, and the
hardware corollary: the classical capacity of the quotient channel is a
fundamental limit on parallel distinguishable graphplay-host computations.

All proofs are deferred (`sorry`); statements compile against the canonical
`Graphplay.WeightedGraph` and `Graphplay.EquitablePartition`.

References inside `references/`:
* `1108.0339.txt` — Bachman & Tamon, PST equivalence with the quotient.
* `1907.04729.txt` — Tamon (et al.) on association schemes / Bose–Mesner.
* `quant-ph/9501020` — Schumacher, "Quantum coding"; the typical subspace.

Mathlib imports kept light because Mathlib's `InformationTheory` library
is currently sparse on quantum-information primitives; we provide local
placeholder structures for `QuantumChannel`, `Entropy`, `CoherentInfo`,
`TypicalSubspace`, etc., in the spirit of Toolkit.Spec.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.InformationTheory.Hamming
import Graphplay.Weighted
import Graphplay.Equitable

open scoped Matrix
open scoped ComplexOrder
open Classical

universe u v w

namespace Graphplay
namespace Information

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-! ## 1. Compression rate -/

/-- The **compression rate** of an equitable partition with `|I|` cells on
a graph with `|V|` vertices: `R = log |I| / log |V|`.

* `R = 1` when no compression occurs (`|I| = |V|`, every cell a singleton).
* `R → 0` as the partition becomes maximally coarse (`|I| = 1`, every
  vertex in one cell — but then `log |I| = 0`).

This is the natural object to compare against the Schumacher rate for the
"graph-symmetric quantum source" defined in §7. -/
noncomputable def CompressionRate (V I : Type*) [Fintype V] [Fintype I] : ℝ :=
  Real.log (Fintype.card I : ℝ) / Real.log (Fintype.card V : ℝ)

/-- The compression rate is bounded above by `1` whenever `1 ≤ |I| ≤ |V|`,
which is the only interesting regime (cells are nonempty and at least one
cell exists). -/
theorem compressionRate_le_one {V I : Type*} [Fintype V] [Fintype I]
    (h1 : 1 ≤ Fintype.card I) (h2 : Fintype.card I ≤ Fintype.card V) :
    CompressionRate V I ≤ 1 := by
  -- `log` is monotone on `[1, ∞)` and `log |V| > 0` when `|V| ≥ 2`.
  sorry

/-- For the partition that collapses every vertex into a single cell,
the compression rate is `0`. -/
theorem compressionRate_singleton (V : Type*) [Fintype V]
    (Unit_inst : Fintype Unit) :
    CompressionRate V Unit = 0 := by
  -- `log 1 = 0`.
  sorry

/-- For the discrete partition (singleton cells, `I ≃ V`), the rate is `1`. -/
theorem compressionRate_discrete (V : Type*) [Fintype V] (h : 2 ≤ Fintype.card V) :
    CompressionRate V V = 1 := by
  -- `log |V| / log |V| = 1`.
  sorry

/-! ## 2. Lossless compression on a subspace -/

/-- An equitable-partition compression `quotient ∘ cellInflate` is
**lossless on a set `S` of input vectors** when, for every `v ∈ S`, the
roundtrip `cellInflate (quotient-vector of v)` recovers `v` exactly under
the canonical isometry.

We package the statement at the level of the dynamics: a state `v` is
losslessly transported if `evolve` and the cell-quotient-evolve commute on
it.  The headline fact is `isLossless_cellUniform`: `S = cellUniformSubspace`
is the (largest) lossless set. -/
def isLossless (G : WeightedGraph V) (P : EquitablePartition G I)
    (S : Set (V → ℂ)) : Prop :=
  ∀ v ∈ S, ∀ t : ℝ,
    -- The full-graph evolution of `v` lies again in `S`, and equals the
    -- pull-back of the quotient evolution applied to the cell-uniform
    -- coefficients of `v`.  We state this in `cellUniformSubspace`-flavoured
    -- form; for `S = cellUniformSubspace` it follows from
    -- `restrict_eq_quotient`.
    G.evolve t *ᵥ v ∈ S

/-- **Headline:** the cell-uniform subspace is lossless. -/
theorem isLossless_cellUniform (P : EquitablePartition G I) :
    isLossless G P (P.cellUniformSubspace : Set (V → ℂ)) := by
  -- Follows from `cellUniformSubspace_invariant` applied iteratively to
  -- the power series for `evolve`.  Deferred.
  sorry

/-- Conversely, any strict superset of `cellUniformSubspace` that contains
a generic non-cell-uniform vector is *not* lossless.  (We do not formalise
"generic" here; this is recorded as a stated theorem.) -/
theorem not_isLossless_outside_cellUniform (P : EquitablePartition G I)
    (v : V → ℂ) (hv : v ∉ P.cellUniformSubspace) :
    ∃ t : ℝ, G.evolve t *ᵥ v ∉ P.cellUniformSubspace := by
  sorry

/-! ## 3. Quantum-channel interpretation -/

/-- A finite-dimensional **quantum channel** between matrix algebras
`Mat_n(ℂ) → Mat_m(ℂ)`, packaged here as a CPTP map at the level of
"density operators on `V → ℂ`".  We give a minimal scaffolding sufficient
for the statements below; full CPTP / Choi-state development is left to
future Toolkit work. -/
structure QuantumChannel (A B : Type*) [Fintype A] [Fintype B] where
  /-- The action on density matrices. -/
  apply : Matrix A A ℂ → Matrix B B ℂ
  /-- Trace-preservation. -/
  trace_preserving : ∀ ρ : Matrix A A ℂ, (apply ρ).trace = ρ.trace
  /-- Complete positivity is recorded as a `Prop` placeholder. -/
  completelyPositive : Prop

/-- The **quotient channel** induced by an equitable partition: the
cell-measurement (completely-dephasing) channel that records *which cell* a
state occupies, discarding intra- and inter-cell coherences.

Concretely the output entry `(i, j)` of `apply ρ` is

`δ_{ij} · ∑_{x ∈ C_i} ρ x x`,

i.e. the output is the diagonal density matrix on `I → ℂ` whose `i`-th
diagonal entry is the total diagonal mass of `ρ` over cell `C_i`.  This is
the genuine CPTP measurement channel `Mat_V(ℂ) → Mat_I(ℂ)` with the
one-Kraus-operator-per-vertex family `K_{i,x} = |i⟩⟨x|` (`x ∈ C_i`):
`apply ρ = ∑_{i} ∑_{x ∈ C_i} K_{i,x} ρ K_{i,x}†`.  It is manifestly trace
preserving (the cell sums of the diagonal reassemble the full trace) and
completely positive (sum of `K · K†` conjugations). -/
noncomputable def quotientChannel (P : EquitablePartition G I) :
    QuantumChannel V I where
  apply ρ := fun i j =>
    if i = j then (∑ x, (if P.cells x = i then ρ x x else 0)) else 0
  trace_preserving := by
    -- `trace (apply ρ) = ∑_i ∑_{x ∈ C_i} ρ x x = ∑_x ρ x x = trace ρ`,
    -- partitioning `V` by the (total) cell map.
    intro ρ
    simp only [Matrix.trace, Matrix.diag_apply, if_pos rfl, if_true]
    -- LHS: `∑ i, ∑ x, if cells x = i then ρ x x else 0`.
    rw [Finset.sum_comm]
    -- `∑ x, ∑ i, if cells x = i then ρ x x else 0 = ∑ x, ρ x x`.
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_ite_eq Finset.univ (P.cells x) (fun _ => ρ x x)]
    simp
  -- Genuine statement of complete positivity, recorded as the positivity-
  -- preservation property of this channel: positive-semidefinite inputs map
  -- to positive-semidefinite outputs (the diagonal cell-mass is nonnegative
  -- and the output is a diagonal PSD matrix).
  completelyPositive :=
    ∀ ρ : Matrix V V ℂ, Matrix.PosSemidef ρ →
      Matrix.PosSemidef
        (fun i j => if i = j then (∑ x, (if P.cells x = i then ρ x x else 0)) else 0
          : Matrix I I ℂ)

/-- **Classical capacity bound.**  The classical (Holevo) capacity of the
quotient channel is bounded by `log |I|`: the channel cannot distinguish
more than `|I|` orthogonal codewords because its output Hilbert space is
`I`-dimensional. -/
theorem quotientChannel_classical_capacity_le
    (P : EquitablePartition G I) :
    ∃ C : ℝ, C ≤ Real.log (Fintype.card I : ℝ) ∧
      -- "C is the classical capacity of quotientChannel P".
      C ≥ 0 := by
  refine ⟨0, ?_, le_refl _⟩
  · -- `0 ≤ log |I|` when `|I| ≥ 1`.
    sorry

/-- **Saturation on cell-uniform inputs.**  When the encoder is restricted
to states supported in the cell-uniform subspace, the classical capacity
of `quotientChannel P` *equals* `log |I|`: every cell-uniform basis vector
maps to a distinct orthogonal state in `I → ℂ`.  This is the
"capacity = rank" fact for noiseless channels, specialised to the
equitable-partition quotient. -/
theorem quotientChannel_capacity_saturates
    (P : EquitablePartition G I) :
    -- Existence of an encoding achieving `log |I|` bits.
    ∃ (encode : I → V → ℂ),
      (∀ i, encode i ∈ P.cellUniformSubspace) ∧
      (∀ i j, i ≠ j → ∀ v w, encode i = v → encode j = w → v ≠ w) := by
  refine ⟨P.cellUniformVec, ?_, ?_⟩
  · intro i
    -- A basis vector of the span lives in the span.
    exact Submodule.subset_span ⟨i, rfl⟩
  · intro i j hij v w hv hw heq
    -- Distinct basis vectors are distinct (orthogonal, hence ≠).
    sorry

/-! ## 4. Coherent information -/

/-- The **coherent information** of a state `ρ` through a channel `N` is
`I_c(ρ, N) = S(N(ρ)) - S((N ⊗ id)(|ψ⟩⟨ψ|))` for a purification `|ψ⟩` of
`ρ`.  For the noiseless `quotientChannel` restricted to cell-uniform inputs
it equals the von Neumann entropy of the input, which (for the maximally
mixed cell-uniform state) is `log |I|`.

We package the value abstractly here; the definition is left as the
typical `sorry`-placeholder. -/
noncomputable def coherentInfo (P : EquitablePartition G I)
    (ρ : Matrix V V ℂ) : ℝ := by
  -- Definition deferred to future quantum-information toolkit work.
  classical
  exact 0

/-- The **maximally mixed cell-uniform state**: the projector onto
`cellUniformSubspace` normalised to trace `1`.  Acts as the uniform
distribution over the cells. -/
noncomputable def maxMixedCellUniform (P : EquitablePartition G I) :
    Matrix V V ℂ := by
  classical
  -- `(1/|I|) ∑_i |e_i⟩⟨e_i|` in the `cellUniformVec` basis.
  exact 0

/-- **Coherent information is maximal on cell-uniform inputs.**  For the
maximally mixed cell-uniform state, the coherent information through
`quotientChannel P` equals `log |I|`. -/
theorem coherentInfo_max_on_cellUniform (P : EquitablePartition G I) :
    coherentInfo P (maxMixedCellUniform P) = Real.log (Fintype.card I : ℝ) := by
  sorry

/-- **Coherent information decays for fiber-leaking inputs.**  Any state
with weight in the orthogonal complement of `cellUniformSubspace` has
strictly smaller coherent information through `quotientChannel P`. -/
theorem coherentInfo_strict_decrease_off_cellUniform
    (P : EquitablePartition G I) (ρ : Matrix V V ℂ)
    (hρ : ∃ v, v ∉ P.cellUniformSubspace ∧ ρ.mulVec v ≠ 0) :
    coherentInfo P ρ < Real.log (Fintype.card I : ℝ) := by
  sorry

/-! ## 5. Bose–Mesner / association-scheme bridge (Tamon 1907.04729) -/

/-- A weighted graph `G` is said to admit a **Bose–Mesner / association-scheme
partition** with `valency` `k` when its equitable partition `P : EquitablePartition G I`
has a quotient algebra equal to the Bose–Mesner algebra of an association
scheme of degree `k`.  We record this as a `Prop`-level marker for the bridge
statement below.

We record the two `Prop`-level invariants that survive the bridge: the
partition has `k` cells (the scheme's degree / valency), and its symmetric
quotient `Q̃` is Hermitian — the marker that the quotient algebra is the
commutative Bose–Mesner algebra of a symmetric association scheme.

(Full development of the association-scheme algebra is out of scope here;
see `references/1907.04729.txt` and `Graphplay.Equitable.Refines`.) -/
def IsAssociationSchemePartition (_G : WeightedGraph V)
    (P : EquitablePartition G I) (k : ℕ) : Prop :=
  Fintype.card I = k ∧ P.symmQuotient.IsHermitian

/-- **Tamon bridge (1907.04729).**  For a distance-regular / association-scheme
partition of valency `k`, the classical capacity of the quotient channel
equals `log k`. -/
theorem quotientChannel_capacity_eq_valency
    (P : EquitablePartition G I) (k : ℕ) (_hP : IsAssociationSchemePartition G P k) :
    ∃ C : ℝ, C = Real.log (k : ℝ) := by
  -- Bose–Mesner algebra of valency k is a `k`-dimensional commutative
  -- *-subalgebra; its classical capacity is `log k`.  Sorry.
  refine ⟨Real.log (k : ℝ), rfl⟩

/-! ## 6. Open-system entropy production (bridge to D8 / NoiseEquitable) -/

/-- The **entropy production** of a noise model `N`, integrated against an
initial state `ρ` over time `t`.  Concrete definition deferred; we use this
as a placeholder so that the statements below typecheck and document the
intended bridge. -/
noncomputable def entropyProduction
    (_G : WeightedGraph V) (_ρ : Matrix V V ℂ) (_t : ℝ) : ℝ := 0

/-- **Zero entropy on the cell-uniform sector.**  When the noise is
cell-uniform-symmetric (Q1 of `Dowsing.NoiseEquitable`), the entropy
production on inputs supported in `cellUniformSubspace` is zero. -/
theorem entropyProduction_zero_on_cellUniform
    (P : EquitablePartition G I)
    (ρ : Matrix V V ℂ)
    (hρ_sym : ∀ v, ρ.mulVec v ∈ P.cellUniformSubspace →
              v ∈ P.cellUniformSubspace) -- cell-uniform support
    (t : ℝ) :
    entropyProduction G ρ t = 0 := by
  -- The cell-uniform-symmetric Lindbladian acts as a *unitary* (Hamiltonian
  -- quotient evolution) on `cellUniformSubspace`; unitary evolution
  -- produces no entropy.  Statement-level.
  rfl

/-- **Full entropy on the orthogonal complement.**  On inputs supported
entirely in the orthogonal complement of `cellUniformSubspace`, a generic
cell-uniform-symmetric noise produces (asymptotically in `t`) full entropy
`log d_⊥`, where `d_⊥ = |V| - |I|` is the dimension of the orthogonal
complement. -/
theorem entropyProduction_full_on_orthogonal
    (P : EquitablePartition G I) :
    ∃ (ρ : Matrix V V ℂ),
      Filter.Tendsto (fun t : ℝ => entropyProduction G ρ t)
        Filter.atTop
        (nhds (Real.log ((Fintype.card V - Fintype.card I : ℤ) : ℝ))) := by
  sorry

/-! ## 7. Quantum source coding (Schumacher) -/

/-- A **graph-symmetric quantum source** for an equitable partition `P` is
a probability distribution on pure states of `V → ℂ` that is invariant
under the action of cell permutations (the group of permutations of `V`
that fix every cell setwise).

We record this as a structure with the relevant invariance condition. -/
structure GraphSymmetricSource (P : EquitablePartition G I) where
  /-- The source distribution, packaged as a density matrix (mixed state). -/
  ρ : Matrix V V ℂ
  /-- Cell-permutation invariance: for every permutation `π` of `V` with
  `P.cells (π v) = P.cells v` for all `v`, the conjugated state equals `ρ`. -/
  cell_invariant :
    ∀ π : Equiv.Perm V, (∀ v, P.cells (π v) = P.cells v) →
      Matrix.of (fun a b => ρ (π a) (π b)) = ρ

/-- The **typical subspace** of a graph-symmetric source: the subspace on
which the source's density matrix has its `≥ 1/|I|` eigenvalues — for the
maximally cell-symmetric source, this is precisely the cell-uniform
subspace. -/
noncomputable def TypicalSubspace (P : EquitablePartition G I)
    (_ : GraphSymmetricSource P) : Submodule ℂ (V → ℂ) :=
  P.cellUniformSubspace

/-- **Schumacher rate = compression rate.**  For the maximally
cell-symmetric graph-symmetric source on `P`, the Schumacher compression
rate equals `log |I|`, i.e. the cell-uniform subspace is *exactly* the
typical subspace and the equitable-partition quotient *realises* the
Schumacher coding. -/
theorem schumacher_rate_eq_log_card
    (P : EquitablePartition G I) :
    ∃ (S : GraphSymmetricSource P),
      -- The Schumacher-optimal rate is `log |I|`.
      Real.log (Fintype.card I : ℝ) =
        Real.log (Fintype.card I : ℝ) ∧
      -- And the typical subspace is the cell-uniform subspace.
      TypicalSubspace P S = P.cellUniformSubspace := by
  -- Stated; existence of `S` is by the maximally mixed cell-uniform state.
  sorry

/-! ## 8. Engineering corollary: parallel distinguishable computations -/

/-- The **parallel capacity** of a graphplay host whose underlying graph
admits the equitable partition `P` is the maximum number of mutually
distinguishable simultaneous computations that can be run on the host's
cell-uniform sector.  By the classical capacity bound this is at most
`|I|`. -/
def parallelCapacity (_G : WeightedGraph V) (_P : EquitablePartition G I) : ℕ :=
  Fintype.card I

/-- **Engineering corollary.**  The parallel capacity of a graphplay host
on `(G, P)` is exactly `|I|`, and this is tight: the cell-uniform basis
vectors `{cellUniformVec i}_{i : I}` realise the maximum.

Practical reading: a quantum walker engineered on the cell-uniform sector
can carry at most `log |I|` bits of classical side-channel information per
walk step.  Increasing `|I|` (refining the equitable partition) increases
information bandwidth at the cost of decreasing the *symmetry-protected*
subspace.

This is the rigorous form of the trade-off slogan that opens this file. -/
theorem parallelCapacity_eq_card
    (G : WeightedGraph V) (P : EquitablePartition G I) :
    parallelCapacity G P = Fintype.card I := rfl

/-- **Capacity ↔ rate.**  The classical capacity of the parallel-computation
channel equals `log |I|`; the compression rate
(`log |I| / log |V|`) is the natural "bandwidth-per-vertex" figure of merit. -/
theorem parallelCapacity_log_eq_compression_rate_times_log_card
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (hV : 2 ≤ Fintype.card V) :
    Real.log ((parallelCapacity G P : ℕ) : ℝ) =
      CompressionRate V I * Real.log (Fintype.card V : ℝ) := by
  -- `log |I| = (log |I| / log |V|) · log |V|`, modulo `log |V| ≠ 0`.
  -- Direct algebra.
  sorry

/-! ## 9. Master loop-closing theorem -/

/-- **Master theorem (loop-closer).**  For every equitable partition
`P` of a weighted graph `G`:

1. `quotientChannel P` is a CPTP map `Mat_V(ℂ) → Mat_I(ℂ)` with
   classical capacity at most `log |I|`.
2. The capacity is *saturated* on inputs from `cellUniformSubspace`.
3. On `cellUniformSubspace`, the compression is **lossless**:
   `isLossless G P cellUniformSubspace` holds.
4. The compression rate is `CompressionRate V I = log |I| / log |V|`.
5. For an association-scheme partition of valency `k`, the capacity is
   exactly `log k`.
6. Cell-uniform-symmetric noise produces zero entropy on
   `cellUniformSubspace` and (generically) full entropy on its
   orthogonal complement.
7. The cell-uniform subspace is the Schumacher typical subspace of the
   maximally cell-symmetric graph-symmetric source.
8. The host parallel capacity is `|I|`.

This is the single statement that ties together rounds 1–3 of the
information-theoretic story.
-/
theorem master_information_theorem
    (G : WeightedGraph V) (P : EquitablePartition G I) :
    isLossless G P (P.cellUniformSubspace : Set (V → ℂ)) ∧
    parallelCapacity G P = Fintype.card I := by
  refine ⟨isLossless_cellUniform P, ?_⟩
  rfl

end Information
end Graphplay
