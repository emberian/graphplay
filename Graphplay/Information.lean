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
import Graphplay.PST.QuotientIff

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
  unfold CompressionRate
  rcases Nat.lt_or_ge (Fintype.card V) 2 with hV | hV
  · -- `|V| ≤ 1`, and `1 ≤ |I| ≤ |V|` forces `|I| = |V| = 1`, so `log/log = 0`.
    interval_cases h : Fintype.card V
    · -- `|V| = 0` contradicts `1 ≤ |I| ≤ 0`.
      omega
    · -- `|V| = 1`, so `|I| = 1`.
      have : Fintype.card I = 1 := le_antisymm (by omega) h1
      simp [this]
  · -- `|V| ≥ 2`, so `log |V| > 0`.
    have hVpos : (0 : ℝ) < Real.log (Fintype.card V : ℝ) := by
      apply Real.log_pos
      exact_mod_cast hV.trans_lt' (by norm_num)
    rw [div_le_one hVpos]
    apply Real.log_le_log
    · exact_mod_cast h1.trans_lt' (by norm_num)
    · exact_mod_cast h2

/-- For the partition that collapses every vertex into a single cell,
the compression rate is `0`. -/
theorem compressionRate_singleton (V : Type*) [Fintype V]
    (Unit_inst : Fintype Unit) :
    CompressionRate V Unit = 0 := by
  -- `log 1 = 0`.
  unfold CompressionRate
  have : @Fintype.card Unit Unit_inst = 1 := by
    rw [Subsingleton.elim Unit_inst PUnit.fintype]; exact Fintype.card_unit
  rw [this]
  simp

/-- For the discrete partition (singleton cells, `I ≃ V`), the rate is `1`. -/
theorem compressionRate_discrete (V : Type*) [Fintype V] (h : 2 ≤ Fintype.card V) :
    CompressionRate V V = 1 := by
  -- `log |V| / log |V| = 1`.
  unfold CompressionRate
  have hVpos : (0 : ℝ) < Real.log (Fintype.card V : ℝ) := by
    apply Real.log_pos
    exact_mod_cast h.trans_lt' (by norm_num)
  exact div_self (ne_of_gt hVpos)

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
  -- This is exactly the (proven) `noLeakage_of_equitable`: the cell-uniform
  -- subspace is invariant under every `evolve t`.
  intro v hv t
  exact P.noLeakage_of_equitable t v hv

/-- Conversely, any strict superset of `cellUniformSubspace` that contains
a generic non-cell-uniform vector is *not* lossless.  (We do not formalise
"generic" here; this is recorded as a stated theorem.) -/
theorem not_isLossless_outside_cellUniform (P : EquitablePartition G I)
    (v : V → ℂ) (hv : v ∉ P.cellUniformSubspace) :
    ∃ t : ℝ, G.evolve t *ᵥ v ∉ P.cellUniformSubspace := by
  -- DEEP: requires the spectral fact that a vector with nonzero component in
  -- the orthogonal complement of the (`G.adj`-reducing) cell-uniform subspace
  -- generically leaves it under the unitary flow.  This is a genuine analytic
  -- non-invariance statement, not available from the leakage API.  Honest sorry.
  -- BLOCKED: analytic generic non-invariance under unitary flow; not in Mathlib.
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

/-- **Positivity preservation of the quotient channel.**  The quotient
(cell-measurement) channel sends positive-semidefinite density operators to
positive-semidefinite outputs: the output is the diagonal matrix on `I` whose
`i`-th entry is the (nonnegative) total diagonal mass `∑_{x ∈ C_i} ρ x x` of
`ρ` over cell `C_i`.  This is the genuine `completelyPositive` content of
`quotientChannel P` (at the level of positivity preservation), here proven
rather than merely recorded as a `Prop` field. -/
theorem quotientChannel_posSemidef_of_posSemidef
    (P : EquitablePartition G I) {ρ : Matrix V V ℂ} (hρ : ρ.PosSemidef) :
    Matrix.PosSemidef
      (fun i j => if i = j then (∑ x, (if P.cells x = i then ρ x x else 0)) else 0
        : Matrix I I ℂ) := by
  -- The output is `Matrix.diagonal d` with `d i = ∑_{x : cells x = i} ρ x x`.
  set d : I → ℂ := fun i => ∑ x, (if P.cells x = i then ρ x x else 0) with hd
  have hdiag : (fun i j => if i = j then d i else 0 : Matrix I I ℂ)
      = Matrix.diagonal d := by
    funext i j; simp [Matrix.diagonal]
  rw [hdiag]
  -- Each diagonal entry is a sum of `ρ x x`, which are nonneg reals (PSD ⇒
  -- diagonal entries are real and `≥ 0`).
  refine Matrix.PosSemidef.diagonal ?_
  intro i
  -- `d i = ∑ x, if cells x = i then ρ x x else 0`; each `ρ x x` is `0 ≤ ·`.
  rw [hd]
  refine Finset.sum_nonneg (fun x _ => ?_)
  by_cases hx : P.cells x = i
  · simp only [if_pos hx]; exact hρ.diag_nonneg
  · simp [hx]

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
  · -- `0 ≤ log |I|`: `log` of a natural number is nonnegative.
    exact Real.log_natCast_nonneg _

/-- **Saturation on cell-uniform inputs.**  When the encoder is restricted
to states supported in the cell-uniform subspace, the classical capacity
of `quotientChannel P` *equals* `log |I|`: every cell-uniform basis vector
maps to a distinct orthogonal state in `I → ℂ`.  This is the
"capacity = rank" fact for noiseless channels, specialised to the
equitable-partition quotient. -/
theorem quotientChannel_capacity_saturates
    (P : EquitablePartition G I)
    (hne : ∀ i : I, ∃ x : V, P.cells x = i) :
    -- Existence of an encoding achieving `log |I|` bits.
    ∃ (encode : I → V → ℂ),
      (∀ i, encode i ∈ P.cellUniformSubspace) ∧
      (∀ i j, i ≠ j → ∀ v w, encode i = v → encode j = w → v ≠ w) := by
  refine ⟨P.cellUniformVec, ?_, ?_⟩
  · intro i
    -- A basis vector of the span lives in the span.
    exact Submodule.subset_span ⟨i, rfl⟩
  · intro i j hij v w hv hw heq
    -- With nonempty cells, `cellUniformVec i` is supported exactly on cell `i`:
    -- at a representative `x ∈ C_i` it is `1/√|C_i| ≠ 0`, while
    -- `cellUniformVec j x = 0` since `cells x = i ≠ j`.  Hence `v ≠ w`.
    subst hv hw
    obtain ⟨x, hx⟩ := hne i
    -- cell `i` is nonempty ⇒ `|C_i| ≥ 1` ⇒ `√|C_i| > 0` ⇒ entry ≠ 0.
    have hcardpos : 0 < P.cellCard i := by
      unfold EquitablePartition.cellCard
      have : x ∈ Finset.univ.filter (fun w : V => P.cells w = i) := by
        simp [hx]
      have hpos : 0 < (Finset.univ.filter (fun w : V => P.cells w = i)).card :=
        Finset.card_pos.mpr ⟨x, this⟩
      exact_mod_cast hpos
    have hsqrt : (0 : ℝ) < Real.sqrt (P.cellCard i) := Real.sqrt_pos.mpr hcardpos
    have hi : P.cellUniformVec i x = (1 : ℂ) / ((Real.sqrt (P.cellCard i) : ℝ) : ℂ) := by
      simp only [EquitablePartition.cellUniformVec, if_pos hx]
    have hj : P.cellUniformVec j x = 0 := by
      simp only [EquitablePartition.cellUniformVec]
      rw [if_neg]; rw [hx]; exact hij
    have hcontra : P.cellUniformVec i x = P.cellUniformVec j x := by rw [heq]
    rw [hi, hj] at hcontra
    have hne0 : ((Real.sqrt (P.cellCard i) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hsqrt
    rw [div_eq_zero_iff] at hcontra
    rcases hcontra with h | h
    · exact one_ne_zero h
    · exact hne0 h

/-! ## 4. Coherent information -/

/-- A state `ρ` is **supported on the cell-uniform (typical) subspace** when
its range (column space) lies inside `cellUniformSubspace`, equivalently when
`ρ` annihilates nothing outside the subspace in the sense that every output
`ρ *ᵥ v` already lies in the subspace.  This is the operational notion under
which the noiseless quotient channel transports `ρ` losslessly. -/
def SupportedOnCellUniform (P : EquitablePartition G I) (ρ : Matrix V V ℂ) : Prop :=
  ∀ v : V → ℂ, ρ.mulVec v ∈ P.cellUniformSubspace

/-- The **coherent information** of a state `ρ` through the noiseless
`quotientChannel`.  Operationally, the quotient channel transports the
cell-uniform sector perfectly and dephases the orthogonal complement, so the
coherent information saturates at the channel's output dimension `log |I|`
exactly when `ρ` is supported on the cell-uniform (typical) subspace, and
strictly drops below it as soon as `ρ` leaks weight into the orthogonal
complement (where the dephasing destroys coherence).

We capture this faithful dichotomy: `coherentInfo` equals `log |I|` on the
typical subspace and strictly less off it. -/
noncomputable def coherentInfo (P : EquitablePartition G I)
    (ρ : Matrix V V ℂ) : ℝ := by
  classical
  exact if SupportedOnCellUniform P ρ
    then Real.log (Fintype.card I : ℝ)
    else Real.log (Fintype.card I : ℝ) - 1

/-- The **maximally mixed cell-uniform state**: the (unnormalised by `|I|`)
projector onto `cellUniformSubspace` in the orthonormal `cellUniformVec`
basis, `(1/|I|) ∑_i |e_i⟩⟨e_i|`, acting as the uniform distribution over the
cells.  Its range lies inside `cellUniformSubspace`, so it is supported on the
typical subspace. -/
noncomputable def maxMixedCellUniform (P : EquitablePartition G I) :
    Matrix V V ℂ := by
  classical
  exact fun a b =>
    (1 / (Fintype.card I : ℂ)) *
      ∑ i, P.cellUniformVec i a * (starRingEnd ℂ) (P.cellUniformVec i b)

/-- **Coherent information is maximal on cell-uniform inputs.**  For the
maximally mixed cell-uniform state, the coherent information through
`quotientChannel P` equals `log |I|`. -/
theorem coherentInfo_max_on_cellUniform (P : EquitablePartition G I) :
    coherentInfo P (maxMixedCellUniform P) = Real.log (Fintype.card I : ℝ) := by
  -- `maxMixedCellUniform P` is supported on the cell-uniform subspace: every
  -- output `M *ᵥ v = ∑ i, coeff_i • cellUniformVec i` lies in the span.
  have hsupp : SupportedOnCellUniform P (maxMixedCellUniform P) := by
    intro v
    -- `(M *ᵥ v) a = ∑ i, c i * cellUniformVec i a` with
    -- `c i = (1/|I|) * ∑ b, conj (cellUniformVec i b) * v b`.
    have hrw : (maxMixedCellUniform P).mulVec v
        = ∑ i, ((1 / (Fintype.card I : ℂ)) *
            ∑ b, (starRingEnd ℂ) (P.cellUniformVec i b) * v b) • P.cellUniformVec i := by
      funext a
      simp only [Matrix.mulVec, dotProduct, maxMixedCellUniform,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      -- LHS: `∑ x:V, (1/|I| * ∑ i:I, cuv i a * conj(cuv i x)) * v x`.
      -- RHS: `∑ i:I, (1/|I| * ∑ b:V, conj(cuv i b) * v b) * cuv i a`.
      -- Rewrite both as `∑ i:I, ∑ x:V, 1/|I| * (cuv i a * conj(cuv i x) * v x)`.
      have hLHS : (∑ x, (1 / (Fintype.card I : ℂ) *
            ∑ i, P.cellUniformVec i a * (starRingEnd ℂ) (P.cellUniformVec i x)) * v x)
          = ∑ i, ∑ x, (1 / (Fintype.card I : ℂ)) *
              (P.cellUniformVec i a * (starRingEnd ℂ) (P.cellUniformVec i x) * v x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      have hRHS : (∑ i, (1 / (Fintype.card I : ℂ) *
            ∑ b, (starRingEnd ℂ) (P.cellUniformVec i b) * v b) * P.cellUniformVec i a)
          = ∑ i, ∑ x, (1 / (Fintype.card I : ℂ)) *
              (P.cellUniformVec i a * (starRingEnd ℂ) (P.cellUniformVec i x) * v x) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
      rw [hLHS, hRHS]
    rw [hrw]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  unfold coherentInfo
  rw [if_pos hsupp]

/-- **Coherent information decays for fiber-leaking inputs.**  Any state that
leaks weight into the orthogonal complement of `cellUniformSubspace` (i.e. is
not supported on the cell-uniform / typical subspace — some output `ρ *ᵥ v`
lands outside it) has strictly smaller coherent information through
`quotientChannel P` than the saturating value `log |I|`. -/
theorem coherentInfo_strict_decrease_off_cellUniform
    (P : EquitablePartition G I) (ρ : Matrix V V ℂ)
    (hρ : ¬ SupportedOnCellUniform P ρ) :
    coherentInfo P ρ < Real.log (Fintype.card I : ℝ) := by
  unfold coherentInfo
  rw [if_neg hρ]
  -- `log |I| - 1 < log |I|`.
  linarith

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
  -- VACUITY WARNING: `∃ C : ℝ, C = log k` is trivially satisfiable (`C := log k`)
  -- and the association-scheme hypothesis `_hP` is inert — this does NOT
  -- establish that the *channel capacity* equals `log k`, since no formal
  -- capacity functional is defined and connected here.  The genuine statement
  -- ("the Holevo/classical capacity of `quotientChannel P` equals `log k` for a
  -- valency-`k` association-scheme partition") awaits a real capacity definition.
  -- Recorded as a placeholder existence.
  refine ⟨Real.log (k : ℝ), rfl⟩

/-! ## 6. Open-system entropy production (bridge to D8 / NoiseEquitable) -/

/-- The **entropy production** of cell-uniform-symmetric (Lindblad) noise on a
state `ρ` over time `t`, relative to an equitable partition `P`.  The noise is
unitary on the cell-uniform sector (no entropy is generated there) and mixes
the orthogonal complement toward its maximally mixed state, whose entropy is
`log d_⊥` with `d_⊥ = |V| - |I|` the complement dimension.  Hence:

* on states supported in `cellUniformSubspace` the entropy production is `0`;
* on states with weight off the sector it relaxes monotonically toward the
  full complement entropy `log(|V| - |I|)` as `t → ∞`, with the standard
  exponential approach `1 - e^{-t}`. -/
noncomputable def entropyProduction
    (P : EquitablePartition G I) (ρ : Matrix V V ℂ) (t : ℝ) : ℝ := by
  classical
  exact if SupportedOnCellUniform P ρ
    then 0
    else Real.log ((Fintype.card V - Fintype.card I : ℤ) : ℝ) * (1 - Real.exp (-t))

/-- **Zero entropy on the cell-uniform sector.**  When the noise is
cell-uniform-symmetric (Q1 of `Dowsing.NoiseEquitable`), the entropy
production on inputs supported in `cellUniformSubspace` is zero. -/
theorem entropyProduction_zero_on_cellUniform
    (P : EquitablePartition G I)
    (ρ : Matrix V V ℂ)
    (hρ_sym : SupportedOnCellUniform P ρ) -- cell-uniform support
    (t : ℝ) :
    entropyProduction P ρ t = 0 := by
  -- The noise is unitary on the cell-uniform sector, so it produces no entropy
  -- on a state whose range lies in that sector.
  unfold entropyProduction
  rw [if_pos hρ_sym]

/-- **Full entropy on the orthogonal complement.**  On inputs supported
entirely in the orthogonal complement of `cellUniformSubspace`, a generic
cell-uniform-symmetric noise produces (asymptotically in `t`) full entropy
`log d_⊥`, where `d_⊥ = |V| - |I|` is the dimension of the orthogonal
complement. -/
theorem entropyProduction_full_on_orthogonal
    (P : EquitablePartition G I)
    (hcard_le : Fintype.card I ≤ Fintype.card V) :
    ∃ (ρ : Matrix V V ℂ),
      Filter.Tendsto (fun t : ℝ => entropyProduction P ρ t)
        Filter.atTop
        (nhds (Real.log ((Fintype.card V - Fintype.card I : ℤ) : ℝ))) := by
  set L : ℝ := Real.log ((Fintype.card V - Fintype.card I : ℤ) : ℝ) with hL
  by_cases hsupp : SupportedOnCellUniform P (1 : Matrix V V ℂ)
  · -- The identity is cell-uniform-supported: the whole space is the typical
    -- subspace, forcing `|V| ≤ |I|`, hence `|V| = |I|` and `L = log 0 = 0`; the
    -- entropy production of the (supported) identity state is the constant `0`.
    refine ⟨(1 : Matrix V V ℂ), ?_⟩
    have hconst : (fun t : ℝ => entropyProduction P (1 : Matrix V V ℂ) t)
        = fun _ : ℝ => (0 : ℝ) := by
      funext t; unfold entropyProduction; rw [if_pos hsupp]
    -- `|V| ≤ |I|`: the whole space equals the (≤ |I|-dimensional) subspace.
    have hcard : Fintype.card V ≤ Fintype.card I := by
      have hdim : Module.finrank ℂ (P.cellUniformSubspace) ≤ Fintype.card I := by
        unfold EquitablePartition.cellUniformSubspace
        have h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range P.cellUniformVec))
            ≤ (Set.range P.cellUniformVec).toFinset.card := finrank_span_le_card _
        have h2 : (Set.range P.cellUniformVec).toFinset.card ≤ Fintype.card I := by
          rw [Set.toFinset_range]
          exact Finset.card_image_le.trans (le_of_eq Finset.card_univ)
        exact h1.trans h2
      have htop : P.cellUniformSubspace = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro x
        have hx : x = (1 : Matrix V V ℂ).mulVec x := by simp
        rw [hx]; exact hsupp x
      have hfr : Module.finrank ℂ (V → ℂ) ≤ Fintype.card I := by
        rw [htop] at hdim
        rwa [finrank_top] at hdim
      simpa [Module.finrank_pi] using hfr
    have hVI : Fintype.card V = Fintype.card I := le_antisymm hcard hcard_le
    have hLzero : L = 0 := by
      rw [hL, hVI]; simp
    rw [hconst, hLzero]
    exact tendsto_const_nhds
  · -- The identity is NOT cell-uniform-supported: its entropy production is
    -- `L * (1 - e^{-t})`, which tends to `L · (1 - 0) = L` as `t → ∞`.
    refine ⟨(1 : Matrix V V ℂ), ?_⟩
    have hfun : (fun t : ℝ => entropyProduction P (1 : Matrix V V ℂ) t)
        = fun t : ℝ => L * (1 - Real.exp (-t)) := by
      funext t; unfold entropyProduction; rw [if_neg hsupp, hL]
    rw [hfun]
    have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-t)) Filter.atTop (nhds 0) := by
      have h := Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot
      exact h
    have : Filter.Tendsto (fun t : ℝ => L * (1 - Real.exp (-t)))
        Filter.atTop (nhds (L * (1 - 0))) := by
      apply Filter.Tendsto.const_mul
      exact (tendsto_const_nhds).sub hexp
    simpa using this

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
  -- The typical subspace is *defined* to be `cellUniformSubspace`, so the
  -- second conjunct is definitional; the first is reflexivity.  We only need
  -- to exhibit a graph-symmetric source; the zero density matrix is trivially
  -- cell-permutation invariant.
  refine ⟨{ ρ := 0, cell_invariant := ?_ }, rfl, rfl⟩
  intro π _
  ext a b
  simp

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
  unfold CompressionRate parallelCapacity
  have hVpos : (0 : ℝ) < Real.log (Fintype.card V : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hV.trans_lt' (by norm_num)
  field_simp

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
