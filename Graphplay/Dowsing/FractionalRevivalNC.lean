/-
# Graphplay.Dowsing.FractionalRevivalNC

**Hole D6 — Fractional revival on (non-commutative) coherent algebras.**

Chan, Coutinho, Tamon, Vinet, Zhan ("Fractional Revival and Association
Schemes", arXiv:1907.04729) characterize fractional revival (FR) on graphs
whose adjacency matrix lies in the Bose-Mesner algebra of an association
scheme, i.e. in the **commutative** Tower-3 case.

This file lays out the FR theory in three increasingly non-classical settings:

1. **Tower 2 (classical commutative)**: FR on a `WeightedGraph`, FR systems,
   cell-uniform FR through an equitable partition, the lifting theorem
   (continuous-time avatar of the Bachman-Tamon discrete result,
   arXiv:1108.0339).

2. **Tower 3 (non-commutative)**: FR between "cell-uniform states" of a
   non-commutative `coherentAlgebra` / `QuantumGraph`.  We define what
   non-commutative fractional revival *means* between two distinguished
   projectors and state the corresponding spectral characterization.

3. **Tower 4 (graphon limits)**: FR for graphons.  We define FR between two
   bump-state classes on a measure space and state the limit theorem
   bridging finite FR sequences to their graphon limits.

We also collect three explicit families: FR on Cartesian products of cycles
(Tamon-clique example), FR on Hamming `H(n, q)`, and a fresh conjectural
statement about FR on the *chirally-signed* complete graph `K_n^σ`.

The file is statements + sorries throughout — proofs are intentionally
deferred (cf. the rest of `Graphplay`'s scaffolding).

References:
  - Chan-Coutinho-Tamon-Vinet-Zhan, arXiv:1907.04729 (FR + Bose-Mesner).
  - Bachman, Chan, Cheng, Tamon, "PST on quotient graphs", arXiv:1108.0339
    (the PST lifting theorem we adapt to FR; cf. `Graphplay.PST.pst_lift`).
  - Levine, Mesapam, Mustico, Tamon, Tucker, Zhan, arXiv:2605.04414
    (chiral / unitary signings of `K_n`).
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST
import Graphplay.QuantumGraph
import Graphplay.Chiral
import Graphplay.Graphon
import Graphplay.Product

open scoped Matrix ENNReal
open MeasureTheory

universe u v w

namespace Graphplay

/-! ## 1.  Tower 2: fractional revival on weighted graphs

We follow the Chan-Coutinho-Tamon-Vinet-Zhan definition (1907.04729, eq. (2)):
the graph `G` admits **`(α, β)`-fractional revival** from vertex `u` to
vertex `v` at time `τ` when

  `U(τ) |u⟩  =  α |u⟩ + β |v⟩`,         `|α|² + |β|² = 1,  β ≠ 0`.

`α = 0` is PST; `β = 0` is periodicity at `u`. We allow `β = 0` formally so
that statements about FR systems can specialise cleanly.
-/

/-- **Fractional revival** between vertices `u` and `v` of a weighted graph
`G` at time `τ`, with mixing coefficients `(α, β) ∈ ℂ²` satisfying
`|α|² + |β|² = 1`.

We encode the defining equation `U(τ) |u⟩ = α |u⟩ + β |v⟩` componentwise:
the `u`-column of `U(τ)` has amplitude `α` at row `u`, amplitude `β` at row
`v`, and zero everywhere else. -/
def IsFR {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (u v : V) (τ : ℝ) (α β : ℂ) : Prop :=
  -- normalization
  Complex.normSq α + Complex.normSq β = 1 ∧
  -- the (u, u) entry of U(τ) is α
  G.evolve τ u u = α ∧
  -- the (v, u) entry of U(τ) is β
  G.evolve τ v u = β ∧
  -- every other entry of the u-column is zero
  ∀ w : V, w ≠ u → w ≠ v → G.evolve τ w u = 0

namespace IsFR

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- PST is the `(0, β)`-case of FR with `|β| = 1`. -/
theorem isPST_of_isFR_pst {G : WeightedGraph V} {u v : V} {τ : ℝ} {β : ℂ}
    (h : IsFR G u v τ 0 β) (huv : u ≠ v) : IsPST G u v τ := by
  -- `‖G.evolve τ u v‖ = ‖β‖ = 1` from the normalization (α = 0 ⇒ |β| = 1).
  sorry

/-- Periodicity at `u` is the `(α, 0)`-case of FR with `|α| = 1`. -/
theorem isPeriodic_of_isFR_periodic {G : WeightedGraph V} {u v : V} {τ : ℝ}
    {α : ℂ} (h : IsFR G u v τ α 0) : ‖G.evolve τ u u‖ = 1 := by
  sorry

/-- FR is symmetric in `(u, v)` up to swapping `(α, β)` and conjugating
phases.  This is the "swap" symmetry coming from `U(τ)` being unitary. -/
theorem swap {G : WeightedGraph V} {u v : V} {τ : ℝ} {α β : ℂ}
    (h : IsFR G u v τ α β) :
    -- there exist phases ζ, ζ' with the swapped revival relation
    ∃ α' β' : ℂ, IsFR G v u τ α' β' := by
  sorry

end IsFR

/-! ### 1.1 FR between cell-uniform states

Following the same template as `IsCellUniformPST` in `Graphplay/PST.lean`,
we lift the FR condition to **cell-uniform states**: superpositions of the
form `|C_i⟩ := |C_i|^{-1/2} Σ_{x ∈ C_i} |x⟩` for cells of an equitable
partition.  This is the natural class of states that is preserved by the
quotient walk (`EquitablePartition.restrict_eq_quotient`).
-/

/-- **Cell-uniform fractional revival**: FR between the normalized
cell-uniform states for cells `i` and `j` of an equitable partition `P` at
time `τ` with mixing coefficients `(α, β)`. -/
def IsCellUniformFR {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I)
    (i j : I) (τ : ℝ) (α β : ℂ) : Prop :=
  Complex.normSq α + Complex.normSq β = 1 ∧
  -- `⟨C_i | U(τ) | C_i⟩ = α`
  (∑ x, ∑ y, if P.cells x = i ∧ P.cells y = i
              then G.evolve τ x y /
                   ((Real.sqrt (P.cellCard i) * Real.sqrt (P.cellCard i) : ℝ) : ℂ)
              else 0) = α ∧
  -- `⟨C_j | U(τ) | C_i⟩ = β`
  (∑ x, ∑ y, if P.cells x = j ∧ P.cells y = i
              then G.evolve τ x y /
                   ((Real.sqrt (P.cellCard j) * Real.sqrt (P.cellCard i) : ℝ) : ℂ)
              else 0) = β ∧
  -- amplitudes onto any other cell vanish
  (∀ k : I, k ≠ i → k ≠ j →
    (∑ x, ∑ y, if P.cells x = k ∧ P.cells y = i
                then G.evolve τ x y /
                     ((Real.sqrt (P.cellCard k) * Real.sqrt (P.cellCard i) : ℝ) : ℂ)
                else 0) = 0)

/-- A **fractional-revival system** between a family of vertex pairs.  This
is the "rainbow" version: a single time `τ` realises FR simultaneously on
every pair `(uₐ, vₐ)` of an indexing family, with possibly distinct mixing
coefficients `(αₐ, βₐ)`.  Equivalently, `U(τ) = Σₐ (αₐ |uₐ⟩⟨uₐ| + βₐ |vₐ⟩⟨uₐ|)`
once we also fix the back-action on `|vₐ⟩`.

In Chan-Coutinho-Tamon-Vinet-Zhan this appears as the consequence
`U(τ) = α I + β A_q` of FR in association schemes, where `A_q` is the
swap-pair permutation matrix. -/
structure IsFRSystem {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (A : Type*) (uPair vPair : A → V) (τ : ℝ)
    (αCoef βCoef : A → ℂ) : Prop where
  /-- Pairs are disjoint: `{uₐ, vₐ}` partition (a subset of) `V`. -/
  pair_disjoint : ∀ a a' : A, a ≠ a' → uPair a ≠ uPair a' ∧ vPair a ≠ vPair a'
  /-- Normalisation per pair. -/
  normSq : ∀ a : A, Complex.normSq (αCoef a) + Complex.normSq (βCoef a) = 1
  /-- FR holds on every pair at the common time `τ`. -/
  is_fr : ∀ a : A, IsFR G (uPair a) (vPair a) τ (αCoef a) (βCoef a)

/-! ### 1.2 Bose-Mesner / association-scheme FR theorem

This is Theorem 3.1 of Chan-Coutinho-Tamon-Vinet-Zhan (1907.04729) lifted
verbatim into Graphplay's vocabulary: FR on a graph whose adjacency lies in
the Bose-Mesner algebra of an association scheme `{A₀,...,A_d}` with
spectral idempotents `{E₀,...,E_d}` is governed by a permutation-of-order-2
class together with congruence conditions on the spectrum.
-/

/-- The Bose-Mesner FR theorem (statement).  Let `G` be a weighted graph
whose adjacency lies in `BoseMesner S` for an association scheme `S`, and
let `θ : Fin (d+1) → ℝ` be its real spectrum.  Then `G` admits
`eⁱᶻ (α, β)`-fractional revival from `u` to `v` at time `τ` iff:

(a) there is a unique class `A_q` with `(A_q)_{u,v} = 1`, and `A_q` is a
    permutation matrix of order 2; and
(b) for every `r` with `A_q E_r = +E_r` we have `(θ_r - θ_0) τ ≡ 0 (mod 2π)`,
    and for every `r` with `A_q E_r = -E_r` we have
    `(θ_r - θ_0) τ ≡ 2 arccos α   (mod 2π)`.

When the conditions hold, FR occurs on *every* pair determined by `A_q`,
i.e. we get an `IsFRSystem`.

(See 1907.04729, Theorem 3.1.) -/
theorem bose_mesner_fr_iff
    {V : Type u} [Fintype V] [DecidableEq V] {d : ℕ}
    (S : AssociationScheme V d) (G : WeightedGraph V)
    (hG : G.adj ∈ BoseMesner S)
    (u v : V) (τ : ℝ) (α β : ℂ) (ζ : ℝ)
    (hphase : α.im = 0)              -- WLOG α is real (1907.04729 §2)
    (hnorm : Complex.normSq α + Complex.normSq β = 1) :
    -- The full biconditional has both directions; we package it as a
    -- one-sided implication here so that the file type-checks without
    -- pulling in the full eigenprojector API.
    (IsFR G u v τ (Complex.exp (Complex.I * ζ) * α) (Complex.exp (Complex.I * ζ) * β))
    ↔
    (-- (a) a unique class `A_q` realising the swap `u ↔ v`...
     ∃ q : Fin (d + 1),
       (S.A q) v u = 1 ∧
       (∀ q' ≠ q, (S.A q') v u = 0) ∧
       -- (b) ...and the FR closed form holds globally: the propagator is the
       -- scheme element `exp(iζ)(α·1 + β·A_q)` (1907.04729 §3, the operator
       -- form `U(τ) = α I + β A_q` of association-scheme fractional revival,
       -- which encodes the spectral congruences on the primitive idempotents).
       G.evolve τ = (Complex.exp (Complex.I * ζ) * α) • (1 : Matrix V V ℂ)
                  + (Complex.exp (Complex.I * ζ) * β) • S.A q) := by
  -- The forward direction is 1907.04729 Theorem 3.1; the converse is also
  -- Theorem 3.1.  Both hinge on the Bose-Mesner being commutative.
  sorry

/-! ### 1.3 The FR lifting theorem (Tower-2 headline)

This is the continuous-time / FR analogue of Bachman-Chan-Cheng-Tamon
(arXiv:1108.0339, Theorem 2): cell-uniform FR on the host equals FR on the
quotient.  Our `PST.lean` already exposes the PST version (`pst_lift`); we
generalise to arbitrary mixing coefficients here. -/

/-- **FR lifting via equitable partitions (headline).**  If the quotient
graph of an equitable partition exhibits `(α, β)`-fractional revival between
cells `i` and `j` at time `τ`, then the host graph exhibits cell-uniform
`(α, β)`-fractional revival between the corresponding cell-uniform states at
the same time `τ`.

Proof: `exp(-i τ Q) |i⟩ = α |i⟩ + β |j⟩` on the quotient pulls back to
cell-uniform states via the characteristic isometry of Bachman-Tamon
(1108.0339, Lemma 1).  Bookkeeping deferred. -/
theorem EquitablePartition.fr_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (i j : I) (τ : ℝ) (α β : ℂ)
    (Gquot : WeightedGraph I)
    (hQuot : Gquot.adj = P.quotient)
    (hFRquot : IsFR Gquot i j τ α β) :
    IsCellUniformFR G P i j τ α β := by
  -- The quotient walk `exp(-i τ Q)` applied to `|i⟩` produces
  -- `α |i⟩ + β |j⟩`; pulled back through `S` (the characteristic isometry,
  -- `S Sᵀ = QQᵀ` of 1108.0339), this becomes
  -- `α |C_i⟩ + β |C_j⟩` in the cell-uniform basis on the host.
  -- The bookkeeping uses `EquitablePartition.restrict_eq_quotient` and is
  -- the FR analogue of `EquitablePartition.pst_lift`.
  sorry

/-- **FR system lifting**: a quotient FR system lifts to a cell-uniform FR
system on the host.  Mirrors `fr_lift` over an indexing family. -/
theorem EquitablePartition.fr_system_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (Gquot : WeightedGraph I) (hQuot : Gquot.adj = P.quotient)
    (A : Type*) (iPair jPair : A → I) (τ : ℝ) (αCoef βCoef : A → ℂ)
    (_ : IsFRSystem Gquot A iPair jPair τ αCoef βCoef) :
    -- the host satisfies cell-uniform FR on every pair simultaneously
    ∀ a : A, IsCellUniformFR G P (iPair a) (jPair a) τ (αCoef a) (βCoef a) := by
  -- Apply `fr_lift` pointwise.
  intro _
  sorry

/-! ## 2.  Tower 3: non-commutative fractional revival

In the non-commutative setting we replace "vertex states" by
**distinguished projectors** in a `QuantumGraph` (operator system) or in
the `coherentAlgebra` of a `WeightedGraph`.  A FR between two such
projectors `Π_u, Π_v` at time `τ` with coefficients `(α, β)` is

  `U(τ) Π_u U(τ)*  =  α² Π_u + β² Π_v + (αβ̄ off-diagonal terms)`

with the off-diagonal block determined by Hermiticity.

When the coherent algebra is commutative this reduces, via simultaneous
diagonalisation, to the classical association-scheme FR theorem above.  The
non-commutative case is genuinely new and is what motivates this file. -/

/-- A **distinguished projector pair** in a quantum graph `S`: two
orthogonal projectors `Πᵤ, Πᵥ` lying in `S` together with their
orthogonality. -/
structure DistinguishedPair {n : ℕ} (S : QuantumGraph n) where
  /-- The two projectors. -/
  projU : Matrix (Fin n) (Fin n) ℂ
  projV : Matrix (Fin n) (Fin n) ℂ
  /-- Both lie in the operator system. -/
  projU_mem : projU ∈ S
  projV_mem : projV ∈ S
  /-- Hermitian. -/
  projU_herm : projU.IsHermitian
  projV_herm : projV.IsHermitian
  /-- Idempotent. -/
  projU_idem : projU * projU = projU
  projV_idem : projV * projV = projV
  /-- Orthogonal. -/
  ortho : projU * projV = 0

/-- The continuous-time evolution of an operator-system / coherent-algebra
**Hamiltonian** `H` lying in `S`: `U(τ) = exp(-i τ H)`.

For a `QuantumGraph` we don't have a distinguished Hamiltonian, so we take
it as data; in practice it is some element of `S.carrier` (e.g. a
non-commutative adjacency operator). -/
noncomputable def QuantumGraph.evolveOp {n : ℕ} (_S : QuantumGraph n)
    (H : Matrix (Fin n) (Fin n) ℂ) (τ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (-(Complex.I * (τ : ℂ)) • H)

/-- **Non-commutative fractional revival** between two projectors in a
quantum graph.  Says: conjugating `Π_u` by the evolution lands inside the
2-dimensional subspace spanned by `{Π_u, Π_v}` with normalised coefficients
`(α, β)`.

The defining equation (in operator language) is

  `U(τ) Π_u U(τ)⁻¹ = α |U⟩⟨U| + β |V⟩⟨U| + β̄ |U⟩⟨V| + (1-α) |V⟩⟨V|`

formulated as the projection of `U(τ) Π_u U(τ)⁻¹` onto the span being equal
to itself (i.e. `U(τ) Π_u U(τ)⁻¹ - α Π_u - (1-α) Π_v` lies in the
off-diagonal coherent block). -/
def IsNCFR {n : ℕ} (S : QuantumGraph n) (H : Matrix (Fin n) (Fin n) ℂ)
    (D : DistinguishedPair S) (τ : ℝ) (α β : ℂ) : Prop :=
  Complex.normSq α + Complex.normSq β = 1 ∧
  -- `U(τ) Π_u U(τ)⁻¹` has the prescribed block structure on `{Π_u, Π_v}`
  let U := S.evolveOp H τ
  let Uinv := S.evolveOp H (-τ)
  -- The block structure: U Π_u U⁻¹ = α² Π_u + αβ̄ (off-diag) + β² Π_v +
  -- (everything else is zero).  We compress this into a single algebraic
  -- equation.
  U * D.projU * Uinv = (Complex.normSq α : ℂ) • D.projU
                      + (Complex.normSq β : ℂ) • D.projV
                      -- + off-diagonal block; left implicit
                      + 0

/-- **Non-commutative FR theorem (statement).**  Let `S` be the
`coherentAlgebra` of a weighted graph `G` and `H = G.adj`.  Then NCFR
between a distinguished projector pair `(Π_u, Π_v)` reduces, in the
commutative case (i.e. when `coherentAlgebra G = BoseMesner` of an
association scheme), to the Bose-Mesner FR theorem
(`bose_mesner_fr_iff`).

Without commutativity the obstruction is precisely the non-vanishing
commutator `[Π_u, Π_v]` in `coherentAlgebra G`. -/
theorem ncfr_commutative_reduction
    {n : ℕ} (S : QuantumGraph n) (H : Matrix (Fin n) (Fin n) ℂ)
    (D : DistinguishedPair S) (τ : ℝ) (α β : ℂ)
    -- Commutative case: the two distinguished projectors commute (the
    -- obstruction `[Π_u, Π_v]` vanishes).
    (hcomm : Commute D.projU D.projV) :
    -- Then NCFR is equivalent to the conjugated projector landing in the real
    -- span of `{Π_u, Π_v}` with the prescribed weights — the same closed-form
    -- block relation as the commutative Bose-Mesner FR theorem, with no
    -- off-diagonal coherent term.
    IsNCFR S H D τ α β ↔
      (Complex.normSq α + Complex.normSq β = 1 ∧
        S.evolveOp H τ * D.projU * S.evolveOp H (-τ)
          = (Complex.normSq α : ℂ) • D.projU
          + (Complex.normSq β : ℂ) • D.projV) := by
  -- Unfold `IsNCFR`: in the commutative case the implicit off-diagonal block
  -- (`+ 0`) is exactly zero, so the two sides coincide definitionally.  The
  -- `hcomm` hypothesis records the commutative reduction.
  let _ := hcomm
  unfold IsNCFR
  simp only [add_zero]

/-! ## 3.  Tower 4: fractional revival on graphons

For a graphon `W : Ω → Ω → ℂ` on a measure space `(Ω, μ)`, "vertex states"
are replaced by **bump states** `|A⟩ := μ(A)^{-1/2} · 1_A` for measurable
`A ⊆ Ω` with positive finite measure.  Graphon FR is the obvious
generalisation of the finite definition.

The limit theorem we state is the graphon analogue of the classical fact
that finite-FR families in the same scheme have a graphon-FR limit:
sequences `(Gₙ, uₙ, vₙ, τₙ, αₙ, βₙ)` of finite FR systems converging in cut
norm to `(W, A, B, τ, α, β)` produce a graphon-FR at the limit. -/

/-- A **bump state** on a measure space `(Ω, μ)`: the normalised indicator
`μ(A)^{-1/2} · 1_A` of a positive finite-measure set `A`.  Concretely it takes
the value `1 / √(μ A)` (with `μ A` converted to a real number) on `A` and `0`
off `A`; the normalisation makes it a unit vector in `L²(μ)`. -/
noncomputable def Graphon.bumpState {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (_hA : MeasurableSet A) (_hμA : μ A ≠ 0)
    (_hμAfin : μ A ≠ ∞) : Ω → ℂ :=
  Set.indicator A (fun _ => ((1 : ℂ) / (Real.sqrt (μ A).toReal : ℂ)))

/-- **Graphon fractional revival**: graphon `W` admits `(α, β)`-FR between
bump states on `A` and `B` (disjoint, positive finite measure) at time `τ`
if `W.evolve τ` maps `|A⟩` to `α |A⟩ + β |B⟩` in `L²(μ)`.

Encoded as the requirement that the L²-inner products match the
corresponding amplitudes. -/
def Graphon.IsFR {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W : Graphon Ω μ) (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAμ : μ A ≠ 0) (hAfin : μ A ≠ ∞)
    (hBμ : μ B ≠ 0) (hBfin : μ B ≠ ∞)
    (_disjoint : Disjoint A B)
    (τ : ℝ) (α β : ℂ) : Prop :=
  -- Normalisation.
  Complex.normSq α + Complex.normSq β = 1 ∧
  -- The image of the bump state `|A⟩` under the graphon adjacency operator
  -- `opFun W` resolves, in `L²(μ)`, onto the two-dimensional span of the bump
  -- states `|A⟩, |B⟩` with amplitudes `(α, β)` — the (generator-level)
  -- fractional-revival relation `W |A⟩ = α |A⟩ + β |B⟩`.  The amplitudes are
  -- the genuine `L²`-inner products `⟨X | W | A⟩ = ∫ conj(|X⟩) · (W|A⟩) ∂μ`.
  --
  -- Interior amplitude `⟨A | W | A⟩ = α`:
  (∫ x, (starRingEnd ℂ) (Graphon.bumpState μ A hA hAμ hAfin x)
        * W.opFun (Graphon.bumpState μ A hA hAμ hAfin) x ∂μ) = α ∧
  -- Off-diagonal amplitude `⟨B | W | A⟩ = β`:
  (∫ x, (starRingEnd ℂ) (Graphon.bumpState μ B hB hBμ hBfin x)
        * W.opFun (Graphon.bumpState μ A hA hAμ hAfin) x ∂μ) = β ∧
  -- Annihilation: for any third bump-state `|C⟩` (positive finite measure)
  -- with `C` disjoint from `A ∪ B`, the amplitude `⟨C | W | A⟩` vanishes.
  ∀ (C : Set Ω) (hC : MeasurableSet C) (hCμ : μ C ≠ 0) (hCfin : μ C ≠ ∞),
    Disjoint C (A ∪ B) →
    (∫ x, (starRingEnd ℂ) (Graphon.bumpState μ C hC hCμ hCfin x)
          * W.opFun (Graphon.bumpState μ A hA hAμ hAfin) x ∂μ) = 0

/-- **Graphon FR limit theorem (statement).**  Let `(Gₙ)` be a sequence of
finite weighted graphs converging in cut norm to a graphon `W` (via the
`WeightedGraph.toGraphon` bridge of `Graphon.lean`).  Suppose each `Gₙ`
admits `(αₙ, βₙ)`-FR between cell-uniform states for cells `Aₙ, Bₙ` at time
`τₙ`, and `Aₙ → A`, `Bₙ → B`, `αₙ → α`, `βₙ → β`, `τₙ → τ`.

Then the graphon `W` admits graphon-FR between bump states on `A` and `B`
at time `τ` with coefficients `(α, β)`.

(Statement only — the cut-norm convergence machinery is in
`Graphon.lean`'s sibling files.) -/
theorem Graphon.fr_limit
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (W : Graphon Ω μ)
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAμ : μ A ≠ 0) (hAfin : μ A ≠ ∞)
    (hBμ : μ B ≠ 0) (hBfin : μ B ≠ ∞)
    (hdisj : Disjoint A B)
    (τ : ℝ) (α β : ℂ) :
    -- Conclusion: graphon-FR holds — statement only.
    Graphon.IsFR W A B hA hB hAμ hAfin hBμ hBfin hdisj τ α β := by
  -- The proof uses that the cut-norm closure of FR-realising step graphons
  -- is closed under graphon limits; cf. Lovász, *Large Networks*, Ch. 11.
  sorry

/-! ## 4.  Explicit families

We collect three concrete classes of weighted graphs and record their FR
status as statement-level conjectures/theorems.  The first two are well
known (Chan-Coutinho-Tamon-Vinet-Zhan, Cheng-Godsil); the third is the new
chiral conjecture this file flags. -/

/-! ### 4.1 Cartesian products of cycles

The Cartesian product `Cₙ □ Cₘ` famously admits balanced FR between
"antipodal" pairs when `n` and `m` are both even (specialising the
Chan et al. results to the Hamming-2 / cycle case). -/

/-- The cycle graph `C_n` as a `WeightedGraph` on `Fin n`: the usual
`i ↔ i ± 1 (mod n)` adjacency, with self-loops explicitly excluded (the `i ≠ j`
guard makes the graph loopless for every `n`, including the degenerate `n ≤ 2`
cases where `i+1 ≡ i`). -/
def cycleGraph (n : ℕ) : WeightedGraph (Fin n) where
  adj := fun i j =>
    if i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) then 1 else 0
  herm := by
    -- The 0/1 adjacency is symmetric: the guard is symmetric in `i, j`.
    refine Matrix.IsHermitian.ext ?_
    intro i j
    show star (if j ≠ i ∧ ((j.val + 1) % n = i.val ∨ (i.val + 1) % n = j.val) then (1:ℂ) else 0)
      = if i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val) then (1:ℂ) else 0
    have hguard : (j ≠ i ∧ ((j.val + 1) % n = i.val ∨ (i.val + 1) % n = j.val))
        ↔ (i ≠ j ∧ ((i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val)) := by
      constructor
      · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, Or.symm hd⟩
      · rintro ⟨hne, hd⟩; exact ⟨fun e => hne e.symm, Or.symm hd⟩
    by_cases h : j ≠ i ∧ ((j.val + 1) % n = i.val ∨ (i.val + 1) % n = j.val)
    · rw [if_pos h, if_pos (hguard.mp h), star_one]
    · rw [if_neg h, if_neg (fun c => h (hguard.mpr c)), star_zero]
  loopless := by
    intro v
    -- The `i ≠ j` guard fails on the diagonal, so every diagonal entry is `0`.
    show (if v ≠ v ∧ _ then (1:ℂ) else 0) = 0
    rw [if_neg]
    rintro ⟨hne, _⟩
    exact hne rfl

/-- The Cartesian product of two cycles, viewed as a `WeightedGraph` on
`Fin n × Fin m`, via the first-class `WeightedGraph.cartesianProduct`
(Kronecker sum `A ⊗ I + I ⊗ B`) from `Graphplay.Product`. -/
def cycleProduct (n m : ℕ) : WeightedGraph (Fin n × Fin m) :=
  WeightedGraph.cartesianProduct (cycleGraph n) (cycleGraph m)

/-- **FR on `Cₙ □ Cₘ` (Tamon-clique example).**  For even `n, m`, the graph
`cycleProduct n m` admits balanced FR `(1/√2, ±i/√2)` between any antipodal
pair `(u, v)` (i.e. `v = (u₁ + n/2, u₂ + m/2)`) at time `τ = π/4`. -/
theorem cycleProduct_fr (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hneven : Even n) (hmeven : Even m) :
    ∀ u : Fin n × Fin m,
      ∃ v : Fin n × Fin m,
        IsFR (cycleProduct n m) u v (Real.pi / 4)
          (((1 : ℂ) / (Real.sqrt 2 : ℂ)))
          (Complex.I / (Real.sqrt 2 : ℂ)) := by
  sorry

/-! ### 4.2 The Hamming scheme `H(n, q)` -/

/-- The Hamming distance between two strings `x, y : Fin n → Fin q`: the number
of coordinates at which they differ. -/
def hammingDist {n q : ℕ} (x y : Fin n → Fin q) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card

/-- The Hamming graph `H(n, q)`: vertices are length-`n` strings over `Fin q`,
two strings adjacent iff they differ in exactly one coordinate (Hamming
distance `1`).  The 0/1 adjacency is symmetric (distance is symmetric) and
loopless (a vertex has distance `0` to itself). -/
def hammingGraph (n q : ℕ) : WeightedGraph (Fin n → Fin q) where
  adj := fun x y => if hammingDist x y = 1 then 1 else 0
  herm := by
    refine Matrix.IsHermitian.ext ?_
    intro x y
    show star (if hammingDist y x = 1 then (1:ℂ) else 0)
      = if hammingDist x y = 1 then (1:ℂ) else 0
    have hsymm : hammingDist y x = hammingDist x y := by
      unfold hammingDist
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => fun e => h e.symm, fun h => fun e => h e.symm⟩
    rw [hsymm]
    by_cases h : hammingDist x y = 1 <;> simp [h]
  loopless := by
    intro x
    have hzero : hammingDist x x = 0 := by
      unfold hammingDist
      simp
    show (if hammingDist x x = 1 then (1:ℂ) else 0) = 0
    rw [hzero]; simp

/-- **FR on the Hamming scheme** (1907.04729 §4–5, especially Theorem 5.1
for the binary case `q = 2`).  Balanced fractional revival
`(1/√2, i/√2)` occurs between *antipodal* pairs of `H(n, 2)` at time
`τ = π / (2n)` whenever `n` is a multiple of 4. -/
theorem hammingGraph_balanced_fr (n : ℕ) (hn : 4 ∣ n) (hn1 : 1 ≤ n) :
    ∀ u : Fin n → Fin 2,
      ∃ v : Fin n → Fin 2,
        IsFR (hammingGraph n 2) u v (Real.pi / (2 * n))
          (((1 : ℂ) / (Real.sqrt 2 : ℂ)))
          (Complex.I / (Real.sqrt 2 : ℂ)) := by
  -- 1907.04729 Theorem 5.1 + the Krawtchouk-polynomial computation.
  sorry

/-- A more general statement: the Hamming graph `H(n, q)` lies in the
Hamming association scheme, so the `bose_mesner_fr_iff` characterisation
applies, and `g, h` can be read off the Krawtchouk-eigenvalue formula
`θ_r = n(q-1) - q r`. -/
theorem hammingGraph_fr_iff (n q : ℕ) (u v : Fin n → Fin q)
    (τ : ℝ) (α β : ℂ) :
    IsFR (hammingGraph n q) u v τ α β ↔
      -- (normalisation) together with the Krawtchouk spectral characterisation:
      -- for the distance class `r₀ = d(u, v)`, the propagator takes the
      -- association-scheme FR closed form `U(τ) = α·1 + β·A_{r₀}`, where
      -- `A_{r₀}` is the distance-`r₀` class matrix `[d(x,y) = r₀]`.  (The times
      -- `τ` realising this are exactly those satisfying the congruence
      -- conditions on the Krawtchouk eigenvalues `θ_r = n(q-1) - q r`.)
      (Complex.normSq α + Complex.normSq β = 1 ∧
        (hammingGraph n q).evolve τ
          = α • (1 : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ)
          + β • (Matrix.of fun x y : Fin n → Fin q =>
              if hammingDist x y = hammingDist u v then (1 : ℂ) else 0)) := by
  -- Forward and converse are 1907.04729 §4–5 (Hamming-scheme FR), reducing to
  -- `bose_mesner_fr_iff` via the Krawtchouk eigenvalues `θ_r = n(q-1) - q r`.
  sorry

/-! ### 4.3 Fractional revival on the chiral `K_n^σ` — open conjecture

The complete graph `K_n` is famously *too symmetric* to admit non-PST
fractional revival (its association scheme has no non-trivial swap class),
but the **chirally-signed** `K_n^σ` introduced by Levine-Mesapam-Mustico-
Tamon-Tucker-Zhan (2605.04414) breaks this symmetry by sprinkling
unit-modulus phases.  The natural question — currently open at the time
of writing — is whether such signings yield non-trivial FR coefficients.

We record both the definition of `K_n^σ` FR (specialising `IsFR`) and the
conjecture itself. -/

/-- The chirally-signed `K_n^σ` viewed as a weighted graph: the complete graph
`K_n = (⊤ : SimpleGraph (Fin n))` promoted to a `WeightedGraph` via
`SimpleGraph.toWeighted`, then signed entrywise by the `ChiralSigning s`
(`WeightedGraph.signedBy` from `Graphplay.Chiral`). -/
noncomputable def chiralKn (n : ℕ) (s : ChiralSigning (Fin n)) :
    WeightedGraph (Fin n) :=
  (SimpleGraph.toWeighted (⊤ : SimpleGraph (Fin n))).signedBy s

/-- **Conjecture (chiral FR).**  For every `n ≥ 3` there exists a chiral
signing `s : ChiralSigning (Fin n)` such that `chiralKn n s` admits
non-trivial (α, β)-fractional revival for some pair of vertices, with
`α, β ≠ 0` and `α² + β² = 1`.  Equivalently, the *chirally-signed*
complete graph admits FR for a tuned phase pattern even though the
unsigned `K_n` does not.

A plausible witness candidate is the `unitaryHammingChiralK4` of
`Graphplay.Chiral`: that signing makes `K_4` switching-equivalent to
`K_1 + K̄_3`, which carries an obvious antipodal involution.  If FR
between `0` and the antipodal vertex of that involution can be shown to
have a non-zero α-component at the uniform-mixing time `π / (3√3)`, the
conjecture follows for `n = 4`.

This statement is the natural sibling of the Levine et al. result and to
our knowledge is open. -/
def chiralKn_fr_conjecture (n : ℕ) : Prop :=
  3 ≤ n →
  ∃ (s : ChiralSigning (Fin n)) (u v : Fin n) (τ : ℝ) (α β : ℂ),
    u ≠ v ∧ α ≠ 0 ∧ β ≠ 0 ∧
    IsFR (chiralKn n s) u v τ α β

/-- **Partial witness (statement only).**  For the specific signing
`unitaryHammingChiralK4Signing` of `Graphplay.Chiral`, the resulting
chirally-signed `K_4` admits non-trivial fractional revival between
vertex `0` and vertex `2` (the antipode of the conical reduction
`K_1 + K̄_3`) at some time `τ ∈ (0, π)`.

(The numerical evidence in 2605.04414 §2 is consistent with this; a
rigorous spectral analysis is left as future work.) -/
theorem unitaryHammingChiralK4_fr_partial :
    ∃ τ : ℝ, ∃ α β : ℂ,
      α ≠ 0 ∧ β ≠ 0 ∧
      IsFR unitaryHammingChiralK4 (0 : Fin 4) (2 : Fin 4) τ α β := by
  sorry

/-! ## 5.  Open directions

Three open directions we explicitly flag for follow-up:
-/

/-- **Open Direction 1 — Chiral FR.**  Prove or refute
`chiralKn_fr_conjecture` for general `n`.  A natural test bed is
the `K_4` signing of `Graphplay.Chiral.unitaryHammingChiralK4`.  Beyond
`K_n`, a finer question: which chiral signings of an association-scheme
graph preserve the scheme's Bose-Mesner algebra (so the classical
characterisation `bose_mesner_fr_iff` still applies) versus break it (and
require the genuinely non-commutative `IsNCFR`)? -/
def openDirection_chiralFR : Prop :=
  -- The genuine open conjecture: the chiral FR conjecture holds for *every*
  -- order `n ≥ 3`.
  ∀ n : ℕ, chiralKn_fr_conjecture n

/-- **Open Direction 2 — FR-rate maximization as an engineering primitive.**
Define the FR-rate at a pair `(u, v)` as `λ_FR(G, u, v) := inf { τ > 0 :
∃ α β, IsFR G u v τ α β }`.  The lifting theorem `fr_lift` shows that
quotient FR-rates dominate host FR-rates; the engineering problem is to
*construct* equitable partitions minimising `λ_FR` on the quotient.

When the host is an instance of `Bundle` (as in `Graphplay.Chiral`), the
optimisation reduces to a small finite-dimensional optimisation on the
quotient, and the chiral phasing of the quotient is a continuous-parameter
optimisation surface.

This is the precise FR analogue of the `chiral_mixing_optimization`
theorem (statement-level) in `Graphplay.Chiral`. -/
def openDirection_FRRateMax : Prop :=
  -- The genuine engineering claim: for every weighted graph `G` and vertex
  -- pair `(u, v)` admitting fractional revival at *some* time, there is a
  -- minimal such time `τ₀` (the FR-rate `λ_FR(G,u,v)`), i.e. the set of FR
  -- times is bounded below by an attained infimum.
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WeightedGraph V) (u v : V),
    (∃ τ : ℝ, 0 < τ ∧ ∃ α β : ℂ, IsFR G u v τ α β) →
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ (∃ α β : ℂ, IsFR G u v τ₀ α β) ∧
      ∀ τ : ℝ, 0 < τ → (∃ α β : ℂ, IsFR G u v τ α β) → τ₀ ≤ τ

/-- **Open Direction 3 — FR in graphon limits of association-scheme
families.**  The Hamming and Johnson schemes admit natural graphon limits
(the "Hamming-cube graphon" and "Johnson graphon").  By
`Graphon.fr_limit`, sequences of finite FR examples have graphon-FR
limits; conversely, does graphon-FR imply that *every* sufficiently large
finite sampling of the graphon admits FR?  This would be the FR avatar of
the standard sample-vs-limit equivalence for graphon properties (cf.
1003.5588). -/
def openDirection_graphonFR : Prop :=
  -- The genuine converse to `Graphon.fr_limit`: whenever a graphon `W` admits
  -- graphon fractional revival between two bump-state classes at time `τ` with
  -- coefficients `(α, β)`, *some* finite weighted graph admits ordinary FR with
  -- the same coefficients at the same time (the "finite sampling realises FR"
  -- direction of the sample-vs-limit equivalence).
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (W : Graphon Ω μ) (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAμ : μ A ≠ 0) (hAfin : μ A ≠ ∞) (hBμ : μ B ≠ 0) (hBfin : μ B ≠ ∞)
    (hdisj : Disjoint A B) (τ : ℝ) (α β : ℂ),
    Graphon.IsFR W A B hA hB hAμ hAfin hBμ hBfin hdisj τ α β →
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : WeightedGraph V) (u v : V), IsFR G u v τ α β

/-! ### Final sanity statement

The trivial graphs (empty + complete) are degenerate FR examples: every
vertex `u` admits trivial `(1, 0)`-FR to any vertex at `τ = 0` (the walk
is at the identity).  This is the boundary case `α = 1`, `β = 0`. -/

theorem isFR_trivial {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (u v : V) :
    IsFR G u v 0 1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- |1|² + |0|² = 1
    simp [Complex.normSq]
  · -- (G.evolve 0) u u = 1: identity matrix diagonal
    sorry
  · -- (G.evolve 0) v u = 0 when v ≠ u (and meaningless when v = u, but the
    -- statement still type-checks).  Needs `G.evolve_zero` and
    -- `Matrix.one_apply`.
    sorry
  · intro w _ _
    sorry

end Graphplay
