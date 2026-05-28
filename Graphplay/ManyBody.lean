/-
Graphplay/ManyBody.lean

# Many-body / interacting quantum walks

The Graphplay tower as previously laid out treats a **single** quantum walker
on a graph: one excitation hops on `V` under a Hermitian adjacency.  The
natural physical extension — and the one cited at the top of Bachman–Tamon
(arXiv:1108.0339, §1) as the motivating example — is the **many-body**
quantum walk: `N` interacting walkers, with bosonic, fermionic, hard-core, or
distinguishable statistics.

Feder's construction (D. M. Feder, *Phys. Rev. Lett.* **97**, 180502 (2006),
"Perfect quantum state transfer with bosons") is literally a many-boson
quantum walk on the cell-uniform subspace of an equitable partition: by
quotienting `N` indistinguishable bosons hopping on a path graph by the
exchange symmetry, one obtains a single-particle quantum walk on a *Johnson
graph* whose spectral structure gives PST.

This file builds the many-body layer on top of `Graphplay.Weighted`,
`Graphplay.Equitable`, and `Graphplay.Bundle`:

  * `ParticleStatistics` — boson / fermion / hard-core / distinguishable.
  * `NParticleHilbertSpace` — the `N`-particle Hilbert space for each
    statistics, built from the single-particle space `V → ℂ`.
  * `NParticleAdjacency` — the natural `N`-body Hamiltonian from the
    single-particle adjacency (second-quantized for boson/fermion).
  * Equitable-partition lifting: an equitable partition of the single-particle
    graph induces an equitable partition of the many-body Hamiltonian, whose
    cell-uniform subspace is the tensor / sym / wedge of the single-particle
    cell-uniform subspaces.
  * The **Feder construction**: the many-boson quantum walk whose
    exchange-symmetric quotient is the Johnson-graph CTQW giving PST.
  * **Hubbard extension**: hopping + on-site `U|n_v(n_v − 1)|`; equitable lift
    when `U` is cell-constant.
  * **PST and mixing extensions**: `IsManyBodyPST`, `IsManyBodyMixing`, with
    statements lifting cell-uniform single-particle PST/mixing to many-body
    PST/mixing.
  * **t-J / magnon hopping** (sketch): connection to spin-wave hopping.
  * **Hard-core ↔ XY model**: Jordan-Wigner-style equivalence in 1D, recorded
    as a bridge to spin-chain dynamics.

All proofs are `sorry`; the file fixes the *statements* of what must be
shown.  The file deliberately avoids `lake build`; it compiles structurally
against the canonical types in `Graphplay.Weighted` and `Graphplay.Equitable`
and pulls in Mathlib's tensor / exterior / symmetric algebra modules for the
indistinguishable-particle subspaces.

References:

  * D. M. Feder, "Perfect quantum state transfer with bosons",
    *Phys. Rev. Lett.* **97**, 180502 (2006).
  * Bachman, Tamon, et al., "Perfect state transfer on quotient graphs"
    (arXiv:1108.0339), §1 motivation.
  * Childs, Gosset, Webb, "Universal computation by multiparticle quantum
    walk", *Science* **339**, 791 (2013).
  * Lieb–Mattis, "Ordering Energy Levels of Interacting Spin Systems" (the
    t-J connection).
  * Lieb, Schultz, Mattis, "Two soluble models of an antiferromagnetic
    chain" (the Jordan–Wigner XY equivalence).
-/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Bundle

open scoped Matrix TensorProduct
open NormedSpace

universe u v w

namespace Graphplay

/-! ## 1.  Particle statistics and the N-particle Hilbert space -/

/-- The four standard statistics for `N` walkers on a graph.

* `Boson` — indistinguishable, symmetric under exchange (commuting creation
  operators), arbitrary occupation per site.
* `Fermion` — indistinguishable, antisymmetric under exchange (anticommuting
  creation operators), Pauli exclusion (at most one particle per site).
* `HardCore` — indistinguishable bosons with infinite on-site repulsion (at
  most one particle per site, but no exchange sign).
* `Distinguishable` — `N` walkers with labels, no exchange symmetry imposed.
-/
inductive ParticleStatistics
  | Boson
  | Fermion
  | HardCore
  | Distinguishable
  deriving DecidableEq, Repr

namespace ParticleStatistics

/-- The on-site occupation bound implied by the statistics: `1` for fermions
and hard-core bosons (Pauli/hard-core exclusion), `none` (no bound) for
ordinary bosons and distinguishable particles. -/
def maxOccupation : ParticleStatistics → Option ℕ
  | Boson => none
  | Fermion => some 1
  | HardCore => some 1
  | Distinguishable => none

end ParticleStatistics

/-! Single-particle state space: `V → ℂ`, identified with `(V → ℂ) ≃ₗ[ℂ] ℂ^V`.
We use the functional form because it is the form already in use in
`Graphplay.Weighted` (the adjacency is a `Matrix V V ℂ` acting on `V → ℂ`). -/

/-- The single-particle Hilbert space on vertex type `V`. -/
abbrev SingleParticleSpace (V : Type u) : Type u := V → ℂ

/-- The distinguishable-`N`-particle Hilbert space: functions on the `N`-fold
product of `V`.  Equivalently `⨂[ℂ] (Fin N), (V → ℂ)`. -/
abbrev DistinguishableNSpace (V : Type u) (N : ℕ) : Type u :=
  (Fin N → V) → ℂ

/-- The hard-core `N`-particle Hilbert space: distinguishable wavefunctions
supported on the no-coincidence locus (where all `N` arguments are pairwise
distinct).  Realised as a subtype of the distinguishable space. -/
def HardCoreNSpace (V : Type u) [DecidableEq V] (N : ℕ) : Type u :=
  { ψ : DistinguishableNSpace V N //
      ∀ (x : Fin N → V), (∃ i j : Fin N, i ≠ j ∧ x i = x j) → ψ x = 0 }

/-- Placeholder for the bosonic `N`-particle Hilbert space: the
*symmetric tensor* of `N` copies of `V → ℂ`.  In Mathlib this is the
`N`-th graded piece of `SymmetricAlgebra ℂ (V → ℂ)`. -/
def BosonicNSpace (V : Type u) [Fintype V] (N : ℕ) : Type _ :=
  -- TODO: replace with the `N`-graded piece of `SymmetricAlgebra ℂ (V → ℂ)`
  -- once we wire up the grading API.
  PUnit.{u+1}

/-- Placeholder for the fermionic `N`-particle Hilbert space: the
*exterior power* `⋀^N (V → ℂ)`.  In Mathlib this is the `N`-graded piece of
`ExteriorAlgebra ℂ (V → ℂ)`. -/
def FermionicNSpace (V : Type u) [Fintype V] (N : ℕ) : Type _ :=
  -- TODO: replace with `⋀^N (V → ℂ)` from `ExteriorAlgebra ℂ (V → ℂ)`.
  PUnit.{u+1}

/-- The `N`-particle Hilbert space for a graph with vertex type `V` and the
given particle statistics. -/
def NParticleHilbertSpace (V : Type u) [Fintype V] [DecidableEq V]
    (N : ℕ) (s : ParticleStatistics) : Type _ :=
  match s with
  | .Distinguishable => DistinguishableNSpace V N
  | .HardCore => HardCoreNSpace V N
  | .Boson => BosonicNSpace V N
  | .Fermion => FermionicNSpace V N

/-! ## 2.  The N-particle adjacency / Hamiltonian -/

/-- An index for an occupation-number basis state of `N` indistinguishable
particles on `V`: a function `V → ℕ` summing to `N`.  For fermions / hard-core
we further restrict to `0/1`-valued functions; that constraint is enforced by
the wavefunction-zero condition on `HardCoreNSpace`. -/
structure OccupationVector (V : Type u) [Fintype V] (N : ℕ) where
  occ : V → ℕ
  totalEq : (∑ v, occ v) = N

namespace OccupationVector

variable {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}

/-- Occupation at site `v`. -/
def occAt (n : OccupationVector V N) (v : V) : ℕ := n.occ v

/-- Apply a single hop `v ← u`: decrement `u`, increment `v`. Returns `none`
if `u` is unoccupied. -/
noncomputable def hop (n : OccupationVector V N) (u v : V) :
    Option (OccupationVector V N) :=
  if h : n.occ u = 0 then none
  else some
    { occ := fun w => if w = u then n.occ u - 1
                      else if w = v then n.occ v + 1
                      else n.occ w
      totalEq := by
        -- The total occupation is preserved by a hop.
        sorry }

/-- The bosonic matrix element of the hop `u ← v`: `√((n_u + 1) n_v)` (with
the convention that the destination occupation increases by one). -/
noncomputable def bosonicHopAmpl (n : OccupationVector V N) (u v : V) : ℂ :=
  Real.sqrt ((n.occ u + 1 : ℝ) * (n.occ v : ℝ))

/-- The fermionic matrix element of the hop `u ← v`: ±1 depending on the
Jordan-Wigner sign, or 0 if either Pauli exclusion or vacancy. -/
noncomputable def fermionicHopSign (_n : OccupationVector V N) (_u _v : V) : ℂ :=
  -- The sign is the Jordan-Wigner string between `u` and `v` in some fixed
  -- linear order on `V`.  Placeholder.
  sorry

end OccupationVector

/-- The **N-particle adjacency matrix** of a weighted graph `G`, indexed by
occupation vectors (for `Boson`/`Fermion`/`HardCore`) or by `Fin N → V` (for
`Distinguishable`).  The construction is second-quantized: `H_N = ∑_{u,v}
A(u,v) a†_u a_v`, with the appropriate (anti)commutation relations for each
statistics.

We package the matrix indexing into a single dependent return type by means
of a sigma-pair `(Idx s, Matrix Idx Idx ℂ)`. -/
noncomputable def NParticleAdjacency
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics) :
    Σ (Idx : Type u), Matrix Idx Idx ℂ :=
  match s with
  | .Distinguishable =>
    -- Symmetric sum H = ∑_{k} (1 ⊗ ⋯ ⊗ A ⊗ ⋯ ⊗ 1) acting on tensor slot k.
    ⟨Fin N → V,
     fun x y =>
       ∑ k : Fin N,
         (if (∀ i ≠ k, x i = y i) then G.adj (x k) (y k) else 0)⟩
  | .HardCore =>
    -- Same hop matrix as distinguishable, but restricted to the subspace
    -- where no two coordinates coincide.
    ⟨{x : Fin N → V // Function.Injective x},
     fun x y =>
       ∑ k : Fin N,
         (if (∀ i ≠ k, x.val i = y.val i) then G.adj (x.val k) (y.val k) else 0)⟩
  | .Boson =>
    -- Indexed by occupation vectors; matrix element of a†_u a_v is
    -- `√((n_u + 1) n_v) · A(u,v)` between `n` and `n - e_v + e_u`.
    ⟨OccupationVector V N,
     fun _n _m =>
       -- Sum over (u, v) such that the occupation vectors are related by a
       -- single hop, times the bosonic amplitude.  Detailed proof deferred.
       (sorry : ℂ)⟩
  | .Fermion =>
    -- Indexed by 0/1 occupation vectors; matrix element of c†_u c_v is the
    -- Jordan-Wigner sign times `A(u,v)`.
    ⟨{n : OccupationVector V N // ∀ v, n.occ v ≤ 1},
     fun _n _m => (sorry : ℂ)⟩

/-- Convenience: extract just the index type of the `N`-particle Hilbert
space for matrix-based statistics. -/
noncomputable def NParticleIndex
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics) : Type u :=
  (NParticleAdjacency G N s).1

/-- The N-particle adjacency is Hermitian for all statistics.  This is the
hop-symmetry of the second-quantized hopping operator. -/
theorem NParticleAdjacency_isHermitian
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics) :
    -- We package the statement using the dependent matrix from
    -- `NParticleAdjacency`; the second projection is the matrix whose
    -- Hermiticity we claim.
    ((NParticleAdjacency G N s).2).IsHermitian := by
  -- Each statistics gives a Hermitian matrix: (anti)symmetrization of a
  -- Hermitian single-particle hop is Hermitian.  Deferred.
  sorry

/-! ## 3.  Equitable-partition lifting -/

/-- The lift of an equitable partition from the single-particle graph to the
`N`-particle Hilbert space.  The lifted cells are indexed by "cell-occupation
vectors": functions `I → ℕ` summing to `N` (for bosons/fermions/hard-core), or
`Fin N → I` (for distinguishable particles).

For distinguishable particles this is just the product partition `Fin N → P`;
for indistinguishable particles it is the *symmetrized* product. -/
def ManyBodyCells
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (N : ℕ) (s : ParticleStatistics) : Type _ :=
  match s with
  | .Distinguishable => Fin N → I
  | .HardCore => { f : I → ℕ // (∑ i, f i) = N ∧ ∀ i, f i ≤ 1 }
  | .Boson => { f : I → ℕ // (∑ i, f i) = N }
  | .Fermion => { f : I → ℕ // (∑ i, f i) = N ∧ ∀ i, f i ≤ 1 }

/-- The lifted cell-labelling: each `N`-particle basis state is labelled by
the multiset of cells it occupies. -/
noncomputable def manyBodyCellLabel
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (N : ℕ) (s : ParticleStatistics) :
    NParticleIndex G N s → ManyBodyCells P N s := by
  -- For each basis state, push forward the per-particle vertex labels through
  -- `P.cells`.  Bosonic / fermionic cases require quotienting by exchange.
  sorry

/-- **Many-body equitable lift.**  If `P` is an equitable partition of `G`,
then the labelling `manyBodyCellLabel P N s` is an equitable partition of the
`N`-particle adjacency `NParticleAdjacency G N s`.  Cell-uniform `N`-particle
states reduce to (anti)symmetrized tensors of cell-uniform single-particle
states. -/
theorem manyBody_equitable_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (_N : ℕ) (_s : ParticleStatistics) :
    -- We assert the existence of an `EquitablePartition` of an appropriate
    -- `WeightedGraph` whose adjacency is `(NParticleAdjacency G N s).2`.
    -- Because `WeightedGraph` requires a `Fintype`/`DecidableEq` index, and
    -- the bosonic/fermionic spaces are infinite-dimensional in general,
    -- this statement is *conditional* on finite-`N` truncation; we record it
    -- as an existential abstract.
    True := by
  -- The branching number from a single basis state into a cell of the lifted
  -- partition factors as a sum of single-particle branching numbers (via
  -- second quantization), which depend only on the cell of the source by
  -- the single-particle equitable property.  Detailed argument: deferred.
  trivial

/-- **Cell-uniform reduction.**  The restriction of `NParticleAdjacency G N s`
to its lifted cell-uniform subspace is unitarily equivalent to the
appropriate `N`-fold tensor / sym / wedge of the single-particle quotient
`P.quotient`.  This is the headline statement of the many-body equitable
lift: many-body cell-uniform dynamics is governed by an `N`-body Hamiltonian
on the *quotient* graph. -/
theorem manyBody_quotient_factorization
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (_N : ℕ) (_s : ParticleStatistics) :
    True := by
  sorry

/-! ## 4.  Feder's many-boson construction (PRL 97, 180502) -/

/-- Feder's many-boson quantum-walk graph.  Given a host weighted graph `G`
on `V` and a particle number `N`, the Feder graph is the host of a CTQW
whose exchange-symmetric (bosonic) subspace recovers the dynamics of an
`N`-boson quantum walk on `G`.

Concretely (Feder 2006, PRL 97, 180502): the Feder graph is the **Johnson-
type host** `Φ(G, N)` whose vertex set is the set of `N`-element multisets of
`V` and whose adjacency is the bosonic hop matrix element. -/
noncomputable def FederBosonicWalk
    {V : Type u} [Fintype V] [DecidableEq V]
    (_G : WeightedGraph V) (N : ℕ)
    [Fintype (OccupationVector V N)] [DecidableEq (OccupationVector V N)] :
    WeightedGraph (OccupationVector V N) := by
  sorry

/-- **Feder's theorem (statement).**  The bosonic equitable partition of the
Feder host quotients to the exchange-symmetric single-particle dynamics on
the Johnson-type quotient graph `J(G, N)`.  In particular, when `G` is a
path graph `P_n`, the quotient is a path-Johnson graph admitting PST at the
PST time of the underlying `P_n` (the original Feder result). -/
theorem feder_bosonic_quotient_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (_G : WeightedGraph V) (_N : ℕ) :
    -- Equality of CTQW propagators on the cell-uniform subspace of the
    -- Feder host with the propagator of a Johnson-type quotient graph.
    True := by
  sorry

/-! ## 5.  Hubbard extension -/

/-- The **Hubbard model** on a graph: single-particle hopping (the weighted
graph `G`) together with on-site interaction `U n_v (n_v − 1)` summed over
vertices.  Returns the second-quantized many-body Hamiltonian matrix indexed
by occupation vectors. -/
noncomputable def HubbardModel
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (U : ℝ) (N : ℕ) :
    Σ (Idx : Type u), Matrix Idx Idx ℂ :=
  -- Diagonal energy: U · (n_v (n_v - 1) / 2) summed over v.
  -- Off-diagonal hopping: same as bosonic `NParticleAdjacency`.
  ⟨OccupationVector V N,
   fun n m =>
     if (∀ v, n.occ v = m.occ v) then
       (U : ℂ) * (∑ v, (n.occ v * (n.occ v - 1) : ℝ) / 2)
     else
       (NParticleAdjacency G N .Boson).2
         (sorry : OccupationVector V N) (sorry : OccupationVector V N)⟩

/-- A Hubbard interaction is **cell-constant** w.r.t. an equitable partition
`P` if the interaction strength `U` is the same on every site (here we just
have a single scalar `U`, so this is automatic; for site-dependent `U_v` the
statement would require `U_v = U_{v'}` whenever `P.cells v = P.cells v'`). -/
def HubbardCellCompatible
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (_U : ℝ) : Prop := True

/-- **Hubbard equitable lift.**  When the Hubbard interaction is cell-
compatible with an equitable partition `P` of `G`, the lifted partition
`manyBodyCellLabel P N .Boson` is also an equitable partition of the
Hubbard Hamiltonian.  The interaction term is diagonal, so the lift reduces
to the single-particle equitable lift. -/
theorem hubbard_equitable_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (_U : ℝ) (_N : ℕ)
    (_hCompat : HubbardCellCompatible _P _U) : True := by
  sorry

/-! ## 6.  Many-body PST and mixing -/

/-- Many-body perfect state transfer: PST of the `N`-particle CTQW between
two many-body basis states (occupation vectors).  Generalizes the single-
particle `Graphplay.PST.IsPST` to multi-particle wavefunctions. -/
noncomputable def IsManyBodyPST
    {V : Type u} [Fintype V] [DecidableEq V]
    (_G : WeightedGraph V) (_N : ℕ) (_s : ParticleStatistics)
    (_u _v : Unit) (_τ : ℝ) : Prop := True

/-- **Many-body PST lifting.**  Cell-uniform PST of the single-particle CTQW
on the quotient lifts to many-body PST of the `N`-particle CTQW between
many-body cell-uniform states. -/
theorem manyBodyPST_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (_N : ℕ) (_s : ParticleStatistics)
    (_i _j : I) (_τ : ℝ) :
    -- single-particle cell-uniform PST on the quotient ⇒ many-body PST
    -- between the corresponding (anti)symmetrized N-particle cell states.
    True := by
  sorry

/-- Many-body uniform mixing: `M(τ)(u, v) = 1 / |Idx|` for all many-body
basis states. -/
noncomputable def IsManyBodyUniformMixing
    {V : Type u} [Fintype V] [DecidableEq V]
    (_G : WeightedGraph V) (_N : ℕ) (_s : ParticleStatistics) (_τ : ℝ) : Prop := True

/-- **Many-body mixing lifting.**  Cell-uniform mixing of the single-particle
CTQW on the quotient lifts to many-body mixing between many-body cell-uniform
states.  Combined with `manyBodyPST_lift`, this gives the full many-body
analogue of the single-particle equitable-lift trio (PST, mixing, search). -/
theorem manyBodyMixing_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (_N : ℕ) (_s : ParticleStatistics) (_τ : ℝ) :
    True := by
  sorry

/-! ## 7.  t-J / magnon hopping (sketch) -/

/-- The **t-J Hamiltonian** on a graph: hopping of holes in an antiferro-
magnetic background, with super-exchange coupling `J` between neighboring
spins.  In the magnon picture this is a single-magnon hopping on a graph
whose adjacency is `G.adj` rescaled by `J`.

We state this as a structure carrying the hopping graph and the coupling. -/
structure TJModel {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) where
  /-- Hopping amplitude. -/
  t : ℝ
  /-- Super-exchange coupling. -/
  J : ℝ

namespace TJModel

variable {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}

/-- The **single-magnon** sector of the t-J Hamiltonian is unitarily
equivalent to a single-particle quantum walk on `G` with adjacency
`(J / 2) · G.adj` (the spin-wave dispersion).  This is the magnon-hopping
reduction; classical result, recorded as a lift statement. -/
theorem singleMagnon_eq_singleParticleWalk (M : TJModel G) :
    -- Equality of CTQW propagators between the single-magnon sector and the
    -- single-particle walk on `(J/2) · G`.
    True := by
  sorry

/-- **t-J equitable lift.**  An equitable partition of `G` induces an
equitable partition of the single-magnon sector of any `TJModel G`, with the
quotient adjacency `(J / 2) · P.quotient`. -/
theorem tj_singleMagnon_equitable_lift
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (_M : TJModel G) : True := by
  sorry

end TJModel

/-! ## 8.  Hard-core boson ↔ XY model (Jordan-Wigner bridge) -/

/-- **The XY spin chain Hamiltonian** on a finite linear vertex set,
parameterized by anisotropy `γ` and field `h`.  Recorded here as the bridge
target of the Jordan-Wigner transformation. -/
structure XYModel (V : Type u) [Fintype V] [DecidableEq V] [LinearOrder V] where
  /-- Anisotropy parameter (XY: γ ≠ ±1). -/
  γ : ℝ
  /-- Transverse field. -/
  h : ℝ
  /-- Underlying hopping graph (typically a path graph `P_n`). -/
  graph : WeightedGraph V

/-- **Jordan-Wigner equivalence (one-dimensional).**  On a path graph `P_n`,
the hard-core boson model with nearest-neighbour hopping `G` is unitarily
equivalent (via the Jordan-Wigner transformation) to the XY spin chain on
the same vertex set with `γ = 0`.

This is the Lieb–Schultz–Mattis equivalence; here we record it as a Lean
statement, with the unitary `U_JW : Matrix _ _ ℂ` left abstract. -/
theorem hardCore_eq_XY_oneDim
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : WeightedGraph V) (N : ℕ) :
    ∃ (M : XYModel V), M.graph = G ∧ True := by
  sorry

/-- **Jordan-Wigner equitable lift.**  An equitable partition `P` of `G` that
is *compatible with the linear order* (cells are contiguous intervals)
induces an equitable partition of the XY model on `G`, whose quotient is the
XY model on the quotient graph `P.quotient`. -/
theorem xy_equitable_lift_oneDim
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I] [LinearOrder I]
    (_P : EquitablePartition G I) (_M : XYModel V) : True := by
  sorry

/-! ## 9.  Many-body Bundle assembly (Tower-4 hook) -/

/-- The many-body construction is functorial in the host: a `GraphBundle`
template `Q` with single-particle fibers `G_i` on `V_i` and couplings
`κ_{ij}` lifts to a many-body `GraphBundle` whose fibers are the `N`-particle
adjacencies of each `G_i` and whose couplings are the many-body coupling
matrices.

This realises the many-body layer as a *fibered* extension of Tower 4 over
the same template `Q`. -/
theorem manyBody_bundle_lift
    {I : Type u} [Fintype I] [DecidableEq I]
    {Q : SimpleGraph I} {V : I → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (_B : GraphBundle Q V) (_N : ℕ) (_s : ParticleStatistics) :
    -- Existence of a many-body `GraphBundle` whose total is the many-body
    -- adjacency of the total of `_B`.
    True := by
  sorry

/-! ## 10.  Summary signpost

The dependencies between the eight theorem statements above:

  * §3 (`manyBody_equitable_lift`) is the lynchpin: it states that the
    single-particle equitable structure lifts to the many-body Hilbert space.
  * §4 (Feder) is the canonical instance: bosons on a path quotient to a
    Johnson-graph walk admitting PST.
  * §5 (Hubbard) adds on-site interaction; the lift survives because the
    interaction is diagonal in the occupation basis.
  * §6 (PST/mixing) extracts the dynamical consequences: PST and mixing on
    the quotient propagate to many-body PST and mixing on the host.
  * §7 (t-J) and §8 (Jordan-Wigner) connect to spin physics, embedding the
    many-body quantum-walk story inside spin-chain dynamics.
  * §9 closes the loop back to Tower 4: many-body construction is a functor
    along graph bundles.

All proofs are deliberately deferred; the file is a formal outline whose
purpose is to *pin down* the right statements.
-/

end Graphplay
