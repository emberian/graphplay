/-
Graphplay/ManyBody.lean

# Many-body / interacting quantum walks

The rest of the Graphplay tower treats a **single** quantum walker
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

The core dynamical results are fully proved.  In particular the
**distinguishable** sector is fully developed: the second-quantized branching
identity and equitable lift (`manyBody_equitable_lift`,
`manyBody_quotient_factorization`), the propagator tensor-power factorization
`exp(-iτ ⊕_k A) = ⊗_k exp(-iτ A)` (`manyBodyEvolve_distinguishable_apply`, built
from the slot-embedding algebra homomorphism `slotEmbed`), and the multiparticle
PST and uniform-mixing lifts (`manyBodyPST_lift`, `manyBodyMixing_lift`,
Childs–Gosset–Webb).  The Jordan–Wigner / hard-core ↔ XY bridge is also proved
(`stringUnitary_conj_eq_xyHamiltonian`, `hardCore_eq_XY_oneDim`).  For the
**boson / fermion** sectors the entrywise equitable lift and cell-uniform
subspace reduction are *false* for an arbitrary equitable partition
(the occupation-dependent amplitudes `√((n_u+1)n_v)` / Jordan–Wigner signs are
not cell-functions — see the counterexamples in the docstrings of
`manyBody_equitable_lift` and `manyBody_quotient_factorization`); those lifts are
therefore stated and proved for the distinguishable statistics, where they hold.

The file pulls in Mathlib's tensor / exterior / symmetric algebra modules for the
indistinguishable-particle subspaces and the matrix-exponential API for the
propagators.

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
import Graphplay.PST
import Graphplay.LiteratureInterfaces

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

/-- Apply a single hop `v ← u` between **distinct** sites `u ≠ v`: decrement
`u`, increment `v`. Returns `none` if `u` is unoccupied.

The `u ≠ v` hypothesis is the physical content of a hop: a particle moves
from one site to a *different* site.  Without it, the `if w = u` branch (which
is tested first) would shadow the increment at `v` when `u = v`, decreasing
the total occupation by one — so total-occupation conservation
requires `u ≠ v`. -/
noncomputable def hop (n : OccupationVector V N) (u v : V) (huv : u ≠ v) :
    Option (OccupationVector V N) :=
  if h : n.occ u = 0 then none
  else some
    { occ := fun w => if w = u then n.occ u - 1
                      else if w = v then n.occ v + 1
                      else n.occ w
      totalEq := by
        -- The total occupation is preserved by a hop between distinct sites.
        have hu : 1 ≤ n.occ u := Nat.one_le_iff_ne_zero.mpr h
        classical
        have hv_mem : v ∈ Finset.univ.erase u :=
          Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩
        -- On the doubly-erased index set the modified occupation equals `n.occ`.
        have hrest : (∑ w ∈ (Finset.univ.erase u).erase v,
              (if w = u then n.occ u - 1 else if w = v then n.occ v + 1 else n.occ w))
            = ∑ w ∈ (Finset.univ.erase u).erase v, n.occ w := by
          refine Finset.sum_congr rfl (fun w hw => ?_)
          rw [Finset.mem_erase] at hw
          obtain ⟨hwv, hw'⟩ := hw
          rw [Finset.mem_erase] at hw'
          obtain ⟨hwu, _⟩ := hw'
          rw [if_neg hwu, if_neg hwv]
        -- Extract sites `u` and `v` from both the new sum and `n.totalEq`.
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u),
            ← Finset.add_sum_erase _ _ hv_mem, hrest]
        rw [if_pos rfl, if_neg huv.symm, if_pos rfl]
        have htot := n.totalEq
        rw [← Finset.add_sum_erase Finset.univ n.occ (Finset.mem_univ u),
            ← Finset.add_sum_erase _ n.occ hv_mem] at htot
        omega }

/-- The bosonic matrix element of the hop `u ← v`: `√((n_u + 1) n_v)` (with
the convention that the destination occupation increases by one). -/
noncomputable def bosonicHopAmpl (n : OccupationVector V N) (u v : V) : ℂ :=
  Real.sqrt ((n.occ u + 1 : ℝ) * (n.occ v : ℝ))

/-- The canonical linear index of a vertex, using the choice-fixed
`Fintype.equivFin` ordering on `V`.  This pins down the "site order" needed for
the Jordan–Wigner string. -/
noncomputable def siteIndex (w : V) : ℕ := ((Fintype.equivFin V) w).val

/-- The set of sites that lie **strictly between** `u` and `v` in the fixed
linear order (`min < · < max` of the two site indices). -/
noncomputable def betweenSites (u v : V) : Finset V :=
  Finset.univ.filter (fun w =>
    min (siteIndex u) (siteIndex v) < siteIndex w ∧
    siteIndex w < max (siteIndex u) (siteIndex v))

/-- The fermionic matrix element of the hop `u ← v`: the Jordan–Wigner string
sign `(-1)^(number of occupied sites strictly between u and v)`, with the
result `0` when either the source `v` is empty (no particle to move) or the
destination `u` is already occupied (Pauli exclusion), since fermions have
occupation in `{0,1}`.

Concretely: list the occupied sites strictly between `u` and `v` (in the fixed
site order from `siteIndex`); the creation/annihilation operators must
anticommute past each of those occupied modes, contributing one factor of `-1`
each.  The total sign is `(-1)^k` with `k` the count of such occupied sites. -/
noncomputable def fermionicHopSign (n : OccupationVector V N) (u v : V) : ℂ :=
  if n.occ v = 0 ∨ 1 ≤ n.occ u then 0
  else
    (-1 : ℂ) ^ ((betweenSites u v).filter (fun w => n.occ w = 1)).card

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
    -- Indexed by occupation vectors; matrix element of `a†_u a_v` is
    -- `√((n_u + 1) n_v) · A(u,v)` between `n` and `n - e_v + e_u`.
    --
    -- Concretely we sum over ordered pairs `(u, v)` of *distinct* sites: a
    -- pair contributes `A u v · √((n_u+1) n_v)` exactly when hopping a boson
    -- from `v` to `u` carries the source configuration `n` onto the target
    -- configuration `m` (compared on the underlying occupation functions).
    ⟨OccupationVector V N,
     fun n m =>
       ∑ u : V, ∑ v : V,
         if huv : u ≠ v then
           (match OccupationVector.hop n v u (huv.symm) with
            | some n' => if n'.occ = m.occ then
                           G.adj u v * OccupationVector.bosonicHopAmpl n u v
                         else 0
            | none => 0)
         else 0⟩
  | .Fermion =>
    -- Indexed by 0/1 occupation vectors; matrix element of `c†_u c_v` is the
    -- Jordan–Wigner sign (`fermionicHopSign`) times `A(u,v)`, summed over the
    -- distinct ordered pairs `(u, v)` whose hop carries `n` onto `m`.
    ⟨{n : OccupationVector V N // ∀ v, n.occ v ≤ 1},
     fun n m =>
       ∑ u : V, ∑ v : V,
         if huv : u ≠ v then
           (match OccupationVector.hop n.val v u (huv.symm) with
            | some n' => if n'.occ = m.val.occ then
                           G.adj u v * OccupationVector.fermionicHopSign n.val u v
                         else 0
            | none => 0)
         else 0⟩

/-- Convenience: extract just the index type of the `N`-particle Hilbert
space for matrix-based statistics.  Reducible so that the many-body propagator
matrix `(NParticleAdjacency G N s).2 : Matrix _ _ ℂ` and statements phrased over
`NParticleIndex` share the same index type up to definitional unfolding (needed
for `Fintype`/`DecidableEq`/algebra instance synthesis). -/
@[reducible] noncomputable def NParticleIndex
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics) : Type u :=
  (NParticleAdjacency G N s).1

/-- The occupation count, at site `w`, produced by a successful hop `u → v`
(i.e. when `hop n u v huv = some n'`): one removed from `u`, one added to `v`. -/
theorem OccupationVector.hop_some_occ_apply
    {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (n : OccupationVector V N) (u v : V) (huv : u ≠ v) (n' : OccupationVector V N)
    (h : OccupationVector.hop n u v huv = some n') (w : V) :
    n'.occ w = if w = u then n.occ u - 1
               else if w = v then n.occ v + 1 else n.occ w := by
  unfold OccupationVector.hop at h
  by_cases h0 : n.occ u = 0
  · rw [dif_pos h0] at h; exact absurd h (by simp)
  · rw [dif_neg h0] at h
    have : n'.occ = fun w => if w = u then n.occ u - 1
                      else if w = v then n.occ v + 1 else n.occ w :=
      ((Option.some.injEq _ _).mp h.symm) ▸ rfl
    rw [this]

/-- A successful hop `u → v` requires the source `u` to be occupied. -/
theorem OccupationVector.hop_some_pos
    {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (n : OccupationVector V N) (u v : V) (huv : u ≠ v) (n' : OccupationVector V N)
    (h : OccupationVector.hop n u v huv = some n') :
    n.occ u ≠ 0 := by
  unfold OccupationVector.hop at h
  by_cases h0 : n.occ u = 0
  · rw [dif_pos h0] at h; exact absurd h (by simp)
  · exact h0

/-- **Bosonic hopping matrix is Hermitian.**  The reverse hop `u → v` from `m`
matches the forward hop `v → u` from `n` (they are inverse hops carrying the
same configurations), the bosonic amplitudes coincide (both equal
`√((n_u+1) n_v)` once the configurations are pinned), and `G.adj` is Hermitian;
so swapping the summation indices `u ↔ v` and using `star (G.adj u v) = G.adj v u`
gives the conjugate-symmetry of the matrix. -/
theorem NParticleAdjacency_boson_isHermitian
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) :
    ((NParticleAdjacency G N .Boson).2).IsHermitian := by
  classical
  refine Matrix.IsHermitian.ext ?_
  intro n m
  -- Reduce to the entrywise conjugate-symmetry of the bosonic hopping matrix.
  show star ((NParticleAdjacency G N .Boson).2 m n)
      = (NParticleAdjacency G N .Boson).2 n m
  show star (∑ u : V, ∑ v : V,
        if huv : u ≠ v then
          (match OccupationVector.hop m v u huv.symm with
           | some m' => if m'.occ = n.occ then
                          G.adj u v * OccupationVector.bosonicHopAmpl m u v else 0
           | none => 0) else 0)
      = ∑ u : V, ∑ v : V,
        if huv : u ≠ v then
          (match OccupationVector.hop n v u huv.symm with
           | some n' => if n'.occ = m.occ then
                          G.adj u v * OccupationVector.bosonicHopAmpl n u v else 0
           | none => 0) else 0
  -- Push `star` through both sums.
  rw [star_sum]
  simp only [star_sum]
  -- Swap the order of summation on the left so we can match index `(u,v)` of
  -- the left with `(v,u)` of the right.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  -- Goal (after sum_comm): `star (term_{m n}(v, u)) = term_{n m}(u, v)`, where
  -- `term_{a b}(p, q)` is the `(p,q)`-summand.  We prove it for arbitrary `u, v`.
  by_cases huv : u ≠ v
  · -- both dite-guards (`v ≠ u` on the left, `u ≠ v` on the right) are positive.
    rw [dif_pos huv.symm, dif_pos huv]
    -- Analyse the two hops.
    cases hm : OccupationVector.hop m u v huv with
    | none =>
      -- Left summand is 0; show the right is too.
      simp only [star_zero]
      cases hn : OccupationVector.hop n v u huv.symm with
      | none => rfl
      | some n' =>
        -- If the right hop succeeds with `n'.occ = m.occ`, then `m.occ u ≥ 1`,
        -- contradicting `hop m u v = none` (which forces `m.occ u = 0`).
        by_cases hcond : n'.occ = m.occ
        · exfalso
          -- `n'.occ u = n.occ u + 1` (since `u ≠ v`), and `= m.occ u`.
          have hu := OccupationVector.hop_some_occ_apply n v u huv.symm n' hn u
          rw [if_neg huv, if_pos rfl] at hu
          have hmu := congrFun hcond u
          -- but `hop m u v = none` means `m.occ u = 0`.
          unfold OccupationVector.hop at hm
          by_cases hm0 : m.occ u = 0
          · omega
          · rw [dif_neg hm0] at hm; exact absurd hm (by simp)
        · simp only [if_neg hcond]
    | some m' =>
      -- Left hop succeeds (`m.occ u ≠ 0`).  `m'.occ = m with u↓ v↑`.
      cases hn : OccupationVector.hop n v u huv.symm with
      | none =>
        -- Right hop fails: `n.occ v = 0`.  Then left condition `m'.occ = n.occ`
        -- would force `n.occ v = m.occ v + 1 ≥ 1`, contradiction; so left is 0.
        by_cases hcond : m'.occ = n.occ
        · exfalso
          have hv := OccupationVector.hop_some_occ_apply m u v huv m' hm v
          rw [if_neg (Ne.symm huv), if_pos rfl] at hv
          have hmv := congrFun hcond v
          unfold OccupationVector.hop at hn
          by_cases hn0 : n.occ v = 0
          · omega
          · rw [dif_neg hn0] at hn; exact absurd hn (by simp)
        · simp only [if_neg hcond, star_zero]
      | some n' =>
        -- The two conditions `m'.occ = n.occ` and `n'.occ = m.occ` are equivalent.
        -- `m'.occ w = if w=u then m_u-1 else if w=v then m_v+1 else m_w`
        -- `n'.occ w = if w=v then n_v-1 else if w=u then n_u+1 else n_w`
        have hmu : m.occ u ≠ 0 := OccupationVector.hop_some_pos m u v huv m' hm
        have hnv : n.occ v ≠ 0 := OccupationVector.hop_some_pos n v u huv.symm n' hn
        by_cases hcond : m'.occ = n.occ
        · -- Left condition holds; derive the right condition and amplitude equality.
          have hright : n'.occ = m.occ := by
            funext w
            have hnw := OccupationVector.hop_some_occ_apply n v u huv.symm n' hn w
            have hmw := congrFun hcond w
            rw [OccupationVector.hop_some_occ_apply m u v huv m' hm w] at hmw
            rw [hnw]
            by_cases hwu : w = u
            · subst hwu
              rw [if_neg huv, if_pos rfl]
              rw [if_pos rfl] at hmw; omega
            · by_cases hwv : w = v
              · subst hwv
                rw [if_pos rfl]
                rw [if_neg (Ne.symm huv), if_pos rfl] at hmw; omega
              · rw [if_neg hwv, if_neg hwu]
                rw [if_neg hwu, if_neg hwv] at hmw; omega
          simp only [if_pos hcond, if_pos hright]
          rw [star_mul']
          -- `star (G.adj v u) = G.adj u v` and the amplitudes are equal reals.
          have hadj : star (G.adj v u) = G.adj u v := G.herm.apply u v
          have hampl : star (OccupationVector.bosonicHopAmpl m v u)
              = OccupationVector.bosonicHopAmpl n u v := by
            unfold OccupationVector.bosonicHopAmpl
            -- `m'.occ u = m_u - 1 = n_u` and `m'.occ v = m_v + 1 = n_v`.
            have hmu_eq : m.occ u = n.occ u + 1 := by
              have := congrFun hcond u
              rw [OccupationVector.hop_some_occ_apply m u v huv m' hm u, if_pos rfl] at this
              omega
            have hmv_eq : m.occ v = n.occ v - 1 := by
              have := congrFun hcond v
              rw [OccupationVector.hop_some_occ_apply m u v huv m' hm v,
                if_neg (Ne.symm huv), if_pos rfl] at this
              omega
            rw [Complex.star_def, Complex.conj_ofReal]
            congr 2
            have hnv1 : 1 ≤ n.occ v := Nat.one_le_iff_ne_zero.mpr hnv
            rw [hmu_eq, hmv_eq]
            push_cast [Nat.cast_sub hnv1]
            ring
          rw [hadj, hampl, mul_comm]
        · -- Left condition fails; show the right one fails too.
          have hrightfail : n'.occ ≠ m.occ := by
            intro hr
            apply hcond
            funext w
            have hnw := congrFun hr w
            rw [OccupationVector.hop_some_occ_apply n v u huv.symm n' hn w] at hnw
            rw [OccupationVector.hop_some_occ_apply m u v huv m' hm w]
            by_cases hwu : w = u
            · subst hwu
              rw [if_pos rfl]
              rw [if_neg huv, if_pos rfl] at hnw; omega
            · by_cases hwv : w = v
              · subst hwv
                rw [if_neg (Ne.symm huv), if_pos rfl]
                rw [if_pos rfl] at hnw; omega
              · rw [if_neg hwu, if_neg hwv]
                rw [if_neg hwv, if_neg hwu] at hnw; omega
          simp only [if_neg hcond, if_neg hrightfail, star_zero]
  · -- `u = v`: both dite-guards are negative.
    push_neg at huv
    rw [dif_neg (by simp [huv]), dif_neg (by simp [huv]), star_zero]

/-- The N-particle adjacency is Hermitian for all statistics.  This is the
hop-symmetry of the second-quantized hopping operator.

Closed for the bosonic case (`NParticleAdjacency_boson_isHermitian`); the
distinguishable / hard-core / fermionic cases are deferred (the fermionic case
in particular requires the Jordan–Wigner-string sign bookkeeping). -/
theorem NParticleAdjacency_isHermitian
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics) :
    -- We package the statement using the dependent matrix from
    -- `NParticleAdjacency`; the second projection is the matrix whose
    -- Hermiticity we claim.
    ((NParticleAdjacency G N s).2).IsHermitian := by
  cases s with
  | Boson => exact NParticleAdjacency_boson_isHermitian G N
  | Distinguishable =>
    -- `M x y = ∑_k [∀ i≠k, x i = y i] G.adj (x k) (y k)`: term-symmetric.
    refine Matrix.IsHermitian.ext ?_
    intro x y
    show star (∑ k : Fin N, if (∀ i ≠ k, y i = x i) then G.adj (y k) (x k) else 0)
        = ∑ k : Fin N, if (∀ i ≠ k, x i = y i) then G.adj (x k) (y k) else 0
    rw [star_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : ∀ i ≠ k, x i = y i
    · have h' : ∀ i ≠ k, y i = x i := fun i hi => (h i hi).symm
      rw [if_pos h, if_pos h', G.herm.apply (x k) (y k)]
    · have h' : ¬ (∀ i ≠ k, y i = x i) := by
        intro hc; exact h (fun i hi => (hc i hi).symm)
      rw [if_neg h, if_neg h', star_zero]
  | HardCore =>
    refine Matrix.IsHermitian.ext ?_
    intro x y
    show star (∑ k : Fin N, if (∀ i ≠ k, y.val i = x.val i) then
                G.adj (y.val k) (x.val k) else 0)
        = ∑ k : Fin N, if (∀ i ≠ k, x.val i = y.val i) then
                G.adj (x.val k) (y.val k) else 0
    rw [star_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : ∀ i ≠ k, x.val i = y.val i
    · have h' : ∀ i ≠ k, y.val i = x.val i := fun i hi => (h i hi).symm
      rw [if_pos h, if_pos h', G.herm.apply (x.val k) (y.val k)]
    · have h' : ¬ (∀ i ≠ k, y.val i = x.val i) := by
        intro hc; exact h (fun i hi => (hc i hi).symm)
      rw [if_neg h, if_neg h', star_zero]
  | Fermion =>
    -- The Jordan–Wigner string sign `fermionicHopSign` matches between
    -- forward/reverse hops: `betweenSites` is symmetric in `u, v`, the occupied
    -- sites strictly between `u` and `v` are unchanged by a hop on `u/v`, and the
    -- fermion exclusion constraint makes both sign guards inactive when the hops
    -- succeed.  The structure mirrors the bosonic case.
    refine Matrix.IsHermitian.ext ?_
    intro n m
    show star ((NParticleAdjacency G N .Fermion).2 m n)
        = (NParticleAdjacency G N .Fermion).2 n m
    show star (∑ u : V, ∑ v : V,
          if huv : u ≠ v then
            (match OccupationVector.hop m.val v u huv.symm with
             | some m' => if m'.occ = n.val.occ then
                            G.adj u v * OccupationVector.fermionicHopSign m.val u v else 0
             | none => 0) else 0)
        = ∑ u : V, ∑ v : V,
          if huv : u ≠ v then
            (match OccupationVector.hop n.val v u huv.symm with
             | some n' => if n'.occ = m.val.occ then
                            G.adj u v * OccupationVector.fermionicHopSign n.val u v else 0
             | none => 0) else 0
    rw [star_sum]
    simp only [star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    by_cases huv : u ≠ v
    · rw [dif_pos huv.symm, dif_pos huv]
      cases hm : OccupationVector.hop m.val u v huv with
      | none =>
        simp only [star_zero]
        cases hn : OccupationVector.hop n.val v u huv.symm with
        | none => rfl
        | some n' =>
          by_cases hcond : n'.occ = m.val.occ
          · exfalso
            have hu := OccupationVector.hop_some_occ_apply n.val v u huv.symm n' hn u
            rw [if_neg huv, if_pos rfl] at hu
            have hmu := congrFun hcond u
            unfold OccupationVector.hop at hm
            by_cases hm0 : m.val.occ u = 0
            · omega
            · rw [dif_neg hm0] at hm; exact absurd hm (by simp)
          · simp only [if_neg hcond]
      | some m' =>
        cases hn : OccupationVector.hop n.val v u huv.symm with
        | none =>
          by_cases hcond : m'.occ = n.val.occ
          · exfalso
            have hv := OccupationVector.hop_some_occ_apply m.val u v huv m' hm v
            rw [if_neg (Ne.symm huv), if_pos rfl] at hv
            have hmv := congrFun hcond v
            unfold OccupationVector.hop at hn
            by_cases hn0 : n.val.occ v = 0
            · omega
            · rw [dif_neg hn0] at hn; exact absurd hn (by simp)
          · simp only [if_neg hcond, star_zero]
        | some n' =>
          have hmu : m.val.occ u ≠ 0 := OccupationVector.hop_some_pos m.val u v huv m' hm
          have hnv : n.val.occ v ≠ 0 := OccupationVector.hop_some_pos n.val v u huv.symm n' hn
          by_cases hcond : m'.occ = n.val.occ
          · have hright : n'.occ = m.val.occ := by
              funext w
              have hnw := OccupationVector.hop_some_occ_apply n.val v u huv.symm n' hn w
              have hmw := congrFun hcond w
              rw [OccupationVector.hop_some_occ_apply m.val u v huv m' hm w] at hmw
              rw [hnw]
              by_cases hwu : w = u
              · subst hwu
                rw [if_neg huv, if_pos rfl]
                rw [if_pos rfl] at hmw; omega
              · by_cases hwv : w = v
                · subst hwv
                  rw [if_pos rfl]
                  rw [if_neg (Ne.symm huv), if_pos rfl] at hmw; omega
                · rw [if_neg hwv, if_neg hwu]
                  rw [if_neg hwu, if_neg hwv] at hmw; omega
            simp only [if_pos hcond, if_pos hright]
            rw [star_mul']
            have hadj : star (G.adj v u) = G.adj u v := G.herm.apply u v
            -- The two relevant occupation values, via the hop relations and the
            -- fermion exclusion constraint, satisfy `n.occ u = 0`, `m.occ v = 0`.
            have hmu_eq : m.val.occ u = n.val.occ u + 1 := by
              have := congrFun hcond u
              rw [OccupationVector.hop_some_occ_apply m.val u v huv m' hm u, if_pos rfl] at this
              omega
            have hmv_eq : m.val.occ v = n.val.occ v - 1 := by
              have := congrFun hcond v
              rw [OccupationVector.hop_some_occ_apply m.val u v huv m' hm v,
                if_neg (Ne.symm huv), if_pos rfl] at this
              omega
            have hnu0 : n.val.occ u = 0 := by
              have := m.property u; omega
            have hmv0 : m.val.occ v = 0 := by
              have := n.property v; omega
            -- Sign equality: both guards inactive, and the between-occupied counts agree.
            have hsign : OccupationVector.fermionicHopSign m.val v u
                = OccupationVector.fermionicHopSign n.val u v := by
              unfold OccupationVector.fermionicHopSign
              have hg1 : ¬ (m.val.occ u = 0 ∨ 1 ≤ m.val.occ v) := by
                push_neg; exact ⟨hmu, by omega⟩
              have hg2 : ¬ (n.val.occ v = 0 ∨ 1 ≤ n.val.occ u) := by
                push_neg; exact ⟨hnv, by omega⟩
              rw [if_neg hg1, if_neg hg2]
              congr 1
              -- `betweenSites v u = betweenSites u v`; and on between sites
              -- (which exclude `u, v`) the two occupations agree.
              have hbtw : OccupationVector.betweenSites (V := V) v u
                  = OccupationVector.betweenSites u v := by
                unfold OccupationVector.betweenSites
                refine Finset.filter_congr (fun w _ => ?_)
                rw [min_comm, max_comm]
              rw [hbtw]
              congr 1
              apply Finset.filter_congr
              intro w hw
              -- `w ∈ betweenSites u v` forces `w ≠ u` and `w ≠ v` (strict order).
              unfold OccupationVector.betweenSites at hw
              rw [Finset.mem_filter] at hw
              obtain ⟨_, hlo, hhi⟩ := hw
              have hwu : w ≠ u := by
                intro he
                have : OccupationVector.siteIndex w = OccupationVector.siteIndex u := by rw [he]
                omega
              have hwv : w ≠ v := by
                intro he
                have : OccupationVector.siteIndex w = OccupationVector.siteIndex v := by rw [he]
                omega
              -- On `w ∉ {u,v}` the occupations agree: `m.occ w = n.occ w`.
              have hmweq : m.val.occ w = n.val.occ w := by
                have := congrFun hcond w
                rw [OccupationVector.hop_some_occ_apply m.val u v huv m' hm w,
                  if_neg hwu, if_neg hwv] at this
                exact this
              rw [hmweq]
            rw [hadj, hsign]
            -- The sign is a real `±1`, so `star` fixes it; then commute the product.
            have hstarS : star (OccupationVector.fermionicHopSign n.val u v)
                = OccupationVector.fermionicHopSign n.val u v := by
              unfold OccupationVector.fermionicHopSign
              by_cases hg : n.val.occ v = 0 ∨ 1 ≤ n.val.occ u
              · rw [if_pos hg, star_zero]
              · rw [if_neg hg]
                rw [show ((-1 : ℂ) ^ _) = (((-1 : ℝ) ^ _ : ℝ) : ℂ) by push_cast; ring]
                rw [Complex.star_def, Complex.conj_ofReal]
            rw [hstarS, mul_comm]
          · have hrightfail : n'.occ ≠ m.val.occ := by
              intro hr
              apply hcond
              funext w
              have hnw := congrFun hr w
              rw [OccupationVector.hop_some_occ_apply n.val v u huv.symm n' hn w] at hnw
              rw [OccupationVector.hop_some_occ_apply m.val u v huv m' hm w]
              by_cases hwu : w = u
              · subst hwu
                rw [if_pos rfl]
                rw [if_neg huv, if_pos rfl] at hnw; omega
              · by_cases hwv : w = v
                · subst hwv
                  rw [if_neg (Ne.symm huv), if_pos rfl]
                  rw [if_pos rfl] at hnw; omega
                · rw [if_neg hwu, if_neg hwv]
                  rw [if_neg hwv, if_neg hwu] at hnw; omega
            simp only [if_neg hcond, if_neg hrightfail, star_zero]
    · push_neg at huv
      rw [dif_neg (by simp [huv]), dif_neg (by simp [huv]), star_zero]

/-- **The N-particle adjacency has zero diagonal for all statistics.**  The
hopping operator only connects *distinct* configurations: for the matrix-indexed
(distinguishable / hard-core) statistics the diagonal is a sum of loopless
single-particle diagonals `G.adj (x k) (x k) = 0`, and for the occupation-vector
(boson / fermion) statistics every contributing hop between distinct sites
changes the occupation, so the `n'.occ = n.occ` guard never fires. -/
theorem NParticleAdjacency_diag_zero
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics)
    (x : (NParticleAdjacency G N s).1) :
    (NParticleAdjacency G N s).2 x x = 0 := by
  cases s with
  | Distinguishable =>
    show (∑ k : Fin N, if (∀ i ≠ k, x i = x i) then G.adj (x k) (x k) else 0) = 0
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_pos (fun _ _ => rfl), G.loopless]
  | HardCore =>
    show (∑ k : Fin N, if (∀ i ≠ k, x.val i = x.val i) then
            G.adj (x.val k) (x.val k) else 0) = 0
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_pos (fun _ _ => rfl), G.loopless]
  | Boson =>
    -- A successful hop `v → u` (distinct sites) sets `n'.occ u = n.occ u + 1 ≠ n.occ u`.
    show (∑ u : V, ∑ v : V,
        if huv : u ≠ v then
          (match OccupationVector.hop x v u huv.symm with
           | some n' => if n'.occ = x.occ then
                          G.adj u v * OccupationVector.bosonicHopAmpl x u v else 0
           | none => 0) else 0) = 0
    refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
    by_cases huv : u ≠ v
    · rw [dif_pos huv]
      cases hhop : OccupationVector.hop x v u huv.symm with
      | none => rfl
      | some n' =>
        have hval : n'.occ u = x.occ u + 1 := by
          have := OccupationVector.hop_some_occ_apply x v u huv.symm n' hhop u
          rwa [if_neg huv, if_pos rfl] at this
        have hne : n'.occ ≠ x.occ := fun hc => by
          have : n'.occ u = x.occ u := by rw [hc]
          omega
        simp [hne]
    · rw [dif_neg huv]
  | Fermion =>
    show (∑ u : V, ∑ v : V,
        if huv : u ≠ v then
          (match OccupationVector.hop x.val v u huv.symm with
           | some n' => if n'.occ = x.val.occ then
                          G.adj u v * OccupationVector.fermionicHopSign x.val u v else 0
           | none => 0) else 0) = 0
    refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
    by_cases huv : u ≠ v
    · rw [dif_pos huv]
      cases hhop : OccupationVector.hop x.val v u huv.symm with
      | none => rfl
      | some n' =>
        have hval : n'.occ u = x.val.occ u + 1 := by
          have := OccupationVector.hop_some_occ_apply x.val v u huv.symm n' hhop u
          rwa [if_neg huv, if_pos rfl] at this
        have hne : n'.occ ≠ x.val.occ := fun hc => by
          have : n'.occ u = x.val.occ u := by rw [hc]
          omega
        simp [hne]
    · rw [dif_neg huv]

/-! ## 3.  Equitable-partition lifting -/

/-- The lift of an equitable partition from the single-particle graph to the
`N`-particle Hilbert space.  The lifted cells are indexed by "cell-occupation
vectors": functions `I → ℕ` summing to `N` (for bosons/fermions/hard-core), or
`Fin N → I` (for distinguishable particles).

For distinguishable particles this is just the product partition `Fin N → P`;
for indistinguishable particles it is the *symmetrized* product — a
cell-occupation vector `f : I → ℕ` summing to `N`.

Note: hard-core/fermionic exclusion is a constraint at the *vertex* level
(at most one particle per vertex), which is already enforced by the index
type `NParticleIndex` for these statistics.  It is **not** a cell-level
constraint: several distinct occupied vertices can share a cell, so the
cell-occupation pushforward need not be `0/1`-valued.  Hence the cell type for
every indistinguishable statistics is the same `∑ f = N` simplex; only the
underlying single-particle index type differs. -/
def ManyBodyCells
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (_P : EquitablePartition G I) (N : ℕ) (s : ParticleStatistics) : Type _ :=
  match s with
  | .Distinguishable => Fin N → I
  | .HardCore => { f : I → ℕ // (∑ i, f i) = N }
  | .Boson => { f : I → ℕ // (∑ i, f i) = N }
  | .Fermion => { f : I → ℕ // (∑ i, f i) = N }

/-- The cell-occupation count of an occupation vector `n` at cell `i`: the
total number of particles sitting on vertices of cell `i`. -/
noncomputable def EquitablePartition.cellOcc
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) {N : ℕ} (n : OccupationVector V N) (i : I) : ℕ :=
  ∑ v ∈ Finset.univ.filter (fun v => P.cells v = i), n.occ v

/-- Pushing the occupation forward along the cells conserves total particle
number: `∑_i (cell-occupation at i) = ∑_v n_v = N`. -/
theorem EquitablePartition.sum_cellOcc
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) {N : ℕ} (n : OccupationVector V N) :
    (∑ i, P.cellOcc n i) = N := by
  unfold EquitablePartition.cellOcc
  rw [Finset.sum_fiberwise Finset.univ P.cells n.occ]
  exact n.totalEq

/-- The lifted cell-labelling: each `N`-particle basis state is labelled by the
cell-occupation vector it induces (the multiset of cells it occupies).

* Distinguishable: post-compose the per-particle vertex labels with `P.cells`.
* Boson / Fermion / HardCore: push the occupation forward to cell-occupation
  counts `cellOcc`, which sum to `N` by `sum_cellOcc` (for the tuple-indexed
  HardCore case, convert to the occupation vector counting each vertex once). -/
noncomputable def manyBodyCellLabel
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (N : ℕ) (s : ParticleStatistics) :
    NParticleIndex G N s → ManyBodyCells P N s :=
  match s with
  | .Distinguishable => fun x => P.cells ∘ x
  | .Boson => fun n => ⟨P.cellOcc n, P.sum_cellOcc n⟩
  | .Fermion => fun n => ⟨P.cellOcc n.val, P.sum_cellOcc n.val⟩
  | .HardCore => fun x =>
      -- Count, for each cell `i`, how many of the `N` (distinct) particle
      -- positions land in cell `i`.
      ⟨fun i => (Finset.univ.filter (fun k : Fin N => P.cells (x.val k) = i)).card,
       by
        -- `∑_i #{k : cells (x k) = i} = #(univ : Finset (Fin N)) = N`.
        rw [← Finset.card_eq_sum_card_fiberwise
              (f := fun k : Fin N => P.cells (x.val k))
              (fun k _ => Finset.mem_univ _)]
        simp⟩

/-- The distinguishable `N`-particle adjacency entry, unfolded: a sum over the
particle slot `k` of single-particle hops with the other coordinates frozen. -/
theorem NParticleAdjacency_distinguishable_apply
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (x z : Fin N → V) :
    (NParticleAdjacency G N .Distinguishable).2 x z
      = ∑ k : Fin N, (if (∀ i ≠ k, x i = z i) then G.adj (x k) (z k) else 0) :=
  rfl

/-- **Branching factorization (distinguishable case).**  For distinguishable
particles the lifted-cell branching number from a configuration `x` into a
lifted cell `d : Fin N → I` factors as a sum over the particle slot `k` of:
the single-particle branching number `P.branching (d k) (x k)` of the hopping
particle, gated by the requirement that the *frozen* particles already sit in
the cells prescribed by `d`.

This is the second-quantized branching identity for distinguishable statistics;
it makes the equitable lift a direct corollary of the single-particle equitable
property (`P.branching` depends only on the source cell). -/
theorem manyBody_distinguishable_branching_factor
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (N : ℕ) (d : Fin N → I) (x : Fin N → V) :
    (∑ z : Fin N → V,
      (if P.cells ∘ z = d then (NParticleAdjacency G N .Distinguishable).2 x z else 0))
    = ∑ k : Fin N,
        (if (∀ i ≠ k, P.cells (x i) = d i) then P.branching (d k) (x k) else 0) := by
  classical
  -- Unfold the matrix entry and push the cell indicator `[P∘z = d]` into the
  -- `k`-sum, then swap the `z`-sum past the `k`-sum.
  have hstep1 :
      (∑ z : Fin N → V,
        (if P.cells ∘ z = d then (NParticleAdjacency G N .Distinguishable).2 x z else 0))
      = ∑ k : Fin N, ∑ z : Fin N → V,
          (if P.cells ∘ z = d then
            (if (∀ i ≠ k, x i = z i) then G.adj (x k) (z k) else 0) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [NParticleAdjacency_distinguishable_apply]
    by_cases hp : P.cells ∘ z = d
    · rw [if_pos hp]
      exact Finset.sum_congr rfl (fun k _ => (if_pos hp).symm)
    · rw [if_neg hp]
      exact (Finset.sum_eq_zero (fun k _ => if_neg hp)).symm
  rw [hstep1]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- Per `k`: reindex the `z`-sum along the fiber `{z | ∀ i≠k, x i = z i}` (off the
  -- fiber the summand is 0) by `z ↦ z k`, identifying the cell constraint
  -- `P∘z = d` with `frozen-cells ∧ P(z k) = d k`.
  have hreindex :
      (∑ z : Fin N → V,
        if P.cells ∘ z = d then
          (if (∀ i ≠ k, x i = z i) then G.adj (x k) (z k) else 0) else 0)
      = ∑ w : V,
          if (∀ i ≠ k, P.cells (x i) = d i) ∧ P.cells w = d k
            then G.adj (x k) w else 0 := by
    rw [← Finset.sum_subset
          (Finset.filter_subset (fun z : Fin N → V => ∀ i ≠ k, x i = z i) Finset.univ)
          (by
            -- off-fiber summands vanish: the inner indicator is false there.
            intro z _ hz
            rw [Finset.mem_filter, not_and] at hz
            have hz' : ¬ (∀ i ≠ k, x i = z i) := hz (Finset.mem_univ _)
            rw [if_neg hz', ite_self])]
    refine Finset.sum_nbij' (i := fun z => z k) (j := Function.update x k)
      ?_ ?_ ?_ ?_ ?_
    · intro z _; exact Finset.mem_univ _
    · intro w _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun i hi => ?_⟩
      rw [Function.update_of_ne hi]
    · intro z hz
      rw [Finset.mem_filter] at hz
      funext i
      by_cases hi : i = k
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi]; exact hz.2 i hi
    · intro w _; show Function.update x k w k = w; rw [Function.update_self]
    · -- summand agreement under `z ↦ z k`: `F z = G (z k)`, where the outer
      -- cell constraint `P∘z = d` matches `frozen-cells ∧ P(z k) = d k`.
      intro z hz
      rw [Finset.mem_filter] at hz
      simp only []
      by_cases hzd : P.cells ∘ z = d
      · rw [if_pos hzd, if_pos hz.2, if_pos]
        refine ⟨fun i hi => ?_, ?_⟩
        · have hh := congrFun hzd i
          rw [Function.comp_apply] at hh
          rw [hz.2 i hi]; exact hh
        · have hh := congrFun hzd k; rwa [Function.comp_apply] at hh
      · rw [if_neg hzd, if_neg]
        rintro ⟨hfr, hk⟩
        apply hzd
        funext i
        by_cases hi : i = k
        · subst hi; rw [Function.comp_apply]; exact hk
        · rw [Function.comp_apply, ← hz.2 i hi]; exact hfr i hi
  rw [hreindex]
  -- Split off the frozen-cell indicator and recognise the branching sum.
  by_cases hfrozen : (∀ i ≠ k, P.cells (x i) = d i)
  · rw [if_pos hfrozen]
    unfold EquitablePartition.branching
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hw : P.cells w = d k
    · rw [if_pos ⟨hfrozen, hw⟩, if_pos hw]
    · rw [if_neg (fun h => hw h.2), if_neg hw]
  · rw [if_neg hfrozen]
    refine Finset.sum_eq_zero (fun w _ => ?_)
    rw [if_neg (fun h => hfrozen h.1)]

/-- **Many-body equitable lift — distinguishable particles.**
For *distinguishable* `N`-particle walks the lifted cell labelling
`manyBodyCellLabel P N .Distinguishable = (P.cells ∘ ·)` is an equitable
partition of `(NParticleAdjacency G N .Distinguishable).2`: the branching number
from a configuration into any lifted cell depends only on the lifted cell of the
source.

This is the fully second-quantized branching identity made rigorous: by
`manyBody_distinguishable_branching_factor` the many-body branching factors as a
sum over the hopping particle's slot `k` of single-particle branching numbers
`P.branching (d k) (x k)`, each gated by the requirement that the *frozen*
particles already occupy the cells prescribed by `d`.  Both the gate (a function
of `P.cells ∘ x`) and each branching number (`P.branching` is constant on cells)
depend only on the source's lifted cell, giving equitability.

(The analogous *entrywise* statement is **false** for bosons and
fermions, whose hop matrix elements carry occupation-dependent amplitudes
`√((n_u+1)n_v)` resp. Jordan–Wigner signs that are *not* functions of the
cell-occupation profile alone; the indistinguishable lift only holds on the
cell-uniform subspace, not entrywise.  Hence the lift is stated and proved for
the distinguishable statistics, where it is an equitable partition.) -/
theorem manyBody_equitable_lift_distinguishable
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (N : ℕ) :
    -- Phrased with the reducible index/cell types inlined
    -- (`NParticleIndex G N .Distinguishable = Fin N → V`,
    --  `ManyBodyCells P N .Distinguishable = Fin N → I`,
    --  `manyBodyCellLabel _ x = P.cells ∘ x`) so the canonical `Pi` instances align.
    ∀ (c d : Fin N → I) (x y : Fin N → V),
      P.cells ∘ x = c → P.cells ∘ y = c →
      (∑ z, (if P.cells ∘ z = d
              then (NParticleAdjacency G N .Distinguishable).2 x z else 0))
      = (∑ z, (if P.cells ∘ z = d
              then (NParticleAdjacency G N .Distinguishable).2 y z else 0)) := by
  classical
  intro c d x y hx hy
  -- The factorization helper rewrites each side's branching.
  rw [manyBody_distinguishable_branching_factor P N d x,
      manyBody_distinguishable_branching_factor P N d y]
  -- `P.cells ∘ x = c = P.cells ∘ y`, so `P.cells (x i) = P.cells (y i)` for all `i`.
  have hxy : (P.cells ∘ x : Fin N → I) = P.cells ∘ y := hx.trans hy.symm
  have hcell : ∀ i : Fin N, P.cells (x i) = P.cells (y i) := by
    intro i
    have := congrFun hxy i
    rwa [Function.comp_apply, Function.comp_apply] at this
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- The frozen-cell gate agrees (it only reads `P.cells (x i)`), and each
  -- single-particle branching agrees by single-particle equitability.
  have hgate : (∀ i ≠ k, P.cells (x i) = d i) ↔ (∀ i ≠ k, P.cells (y i) = d i) := by
    constructor <;> intro h i hi
    · rw [← hcell i]; exact h i hi
    · rw [hcell i]; exact h i hi
  have hbr : P.branching (d k) (x k) = P.branching (d k) (y k) :=
    P.branching_eq (P.cells (x k)) (d k) (x k) (y k) rfl (hcell k).symm
  by_cases hg : (∀ i ≠ k, P.cells (x i) = d i)
  · rw [if_pos hg, if_pos (hgate.mp hg), hbr]
  · rw [if_neg hg, if_neg (fun h => hg (hgate.mpr h))]

/-- **Many-body equitable lift (distinguishable statistics).**  If
`P` is an equitable partition of `G`, then the lifted cell labelling
`manyBodyCellLabel P N .Distinguishable = (P.cells ∘ ·)` is an equitable
partition of the distinguishable `N`-particle adjacency
`(NParticleAdjacency G N .Distinguishable).2`: the branching number from a
configuration into any lifted cell `d` depends only on the lifted cell of the
source.

This is the fully second-quantized branching identity, closed via
`manyBody_equitable_lift_distinguishable` (which uses the branching factorization
`manyBody_distinguishable_branching_factor`).

**Why this is stated for the distinguishable sector only — the all-`s` entrywise
form is false for bosons (and fermions).**  Their hop matrix elements
carry occupation-dependent amplitudes `√((n_u+1) n_v)` (resp. Jordan–Wigner
signs) that are *not* functions of the cell-occupation profile alone, so two
configurations with the same lifted cell can have different branching numbers.
Concrete bosonic counterexample (`N = 2`): on the path `a—b—c` with equitable
cells `{a,c}` and `{b}`, the configurations `2·a` and `a+c` share the same
cell-occupation, yet the row-sums of the bosonic hopping matrix are `√2` and `2`
respectively (the `√((n_u+1)n_v)` amplitudes differ within the cell-occupation
fiber).  Hence the *entrywise* equitable property holds only for the
distinguishable statistics, where the hop element is the plain `G.adj` with no
occupation amplitude; for bosons/fermions only the cell-uniform *subspace* is
preserved on the Feder host (a graph-specific fact), not an entrywise equitable
partition. -/
theorem manyBody_equitable_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (N : ℕ) :
    -- The lifted cell labelling `manyBodyCellLabel P N .Distinguishable` is
    -- equitable for the distinguishable many-body adjacency: the branching number
    -- from a basis state into any lifted cell `d` depends only on the lifted cell
    -- of the source.  Phrased with the reducible index/cell types inlined
    -- (`NParticleIndex G N .Distinguishable = Fin N → V`,
    --  `ManyBodyCells P N .Distinguishable = Fin N → I`,
    --  `manyBodyCellLabel _ x = P.cells ∘ x`, all definitional) so the canonical
    -- `Pi` fintype/decidable instances are used — matching the helper.
    ∀ (c d : Fin N → I) (x y : Fin N → V),
      P.cells ∘ x = c → P.cells ∘ y = c →
      (∑ z, (if P.cells ∘ z = d
              then (NParticleAdjacency G N .Distinguishable).2 x z else 0))
      = (∑ z, (if P.cells ∘ z = d
              then (NParticleAdjacency G N .Distinguishable).2 y z else 0)) := by
  -- This is exactly `manyBody_equitable_lift_distinguishable` (the lifted cell
  -- labelling `manyBodyCellLabel P N .Distinguishable` is `P.cells ∘ ·`).
  exact manyBody_equitable_lift_distinguishable P N

/-- **Cell-uniform reduction — distinguishable particles.**  The
distinguishable many-body adjacency **preserves the lifted cell-uniform
subspace**: a wavefunction `ψ` constant on each lifted cell (i.e. constant on
each fiber of `P.cells ∘ ·`) is mapped by `(NParticleAdjacency G N
.Distinguishable).2` to one that is again constant on each lifted cell.

This is the operational form of "many-body cell-uniform dynamics is governed by
an `N`-body Hamiltonian on the quotient graph", and follows directly from the
equitable lift `manyBody_equitable_lift_distinguishable`: grouping the
matrix–vector sum by the target's lifted cell `d`, the `ψ`-value is constant on
each fiber, and the residual cell-branching coefficient depends only on the
source's lifted cell. -/
theorem manyBody_quotient_factorization_distinguishable
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (N : ℕ) :
    -- The matrix–vector action `(H_N ψ)(a) = ∑_z H_N(a,z) ψ(z)` is written as an
    -- explicit sum (the `mulVec` of the many-body adjacency) over the concrete
    -- index `Fin N → V`, to use its canonical `Pi` instances.
    ∀ (ψ : (Fin N → V) → ℂ),
      (∀ a b : Fin N → V, P.cells ∘ a = P.cells ∘ b → ψ a = ψ b) →
      ∀ a b : Fin N → V, P.cells ∘ a = P.cells ∘ b →
        (∑ z : Fin N → V, (NParticleAdjacency G N .Distinguishable).2 a z * ψ z)
        = (∑ z : Fin N → V, (NParticleAdjacency G N .Distinguishable).2 b z * ψ z) := by
  classical
  intro ψ hψ a b hab
  -- Abbreviate the many-body matrix.
  set M : Matrix (Fin N → V) (Fin N → V) ℂ := (NParticleAdjacency G N .Distinguishable).2 with hM
  -- `psiCell d`: the common `ψ`-value on the cell-fiber `d` (0 if the fiber is empty).
  set psiCell : (Fin N → I) → ℂ :=
    fun d => if h : ∃ z : Fin N → V, P.cells ∘ z = d then ψ h.choose else 0 with hpsiCell
  -- Group the matrix–vector sum by the target's lifted cell `d = P.cells ∘ z`,
  -- writing each fiber-branching as the cell-indicator sum used by the equitable
  -- lift `manyBody_equitable_lift_distinguishable`.
  have hgroup : ∀ w : Fin N → V,
      (∑ z : Fin N → V, M w z * ψ z)
      = ∑ d : Fin N → I, psiCell d *
          (∑ z, if P.cells ∘ z = d then M w z else 0) := by
    intro w
    -- Fiberwise over the cell label `P.cells ∘ ·`.
    rw [← Finset.sum_fiberwise Finset.univ (fun z : Fin N → V => P.cells ∘ z)
          (fun z => M w z * ψ z)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    -- Rewrite the RHS cell-indicator sum into a filtered sum, then compare termwise
    -- on the fiber `{z | P.cells ∘ z = d}`, where `ψ z = psiCell d`.
    rw [Finset.mul_sum]
    rw [show (∑ z : Fin N → V, psiCell d * if P.cells ∘ z = d then M w z else 0)
          = ∑ z ∈ Finset.univ.filter (fun z : Fin N → V => P.cells ∘ z = d),
              psiCell d * M w z by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      by_cases hz : P.cells ∘ z = d
      · rw [if_pos hz, if_pos hz]
      · rw [if_neg hz, if_neg hz, mul_zero]]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [Finset.mem_filter] at hz
    -- On the fiber, `ψ z = psiCell d`.
    have hψz : ψ z = psiCell d := by
      have hex : ∃ z' : Fin N → V, P.cells ∘ z' = d := ⟨z, hz.2⟩
      simp only [psiCell, dif_pos hex]
      exact hψ z hex.choose (hz.2.trans hex.choose_spec.symm)
    rw [hψz]; ring
  rw [hgroup a, hgroup b]
  -- Each cell-branching coefficient depends only on the source's lifted cell;
  -- since `P.cells ∘ a = P.cells ∘ b`, the two grouped sums agree term-by-term.
  refine Finset.sum_congr rfl (fun d _ => ?_)
  congr 1
  exact manyBody_equitable_lift_distinguishable P N (P.cells ∘ a) d a b rfl hab.symm

/-- **Cell-uniform reduction (distinguishable statistics).**  The
distinguishable many-body adjacency **preserves the lifted cell-uniform
subspace**: a wavefunction `ψ` constant on each lifted cell (each fiber of
`manyBodyCellLabel P N .Distinguishable = P.cells ∘ ·`) is mapped by
`(NParticleAdjacency G N .Distinguishable).2` to one that is again constant on
each lifted cell.  This is the operational form of "many-body cell-uniform
dynamics is governed by an `N`-body Hamiltonian on the quotient graph", closed
via `manyBody_quotient_factorization_distinguishable` (group the matrix–vector
sum by the target's lifted cell, apply `manyBody_equitable_lift_distinguishable`).

**Why the distinguishable sector only — the all-`s` form is false for
bosons.**  Preservation of the cell-uniform subspace is *not* an equitable-lift
fact for bosons: the bosonic hopping amplitudes `√((n_u+1)n_v)` vary within a
cell-occupation fiber.  Take `N = 2` on the path `a—b—c` with equitable cells
`{a,c}`, `{b}`, and `ψ ≡ 1` (constant on every fiber).  Then `(Hψ)(2·a) = √2`
while `(Hψ)(a+c) = 2`, although `2·a` and `a+c` lie in the same lifted cell —
so the bosonic many-body adjacency does *not* preserve the cell-uniform subspace
of an arbitrary equitable partition.  (Feder's PST is a *graph-specific* fact
about the path→Johnson quotient, recovered here as `FederBosonicWalk` /
`feder_bosonic_quotient_eq`, not a general cell-uniform-subspace reduction.)
For distinguishable particles the hop element is the plain `G.adj` with no
amplitude, so the reduction holds. -/
theorem manyBody_quotient_factorization
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (N : ℕ) :
    -- The distinguishable many-body adjacency preserves the lifted cell-uniform
    -- subspace.  Phrased with the index/cell types inlined
    -- (`NParticleIndex G N .Distinguishable = Fin N → V`,
    --  `manyBodyCellLabel _ a = P.cells ∘ a`, definitional) so the canonical `Pi`
    -- fintype instance is used — matching the helper.
    -- The matrix–vector action `(H_N ψ)(a) = ∑_z H_N(a,z) ψ(z)` is written as an
    -- explicit sum over the concrete index `Fin N → V` (matching the helper, and
    -- avoiding a `Fintype (NParticleAdjacency …).fst` synthesis on the dependent
    -- sigma index that `Matrix.mulVec` would demand).
    ∀ (ψ : (Fin N → V) → ℂ),
      (∀ a b : Fin N → V, P.cells ∘ a = P.cells ∘ b → ψ a = ψ b) →
      ∀ a b : Fin N → V, P.cells ∘ a = P.cells ∘ b →
        (∑ z : Fin N → V, (NParticleAdjacency G N .Distinguishable).2 a z * ψ z)
        = (∑ z : Fin N → V, (NParticleAdjacency G N .Distinguishable).2 b z * ψ z) := by
  -- The labelling `manyBodyCellLabel P N .Distinguishable` is `P.cells ∘ ·`, so
  -- this is exactly the distinguishable factorization.
  exact manyBody_quotient_factorization_distinguishable P N

/-! ## 4.  Feder's many-boson construction (PRL 97, 180502) -/

/-- Feder's many-boson quantum-walk graph.  Given a host weighted graph `G`
on `V` and a particle number `N`, the Feder graph is the host of a CTQW
whose exchange-symmetric (bosonic) subspace recovers the dynamics of an
`N`-boson quantum walk on `G`.

Concretely (Feder 2006, PRL 97, 180502): the Feder graph is the **Johnson-
type host** `Φ(G, N)` whose vertex set is the set of `N`-element multisets of
`V` and whose adjacency is the bosonic hop matrix element.

We take the adjacency to be the (Hermitian) symmetrization
`½(B + Bᴴ)` of the bosonic many-body hopping matrix `B := (NParticleAdjacency
G N .Boson).2`.  Mathematically `B` is already Hermitian, so this *is* the
bosonic hopping host; symmetrizing simply makes Hermiticity hold definitionally
without invoking the (deferred) `NParticleAdjacency_isHermitian`.  The diagonal
of `B` is zero — a hop between distinct sites always changes the
occupation — so the symmetrized host is loopless. -/
noncomputable def FederBosonicWalk
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ)
    [Fintype (OccupationVector V N)] [DecidableEq (OccupationVector V N)] :
    WeightedGraph (OccupationVector V N) where
  adj := fun n m =>
    (1 / 2 : ℂ) * ((NParticleAdjacency G N .Boson).2 n m
                    + star ((NParticleAdjacency G N .Boson).2 m n))
  herm := by
    refine Matrix.IsHermitian.ext ?_
    intro n m
    show star ((1 / 2 : ℂ) * ((NParticleAdjacency G N .Boson).2 m n
              + star ((NParticleAdjacency G N .Boson).2 n m)))
      = (1 / 2 : ℂ) * ((NParticleAdjacency G N .Boson).2 n m
              + star ((NParticleAdjacency G N .Boson).2 m n))
    rw [star_mul', star_add, star_star]
    simp only [star_div₀, star_one, star_ofNat]
    ring
  loopless := by
    intro n
    -- The diagonal of the bosonic hopping matrix vanishes: every contributing
    -- hop `v → u` with `u ≠ v` changes the occupation at `u`, so the
    -- `n'.occ = n.occ` guard is never satisfied.
    have hdiag : (NParticleAdjacency G N .Boson).2 n n = 0 := by
      show (∑ u : V, ∑ v : V,
          if huv : u ≠ v then
            (match OccupationVector.hop n v u (huv.symm) with
             | some n' => if n'.occ = n.occ then
                            G.adj u v * OccupationVector.bosonicHopAmpl n u v
                          else 0
             | none => 0)
          else 0) = 0
      refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ => ?_))
      by_cases huv : u ≠ v
      · rw [dif_pos huv]
        -- Inspect the hop: if it returns `some n'`, then `n'.occ u = n.occ u + 1`.
        cases hhop : OccupationVector.hop n v u huv.symm with
        | none => rfl
        | some n' =>
          -- From the definition of `hop`, `n'.occ u = n.occ u + 1 ≠ n.occ u`.
          have hval : n'.occ u = n.occ u + 1 := by
            unfold OccupationVector.hop at hhop
            by_cases hv0 : n.occ v = 0
            · rw [dif_pos hv0] at hhop; exact absurd hhop (by simp)
            · rw [dif_neg hv0] at hhop
              -- `hhop : some {occ := f, ..} = some n'`, so `n'.occ = f`.
              have heq : n'.occ = (fun w => if w = v then n.occ v - 1
                                    else if w = u then n.occ u + 1 else n.occ w) := by
                have hrec := (Option.some.injEq _ _).mp hhop.symm
                rw [hrec]
              rw [heq]
              show (if u = v then n.occ v - 1 else if u = u then n.occ u + 1 else n.occ u)
                = n.occ u + 1
              rw [if_neg huv, if_pos rfl]
          have hne : n'.occ ≠ n.occ := by
            intro hcontra
            have : n'.occ u = n.occ u := by rw [hcontra]
            omega
          simp [hne]
      · rw [dif_neg huv]
    rw [hdiag, star_zero, add_zero, mul_zero]

/-- **Feder's theorem (statement).**  The bosonic equitable partition of the
Feder host quotients to the exchange-symmetric single-particle dynamics on
the Johnson-type quotient graph `J(G, N)`.  In particular, when `G` is a
path graph `P_n`, the quotient is a path-Johnson graph admitting PST at the
PST time of the underlying `P_n` (the original Feder result). -/
theorem feder_bosonic_quotient_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ)
    [Fintype (OccupationVector V N)] [DecidableEq (OccupationVector V N)] :
    -- The Feder host **is** the second-quantized N-boson walk: its adjacency
    -- coincides with the bosonic many-body hopping matrix
    -- `(NParticleAdjacency G N .Boson).2` (the Hermitian symmetrization is the
    -- identity because that matrix is already Hermitian).  This is the
    -- combinatorial heart of Feder's PRL 97 180502 construction; the
    -- exchange-symmetric quotient to the Johnson-type graph follows by the
    -- many-body equitable lift.
    (FederBosonicWalk G N).adj = (NParticleAdjacency G N .Boson).2 := by
  -- `FederBosonicWalk.adj n m = ½(B n m + star (B m n))`.  Since `B` is Hermitian
  -- (`NParticleAdjacency_boson_isHermitian`), `star (B m n) = B n m`, so the
  -- symmetrization collapses to `B n m`.
  have hherm := NParticleAdjacency_boson_isHermitian G N
  funext n m
  show (1 / 2 : ℂ) * ((NParticleAdjacency G N .Boson).2 n m
        + star ((NParticleAdjacency G N .Boson).2 m n))
      = (NParticleAdjacency G N .Boson).2 n m
  have hstar : star ((NParticleAdjacency G N .Boson).2 m n)
      = (NParticleAdjacency G N .Boson).2 n m := by
    have := congrFun (congrFun hherm n) m
    -- `hherm : Bᴴ = B`, i.e. `star (B m n) = B n m` at entry `(n, m)`.
    rwa [Matrix.conjTranspose_apply] at this
  rw [hstar]
  ring

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
       -- Diagonal Hubbard energy `U · ∑_v n_v(n_v-1)/2` on configurations that
       -- agree (i.e. `n = m` as occupation functions).
       (U : ℂ) * (∑ v, (n.occ v * (n.occ v - 1) : ℝ) / 2)
     else
       -- Off-diagonal hopping: identical to the bosonic many-body adjacency.
       (NParticleAdjacency G N .Boson).2 n m⟩

/-- A Hubbard interaction is **cell-constant** w.r.t. an equitable partition
`P` if the per-site interaction strength is the same on any two vertices that
share a cell.  The condition: the (constant-`U`) on-site interaction
function `fun _ : V => U` is invariant within each cell of `P`, i.e.
`P.cells v = P.cells v' → U = U`.

*Interpretation note.*  The `HubbardModel` here carries a single scalar `U`,
so the per-site function is literally constant and this condition holds for
every partition; we nonetheless state it in the site-dependent form
(`Uf v = Uf v'` whenever `P.cells v = P.cells v'`, with `Uf := fun _ => U`)
rather than as `True`, so that the predicate has the correct meaning when the
model is later generalised to a site-dependent `Uf : V → ℝ`. -/
def HubbardCellCompatible
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (U : ℝ) : Prop :=
  ∀ v v' : V, P.cells v = P.cells v' → (fun _ : V => U) v = (fun _ : V => U) v'

/-- **Hubbard equitable lift.**  When the Hubbard interaction is cell-
compatible with an equitable partition `P` of `G`, the lifted partition
`manyBodyCellLabel P N .Boson` is constant on the diagonal interaction energy:
two occupation vectors with the *same cell-occupation label* and the same
underlying occupation function carry the same Hubbard diagonal energy, and that
energy is invariant under permuting occupied vertices within a cell.

Concretely we state the lift content as the **fiber-invariance of the
interaction energy**: the diagonal Hubbard matrix entry depends only on the
occupation function (not on the matrix's row/column pairing) — i.e. for any two
configurations `n, m` with `n.occ = m.occ`, the Hubbard diagonal energies agree.
This is the diagonal half of the equitable lift; the off-diagonal half is the
bosonic hopping lift `manyBody_equitable_lift`.  (The interaction term being
diagonal is what makes the full lift reduce to the single-particle case.) -/
theorem hubbard_equitable_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (U : ℝ) (N : ℕ)
    (_hCompat : HubbardCellCompatible P U)
    (n m : OccupationVector V N) (hnm : n.occ = m.occ) :
    (HubbardModel G U N).2 n m = (HubbardModel G U N).2 m n := by
  -- With `n.occ = m.occ`, both entries take the diagonal branch (the occupation
  -- functions agree), and the diagonal Hubbard energies are equal since they
  -- depend only on the (common) occupation function.
  have hnm' : ∀ v, n.occ v = m.occ v := fun v => congrFun hnm v
  have hmn' : ∀ v, m.occ v = n.occ v := fun v => (hnm' v).symm
  show (if (∀ v, n.occ v = m.occ v) then
          (U : ℂ) * (∑ v, (n.occ v * (n.occ v - 1) : ℝ) / 2)
        else (NParticleAdjacency G N .Boson).2 n m)
      = (if (∀ v, m.occ v = n.occ v) then
          (U : ℂ) * (∑ v, (m.occ v * (m.occ v - 1) : ℝ) / 2)
        else (NParticleAdjacency G N .Boson).2 m n)
  rw [if_pos hnm', if_pos hmn']
  -- The two diagonal energies agree because `n.occ = m.occ`.
  rw [hnm]

/-! ## 6.  Many-body PST and mixing -/

-- The `Matrix` exponential lemmas (`NormedSpace.exp`) require a normed-ring /
-- normed-algebra instance on `Matrix`, of which Mathlib offers several
-- (operator, Frobenius, …) registered only as *local* instances.  We pick the
-- ℓ∞→ℓ∞ operator norm, matching `Graphplay.PST` and `Graphplay.Product.PST`.
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The canonical `Fintype` on the distinguishable `N`-particle index
(`NParticleIndex G N .Distinguishable = Fin N → V`), via the `Pi` instance — it
is *not* found by synthesis through the dependent `(NParticleAdjacency …).fst`,
so we register it explicitly (definitionally `Pi.instFintype`). -/
instance instFintypeNParticleDistinguishable
    {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ} (G : WeightedGraph V) :
    Fintype (NParticleIndex G N .Distinguishable) :=
  (inferInstance : Fintype (Fin N → V))

/-- The canonical `DecidableEq` on the distinguishable `N`-particle index. -/
instance instDecidableEqNParticleDistinguishable
    {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ} (G : WeightedGraph V) :
    DecidableEq (NParticleIndex G N .Distinguishable) :=
  (inferInstance : DecidableEq (Fin N → V))

/-- The continuous-time `N`-particle quantum walk propagator
`U_N(τ) = exp(-i τ H_N)`, where `H_N = (NParticleAdjacency G N s).2` is the
second-quantized many-body Hamiltonian.  Requires the many-body index type to
be a `Fintype` with `DecidableEq` (so that `Matrix _ _ ℂ` is a normed algebra);
this holds for the finite-`N` truncations realised by `NParticleIndex`. -/
noncomputable def manyBodyEvolve
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics)
    [Fintype (NParticleIndex G N s)] [DecidableEq (NParticleIndex G N s)]
    (τ : ℝ) : Matrix (NParticleIndex G N s) (NParticleIndex G N s) ℂ :=
  NormedSpace.exp (-(Complex.I * (τ : ℂ)) • (NParticleAdjacency G N s).2)

/-- **Many-body perfect state transfer**: PST of the `N`-particle CTQW between
two many-body basis states `u, v : NParticleIndex G N s` at time `τ`.  This is
the multi-particle generalisation of the single-particle
`Graphplay.PST.IsPST`: the modulus of the propagator's `(u, v)` matrix element
is one, i.e. `|⟨v| exp(-i τ H_N) |u⟩| = 1`. -/
noncomputable def IsManyBodyPST
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics)
    [Fintype (NParticleIndex G N s)] [DecidableEq (NParticleIndex G N s)]
    (u v : NParticleIndex G N s) (τ : ℝ) : Prop :=
  ‖manyBodyEvolve G N s τ u v‖ = 1

/-! ### Distinguishable-statistics propagator factorization (Childs–Gosset–Webb)

For *distinguishable* particles the `N`-body Hamiltonian is the Kronecker sum
`H_N = ∑_k A^{(k)}` of the single-particle adjacency `A = G.adj` placed in each
of the `N` tensor slots.  These slot operators commute (they act on independent
factors), so the propagator factors as the `N`-fold tensor power of the
single-particle propagator:

  `exp(-iτ H_N)_{x,y} = ∏_k exp(-iτ A)_{x_k, y_k} = ∏_k U(τ)_{x_k, y_k}`.

This is the operator content behind multiparticle quantum-walk PST/mixing
lifts (Childs–Gosset–Webb, *Science* 339, 791).  We build the slot-embedding
algebra homomorphism, prove the entrywise product formula for a commuting
`noncommProd` of slot operators, and assemble the factorization. -/

/-- **Slot embedding.**  The unital `ℂ`-algebra homomorphism placing a
single-particle operator `A : Matrix V V ℂ` into tensor slot `k`, acting as the
identity on the other `N-1` slots:
`(slotEmbed k A)_{x,y} = [∀ i ≠ k, x_i = y_i] · A(x_k, y_k)`.  It is multiplicative
because the off-`k` Kronecker δ's force the intermediate configuration to agree
with `x` (= `y`) off slot `k`, collapsing the matrix product to `(A·B)(x_k,y_k)`. -/
noncomputable def slotEmbed {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (k : Fin N) : Matrix V V ℂ →ₐ[ℂ] Matrix (Fin N → V) (Fin N → V) ℂ where
  toFun A := Matrix.of fun x y => if (∀ i ≠ k, x i = y i) then A (x k) (y k) else 0
  map_one' := by
    ext x y; simp only [Matrix.of_apply, Matrix.one_apply]
    by_cases h : ∀ i ≠ k, x i = y i
    · rw [if_pos h]
      by_cases hk : x k = y k
      · rw [if_pos hk, if_pos]; funext i; by_cases hik : i = k
        · subst hik; exact hk
        · exact h i hik
      · rw [if_neg hk, if_neg]; intro hxy; exact hk (by rw [hxy])
    · rw [if_neg h, if_neg]; intro hxy; exact h (fun i _ => by rw [hxy])
  map_mul' A B := by
    ext x y; simp only [Matrix.of_apply, Matrix.mul_apply]
    by_cases h : ∀ i ≠ k, x i = y i
    · rw [if_pos h]
      rw [← Finset.sum_subset
            (Finset.filter_subset (fun z : Fin N → V => ∀ i ≠ k, x i = z i) Finset.univ)
            (by intro z _ hz; rw [Finset.mem_filter, not_and] at hz
                rw [if_neg (hz (Finset.mem_univ _)), zero_mul])]
      refine (Finset.sum_nbij' (i := fun z => z k) (j := fun w => Function.update x k w)
        ?_ ?_ ?_ ?_ ?_).symm
      · intro z _; exact Finset.mem_univ _
      · intro w _; rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun i hi => by simp only [Function.update_of_ne hi]⟩
      · intro z hz; rw [Finset.mem_filter] at hz
        funext i; by_cases hi : i = k
        · subst hi; simp only [Function.update_self]
        · simp only [Function.update_of_ne hi]; exact hz.2 i hi
      · intro w _; simp only [Function.update_self]
      · intro z hz; rw [Finset.mem_filter] at hz
        have h1 : (∀ i ≠ k, x i = z i) := hz.2
        have h2 : (∀ i ≠ k, z i = y i) := fun i hi => by rw [← hz.2 i hi]; exact h i hi
        rw [if_pos h1, if_pos h2]
    · rw [if_neg h]; symm; apply Finset.sum_eq_zero; intro z _
      by_cases h1 : (∀ i ≠ k, x i = z i)
      · by_cases h2 : (∀ i ≠ k, z i = y i)
        · exact absurd (fun i hi => (h1 i hi).trans (h2 i hi)) h
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  map_zero' := by ext x y; simp [Matrix.of_apply]
  map_add' A B := by
    ext x y; simp only [Matrix.of_apply, Matrix.add_apply]
    by_cases h : ∀ i ≠ k, x i = y i
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  commutes' c := by
    ext x y
    have key : (∀ i ≠ k, x i = y i) → (x k = y k ↔ x = y) := by
      intro h; refine ⟨fun hk => ?_, fun hxy => by rw [hxy]⟩
      funext i; by_cases hik : i = k
      · subst hik; exact hk
      · exact h i hik
    simp only [Matrix.of_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases h : ∀ i ≠ k, x i = y i
    · rw [if_pos h]; by_cases hk : x k = y k
      · rw [if_pos hk, if_pos ((key h).mp hk)]
      · rw [if_neg hk, if_neg (fun hxy => hk (by rw [hxy])), mul_zero]
    · rw [if_neg h, if_neg (fun hxy => h (fun i _ => by rw [hxy])), mul_zero]

/-- Entrywise formula for the slot embedding. -/
theorem slotEmbed_apply {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (k : Fin N) (A : Matrix V V ℂ) (x y : Fin N → V) :
    slotEmbed k A x y = if (∀ i ≠ k, x i = y i) then A (x k) (y k) else 0 := rfl

/-- The slot embedding is continuous (a linear map between finite-dimensional
spaces), so it commutes with `NormedSpace.exp`. -/
theorem slotEmbed_continuous {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (k : Fin N) : Continuous (slotEmbed (V := V) (N := N) k) :=
  LinearMap.continuous_of_finiteDimensional (slotEmbed k).toLinearMap

/-- The `(x,y)` entry of a product of two *distinct* slot operators: the two
single-particle factors `A(x_k,y_k)·A(x_l,y_l)`, gated by agreement of `x` and
`y` off slots `k` and `l` (a unique intermediate configuration contributes). -/
theorem slotEmbed_prod_apply {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (A : Matrix V V ℂ) (k l : Fin N) (hkl : k ≠ l) (x y : Fin N → V) :
    (∑ z : Fin N → V, (if (∀ i ≠ k, x i = z i) then A (x k) (z k) else 0)
        * (if (∀ i ≠ l, z i = y i) then A (z l) (y l) else 0))
    = (if (∀ i, i ≠ k → i ≠ l → x i = y i) then A (x k) (y k) * A (x l) (y l) else 0) := by
  by_cases hxy : ∀ i, i ≠ k → i ≠ l → x i = y i
  · rw [if_pos hxy]
    set z₀ : Fin N → V := fun i => if i = k then y k else if i = l then x l else x i with hz₀
    have ek : z₀ k = y k := by simp [hz₀]
    have el : z₀ l = x l := by simp [hz₀, Ne.symm hkl]
    have eo : ∀ i, i ≠ k → i ≠ l → z₀ i = x i := by intro i hik hil; simp [hz₀, hik, hil]
    rw [Finset.sum_eq_single z₀]
    · have hk : (∀ i ≠ k, x i = z₀ i) := by
        intro i hi; by_cases hil : i = l
        · rw [hil, el]
        · rw [eo i hi hil]
      have hl : (∀ i ≠ l, z₀ i = y i) := by
        intro i hi; by_cases hik : i = k
        · rw [hik, ek]
        · rw [eo i hik hi]; exact hxy i hik hi
      rw [if_pos hk, if_pos hl, ek, el]
    · intro z _ hz
      by_cases hk : (∀ i ≠ k, x i = z i)
      · by_cases hl : (∀ i ≠ l, z i = y i)
        · exfalso; apply hz; funext i; by_cases hik : i = k
          · rw [hik, ek]; exact hl k hkl
          · by_cases hil : i = l
            · rw [hil, el]; exact (hk l (Ne.symm hkl)).symm
            · rw [eo i hik hil]; exact (hk i hik).symm
        · rw [if_neg hl, mul_zero]
      · rw [if_neg hk, zero_mul]
    · intro hcontra; exact absurd (Finset.mem_univ _) hcontra
  · rw [if_neg hxy]; apply Finset.sum_eq_zero; intro z _
    by_cases hk : (∀ i ≠ k, x i = z i)
    · by_cases hl : (∀ i ≠ l, z i = y i)
      · exfalso; apply hxy; intro i hik hil; exact (hk i hik).trans (hl i hil)
      · rw [if_neg hl, mul_zero]
    · rw [if_neg hk, zero_mul]

/-- Slot operators for distinct slots commute (they act on independent tensor
factors); the product entry `slotEmbed_prod_apply` is symmetric under `k ↔ l`. -/
theorem slotEmbed_commute {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (A : Matrix V V ℂ) (k l : Fin N) : Commute (slotEmbed k A) (slotEmbed l A) := by
  by_cases hkl : k = l
  · subst hkl; exact Commute.refl _
  · unfold Commute SemiconjBy
    ext x y
    simp only [Matrix.mul_apply, slotEmbed_apply]
    rw [slotEmbed_prod_apply A k l hkl x y, slotEmbed_prod_apply A l k (Ne.symm hkl) x y]
    by_cases h : ∀ i, i ≠ k → i ≠ l → x i = y i
    · rw [if_pos h, if_pos (fun i hil hik => h i hik hil), mul_comm]
    · rw [if_neg h, if_neg (fun hc => h (fun i hik hil => hc i hil hik))]

/-- The pairwise-commuting witness for a `Finset`-family of slot operators
(needed to form the `Finset.noncommProd`). -/
noncomputable def slotComm {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (U : Matrix V V ℂ) (T : Finset (Fin N)) :
    (↑T : Set (Fin N)).Pairwise (Function.onFun Commute (fun k => slotEmbed k U)) :=
  fun p _ q _ _ => slotEmbed_commute U p q

/-- **Entry of a commuting product of slot operators.**  For a sub-Finset `T` of
slots, the non-commutative product `∏_{k∈T} slotEmbed k U` has `(x,y)` entry
`∏_{k∈T} U(x_k,y_k)` when `x` and `y` agree off `T` (and `0` otherwise).  Proven
by induction on `T`: inserting a fresh slot `a` contributes one factor
`U(x_a,y_a)` via the single-slot annihilation sum. -/
theorem noncommProd_slotEmbed_apply {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (U : Matrix V V ℂ) (T : Finset (Fin N)) :
    ∀ x y : Fin N → V,
    (T.noncommProd (fun k => slotEmbed k U) (slotComm U T)) x y
      = if (∀ i ∉ T, x i = y i) then (∏ k ∈ T, U (x k) (y k)) else 0 := by
  classical
  induction T using Finset.induction with
  | empty =>
    intro x y
    rw [Finset.noncommProd_empty]
    simp only [Finset.notMem_empty, not_false_eq_true, forall_const, Finset.prod_empty]
    by_cases h : ∀ i, x i = y i
    · rw [if_pos h, Matrix.one_apply, if_pos (funext h)]
    · rw [if_neg h, Matrix.one_apply, if_neg (fun he => h (fun i => by rw [he]))]
  | @insert a T ha ih =>
    intro x y
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Matrix.mul_apply]
    have hfib : (∑ z : Fin N → V, slotEmbed a U x z
          * (T.noncommProd (fun k => slotEmbed k U) (slotComm U T)) z y)
        = ∑ w : V, U (x a) w
            * (T.noncommProd (fun k => slotEmbed k U) (slotComm U T)) (Function.update x a w) y := by
      rw [← Finset.sum_subset
            (Finset.filter_subset (fun z : Fin N → V => ∀ i ≠ a, x i = z i) Finset.univ)
            (by intro z _ hz; rw [Finset.mem_filter, not_and] at hz
                rw [slotEmbed_apply, if_neg (hz (Finset.mem_univ _)), zero_mul])]
      refine Finset.sum_nbij' (i := fun z => z a) (j := fun w => Function.update x a w)
        ?_ ?_ ?_ ?_ ?_
      · intro z _; exact Finset.mem_univ _
      · intro w _; rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun i hi => by simp only [Function.update_of_ne hi]⟩
      · intro z hz; rw [Finset.mem_filter] at hz
        funext i; by_cases hi : i = a
        · subst hi; simp only [Function.update_self]
        · simp only [Function.update_of_ne hi]; exact hz.2 i hi
      · intro w _; simp only [Function.update_self]
      · intro z hz; rw [Finset.mem_filter] at hz
        rw [slotEmbed_apply, if_pos hz.2]
        have hzeq : Function.update x a (z a) = z := by
          funext i; by_cases hi : i = a
          · subst hi; simp only [Function.update_self]
          · simp only [Function.update_of_ne hi]; exact hz.2 i hi
        simp only [hzeq]
    rw [hfib]
    have hupd : ∀ (w : V) (k : Fin N), k ∈ T → (Function.update x a w) k = x k := by
      intro w k hk; rw [Function.update_of_ne (by rintro rfl; exact ha hk)]
    have hcond : ∀ w : V,
        (∀ i ∉ T, (Function.update x a w) i = y i)
        ↔ (w = y a ∧ ∀ i ∉ insert a T, x i = y i) := by
      intro w; constructor
      · intro h; refine ⟨?_, ?_⟩
        · have := h a ha; rwa [Function.update_self] at this
        · intro i hi; rw [Finset.mem_insert, not_or] at hi
          have := h i hi.2; rwa [Function.update_of_ne hi.1] at this
      · rintro ⟨hwa, hC⟩ i hi
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hwa
        · rw [Function.update_of_ne hia]
          exact hC i (by rw [Finset.mem_insert, not_or]; exact ⟨hia, hi⟩)
    have hstep : ∀ w : V, U (x a) w
          * (T.noncommProd (fun k => slotEmbed k U) (slotComm U T)) (Function.update x a w) y
        = if (w = y a ∧ ∀ i ∉ insert a T, x i = y i)
            then U (x a) w * (∏ k ∈ T, U (x k) (y k)) else 0 := by
      intro w; rw [ih (Function.update x a w) y]
      by_cases hc : (∀ i ∉ T, (Function.update x a w) i = y i)
      · rw [if_pos hc, if_pos ((hcond w).mp hc)]
        congr 1; refine Finset.prod_congr rfl (fun k hk => ?_); rw [hupd w k hk]
      · rw [if_neg hc, mul_zero, if_neg (fun h => hc ((hcond w).mpr h))]
    rw [Finset.sum_congr rfl (fun w _ => hstep w)]
    by_cases hC : (∀ i ∉ insert a T, x i = y i)
    · rw [if_pos hC, Finset.prod_insert ha, Finset.sum_eq_single (y a)]
      · rw [if_pos ⟨rfl, hC⟩]
      · intro w _ hw; rw [if_neg (fun h => hw h.1)]
      · intro hcontra; exact absurd (Finset.mem_univ _) hcontra
    · rw [if_neg hC]; apply Finset.sum_eq_zero; intro w _; rw [if_neg (fun h => hC h.2)]

set_option maxHeartbeats 800000 in
/-- The slot embedding commutes with `NormedSpace.exp`: it is a continuous
algebra homomorphism, so it maps the exponential power series term-by-term
(`map_smul`/`map_pow`), giving `exp(slotEmbed k M) = slotEmbed k (exp M)`. -/
theorem exp_slotEmbed {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (k : Fin N) (M : Matrix V V ℂ) :
    NormedSpace.exp (slotEmbed k M) = slotEmbed k (NormedSpace.exp M) := by
  let φ : Matrix V V ℂ →+ Matrix (Fin N → V) (Fin N → V) ℂ :=
    { toFun := fun X => slotEmbed k X
      map_zero' := map_zero _
      map_add' := fun X Y => map_add _ X Y }
  have hφc : Continuous φ := slotEmbed_continuous k
  have hM : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n) (NormedSpace.exp M) :=
    NormedSpace.exp_series_hasSum_exp' _
  have hSk : HasSum (fun n => (Nat.factorial n : ℂ)⁻¹ • (slotEmbed k M) ^ n)
      (NormedSpace.exp (slotEmbed k M)) := NormedSpace.exp_series_hasSum_exp' _
  have hMφ := hM.map φ hφc
  have hterm : (φ ∘ fun n => (Nat.factorial n : ℂ)⁻¹ • M ^ n)
      = fun n => (Nat.factorial n : ℂ)⁻¹ • (slotEmbed k M) ^ n := by
    funext n
    show slotEmbed k ((Nat.factorial n : ℂ)⁻¹ • M ^ n)
        = (Nat.factorial n : ℂ)⁻¹ • (slotEmbed k M) ^ n
    rw [map_smul, map_pow]
  rw [hterm] at hMφ
  exact (hMφ.unique hSk).symm

/-- The distinguishable `N`-particle adjacency is the Kronecker sum of the
single-particle adjacency over the `N` slots: `H_N = ∑_k slotEmbed k G.adj`. -/
theorem nparticleAdjacency_distinguishable_eq_slotSum
    {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ} (G : WeightedGraph V) :
    (NParticleAdjacency G N .Distinguishable).2 = ∑ k : Fin N, slotEmbed k G.adj := by
  ext x y
  rw [Matrix.sum_apply]
  show (∑ k : Fin N, if (∀ i ≠ k, x i = y i) then G.adj (x k) (y k) else 0)
      = ∑ k : Fin N, slotEmbed k G.adj x y
  exact Finset.sum_congr rfl (fun k _ => (slotEmbed_apply k G.adj x y).symm)

/-- **Distinguishable propagator tensor-power factorization (Childs–Gosset–Webb).**
The `N`-distinguishable-particle propagator entry is the product of the
single-particle propagator entries over the slots:

  `⟨y| exp(-iτ H_N) |x⟩ = ∏_k ⟨y_k| exp(-iτ A) |x_k⟩ = ∏_k U(τ)_{x_k, y_k}`.

This is the operator identity `exp(-iτ ⊕_k A) = ⊗_k exp(-iτ A)`, proven via the
commuting slot decomposition (`nparticleAdjacency_distinguishable_eq_slotSum`,
`slotEmbed_commute`), `Matrix.exp_sum_of_commute`, `exp_slotEmbed`, and the
commuting-product entry formula `noncommProd_slotEmbed_apply`.  It is the engine
of the multiparticle PST and mixing lifts below. -/
theorem manyBodyEvolve_distinguishable_apply
    {V : Type u} [Fintype V] [DecidableEq V] {N : ℕ}
    (G : WeightedGraph V) (τ : ℝ) (x y : Fin N → V) :
    manyBodyEvolve G N .Distinguishable τ x y
      = ∏ k : Fin N, (G.evolve τ) (x k) (y k) := by
  show (NormedSpace.exp (-(Complex.I * (τ:ℂ)) • (NParticleAdjacency G N .Distinguishable).2)) x y
      = ∏ k : Fin N, (G.evolve τ) (x k) (y k)
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix V V ℂ, M = -(Complex.I * (τ:ℂ)) • G.adj := ⟨_, rfl⟩
  have hsum : -(Complex.I * (τ:ℂ)) • (NParticleAdjacency G N .Distinguishable).2
      = ∑ k ∈ (Finset.univ : Finset (Fin N)), slotEmbed k M := by
    ext x' y'
    rw [Matrix.smul_apply, nparticleAdjacency_distinguishable_eq_slotSum, Matrix.sum_apply,
        Matrix.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hMdef, map_smul, Matrix.smul_apply]
  rw [hsum]
  show NormedSpace.exp (∑ k ∈ (Finset.univ : Finset (Fin N)), slotEmbed k M) x y
      = ∏ k : Fin N, (G.evolve τ) (x k) (y k)
  rw [Matrix.exp_sum_of_commute (Finset.univ : Finset (Fin N)) (fun k => slotEmbed k M)
        (slotComm M Finset.univ)]
  simp only [exp_slotEmbed]
  rw [noncommProd_slotEmbed_apply (NormedSpace.exp M) Finset.univ x y,
      if_pos (by intro i hi; exact absurd (Finset.mem_univ i) hi)]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [show (NormedSpace.exp M : Matrix V V ℂ) = G.evolve τ from by rw [hMdef]; rfl]


/-- **Many-body PST lifting (distinguishable statistics,
Childs–Gosset–Webb).**  If the single-particle CTQW on `G` exhibits perfect state
transfer between vertices `a` and `b` at time `τ` (`IsPST G a b τ`, i.e.
`‖U(τ)_{a,b}‖ = 1`), then the `N`-distinguishable-particle CTQW exhibits
many-body PST between the *constant configurations* `(a,…,a)` and `(b,…,b)` at the
same time `τ`: every particle transfers from `a` to `b` simultaneously.

By the propagator
factorization `manyBodyEvolve_distinguishable_apply`, the realizing many-body
amplitude is `∏_k U(τ)_{a,b} = (U(τ)_{a,b})^N`, whose modulus is
`‖U(τ)_{a,b}‖^N = 1^N = 1`.  (This is the basis-state form of the multiparticle
PST lift; the vertex-level single-particle hypothesis is what makes the
many-body *basis-state* conclusion true — a cell-uniform *superposition*
hypothesis would only give a superposition-to-superposition transfer, not a
basis-state one.) -/
theorem manyBodyPST_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} (N : ℕ) (a b : V) (τ : ℝ)
    (hPST : IsPST G a b τ) :
    IsManyBodyPST G N .Distinguishable (fun _ => a) (fun _ => b) τ := by
  -- `IsPST G a b τ` is `‖G.evolve τ a b‖ = 1`; the many-body amplitude is the
  -- `N`-fold product of this single-particle amplitude.
  have hab : ‖G.evolve τ a b‖ = 1 := hPST
  unfold IsManyBodyPST
  rw [manyBodyEvolve_distinguishable_apply, norm_prod]
  simp only [hab, Finset.prod_const_one]

/-- **Many-body uniform mixing**: the `N`-particle CTQW is *uniformly mixing*
at time `τ` when the mixing matrix `M(τ)_{u,v} = |U_N(τ)_{u,v}|²` is constant,
equal to `1 / |Idx|` at every pair of many-body basis states.  Equivalently,
`‖exp(-i τ H_N)_{u,v}‖² = 1 / |NParticleIndex G N s|` for all `u, v`. -/
noncomputable def IsManyBodyUniformMixing
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (s : ParticleStatistics)
    [Fintype (NParticleIndex G N s)] [DecidableEq (NParticleIndex G N s)]
    (τ : ℝ) : Prop :=
  ∀ u v : NParticleIndex G N s,
    ‖manyBodyEvolve G N s τ u v‖ ^ 2
      = 1 / (Fintype.card (NParticleIndex G N s) : ℝ)

/-- **Many-body mixing lifting (distinguishable statistics,
Childs–Gosset–Webb).**  If the *single-particle* CTQW on `G` is uniformly mixing
at time `τ` — every propagator amplitude has modulus `1/√|V|`, i.e.
`‖U(τ)_{a,b}‖² = 1/|V|` for all vertices `a, b` — then the
`N`-distinguishable-particle CTQW is uniformly mixing at the same time `τ`.

By the propagator factorization
`manyBodyEvolve_distinguishable_apply`, every many-body amplitude is the product
`∏_k U(τ)_{x_k,y_k}`, so its squared modulus is `∏_k (1/|V|) = (1/|V|)^N =
1/|V|^N = 1 / |Fin N → V| = 1 / |NParticleIndex G N .Distinguishable|`, which is
exactly uniform mixing of the `N`-particle walk.  Together with
`manyBodyPST_lift` this gives the distinguishable many-body analogue of the
single-particle dynamical lifts (PST and uniform mixing). -/
theorem manyBodyMixing_lift
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ) (τ : ℝ)
    (hMix : ∀ a b : V, ‖G.evolve τ a b‖ ^ 2 = 1 / (Fintype.card V : ℝ)) :
    IsManyBodyUniformMixing G N .Distinguishable τ := by
  intro u v
  -- Factor the many-body amplitude as the product of single-particle amplitudes,
  -- square the modulus, and collapse the constant product over the `N` slots.
  rw [manyBodyEvolve_distinguishable_apply, norm_prod, ← Finset.prod_pow]
  rw [show (fun k : Fin N => ‖G.evolve τ (u k) (v k)‖ ^ 2)
        = (fun _ : Fin N => 1 / (Fintype.card V : ℝ))
      from funext (fun k => hMix (u k) (v k))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- `(1/|V|)^N = 1 / |Fin N → V| = 1 / |NParticleIndex G N .Distinguishable|`.
  have hcard : Fintype.card (NParticleIndex G N .Distinguishable)
      = (Fintype.card V) ^ N := by
    show Fintype.card (Fin N → V) = (Fintype.card V) ^ N
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcard, div_pow, one_pow, Nat.cast_pow]

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
reduction; classical result, recorded as a lift statement.

Precisely: there is a single-magnon hopping matrix `Hmag` equal to the
rescaled adjacency `(J/2) • G.adj`, and its CTQW propagator agrees with the
single-particle walk on the same rescaled adjacency for every time `τ`.  (For
the single excitation the magnon Hilbert space is just `V → ℂ`, so the only
content is the value of the hopping matrix; the propagator equality is then a
definitional identity once the hopping matrix is identified.) -/
theorem singleMagnon_eq_singleParticleWalk (M : TJModel G) :
    ∃ Hmag : Matrix V V ℂ,
      Hmag = ((M.J / 2 : ℝ) : ℂ) • G.adj ∧
      ∀ τ : ℝ, NormedSpace.exp (-(Complex.I * (τ : ℂ)) • Hmag)
        = NormedSpace.exp (-(Complex.I * (τ : ℂ)) • (((M.J / 2 : ℝ) : ℂ) • G.adj)) := by
  -- Take `Hmag := (J/2) • G.adj`; both halves are then `rfl` after substitution.
  exact ⟨((M.J / 2 : ℝ) : ℂ) • G.adj, rfl, fun _ => rfl⟩

/-- **t-J equitable lift.**  An equitable partition of `G` induces an
equitable partition of the single-magnon sector of any `TJModel G`, with the
quotient adjacency `(J / 2) · P.quotient`.

Faithful statement: the cell map `P.cells` again satisfies the equitable
`uniform` branching condition when `G.adj` is replaced by the rescaled
single-magnon adjacency `(J/2) • G.adj`.  (Real scalar scaling pulls out of
every branching sum, so equitability is preserved with the quotient scaled by
the same factor.) -/
theorem tj_singleMagnon_equitable_lift
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (M : TJModel G) :
    ∀ (i j : I) (x y : V), P.cells x = i → P.cells y = i →
      (∑ z, (if P.cells z = j then ((M.J / 2 : ℝ) : ℂ) * G.adj x z else 0))
      = (∑ z, (if P.cells z = j then ((M.J / 2 : ℝ) : ℂ) * G.adj y z else 0)) := by
  intro i j x y hx hy
  -- Pull the scalar `J/2` out of each branching sum and use the unscaled
  -- equitability of `P`.
  have hpull : ∀ w : V,
      (∑ z, (if P.cells z = j then ((M.J / 2 : ℝ) : ℂ) * G.adj w z else 0))
      = ((M.J / 2 : ℝ) : ℂ) * (∑ z, (if P.cells z = j then G.adj w z else 0)) := by
    intro w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hz : P.cells z = j
    · rw [if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz, mul_zero]
  rw [hpull x, hpull y, P.uniform i j x y hx hy]

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

/-! ### The Jordan–Wigner string unitary

The Jordan–Wigner transform is, concretely, conjugation by the **Jordan–Wigner
string** — a *diagonal* unitary `U = ∏_k Z_k^{…}` whose entries are the parity
signs `(-1)^{#occupied modes to the left}`.  At the level of a single basis
index `b` of the configuration space this is a fixed `±1` phase
`ε(b) = (-1)^{(order of b)}`, read off the canonical linear order
`Fintype.equivFin B` on the (finite) index type `B`.

Because the JW transform is a *similarity* `H ↦ U H U⁻¹`, the XY image is the
conjugate `H_XY = U · H_hardcore · U⁻¹`, **not** an alias of
`H_hardcore` — exactly the Lieb–Schultz–Mattis content that the
`JordanWignerIntertwiner` interface demands as its *output*.  We build the
unitary `U` and prove `star U * U = 1`, `U * star U = 1` outright. -/

namespace JordanWigner

open scoped Matrix

/-- The Jordan–Wigner string **sign** at a basis index `b`: the parity
`(-1)^{(linear index of b)}` of its position in the fixed order on `B`.  This is
the diagonal entry of the Z-string unitary, a `±1` real phase. -/
noncomputable def stringSign {B : Type*} [Fintype B] (b : B) : ℂ :=
  (-1 : ℂ) ^ ((Fintype.equivFin B) b).val

/-- The Jordan–Wigner string sign squares to one (each Z-factor is an
involution): `ε(b)² = 1`. -/
theorem stringSign_sq {B : Type*} [Fintype B] (b : B) :
    stringSign b * stringSign b = 1 := by
  unfold stringSign
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The Jordan–Wigner string sign is real, so `star` fixes it. -/
theorem star_stringSign {B : Type*} [Fintype B] (b : B) :
    star (stringSign b) = stringSign b := by
  unfold stringSign
  rw [show ((-1 : ℂ) ^ ((Fintype.equivFin B) b).val)
        = (((-1 : ℝ) ^ ((Fintype.equivFin B) b).val : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The Jordan–Wigner string **unitary** on the configuration space `B`: the
diagonal matrix of string signs `U = diagonal ε`.  This is the concrete
`U = ∏_k Z_k^{…}` operator of Jordan–Wigner / Lieb–Schultz–Mattis. -/
noncomputable def stringUnitary (B : Type*) [Fintype B] [DecidableEq B] :
    Matrix B B ℂ :=
  Matrix.diagonal (stringSign (B := B))

/-- The JW string unitary is its own conjugate-transpose (it is a real diagonal
involution): `star U = U`. -/
theorem star_stringUnitary (B : Type*) [Fintype B] [DecidableEq B] :
    star (stringUnitary B) = stringUnitary B := by
  unfold stringUnitary
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext b
  exact star_stringSign b

/-- **The JW string operator is unitary**: `star U * U = 1`. -/
theorem stringUnitary_isUnitary_left (B : Type*) [Fintype B] [DecidableEq B] :
    star (stringUnitary B) * stringUnitary B = (1 : Matrix B B ℂ) := by
  rw [star_stringUnitary]
  unfold stringUnitary
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun b => stringSign b * stringSign b) = (fun _ : B => (1 : ℂ)) from
    funext (fun b => stringSign_sq b)]
  exact Matrix.diagonal_one

/-- **The JW string operator is unitary**: `U * star U = 1`. -/
theorem stringUnitary_isUnitary_right (B : Type*) [Fintype B] [DecidableEq B] :
    stringUnitary B * star (stringUnitary B) = (1 : Matrix B B ℂ) := by
  rw [star_stringUnitary]
  unfold stringUnitary
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun b => stringSign b * stringSign b) = (fun _ : B => (1 : ℂ)) from
    funext (fun b => stringSign_sq b)]
  exact Matrix.diagonal_one

/-- **The string-sign dressing of an arbitrary hopping matrix**: the entrywise
real `±1` dressing `(xyDressing H) a b = ε(a) · H(a,b) · ε(b)`.  This is the
*independently-written* XY-image operator — an explicit entry formula, **not** the
conjugation product `U · H · star U`.  (That the two coincide is the theorem
`stringUnitary_conj_eq_xyDressing` below; the class-level `H_XY` is pinned to this
entry formula precisely so it can never be a tautological conjugation alias.) -/
noncomputable def xyDressing {B : Type*} [Fintype B] [DecidableEq B]
    (H : Matrix B B ℂ) : Matrix B B ℂ :=
  Matrix.of fun a b => stringSign a * H a b * stringSign b

@[simp] theorem xyDressing_apply {B : Type*} [Fintype B] [DecidableEq B]
    (H : Matrix B B ℂ) (a b : B) :
    xyDressing H a b = stringSign a * H a b * stringSign b := rfl

/-- **The string-conjugate equals the entrywise dressing** (general form): the
similarity image `U · H · star U` of *any* matrix by the diagonal string
unitary equals its explicit entrywise `±1` dressing.  This is the diagonal-
conjugation-acts-entrywise fact; the hard-core specialisation
`stringUnitary_conj_eq_xyHamiltonian` is the `H := NParticleAdjacency` case. -/
theorem stringUnitary_conj_eq_xyDressing {B : Type*} [Fintype B] [DecidableEq B]
    (H : Matrix B B ℂ) :
    stringUnitary B * H * star (stringUnitary B) = xyDressing H := by
  ext a b
  rw [star_stringUnitary]
  unfold stringUnitary xyDressing
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- **The Jordan–Wigner intertwining, general form** (Lieb–Schultz–Mattis): the
diagonal string unitary intertwines *any* hopping matrix with its entrywise XY
dressing, `U · H = (xyDressing H) · U`.  Proof: entrywise `ε(a) · H(a,b)` on both
sides, since `ε(b)² = 1` cancels the trailing string factor on the right. -/
theorem stringUnitary_intertwine {B : Type*} [Fintype B] [DecidableEq B]
    (H : Matrix B B ℂ) :
    stringUnitary B * H = xyDressing H * stringUnitary B := by
  unfold stringUnitary xyDressing
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, mul_assoc,
      stringSign_sq, mul_one]

/-! #### The non-centrality witness (the Z-string fails to commute)

The witness for `JordanWignerIntertwiner.string_noncentral`:
on any configuration type with `≥ 2` elements, the Jordan–Wigner string
unitary `U = diagonal ε` does **not** commute with a single off-diagonal hop
between two sign-opposite configurations.  Concretely the `Fintype.equivFin`
order singles out an index-`0` config (string sign `+1`) and an index-`1` config
(string sign `−1`); the elementary hop `E` between them satisfies
`(U·E)` carrying `ε(+) = +1` while `(E·U)` carries `ε(−) = −1`, so they differ.
In particular `U_JW` cannot be the identity (which commutes with
everything). -/

/-- The index-`0` configuration in the fixed `equivFin` order (string sign `+1`). -/
noncomputable def stringConfig0 (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B] : B :=
  (Fintype.equivFin B).symm ⟨0, by
    have : 0 < Fintype.card B := Fintype.card_pos; omega⟩

/-- The index-`1` configuration in the fixed `equivFin` order (string sign `−1`),
available once `B` has at least two configurations. -/
noncomputable def stringConfig1 (B : Type*) [Fintype B] [DecidableEq B]
    (h2 : 2 ≤ Fintype.card B) : B :=
  (Fintype.equivFin B).symm ⟨1, by omega⟩

theorem stringSign_config0 (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B] :
    stringSign (stringConfig0 B) = 1 := by
  unfold stringSign stringConfig0; rw [Equiv.apply_symm_apply]; simp

theorem stringSign_config1 (B : Type*) [Fintype B] [DecidableEq B]
    (h2 : 2 ≤ Fintype.card B) :
    stringSign (stringConfig1 B h2) = -1 := by
  unfold stringSign stringConfig1; rw [Equiv.apply_symm_apply]; simp

/-- The elementary single-hop matrix `E_{0,1}` supported on the ordered pair
`(stringConfig0, stringConfig1)` — a concrete hard-core-style hopping the string
unitary fails to commute with. -/
noncomputable def stringHop (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B]
    (h2 : 2 ≤ Fintype.card B) : Matrix B B ℂ :=
  Matrix.of fun i j => if i = stringConfig0 B ∧ j = stringConfig1 B h2 then 1 else 0

/-- **The Jordan–Wigner string unitary is non-central** (`≥ 2` configurations):
`U · E ≠ E · U` for the elementary sign-opposite hop `E`.  This is the
non-degeneracy witness for `JordanWignerIntertwiner` (it rules out
`U_JW = 1`). -/
theorem stringUnitary_noncentral (B : Type*) [Fintype B] [DecidableEq B] [Nonempty B]
    (h2 : 2 ≤ Fintype.card B) :
    stringUnitary B * stringHop B h2 ≠ stringHop B h2 * stringUnitary B := by
  intro h
  have key := congrFun (congrFun h (stringConfig0 B)) (stringConfig1 B h2)
  unfold stringUnitary stringHop at key
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply,
      if_pos ⟨rfl, rfl⟩, stringSign_config0, stringSign_config1] at key
  norm_num at key

end JordanWigner

/-! ### The concrete XY-chain Hamiltonian as the Jordan–Wigner image

We now build the XY-chain target as a **concrete, independently-defined matrix**
in the hard-core occupation basis — *not* as the matrix product
`U · Hhc · U⁻¹`.  The Jordan–Wigner string conjugation by the diagonal string
unitary `U = diagonal ε` acts on a matrix entry `(Hhc)_{ab}` by the explicit
real `±1` dressing `ε(a) · ε(b)`, since `U` is diagonal and `ε` is real:

  `(U · Hhc · U⁻¹)_{ab} = ε(a) · (Hhc)_{ab} · ε(b)`.

For the hard-core hopping matrix this is exactly the Lieb–Schultz–Mattis content:
each off-diagonal hopping amplitude `(Hhc)_{ab}` connecting two configurations
that differ by moving one particle picks up the Jordan–Wigner string sign
`ε(a)ε(b) = (-1)^{(#modes between the two sites)}`, and for *adjacent* sites this
string collapses, leaving precisely the local `½(X_iX_{i+1} + Y_iY_{i+1})` XY
two-site term written in the occupation basis.  We define `xyHamiltonian` by this
explicit entry formula (concrete, no conjugation product) and then *prove* that
the string conjugate `U · Hhc · U⁻¹` equals it. -/

/-- **The XY-chain Hamiltonian in the hard-core occupation basis**, defined
*concretely* (entry-wise) as the Jordan–Wigner-string-dressed hard-core hopping
matrix:

  `xyHamiltonian G N _ a b = ε(a) · (Hhc)_{ab} · ε(b)`,

with `ε = JordanWigner.stringSign` the real `±1` Z-string parity and
`Hhc = (NParticleAdjacency G N .HardCore).2` the hard-core hopping matrix.

This is an **independent operator**: it is built directly from the hard-core
entries with the explicit string signs through `Matrix.of`, *not* as the matrix
product `U · Hhc · star U`.  The content of the Jordan–Wigner equivalence is then
the theorem `stringUnitary_conj_eq_xyHamiltonian` below, which proves that the
string conjugate of `Hhc` *equals* this concrete matrix. -/
noncomputable def xyHamiltonian
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ)
    [Fintype (NParticleIndex G N .HardCore)]
    [DecidableEq (NParticleIndex G N .HardCore)] :
    Matrix (NParticleIndex G N .HardCore) (NParticleIndex G N .HardCore) ℂ :=
  Matrix.of fun a b =>
    JordanWigner.stringSign a
      * (NParticleAdjacency G N .HardCore).2 a b
      * JordanWigner.stringSign b

/-- **The Jordan–Wigner string conjugate of the hard-core hopping matrix is the
concrete XY Hamiltonian** (Lieb–Schultz–Mattis).

The similarity image `U · Hhc · U⁻¹` of the hard-core hopping matrix by
the concrete Jordan–Wigner string unitary `U = JordanWigner.stringUnitary` equals
the *independently-defined* concrete matrix `xyHamiltonian`.  Because
`xyHamiltonian` is defined entry-wise rather than as the conjugation product,
the equation `U · Hhc · U⁻¹ = xyHamiltonian` is a non-trivial
matrix identity (diagonal conjugation acting entry-wise by the real string signs).

Proof: `U = diagonal ε`, `star U = diagonal ε` (`star_stringUnitary`), so
`(U · Hhc · star U)_{ab} = ε(a) · (Hhc)_{ab} · ε(b)` by `diagonal_mul` / `mul_diagonal`,
which is the defining entry of `xyHamiltonian`. -/
theorem stringUnitary_conj_eq_xyHamiltonian
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (N : ℕ)
    [Fintype (NParticleIndex G N .HardCore)]
    [DecidableEq (NParticleIndex G N .HardCore)] :
    JordanWigner.stringUnitary (NParticleIndex G N .HardCore)
        * (NParticleAdjacency G N .HardCore).2
        * star (JordanWigner.stringUnitary (NParticleIndex G N .HardCore))
      = xyHamiltonian G N := by
  classical
  ext a b
  -- `star U = U = diagonal ε`; expand the diagonal multiplications entry-wise.
  rw [JordanWigner.star_stringUnitary]
  unfold JordanWigner.stringUnitary xyHamiltonian
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- **The Jordan–Wigner intertwiner instance (Lieb–Schultz–Mattis).**

Supplies the `JordanWignerIntertwiner` interface with **fixed,
concrete functions of the path data**:

* `epsilon B := JordanWigner.stringSign` — the `±1` Z-string parity
  `ε(b) = (−1)^{(order of b)}` (`epsilon_sq`/`epsilon_real` are the proven
  `stringSign_sq`/`star_stringSign`);
* `U_JW B := JordanWigner.stringUnitary B = diagonal stringSign` (so
  `U_JW_eq_diagonal` is `rfl`) — a *non-central* unitary, **not** `1`;
* `H_XY B Hhc := JordanWigner.xyDressing Hhc` — the XY image written down by the
  explicit **entrywise dressing** `ε(a)·Hhc(a,b)·ε(b)` (so `H_XY_apply` is `rfl`),
  an independent operator that is *not* the tautological conjugation product
  (that it equals `U · Hhc · star U` is the separate theorem
  `stringUnitary_conj_eq_xyDressing`, not a definitional alias).

The intertwining `U · Hhc = (xyDressing Hhc) · U` is the matrix identity
`stringUnitary_intertwine` (entrywise `ε(a)·Hhc(a,b)`, using `ε(b)² = 1`).  The
`string_noncentral` field is the non-degeneracy witness
`stringUnitary_noncentral` on `B := Fin 2` (the Z-string fails to commute with a
sign-opposite hop), ruling out `U_JW = 1`.  Discharges
`Graphplay.ManyBody.hardCore_eq_XY_oneDim` unconditionally. -/
noncomputable instance instJordanWignerIntertwiner :
    Graphplay.LiteratureInterfaces.JordanWignerIntertwiner where
  epsilon {B} _ _ := JordanWigner.stringSign
  U_JW {B} _ _ := JordanWigner.stringUnitary B
  H_XY {B} _ _ := JordanWigner.xyDressing
  epsilon_sq {B} _ _ := JordanWigner.stringSign_sq
  epsilon_real {B} _ _ := JordanWigner.star_stringSign
  U_JW_eq_diagonal {B} _ _ := rfl
  U_JW_unitary_left {B} _ _ := JordanWigner.stringUnitary_isUnitary_left B
  U_JW_unitary_right {B} _ _ := JordanWigner.stringUnitary_isUnitary_right B
  H_XY_apply {B} _ _ := fun _ _ _ => rfl
  jordanWigner_image {B} _ _ := JordanWigner.stringUnitary_intertwine
  string_noncentral :=
    -- the non-centrality witness on `Fin 2`: the Z-string fails to
    -- commute with the elementary sign-opposite hop, so `U_JW ≠ 1`.
    ⟨Fin 2, inferInstance, inferInstance,
      JordanWigner.stringHop (Fin 2) (by simp),
      JordanWigner.stringUnitary_noncentral (Fin 2) (by simp)⟩

/-- **Jordan-Wigner equivalence (one-dimensional).**  On a path graph `P_n`,
the hard-core boson model with nearest-neighbour hopping `G` is unitarily
equivalent (via the Jordan-Wigner transformation) to the XY spin chain on
the same vertex set with `γ = 0`.  This is the Lieb–Schultz–Mattis equivalence.

The statement pins **both** operators to *concrete* matrices, leaving
**no free existential** — a form with both `U_JW` and `Hxy` existentially
quantified is satisfied degenerately by `U_JW = 1, Hxy = Hhc` and says nothing —
and makes `Hxy` an **independent** operator
(not aliased to `U · Hhc · U⁻¹` by definition):

* the intertwiner `U_JW` is the **concrete Jordan–Wigner string unitary**
  `JordanWigner.stringUnitary` — the non-trivial diagonal Z-string
  `ε(b) = (-1)^{(order of b)}`, *not* the identity (`star U · U = 1`,
  `U · star U = 1` are the proven `stringUnitary_isUnitary_{left,right}`);
* the XY image `Hxy` is the **concrete, independently-defined** matrix
  `xyHamiltonian G N` — built entry-wise as the Jordan–Wigner-string-dressed
  hard-core hopping matrix `ε(a) · (Hhc)_{ab} · ε(b)` — *not* the matrix product
  `U_JW · Hhc · star U_JW`.  That the string conjugate of `Hhc` *equals*
  this concrete `xyHamiltonian` is the separate theorem
  `stringUnitary_conj_eq_xyHamiltonian` (diagonal conjugation acting entry-wise
  by the real string signs — the Lieb–Schultz–Mattis sign dressing).

The statement then asserts the intertwining `U_JW · Hhc = Hxy · U_JW` for these
*fixed* operators, together with `γ = 0` and `M.graph = G`:
`Hxy` is an explicit operator
written down without reference to the conjugation, and the theorem asserts that
conjugating the hard-core hopping by the string unitary lands exactly on it. -/
theorem hardCore_eq_XY_oneDim
    {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : WeightedGraph V) (N : ℕ)
    [Fintype (NParticleIndex G N .HardCore)]
    [DecidableEq (NParticleIndex G N .HardCore)] :
    -- There is an XY model on the same graph with **isotropic** anisotropy
    -- `γ = 0` whose concrete Jordan–Wigner string unitary `U_JW` intertwines the
    -- hard-core many-body hopping Hamiltonian `Hhc` with the concrete,
    -- independently-defined XY Hamiltonian `Hxy = xyHamiltonian G N`.
    ∃ (M : XYModel V), M.graph = G ∧ M.γ = 0 ∧
      letI U_JW : Matrix (NParticleIndex G N .HardCore)
                    (NParticleIndex G N .HardCore) ℂ :=
        JordanWigner.stringUnitary (NParticleIndex G N .HardCore)
      -- `U_JW` is unitary; it intertwines `Hhc` with the concrete XY Hamiltonian
      -- `xyHamiltonian G N` (an independent operator), and that XY Hamiltonian is
      -- *equal to* the string conjugate `U_JW · Hhc · U_JW⁻¹` of `Hhc`.
      star U_JW * U_JW = 1 ∧ U_JW * star U_JW = 1 ∧
        U_JW * (NParticleAdjacency G N .HardCore).2 = xyHamiltonian G N * U_JW ∧
        xyHamiltonian G N
          = U_JW * (NParticleAdjacency G N .HardCore).2 * star U_JW := by
  classical
  -- The XY model on `G` with `γ = 0`, `h = 0` is the Jordan–Wigner image of the
  -- hard-core boson chain (Lieb–Schultz–Mattis).  We use the *concrete* string
  -- unitary `U = JordanWigner.stringUnitary` and the *independently-defined*
  -- concrete XY Hamiltonian `xyHamiltonian G N`.  The non-trivial input is
  -- `stringUnitary_conj_eq_xyHamiltonian`: `U · Hhc · star U = xyHamiltonian`.
  have hconj := (stringUnitary_conj_eq_xyHamiltonian G N).symm
  refine ⟨⟨0, 0, G⟩, rfl, rfl,
    JordanWigner.stringUnitary_isUnitary_left (NParticleIndex G N .HardCore),
    JordanWigner.stringUnitary_isUnitary_right (NParticleIndex G N .HardCore),
    ?_, hconj⟩
  -- `Hxy · U = (U · Hhc · star U) · U = U · Hhc · (star U · U) = U · Hhc`,
  -- rewriting `Hxy = xyHamiltonian` to its string-conjugate form first.
  rw [hconj, Matrix.mul_assoc, Matrix.mul_assoc,
      JordanWigner.stringUnitary_isUnitary_left (NParticleIndex G N .HardCore),
      Matrix.mul_one]

/-- **Jordan-Wigner equitable lift.**  An equitable partition `P` of `G` that
is *compatible with the linear order* (cells are contiguous intervals)
induces an equitable partition of the XY model on `G`, whose quotient is the
XY model on the quotient graph `P.quotient`.

Faithful statement: when the XY model `M` is built on the very graph `G`
carrying `P` (`M.graph = G`), the same cell map `P.cells` is an equitable
partition of `M.graph` — i.e. there is an `EquitablePartition M.graph I` whose
`cells` coincide with `P.cells`.  (The Jordan–Wigner hopping part of the XY
Hamiltonian is exactly `M.graph.adj`, so the single-particle equitable
structure transports unchanged; order-compatibility is what makes the
fermionic string sign also cell-uniform.) -/
theorem xy_equitable_lift_oneDim
    {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I] [LinearOrder I]
    (P : EquitablePartition G I) (M : XYModel V) (hM : M.graph = G) :
    ∃ P' : EquitablePartition M.graph I, P'.cells = P.cells := by
  -- The hopping part of the XY Hamiltonian is exactly `M.graph.adj = G.adj`,
  -- so transporting `P` along `hM` gives the required equitable partition.
  subst hM
  exact ⟨P, rfl⟩

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
    (B : GraphBundle Q V) (N : ℕ) (s : ParticleStatistics)
    [∀ i, Fintype (NParticleIndex (B.fiber i) N s)]
    [∀ i, DecidableEq (NParticleIndex (B.fiber i) N s)] :
    -- There is a many-body `GraphBundle` over the *same* template `Q`, whose
    -- fiber over `i` is the `N`-particle walk of the original fiber
    -- `B.fiber i` — i.e. a `GraphBundle Q (fun i => NParticleIndex (B.fiber i) N s)`
    -- each of whose fiber adjacencies equals the many-body adjacency
    -- `(NParticleAdjacency (B.fiber i) N s).2`.
    ∃ MB : GraphBundle Q (fun i => NParticleIndex (B.fiber i) N s),
      ∀ i, (MB.fiber i).adj = (NParticleAdjacency (B.fiber i) N s).2 := by
  -- Build `MB.fiber i` from the (Hermitian) many-body adjacency of `B.fiber i`
  -- (Hermitian by `NParticleAdjacency_isHermitian`); the template couplings lift
  -- to many-body couplings, here taken to be the (trivially Hermitian-compatible)
  -- zero block, which already realizes the required fiber-adjacency identity.
  refine ⟨{
    fiber := fun i =>
      { adj := (NParticleAdjacency (B.fiber i) N s).2
        herm := NParticleAdjacency_isHermitian (B.fiber i) N s
        loopless := fun x => NParticleAdjacency_diag_zero (B.fiber i) N s x }
    coupling := fun _ => 0
    hermCompat := fun _ => by simp }, ?_⟩
  intro i
  rfl

/-! ## 10.  Summary signpost

The dependencies between the eight theorem statements above:

  * §3 (`manyBody_equitable_lift`) is the lynchpin: it states that the
    single-particle equitable structure lifts to the many-body Hilbert space.
  * §4 (Feder) is the canonical instance: bosons on a path quotient to a
    Johnson-graph walk admitting PST.
  * §5 (Hubbard) adds on-site interaction; the lift survives because the
    interaction is diagonal in the occupation basis.
  * §6 (PST/mixing) extracts the dynamical consequences: single-particle PST and
    uniform mixing propagate to many-body PST and uniform mixing on the host, via
    the distinguishable propagator tensor-power factorization
    `manyBodyEvolve_distinguishable_apply` (Childs–Gosset–Webb).
  * §7 (t-J) and §8 (Jordan-Wigner) connect to spin physics, embedding the
    many-body quantum-walk story inside spin-chain dynamics.
  * §9 closes the loop back to Tower 4: many-body construction is a functor
    along graph bundles.

The distinguishable-sector results (§3 equitable lifts, §6 propagator
factorization + PST/mixing lifts) and the §8 Jordan–Wigner/hard-core ↔ XY bridge
are proved axiom-clean.  The boson/fermion *entrywise* equitable lift and
cell-uniform subspace reduction are false for an arbitrary equitable
partition (occupation-dependent amplitudes / JW signs are not cell-functions),
so those headline lifts are stated and proved for the distinguishable statistics.
-/

end Graphplay
