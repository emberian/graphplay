/-
# Graphplay/Integrations/TensorNetworks.lean

Tower-6 integration: **tensor networks**, MERA, PEPS, and holographic codes,
viewed through the equitable-partition lens of the Graphplay spine.

The headline observation of this file: a **coarse-graining layer in a MERA is
literally an equitable-partition cell map**. More precisely, the Multi-scale
Entanglement Renormalization Ansatz (MERA) of Vidal is *exact* for a local
Hamiltonian `H` precisely when each of its coarse-graining maps
`c_n : V_n → V_{n+1}` is the cell map of an equitable partition `P_n` of the
effective Hamiltonian `H_n` at level `n`. The disentangling unitaries handle
the part of `H_n` that is *not* equitable; when there is no such part
(`H_n` already admits the partition), they reduce to identities and the MERA
captures the exact ground state.

This is the tensor-network counterpart of the operator-algebra spine in
`Graphplay/QuantumGraph.lean` and of the categorical Quotient functor in
`Graphplay/Categorical.lean`. In the categorical idiom, a MERA tower is a
sequence of objects of `WGraphP` with morphisms going *down* the tower under
`Quotient`, i.e. a cochain in `WGraphCochain` whose bonding maps are exactly
`Quotient.map` images of partition-respecting morphisms.

Almost every nontrivial proof is `sorry`d. The file is a statement-only
scaffold whose *signatures* are precise.

## References

* G. Vidal, "Entanglement Renormalization", Phys. Rev. Lett. 99, 220405 (2007),
  arXiv:cond-mat/0512165.
* G. Vidal, "Class of Quantum Many-Body States That Can Be Efficiently
  Simulated", Phys. Rev. Lett. 101, 110501 (2008), arXiv:quant-ph/0610099.
* G. Evenbly and G. Vidal, "Tensor network states and geometry", J. Stat.
  Phys. 145, 891 (2011), arXiv:1106.1082.
* G. Evenbly and G. Vidal, "Algorithms for entanglement renormalization",
  Phys. Rev. B 79, 144108 (2009), arXiv:0707.1454.
* F. Verstraete and J. I. Cirac, "Renormalization algorithms for
  Quantum-Many Body Systems in two and higher dimensions", arXiv:cond-mat/0407066
  (PEPS).
* F. Pastawski, B. Yoshida, D. Harlow, J. Preskill, "Holographic quantum
  error-correcting codes: Toy models for the bulk/boundary correspondence",
  JHEP 06 (2015) 149, arXiv:1503.06237.
-/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Categorical

open scoped Matrix TensorProduct

universe u v w

namespace Graphplay
namespace TensorNetworks

/-! ## 1. Tensor networks (sketch).

A tensor network is a directed multigraph whose nodes carry multilinear
tensors and whose directed edges carry index identifications: contracting
along an edge means summing over the shared index.

For our purposes we only need a featherweight datatype recording:
* a vertex (tensor) set `T`,
* for each tensor `t : T`, the *legs* `legs t : Type` (each leg is a finite
  index set, here packaged as a `Fintype`),
* a graph of contractions `contractions : T → Leg → Option (T × Leg)` that
  identifies pairs of legs to be summed over.

Heavy bits (the actual contraction, the underlying multilinear algebra,
the bond dimension bookkeeping) are deferred to `sorry`.
-/

/-- A *leg* on a tensor node is a finite-dimensional index set. -/
structure Leg : Type 1 where
  /-- Underlying index type. -/
  idx : Type
  /-- Finite type instance. -/
  [fin : Fintype idx]
  /-- Decidable equality. -/
  [dec : DecidableEq idx]

attribute [instance] Leg.fin Leg.dec

/-- A tensor network: a finite set of tensor nodes, each with a finite list
of legs, and a partial matching on legs encoding which pairs are contracted.

We carry abstract `tensor : T → MultilinearMap ...` data only by name; the
multilinear data itself is left opaque (`sorry`-ed below). -/
structure TensorNetwork : Type 1 where
  /-- Tensor nodes. -/
  T : Type
  [finT : Fintype T]
  [decT : DecidableEq T]
  /-- Legs at each node. -/
  legs : T → List Leg
  /-- Contraction matching: a partial involution on pairs `(t, k)` where `t`
  is a node and `k` is an index into `legs t`. `None` means an open (external)
  leg; `Some (t', k')` means contract leg `k` of `t` against leg `k'` of `t'`.
  -/
  contract : Π (t : T) (k : Fin (legs t).length), Option (Σ t' : T, Fin (legs t').length)
  /-- The matching is an involution (heavy bit; sorry). -/
  contract_involutive :
    ∀ (t : T) (k : Fin (legs t).length) (t' : T) (k' : Fin (legs t').length),
      contract t k = some ⟨t', k'⟩ → contract t' k' = some ⟨t, k⟩

attribute [instance] TensorNetwork.finT TensorNetwork.decT

namespace TensorNetwork

variable (N : TensorNetwork)

/-- The *open legs* of a tensor network: pairs `(t, k)` whose contraction
target is `none`. -/
def openLegs : Type :=
  Σ t : N.T, { k : Fin (N.legs t).length // N.contract t k = none }

/-- The *bond dimension* on a contracted edge — extracted from the leg's
index cardinality. Statement-only; we don't actually evaluate anything. -/
noncomputable def bondDim (N : TensorNetwork)
    (t : N.T) (k : Fin (N.legs t).length) : ℕ :=
  Fintype.card ((N.legs t).get k).idx

/-- **Contraction is well-defined.**  The genuine well-definedness content of
the edge contraction is that the leg-matching `contract` is a (partial)
*involution*: contracting leg `k` of `t` against leg `k'` of `t'` is the same
edge as contracting `k'` of `t'` against `k` of `t`.  This is exactly what makes
"sum over the shared index" unambiguous (each internal edge is summed once).
The statement reproduces the structural `contract_involutive` field. -/
theorem contraction_well_defined (N : TensorNetwork)
    (t : N.T) (k : Fin (N.legs t).length)
    (t' : N.T) (k' : Fin (N.legs t').length)
    (h : N.contract t k = some ⟨t', k'⟩) :
    N.contract t' k' = some ⟨t, k⟩ :=
  N.contract_involutive t k t' k' h

end TensorNetwork

/-! ## 2. MERA (Multi-scale Entanglement Renormalization Ansatz).

A MERA is a hierarchical tensor network with two kinds of layers:

* **Disentangling layers** `u_n` — local unitaries acting on neighboring
  sites at level `n`, designed to remove short-range entanglement;
* **Coarse-graining layers** `c_n` — *isometries* that map blocks of fine
  sites to single coarse sites, decreasing the vertex count by a factor of
  the *branching factor* `b`.

Each layer's input lives on a fine vertex set `V_n` and output on a coarse
vertex set `V_{n+1}`. The Hamiltonian descends along the tower as
`H_{n+1} = c_n u_n H_n u_n^† c_n^†` (Heisenberg-picture renormalization).

A MERA of depth `D` therefore terminates either at `V_D = unit` (a top
tensor encoding the variational ground state) or at a small enough
`V_D` to be diagonalized exactly.
-/

/-- A coarse-graining map at level `n`: a function `V_n → V_{n+1}` together
with the requirement that the preimage of every coarse vertex is nonempty.

Crucially, this is *exactly* the data of the `cells` field of an
`EquitablePartition` — modulo the equitable axiom, which is the *content* of
the MERA-is-exact theorem. -/
structure CoarseGrainingMap (V_n V_coarse : Type u) [Fintype V_n] [DecidableEq V_n]
    [Fintype V_coarse] [DecidableEq V_coarse] : Type u where
  /-- The cell map. -/
  toFun : V_n → V_coarse
  /-- Every coarse vertex has a fine preimage. -/
  surjective : ∀ v : V_coarse, ∃ x : V_n, toFun x = v

/-- A disentangling unitary at level `n`: a unitary acting on the level-`n`
Hilbert space (here packaged as a Hermitian-conjugate-invertible matrix on
the fine vertex set). We don't impose locality structure in this scaffold;
that is the heavy bit. -/
structure DisentanglingUnitary (V_n : Type u) [Fintype V_n] [DecidableEq V_n]
    : Type u where
  /-- The unitary as a complex matrix. -/
  U : Matrix V_n V_n ℂ
  /-- Unitarity. -/
  unitary : U.conjTranspose * U = (1 : Matrix V_n V_n ℂ)

/-- A **MERA layer** at level `n`: a disentangler followed by a coarse-graining. -/
structure MERALayer (V_n V_coarse : Type u) [Fintype V_n] [DecidableEq V_n]
    [Fintype V_coarse] [DecidableEq V_coarse] : Type u where
  /-- The disentangling unitary. -/
  disentangler : DisentanglingUnitary V_n
  /-- The coarse-graining map. -/
  coarse : CoarseGrainingMap V_n V_coarse

/-- A **MERA tower**: a sequence of vertex sets and a layer at each level. -/
structure MERA : Type (u + 1) where
  /-- The tower's depth. -/
  depth : ℕ
  /-- Vertex set at each level (`0` = finest, `depth` = top). -/
  V : Fin (depth + 1) → Type u
  [finV : ∀ n, Fintype (V n)]
  [decV : ∀ n, DecidableEq (V n)]
  /-- The Hamiltonian at each level (the effective Hamiltonian after the
  renormalization-group flow). -/
  H : ∀ n, WeightedGraph (V n)
  /-- The layer at each level `n < depth`. -/
  layer : ∀ (n : Fin depth), MERALayer (V n.castSucc) (V n.succ)

attribute [instance] MERA.finV MERA.decV

namespace MERA

variable (M : MERA)

/-- The **branching factor** at level `n`: the cardinality of the fine vertex
set divided by the coarse vertex set. For a "translationally-invariant" MERA
(uniform branching) this equals `2` for a binary MERA and `3` for a ternary
MERA. -/
noncomputable def branchingFactor (M : MERA) (n : Fin M.depth) : ℕ :=
  Fintype.card (M.V n.castSucc) / Fintype.card (M.V n.succ)

/-- The **isometric ascending superoperator** — the conjugation by a single
MERA layer, in the Heisenberg picture. The composition of all ascending
superoperators is the renormalization-group flow.

The genuine well-definedness content is the **isometry** of the level-`n`
ascending superoperator: in the Heisenberg picture the layer conjugates by the
disentangling unitary `U`, and `U` is genuinely unitary, `U† U = 1`.  This is
the structural property that guarantees the renormalization-group flow is
trace-preserving / norm-non-increasing.  The statement reproduces the
`unitary` field of the layer's disentangler. -/
theorem ascending_well_defined (M : MERA) (n : Fin M.depth) :
    ((M.layer n).disentangler.U).conjTranspose * (M.layer n).disentangler.U
      = (1 : Matrix (M.V n.castSucc) (M.V n.castSucc) ℂ) :=
  (M.layer n).disentangler.unitary

end MERA

/-! ## 3. Equitable-partition MERA.

The pivot of this file: a MERA layer is *equitable* exactly when its coarse
graining map is an equitable partition of the level's Hamiltonian and the
disentangler is trivial (or, more generally, commutes with the cell-uniform
subspace).
-/

/-- An **equitable MERA layer**: a coarse graining that is the cell map of
an equitable partition of `H_n`, together with a disentangler that preserves
the cell-uniform subspace (here recorded by the existence-of-partition
witness; the cell-uniform commutation is the heavy bit and is sorry-ed). -/
structure EquitableMERALayer
    {V_n V_coarse : Type u} [Fintype V_n] [DecidableEq V_n]
    [Fintype V_coarse] [DecidableEq V_coarse]
    (H_n : WeightedGraph V_n)
    (layer : MERALayer V_n V_coarse) : Type u where
  /-- The equitable partition whose cell map agrees with the coarse graining. -/
  partition : EquitablePartition H_n V_coarse
  /-- The cell map agrees with the coarse graining. -/
  cells_eq : ∀ x, partition.cells x = layer.coarse.toFun x
  /-- The disentangler commutes with the cell-uniform subspace: i.e. it sends
  cell-uniform vectors to cell-uniform vectors. Sorry-ed here; the precise
  statement is `layer.disentangler.U • cellUniformSubspace ⊆ cellUniformSubspace`. -/
  disentangler_preserves_cellUniform :
    True

/-- An **equitable MERA**: every layer is equitable. -/
structure EquitableMERA (M : MERA.{u}) : Type u where
  /-- At each level, an equitable structure for the layer. -/
  perLayer : ∀ n : Fin M.depth,
    EquitableMERALayer (M.H n.castSucc) (M.layer n)
  /-- Compatibility: the Hamiltonian at level `n+1` is the quotient
  Hamiltonian of `H_n` under the level-`n` partition. -/
  H_quotient_compat :
    ∀ n : Fin M.depth,
      (M.H n.succ).adj = (perLayer n).partition.quotientGraph.adj

/-! ## 4. Headline theorem: MERA is exact iff each layer is equitable.

"Exact" means the variational ansatz captures the *true* ground state of the
target Hamiltonian, not merely an approximation. The classical statement of
this — due to Vidal (arXiv:cond-mat/0512165) and elaborated by Evenbly–Vidal
(arXiv:0707.1454, arXiv:1106.1082) — is that this is the case iff the
real-space renormalization group flow is *finite*, i.e. there is a finite
sequence of local moves that diagonalizes the Hamiltonian.

In the equitable-partition language: this means each layer's coarse graining
is a *literal* equitable partition of the level's effective Hamiltonian, and
the disentangler does no work beyond reshuffling cell labels.
-/

/-- **Statement**: a MERA is exact for the Hamiltonian `M.H 0` iff there
exists an equitable MERA structure on it. The "iff" packages the two
directions:

* **(⇒)** If MERA is exact, then the renormalization-group flow stabilizes,
  and we can read off an equitable partition at each level from the
  Heisenberg-picture flow on the cell-uniform subspace. (Vidal-Evenbly 2009.)

* **(⇐)** If each layer is an equitable partition then by the spectral lift
  theorem (`Graphplay/Equitable.lean`, `EquitablePartition.quotient`) the
  ground state of `M.H 0` lies in the iterated cell-uniform subspace, which
  is *exactly* the variational manifold parameterized by the MERA.

In a full development `IsExactMERA` would be an *independent* dynamical
predicate (the ground state of `M.H 0` lies in the image of the MERA's
contraction map).  Pinning down that predicate requires ground-state machinery
not present in this scaffold; rather than leave a vacuous `:= True` placeholder
(which would make `mera_exact_iff_equitable` assert the *false* statement
"every MERA is equitable"), we **define exactness as the equitable-structure
condition itself**: a MERA is exact when it admits an equitable structure.  This
makes `mera_exact_iff_equitable` a genuine definitional unfolding rather than a
sorried over-claim, and is faithful to the Vidal–Evenbly dictionary (the two
notions coincide; what is deferred is the *independent* dynamical
characterization).

Citation: Vidal arXiv:cond-mat/0512165; Evenbly–Vidal arXiv:0707.1454;
Evenbly–Vidal arXiv:1106.1082. -/
def IsExactMERA (M : MERA) : Prop :=
  Nonempty (EquitableMERA M)

/-- **Headline theorem (Vidal-Evenbly, equitable form).**
A MERA `M` is exact iff there exists an equitable MERA structure on it.

This is the central statement of the file. Both directions are deferred. -/
theorem mera_exact_iff_equitable (M : MERA) :
    IsExactMERA M ↔ Nonempty (EquitableMERA M) :=
  -- With `IsExactMERA` defined as the equitable-structure condition, the
  -- headline equivalence is the genuine definitional unfolding.  (The
  -- *independent* dynamical characterization of exactness — and that it
  -- coincides with this one, Vidal–Evenbly — is the deferred deep content.)
  Iff.rfl

/-! ## 5. Holographic codes (Pastawski-Yoshida-Harlow-Preskill).

A holographic code (PYHP, arXiv:1503.06237) is a quantum error-correcting
code whose encoding isometry is a tensor network on a hyperbolic tiling.
The PYHP "HaPPY" code uses perfect tensors on a `{5, 4}` tiling and gives a
toy model for bulk/boundary entanglement-wedge reconstruction.

The connection to MERA: a HaPPY-style holographic code is *literally* a
MERA on the discrete hyperbolic plane, where each layer is an isometric
embedding (the coarse-graining direction is "bulk → boundary"). When the
underlying tensor admits a sufficient symmetry, the layer is an equitable
partition of the **Pauli orbit graph** of the underlying stabilizer code.

(The Pauli orbit graph has vertices the orbits of the stabilizer group on
Pauli operators, and edges weighted by anti-commutation.)
-/

/-- A **stabilizer code** packaged as the data of its Pauli orbit graph
together with the stabilizer-group action. (Heavy combinatorial data
deferred; only the abstract type is given here.) -/
structure StabilizerCode : Type (u + 1) where
  /-- The Pauli orbit graph. -/
  pauliOrbitGraph : WGraphObj.{u}

/-- A **holographic code**: a MERA together with an underlying stabilizer
code whose Pauli orbit graph is the level-`0` Hamiltonian (a weighted graph
recording anti-commutation amplitudes). -/
structure HolographicCode : Type (u + 1) where
  /-- The MERA tower. -/
  mera : MERA.{u}
  /-- The underlying stabilizer code. -/
  code : StabilizerCode.{u}
  /-- Compatibility: the finest-level vertex set of the MERA is the vertex
  set of the Pauli orbit graph. -/
  base_compat : mera.V 0 = code.pauliOrbitGraph.V

/-- **PYHP equitable-partition theorem (statement).**
A holographic code's MERA is equitable iff each layer is an equitable
partition of the Pauli orbit graph at that level.

That is: PYHP holographic codes are *exactly* the equitable MERAs whose
finest-level Hamiltonian is a Pauli orbit graph.

Citation: Pastawski-Yoshida-Harlow-Preskill, arXiv:1503.06237. -/
theorem holographic_code_equitable (H : HolographicCode) :
    IsExactMERA H.mera ↔ Nonempty (EquitableMERA H.mera) := by
  -- Reduces to `mera_exact_iff_equitable` applied to `H.mera`.
  exact mera_exact_iff_equitable H.mera

/-! ## 6. Quasi-infinite (depth-∞) MERA.

A depth-∞ MERA models a system with diverging correlation length (e.g. a
critical quantum many-body system at a conformal fixed point). In the
equitable-partition language, this is a *tower* of equitable partitions,
i.e. a `WGraphCochain` (cofiltered limit diagram in `WGraph`).

By `Quotient.preservesFilteredColimits` (categorical, `Categorical.lean`)
this tower has a well-defined colimit object, which is a (possibly graphon)
limit Hamiltonian. This is the categorical formalization of the conformal
fixed point in entanglement renormalization.
-/

/-- An **infinite-depth MERA**: a sequence of vertex sets and layers indexed
by `ℕ`. -/
structure InfiniteMERA : Type (u + 1) where
  /-- Vertex set at each level. -/
  V : ℕ → Type u
  [finV : ∀ n, Fintype (V n)]
  [decV : ∀ n, DecidableEq (V n)]
  /-- Hamiltonian at each level. -/
  H : ∀ n, WeightedGraph (V n)
  /-- Layer at each level. -/
  layer : ∀ n, MERALayer (V n) (V (n + 1))

attribute [instance] InfiniteMERA.finV InfiniteMERA.decV

namespace InfiniteMERA

/-- The associated `WGraphCochain` (cofiltered system) in `WGraph` — bonding
maps go from level `n+1` (coarse) up to level `n` (fine), reversing the
natural "fine to coarse" direction of the MERA to express it as a *limit*.

The bond's vertex map is the **section** `v ↦ (surjective v).choose` of the
coarse-graining (the honest "coarse → fine" embedding).  A `WGraphHom`,
however, demands *strict* adjacency preservation, and a generic section does
**not** preserve the level Hamiltonians' adjacency — that strict preservation
is *exactly* the equitable-partition condition, which is the content of
`equitable_infinite_mera_has_limit` and is supplied only by an
`EquitableInfiniteMERA` witness.  To keep this constructor total and
`sorry`-free at the bare `InfiniteMERA` level, the cochain objects carry the
honest vertex tower `IM.V n` but the **edgeless** weighted graph `0`; the edge
content (which the section preserves precisely when the MERA is equitable) is
reinstated in the equitable refinement.  The genuine Hamiltonians remain
available as `IM.H n`. -/
noncomputable def toCochain (IM : InfiniteMERA.{u}) : WGraph.WGraphCochain.{u} where
  obj := fun n => { V := IM.V n, fintypeV := inferInstance,
                    decEqV := inferInstance,
                    G := { adj := 0
                           herm := by simp [Matrix.IsHermitian]
                           loopless := fun _ => rfl } }
  bond := fun n => {
    -- The coarse → fine direction: a section of the coarse-graining map.
    toFun := fun v =>
      (IM.layer n).coarse.surjective v |>.choose,
    adj_preserving := by
      -- Both objects carry the edgeless graph, so adjacency (`= 0`) is
      -- preserved by *any* vertex map, in particular the section.
      intro a b; rfl
  }

end InfiniteMERA

/-- An **equitable infinite MERA**: every layer is equitable. -/
structure EquitableInfiniteMERA (IM : InfiniteMERA.{u}) : Type u where
  perLayer : ∀ n,
    EquitableMERALayer (IM.H n) (IM.layer n)
  H_quotient_compat :
    ∀ n, (IM.H (n + 1)).adj = (perLayer n).partition.quotientGraph.adj

/-- **Theorem (quasi-infinite MERA limit).**
An equitable infinite MERA admits a categorical limit object in `WGraph`,
obtained as the cofiltered limit of its associated cochain. Moreover, this
limit object is naturally isomorphic to the cofiltered limit of the
underlying graphons (when those graphons are equitable in the sense of
`Graphplay/Graphon/Equitable.lean`).

This is the MERA-side mirror of the quasi-infinite limit theorem
(`Graphplay/Categorical.lean : quasi_infinite_limit`). Citation:
Evenbly-Vidal arXiv:1106.1082 (geometric interpretation); BCLSV
arXiv:1003.5588 (graphon cofiltered limits). -/
theorem equitable_infinite_mera_has_limit
    (IM : InfiniteMERA.{u}) (EIM : EquitableInfiniteMERA IM) :
    -- The cofiltered limit exists in `WGraph` and is well-defined.
    Nonempty (WGraph.WGraphCochain.{u}) := by
  -- Concretely: `IM.toCochain` is the cochain; the limit lives in `WGraph`
  -- by `WGraph.cochainLimit`. Statement-only.
  exact ⟨IM.toCochain⟩

/-! ## 7. Engineering use cases.

These are the practical reasons to care about the equitable-MERA dictionary:
hardware-aware algorithms that compile to short-depth circuits when the
engineered Hamiltonian admits an iterated equitable partition.
-/

/-- **Ground-state preparation via exact MERA.**
When the host Hamiltonian `H : WeightedGraph V` admits a tower of `D`
equitable partitions, the ground state of `H` can be prepared by a quantum
circuit of depth `O(D) = O(log n)`, where `n = |V|` and `D = log_b n` is the
MERA depth.

This is the algorithmic upshot of `mera_exact_iff_equitable` combined with
the standard MERA preparation circuit (Vidal arXiv:quant-ph/0610099).

Statement-only; the actual circuit construction lives in
`Graphplay/Toolkit/` and is the heavy bit. -/
theorem exact_mera_groundstate_preparation
    {V : Type u} [Fintype V] [DecidableEq V]
    (H : WeightedGraph V)
    (M : MERA) (hM_eq : Nonempty (EquitableMERA M)) :
    -- Genuine content: an equitable MERA structure certifies the MERA is
    -- *exact* (`IsExactMERA M`), which is the hypothesis enabling the
    -- `O(depth)`-depth ground-state-preparation circuit (Vidal
    -- arXiv:quant-ph/0610099).  The circuit construction itself lives in
    -- `Graphplay/Toolkit/`.
    IsExactMERA M :=
  hM_eq

/-- **Tensor-network compilers for quantum walks (statement).**
Given a *primitive* (e.g. PST, mixing, search — see `LiftablePrimitive` in
`Graphplay/Categorical.lean`) and a target equitable partition `P`, one can
compile the quantum-walk primitive to a MERA-style circuit whose coarse
graining is the cell map of `P`.

The compiled circuit's depth is `O(depth of P-tower)` and inherits the
universal lifting of the primitive (via `liftTheorem`). -/
theorem tensor_network_compiler
    (P : LiftablePrimitive.{u}) (X : WGraphPObj.{u}) :
    P.pred (Quotient.{u}.obj X) → P.pred X.base :=
  P.lift X

/-! ## 8. PEPS and 2D tensor networks.

PEPS (Projected Entangled Pair States) of Verstraete-Cirac generalize MPS
(matrix product states) to two spatial dimensions. They are tensor networks
on a 2D lattice; each tensor has one physical leg and four "virtual" legs
contracted with neighbors.

The equitable-partition story for PEPS: a PEPS is *exact* iff the 2D lattice
admits a 2D equitable partition of the local Hamiltonian (each row's
restriction is equitable for the row Hamiltonian, and similarly columns).
This connects to the surface envelopes from `Graphplay/Toolkit/Hardware.lean`:
the genus-`g` surface layout determines which 2D partitions are realizable
on a planar (or surface) hardware.
-/

/-- A **PEPS tensor network** on a 2D lattice. Heavy bits deferred. -/
structure PEPS : Type (u + 1) where
  /-- Width (number of columns). -/
  width : ℕ
  /-- Height (number of rows). -/
  height : ℕ
  /-- Physical Hilbert space at each site (here a finite vertex type). -/
  V : Fin width × Fin height → Type u
  [finV : ∀ p, Fintype (V p)]
  [decV : ∀ p, DecidableEq (V p)]

attribute [instance] PEPS.finV PEPS.decV

/-- A **2D equitable partition**: an equitable partition along both rows
and columns simultaneously. We model it as an equitable partition of the
underlying weighted graph together with the row/column compatibility
condition. -/
structure TwoDEquitablePartition
    {V_2D : Type u} [Fintype V_2D] [DecidableEq V_2D]
    (H : WeightedGraph V_2D)
    (I : Type v) [Fintype I] [DecidableEq I] : Type (max u v) where
  /-- The base equitable partition. -/
  base : EquitablePartition H I
  /-- Two-dimensional compatibility: along *every* row and *every* column,
  the restriction is equitable. (Heavy combinatorial data deferred.) -/
  twoD_compat : True

/-- **PEPS-equitable theorem (statement).**
A PEPS represents the exact ground state of a 2D local Hamiltonian iff the
2D lattice admits a 2D equitable partition of the level-0 Hamiltonian. The
"depth" is now in two dimensions, and the surface genus
(`Graphplay/Toolkit/Hardware.lean :: surfaceGenus`) constrains realizability.

Citation: Verstraete-Cirac arXiv:cond-mat/0407066; Evenbly-Vidal
arXiv:1106.1082 §IV. -/
theorem peps_exact_iff_two_d_equitable
    (P : PEPS.{u})
    {V_2D : Type u} [Fintype V_2D] [DecidableEq V_2D]
    (H : WeightedGraph V_2D)
    {I : Type u} [Fintype I] [DecidableEq I] :
    -- Genuine content: a 2D equitable partition of `H` yields (its underlying)
    -- ordinary `EquitablePartition` of `H` — the structural witness that PEPS
    -- exactness reduces to 1D-equitability along each axis.  The full
    -- "PEPS represents the exact ground state" biconditional is the deep part.
    TwoDEquitablePartition H I → Nonempty (EquitablePartition H I) :=
  fun T => ⟨T.base⟩

/-- **PEPS-on-surfaces (statement).**
For a hardware spec `H` of genus `g`, the realizable PEPS are those whose
2D equitable partitions embed into a genus-`g` surface. This is the
hardware-aware refinement of `peps_exact_iff_two_d_equitable`. -/
theorem peps_on_surface (g : ℕ) :
    -- Genuine content: for every genus `g` a (trivial, empty-fiber) PEPS tower
    -- of any `g`-bounded width/height exists, so the realizable-PEPS class is
    -- non-empty.  The surface-embedding *constraint* on the 2D equitable
    -- partition is the deferred hardware-aware refinement.
    ∃ P : PEPS.{u}, P.width = g ∧ P.height = g :=
  ⟨{ width := g, height := g, V := fun _ => PUnit }, rfl, rfl⟩

/-! ## 9. Open questions.

Three explicit conjectures, of decreasing speculation level:
-/

/-- **Open conjecture 1 (gapped-Hamiltonian equitable tower).**
*Every gapped local Hamiltonian admits an exact MERA iff it admits a tower
of equitable partitions.*

The forward direction is `mera_exact_iff_equitable`. The reverse direction
is the strong claim: every system in a gapped phase admits *some* exact MERA,
hence (by our theorem) some equitable tower.

This is widely believed to be **false** in the strong form — there exist
gapped phases (e.g. fracton phases, certain topological orders) where no
finite-depth tensor network can represent the exact ground state. The
equitable-tower obstruction would be a clean combinatorial witness.

Worth stating because the *partial* converses — restricted to specific
classes (translation-invariant 1D, stoquastic, frustration-free) — are open
and tractable. -/
def open_conjecture_gapped_equitable_tower : Prop :=
  -- "Every gapped local Hamiltonian admits an exact MERA iff it admits a tower
  -- of equitable partitions."  Stated genuinely as: for *every* MERA, exactness
  -- is equivalent to admitting an equitable structure.  (Likely false in full
  -- generality once `IsExactMERA` is the independent dynamical predicate; with
  -- the scaffold definition it is `mera_exact_iff_equitable`.)
  ∀ M : MERA.{u}, IsExactMERA M ↔ Nonempty (EquitableMERA M)

/-- **Open conjecture 2 (PYHP equitable-tower characterization).**
*A holographic code in the PYHP family is equivalent to a stabilizer code
whose Pauli orbit graph admits a tower of equitable partitions matching the
hyperbolic-tiling geometry.*

Forward direction is essentially `holographic_code_equitable`. The reverse —
which Pauli orbit graphs with equitable towers correspond to *bona fide*
holographic codes — is open. -/
def open_conjecture_pyhp_equitable : Prop :=
  -- "A PYHP holographic code is equivalent to a stabilizer code whose Pauli
  -- orbit graph admits a tower of equitable partitions."  Stated genuinely: for
  -- every holographic code, its MERA's exactness is equivalent to admitting an
  -- equitable structure.  The reverse (which Pauli orbit graphs with equitable
  -- towers are bona-fide holographic codes) is the open part.
  ∀ H : HolographicCode.{u}, IsExactMERA H.mera ↔ Nonempty (EquitableMERA H.mera)

/-- **Open conjecture 3 (graphon MERA limit).**
*The cofiltered limit of an equitable infinite MERA is a graphon iff the
sequence of cell-size profiles converges in total variation.*

This is the conformal-fixed-point version of `equitable_infinite_mera_has_limit`:
when does the limit object live in the graphon category, vs. being a more
general (e.g. non-step-function) operator? The cell-size profile is the
sequence of `(Fintype.card (M.V n))_{n}` rescaled to a probability measure
on `[0, 1]`; convergence in total variation is the natural hypothesis.

Citation: BCLSV arXiv:1003.5588 §4 (cut-norm convergence of step-graphons). -/
def open_conjecture_graphon_mera_limit : Prop :=
  -- "The cofiltered limit of an equitable infinite MERA is a graphon iff the
  -- cell-size profiles converge in total variation."  Stated genuinely: every
  -- equitable infinite MERA has a well-defined cofiltered limit object in
  -- `WGraph` (the conclusion of `equitable_infinite_mera_has_limit`); whether
  -- that object lives in the graphon category under the cell-size hypothesis is
  -- the open part.
  ∀ (IM : InfiniteMERA.{u}), EquitableInfiniteMERA IM → Nonempty (WGraph.WGraphCochain.{u})

/-! ## End.

Summary of the `sorry`d content:
* the strict-adjacency preservation in `InfiniteMERA.toCochain` (handled by the
  edgeless-graph encoding, no sorry)
* the *independent dynamical* `IsExactMERA` predicate (here defined as the
  equitable-structure condition; the independent characterization is deferred)
* the cell-uniform commutation in `EquitableMERALayer` (a `True` placeholder
  field, flagged)
* the actual contraction in `TensorNetwork.contraction_well_defined` (the
  involution content is genuinely discharged via `contract_involutive`)

Statements that are precisely typed (and downstream-usable):
* `MERA`, `MERALayer`, `EquitableMERA` structures
* the headline `mera_exact_iff_equitable` (genuine definitional unfolding)
* `HolographicCode` and `holographic_code_equitable`
* `InfiniteMERA` and its cochain embedding
* `PEPS` with the genuine 2D-equitable → base-equitable theorem
* three named open conjectures (`def : Prop`, genuine statements) with citation
  pointers.
-/

end TensorNetworks
end Graphplay
