/-
# Graphplay/Dowsing/HypergraphPST.lean

## Hole D7 — Hypergraph continuous-time quantum walks and perfect state transfer

Quantum walks on hypergraphs are an active and *unsettled* corner of the
quantum-walk literature: unlike on graphs, there is no single canonical
choice of Hamiltonian.  Three constructions dominate the discussion:

* the **clique-expansion Laplacian** — replace each `k`-hyperedge with the
  complete graph `K_k` on its support and use the standard graph Laplacian
  of the resulting (multi-)graph;
* the **Hodge (incidence) Laplacian** `L = B Bᴴ` formed from the complex
  vertex–edge incidence matrix introduced in `Graphplay/Relational.lean`,
  and (for `k ≥ 3`) its companion in the simplicial chain complex
  `∂ : C_k → C_{k-1}`, both viewed as Hermitian operators on the vertex
  space;
* the **tensor / higher-order line walk** — CTQW on the higher-order line
  graph whose vertices are `k`-tuples lying in a common hyperedge.

This file packages all three as `WeightedGraph V` constructions, defines
PST in each model in parallel with `Graphplay/PST.lean`, and lifts every
PST predicate through `RelEquitablePartition` quotients in the manner of
`Graphplay/Equitable.lean`.

It then conjectures the *cross-model coincidence theorem*: a hypergraph
admits PST in all three models simultaneously iff its incidence relation
itself satisfies a "doubly equitable" cell-uniformity condition, and lists
concrete families where the conjecture should be testable (Steiner triple
systems, complete `k`-uniform hypergraphs, partition designs from finite
geometries).

The chiral / signed extension and a Tower-4 hypergraphon limit appear in
sections 6 and 7.  Section 8 collects three open questions.

References:

* Lovász, *Large Networks and Graph Limits* (hypergraphon kernels).
* Chan–Coutinho–Tamon–Vinet–Zhan, *Fractional Revival and Association
  Schemes*, arXiv:1907.04729.
* Banerjee, *On the spectrum of hypergraphs*, Linear Algebra Appl. 614
  (2021) (Hodge Laplacian background).
* Bachman–Tamon, arXiv:1108.0339 (PST quotient lifting; binary case).

All proofs are `sorry`; this is a scaffold of the right shape, not a
verified development.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST
import Graphplay.Mixing
import Graphplay.Search
import Graphplay.Chiral
import Graphplay.Relational
import Graphplay.Graphon

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay
namespace Hypergraph

/-! ## 1. Three CTQW Hamiltonians on a hypergraph

Let `H : KUniform k V` be a `k`-uniform hypergraph in the sense of
`Graphplay/Relational.lean`, equipped with an explicit indexing of its
hyperedges by a finite type `E` and an `edge : E → (Fin k → V)` data.  We
build three Hermitian-zero-diagonal matrices on `V`, one per Hamiltonian
model, and package each as a `WeightedGraph V`.

The arguments `H : KUniform k V` and `_compat : ∀ e, H.rel () (edge e)`
say that `edge` enumerates a subset of the hyperedges of `H`; we keep
`H` around for the equitable-partition compatibility statements in §3.
-/

variable {k : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
variable {E : Type v} [Fintype E] [DecidableEq E]

/-! ### 1a. Clique-expansion Laplacian.

Each `k`-hyperedge `e` contributes one edge of weight `1` between every
unordered pair of distinct vertices in `e`.  The associated multigraph
(with multiplicities aggregated as a sum) has standard graph Laplacian
`D - A` where `A` is the adjacency multimatrix.  We package the **negated
adjacency** as a `WeightedGraph` so the CTQW Hamiltonian `H_clique = A` is
Hermitian and loopless (the diagonal of the Laplacian moves into a global
shift which is irrelevant for the unitary `exp(-i t · A)`).
-/

/-- The clique-expansion adjacency: for `u ≠ v`, the number of hyperedges
containing both `u` and `v`.  For `u = v`, zero. -/
def cliqueAdjEntry
    (edge : E → (Fin k → V)) (u v : V) : ℂ :=
  if u = v then 0
  else
    ((Finset.univ.filter
      (fun e : E => ∃ i j : Fin k, edge e i = u ∧ edge e j = v ∧ i ≠ j)).card : ℂ)

/-- The clique-expansion CTQW Hamiltonian as a `WeightedGraph V`. -/
def cliqueLaplacian
    (edge : E → (Fin k → V)) : WeightedGraph V where
  adj := fun u v => cliqueAdjEntry (E := E) edge u v
  herm := by
    -- Symmetric ℝ-valued entries are Hermitian.
    sorry
  loopless := by
    intro v
    simp [cliqueAdjEntry]

/-- The "Laplacian-shape" matrix `D - A` is preserved by `cliqueLaplacian`
up to the diagonal shift `D`, which commutes with `A`.  We expose `D` for
spectral discussions; in CTQW the diagonal phases just multiply the global
state by `exp(-i t d_v)` per vertex and so do not affect `IsPST` predicates
when the diagonal is constant (i.e. the hypergraph is regular). -/
def cliqueDegreeMatrix
    (edge : E → (Fin k → V)) : Matrix V V ℂ :=
  Matrix.diagonal (fun v : V =>
    ((Finset.univ.filter
      (fun e : E => ∃ i : Fin k, edge e i = v)).card : ℂ))

/-- A hypergraph is **clique-regular** if every vertex sits in the same
number of hyperedges.  When this holds the diagonal degree shift is a
scalar multiple of `1`, so it can be ignored in PST analysis. -/
def IsCliqueRegular
    (edge : E → (Fin k → V)) : Prop :=
  ∃ d : ℕ, ∀ v : V,
    (Finset.univ.filter (fun e : E => ∃ i : Fin k, edge e i = v)).card = d

/-! ### 1b. Hodge / incidence Laplacian.

We reuse the complex incidence matrix `Hypergraph.incidence k V E edge`
from `Graphplay/Relational.lean` and form the vertex-side Hodge Laplacian
`L_H = B Bᴴ` (acting on `ℂ^V`).  Hermiticity is automatic; looplessness
needs the standard normalization of `B` so that the diagonal of `B Bᴴ`
matches the vertex degree (already arranged in `Hypergraph.laplacian`).

We rebuild the operator here (rather than reusing `Hypergraph.laplacian`
directly) because we want the **off-diagonal** part only, which is the
piece responsible for inter-vertex transitions in the CTQW.
-/

/-- The Hodge / incidence Laplacian as a `WeightedGraph V`, equal to
`B Bᴴ` minus its own diagonal (so as to fit the loopless convention). -/
def hodgeLaplacian
    (edge : E → (Fin k → V)) : WeightedGraph V where
  adj := fun u v =>
    if u = v then 0
    else (Hypergraph.incidence k V E edge *
          (Hypergraph.incidence k V E edge).conjTranspose) u v
  herm := by
    -- `B Bᴴ` is Hermitian and removing the diagonal preserves Hermiticity.
    sorry
  loopless := by
    intro v; simp

/-- The simplicial `(k-1)`-Hodge Laplacian on the *edge* space `ℂ^E`:
`Δ_{k-1} = Bᴴ B`.  In dimension `k = 2` this is exactly the line-graph
Laplacian and `Δ_0 = B Bᴴ` on `ℂ^V` is the graph Laplacian.  For `k ≥ 3`
the two encode independent spectral information; the *up Laplacian*
`Δ_{k-1}^{up}` corresponds to walking on hyperedges that share a vertex.

Statement only — the proper definition requires a chain complex
`C_0 ← C_1 ← ... ← C_{k-1}` with boundary maps, which is left to a future
Tower-1.5 extension. -/
def hodgeEdgeLaplacian
    (edge : E → (Fin k → V)) : Matrix E E ℂ :=
  (Hypergraph.incidence k V E edge).conjTranspose *
    Hypergraph.incidence k V E edge

/-! ### 1c. Tensor / higher-order line walk.

The **higher-order line graph** `L_k(H)` has as vertex set the set of
ordered `k`-tuples in some hyperedge of `H`, and two such tuples are
adjacent iff they share `k-1` positions.  In the `k = 2` binary case this
reduces to the ordinary line graph.  The associated CTQW is sometimes
called the *tensor walk* because the Hamiltonian factorises into tensor
products of position-permutation operators.

We expose the vertex set as `{ (e, π) : E × (Fin k → V) // ... }` and
the adjacency as a `WeightedGraph`.
-/

/-- Vertices of the higher-order line graph: an enumerated `k`-tuple
inside one of the hyperedges.  We use the indexing `Fin k → V` and remember
the originating edge `e` so that the adjacency is decidable. -/
structure TensorVertex
    (edge : E → (Fin k → V)) where
  /-- The originating hyperedge. -/
  edgeIdx : E
  /-- A permutation of the positions within `edge edgeIdx`. -/
  perm : Fin k → Fin k
  /-- We only keep permutations (bijections of `Fin k`). -/
  perm_inj : Function.Injective perm

instance tensorVertex_fintype
    (edge : E → (Fin k → V)) : Fintype (TensorVertex (E := E) edge) := by
  -- Subtype of `E × (Fin k → Fin k)` with the injectivity predicate.
  classical
  sorry

instance tensorVertex_decEq
    (edge : E → (Fin k → V)) : DecidableEq (TensorVertex (E := E) edge) := by
  classical
  sorry

/-- The tensor-walk adjacency: two `k`-tuples are adjacent iff they share
`k-1` positions (and so differ by a transposition).  Hermitian, loopless. -/
def tensorWalk
    (edge : E → (Fin k → V)) :
    WeightedGraph (TensorVertex (E := E) edge) where
  adj := fun u v =>
    if u = v then 0
    else
      -- Count the number of positions on which `u.perm` and `v.perm`
      -- disagree, with `u.edgeIdx = v.edgeIdx`.
      if u.edgeIdx = v.edgeIdx ∧
         (Finset.univ.filter (fun i : Fin k => u.perm i ≠ v.perm i)).card = 2
      then 1 else 0
  herm := by
    -- Symmetric 0/1 matrix.
    sorry
  loopless := by
    intro v
    simp

/-! ## 2. PST predicates in each of the three models

We restate `IsPST` from `Graphplay/PST.lean` once per model.  The shape is
identical — `‖U(τ) u v‖ = 1` — only the underlying Hamiltonian changes.
We name the three predicates so the cross-model comparison theorem below
is statable without ambiguity.
-/

/-- PST between `u v : V` at time `τ` in the **clique-expansion** model. -/
def IsHypergraphPST_clique
    (edge : E → (Fin k → V)) (u v : V) (τ : ℝ) : Prop :=
  IsPST (cliqueLaplacian (E := E) edge) u v τ

/-- PST between `u v : V` at time `τ` in the **Hodge / incidence** model. -/
def IsHypergraphPST_hodge
    (edge : E → (Fin k → V)) (u v : V) (τ : ℝ) : Prop :=
  IsPST (hodgeLaplacian (E := E) edge) u v τ

/-- PST between tensor-walk vertices `u v` at time `τ` in the **tensor**
model. -/
def IsHypergraphPST_tensor
    (edge : E → (Fin k → V))
    (u v : TensorVertex (E := E) edge) (τ : ℝ) : Prop :=
  IsPST (tensorWalk (E := E) edge) u v τ

/-! ### Pretty-good state transfer in each model.

PGST is a strictly weaker condition: the modulus may approach `1` only
in a limit.  Useful for the spectral examples below (Steiner triple
systems often exhibit PGST without PST).
-/

def IsHypergraphPGST_clique
    (edge : E → (Fin k → V)) (u v : V) : Prop :=
  IsPGST (cliqueLaplacian (E := E) edge) u v

def IsHypergraphPGST_hodge
    (edge : E → (Fin k → V)) (u v : V) : Prop :=
  IsPGST (hodgeLaplacian (E := E) edge) u v

def IsHypergraphPGST_tensor
    (edge : E → (Fin k → V))
    (u v : TensorVertex (E := E) edge) : Prop :=
  IsPGST (tensorWalk (E := E) edge) u v

/-! ## 3. Equitable-partition lifting in each model

The relational equitable partition `RelEquitablePartition` from
`Graphplay/Relational.lean` is the right "upstairs" object.  We claim
that in each of the three models, the relational partition descends to a
Tower-2 `EquitablePartition` of the associated `WeightedGraph`, and that
PST / PGST / mixing / search all lift through the quotient by the
respective `EquitablePartition.*_lift` theorems already in `PST.lean`,
`Mixing.lean`, `Search.lean`.
-/

variable {I : Type w} [Fintype I] [DecidableEq I]

/-- **Clique-model equitable lifting.**  A relational equitable partition
of a hypergraph induces a Tower-2 equitable partition of its
clique-expansion `WeightedGraph`. -/
def relEquitable_clique
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (_compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I) :
    EquitablePartition (cliqueLaplacian (E := E) edge) I where
  cells := π.cells
  uniform := by
    -- For each pair of cells `i j` the branching number from `x ∈ C_i`
    -- into `C_j` is `∑_{y ∈ C_j} #{hyperedges containing both x and y}`
    -- which by the relational equitable condition (applied at every
    -- position pair `(p, q)`) depends only on the cell of `x`.
    sorry

/-- **Hodge-model equitable lifting.** -/
def relEquitable_hodge
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (_compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I) :
    EquitablePartition (hodgeLaplacian (E := E) edge) I where
  cells := π.cells
  uniform := by
    -- For Hodge: branching into cell `j` is `∑_{y ∈ C_j} (B Bᴴ)(x, y)`
    -- = `∑_e ∑_{y ∈ C_j, y ≠ x} B(x, e) star (B(y, e))`.  Cell-uniformity
    -- follows from the position-indexed relational equitable condition
    -- once we sum over edges incident to `x` of each "edge type"
    -- (Fin k → I).
    sorry

/-- **Tensor-model equitable lifting.**  The tensor-walk vertex set
`TensorVertex edge` admits a *derived* partition from `π`: a vertex
`(e, σ)` is classified by the cell-type `i ∘ σ : Fin k → I` of its
positions.  This derived partition is equitable for `tensorWalk`. -/
def relEquitable_tensor
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (_compat : ∀ e, H.rel () (edge e))
    (_π : RelEquitablePartition H I) :
    -- The derived index type for the tensor walk is `Fin k → I`.
    EquitablePartition
      (tensorWalk (E := E) edge)
      (Fin k → I) where
  cells := fun u =>
    -- the cell-type of the `k`-tuple `(u.perm i ↦ edge u.edgeIdx (u.perm i))`
    sorry
  uniform := by sorry

/-- **PST lift, clique model.**  PST on the relational quotient (between
two cells `i j : I`) lifts to cell-uniform PST on the host
`cliqueLaplacian`. -/
theorem pst_lift_clique
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (i j : I) (τ : ℝ) :
    True →  -- placeholder for "PST on the (clique) quotient at (i,j,τ)"
    IsCellUniformPST
      (cliqueLaplacian (E := E) edge)
      (relEquitable_clique (E := E) H edge compat π) i j τ := by
  intro _
  -- Reduce to `EquitablePartition.pst_lift` from `Graphplay/PST.lean`.
  sorry

/-- **PST lift, Hodge model.** -/
theorem pst_lift_hodge
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (i j : I) (τ : ℝ) :
    True →
    IsCellUniformPST
      (hodgeLaplacian (E := E) edge)
      (relEquitable_hodge (E := E) H edge compat π) i j τ := by
  intro _
  sorry

/-- **PST lift, tensor model.**  Indexed by the derived cell type
`Fin k → I`. -/
theorem pst_lift_tensor
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (i j : Fin k → I) (τ : ℝ) :
    True →
    IsCellUniformPST
      (tensorWalk (E := E) edge)
      (relEquitable_tensor (E := E) H edge compat π) i j τ := by
  intro _
  sorry

/-! ### Mixing and search liftings (statement-only).

We re-export the cell-uniform mixing and optimal-search predicates from
`Mixing.lean` / `Search.lean` for each of the three Hamiltonians. -/

theorem mixing_lift_clique
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (t : ℝ) :
    True →
    IsCellUniformMixing
      (cliqueLaplacian (E := E) edge)
      (relEquitable_clique (E := E) H edge compat π) t := by
  intro _; sorry

theorem mixing_lift_hodge
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (t : ℝ) :
    True →
    IsCellUniformMixing
      (hodgeLaplacian (E := E) edge)
      (relEquitable_hodge (E := E) H edge compat π) t := by
  intro _; sorry

theorem search_lift_clique
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (_π : RelEquitablePartition H I)
    (M : Finset V) (γ τ : ℝ) :
    True →
    IsOptimalSearch (cliqueLaplacian (E := E) edge) M γ τ := by
  intro _; sorry

theorem search_lift_hodge
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (_π : RelEquitablePartition H I)
    (M : Finset V) (γ τ : ℝ) :
    True →
    IsOptimalSearch (hodgeLaplacian (E := E) edge) M γ τ := by
  intro _; sorry

/-! ## 4. Cross-model comparison: doubly-equitable hypergraphs

When does a single relational equitable partition simultaneously give a
PST witness in all three CTQW models?  Conjecturally, this happens
precisely when a strengthened cell-uniformity condition holds: not only
must the *vertex* counts be cell-uniform (the standard
`RelEquitablePartition` axiom), but the *incidence* relation
`(v, e) ↦ ∃ i, edge e i = v` must itself be equitable as a binary
relation between vertices and edges.  We call this the **doubly-equitable**
condition.

The intuition: clique-expansion sees only pairs `(v, w)` co-occurring in
an edge, Hodge sees the incidence matrix `B` directly, and the tensor
walk sees the full position-indexed structure.  A single partition can
control all three exactly when it controls the incidence relation itself.
-/

/-- The doubly-equitable condition: the relational partition `π`
restricts to an equitable partition of both the vertex side and the
edge side of the incidence bipartite graph. -/
structure IsDoublyEquitable
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (π : RelEquitablePartition H I)
    (J : Type w) [Fintype J] [DecidableEq J]
    (edgeCells : E → J) : Prop where
  /-- Cell-uniformity of the incidence count `#{e ∈ C_J(j) : v ∈ e}`
  for `v` in each `π`-cell. -/
  vertex_uniform :
    ∀ (i : I) (j : J) (x y : V), π.cells x = i → π.cells y = i →
      (Finset.univ.filter
        (fun e : E => edgeCells e = j ∧ ∃ p : Fin k, edge e p = x)).card
      = (Finset.univ.filter
        (fun e : E => edgeCells e = j ∧ ∃ p : Fin k, edge e p = y)).card
  /-- Cell-uniformity of the incidence count `#{v ∈ C_I(i) : v ∈ e}`
  for `e` in each `edgeCells`-cell. -/
  edge_uniform :
    ∀ (i : I) (j : J) (e₁ e₂ : E), edgeCells e₁ = j → edgeCells e₂ = j →
      (Finset.univ.filter
        (fun p : Fin k => π.cells (edge e₁ p) = i)).card
      = (Finset.univ.filter
        (fun p : Fin k => π.cells (edge e₂ p) = i)).card

/-- **Cross-model PST coincidence (conjecture).**

Assume `π` is doubly-equitable for `H` with edge partition `edgeCells :
E → J`.  Then for any pair of `π`-cells `i j` and any time `τ`, the
following are equivalent:

* PST on the clique-quotient between cells `i` and `j` at time `τ`;
* PST on the Hodge-quotient between cells `i` and `j` at time `τ`;
* PST on the tensor-quotient between any "lifted" position-cells
  matching `(i, j)` at time `τ`.

In particular: under double equitability the *three CTQW models become
spectrally equivalent on the quotient*.  Stated here as a `sorry` —
the binary version of this for line graphs is folklore; the genuine
3-way equivalence for `k ≥ 3` appears not to be in the literature. -/
theorem cross_model_coincidence
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    {J : Type w} [Fintype J] [DecidableEq J]
    (edgeCells : E → J)
    (_hde : IsDoublyEquitable (E := E) H edge π J edgeCells)
    (i j : I) (τ : ℝ) :
    -- "Clique-quotient PST at τ" ↔ "Hodge-quotient PST at τ" ↔
    -- "Tensor-quotient PST at τ" (statement-level).
    True ↔ True := by
  exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- A weaker but more checkable cross-model statement: if the host
hypergraph is *clique-regular* (and hence the clique-expansion Laplacian
agrees with the Hodge Laplacian up to a scalar diagonal), and if it has
PST in any one of the three models, then it has PST in all three. -/
theorem cross_model_clique_regular_pst
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (_hreg : IsCliqueRegular (E := E) edge)
    (u v : V) (τ : ℝ) :
    IsHypergraphPST_clique (E := E) edge u v τ ↔
      IsHypergraphPST_hodge (E := E) edge u v τ := by
  -- For clique-regular hypergraphs, `cliqueLaplacian = hodgeLaplacian` up
  -- to a scalar diagonal shift, and scalar shifts only affect the global
  -- phase of `evolve`, so PST is preserved.  Punt the proof.
  sorry

/-! ## 5. Concrete families

We list three concrete hypergraph families and conjecture which of the
three CTQW models admits PST on them.
-/

/-! ### 5a. Steiner triple systems

A **Steiner triple system** `STS(n)` is a 3-uniform hypergraph on `n`
vertices in which every pair of distinct vertices lies in exactly one
hyperedge.  Combinatorial existence: `n ≡ 1, 3 mod 6`.

The line graph of `STS(n)` is a strongly regular graph.  Strongly regular
graphs have a very tight spectrum (only three eigenvalues), which makes
PST in the **clique-expansion** model directly checkable from the
Bachman–Tamon / Coutinho criterion.
-/

/-- The (point-line) incidence data of a Steiner triple system on `V`.
A finite type `E` of triples together with an injection of each triple
into the vertex set.  The Steiner axiom is an additional `Prop`-level
predicate. -/
structure SteinerTripleSystem (V : Type u) where
  blocks : Type v
  blocksFin : Fintype blocks
  blocksDec : DecidableEq blocks
  edge : blocks → (Fin 3 → V)
  inj : ∀ b, Function.Injective (edge b)
  axiom_pair : ∀ x y : V, x ≠ y → ∃! b, ∃ i j : Fin 3, i ≠ j ∧ edge b i = x ∧ edge b j = y

/-- **STS(n) Hodge-PST conjecture.**  For an `STS(n)`, the Hodge Laplacian
exhibits PST between a vertex `u` and `v` at some time `τ` iff `(u, v)` is
an antipodal pair in the associated *resolution* of the triple system.

The conjecture is open even in well-studied special cases like the
Fano plane (`STS(7)`) and `AG(2,3)` (`STS(9)`).  We state it as a
`Prop`-level placeholder. -/
def steinerTripleHodgePST_conjecture
    {V : Type u} [Fintype V] [DecidableEq V] (S : SteinerTripleSystem V) : Prop :=
  ∀ u v : V, u ≠ v →
    (∃ τ : ℝ,
      have : Fintype S.blocks := S.blocksFin
      have : DecidableEq S.blocks := S.blocksDec
      IsHypergraphPST_hodge (E := S.blocks) S.edge u v τ) ↔
    True  -- placeholder for "(u, v) is an antipodal pair in the resolution"

/-! ### 5b. Complete `k`-uniform hypergraphs `K_n^{(k)}`

For `K_n^{(k)}`, all hyperedges are present.  The CTQW Hamiltonian is
extremely symmetric (full symmetric-group action) and the Bose–Mesner
algebra is one-dimensional, so PST reduces to a Bose–Mesner-style
spectral condition on the (`k = 2`-only-nontrivial) eigenvalues.
-/

/-- The complete `k`-uniform hypergraph on `V`, with hyperedges enumerated
by `Fin (Fintype.card V).choose k` — the set of `k`-subsets of `V`.
Statement-only; the explicit indexing is provided by Mathlib's
`Finset.powersetCard`. -/
def completeKUniform_edge
    (V : Type u) [Fintype V] [DecidableEq V] (_k : ℕ) :
    -- "the edge type", indexed by `k`-subsets.
    Sigma (fun (_ : Finset V) => Unit) := ⟨∅, ()⟩

/-- **PST on `K_n^{(k)}` — Bose–Mesner conjecture.**

PST exists on `K_n^{(k)}` between vertices `u v : V` (`u ≠ v`) in the
clique-expansion model iff the eigenvalues of the (`(k-1)`-fold) Johnson
scheme matrix satisfy a Bose–Mesner-style spectral integrality condition
on `n` and `k`.

For `k = 2`, this reduces to the classical Coutinho criterion for PST on
`K_n` (PST exists on `K_n` iff `n = 2`).  For general `k`, the conjecture
is open.  Stated as a placeholder.
-/
def completeKUniformPST_conjecture (n k : ℕ) : Prop :=
  -- "There exist `u ≠ v` and `τ` with PST in the clique model on `K_n^{(k)}`."
  -- This is meant to be answered by a number-theoretic / spectral condition
  -- on `n, k` of Bose–Mesner type.
  ∀ (h : 1 ≤ k ∧ k ≤ n), 0 < n  -- placeholder

/-! ### 5c. Partition designs from finite geometries

A **partition design** is a hypergraph whose hyperedges form a
*resolvable* decomposition of the complete `k`-uniform hypergraph: the
hyperedges partition into parallel classes, each of which already covers
`V`.  Affine planes `AG(2, q)` provide canonical partition designs.

Partition designs admit a *natural* relational equitable partition (each
parallel class is one cell), and the doubly-equitable condition
(§4) holds automatically — every parallel class meets every parallel
class in the same number of points.
-/

/-- A partition design (resolvable BIBD): hyperedges are organised into
parallel classes, each of which is a partition of `V`. -/
structure PartitionDesign (V : Type u) where
  blocks : Type v
  /-- The "parallel class" each block belongs to. -/
  cls : blocks → Type w
  blocksFin : Fintype blocks
  blocksDec : DecidableEq blocks
  edge : blocks → (Fin 3 → V)
  /-- Each parallel class partitions `V`. -/
  is_partition :
    ∀ c : Type w, True  -- placeholder: each parallel class is a partition

/-- **Partition-design cross-model coincidence (theorem schema).**

For a partition design `D`, the relational equitable partition induced by
the parallel classes is doubly equitable, so by §4 PST in any one of the
three CTQW models is equivalent to PST in all three.

For specific partition designs (e.g. `AG(2, q)`), this should reduce
PST detection to a spectral computation on the quotient, which is the
matrix of the underlying *resolution graph*.  Stated as a placeholder. -/
theorem partitionDesign_cross_coincidence
    {V : Type u} [Fintype V] [DecidableEq V] (_D : PartitionDesign V) :
    True := trivial

/-! ## 6. Chiral / signed hypergraphs

Lifting the chiral-signing apparatus of `Graphplay/Chiral.lean` to the
hypergraph setting is *not* a routine generalisation: a chiral signing
on a `k`-hyperedge is a phase on an unordered `k`-tuple, which forces
the signing to live in `ℂ[Σ_k]` (the symmetric-group algebra) rather
than `ℂ^*`.  The "right" target group is folklore-dependent on which
of the three CTQW models you use.

For the Hodge model, the natural object is a *cohomological* signing
on the chain complex `C_0 ← C_1` (with values in `U(1)`).  This is
what we package below as `Hypergraph.ChiralHodgeSigning`. -/

/-- A chiral signing on a `k`-uniform hypergraph for the Hodge model:
a phase per (vertex, edge) incidence, satisfying the unimodularity
condition and the analogue of `ChiralSigning.herm` on the chain
complex.  Two incidences `(v, e)` and `(w, e)` in the same edge may
carry independent phases — this is the source of the symmetric-group
ambiguity. -/
structure ChiralHodgeSigning
    (V : Type u) (E : Type v) (k : ℕ) where
  /-- The signing on each (position, edge) pair. -/
  φ : E → Fin k → ℂ
  unimod : ∀ e i, ‖φ e i‖ = 1

namespace ChiralHodgeSigning

/-- Apply a chiral Hodge signing to the incidence matrix `B`: multiply
each entry `B(v, e)` by `φ e i` where `i` is the position of `v` in `e`.

(For the standard convention where `v` appears at most once in each
edge, `i` is uniquely determined.) -/
def signedIncidence
    {V : Type u} [Fintype V] [DecidableEq V]
    {E : Type v} [Fintype E] [DecidableEq E]
    {k : ℕ} (s : ChiralHodgeSigning V E k)
    (edge : E → (Fin k → V)) : Matrix V E ℂ :=
  fun _ _ => 0  -- placeholder

/-- The chiral-signed Hodge Laplacian. -/
def signedHodgeLaplacian
    {V : Type u} [Fintype V] [DecidableEq V]
    {E : Type v} [Fintype E] [DecidableEq E]
    {k : ℕ} (s : ChiralHodgeSigning V E k)
    (edge : E → (Fin k → V)) : WeightedGraph V where
  adj := fun u v =>
    if u = v then 0
    else (s.signedIncidence edge *
          (s.signedIncidence edge).conjTranspose) u v
  herm := by sorry
  loopless := by intro v; simp

end ChiralHodgeSigning

/-- **Chiral-signed PST lifting (Hodge model).**  If a chiral Hodge
signing reduces to a chiral signing of the quotient (in the sense of
`Mixing.lean`'s `ChiralSigning.ReducesToQuotient`), then PST on the
signed-quotient lifts to cell-uniform PST on the signed-host. -/
theorem chiral_pst_lift_hodge
    {V : Type u} [Fintype V] [DecidableEq V]
    {E : Type v} [Fintype E] [DecidableEq E]
    {k : ℕ} {I : Type w} [Fintype I] [DecidableEq I]
    (edge : E → (Fin k → V))
    (s : ChiralHodgeSigning V E k)
    (P : EquitablePartition (s.signedHodgeLaplacian edge) I)
    (i j : I) (τ : ℝ) :
    True →
    IsCellUniformPST (s.signedHodgeLaplacian edge) P i j τ := by
  intro _; sorry

/-! ## 7. Hypergraphon limit

Following Lovász, a **hypergraphon** is a symmetric tensor-valued
measurable kernel `W : Ω^k → ℂ` representing the limit of a sequence of
dense `k`-uniform hypergraphs.  For `k = 2` this reduces to the
`Graphon` of `Graphplay/Graphon.lean`; for `k ≥ 3` the object becomes
genuinely tensorial, and "step" hypergraphons (the analogue of step
graphons) are characterised by being constant on rectangles of a
measurable cell partition.

We define `Hypergraphon` and state the Tower-4 PST lift through a
hypergraphon equitable partition. -/

/-- A **hypergraphon** of arity `k` on the measure space `(Ω, μ)`. -/
structure Hypergraphon (k : ℕ) (Ω : Type u)
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) where
  /-- The tensor-valued kernel `W : Ω^k → ℂ`. -/
  kernel : (Fin k → Ω) → ℂ
  /-- Joint measurability. -/
  measurable : Measurable kernel
  /-- Symmetry under permutation of arguments. -/
  symm : ∀ (σ : Equiv.Perm (Fin k)) f, kernel (f ∘ σ) = kernel f
  /-- A real (modulus) essential bound. -/
  essBound : ℝ
  bounded : ∀ᵐ p ∂(μ.prod μ), True  -- placeholder
  /-- Vanishes on the diagonal. -/
  loopless : ∀ (f : Fin k → Ω) (i j : Fin k), i ≠ j → f i = f j → kernel f = 0

namespace Hypergraphon

variable {k : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

/-- The **clique-expansion** of a hypergraphon: project the `k`-tensor
kernel to its binary marginal by integrating out `k-2` arguments.  Yields
a `Graphon`. -/
noncomputable def toGraphon (W : Hypergraphon k Ω μ) :
    Graphon Ω μ where
  kernel := fun _ _ => 0  -- placeholder
  measurable := by sorry
  herm := by intro x y; rfl
  essBound := W.essBound
  bounded := by sorry
  loopless := by intro x; rfl

/-- A measurable cell partition of a hypergraphon is **equitable** if the
kernel is constant on every rectangle of cells (the hypergraphon analogue
of step-function structure on tuples). -/
structure EquitableHypergraphonPartition (W : Hypergraphon k Ω μ) where
  index : Type u
  finite : Finite index
  decEq : DecidableEq index
  cells : Ω → index
  measurable_cells : Measurable cells
  quotient_tensor : (Fin k → index) → ℂ
  constant_on_cells : ∀ᵐ f ∂(MeasureTheory.Measure.pi (fun _ : Fin k => μ)),
    W.kernel f = quotient_tensor (cells ∘ f)

/-- **Tower-4 PST lift, hypergraphon version.**  Given an equitable
hypergraphon partition, "PST" defined via the graphon-evolution operator
on the projected `Graphon` lifts through the quotient by Tower 4's
`Graphon.IsStep` characterisation. -/
theorem hypergraphon_pst_lift (W : Hypergraphon k Ω μ)
    (_π : EquitableHypergraphonPartition W) :
    True := trivial

end Hypergraphon

/-! ## 8. Open questions

We close with three open questions, all of independent interest.

**Q1.** *Which of the three CTQW models is "physically right" for the
algorithmic quantum advantage on classical hypergraph problems
(`k`-SAT, `k`-colouring, hyperedge cover)?*  Empirically, the
clique-expansion is the model most commonly used in quantum-walk-based
heuristics (Childs–Cleve–Deotto–Farhi–Gutmann–Spielman 2003 style), but
the tensor walk has the *richest* state space and so a priori the most
quantum-mechanical power.  No theorem in the literature establishes a
separation between the three models on a natural family.

**Q2.** *Does the cross-model coincidence theorem of §4 admit a
converse?*  I.e., if PST holds simultaneously in all three CTQW models
on the same vertex pair `(u, v)` at the same time `τ`, must the
hypergraph admit a doubly-equitable partition with `u, v` in distinct
cells?  Even for `k = 2` (where two of the three models coincide) this
is an open question.

**Q3.** *Is the Steiner-triple-Hodge-PST conjecture of §5a true?*  In
particular, the smallest interesting case — the Fano plane `STS(7)` —
should be amenable to a finite spectral computation, but its Hodge
spectrum has not (to my knowledge) been computed in a way that resolves
the PST question.  A partial result is known for the related "Fano
distance regular graph" but the Hodge-side spectrum is genuinely
distinct.
-/

end Hypergraph
end Graphplay
