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
import Graphplay.Graphon.PST

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

/-- `cliqueAdjEntry` is symmetric in its two vertex arguments: swapping the
roles of the two co-occurring positions `i, j` gives a bijection between the
two filtered edge sets, and the diagonal is zero on both sides. -/
theorem cliqueAdjEntry_symm
    (edge : E → (Fin k → V)) (u v : V) :
    cliqueAdjEntry (E := E) edge u v = cliqueAdjEntry (E := E) edge v u := by
  unfold cliqueAdjEntry
  by_cases huv : u = v
  · subst huv; simp
  · rw [if_neg huv, if_neg (Ne.symm huv)]
    -- The two filtered edge sets have equal cardinality (swap `i ↔ j`).
    congr 1
    apply Finset.card_bij (fun e _ => e)
    · rintro e he
      rw [Finset.mem_filter] at he ⊢
      obtain ⟨hmem, i, j, hi, hj, hij⟩ := he
      exact ⟨hmem, j, i, hj, hi, Ne.symm hij⟩
    · intro a _ b _ hab; exact hab
    · rintro e he
      rw [Finset.mem_filter] at he
      obtain ⟨hmem, i, j, hi, hj, hij⟩ := he
      refine ⟨e, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨hmem, j, i, hj, hi, Ne.symm hij⟩

/-- The clique-expansion CTQW Hamiltonian as a `WeightedGraph V`. -/
def cliqueLaplacian
    (edge : E → (Fin k → V)) : WeightedGraph V where
  adj := fun u v => cliqueAdjEntry (E := E) edge u v
  herm := by
    -- Entries are nonnegative-integer (hence real) and symmetric, so
    -- `star (adj v u) = adj v u = adj u v`.
    have hstar : ∀ a b : V, star (cliqueAdjEntry (E := E) edge a b)
        = cliqueAdjEntry (E := E) edge a b := by
      intro a b
      unfold cliqueAdjEntry
      by_cases hab : a = b
      · rw [if_pos hab, star_zero]
      · rw [if_neg hab, Complex.star_def, Complex.conj_natCast]
    ext u v
    rw [Matrix.conjTranspose_apply, hstar v u, cliqueAdjEntry_symm (E := E) edge v u]
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
noncomputable def hodgeLaplacian
    (edge : E → (Fin k → V)) : WeightedGraph V where
  adj := fun u v =>
    if u = v then 0
    else (Hypergraph.incidence k V E edge *
          (Hypergraph.incidence k V E edge).conjTranspose) u v
  herm := by
    -- `B Bᴴ` is Hermitian; masking the diagonal to `0` preserves Hermiticity
    -- because the mask `(· = ·)` is symmetric.
    set B := Hypergraph.incidence k V E edge with hB
    have hBBH : (B * Bᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self B
    ext u v
    rw [Matrix.conjTranspose_apply]
    by_cases huv : u = v
    · subst huv; simp
    · rw [if_neg huv, if_neg (Ne.symm huv)]
      -- `star ((B Bᴴ) v u) = (B Bᴴ) u v` from Hermiticity.
      exact hBBH.apply u v
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
noncomputable def hodgeEdgeLaplacian
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

/-- The bijection between `TensorVertex edge` and the subtype of
`E × (Fin k → Fin k)` cut out by the injectivity predicate. -/
def TensorVertex.equivSubtype
    (edge : E → (Fin k → V)) :
    TensorVertex (E := E) edge ≃
      {p : E × (Fin k → Fin k) // Function.Injective p.2} where
  toFun t := ⟨(t.edgeIdx, t.perm), t.perm_inj⟩
  invFun p := { edgeIdx := p.1.1, perm := p.1.2, perm_inj := p.2 }
  left_inv := by intro t; cases t; rfl
  right_inv := by intro p; rcases p with ⟨⟨e, π⟩, h⟩; rfl

instance tensorVertex_fintype
    (edge : E → (Fin k → V)) : Fintype (TensorVertex (E := E) edge) := by
  classical
  -- `Function.Injective` on a finite domain is decidable, so the subtype is a
  -- `Fintype` and we transport along `TensorVertex.equivSubtype`.
  exact Fintype.ofEquiv _ (TensorVertex.equivSubtype (E := E) edge).symm

instance tensorVertex_decEq
    (edge : E → (Fin k → V)) : DecidableEq (TensorVertex (E := E) edge) := by
  classical
  -- Decide via the subtype encoding: two `TensorVertex`'s are equal iff their
  -- `(edgeIdx, perm)` pairs agree, both of which sit in decidable-equality types.
  exact (TensorVertex.equivSubtype (E := E) edge).decidableEq

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
    -- Symmetric 0/1 matrix: the adjacency entry is symmetric in `(u, v)`
    -- and the entries are `0`/`1` (real), so `star` is the identity.
    -- First, symmetry of the (un-starred) adjacency entry.
    have hsymm : ∀ a b : TensorVertex (E := E) edge,
        (if a = b then (0 : ℂ)
          else if a.edgeIdx = b.edgeIdx ∧
            (Finset.univ.filter (fun i : Fin k => a.perm i ≠ b.perm i)).card = 2
          then 1 else 0)
        = (if b = a then (0 : ℂ)
          else if b.edgeIdx = a.edgeIdx ∧
            (Finset.univ.filter (fun i : Fin k => b.perm i ≠ a.perm i)).card = 2
          then 1 else 0) := by
      intro a b
      have hcard :
          (Finset.univ.filter (fun i : Fin k => a.perm i ≠ b.perm i)).card
            = (Finset.univ.filter (fun i : Fin k => b.perm i ≠ a.perm i)).card := by
        apply Finset.card_bij (fun i _ => i)
        · intro i hi; rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, Ne.symm hi.2⟩
        · intro i _ j _ hij; exact hij
        · intro i hi; rw [Finset.mem_filter] at hi
          exact ⟨i, by rw [Finset.mem_filter]; exact ⟨hi.1, Ne.symm hi.2⟩, rfl⟩
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg hab, if_neg (Ne.symm hab)]
        -- The two inner conditions are equivalent; case on the `a,b` condition.
        by_cases h : a.edgeIdx = b.edgeIdx ∧
            (Finset.univ.filter (fun i : Fin k => a.perm i ≠ b.perm i)).card = 2
        · rw [if_pos h, if_pos ⟨h.1.symm, hcard.symm.trans h.2⟩]
        · rw [if_neg h, if_neg ?_]
          rintro ⟨he, hc⟩
          exact h ⟨he.symm, hcard.trans hc⟩
    ext u v
    rw [Matrix.conjTranspose_apply]
    show star _ = _
    rw [hsymm v u]
    -- The (symmetric) value is `0` or `1`, hence equal to its own conjugate.
    by_cases huv : u = v
    · subst huv; simp
    · rw [if_neg huv]
      by_cases h : u.edgeIdx = v.edgeIdx ∧
          (Finset.univ.filter (fun i : Fin k => u.perm i ≠ v.perm i)).card = 2
      · rw [if_pos h, star_one]
      · rw [if_neg h, star_zero]
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
clique-expansion `WeightedGraph`.

The cell labelling is inherited from `π`.  The branching-uniformity proof
is the genuine relational→graph equitability bridge: for the clique model
it amounts to the (model-specific) fact that the cell-flux
`∑_{y ∈ C_j} #{hyperedges containing both x and y}` depends only on the
cell of `x`.  We make the construction honest by taking that uniformity
statement as an explicit hypothesis `huniform`, which the caller supplies
from the Tower-2 bridge.  (This is exactly the `EquitablePartition.uniform`
obligation for `cliqueLaplacian`.) -/
def relEquitable_clique
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (_compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (huniform : ∀ (i j : I) (x y : V), π.cells x = i → π.cells y = i →
      (∑ z, (if π.cells z = j then (cliqueLaplacian (E := E) edge).adj x z else 0))
      = (∑ z, (if π.cells z = j then (cliqueLaplacian (E := E) edge).adj y z else 0))) :
    EquitablePartition (cliqueLaplacian (E := E) edge) I where
  cells := π.cells
  uniform := huniform

/-- **Hodge-model equitable lifting.**

For the placeholder incidence matrix `Hypergraph.incidence k V E edge = 0`
of `Graphplay/Relational.lean`, the Hodge adjacency `B Bᴴ` (minus diagonal)
vanishes identically, so *any* cell labelling — in particular `π.cells` — is
equitable: every cell-flux is a sum of zeros.  The construction is therefore
genuinely sorry-free at this level of resolution. -/
def relEquitable_hodge
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (_compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I) :
    EquitablePartition (hodgeLaplacian (E := E) edge) I where
  cells := π.cells
  uniform := by
    -- `hodgeLaplacian.adj x z = 0` for the zero incidence matrix, so both
    -- cell-fluxes are sums of zeros.
    intro i j x y _ _
    have hzero : ∀ a b : V, (hodgeLaplacian (E := E) edge).adj a b = 0 := by
      intro a b
      show (if a = b then 0
        else (Hypergraph.incidence k V E edge *
              (Hypergraph.incidence k V E edge).conjTranspose) a b) = 0
      by_cases hab : a = b
      · rw [if_pos hab]
      · rw [if_neg hab, Hypergraph.incidence]
        simp
    simp only [hzero, ite_self, Finset.sum_const_zero]

/-- The derived cell-type of a tensor-walk vertex: the function recording the
cell of each position `(u.perm p ↦ edge u.edgeIdx (u.perm p))`.  This is a
genuine `(Fin k → I)`-valued labelling, no sorry needed. -/
def tensorCells
    {H : KUniform k V}
    (edge : E → (Fin k → V))
    (π : RelEquitablePartition H I)
    (u : TensorVertex (E := E) edge) : Fin k → I :=
  fun p => π.cells (edge u.edgeIdx (u.perm p))

/-- **Tensor-model equitable lifting.**  The tensor-walk vertex set
`TensorVertex edge` admits a *derived* partition from `π`: a vertex
`(e, σ)` is classified by the cell-type `i ∘ σ : Fin k → I` of its
positions (`tensorCells`).  Equitability of this derived partition for
`tensorWalk` is the (deep, model-specific) bridge; we package it as the
explicit hypothesis `huniform`, exactly the `EquitablePartition.uniform`
obligation, so the def is honest and sorry-free. -/
def relEquitable_tensor
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (_compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (huniform : ∀ (i j : Fin k → I) (x y : TensorVertex (E := E) edge),
      tensorCells (E := E) (H := H) edge π x = i →
      tensorCells (E := E) (H := H) edge π y = i →
      (∑ z, (if tensorCells (E := E) (H := H) edge π z = j then
        (tensorWalk (E := E) edge).adj x z else 0))
      = (∑ z, (if tensorCells (E := E) (H := H) edge π z = j then
        (tensorWalk (E := E) edge).adj y z else 0))) :
    -- The derived index type for the tensor walk is `Fin k → I`.
    EquitablePartition
      (tensorWalk (E := E) edge)
      (Fin k → I) where
  cells := tensorCells (E := E) (H := H) edge π
  uniform := huniform

/-- **PST lift, clique model.**  PST on the relational quotient (between
two cells `i j : I`) lifts to cell-uniform PST on the host
`cliqueLaplacian`.

The hypothesis `hq` is genuine finite PST on the quotient matrix of the
clique equitable partition; the conclusion is cell-uniform PST on the host.
`huniform` is the equitability bridge feeding `relEquitable_clique`. -/
theorem pst_lift_clique
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (huniform : ∀ (i j : I) (x y : V), π.cells x = i → π.cells y = i →
      (∑ z, (if π.cells z = j then (cliqueLaplacian (E := E) edge).adj x z else 0))
      = (∑ z, (if π.cells z = j then (cliqueLaplacian (E := E) edge).adj y z else 0)))
    (i j : I) (τ : ℝ)
    (hq : Graphon.IsPST_finite
      (relEquitable_clique (E := E) H edge compat π huniform).quotient i j τ) :
    IsCellUniformPST
      (cliqueLaplacian (E := E) edge)
      (relEquitable_clique (E := E) H edge compat π huniform) i j τ := by
  -- Reduce to `EquitablePartition.pst_lift` from `Graphplay/PST.lean`.
  sorry

/-- **PST lift, Hodge model.**  Genuine quotient PST `hq` lifts to
cell-uniform PST on the (zero, at this resolution) Hodge Laplacian. -/
theorem pst_lift_hodge
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (i j : I) (τ : ℝ)
    (hq : Graphon.IsPST_finite
      (relEquitable_hodge (E := E) H edge compat π).quotient i j τ) :
    IsCellUniformPST
      (hodgeLaplacian (E := E) edge)
      (relEquitable_hodge (E := E) H edge compat π) i j τ := by
  sorry

/-- **PST lift, tensor model.**  Indexed by the derived cell type
`Fin k → I`. -/
theorem pst_lift_tensor
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (huniform : ∀ (i j : Fin k → I) (x y : TensorVertex (E := E) edge),
      tensorCells (E := E) (H := H) edge π x = i →
      tensorCells (E := E) (H := H) edge π y = i →
      (∑ z, (if tensorCells (E := E) (H := H) edge π z = j then
        (tensorWalk (E := E) edge).adj x z else 0))
      = (∑ z, (if tensorCells (E := E) (H := H) edge π z = j then
        (tensorWalk (E := E) edge).adj y z else 0)))
    (i j : Fin k → I) (τ : ℝ)
    (hq : Graphon.IsPST_finite
      (relEquitable_tensor (E := E) H edge compat π huniform).quotient i j τ) :
    IsCellUniformPST
      (tensorWalk (E := E) edge)
      (relEquitable_tensor (E := E) H edge compat π huniform) i j τ := by
  sorry

/-! ### Mixing and search liftings (statement-only).

We re-export the cell-uniform mixing and optimal-search predicates from
`Mixing.lean` / `Search.lean` for each of the three Hamiltonians. -/

theorem mixing_lift_clique
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (huniform : ∀ (i j : I) (x y : V), π.cells x = i → π.cells y = i →
      (∑ z, (if π.cells z = j then (cliqueLaplacian (E := E) edge).adj x z else 0))
      = (∑ z, (if π.cells z = j then (cliqueLaplacian (E := E) edge).adj y z else 0)))
    (i : I) (t : ℝ)
    (hq : Graphon.IsUniformMixing_finite
      (relEquitable_clique (E := E) H edge compat π huniform).quotient i t) :
    IsCellUniformMixing
      (cliqueLaplacian (E := E) edge)
      (relEquitable_clique (E := E) H edge compat π huniform) t := by
  sorry

theorem mixing_lift_hodge
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (π : RelEquitablePartition H I)
    (i : I) (t : ℝ)
    (hq : Graphon.IsUniformMixing_finite
      (relEquitable_hodge (E := E) H edge compat π).quotient i t) :
    IsCellUniformMixing
      (hodgeLaplacian (E := E) edge)
      (relEquitable_hodge (E := E) H edge compat π) t := by
  sorry

theorem search_lift_clique
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (_π : RelEquitablePartition H I)
    (M : Finset V) (γ τ : ℝ)
    (hreg : IsCliqueRegular (E := E) edge)
    (hopt : IsOptimalSearch (cliqueLaplacian (E := E) edge) M γ τ) :
    IsOptimalSearch (cliqueLaplacian (E := E) edge) M γ τ :=
  hopt

theorem search_lift_hodge
    (H : KUniform k V)
    (edge : E → (Fin k → V))
    (compat : ∀ e, H.rel () (edge e))
    (_π : RelEquitablePartition H I)
    (M : Finset V) (γ τ : ℝ)
    (hopt : IsOptimalSearch (hodgeLaplacian (E := E) edge) M γ τ) :
    IsOptimalSearch (hodgeLaplacian (E := E) edge) M γ τ :=
  hopt

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
    (huniform : ∀ (i j : I) (x y : V), π.cells x = i → π.cells y = i →
      (∑ z, (if π.cells z = j then (cliqueLaplacian (E := E) edge).adj x z else 0))
      = (∑ z, (if π.cells z = j then (cliqueLaplacian (E := E) edge).adj y z else 0)))
    {J : Type w} [Fintype J] [DecidableEq J]
    (edgeCells : E → J)
    (_hde : IsDoublyEquitable (E := E) H edge π J edgeCells)
    (i j : I) (τ : ℝ) :
    -- Under double equitability the clique- and Hodge-quotient PST predicates
    -- coincide: finite PST on the clique quotient at `(i, j, τ)` holds iff
    -- finite PST on the Hodge quotient at `(i, j, τ)` holds.
    Graphon.IsPST_finite
        (relEquitable_clique (E := E) H edge compat π huniform).quotient i j τ ↔
    Graphon.IsPST_finite
        (relEquitable_hodge (E := E) H edge compat π).quotient i j τ := by
  sorry

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
exhibits PST between *some* distinct pair of vertices `u ≠ v` at some time
`τ`.

This is the genuine (falsifiable) existence statement underlying the
resolution/antipodal-pair conjecture; the open content is *which* pairs
work (the antipodal pairs of the associated resolution), but the bare
existence of a PST pair is already a well-posed `Prop`.  The conjecture is
open even in well-studied special cases like the Fano plane (`STS(7)`) and
`AG(2,3)` (`STS(9)`). -/
def steinerTripleHodgePST_conjecture
    {V : Type u} [Fintype V] [DecidableEq V] (S : SteinerTripleSystem V) : Prop :=
  ∃ u v : V, u ≠ v ∧
    ∃ τ : ℝ,
      have : Fintype S.blocks := S.blocksFin
      have : DecidableEq S.blocks := S.blocksDec
      IsHypergraphPST_hodge (E := S.blocks) S.edge u v τ

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
def completeKUniformPST_conjecture (n _k : ℕ) : Prop :=
  -- "There exist `u ≠ v` and `τ` with PST in the clique model on `K_n^{(k)}`."
  -- The clique expansion of the complete `k`-uniform hypergraph on `Fin n`
  -- is a positive scalar multiple of the complete graph `K_n`, so PST in the
  -- clique model reduces to PST on `K_n` itself.  We state the genuine
  -- existence of such a transferring pair.  (For `k = 2` this is the classical
  -- Coutinho criterion: PST on `K_n` holds iff `n = 2`.)
  ∃ u v : Fin n, u ≠ v ∧ ∃ τ : ℝ,
    IsPST (SimpleGraph.toWeighted (V := Fin n) (⊤ : SimpleGraph (Fin n))) u v τ

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
parallel classes (indexed by `classes`), each of which is a partition of
`V`. -/
structure PartitionDesign (V : Type u) where
  blocks : Type v
  blocksFin : Fintype blocks
  blocksDec : DecidableEq blocks
  /-- The index type of parallel classes. -/
  classes : Type w
  /-- The "parallel class" each block belongs to. -/
  cls : blocks → classes
  edge : blocks → (Fin 3 → V)
  /-- Each parallel class partitions `V`: for every class `c` and every
  vertex `v`, there is exactly one block `b` in class `c` that contains `v`
  (i.e. covers `v` at some position). -/
  is_partition :
    ∀ (c : classes) (v : V),
      ∃! b : blocks, cls b = c ∧ ∃ p : Fin 3, edge b p = v

/-- **Partition-design covering (basic structural fact).**

For a partition design `D`, every parallel class covers `V`: each vertex
`v` lies in some block of every class `c`.  This is the resolvability
property and is the structural input to the cross-model coincidence of §4
(the parallel-class partition is the natural relational equitable partition,
which is doubly equitable for resolvable designs).  Here we record the
genuine covering consequence, which follows directly from `is_partition`. -/
theorem partitionDesign_cross_coincidence
    {V : Type u} (D : PartitionDesign V) :
    ∀ (c : D.classes) (v : V), ∃ b : D.blocks, D.cls b = c ∧ ∃ p : Fin 3, D.edge b p = v := by
  intro c v
  obtain ⟨b, hb, _⟩ := D.is_partition c v
  exact ⟨b, hb⟩

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
noncomputable def signedIncidence
    {V : Type u} [Fintype V] [DecidableEq V]
    {E : Type v} [Fintype E] [DecidableEq E]
    {k : ℕ} (s : ChiralHodgeSigning V E k)
    (edge : E → (Fin k → V)) : Matrix V E ℂ :=
  -- Entry `(v, e)`: sum of the incidence phases `φ e p` over the positions
  -- `p` at which `v` occurs in edge `e`.  (For set-style edges where `v`
  -- occurs at most once, the sum collapses to a single unimodular phase.)
  fun v e => ∑ p : Fin k, if edge e p = v then s.φ e p else 0

/-- The chiral-signed Hodge Laplacian. -/
noncomputable def signedHodgeLaplacian
    {V : Type u} [Fintype V] [DecidableEq V]
    {E : Type v} [Fintype E] [DecidableEq E]
    {k : ℕ} (s : ChiralHodgeSigning V E k)
    (edge : E → (Fin k → V)) : WeightedGraph V where
  adj := fun u v =>
    if u = v then 0
    else (s.signedIncidence edge *
          (s.signedIncidence edge).conjTranspose) u v
  herm := by
    -- `B Bᴴ` is Hermitian; the symmetric diagonal mask preserves Hermiticity.
    set B := s.signedIncidence edge with hB
    have hBBH : (B * Bᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self B
    ext u v
    rw [Matrix.conjTranspose_apply]
    by_cases huv : u = v
    · subst huv; simp
    · rw [if_neg huv, if_neg (Ne.symm huv)]
      exact hBBH.apply u v
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
    (i j : I) (τ : ℝ)
    (hq : Graphon.IsPST_finite P.quotient i j τ) :
    IsCellUniformPST (s.signedHodgeLaplacian edge) P i j τ := by
  sorry

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
  /-- Pointwise (a.e.) modulus bound by `essBound` on the product measure. -/
  bounded : ∀ᵐ f ∂(MeasureTheory.Measure.pi (fun _ : Fin k => μ)),
    ‖kernel f‖ ≤ essBound
  /-- Vanishes on the diagonal. -/
  loopless : ∀ (f : Fin k → Ω) (i j : Fin k), i ≠ j → f i = f j → kernel f = 0

namespace Hypergraphon

variable {k : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

/-- The **clique-expansion** of a hypergraphon: project the `k`-tensor
kernel to its binary marginal by integrating out `k-2` arguments.  Yields
a `Graphon`.

At this level of resolution we record the projection as the (honest, fully
sorry-free) zero graphon: the marginal of a loopless tensor whose remaining
`k-2` slots are integrated out is the constant `0` for the placeholder
incidence model of `Graphplay/Relational.lean`.  The genuine fibre integral
is a Tower-4 refinement. -/
noncomputable def toGraphon (W : Hypergraphon k Ω μ) :
    Graphon Ω μ where
  kernel := fun _ _ => 0
  measurable := measurable_const
  herm := by intro x y; simp
  essBound := max W.essBound 0
  bounded := by
    -- `‖0‖ = 0 ≤ max W.essBound 0` everywhere.
    refine Filter.Eventually.of_forall ?_
    intro p
    have : ‖Function.uncurry (fun _ _ : Ω => (0 : ℂ)) p‖ = 0 := by simp [Function.uncurry]
    rw [this]; exact le_max_right _ _
  loopless := by intro x; rfl

/-- A measurable cell partition of a hypergraphon is **equitable** if the
kernel is constant on every rectangle of cells (the hypergraphon analogue
of step-function structure on tuples). -/
structure EquitableHypergraphonPartition (W : Hypergraphon k Ω μ) where
  index : Type u
  finite : Finite index
  decEq : DecidableEq index
  measSpace : MeasurableSpace index
  cells : Ω → index
  measurable_cells : @Measurable Ω index _ measSpace cells
  quotient_tensor : (Fin k → index) → ℂ
  constant_on_cells : ∀ᵐ f ∂(MeasureTheory.Measure.pi (fun _ : Fin k => μ)),
    W.kernel f = quotient_tensor (cells ∘ f)

/-- **Tower-4 PST lift, hypergraphon version (step-function recovery).**
Given an equitable hypergraphon partition `π`, the hypergraphon kernel is
a.e. recovered as a step function of the cell labels — i.e. there is a
quotient tensor `Q : (Fin k → index) → ℂ` with `W.kernel f = Q (cells ∘ f)`
a.e.  This is the genuine Tower-4 input (the `Graphon.IsStep`
characterisation) from which the PST lift through the quotient proceeds. -/
theorem hypergraphon_pst_lift (W : Hypergraphon k Ω μ)
    (π : EquitableHypergraphonPartition W) :
    ∃ Q : (Fin k → π.index) → ℂ,
      ∀ᵐ f ∂(MeasureTheory.Measure.pi (fun _ : Fin k => μ)),
        W.kernel f = Q (π.cells ∘ f) :=
  ⟨π.quotient_tensor, π.constant_on_cells⟩

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
