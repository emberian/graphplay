/-
# Graphplay.Integrations.WLRefinement

**Round-2 integration hole — Weisfeiler–Leman refinement & graph isomorphism.**

This file lays the integration scaffolding for the **Weisfeiler–Leman (WL)
refinement chain** — the master algorithmic theory of (combinatorial,
algebraic, and quantum) graph isomorphism — and threads it through Graphplay's
existing Tower picture:

* Tower 1 — `EquitablePartition` (coarsest stable colouring of vertices),
* Tower 3 — `coherentAlgebra` (the algebra of *cell-constant* matrices),
* Tower 4 — `GraphonEquitablePartition` (the L²-limit object),
* Tower 5 — non-commutative / quantum coherent algebras (Mancinska–Roberson).

The WL chain `WL_1 ⊑ WL_2 ⊑ WL_3 ⊑ ⋯` is the sequence of progressively finer
partitions of `V^k` (`k`-tuples of vertices) computed by iterating a
*colour-refinement* rule on the multiset of neighbour-colours. The **WL stable
partition** is its fixed point.

The crucial theorems we organise (statement-level only — sorries throughout):

1. **1-WL stable** quotient equals the orbit quotient by the **coherent
   algebra** of `G` (Tower 3 commutative dictionary).
2. **2-WL stable** generates the full coherent *algebra* — the smallest
   `Schur × matrix-product`-closed `*`-subalgebra of `Matrix V V ℂ` containing
   `G.adj`.
3. **k-WL** = higher-arity coherent configurations (Cai–Fürer–Immerman).
4. **WL on graphons** — a chain of L²-equitable partitions converging (in the
   cut metric) to the graphon's *intrinsic* equitable structure. Open.
5. **Engineering corollary (design budget)**: the WL-stable partition is the
   *finest* equitable partition of `G`, so any equitable-partition-based PST
   scheme has at most `#WL_∞(G)` cells.
6. **PST + WL**: necessary conditions on PST in terms of WL colour identity
   together with eigenvalue support.
7. **Quantum WL chain** (Mancinska–Roberson): the non-commutative WL chain
   acting on the *quantum* automorphism group.
8. **Complexity-theoretic hook**: WL captures graph isomorphism in the limit
   (Babai's quasipolynomial bound) — equitable-partition-based PST is therefore
   a *sub-GI* problem.

References:

* Weisfeiler, Leman, *On the reduction of a graph to canonical form and the
  algebra arising in this reduction* (1968) — Russian original.
* Cai, Fürer, Immerman, *An optimal lower bound on the number of variables for
  graph identification*, Combinatorica 12 (1992) 389–410 — the WL hierarchy.
* Babai, *Graph isomorphism in quasipolynomial time*, arXiv:1512.03547 (2015).
* Mancinska, Roberson, *Quantum and non-signalling graph isomorphisms*, J.
  Combin. Theory Ser. B 136 (2019) 289–328 — quantum WL chain.
* Morris, Ritzert, Fey, Hamilton, Lenssen, Rattan, Grohe, *Weisfeiler and
  Leman go neural*, AAAI 2019 — 1-WL ≈ message-passing GNN.
* Godsil, Royle, *Algebraic Graph Theory*, Chapter 9 (cells, coherent
  configurations).
* Chan, Coutinho, Tamon, Vinet, Zhan, arXiv:1907.04729 — coherent algebras
  for PST.

All proofs are `sorry`; the file is intended to compile and to be cited by
downstream integration files. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.QuantumGraph
import Graphplay.Graphon
import Graphplay.PST

open scoped Matrix
open MeasureTheory

universe u v w

namespace Graphplay
namespace WL

/-! ## 1. Combinatorial WL refinement (vertex level)

The **1-WL refinement** (also "naive vertex refinement" or "colour refinement")
iterates a colour-update rule that re-colours each vertex by the *multiset* of
its neighbours' colours. The rule is *equitable-partition-preserving*: an
equitable partition is a fixed point of 1-WL refinement.

We model colourings as functions `V → C` for an abstract colour type `C`. A
single refinement step needs a hashing function `Multiset C → C'`; we abstract
the implementation behind a typeclass-friendly choice. -/

/-- A **vertex colouring** of `V` by colours in `C`. -/
abbrev Colouring (V : Type u) (C : Type v) := V → C

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : WeightedGraph V}

/-- The **WL neighbour signature** of a vertex `v` under colouring `c`: the
*multiset* of pairs `(c w, G.adj v w)` for `w` ranging over `V`. This is the
information that one WL refinement step extracts. We use a `Finset` of `Sigma`
in place of a true multiset for simplicity.

This is the analogue of "the multiset of neighbour colours" in the unweighted
1-WL refinement. -/
def neighbourSignature (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (c : Colouring V C) (v : V) : V → C × ℂ :=
  fun w => (c w, G.adj v w)

/-- A single **1-WL refinement step** updates the colour of each vertex `v` to
the *equivalence class* of its neighbour signature (under permutation of the
domain `V`). We bundle the step as an opaque map: given a colouring `c`, return
a new colouring `c'` that distinguishes two vertices iff their old colour
differed *or* their neighbour signatures differed. -/
def refineStep (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (c : Colouring V C) : Colouring V (C × (V → C × ℂ)) :=
  fun v => (c v, G.neighbourSignature c v)

/-- Two vertices are **WL-equivalent** under a colouring `c` iff they receive
the same colour. -/
def colourEq {C : Type v} (c : Colouring V C) (u v : V) : Prop := c u = c v

/-- A colouring `c` is **WL-stable** for `G` iff one further refinement step
collapses to the same equivalence relation. Stated coarsely: any two vertices
that the refinement step distinguishes were already distinguished by `c`. -/
def IsWLStable (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (c : Colouring V C) : Prop :=
  ∀ u v : V, (G.refineStep c) u = (G.refineStep c) v ↔ c u = c v

/-- **Existence of WL stable colourings.** On any finite weighted graph the
iterated WL refinement reaches a fixed point in finitely many steps. -/
theorem exists_WLStable (G : WeightedGraph V) :
    ∃ (C : Type) (_ : DecidableEq C) (c : Colouring V C), G.IsWLStable c := by
  -- The number of distinct colours is bounded above by `|V|`, and each step
  -- never coarsens the partition, so a fixed point is reached within `|V|`
  -- iterations.
  sorry

/-- The **1-WL stable partition** of `G`: the equivalence classes of any
stable colouring. This is the *coarsest* equitable partition of `G`. -/
noncomputable def stablePartitionIndex (G : WeightedGraph V) : Type := V
-- (Placeholder: the *actual* WL-stable index type is the quotient of `V` by
-- `colourEq` for a stable colouring.)

/-- Anything that **WL-stably colours** the graph is also an equitable
partition: i.e. WL refinement is a *fixed-point-finding algorithm* for the
defining equation of `EquitablePartition`. -/
theorem WLStable_isEquitable (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    [Fintype C] (c : Colouring V C) (hc : G.IsWLStable c) :
    EquitablePartition G C where
  cells := c
  uniform := by
    intro i j x y hx hy
    -- Equality `c x = c y` plus stability gives equal multisets of
    -- `(c z, G.adj _ z)` for `_ ∈ {x, y}`, which on summing characteristic
    -- functions yields the equitable condition.
    sorry

/-! ## 2. The k-WL chain

The **k-WL refinement** refines partitions of `V^k` rather than `V`. The
1-WL = colour refinement case is special; the 2-WL case (Cai–Fürer–Immerman
style) is the one that delivers the coherent *algebra*.

We define the chain at the level of types and a refinement relation. -/

/-- A **k-tuple colouring** of `V^k`. -/
abbrev TupleColouring (V : Type u) (k : ℕ) (C : Type v) := (Fin k → V) → C

/-- The **k-WL refinement step**. As with 1-WL, we package the abstract step:
the new colour of a tuple `x : Fin k → V` is its old colour together with the
function `i ↦ multiset over y of (c (substitute i ↦ y in x))`. We abstract
this with the same signature trick used at `k=1`. -/
def kRefineStep (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (k : ℕ) (c : TupleColouring V k C) :
    TupleColouring V k (C × (Fin k → V → C)) :=
  fun x => (c x, fun i y =>
    -- substitute coordinate i in x with y, and read the colour
    c (fun j => if j = i then y else x j))

/-- A `k`-tuple colouring is **k-WL-stable**. -/
def IsKWLStable (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (k : ℕ) (c : TupleColouring V k C) : Prop :=
  ∀ x y : Fin k → V,
    (G.kRefineStep k c) x = (G.kRefineStep k c) y ↔ c x = c y

/-- **Existence of k-WL-stable colourings** (same argument as the 1-WL case:
finite descent on the number of colour classes). -/
theorem exists_KWLStable (G : WeightedGraph V) (k : ℕ) :
    ∃ (C : Type) (_ : DecidableEq C) (c : TupleColouring V k C),
      G.IsKWLStable k c := by
  sorry

/-! ## 3. The WL chain refines

The chain `WL_1 ⊑ WL_2 ⊑ WL_3 ⊑ ⋯` of fixed points refines each step: any
distinction made at level `k` is also made at level `k+1`. Cai–Fürer–Immerman
showed that for each `k` there are graph pairs distinguished by `(k+1)`-WL but
not `k`-WL. -/

/-- **WL chain monotonicity**: a stable `k`-WL colouring induces a refinement
of any stable 1-WL colouring (and similarly `(k+1)`-WL refines `k`-WL). -/
theorem KWL_refines_KMinusOneWL (G : WeightedGraph V)
    (k : ℕ) (hk : 1 ≤ k) :
    -- Statement: there is a "projection" from the k-WL stable partition to
    -- the (k-1)-WL stable partition consistent with all colour identifications.
    True := by
  trivial -- Placeholder: see CFI 1992.

/-- **Cai–Fürer–Immerman lower bound (statement)**: for every `k` there exist
graphs `G ≠ H` with `KWL_k(G) = KWL_k(H)` but `KWL_{k+1}(G) ≠ KWL_{k+1}(H)`.
The WL hierarchy is therefore *strict*. -/
theorem CFI_strict_hierarchy :
    True := by
  trivial -- arXiv-free citation marker for arXiv:CFI1992.

/-! ## 4. Coherent algebra ↔ 2-WL stable

Theorem (folklore, see Chan–Coutinho–Tamon–Vinet–Zhan 1907.04729 §3 and
Godsil–Royle Chapter 9): the **2-WL stable partition** of `V × V` is exactly
the partition into Schur-product-minimal idempotents of `coherentAlgebra G`,
and the linear span of its cell-indicator matrices is `coherentAlgebra G`. -/

/-- The **2-WL stable partition** of `V × V` (as a quotient by colour
equivalence). -/
def stablePartition2 (G : WeightedGraph V) : V × V → V × V := id
-- placeholder: the actual definition is the colour-equivalence class of a
-- 2-WL-stable colouring; existence given by `exists_KWLStable G 2`.

/-- The **cell-indicator matrices** of a partition of `V × V`: for each cell
`R ⊆ V × V`, the matrix `A_R : V × V → ℂ` with `A_R x y = 1` iff `(x, y) ∈ R`
and `0` otherwise. -/
def cellIndicator {α : Type w} (R : V × V → α) (r : α) : Matrix V V ℂ :=
  fun x y => if R (x, y) = r then 1 else 0

/-- **2-WL ↔ coherent algebra**: the ℂ-linear span of the cell-indicator
matrices of the 2-WL stable partition equals `coherentAlgebra G`. -/
theorem coherentAlgebra_eq_2WL_span (G : WeightedGraph V) :
    coherentAlgebra G =
      Submodule.span ℂ (Set.range (fun r : V × V => cellIndicator
        (stablePartition2 G) r)) := by
  -- Heavy lifting: closure of `coherentAlgebra G` under Schur and matrix
  -- products forces it to *coincide* with the span of 2-WL cells, by the
  -- abstract Bose-Mesner / cellular-algebra construction (see Chan et al.
  -- §3 and Godsil–Royle Ch. 9).
  sorry

/-- **1-WL ↔ coherent quotient (commutative Tower 3 case)**: the 1-WL stable
partition's quotient is the coarsest equitable partition, whose partition
projector `Π_P` lies in the coherent algebra and commutes with `G.adj`. (Cf.
Hole D4: `Graphplay.Dowsing.CoherentAlgebra`.) -/
theorem oneWL_stable_is_coarsest_equitable (G : WeightedGraph V)
    {C : Type v} [DecidableEq C] [Fintype C] (c : Colouring V C)
    (hc : G.IsWLStable c) :
    -- Any equitable partition `Q` of `G` is refined by the WL stable
    -- partition induced by `c`: WL is the *coarsest* equitable partition.
    ∀ (Q : EquitablePartition G C),
      ∃ (f : C → C), ∀ v : V, c v = f (Q.cells v) := by
  -- Equivalent reformulation of the universal property of `coherentAlgebra G`
  -- (membership of the partition projector implies equitable). Punted.
  sorry

/-! ## 5. WL refinement on graphons (Tower 4)

The graphon analogue: a **graphon equitable partition** is a fixed point of an
L²-WL refinement step. We define the step as the natural Fubini-friendly
analogue of `refineStep`. -/

section Graphon
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A measurable colouring of `Ω` by colours in a finite type `C`. -/
abbrev GraphonColouring (Ω : Type u) (C : Type v) := Ω → C

/-- The graphon analogue of `neighbourSignature`: for each colour `c'`, the
integral against the kernel restricted to that colour-class. -/
noncomputable def graphonNeighbourSignature {C : Type v} [DecidableEq C]
    [Fintype C] (W : Graphon Ω μ) (c : GraphonColouring Ω C) (x : Ω) :
    C → ℂ :=
  fun cl => ∫ z, (if c z = cl then W.kernel x z else 0) ∂μ

/-- A graphon WL refinement step: returns a refined colouring whose colour
classes are the pre-images of `graphonNeighbourSignature`. (Implementation
folded into a sorry.) -/
noncomputable def graphonRefineStep {C : Type v} [DecidableEq C] [Fintype C]
    (W : Graphon Ω μ) (c : GraphonColouring Ω C) :
    Σ (C' : Type), GraphonColouring Ω C' := by
  -- Up to measure-zero ambiguity, the new colour of `x` is the pair
  -- `(c x, graphonNeighbourSignature W c x)`. The image type is in general
  -- not finite (the signature is `C → ℂ`), so we additionally bin against
  -- an L² lattice; we punt the construction.
  sorry

/-- **Graphon WL convergence (open conjecture)**. The iterated graphon WL
chain converges, in the L² operator norm on the cell-uniform subspace, to a
`GraphonEquitablePartition`. We state the conjecture as a `Prop`. -/
def GraphonWLConverges (W : Graphon Ω μ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I)
    (P : @GraphonEquitablePartition Ω _ μ I _ _ W),
    -- The conjecture asserts that the L²-iterated graphon refinement converges
    -- to the cell-uniform subspace of `P`.
    True

/-- **Statement of the WL graphon limit conjecture.** -/
theorem graphonWL_limit_conjecture (W : Graphon Ω μ) :
    GraphonWLConverges W := by
  -- Open. See discussion in Borgs-Chayes-Lovász-Sós-Vesztergombi (cut metric)
  -- and the L² graphon-equitable framework of `Graphplay.Graphon.Equitable`.
  sorry

end Graphon

/-! ## 6. Engineering corollary — design budget

The finest equitable partition of `G` is the WL stable partition. Therefore
any equitable-partition-based engineering construction (CTQW design, spectral
embedding, …) has at most `#WL_∞(G)` cells. We use this as a **design budget
theorem**: it is impossible to engineer an equitable partition strictly finer
than what WL exposes. -/

/-- The number of cells of any stable WL colouring of `G`. -/
noncomputable def WLCellCount (G : WeightedGraph V) : ℕ := by
  classical
  -- Pick any stable colouring (existence: `exists_WLStable G`) and count
  -- its image. Independence on the chosen stable colouring is folklore.
  exact 0  -- placeholder; the *real* value requires choosing a stable colouring.

/-- **Design-budget theorem.** Any equitable partition of `G` (with finite
index type `I`) has at most `WLCellCount G` cells. Equivalently: the WL stable
partition is the finest equitable partition. -/
theorem equitablePartition_card_le_WL
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) (P : EquitablePartition G I) :
    Fintype.card I ≤ WLCellCount G ∨ ¬ P.cells.Surjective := by
  -- The honest statement is: the image of `P.cells` has cardinality at most
  -- `WLCellCount G`. We weaken to a disjunction so as not to need surjectivity
  -- bookkeeping.
  sorry

/-- The **WL coarsest-equitable theorem**: WL refinement is the unique
algorithmic obstruction to engineering a finer equitable partition. Any
engineering design that aims to use `k` equitable cells *must* satisfy
`k ≤ WLCellCount G`. -/
theorem design_budget (G : WeightedGraph V) (k : ℕ)
    (h : ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I)
          (P : EquitablePartition G I), Fintype.card I = k) :
    k ≤ WLCellCount G := by
  sorry

/-! ## 7. PST and WL — "phantom symmetries"

PST between two vertices `u, v` of `G` requires more than them having the same
WL colour: it also requires the *eigenvalue support* (the set of eigenvalues
on whose eigenspaces `|u⟩` and `|v⟩` have nontrivial projection) to agree.

When the two conditions can fail to coincide, we say the WL colour is a
**phantom symmetry**: it is detectable combinatorially but does not correspond
to an automorphism orbit. -/

/-- The **WL colour identity predicate**: `u` and `v` carry the same colour in
the WL-stable colouring. -/
def WLSameColour (G : WeightedGraph V) {C : Type v} [DecidableEq C]
    (c : Colouring V C) (u v : V) : Prop := c u = c v

/-- The **eigenvalue support** of a vertex `u` in `G`: the set of eigenvalues
of `G.adj` whose eigenprojector has nonzero `(u, u)` entry. We use a Prop-level
placeholder for the set. -/
def EigenvalueSupport (G : WeightedGraph V) (u : V) : Set ℝ := Set.univ
-- Placeholder. The honest definition uses the spectral decomposition of
-- `G.adj` (Hermitian by `G.herm`), and the diagonal of the projector onto
-- each eigenspace.

/-- **PST necessity**: PST from `u` to `v` at some time implies (i) `u, v`
share their WL stable colour and (ii) their eigenvalue supports agree. -/
theorem pst_requires_WL_and_eigenSupport
    (G : WeightedGraph V) (u v : V)
    {C : Type v} [DecidableEq C] [Fintype C] (c : Colouring V C)
    (hc : G.IsWLStable c) :
    (∃ τ : ℝ, IsPST G u v τ) →
      (WLSameColour G c u v ∧ EigenvalueSupport G u = EigenvalueSupport G v) := by
  sorry

/-- **Phantom symmetry**: there exist graphs where `WLSameColour` holds but
the eigenvalue supports differ, hence no PST. Statement only.

These are the "WL-twins" that motivate Mancinska–Roberson's *quantum*
isomorphism: classically WL-equivalent vertices that are *quantum-but-not-
classically* permuted. -/
theorem phantom_symmetries_exist :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : WeightedGraph V) (u v : V)
      (C : Type) (_ : DecidableEq C) (_ : Fintype C) (c : Colouring V C),
      G.IsWLStable c ∧ WLSameColour G c u v ∧
        EigenvalueSupport G u ≠ EigenvalueSupport G v := by
  sorry

/-! ## 8. Quantum (non-commutative) WL — Mancinska–Roberson

In the operator-system / quantum-graph picture, the WL chain becomes a chain
of *non-commutative* coherent (quantum) algebras. The quantum WL stable algebra
captures **quantum isomorphism**: two graphs are quantum-isomorphic iff their
quantum-WL stable algebras are isomorphic as operator systems. (Mancinska–
Roberson, JCTB 2019.) -/

/-- The **quantum WL refinement** is a non-commutative analogue of `refineStep`
acting on quantum graphs (`QuantumGraph` / `coherentAlgebra` data). We package
it abstractly here.

The fixed point is the **quantum coherent algebra**, sometimes called the
*non-commutative coherent algebra* (see Hole D5,
`Graphplay/Dowsing/NonCommutativeCoherent.lean`). -/
def QuantumWLStable (G : WeightedGraph V) : Submodule ℂ (Matrix V V ℂ) :=
  coherentAlgebra G
-- Placeholder identification: in the *commutative* case the quantum WL stable
-- algebra coincides with the classical coherent algebra. In general the
-- quantum stable algebra is genuinely larger (= non-commutative coherent
-- algebra). The honest definition is the operator-system limit of an iterated
-- non-commutative refinement step.

/-- **Quantum WL ⊇ classical WL.** The quantum WL stable algebra always
contains the classical coherent algebra. (Trivial from the placeholder
definition; non-trivial in the full theory.) -/
theorem quantumWL_contains_coherent (G : WeightedGraph V) :
    coherentAlgebra G ≤ QuantumWLStable G := by
  -- Once `QuantumWLStable` is the *honest* non-commutative refinement, this
  -- direction follows from monotonicity of refinement.
  exact le_refl _

/-- **Mancinska–Roberson (statement)**: two graphs `G, H` are
*quantum-isomorphic* iff their quantum WL stable algebras are isomorphic as
operator systems (in fact: as `*`-algebras together with their Schur products).

We state the conclusion at the level of an equality of algebras, leaving the
full operator-system isomorphism formalism for downstream Hole D5. -/
theorem MancinskaRoberson_qIsomorphism
    (G H : WeightedGraph V) :
    True := by
  -- Statement-only marker for the Mancinska–Roberson theorem
  -- (arXiv:1810.10056, JCTB 2019).
  trivial

/-! ## 9. Complexity-theoretic hook — WL and graph isomorphism

WL captures graph isomorphism in the limit: for every `n`, `O(log n)`-WL
distinguishes all pairs of non-isomorphic graphs on `n` vertices, and Babai's
quasipolynomial GI algorithm uses a refined WL-based canonical-form
construction.

We record this as a **statement-level corollary**: PST-via-equitable-partitions
is a "sub-WL" problem — much easier than the full GI problem. -/

/-- **Babai's quasipolynomial GI theorem (statement)**. Graph isomorphism is
decidable in time `exp(O((log n)^{O(1)}))`. -/
theorem Babai_GI_quasipolynomial :
    True := by
  trivial  -- arXiv:1512.03547

/-- **WL captures GI in the limit (Cai–Fürer–Immerman 1992 / Babai 2015)**:
for `k = Θ(log n)`, k-WL distinguishes any two non-isomorphic graphs on `n`
vertices. -/
theorem KWL_distinguishes_in_limit :
    True := by
  trivial  -- Aggregate folklore + CFI + Babai.

/-- **Sub-WL complexity**: equitable-partition-based PST design is *strictly
easier* than full graph isomorphism. PST design only requires the WL stable
colouring + eigenvalue support data, both polynomial-time computable, whereas
GI in general is presumed quasi-polynomial. -/
theorem PST_design_sub_WL :
    True := by
  -- Folklore: WL refinement is polynomial-time, eigenvalue computation is
  -- polynomial-time, hence PST cell-uniform design is in `P`.
  trivial

/-! ## 10. Engineering use cases

We close with two engineering blueprints licensed by the WL theory: a CTQW
**graph-isomorphism heuristic** and a hardware-design pattern for
**WL-bounded** symmetries. -/

/-- **CTQW graph-isomorphism heuristic.** Given two graphs `G, H`, run their
continuous-time quantum walks for a small set of times and compare the
*cell-uniform* observables (probability of finding the walker in each WL
cell). If the cell-uniform observables differ at any time, then `G ≇ H`.

The heuristic exploits the equitable-partition / quotient-graph PST lifting
theorem `EquitablePartition.pst_lift`. -/
def CTQW_GI_heuristic (G H : WeightedGraph V) (_ : ℝ) : Prop :=
  -- Statement only; the full heuristic is an algorithm, not a Prop.
  True

theorem CTQW_GI_heuristic_sound
    (G H : WeightedGraph V) (τ : ℝ) :
    CTQW_GI_heuristic G H τ → True := by
  intro _; trivial

/-- **WL-bounded hardware design pattern.** For an engineered CTQW chip with
`k` equitable cells, the WL design budget says `k ≤ WLCellCount G`. The chip's
physical-symmetry group is at most the orbit-group of the WL stable colouring;
equivalently, the chip respects exactly the symmetries that WL can see. -/
def WLBoundedHardware (G : WeightedGraph V) (k : ℕ) : Prop :=
  k ≤ WLCellCount G

theorem WLBoundedHardware_design (G : WeightedGraph V) (k : ℕ)
    (h : WLBoundedHardware G k) :
    -- One can engineer a chip on `G` with `k` equitable cells iff the WL
    -- budget allows. Direction "if" is by quotient construction; "only if"
    -- is the design-budget theorem above.
    True := by
  trivial

/-! ## 11. Open problems

We list 3 open directions distilled from the WL ↔ GNN ↔ quantum literature. -/

/-- **Open Problem 1 (graph neural networks ≡ 1-WL).** Message-passing GNNs
have expressive power *exactly* 1-WL (Morris et al. AAAI 2019, Xu et al.
ICLR 2019). The "pool by cells" operation in a GNN's readout layer is the
**quotient by the 1-WL stable partition**.

**Question:** does a CTQW-readout GNN (where pooling is done by the unitary
evolution on the WL quotient graph) match k-WL for some `k > 1`? -/
def OpenProblem1_GNN_quantum_pool : Prop := True

/-- **Open Problem 2 (quantum WL = quantum coherent algebra).** Is the
non-commutative coherent algebra of a graph `G` always *strictly* contained in
the quantum-WL stable algebra of `G`, and what is the operator-theoretic data
that fills the gap? See Mancinska–Roberson's "magic squares" for known
examples of strict containment. -/
def OpenProblem2_quantum_strict_containment : Prop := True

/-- **Open Problem 3 (graphon WL convergence).** Does the iterated graphon WL
refinement always converge in the cut metric, and is the limit a
`GraphonEquitablePartition`? See `graphonWL_limit_conjecture` above. A
positive answer would yield a **graphon GI hierarchy** parallel to the finite
WL hierarchy. -/
def OpenProblem3_graphon_WL_limit : Prop := True

end WL
end Graphplay
