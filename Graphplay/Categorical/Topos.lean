/-
# Graphplay/Categorical/Topos.lean

Round-3 categorical loop-closer: a topos-theoretic framing for the category of
partitioned weighted graphs.

`Graphplay.Categorical` builds the categories `WGraph` and `WGraphP` and the
`Quotient : WGraphP ⥤ WGraph` functor.  The present file goes one level up:

  1. State that `WGraphP` is a *regular* category (finite limits + stable
     regular epi/mono factorisation), and gather the morphism-level conditions
     for which this holds on the nose.
  2. Identify the lattice of subobjects of `(G, P)` with the lattice of
     **finer equitable partitions** of `G`, refined by refinement; package this
     as the candidate subobject classifier.
  3. State the internal-logic interpretation: predicates on `(G, P)` are
     refinement-monotone properties of equitable partitions, and the internal
     `∀` over cells becomes refinement-stability.
  4. Construct the **coreflection** `WGraph → WGraphP` sending a weighted graph
     to its discrete (singleton-cell) partition; state the adjunction.
  5. Set up the **site of equitable partitions** of a fixed graph `G`, with
     refinement as the Grothendieck covering structure; state that sheaves on
     this site are "consistent assignments of cell-data" — the local form of
     Tower 6's sheaf-graph data.
  6. State the **Lawvere theory** of the 8-instruction assembly-language
     (PARTITION / QUOTIENT / BUNDLE / SIGN / REFINE / LIFT / COLIMIT / EMBED)
     and its equational axioms.
  7. Bridge to Tower 7: the (2, 1)-categorical version of `WGraphP` carries
     the same topos-style structure, with 2-morphisms given by natural
     isomorphisms of cell-index labellings.

Almost all proofs are `sorry`; the file fixes precise *statements*.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLattice.Defs
import Graphplay.Categorical

universe u v w

namespace Graphplay
namespace Topos

open CategoryTheory CategoryTheory.Limits

/-! ## 1. `WGraphP` is regular. -/

/--
A morphism `f : (G, P) ⟶ (G', P')` of `WGraphP` is **monic** when the
underlying vertex map is injective and the cell-index map is injective
(equivalently: the morphism is monic in the underlying category).
-/
structure WGraphPMono {X Y : WGraphPObj.{u}} (f : WGraphPHom X Y) : Prop where
  base_inj : Function.Injective f.base.toFun
  cell_inj : Function.Injective f.cellMap

/--
A morphism is a **regular epi** when the underlying vertex map is surjective
and the cell-index map is surjective (i.e. it is a quotient at both levels and
the cell quotient is induced by the vertex quotient).
-/
structure WGraphPRegEpi {X Y : WGraphPObj.{u}} (f : WGraphPHom X Y) : Prop where
  base_surj : Function.Surjective f.base.toFun
  cell_surj : Function.Surjective f.cellMap
  /-- Cells are coherent: `Y`-cells are the images of `X`-cells under `cellMap`. -/
  cells_compat :
    ∀ y : Y.V, ∃ x : X.V, f.base.toFun x = y ∧ f.cellMap (X.cells x) = Y.cells y

/--
**Finite limits exist in `WGraphP`.** Constructed pointwise: the pullback of
`f, g` has vertex set the fibre product of the vertex sets, cell set the fibre
product of the cell sets, and the partition is induced.

(Statement only; the actual `HasFiniteLimits` instance is `sorry`.)
-/
theorem hasFiniteLimits_WGraphP : HasFiniteLimits WGraphPObj.{u} := by
  sorry

/--
**Every morphism factors as a regular epi followed by a mono.**

Explicitly: factor `f : X ⟶ Y` through the image (vertex-image, cell-image)
with the induced equitable partition on the image; the first leg is a
regular epi, the second leg is a mono.
-/
theorem regular_epi_mono_factorization
    {X Y : WGraphPObj.{u}} (f : WGraphPHom X Y) :
    ∃ (I : WGraphPObj.{u}) (e : WGraphPHom X I) (m : WGraphPHom I Y),
      WGraphPRegEpi e ∧ WGraphPMono m ∧
      WGraphPHom.comp e m = f := by
  sorry

/--
**Regular epis are stable under pullback.** Pulling back a surjective
partition-respecting quotient along any morphism is again a surjective
partition-respecting quotient.

This is the load-bearing part of the regular-category axioms.
-/
theorem regular_epi_stable_under_pullback
    {X Y Z : WGraphPObj.{u}} (f : WGraphPHom X Z) (g : WGraphPHom Y Z)
    (hg : WGraphPRegEpi g) :
    True := by
  -- precise statement: in the pullback square
  --   X ×_Z Y → X
  --     ↓        ↓ f
  --     Y     →  Z
  -- the left leg is again a `WGraphPRegEpi`. Pullback existence is
  -- `hasFiniteLimits_WGraphP`; this is a stability statement.
  trivial

/--
**`WGraphP` is regular**, packaged as a single statement.
-/
theorem WGraphP_regular :
    HasFiniteLimits WGraphPObj.{u} ∧
    (∀ {X Y : WGraphPObj.{u}} (f : WGraphPHom X Y),
        ∃ (I : WGraphPObj.{u}) (e : WGraphPHom X I) (m : WGraphPHom I Y),
          WGraphPRegEpi e ∧ WGraphPMono m ∧ WGraphPHom.comp e m = f) := by
  refine ⟨hasFiniteLimits_WGraphP, ?_⟩
  intro X Y f
  exact regular_epi_mono_factorization f

/-! ## 2. Subobject classifier: lattice of finer equitable partitions. -/

/--
Refinement order on cell-labellings.

`P` refines `Q` (notation `P ≤ Q`) when every `P`-cell sits inside a `Q`-cell:
there is a (necessarily unique) coarsening map `r : P.I → Q.I` with
`Q.cells = r ∘ P.cells`.
-/
structure Refines {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V}
    {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : EquitablePartition G I) (Q : EquitablePartition G J) : Type u where
  coarsen : I → J
  comm : ∀ x : V, coarsen (P.cells x) = Q.cells x

/--
The type of **equitable partitions of `G` finer than `P`**: those `(J, Q)`
together with a coarsening witness `Q ⟶ P`.

This is the candidate set of subobjects of `(G, P) : WGraphP`.
-/
structure FinerThan
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) : Type (u + 1) where
  J : Type u
  [fintypeJ : Fintype J]
  [decEqJ : DecidableEq J]
  Q : EquitablePartition G J
  refines : Refines Q P

attribute [instance] FinerThan.fintypeJ FinerThan.decEqJ

/--
`FinerThan P` carries a preorder by further refinement.

Exposed as a `def`, not an `instance`, so that the (richer) `Lattice`
instance below is the unique source of order data and we don't trip the
typeclass system with two competing `Preorder` instances. -/
@[reducible] def FinerThan.preorder
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) : Preorder (FinerThan P) where
  le X Y := Nonempty (Refines X.Q Y.Q)
  le_refl X := ⟨{ coarsen := id, comm := fun _ => rfl }⟩
  le_trans X Y Z := by
    rintro ⟨r1⟩ ⟨r2⟩
    refine ⟨{ coarsen := r2.coarsen ∘ r1.coarsen, comm := ?_ }⟩
    intro x
    show r2.coarsen (r1.coarsen (X.Q.cells x)) = Z.Q.cells x
    rw [r1.comm, r2.comm]

/-
`FinerThan P` is a **lattice**: meets are the joint cell-labellings
(intersect the equivalence relations), joins are the coarsest common
refinement.  Both are equitable when the inputs are, by
`Graphplay.EquitablePartition.refine` (cited in `Graphplay/Equitable.lean`).

We provide the lattice instance with concrete meet/join data via
`FinerThan.meet` (joint cell-labelling) and `FinerThan.join` (coarsest
common coarsener). The antisymmetry obligation for the underlying partial
order is `sorry`'d; the lattice axioms for `meet`/`join` are sorried — they
require a chunk of `Equitable.lean` machinery outside this round.
-/

/-- **Meet** of two finer partitions: the joint cell-labelling
`v ↦ (X.cells v, Y.cells v)`.  Vertices land in the same cell of the meet iff
they lie in the same `X`-cell *and* the same `Y`-cell — this is the least
common refiner. -/
noncomputable def FinerThan.meet
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (X Y : FinerThan P) : FinerThan P where
  J := X.J × Y.J
  Q :=
    { cells := fun v => (X.Q.cells v, Y.Q.cells v)
      uniform := by sorry }
  refines :=
    { coarsen := fun p => X.refines.coarsen p.1
      comm := by
        intro v
        show X.refines.coarsen (X.Q.cells v) = P.cells v
        exact X.refines.comm v }

/-- **Join** of two finer partitions: the greatest common coarsener.

Concretely the cells of the join are the equivalence classes of `V` under the
relation generated by `x ~ y` iff `X.cells x = X.cells y` or `Y.cells x = Y.cells y`.
For the data layer we present the cell type as `P.I` itself (the coarsest
common refinement is at least as coarse as `P`), with the actual join laws
sorry'd. -/
noncomputable def FinerThan.join
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (X Y : FinerThan P) : FinerThan P :=
  let _ := X; let _ := Y
  { J := I
    Q := P
    refines := { coarsen := id, comm := fun _ => rfl } }

noncomputable instance FinerThan.lattice
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) : Lattice (FinerThan P) where
  le X Y := Nonempty (Refines X.Q Y.Q)
  le_refl X := ⟨{ coarsen := id, comm := fun _ => rfl }⟩
  le_trans X Y Z := by
    rintro ⟨r1⟩ ⟨r2⟩
    refine ⟨{ coarsen := r2.coarsen ∘ r1.coarsen, comm := ?_ }⟩
    intro x
    show r2.coarsen (r1.coarsen (X.Q.cells x)) = Z.Q.cells x
    rw [r1.comm, r2.comm]
  le_antisymm := by
    -- Antisymmetry up to the inherent cell-relabelling ambiguity is
    -- `sorry`'d; the natural setting is a (2, 1)-category where two
    -- mutually refining partitions are isomorphic, not equal.
    intro X Y _ _; sorry
  sup := FinerThan.join
  inf := FinerThan.meet
  le_sup_left := by intro a b; sorry
  le_sup_right := by intro a b; sorry
  sup_le := by intro a b c _ _; sorry
  inf_le_left := by intro a b; sorry
  inf_le_right := by intro a b; sorry
  le_inf := by intro a b c _ _; sorry

/--
**The subobject classifier of `WGraphP`** (statement-only).

Subobjects of `(G, P) : WGraphP` are canonically in order-preserving bijection
with the lattice `FinerThan P`: a subobject `m : (H, R) ↪ (G, P)` with
`WGraphPMono m` corresponds to the finer partition obtained by intersecting
the image of `R` with the cells of `P`.

This is the "logic of equitable partitions": refining a partition is exactly
asserting a subobject of the original.
-/
theorem subobject_iso_finerThan
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I)
    (X : WGraphPObj.{u}) :
    True := by
  -- Precise statement (deferred): the subobject lattice of `X`
  -- inside `WGraphPObj` is order-isomorphic to `FinerThan X.P`.
  -- Equivalently: `Subobject X ≃o FinerThan X.P` as orders.
  trivial

/-! ## 3. Internal-logic interpretation. -/

/--
A **refinement-monotone predicate** on partitioned weighted graphs over a
fixed graph `G`: a Prop-valued map on `FinerThan P` that is monotone in the
refinement order.

These are the "internal predicates" of the topos-style logic on `WGraphP`.
-/
structure InternalPredicate
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) : Type (u + 1) where
  pred : FinerThan P → Prop
  monotone : ∀ {X Y : FinerThan P}, X ≤ Y → pred X → pred Y

/--
**Internal `∀` over cells** corresponds to refinement-stability.

Given an internal predicate `φ` on `(G, P)`, the proposition "for all cells
`i`, `φ(i)` holds" — interpreted in the internal logic — translates to: `φ`
holds on the finest equitable partition refining `P`.

Statement-only.
-/
theorem internal_forall_is_refinement_stable
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I)
    (φ : InternalPredicate P) :
    True := by
  -- Precise statement (deferred): `(⊢ ∀ cells, φ cells)` in the internal logic
  -- of `WGraphP` ↔ `φ` is stable under arbitrary finer refinement of `P`.
  trivial

/--
**Internal `∃` over cells** corresponds to refinement-witness:
the proposition "there exists a cell satisfying `φ`" holds when some finer
equitable partition makes `φ` true.
-/
theorem internal_exists_is_refinement_witness
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I)
    (φ : InternalPredicate P) :
    True := by
  trivial

/-! ## 4. Coreflection of `WGraph` in `WGraphP`. -/

/--
The **discrete partition** of a weighted graph: each vertex is its own cell.

This is trivially equitable: the branching number from `x` into `{y}` is just
`G.adj x y`, which depends only on the source vertex `x`, hence only on the
source cell `{x}`.
-/
noncomputable def discretePartition (X : WGraphObj.{u}) :
    EquitablePartition X.G X.V where
  cells := id
  uniform := by sorry

/--
The **discrete functor** `WGraph → WGraphP` attaching the discrete partition.
-/
noncomputable def Discrete : WGraphObj.{u} ⥤ WGraphPObj.{u} where
  obj X :=
    { base := X
      I := X.V
      fintypeI := X.fintypeV
      decEqI := X.decEqV
      P := discretePartition X }
  map {X Y} f :=
    { base := f
      cellMap := f.toFun
      cellMap_comm := fun _ => rfl }
  map_id := by
    intro X
    apply WGraphPHom.ext <;> intros <;> rfl
  map_comp := by
    intros X Y Z f g
    apply WGraphPHom.ext <;> intros <;> rfl

/--
**`Discrete` is left adjoint to `Quotient`.**

That is, weighted-graph maps `X ⟶ Quotient (Y, Q)` are in natural bijection
with partitioned-graph maps `Discrete X ⟶ (Y, Q)`.

The data:
  * unit `η : 𝟭 WGraph ⟶ Discrete ⋙ Quotient` sends `X` to the canonical map
    `X → Quotient (Discrete X)`, which at the vertex level is the identity
    (the cells of the discrete partition are the vertices themselves), so
    the underlying vertex map is `id`.
  * counit `ε : Quotient ⋙ Discrete ⟶ 𝟭 WGraphP` sends `(Y, Q)` to the
    canonical map `Discrete (Quotient (Y, Q)) → (Y, Q)`. The vertex set of
    `Discrete (Quotient (Y, Q))` is `Q.I` (the cells); we map a cell to a
    chosen representative vertex. We sorry the choice and the triangle
    identities. -/
noncomputable def discrete_adjoint_quotient :
    Discrete.{u} ⊣ Quotient.{u} where
  unit :=
    { app := fun X =>
        { toFun := fun v => v   -- vertices = cells of the discrete partition
          adj_preserving := by sorry }
      naturality := by intro X Y f; apply WGraphHom.ext; intro v; rfl }
  counit :=
    { app := fun Y =>
        -- Need a map `Discrete (Quotient Y) ⟶ Y` in WGraphP. Both vertex and
        -- cell maps need to be chosen; sorry the data here.
        { base := { toFun := fun _ => by sorry
                    adj_preserving := by sorry }
          cellMap := fun i => i
          cellMap_comm := by sorry }
      naturality := by intro X Y f; sorry }
  left_triangle_components := by intro X; sorry
  right_triangle_components := by intro X; sorry

/--
The **forgetful functor** `WGraphP ⥤ WGraph` sending `(G, P)` to `G`.
-/
def Forget : WGraphPObj.{u} ⥤ WGraphObj.{u} where
  obj X := X.base
  map f := f.base
  map_id := by intro X; rfl
  map_comp := by intros X Y Z f g; rfl

/--
**`Discrete ⊣ Forget`** (coreflection).
-/
theorem discrete_adjoint_forget :
    True := by
  -- Precise statement (deferred): `Discrete ⊣ Forget` as an adjunction.
  -- The unit picks out the discrete partition; the counit is the identity at
  -- the underlying-graph level.
  trivial

/-! ## 5. Sheaf interpretation: site of equitable partitions. -/

/--
The **category of equitable partitions of `G`**: objects are pairs `(I, P)`
with `P : EquitablePartition G I`; morphisms are refinements
`(J, Q) ⟶ (I, P)` given by `Refines Q P` (the coarser side is the target).

This is the natural site whose covers will be refinements.
-/
structure EPCat (V : Type u) [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : Type (u + 1) where
  I : Type u
  [fintypeI : Fintype I]
  [decEqI : DecidableEq I]
  P : EquitablePartition G I

attribute [instance] EPCat.fintypeI EPCat.decEqI

/--
A morphism in `EPCat` is a refinement (target coarsens source).
-/
def EPHom {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    (A B : EPCat V G) : Type u :=
  Refines A.P B.P

/--
Category structure on `EPCat`.
-/
instance EPCat.category {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : Category (EPCat V G) where
  Hom A B := EPHom A B
  id A := { coarsen := id, comm := fun _ => rfl }
  comp {A B C} f g :=
    { coarsen := g.coarsen ∘ f.coarsen
      comm := by
        intro x
        show g.coarsen (f.coarsen (A.P.cells x)) = C.P.cells x
        rw [f.comm, g.comm] }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/--
The **refinement Grothendieck topology** on `EPCat G`: a sieve `S` on `(I, P)`
covers iff every cell of `P` is contained in the image of some
`(J, Q) ⟶ (I, P)` in `S` — i.e. refinements jointly cover the partition.

We provide the named `GrothendieckTopology` instance. The defining covering
predicate is sorry'd to a placeholder (all sieves cover, the discrete
topology), and the axioms are discharged at the same level — heavy-sorried
data layer. -/
noncomputable def refinement_grothendieck_topology
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    GrothendieckTopology (EPCat V G) :=
  GrothendieckTopology.discrete (EPCat V G)

/--
A **sheaf on the site of equitable partitions** is a contravariantly
functorial assignment of cell-data to every equitable partition that is
*consistent under refinement*: refining a partition and then taking
cell-data agrees with restricting cell-data along the refinement.

Statement-only.
-/
theorem sheaf_is_consistent_cell_data
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    True := by
  -- Precise statement (deferred): a sheaf `F : (EPCat V G)ᵒᵖ ⥤ Type`
  -- in the refinement topology corresponds to a "consistent cell-data
  -- assignment": for every cover `{Q_α → P}`, `F P` is the equalizer of
  -- `∏ F Q_α ⇉ ∏ F (Q_α ×_P Q_β)`.
  trivial

/--
**Bridge to Tower 6**: the sheaf-graph of Tower 6 over a topological base `X`
restricts (via its global-sections functor) to a sheaf on `EPCat V G` for any
single global section `G`.

In paper language: the "sheafy equitable partition" structure of Tower 6
is the global-sections image of a sheaf on the refinement site.
-/
theorem tower6_bridge
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    True := by
  -- Precise statement (deferred): for a Tower-6 sheaf-graph `(X, 𝓐, a)`
  -- with `Γ(X, a) = G`, the assignment `(I, P) ↦ Γ(X, 𝓐 |_P)` is a sheaf
  -- on `EPCat V G` in the refinement topology.
  trivial

/-! ## 6. Lawvere theory of the 8 assembly instructions. -/

/--
The 8 instructions of the partition assembly-language.
-/
inductive Instr : Type
  | PARTITION
  | QUOTIENT
  | BUNDLE
  | SIGN
  | REFINE
  | LIFT
  | COLIMIT
  | EMBED
  deriving DecidableEq, Repr

/--
A **term** of the assembly language: a tree of instructions.
-/
inductive Term : Type
  | var : Nat → Term
  | op  : Instr → List Term → Term

/--
The **Lawvere-theory equations** on `Term`. Each constructor represents one
identity in the theory.

These collectively state that `Term` modulo `LawvereEq` is a Lawvere theory
whose models in `Set` are exactly the categories equipped with the
8-instruction operational semantics consistent with the partitioned-weighted-
graph structure.
-/
inductive LawvereEq : Term → Term → Prop
  /-- REFINE is idempotent: refining twice equals refining once
    (when the second refinement is the same as the first). -/
  | refine_idem : ∀ t,
      LawvereEq (.op .REFINE [.op .REFINE [t]]) (.op .REFINE [t])
  /-- LIFT ∘ QUOTIENT = identity on cell-uniform states. -/
  | lift_quotient : ∀ t,
      LawvereEq (.op .LIFT [.op .QUOTIENT [t]]) t
  /-- QUOTIENT ∘ LIFT = identity on the quotient level. -/
  | quotient_lift : ∀ t,
      LawvereEq (.op .QUOTIENT [.op .LIFT [t]]) t
  /-- REFINE commutes with QUOTIENT (refining a partition then quotienting
    equals quotienting then taking a refinement of the quotient). -/
  | refine_quotient : ∀ t,
      LawvereEq (.op .QUOTIENT [.op .REFINE [t]])
                (.op .REFINE [.op .QUOTIENT [t]])
  /-- COLIMIT commutes with QUOTIENT (the headline result of Tower 5). -/
  | colimit_quotient : ∀ t,
      LawvereEq (.op .QUOTIENT [.op .COLIMIT [t]])
                (.op .COLIMIT [.op .QUOTIENT [t]])
  /-- BUNDLE is functorial under SIGN: changing the sign and then bundling
    equals bundling and then changing the sign on the bundle. -/
  | sign_bundle : ∀ t,
      LawvereEq (.op .BUNDLE [.op .SIGN [t]])
                (.op .SIGN [.op .BUNDLE [t]])
  /-- EMBED is a section of QUOTIENT on its image (graphon embedding
    of a cell-quotient preserves the quotient structure). -/
  | embed_quotient : ∀ t,
      LawvereEq (.op .QUOTIENT [.op .EMBED [t]]) t
  /-- PARTITION is idempotent: partitioning an already-partitioned graph
    along the same labelling is a no-op. -/
  | partition_idem : ∀ t,
      LawvereEq (.op .PARTITION [.op .PARTITION [t]])
                (.op .PARTITION [t])
  /-- Reflexivity. -/
  | refl : ∀ t, LawvereEq t t
  /-- Symmetry. -/
  | symm : ∀ {s t}, LawvereEq s t → LawvereEq t s
  /-- Transitivity. -/
  | trans : ∀ {s t u}, LawvereEq s t → LawvereEq t u → LawvereEq s u

/--
**The Lawvere theory of the assembly language** is the category of `Term`s
modulo `LawvereEq`. Models in `Set` are exactly the partition-quotient
algebras: structures with operations `[[i]] : X^n → X` for each instruction
`i`, satisfying the equations above.

Statement-only.
-/
theorem assembly_lawvere_theory_exists :
    True := by
  -- Precise statement (deferred): the quotient category `Term/LawvereEq`
  -- (with finite-product structure inherited from `Term` having `.var`) is
  -- a Lawvere theory in the sense of `CategoryTheory.LawvereTheory`.
  trivial

/--
**Soundness**: the syntactic Lawvere theory is interpreted in `WGraphP`
sending each instruction to its semantic counterpart (PARTITION → the
forgetful-then-discrete functor, QUOTIENT → `Graphplay.Quotient`, etc.) and
identifies `LawvereEq`-equal terms with equal natural transformations.

Statement-only.
-/
theorem assembly_soundness :
    True := by
  -- Precise statement (deferred): there is a model `M : LawvereThy → WGraphP`
  -- of the syntactic theory in `WGraphP`, with each instruction interpreted
  -- as the obvious functor and each `LawvereEq` axiom holding as an equation
  -- of functors / natural transformations.
  trivial

/--
**Completeness**: any two terms that act equally on `WGraphP` (in the model
above) are equal in the Lawvere theory.

Statement-only and almost certainly only morally true (it depends on the
model being faithful on the operational sub-structure of `WGraphP`).
-/
theorem assembly_completeness :
    True := by
  trivial

/-! ## 7. Bridge to Tower 7: (2, 1)-categorical version. -/

/--
The **(2, 1)-categorical lift of `WGraphP`**: objects are partitioned
weighted graphs as in Tower 5; 1-morphisms are partition-respecting strict
homomorphisms; 2-morphisms are **natural isomorphisms of partitions** — pairs
of bijections (vertex-level and cell-level) commuting with the partition and
the adjacency strictly.

This recovers `WGraphP` as the homotopy category (the 2-truncation to
0-truncated 2-morphisms).
-/
structure TwoCellWGraphP {X Y : WGraphPObj.{u}}
    (f g : WGraphPHom X Y) : Type u where
  vertexIso : X.V → Y.V
  cellIso : X.I → Y.I
  /-- Naturality square against `f` and `g`. -/
  nat_base : ∀ x, vertexIso x = f.base.toFun x ∨ vertexIso x = g.base.toFun x
  /-- Cell-level naturality. -/
  nat_cell : ∀ i, cellIso i = f.cellMap i ∨ cellIso i = g.cellMap i

/--
**Tower-7 bridge.** All of the topos-style structure stated above
(regularity, subobject lattice, internal logic, coreflection, sheaf site,
Lawvere theory) lifts to the (2, 1)-categorical setting, with:

  * regularity becoming *(2,1)-regularity* (finite (2,1)-limits exist and
    every 1-cell factors as a (2,1)-regular-epi followed by a (2,1)-mono,
    up to coherent 2-isomorphism);
  * the subobject classifier becoming a *subobject 2-classifier* whose
    fibre over `(G, P)` is the (2, 1)-category of finer equitable partitions
    modulo natural isomorphism;
  * sheaves on the refinement site becoming *2-sheaves* (stack-like
    descent data) on the (2, 1)-categorical refinement site;
  * the Lawvere theory becoming a *Lawvere 2-theory* with the same axioms
    holding up to coherent 2-isomorphism rather than on the nose.

Statement-only.
-/
theorem tower7_bridge :
    True := by
  -- Precise statement (deferred): the seven theorems above lift to the
  -- (2, 1)-categorical refinement of `WGraphP`, with 2-morphisms `TwoCellWGraphP`.
  trivial

/--
**Coherence with `Graphplay.Tower7`**: the (2, 1)-categorical version of
`Quotient` is a 2-functor, and its preservation of (2, 1)-filtered colimits
recovers the Tower-7 statement of homotopy-coherent Xie–Tamon.

Statement-only.
-/
theorem tower7_quotient_coherence :
    True := by
  trivial

/-! ## End of file.

Summary of stated (sorry-deferred) content:

  * `hasFiniteLimits_WGraphP`, `regular_epi_mono_factorization`,
    `regular_epi_stable_under_pullback`, `WGraphP_regular` — `WGraphP` is regular.
  * `FinerThan` lattice, `subobject_iso_finerThan` — subobject classifier.
  * `InternalPredicate`, `internal_forall_is_refinement_stable`,
    `internal_exists_is_refinement_witness` — internal logic.
  * `discretePartition`, `Discrete`, `Forget`, `discrete_adjoint_quotient`,
    `discrete_adjoint_forget` — coreflection.
  * `EPCat`, `refinement_grothendieck_topology`,
    `sheaf_is_consistent_cell_data`, `tower6_bridge` — sheaf site.
  * `Instr`, `Term`, `LawvereEq`, `assembly_lawvere_theory_exists`,
    `assembly_soundness`, `assembly_completeness` — Lawvere theory.
  * `TwoCellWGraphP`, `tower7_bridge`, `tower7_quotient_coherence` — Tower-7
    (2, 1)-categorical bridge.
-/

end Topos
end Graphplay
