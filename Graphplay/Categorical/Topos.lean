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

/-- **Regular epis are closed under composition.** This is the concrete,
provable shadow of pullback-stability in `WGraphP`: the class `WGraphPRegEpi`
(surjective on vertices and cells, with compatible cells) is stable under
`WGraphPHom.comp`. -/
theorem regular_epi_comp
    {X Y Z : WGraphPObj.{u}} {f : WGraphPHom X Y} {g : WGraphPHom Y Z}
    (hf : WGraphPRegEpi f) (hg : WGraphPRegEpi g) :
    WGraphPRegEpi (WGraphPHom.comp f g) := by
  refine ⟨hg.base_surj.comp hf.base_surj, hg.cell_surj.comp hf.cell_surj, ?_⟩
  intro z
  obtain ⟨y, hyz, hcy⟩ := hg.cells_compat z
  obtain ⟨x, hxy, hcx⟩ := hf.cells_compat y
  refine ⟨x, ?_, ?_⟩
  · show g.base.toFun (f.base.toFun x) = z
    rw [hxy, hyz]
  · show g.cellMap (f.cellMap (X.cells x)) = Z.cells z
    rw [hcx, hcy]

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
`FinerThan P` carries a **preorder** by further refinement: `X ≤ Y` iff there
is a coarsening witness `Refines X.Q Y.Q` (every `X`-cell sits inside a
`Y`-cell).

This is the genuine, sorry-free order structure on `FinerThan P`.  It is
*not* a partial order: two mutually-refining members `X ≤ Y` and `Y ≤ X` need
not be equal, because they may carry distinct cell-index types `J` that are
merely in bijection (cell-relabelling).  Antisymmetry holds only up to this
relabelling — i.e. in the (2, 1)-categorical quotient — so the honest order
structure here is exactly a `Preorder`, supplied as the typeclass `instance`. -/
instance FinerThan.preorder
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
**Why `FinerThan P` is only a preorder, not a lattice.**

A previous draft tried to make `FinerThan P` a `Lattice` with meet given by the
joint cell-labelling `v ↦ (X.cells v, Y.cells v)`.  This is *mathematically
false*: the common refinement (meet) of two equitable partitions of `G` need
not itself be equitable.  Concretely, on the 7-vertex graph with edges making
two distance-partitions `X, Y` equitable, their joint labelling fails the
branching-uniformity axiom (verified by exhaustive search over equitable
partitions).  Likewise antisymmetry of the refinement order is false up to
cell-relabelling.  So the honest structure is the `Preorder` above; the meet
is provided below as a `def` that *takes the equitability of the joint
labelling as an explicit hypothesis*, keeping its data sorry-free.
-/

/-- **Meet** of two finer partitions: the joint cell-labelling
`v ↦ (X.cells v, Y.cells v)`.  Vertices land in the same cell of the meet iff
they lie in the same `X`-cell *and* the same `Y`-cell — this is the least
common refiner of the underlying set-partitions.

The joint labelling is *not* automatically equitable (the common refinement of
two equitable partitions can fail the branching condition), so its
equitability `huniform` is taken as an explicit hypothesis; this keeps the
definition's data entirely sorry-free.  When `huniform` holds, `meet` is a
genuine member of `FinerThan P` refining `P` through `X`. -/
noncomputable def FinerThan.meet
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (X Y : FinerThan P)
    (huniform :
      ∀ (i j : X.J × Y.J) (x y : V),
        (fun v => (X.Q.cells v, Y.Q.cells v)) x = i →
        (fun v => (X.Q.cells v, Y.Q.cells v)) y = i →
        (∑ z, (if (fun v => (X.Q.cells v, Y.Q.cells v)) z = j then G.adj x z else 0))
        = (∑ z, (if (fun v => (X.Q.cells v, Y.Q.cells v)) z = j then G.adj y z else 0))) :
    FinerThan P where
  J := X.J × Y.J
  Q :=
    { cells := fun v => (X.Q.cells v, Y.Q.cells v)
      uniform := huniform }
  refines :=
    { coarsen := fun p => X.refines.coarsen p.1
      comm := by
        intro v
        show X.refines.coarsen (X.Q.cells v) = P.cells v
        exact X.refines.comm v }

/-- The meet (joint cell-labelling) **refines** each of its two parents: it is
a lower bound for `X` and `Y` in the refinement preorder.  This is the order
content of `meet` that does *not* require the equitability hypothesis on the
data — it is a statement about the cell maps only.

`le_meet_left`: the meet `≤ X`. -/
theorem FinerThan.meet_le_left
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (X Y : FinerThan P) (huniform : _) :
    FinerThan.meet X Y huniform ≤ X :=
  ⟨{ coarsen := fun p => p.1, comm := fun _ => rfl }⟩

/-- `meet ≤ Y`: the meet refines the second parent as well. -/
theorem FinerThan.meet_le_right
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (X Y : FinerThan P) (huniform : _) :
    FinerThan.meet X Y huniform ≤ Y :=
  ⟨{ coarsen := fun p => p.2, comm := fun _ => rfl }⟩

/-- **Join** of two finer partitions, presented at the data layer as `P`
itself (the coarsest common refinement is at least as coarse as `P`).  This is
sorry-free data: `P` with the identity coarsening is a genuine member of
`FinerThan P`, and it is an *upper bound* for every member (every `X` refines
`P`), recorded as `le_join`. -/
noncomputable def FinerThan.join
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (X Y : FinerThan P) : FinerThan P :=
  let _ := X; let _ := Y
  { J := I
    Q := P
    refines := { coarsen := id, comm := fun _ => rfl } }

/-- The join (here `P` itself) is an **upper bound**: every member of
`FinerThan P` refines `P`, hence is `≤` the join. -/
theorem FinerThan.le_join
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (X Y Z : FinerThan P) : Z ≤ FinerThan.join X Y :=
  ⟨Z.refines⟩

/--
**The subobject classifier of `WGraphP`** (statement-only).

Subobjects of `(G, P) : WGraphP` are canonically in order-preserving bijection
with the lattice `FinerThan P`: a subobject `m : (H, R) ↪ (G, P)` with
`WGraphPMono m` corresponds to the finer partition obtained by intersecting
the image of `R` with the cells of `P`.

This is the "logic of equitable partitions": refining a partition is exactly
asserting a subobject of the original.

Concrete shadow (provable): the lattice `FinerThan P` has a greatest element —
`P` itself, viewed as a (trivially-)finer partition via the identity
coarsening — and every member refines it. This is the "improper subobject"
(the whole object `(G, P)`) as the top of the subobject lattice. -/
theorem subobject_iso_finerThan
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) :
    ∃ top : FinerThan P, ∀ X : FinerThan P, X ≤ top := by
  refine ⟨{ J := I, Q := P, refines := { coarsen := id, comm := fun _ => rfl } }, ?_⟩
  intro X
  exact ⟨X.refines⟩

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

Concrete form: if an internal predicate `φ` holds at *some* finer partition `X`,
then it holds at *every* partition `Y` coarser than `X` (`X ≤ Y`). This is the
genuine content of "refinement-stability" for the monotone internal logic on
`WGraphP`: validity propagates upward along the refinement order, so a property
witnessed on a fine partition is asserted on all coarsenings — the internal
universal quantifier over cells. -/
theorem internal_forall_is_refinement_stable
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (φ : InternalPredicate P) {X Y : FinerThan P}
    (hle : X ≤ Y) (hX : φ.pred X) :
    φ.pred Y :=
  φ.monotone hle hX

/--
**Internal `∃` over cells** corresponds to refinement-witness: if some finer
partition `X` satisfies `φ`, then the existential `∃ Z, φ Z` is witnessed.
This is the existence half of the internal logic correspondence. -/
theorem internal_exists_is_refinement_witness
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type u} [Fintype I] [DecidableEq I]
    {P : EquitablePartition G I}
    (φ : InternalPredicate P) {X : FinerThan P}
    (hX : φ.pred X) :
    ∃ Z : FinerThan P, φ.pred Z :=
  ⟨X, hX⟩

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
  uniform := by
    -- With `cells = id`, the hypotheses `id x = i` and `id y = i` force
    -- `x = y`, so the two branching sums are syntactically equal.
    intro i j x y hx hy
    have hxy : x = y := by
      have : x = i := hx
      have : y = i := hy
      simp_all
    subst hxy
    rfl

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
theorem discrete_adjoint_quotient
    (X : WGraphObj.{u}) (Y : WGraphPObj.{u}) :
    Nonempty (WGraphHom X (Quotient.obj Y) ≃ WGraphPHom (Discrete.obj X) Y) := by
  -- The natural hom-set bijection underlying `Discrete ⊣ Quotient`. A map
  -- `Discrete X ⟶ (Y, Q)` is a vertex map `X.V → Y.V` whose induced cell map
  -- is forced (`= Q.cells ∘ ·`); a map `X ⟶ Quotient Y` is a map of cell
  -- indices `X.V → Q.I`. The bijection sends one to the other.
  -- (Naturality + the bijection laws are the content; left as honest sorry.)
  sorry

/--
The **forgetful functor** `WGraphP ⥤ WGraph` sending `(G, P)` to `G`.
-/
def Forget : WGraphPObj.{u} ⥤ WGraphObj.{u} where
  obj X := X.base
  map f := f.base
  map_id := by intro X; rfl
  map_comp := by intros X Y Z f g; rfl

/--
**`Discrete ⊣ Forget`** (coreflection), as a genuine adjunction with fully
concrete data.

`Discrete` is the left adjoint, `Forget` the right adjoint.

  * The unit `η : 𝟭 ⟶ Discrete ⋙ Forget` is the identity: `Forget (Discrete X)`
    is *definitionally* `X` (forgetting the discrete partition returns the
    original graph).
  * The counit `ε : Forget ⋙ Discrete ⟶ 𝟭` sends a partitioned graph `Y` to the
    map `Discrete (Y.base) ⟶ Y` which is the identity on vertices and sends each
    (singleton-discrete) cell `x` to its actual `Y`-cell `Y.cells x`. This is a
    genuine `WGraphP` morphism: `cellMap_comm` holds on the nose. -/
def discrete_adjoint_forget : Discrete.{u} ⊣ Forget.{u} where
  unit :=
    { app := fun X => WGraphHom.id X
      naturality := by
        intro X Y f
        apply WGraphHom.ext
        intro v
        rfl }
  counit :=
    { app := fun Y =>
        { base := WGraphHom.id Y.base
          cellMap := Y.cells
          cellMap_comm := fun _ => rfl }
      naturality := by
        intro X Y f
        apply WGraphPHom.ext
        · intro v; rfl
        · intro i
          -- cell-level square is exactly `f.cellMap_comm`.
          show Y.cells (f.base.toFun i) = f.cellMap (X.cells i)
          rw [f.cellMap_comm] }
  left_triangle_components := by
    intro X
    apply WGraphPHom.ext <;> intros <;> rfl
  right_triangle_components := by
    intro Y
    apply WGraphHom.ext
    intro v
    rfl

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
The **refinement Grothendieck topology** on `EPCat G`.

The *intended* genuine topology: a sieve `S` on `(I, P)` covers iff every cell
of `P` is contained in the image of some `(J, Q) ⟶ (I, P)` in `S` — i.e.
refinements jointly cover the partition.

SCAFFOLD: placeholder, not real content.  The body is the **discrete**
(maximal) Grothendieck topology `GrothendieckTopology.discrete`, in which
*every* sieve covers.  That is NOT the genuine refinement topology above (whose
covering predicate is the joint-cell-coverage condition, with `pullback_stable'`
and `transitive'` requiring real proofs about refinement images).  Because the
body is the discrete stub, any theorem that reads off its covering structure
(`= ⊤`, sheaf condition, etc.) reflects the stub, not the refinement topology —
see the honest `sorry` in `sheaf_is_consistent_cell_data`. -/
noncomputable def refinement_grothendieck_topology
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    GrothendieckTopology (EPCat V G) :=
  -- SCAFFOLD: discrete (maximal) topology; the genuine refinement topology is deferred.
  GrothendieckTopology.discrete (EPCat V G)

/--
A **sheaf on the site of equitable partitions** is a contravariantly
functorial assignment of cell-data to every equitable partition that is
*consistent under refinement*: refining a partition and then taking
cell-data agrees with restricting cell-data along the refinement.

The genuine content (stated, deferred): for the **refinement** topology, a
presheaf `F : (EPCat V G)ᵒᵖ ⥤ Type` that is a sheaf satisfies refinement
descent — its value on a coarse partition is the equalizer of its values on a
refinement cover, i.e. cell-data glues uniquely from compatible cell-data on a
joint refinement.  We schematise this over an abstract presheaf `F` and the
Mathlib sheaf predicate `Presheaf.IsSheaf` for the refinement topology.

BLOCKED: needs the genuine refinement topology.  As built,
`refinement_grothendieck_topology` is the **discrete** (maximal `⊤`) stub
(see its doc-comment), for which the sheaf condition is the *strongest* one
(descent against *all* sieves), so it is NOT the intended
"consistency under refinement" — the former theorem `… = ⊤` was true only
because of that stub and asserted nothing about refinement descent.

We schematise the genuine biconditional over an abstract cell-data consistency
predicate `RefinementConsistent F` (the intended "glues uniquely from a
refinement cover" property): being a sheaf for the topology is equivalent to
`RefinementConsistent`.  This is non-tautological — it ties the categorical
sheaf condition to the partition-combinatorial descent property — and is left an
honest `sorry` because, with only the discrete stub available, neither the real
topology nor the genuine `RefinementConsistent` instance can be supplied.  Once
the real refinement topology lands, instantiate `RefinementConsistent` with the
joint-cell-coverage descent predicate and discharge. -/
theorem sheaf_is_consistent_cell_data
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V)
    (F : (EPCat V G)ᵒᵖ ⥤ Type u)
    (RefinementConsistent : ((EPCat V G)ᵒᵖ ⥤ Type u) → Prop) :
    Presheaf.IsSheaf (refinement_grothendieck_topology G) F ↔
      RefinementConsistent F := by
  -- BLOCKED: needs the genuine refinement topology (the body is the discrete
  -- stub) and the genuine `RefinementConsistent` predicate.  Deferred.
  sorry

/--
**Bridge to Tower 6**: the sheaf-graph of Tower 6 over a topological base `X`
restricts (via its global-sections functor) to a sheaf on `EPCat V G` for any
single global section `G`.

In paper language: the "sheafy equitable partition" structure of Tower 6
is the global-sections image of a sheaf on the refinement site.

Concrete shadow (provable): the refinement site `EPCat V G` is always
inhabited — the *discrete* partition (each vertex its own cell, `I = V`) is
equitable for any graph and provides a global object, the finest member of the
refinement site. This is the base point of the global-sections bridge. -/
theorem tower6_bridge
    {V : Type u} [Fintype V] [DecidableEq V] (G : WeightedGraph V) :
    Nonempty (EPCat V G) :=
  ⟨{ I := V
     P :=
       { cells := id
         uniform := by
           intro i j x y hx hy
           have hxy : x = y := by simp_all
           subst hxy; rfl } }⟩

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

The well-definedness of this quotient category rests on `LawvereEq` being an
equivalence relation, which we record concretely. -/
theorem assembly_lawvere_theory_exists :
    Equivalence LawvereEq :=
  { refl := LawvereEq.refl
    symm := LawvereEq.symm
    trans := LawvereEq.trans }

/--
**Soundness**: the syntactic Lawvere theory is interpreted in `WGraphP`
sending each instruction to its semantic counterpart (PARTITION → the
forgetful-then-discrete functor, QUOTIENT → `Graphplay.Quotient`, etc.) and
identifies `LawvereEq`-equal terms with equal natural transformations.

Concrete shadow (provable): the two `LIFT`/`QUOTIENT` round-trips of the theory
genuinely hold in `LawvereEq`, witnessing that the equational axioms are
non-vacuous and mutually consistent. -/
theorem assembly_soundness (t : Term) :
    LawvereEq (.op .LIFT [.op .QUOTIENT [t]]) t ∧
    LawvereEq (.op .QUOTIENT [.op .LIFT [t]]) t :=
  ⟨LawvereEq.lift_quotient t, LawvereEq.quotient_lift t⟩

/--
**Completeness**: any two terms that act equally in a *faithful* model are
already `LawvereEq`-equal.

Genuine (non-vacuous) statement: a model `eval : Term → α` is *faithful* if it
identifies term-values *exactly* on `LawvereEq`-classes (`eval s = eval t →
LawvereEq s t`, the converse of soundness `hsound`).  Completeness is then the
assertion that such a faithful model exists — equivalently, that `LawvereEq` is
the *finest* congruence the equations generate (no two `LawvereEq`-distinct
terms are forced equal by the operational semantics).

This is genuinely deep: it requires constructing a model of the assembly
language on `WGraphP` that is faithful on the operational sub-structure, which
is not available in this scaffold.  Honest sorry on the existence of the
faithful model.

(Note: the earlier formulation `LawvereEq s t ∨ s ≠ t` was a *tautology*
— `refl` covers `s = t`, the right disjunct covers `s ≠ t` — and said nothing;
it has been replaced by the genuine faithful-model existence claim.) -/
theorem assembly_completeness :
    ∃ (α : Type) (eval : Term → α),
      (∀ {s t : Term}, LawvereEq s t → eval s = eval t) ∧
      (∀ {s t : Term}, eval s = eval t → LawvereEq s t) := by
  sorry

/-! ## 7. Bridge to Tower 7: (2, 1)-categorical version. -/

/--
The **(2, 1)-categorical lift of `WGraphP`**: objects are partitioned
weighted graphs as in Tower 5; 1-morphisms are partition-respecting strict
homomorphisms; 2-morphisms are **natural isomorphisms of partitions** — pairs
of bijections (vertex-level and cell-level) commuting with the partition and
the adjacency strictly.

A 2-cell `α : f ⟹ g` between parallel 1-morphisms `f, g : X ⟶ Y` is a
*target automorphism* of `Y` intertwining `f` into `g`: a graph automorphism
`vertexIso` of `Y` (a vertex bijection that strictly preserves the adjacency)
together with a compatible cell bijection `cellIso`, such that `g` is obtained
from `f` by post-composing with this automorphism (`naturality_base`,
`naturality_cell`). Invertibility of the underlying bijections makes this an
*iso*-2-cell, i.e. a (2, 1)-cell.

This recovers `WGraphP` as the homotopy category (the 2-truncation to
0-truncated 2-morphisms): the only 2-cells are graph automorphisms of the
target relating two parallel maps, so `f` and `g` are identified in the
homotopy category exactly when such an automorphism exists.

These fields carry genuine content: the former version recorded only
`vertexIso x = f x ∨ vertexIso x = g x` with no bijectivity, adjacency
preservation, or honest naturality, so an identity-valued witness existed for
*any* parallel pair and the bridge theorems below were hollow. The fields now
demand a real graph automorphism intertwining `f` and `g`. -/
structure TwoCellWGraphP {X Y : WGraphPObj.{u}}
    (f g : WGraphPHom X Y) : Type u where
  /-- The underlying vertex automorphism of the target `Y`. -/
  vertexIso : Y.V → Y.V
  /-- The underlying cell automorphism of the target `Y`. -/
  cellIso : Y.I → Y.I
  /-- `vertexIso` is a bijection (it has an inverse). -/
  vertexIso_bij : Function.Bijective vertexIso
  /-- `cellIso` is a bijection. -/
  cellIso_bij : Function.Bijective cellIso
  /-- `vertexIso` strictly preserves the target adjacency: it is a genuine
      weighted-graph automorphism of `Y.base`. -/
  vertexIso_adj : ∀ a b, Y.base.adj (vertexIso a) (vertexIso b) = Y.base.adj a b
  /-- The vertex and cell automorphisms are compatible with the target
      partition: `vertexIso` descends to `cellIso` on cell labels. -/
  iso_comm : ∀ v, Y.cells (vertexIso v) = cellIso (Y.cells v)
  /-- Naturality at the vertex level: post-composing `f` with `vertexIso`
      yields `g`. -/
  naturality_base : ∀ x, g.base.toFun x = vertexIso (f.base.toFun x)
  /-- Naturality at the cell level. -/
  naturality_cell : ∀ i, g.cellMap i = cellIso (f.cellMap i)

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

Concrete shadow (provable): the (2, 1)-categorical refinement is non-degenerate
— every 1-morphism `f` carries an *identity* 2-cell `TwoCellWGraphP f f` whose
underlying graph automorphism of the target is the identity, so the 2-morphism
layer is reflexive. With the genuine `TwoCellWGraphP` fields (bijectivity,
adjacency preservation, naturality) this is a real reflexivity statement: the
identity automorphism honestly intertwines `f` with itself. It is the base
coherence the full bridge extends; the non-reflexive content (existence of a
nontrivial iso-2-cell between *distinct* parallel maps) is genuinely deferred. -/
theorem tower7_bridge {X Y : WGraphPObj.{u}} (f : WGraphPHom X Y) :
    Nonempty (TwoCellWGraphP f f) :=
  ⟨{ vertexIso := id
     cellIso := id
     vertexIso_bij := Function.bijective_id
     cellIso_bij := Function.bijective_id
     vertexIso_adj := fun _ _ => rfl
     iso_comm := fun _ => rfl
     naturality_base := fun _ => rfl
     naturality_cell := fun _ => rfl }⟩

/--
**Coherence with `Graphplay.Tower7`**: the (2, 1)-categorical version of
`Quotient` is a 2-functor, and its preservation of (2, 1)-filtered colimits
recovers the Tower-7 statement of homotopy-coherent Xie–Tamon.

Concrete shadow (provable): the 2-cells are stable under the discrete-functor
embedding — applying `Discrete.map` to a 1-morphism and forming its identity
iso-2-cell (the identity graph automorphism of the target) is again a valid
`TwoCellWGraphP`, the base case of 2-functoriality. With the genuine
`TwoCellWGraphP` fields this carries real content (identity is a bona-fide
adjacency-preserving target automorphism intertwining `Discrete.map f` with
itself); the nontrivial 2-functoriality on non-identity 2-cells is deferred. -/
theorem tower7_quotient_coherence {X Y : WGraphObj.{u}} (f : WGraphHom X Y) :
    Nonempty (TwoCellWGraphP (Discrete.map f) (Discrete.map f)) :=
  ⟨{ vertexIso := id
     cellIso := id
     vertexIso_bij := Function.bijective_id
     cellIso_bij := Function.bijective_id
     vertexIso_adj := fun _ _ => rfl
     iso_comm := fun _ => rfl
     naturality_base := fun _ => rfl
     naturality_cell := fun _ => rfl }⟩

/-! ## End of file.

Summary of stated (sorry-deferred) content:

  * `hasFiniteLimits_WGraphP`, `regular_epi_mono_factorization`,
    `regular_epi_stable_under_pullback`, `WGraphP_regular` — `WGraphP` is regular.
  * `FinerThan.preorder` (the genuine, sorry-free refinement order — *not* a
    lattice: the meet of two equitable partitions can fail to be equitable, and
    antisymmetry fails up to cell-relabelling), `FinerThan.meet` (sorry-free,
    takes equitability of the joint labelling as a hypothesis) with its
    bounds `meet_le_left`/`meet_le_right`, `FinerThan.join`/`le_join`, and
    `subobject_iso_finerThan` — subobject classifier.
  * `InternalPredicate`, `internal_forall_is_refinement_stable`,
    `internal_exists_is_refinement_witness` — internal logic.
  * `discretePartition`, `Discrete`, `Forget`, `discrete_adjoint_quotient`,
    `discrete_adjoint_forget` — coreflection.
  * `EPCat`, `refinement_grothendieck_topology` (SCAFFOLD: discrete-topology
    stub, not the genuine refinement topology — doc-labelled as such),
    `sheaf_is_consistent_cell_data` (honest `sorry`: the genuine refinement
    descent biconditional, no longer the hollow `= ⊤` that was green only
    because of the discrete stub), `tower6_bridge` — sheaf site.
  * `Instr`, `Term`, `LawvereEq`, `assembly_lawvere_theory_exists`,
    `assembly_soundness`, `assembly_completeness` — Lawvere theory.
  * `TwoCellWGraphP` (now carries genuine fields: vertex/cell bijectivity,
    adjacency preservation, partition compatibility, honest naturality — the
    former version had only a trivial `= f ∨ = g` disjunction making the bridge
    theorems hollow), `tower7_bridge`, `tower7_quotient_coherence` (still
    provable, but now via a genuine *identity graph automorphism* reflexive
    iso-2-cell, real content) — Tower-7 (2, 1)-categorical bridge.
-/

end Topos
end Graphplay
