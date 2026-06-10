/-
Graphplay/Categorical.lean

Tower 5 — Categorical layer.

Goals of this file:
  * give the category `WGraph` of weighted graphs (Hermitian loopless complex
    adjacency matrices) with strict (isometric) morphisms;
  * give the category `WGraphP` of partitioned weighted graphs together with
    morphisms that respect partitions;
  * define the `Quotient : WGraphP ⥤ WGraph` functor and state its functoriality;
  * re-express the Tower-1 / Tower-2 disjoint union (`SigmaGraph`, `WSigmaGraph`)
    and the Tower-1 / Tower-2 staged union (`UnionGraph`) as coproducts and
    filtered colimits respectively;
  * state the headline preservation theorem
    `Quotient.preservesFilteredColimits` and its corollary
    `quasi_infinite_limit`, the universal form of the Xie–Tamon
    no-infinite-tail-beats-optimality result;
  * state the lift theorem as a natural transformation living over
    `Quotient.op`, encompassing PST, mixing and search lifting;
  * sketch the embedding into graphons (cut-norm topology, BCLSV 1003.5588).

The category structures, the Quotient functor on the quotient-morphism
subcategory `WGraphPQ`, and the headline filtered-colimit preservation theorem
are all proved.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Graphplay.Weighted
import Graphplay.Equitable

universe u v w

namespace Graphplay

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The well-defined "cell-to-cell" weight: pick any representative `x` of cell
`i` and sum `G.adj x z` over `z` in cell `j`. The uniformity axiom makes this
independent of the representative — but here we make it total by choosing
`x = Classical.arbitrary` of the cell when nonempty, otherwise `0`. -/
noncomputable def quotientWeight
    (P : EquitablePartition G I) (i j : I) : ℂ :=
  -- Pick a representative of cell `i` if one exists.
  if h : ∃ x : V, P.cells x = i then
    let x := Classical.choose h
    (∑ z, (if P.cells z = j then G.adj x z else 0))
  else 0

/-- The quotient as a packaged **weighted graph** on the cell index `I`.
Distinct from (but related to) `EquitablePartition.quotient : Matrix I I ℂ` in
`Graphplay.Equitable`: this version uses the Hermitian *symmetric*
quotient `Q̃ = D^{1/2} Q D^{-1/2}` (which is the matrix of `G.adj` in the
orthonormal cell-indicator basis, hence spectrum-sharing) and forces the
diagonal to zero so the result is loopless and lives in the `WeightedGraph`
category. -/
noncomputable def quotientGraph
    (P : EquitablePartition G I) : WeightedGraph I where
  adj := fun i j => if i = j then 0 else P.symmQuotient i j
  herm := by
    -- Off the diagonal we inherit Hermiticity from `symmQuotient_isHermitian`;
    -- on the diagonal both entries are zero.
    have hsymm := P.symmQuotient_isHermitian
    ext i j
    show star (if j = i then 0 else P.symmQuotient j i)
        = (if i = j then 0 else P.symmQuotient i j)
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
      exact congrFun (congrFun hsymm i) j
  loopless := by
    intro i
    -- The construction zeroes the diagonal by definition.
    simp

end EquitablePartition

/-! ## 1. The category `WGraph` of weighted graphs.

Objects are bundled pairs of a finite vertex type and a weighted graph on it.
Morphisms are *strict* (isometric) homomorphisms: an injection (eventually) of
vertex types together with strict preservation of the adjacency matrix.

We package finiteness and decidable equality of the underlying vertex type as
instance fields so that the object structure has decidable, finite vertices in
the foreground for spectral content. -/

/-- Bundled weighted graph object: a finite vertex type plus a weighted graph
on it.

The `Type*` lives in universe `u`. The bundle carries instance fields for the
finite vertex type. -/
structure WGraphObj : Type (u + 1) where
  V : Type u
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  G : WeightedGraph V

attribute [instance] WGraphObj.fintypeV WGraphObj.decEqV

namespace WGraphObj

/-- Convenience accessor for the adjacency matrix of a bundled object. -/
def adj (X : WGraphObj.{u}) : Matrix X.V X.V ℂ := X.G.adj

end WGraphObj

/-- Strict weighted-graph homomorphism: a vertex map whose pullback of the
target adjacency matrix is exactly the source adjacency matrix.

This is the right notion of morphism for spectral content: the source spectrum
is a subset of the target spectrum when `f` is injective, since the spectrum of
`G` is recovered as a *principal submatrix* of the spectrum of `H`. -/
structure WGraphHom (X Y : WGraphObj.{u}) : Type u where
  toFun : X.V → Y.V
  adj_preserving : ∀ (a b : X.V), X.adj a b = Y.adj (toFun a) (toFun b)

namespace WGraphHom

@[ext]
theorem ext {X Y : WGraphObj.{u}} {f g : WGraphHom X Y}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have : f = g := funext h
      cases this
      rfl

/-- The identity morphism. -/
def id (X : WGraphObj.{u}) : WGraphHom X X where
  toFun := fun x => x
  adj_preserving := fun _ _ => rfl

/-- Composition. -/
def comp {X Y Z : WGraphObj.{u}} (f : WGraphHom X Y) (g : WGraphHom Y Z) :
    WGraphHom X Z where
  toFun := fun x => g.toFun (f.toFun x)
  adj_preserving := by
    intro a b
    calc X.adj a b
        = Y.adj (f.toFun a) (f.toFun b) := f.adj_preserving a b
      _ = Z.adj (g.toFun (f.toFun a)) (g.toFun (f.toFun b)) :=
          g.adj_preserving (f.toFun a) (f.toFun b)

end WGraphHom

/-- The category structure on weighted graphs. -/
instance WGraphObj.category : CategoryTheory.Category.{u, u + 1} WGraphObj.{u} where
  Hom X Y := WGraphHom X Y
  id X := WGraphHom.id X
  comp f g := WGraphHom.comp f g
  id_comp f := by
    apply WGraphHom.ext
    intro x
    rfl
  comp_id f := by
    apply WGraphHom.ext
    intro x
    rfl
  assoc f g h := by
    apply WGraphHom.ext
    intro x
    rfl

/-- Notation: the category of weighted graphs in universe `u`. -/
abbrev WGraph : Type (u + 1) := WGraphObj.{u}

/-! ## 2. The category `WGraphP` of partitioned weighted graphs.

Objects are a weighted graph object together with an index type and an
equitable partition. Morphisms respect partitions in the sense that there
exists a map of cell-index types making the obvious vertex/cell square commute.
-/

/-- Bundled partitioned weighted graph: a weighted graph object, a finite cell
index type, and an equitable partition. -/
structure WGraphPObj : Type (u + 1) where
  base : WGraphObj.{u}
  I : Type u
  [fintypeI : Fintype I]
  [decEqI : DecidableEq I]
  P : EquitablePartition base.G I

attribute [instance] WGraphPObj.fintypeI WGraphPObj.decEqI

namespace WGraphPObj

/-- Vertex set. -/
abbrev V (X : WGraphPObj.{u}) : Type u := X.base.V

/-- The cell map of the partition. -/
def cells (X : WGraphPObj.{u}) : X.V → X.I := X.P.cells

end WGraphPObj

/-- A morphism of partitioned weighted graphs: a vertex map preserving the
adjacency strictly, together with a cell-index map making the partition square
commute. -/
structure WGraphPHom (X Y : WGraphPObj.{u}) : Type u where
  base : WGraphHom X.base Y.base
  cellMap : X.I → Y.I
  cellMap_comm : ∀ x, cellMap (X.cells x) = Y.cells (base.toFun x)

namespace WGraphPHom

@[ext]
theorem ext {X Y : WGraphPObj.{u}} {f g : WGraphPHom X Y}
    (hbase : ∀ x, f.base.toFun x = g.base.toFun x)
    (hcell : ∀ i, f.cellMap i = g.cellMap i) : f = g := by
  cases f with
  | mk b1 c1 h1 =>
    cases g with
    | mk b2 c2 h2 =>
      have hb : b1 = b2 := by
        apply WGraphHom.ext
        intro x
        exact hbase x
      have hc : c1 = c2 := funext hcell
      cases hb
      cases hc
      rfl

/-- Identity morphism. -/
def id (X : WGraphPObj.{u}) : WGraphPHom X X where
  base := WGraphHom.id X.base
  cellMap := fun i => i
  cellMap_comm := fun _ => rfl

/-- Composition. -/
def comp {X Y Z : WGraphPObj.{u}}
    (f : WGraphPHom X Y) (g : WGraphPHom Y Z) : WGraphPHom X Z where
  base := WGraphHom.comp f.base g.base
  cellMap := fun i => g.cellMap (f.cellMap i)
  cellMap_comm := by
    intro x
    show g.cellMap (f.cellMap (X.cells x))
      = Z.cells (g.base.toFun (f.base.toFun x))
    rw [f.cellMap_comm x, g.cellMap_comm (f.base.toFun x)]

end WGraphPHom

/-- Category structure on partitioned weighted graphs. -/
instance WGraphPObj.category :
    CategoryTheory.Category.{u, u + 1} WGraphPObj.{u} where
  Hom X Y := WGraphPHom X Y
  id X := WGraphPHom.id X
  comp f g := WGraphPHom.comp f g
  id_comp f := by
    apply WGraphPHom.ext <;> intros <;> rfl
  comp_id f := by
    apply WGraphPHom.ext <;> intros <;> rfl
  assoc f g h := by
    apply WGraphPHom.ext <;> intros <;> rfl

abbrev WGraphP : Type (u + 1) := WGraphPObj.{u}

/-! ## 3. The Quotient functor `WGraphP ⥤ WGraph`. -/

namespace Quotient

/-- The image of an object under the quotient functor: the cell type carries
the cell-to-cell weighted graph. -/
noncomputable def obj (X : WGraphPObj.{u}) : WGraphObj.{u} where
  V := X.I
  fintypeV := X.fintypeI
  decEqV := X.decEqI
  G := X.P.quotientGraph

/-- The cell-index component of a morphism preserves the quotient adjacency.

This is a side condition, *not* automatic: the quotient-graph
adjacency `obj.adj` is built from `EquitablePartition.symmQuotient`, which mixes
in the cell *cardinalities* `√|C_i|/√|C_j|`.  A partition-respecting morphism
`f : X ⟶ Y` may merge several `X`-cells into one `Y`-cell (or enlarge a cell on
the `Y` side), changing those cardinalities while `f.base` only preserves the
raw adjacency — so `X.P.quotientGraph.adj i j = Y.P.quotientGraph.adj (cellMap
i) (cellMap j)` *fails* for arbitrary morphisms.  (An explicit
4-vertex/6-vertex counterexample with an injective `f.base` is recorded in the
project notes.)  The condition does hold when `f` is a *quotient morphism*: a
cell-bijective, cardinality-preserving morphism (e.g. an isomorphism of
partitioned graphs, the case relevant to the spectral lift).

We therefore take the preservation as an explicit hypothesis `hpres`, which
directly supplies the `adj_preserving` field of `map`. -/
noncomputable def map {X Y : WGraphPObj.{u}} (f : WGraphPHom X Y)
    (hpres : ∀ i j, (obj X).adj i j = (obj Y).adj (f.cellMap i) (f.cellMap j)) :
    WGraphHom (obj X) (obj Y) where
  toFun := f.cellMap
  adj_preserving := hpres

/-- **Quotient morphism.**  A partition-respecting morphism `f : X ⟶ Y` is a
*quotient morphism* when its cell-index map is injective and matches the two
ingredients of the symmetric quotient — cell cardinalities and raw branching —
on the nose:

  * `cell_inj`     : `f.cellMap` is injective (no two `X`-cells are merged);
  * `card_pres`    : `Y.cellCard (cellMap i) = X.cellCard i` (cardinalities
                     are preserved);
  * `branch_pres`  : `Y.P.quotient (cellMap i) (cellMap j) = X.P.quotient i j`
                     (the raw branching/divisor matrix is preserved).

These are exactly the conditions under which the cardinality-weighted symmetric
quotient `symmQuotient = √|C_i| · Q i j / √|C_j|` is preserved — see
`cellMap_adj_preserving`.  Isomorphisms of partitioned graphs (and, more
generally, cell-bijective cardinality-preserving morphisms — the case relevant
to the spectral lift) are quotient morphisms; arbitrary cell-merging morphisms
are **not** (the merged off-diagonal weight collapses to the loopless diagonal
`0`, while `symmQuotient i j ≠ 0`). -/
structure IsQuotientMorphism {X Y : WGraphPObj.{u}} (f : WGraphPHom X Y) : Prop where
  cell_inj : Function.Injective f.cellMap
  card_pres : ∀ i, Y.P.cellCard (f.cellMap i) = X.P.cellCard i
  branch_pres : ∀ i j, Y.P.quotient (f.cellMap i) (f.cellMap j) = X.P.quotient i j

/-- **The quotient-adjacency-preservation theorem.**

The `IsQuotientMorphism` hypothesis is necessary; the universal statement is
false.  For an arbitrary partition-respecting morphism the symmetric quotient
`symmQuotient` mixes in the cell cardinalities `√|C_i|/√|C_j|`, and a
cell-merging morphism collapses an off-diagonal weight `symmQuotient i j ≠ 0`
to the loopless diagonal `0` of the target quotient — so
`(obj X).adj i j = (obj Y).adj (cellMap i) (cellMap j)` fails (an explicit
4-vertex/6-vertex counterexample with injective `f.base` is recorded in the
project notes).

Under the three `IsQuotientMorphism` conditions (cell-injective,
cardinality-preserving, raw-branching-preserving) both ingredients of
`symmQuotient` (`√|C_i|` and the raw `quotient i j`) transport, and injectivity
aligns the loopless diagonals.  This is exactly what `Quotient.map` consumes. -/
theorem cellMap_adj_preserving {X Y : WGraphPObj.{u}} (f : WGraphPHom X Y)
    (hf : IsQuotientMorphism f) :
    ∀ i j, (obj X).adj i j = (obj Y).adj (f.cellMap i) (f.cellMap j) := by
  intro i j
  -- `(obj X).adj i j = if i = j then 0 else X.P.symmQuotient i j`, and likewise
  -- on the `Y` side with `cellMap i, cellMap j`.
  show (if i = j then 0 else X.P.symmQuotient i j)
      = (if f.cellMap i = f.cellMap j then 0 else Y.P.symmQuotient (f.cellMap i) (f.cellMap j))
  -- Injectivity aligns the diagonal tests: `cellMap i = cellMap j ↔ i = j`.
  have hiff : (f.cellMap i = f.cellMap j) ↔ (i = j) :=
    ⟨fun h => hf.cell_inj h, fun h => by rw [h]⟩
  by_cases hij : i = j
  · rw [if_pos hij, if_pos (hiff.mpr hij)]
  · rw [if_neg hij, if_neg (fun h => hij (hiff.mp h))]
    -- Off the diagonal: transport `symmQuotient` via cardinality + branching.
    unfold EquitablePartition.symmQuotient
    rw [hf.card_pres i, hf.card_pres j, hf.branch_pres i j]

/-- The identity morphism is a quotient morphism (cell map is `id`: injective,
cardinality- and branching-preserving on the nose). -/
theorem isQuotientMorphism_id (X : WGraphPObj.{u}) :
    IsQuotientMorphism (WGraphPHom.id X) where
  cell_inj := Function.injective_id
  card_pres := fun _ => rfl
  branch_pres := fun _ _ => rfl

/-- Quotient morphisms are closed under composition. -/
theorem isQuotientMorphism_comp {X Y Z : WGraphPObj.{u}}
    {f : WGraphPHom X Y} {g : WGraphPHom Y Z}
    (hf : IsQuotientMorphism f) (hg : IsQuotientMorphism g) :
    IsQuotientMorphism (WGraphPHom.comp f g) where
  cell_inj := by
    -- `(comp f g).cellMap = g.cellMap ∘ f.cellMap`.
    intro a b hab
    exact hf.cell_inj (hg.cell_inj hab)
  card_pres := fun i => by
    show Z.P.cellCard (g.cellMap (f.cellMap i)) = X.P.cellCard i
    rw [hg.card_pres (f.cellMap i), hf.card_pres i]
  branch_pres := fun i j => by
    show Z.P.quotient (g.cellMap (f.cellMap i)) (g.cellMap (f.cellMap j))
        = X.P.quotient i j
    rw [hg.branch_pres (f.cellMap i) (f.cellMap j), hf.branch_pres i j]

end Quotient

/-! ### The quotient-morphism (wide) subcategory `WGraphPQ`.

The quotient-graph adjacency `Quotient.obj.adj` is cardinality-weighted
(`symmQuotient = √|C_i|·Q i j/√|C_j|`), so a *general* partition-respecting
morphism does **not** preserve it (cell-merging collapses an off-diagonal weight
to the loopless diagonal `0`) — see `Quotient.cellMap_adj_preserving`.  The
domain on which the cell-quotient is a strict (adjacency-preserving)
functor is therefore the **wide subcategory of quotient morphisms**: same
objects as `WGraphP`, but only the `IsQuotientMorphism` maps (cell-injective,
cardinality- and branching-preserving).

`WGraphPQ` is *definitionally* `WGraphPObj`, so the cell-quotient object map
`Quotient.obj`/`Quotient.{u}.obj` still applies to bare `WGraphPObj` values (as
used downstream in `LiftablePrimitive`, `TransformerDSL`, `TensorNetworks`). -/
def WGraphPQ : Type (u + 1) := WGraphPObj.{u}

/-- Category structure on the quotient-morphism subcategory: objects are
partitioned weighted graphs, morphisms are quotient morphisms (the
`IsQuotientMorphism` subtype of `WGraphPHom`). -/
instance WGraphPQ.category : CategoryTheory.Category.{u, u + 1} WGraphPQ.{u} where
  Hom (X Y : WGraphPObj.{u}) := { f : WGraphPHom X Y // Quotient.IsQuotientMorphism f }
  id X := ⟨WGraphPHom.id X, Quotient.isQuotientMorphism_id X⟩
  comp f g := ⟨WGraphPHom.comp f.1 g.1, Quotient.isQuotientMorphism_comp f.2 g.2⟩
  id_comp f := by
    apply Subtype.ext; apply WGraphPHom.ext <;> intros <;> rfl
  comp_id f := by
    apply Subtype.ext; apply WGraphPHom.ext <;> intros <;> rfl
  assoc f g h := by
    apply Subtype.ext; apply WGraphPHom.ext <;> intros <;> rfl

/-- **The Quotient functor** on the quotient-morphism subcategory `WGraphPQ`.
Sends `(G, P)` to the cell-to-cell weighted graph on the index type, and a
*quotient* morphism to the induced cell-index map.

The action on a morphism is `Quotient.map f.1` fed the quotient-adjacency
preservation `Quotient.cellMap_adj_preserving f.1 f.2`, which holds precisely
because `f.2 : IsQuotientMorphism f.1`.
Functoriality (`map_id`, `map_comp`) is on the nose at the `toFun = cellMap`
data level. -/
noncomputable def Quotient : CategoryTheory.Functor WGraphPQ.{u} WGraphObj.{u} where
  obj := Quotient.obj
  map f := Quotient.map f.1 (Quotient.cellMap_adj_preserving f.1 f.2)
  map_id := by
    intro X
    apply WGraphHom.ext
    intro i
    rfl
  map_comp := by
    intro X Y Z f g
    apply WGraphHom.ext
    intro i
    rfl

/-! ## 4. Coproducts and filtered colimits in `WGraph`. -/

namespace WGraph

open CategoryTheory CategoryTheory.Limits

/-- The disjoint-union weighted graph: vertices are `Σ i, V_i`, adjacency is
zero across components and inherited within a component.

This is the Tower-2 (weighted) analogue of `SigmaGraph` from `Basic.lean`. -/
noncomputable def WSigmaGraph
    {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, WeightedGraph (V i)) : WeightedGraph (Σ i, V i) where
  adj := fun x y =>
    if h : x.1 = y.1 then (G x.1).adj x.2 (h ▸ y.2) else 0
  herm := by
    ext x y
    show star (if h : y.1 = x.1 then (G y.1).adj y.2 (h ▸ x.2) else 0)
        = (if h : x.1 = y.1 then (G x.1).adj x.2 (h ▸ y.2) else 0)
    obtain ⟨xi, xv⟩ := x
    obtain ⟨yi, yv⟩ := y
    by_cases h : xi = yi
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
      -- Reduce to a single component; use Hermiticity of `G xi`.
      have := (G xi).herm
      exact congrFun (congrFun this xv) yv
    · rw [dif_neg h, dif_neg (fun hc => h hc.symm), star_zero]
  loopless := by
    intro v
    -- Within a single component, the diagonal is zero.
    show (if h : v.1 = v.1 then (G v.1).adj v.2 (h ▸ v.2) else 0) = 0
    rw [dif_pos rfl]
    simp only []
    exact (G v.1).loopless v.2

/-- Bundle the family of weighted graphs into a family of `WGraphObj`. -/
noncomputable def famObj
    {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, WeightedGraph (V i)) (i : I) : WGraphObj.{u} where
  V := V i
  fintypeV := inferInstance
  decEqV := inferInstance
  G := G i

/-- Bundle the disjoint-union weighted graph as a `WGraphObj`. -/
noncomputable def sigmaObj
    {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, WeightedGraph (V i)) : WGraphObj.{u} where
  V := Σ i, V i
  fintypeV := inferInstance
  decEqV := inferInstance
  G := WSigmaGraph V G

/-- Inclusion of component `i` into the disjoint union. -/
noncomputable def sigmaInclusion
    {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, WeightedGraph (V i)) (i : I) :
    WGraphHom (famObj V G i) (sigmaObj V G) where
  toFun := fun x => ⟨i, x⟩
  adj_preserving := by
    intro a b
    -- Within one component the disjoint-union adjacency restricts to the
    -- component adjacency.
    show (G i).adj a b
        = (if h : i = i then (G i).adj a (h ▸ b) else 0)
    rw [dif_pos rfl]

/-- Universal property of disjoint union: a family of strict morphisms out of
the components assembles into one strict morphism out of the disjoint union.
This is the data of a cocone, and we will package it as `IsColimit` for an
appropriate diagram in the category `WGraph` below.

The cross-component independence condition `hindep` is a necessary side
condition on the family `f`: the coproduct in `WGraph` (whose morphisms
strictly preserve the *whole* adjacency matrix, including the zero
off-diagonal blocks of the disjoint union) only absorbs families whose images
in `H` carry no `H`-edges between distinct components.  (For an actual
disjoint union — `H = sigmaObj V G` with `f i = sigmaInclusion`, or any
`H` into which the components embed with edge-disjoint images — `hindep` holds
on the nose; see `sigmaDesc_sigmaObj`.) -/
noncomputable def sigmaDesc
    {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, WeightedGraph (V i))
    {H : WGraphObj.{u}}
    (f : ∀ i, WGraphHom (famObj V G i) H)
    (hindep : ∀ (i i' : I), i ≠ i' →
      ∀ (x : V i) (y : V i'), H.adj ((f i).toFun x) ((f i').toFun y) = 0) :
    WGraphHom (sigmaObj V G) H where
  toFun := fun x => (f x.1).toFun x.2
  adj_preserving := by
    intro a b
    -- Adjacency in the disjoint-union splits by component.  In the
    -- same-component case equality is exactly `H`'s strict preservation under
    -- the component map; the cross-component case is `hindep`.
    show (if h : a.1 = b.1 then (G a.1).adj a.2 (h ▸ b.2) else 0)
        = H.adj ((f a.1).toFun a.2) ((f b.1).toFun b.2)
    by_cases h : a.1 = b.1
    · rw [dif_pos h]
      -- Same component: reduce to `(f a.1).adj_preserving`.
      obtain ⟨ai, av⟩ := a
      obtain ⟨bi, bv⟩ := b
      cases h
      exact (f ai).adj_preserving av bv
    · rw [dif_neg h]
      -- Cross-component: the images carry no `H`-edge by `hindep`.
      exact (hindep a.1 b.1 h a.2 b.2).symm

/-- For the disjoint union `H = sigmaObj V G` with the canonical
inclusions, the cross-component independence hypothesis of `sigmaDesc` holds
automatically: the disjoint-union adjacency is zero across components by
construction. -/
theorem sigmaInclusion_indep
    {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, WeightedGraph (V i)) (i i' : I) (h : i ≠ i')
    (x : V i) (y : V i') :
    (sigmaObj V G).adj ((sigmaInclusion V G i).toFun x)
        ((sigmaInclusion V G i').toFun y) = 0 := by
  show (if hh : i = i' then (G i).adj x (hh ▸ y) else 0) = 0
  rw [dif_neg h]

/-- **Universal property of the disjoint union (factorization form).**

`sigmaDesc f hindep` is a factorization of the cocone given by the
family `f` through the inclusions: composing each inclusion
`sigmaInclusion V G i` with `sigmaDesc V G f hindep` recovers `f i` on the
nose. This is the existence half of the coproduct universal property;
uniqueness is `sigmaDesc_unique`. -/
theorem sigmaInclusion_comp_sigmaDesc
    {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, WeightedGraph (V i))
    {H : WGraphObj.{u}}
    (f : ∀ i, WGraphHom (famObj V G i) H)
    (hindep : ∀ (i i' : I), i ≠ i' →
      ∀ (x : V i) (y : V i'), H.adj ((f i).toFun x) ((f i').toFun y) = 0)
    (i : I) :
    WGraphHom.comp (sigmaInclusion V G i) (sigmaDesc V G f hindep) = f i := by
  apply WGraphHom.ext
  intro x
  rfl

/-- **Uniqueness half of the coproduct universal property.** Any strict
morphism `g` out of the disjoint union whose restriction along every inclusion
equals `f i` agrees with `sigmaDesc V G f hindep` everywhere. -/
theorem sigmaDesc_unique
    {I : Type u} [Fintype I] [DecidableEq I]
    (V : I → Type u) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (G : ∀ i, WeightedGraph (V i))
    {H : WGraphObj.{u}}
    (f : ∀ i, WGraphHom (famObj V G i) H)
    (hindep : ∀ (i i' : I), i ≠ i' →
      ∀ (x : V i) (y : V i'), H.adj ((f i).toFun x) ((f i').toFun y) = 0)
    (g : WGraphHom (sigmaObj V G) H)
    (hg : ∀ i, WGraphHom.comp (sigmaInclusion V G i) g = f i) :
    g = sigmaDesc V G f hindep := by
  apply WGraphHom.ext
  intro x
  obtain ⟨i, v⟩ := x
  have := congrArg (fun (m : WGraphHom (famObj V G i) H) => m.toFun v) (hg i)
  simpa [WGraphHom.comp, sigmaInclusion, sigmaDesc] using this

/-! ### Filtered colimits via `UnionGraph`.

The classical "staged union" of an increasing chain of weighted graphs on a
common vertex set is the colimit of the chain in `WGraph`. We frame it via the
natural-number poset (a filtered category) and assert that the chain colimit
exists.

For the categorical scaffold the actual colimit construction is deferred —
the simple-graph Tower-1 version in `Basic.lean` is the `Bijection`-based
universal property, which is the baby case of the colimit cocone here. -/

/-- Diagram from `ℕ` (as a thin category with arrows `n ⟶ n+1` extending by
composition) into `WGraph`. We assume the underlying vertex type is shared
across stages, modeled by `WGraphObj` whose `V` is a fixed type and whose `G`
varies as `n ↑ ∞`. -/
structure WGraphChain : Type (u + 1) where
  obj : ℕ → WGraphObj.{u}
  inc : ∀ n, WGraphHom (obj n) (obj (n + 1))

/-- The chain `D` as an actual functor `ℕ ⥤ WGraph`, using Mathlib's
`Functor.ofSequence`. -/
noncomputable def WGraphChain.toFunctor (D : WGraphChain.{u}) :
    CategoryTheory.Functor ℕ WGraphObj.{u} :=
  CategoryTheory.Functor.ofSequence (X := D.obj) D.inc

/-- The filtered colimit of a chain in `WGraph`, defined as the Mathlib
`colimit` of the corresponding `ℕ`-shaped diagram.

This requires the `HasColimit` instance on the chain functor (filtered colimits
of weighted graphs in general can outgrow the `Fintype` constraint on
`WGraphObj`, so we leave this as a hypothesis to be supplied at use sites). -/
noncomputable def chainColimit
    (D : WGraphChain.{u}) [HasColimit D.toFunctor] : WGraphObj.{u} :=
  colimit D.toFunctor

/-- The colimit cocone of the chain functor. -/
noncomputable def chainColimit.cocone
    (D : WGraphChain.{u}) [HasColimit D.toFunctor] :
    Cocone D.toFunctor :=
  colimit.cocone D.toFunctor

/-- **The chain colimit is the colimit** — the real `IsColimit` data, supplied
by Mathlib's `colimit.isColimit`. This corresponds to `UnionGraph.homBijection`
in `Basic.lean` for the simple-graph case. -/
noncomputable def chainColimit_isColimit
    (D : WGraphChain.{u}) [HasColimit D.toFunctor] :
    IsColimit (chainColimit.cocone D) :=
  colimit.isColimit D.toFunctor

end WGraph

/-! ## 5. Cofiltered limits and `InverseLimitGraph`. -/

namespace WGraph

open CategoryTheory CategoryTheory.Limits

/-- A cofiltered system: a sequence of objects and *bonding maps* going
`obj (n+1) ⟶ obj n`. -/
structure WGraphCochain : Type (u + 1) where
  obj : ℕ → WGraphObj.{u}
  bond : ∀ n, WGraphHom (obj (n + 1)) (obj n)

/-- The cochain `D` as a functor `ℕᵒᵖ ⥤ WGraph`, using Mathlib's
`Functor.ofOpSequence`. -/
noncomputable def WGraphCochain.toFunctor (D : WGraphCochain.{u}) :
    CategoryTheory.Functor ℕᵒᵖ WGraphObj.{u} :=
  CategoryTheory.Functor.ofOpSequence (X := D.obj) D.bond

/-- The cofiltered limit of a cochain, defined as the Mathlib `limit` of the
corresponding `ℕᵒᵖ`-shaped diagram. -/
noncomputable def cochainLimit
    (D : WGraphCochain.{u}) [HasLimit D.toFunctor] : WGraphObj.{u} :=
  limit D.toFunctor

/-- The limit cone of the cochain functor. -/
noncomputable def cochainLimit.cone
    (D : WGraphCochain.{u}) [HasLimit D.toFunctor] :
    Cone D.toFunctor :=
  limit.cone D.toFunctor

/-- **The cochain limit is a (cofiltered) limit** — the real `IsLimit` data,
supplied by Mathlib's `limit.isLimit`. This corresponds to `InverseLimitGraph`
in `Basic.lean`. -/
noncomputable def cochainLimit_isLimit
    (D : WGraphCochain.{u}) [HasLimit D.toFunctor] :
    IsLimit (cochainLimit.cone D) :=
  limit.isLimit D.toFunctor

end WGraph

/-! ## 6. Headline categorical theorems.

### The Quotient functor preserves filtered colimits.

In categorical terms: the cell-quotient of a directed/filtered union of
partitioned weighted graphs is the directed/filtered union of the cell-quotients.

This is the **universal form** of the Xie–Tamon "no infinite tail beats
optimality" theorem, with the natural-number diagram of `K_n + path-n`
partitioned by distance from the attachment as a special case. -/

open CategoryTheory CategoryTheory.Limits

/-! ### Cell restriction: the test object behind filtered-colimit preservation.

The engine of `Quotient.preservesFilteredColimits` is a counting argument.
Every leg of a cocone in `WGraphPQ` is a quotient morphism, so its cell map is
injective, and the cell counts of a diagram admitting a cocone are bounded by
the (finite) cell count of the cocone vertex.  Pick `j₀` of maximal cell
count.  Filteredness forces the cell image of every leg of a colimit cocone
`c` into the cell image `U` of the leg at `j₀`; the cells of `U`, taken
*whole*, induce a partitioned weighted graph `c.pt.restrictCells U` — all
branching sums, cell cardinalities and quotient entries are untouched — and it
is the vertex of a competing cocone over the same diagram.  The descent
morphism supplied by the universal property has an injective cell map
`c.pt.I → U`, so the colimit vertex carries no surplus cells:
`(c.ι.app j₀).cellMap` is a bijection (`Quotient.exists_bijective_leg`), and
the colimit property of the mapped cocone follows directly. -/

section RestrictCells

variable (X : WGraphPObj.{u}) (U : Finset X.I)

/-- Cell-local sums in the restriction agree with cell-local sums in the
ambient graph: a `U`-cell survives the restriction *whole*. -/
private theorem WGraphPObj.restrictCells_sum_aux (j : X.I) (hj : j ∈ U) (x : X.V) :
    (∑ z : {v : X.V // X.cells v ∈ U},
        (if (⟨X.cells z.1, z.2⟩ : {i : X.I // i ∈ U}) = ⟨j, hj⟩
          then X.base.G.adj x z.1 else 0))
      = ∑ z, (if X.cells z = j then X.base.G.adj x z else 0) := by
  have h1 : ∀ z : {v : X.V // X.cells v ∈ U},
      (if (⟨X.cells z.1, z.2⟩ : {i : X.I // i ∈ U}) = ⟨j, hj⟩
        then X.base.G.adj x z.1 else 0)
      = (if X.cells z.1 = j then X.base.G.adj x z.1 else 0) := by
    intro z
    by_cases h : X.cells z.1 = j
    · rw [if_pos h, if_pos (Subtype.ext h)]
    · rw [if_neg h, if_neg (fun hc => h (congrArg Subtype.val hc))]
  calc (∑ z : {v : X.V // X.cells v ∈ U},
          (if (⟨X.cells z.1, z.2⟩ : {i : X.I // i ∈ U}) = ⟨j, hj⟩
            then X.base.G.adj x z.1 else 0))
      = ∑ z : {v : X.V // X.cells v ∈ U},
          (if X.cells z.1 = j then X.base.G.adj x z.1 else 0) :=
        Finset.sum_congr rfl (fun z _ => h1 z)
    _ = ∑ z ∈ Finset.univ.filter (fun v : X.V => X.cells v ∈ U),
          (if X.cells z = j then X.base.G.adj x z else 0) :=
        (Finset.sum_subtype (Finset.univ.filter (fun v : X.V => X.cells v ∈ U))
          (fun v => by simp) (fun z => if X.cells z = j then X.base.G.adj x z else 0)).symm
    _ = ∑ z, (if X.cells z = j then X.base.G.adj x z else 0) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro z _ hz
        have hzj : X.cells z ≠ j := fun hcz =>
          hz (Finset.mem_filter.mpr ⟨Finset.mem_univ z, by rw [hcz]; exact hj⟩)
        rw [if_neg hzj]

/-- **Cell restriction.**  The partitioned weighted graph induced on the union
of the cells of `X` indexed by `U`.  Cells are taken whole, so equitability is
inherited and every branching sum, cell cardinality and quotient entry over `U`
agrees with that of `X` (`restrictCells_cellCard`, `restrictCells_quotient`). -/
noncomputable def WGraphPObj.restrictCells : WGraphPObj.{u} where
  base :=
    { V := {v : X.V // X.cells v ∈ U}
      G :=
        { adj := fun a b => X.base.G.adj a.1 b.1
          herm := by
            ext a b
            show star (X.base.G.adj b.1 a.1) = X.base.G.adj a.1 b.1
            exact X.base.G.herm.apply a.1 b.1
          loopless := fun v => X.base.G.loopless v.1 } }
  I := {i : X.I // i ∈ U}
  P :=
    { cells := fun v => ⟨X.cells v.1, v.2⟩
      uniform := by
        rintro ⟨i, hi⟩ ⟨j, hj⟩ x y hx hy
        have hx' : X.cells x.1 = i := congrArg Subtype.val hx
        have hy' : X.cells y.1 = i := congrArg Subtype.val hy
        calc (∑ z : {v : X.V // X.cells v ∈ U},
                (if (⟨X.cells z.1, z.2⟩ : {i' : X.I // i' ∈ U}) = ⟨j, hj⟩
                  then X.base.G.adj x.1 z.1 else 0))
            = ∑ z, (if X.cells z = j then X.base.G.adj x.1 z else 0) :=
              WGraphPObj.restrictCells_sum_aux X U j hj x.1
          _ = ∑ z, (if X.cells z = j then X.base.G.adj y.1 z else 0) :=
              X.P.uniform i j x.1 y.1 hx' hy'
          _ = ∑ z : {v : X.V // X.cells v ∈ U},
                (if (⟨X.cells z.1, z.2⟩ : {i' : X.I // i' ∈ U}) = ⟨j, hj⟩
                  then X.base.G.adj y.1 z.1 else 0) :=
              (WGraphPObj.restrictCells_sum_aux X U j hj y.1).symm }

/-- Restriction preserves the cardinality of every surviving cell. -/
theorem WGraphPObj.restrictCells_cellCard (i : X.I) (hi : i ∈ U) :
    (X.restrictCells U).P.cellCard ⟨i, hi⟩ = X.P.cellCard i := by
  have hcard :
      (Finset.univ.filter
          (fun w : (X.restrictCells U).V =>
            (X.restrictCells U).P.cells w = ⟨i, hi⟩)).card
        = (Finset.univ.filter (fun w : X.V => X.P.cells w = i)).card := by
    apply Finset.card_bij (fun (a : (X.restrictCells U).V) _ => a.1)
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, congrArg Subtype.val ha.2⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro b hb
      rw [Finset.mem_filter] at hb
      refine ⟨⟨b, ?_⟩, ?_, rfl⟩
      · show X.cells b ∈ U
        rw [show X.cells b = i from hb.2]
        exact hi
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Subtype.ext hb.2⟩
  exact congrArg (fun n : ℕ => (n : ℝ)) hcard

/-- Restriction preserves every quotient (branching) entry over surviving
cells: the branching sums range over whole cells, all of which survive. -/
theorem WGraphPObj.restrictCells_quotient (i j : X.I) (hi : i ∈ U) (hj : j ∈ U) :
    (X.restrictCells U).P.quotient ⟨i, hi⟩ ⟨j, hj⟩ = X.P.quotient i j := by
  by_cases hex : ∃ x : X.V, X.P.cells x = i
  · obtain ⟨x, hx⟩ := hex
    have hxU : X.cells x ∈ U := by
      show X.P.cells x ∈ U
      rw [hx]; exact hi
    have hxZ : (X.restrictCells U).P.cells ⟨x, hxU⟩ = ⟨i, hi⟩ := Subtype.ext hx
    rw [EquitablePartition.quotient_apply (X.restrictCells U).P ⟨i, hi⟩ ⟨j, hj⟩
        ⟨x, hxU⟩ hxZ,
      EquitablePartition.quotient_apply X.P i j x hx]
    show (∑ z : {v : X.V // X.cells v ∈ U},
        (if (⟨X.cells z.1, z.2⟩ : {i' : X.I // i' ∈ U}) = ⟨j, hj⟩
          then X.base.G.adj x z.1 else 0))
      = ∑ z, (if X.cells z = j then X.base.G.adj x z else 0)
    exact WGraphPObj.restrictCells_sum_aux X U j hj x
  · have hexZ : ¬∃ xZ : (X.restrictCells U).V,
        (X.restrictCells U).P.cells xZ = ⟨i, hi⟩ := by
      rintro ⟨xZ, hxZ⟩
      exact hex ⟨xZ.1, congrArg Subtype.val hxZ⟩
    unfold EquitablePartition.quotient
    rw [dif_neg hexZ, dif_neg hex]

end RestrictCells

/-- Pointwise cell-map form of the cocone commutation law in `WGraphPQ`. -/
theorem Quotient.cocone_cellMap_eq {J : Type u} [Category.{u} J]
    (K : Functor J WGraphPQ.{u}) (c : Cocone K) {a b : J} (u : a ⟶ b)
    (i : (K.obj a).I) :
    (c.ι.app a).1.cellMap i = (c.ι.app b).1.cellMap ((K.map u).1.cellMap i) :=
  (congrArg (fun (f : K.obj a ⟶ c.pt) => f.1.cellMap i) (c.w u)).symm

/-- **A colimit vertex in `WGraphPQ` carries no surplus cells.**  For a
filtered diagram of quotient morphisms with a colimit cocone, the leg at any
object of maximal cell count has a *bijective* cell map: every leg's cell image
lands in its image `U` (filteredness plus injectivity of quotient-morphism cell
maps), the cells of `U` assemble into the restricted vertex
`c.pt.restrictCells U` of a competing cocone, and the descent morphism's
injective cell map pins `Fintype.card c.pt.I` down to `U.card`. -/
theorem Quotient.exists_bijective_leg {J : Type u} [Category.{u} J] [IsFiltered J]
    (K : Functor J WGraphPQ.{u}) (c : Cocone K) (hc : IsColimit c) :
    ∃ j₀ : J, Function.Bijective (c.ι.app j₀).1.cellMap := by
  classical
  haveI : Nonempty J := IsFiltered.nonempty
  -- A maximizer of the (bounded) cell counts.
  obtain ⟨j₀, hj₀⟩ :
      ∃ j₀ : J, ∀ j : J, Fintype.card (K.obj j).I ≤ Fintype.card (K.obj j₀).I := by
    have hbdd : BddAbove (Set.range fun j : J => Fintype.card (K.obj j).I) :=
      ⟨Fintype.card c.pt.I, by
        rintro x ⟨j, rfl⟩
        exact Fintype.card_le_of_injective _ (c.ι.app j).2.cell_inj⟩
    obtain ⟨j₀, hj₀⟩ :=
      Nat.sSup_mem (Set.range_nonempty fun j : J => Fintype.card (K.obj j).I) hbdd
    refine ⟨j₀, fun j => ?_⟩
    have h1 : Fintype.card (K.obj j).I
        ≤ sSup (Set.range fun j : J => Fintype.card (K.obj j).I) :=
      le_csSup hbdd ⟨j, rfl⟩
    have h2 : Fintype.card (K.obj j₀).I
        = sSup (Set.range fun j : J => Fintype.card (K.obj j).I) := hj₀
    omega
  -- Every leg's cell image factors through the leg at `j₀`.
  have hsub : ∀ (j : J) (i : (K.obj j).I),
      ∃ i₀ : (K.obj j₀).I,
        (c.ι.app j).1.cellMap i = (c.ι.app j₀).1.cellMap i₀ := by
    intro j i
    have hinj : Function.Injective (K.map (IsFiltered.leftToMax j₀ j)).1.cellMap :=
      (K.map (IsFiltered.leftToMax j₀ j)).2.cell_inj
    have hcards : Fintype.card (K.obj j₀).I
        = Fintype.card (K.obj (IsFiltered.max j₀ j)).I :=
      le_antisymm (Fintype.card_le_of_injective _ hinj) (hj₀ _)
    have hbij : Function.Bijective (K.map (IsFiltered.leftToMax j₀ j)).1.cellMap :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcards⟩
    obtain ⟨i₀, hi₀⟩ := hbij.2 ((K.map (IsFiltered.rightToMax j₀ j)).1.cellMap i)
    refine ⟨i₀, ?_⟩
    rw [Quotient.cocone_cellMap_eq K c (IsFiltered.rightToMax j₀ j) i, ← hi₀,
      ← Quotient.cocone_cellMap_eq K c (IsFiltered.leftToMax j₀ j) i₀]
  -- The restricted competing cocone.
  let U : Finset c.pt.I := Finset.univ.image (c.ι.app j₀).1.cellMap
  have hmem : ∀ (j : J) (i : (K.obj j).I), (c.ι.app j).1.cellMap i ∈ U := by
    intro j i
    obtain ⟨i₀, h⟩ := hsub j i
    rw [h]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i₀)
  have hbase_mem : ∀ (j : J) (x : (K.obj j).base.V),
      c.pt.cells ((c.ι.app j).1.base.toFun x) ∈ U := by
    intro j x
    have h : (c.ι.app j).1.cellMap ((K.obj j).cells x)
        = c.pt.cells ((c.ι.app j).1.base.toFun x) := (c.ι.app j).1.cellMap_comm x
    rw [← h]
    exact hmem j _
  let d : Cocone K :=
    { pt := c.pt.restrictCells U
      ι :=
        { app := fun j =>
            ⟨{ base :=
                { toFun := fun x => ⟨(c.ι.app j).1.base.toFun x, hbase_mem j x⟩
                  adj_preserving := fun a b => (c.ι.app j).1.base.adj_preserving a b }
               cellMap := fun i => ⟨(c.ι.app j).1.cellMap i, hmem j i⟩
               cellMap_comm := fun x => Subtype.ext ((c.ι.app j).1.cellMap_comm x) },
             ⟨fun a b hab => (c.ι.app j).2.cell_inj (congrArg Subtype.val hab),
              fun i => (c.pt.restrictCells_cellCard U _ (hmem j i)).trans
                ((c.ι.app j).2.card_pres i),
              fun i i' => (c.pt.restrictCells_quotient U _ _ (hmem j i) (hmem j i')).trans
                ((c.ι.app j).2.branch_pres i i')⟩⟩
          naturality := fun a b u => Subtype.ext (WGraphPHom.ext
            (fun x => Subtype.ext
              (congrArg (fun (f : K.obj a ⟶ c.pt) => f.1.base.toFun x) (c.w u)))
            (fun i => Subtype.ext
              (congrArg (fun (f : K.obj a ⟶ c.pt) => f.1.cellMap i) (c.w u)))) } }
  -- Counting via the descent morphism: no surplus cells.
  have hcount : Fintype.card c.pt.I ≤ Fintype.card (K.obj j₀).I := by
    calc Fintype.card c.pt.I
        ≤ Fintype.card (c.pt.restrictCells U).I :=
          Fintype.card_le_of_injective _ (hc.desc d).2.cell_inj
      _ = U.card := Fintype.card_of_subtype U (fun _ => Iff.rfl)
      _ = Finset.univ.card :=
          Finset.card_image_of_injective _ (c.ι.app j₀).2.cell_inj
      _ = Fintype.card (K.obj j₀).I := Finset.card_univ
  exact ⟨j₀, (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨(c.ι.app j₀).2.cell_inj,
      le_antisymm (Fintype.card_le_of_injective _ (c.ι.app j₀).2.cell_inj) hcount⟩⟩

/-- **The Quotient functor preserves filtered colimits** — the `IsColimit`
data: the cell-quotient of a filtered colimit of partitioned weighted graphs
(over the quotient-morphism subcategory `WGraphPQ`) is the filtered colimit of
the cell-quotients.

This is the categorical heart of the spectral story: passing to a filtered
colimit (e.g. taking a "long enough" tail of cells) commutes with quotienting
out a partition, so no infinite tail can do strictly better than a finite
truncation.

Proof shape: by `Quotient.exists_bijective_leg` some leg `c.ι.app j₀` has a
bijective cell map, so `Quotient.map` sends it to an isomorphism of weighted
graphs (cardinality- and branching-preservation transport the symmetric
quotient along the bijection).  Descent through the inverse of that
isomorphism, with the factorization law supplied by filteredness (`max`,
`leftToMax`, `rightToMax`) and uniqueness by surjectivity of the leg. -/
noncomputable def Quotient.mapCocone_isColimit
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (K : Functor J WGraphPQ.{u}) (c : Cocone K) (hc : IsColimit c) :
    IsColimit ((Quotient.{u}).mapCocone c) :=
  let hex := Quotient.exists_bijective_leg K c hc
  let j₀ : J := hex.choose
  let e : (K.obj j₀).I ≃ c.pt.I := Equiv.ofBijective _ hex.choose_spec
  let ginv : WGraphHom (Quotient.obj c.pt) (Quotient.obj (K.obj j₀)) :=
    { toFun := e.symm
      adj_preserving := fun a b => by
        have h : (Quotient.obj (K.obj j₀)).adj (e.symm a) (e.symm b)
            = (Quotient.obj c.pt).adj ((c.ι.app j₀).1.cellMap (e.symm a))
                ((c.ι.app j₀).1.cellMap (e.symm b)) :=
          Quotient.cellMap_adj_preserving (c.ι.app j₀).1 (c.ι.app j₀).2
            (e.symm a) (e.symm b)
        rw [h, show (c.ι.app j₀).1.cellMap (e.symm a) = a from e.apply_symm_apply a,
          show (c.ι.app j₀).1.cellMap (e.symm b) = b from e.apply_symm_apply b] }
  { desc := fun s => WGraphHom.comp ginv (s.ι.app j₀)
    fac := fun s j => by
      apply WGraphHom.ext
      intro x
      show (s.ι.app j₀).toFun (e.symm ((c.ι.app j).1.cellMap x)) = (s.ι.app j).toFun x
      have hsw : ∀ {a b : J} (u : a ⟶ b) (i : (K.obj a).I),
          (s.ι.app a).toFun i = (s.ι.app b).toFun ((K.map u).1.cellMap i) :=
        fun u i => (congrArg
          (fun (f : (K ⋙ Quotient.{u}).obj _ ⟶ s.pt) => f.toFun i) (s.w u)).symm
      have hkey : (K.map (IsFiltered.leftToMax j₀ j)).1.cellMap
            (e.symm ((c.ι.app j).1.cellMap x))
          = (K.map (IsFiltered.rightToMax j₀ j)).1.cellMap x := by
        apply (c.ι.app (IsFiltered.max j₀ j)).2.cell_inj
        rw [← Quotient.cocone_cellMap_eq K c (IsFiltered.leftToMax j₀ j),
          ← Quotient.cocone_cellMap_eq K c (IsFiltered.rightToMax j₀ j)]
        exact e.apply_symm_apply ((c.ι.app j).1.cellMap x)
      rw [hsw (IsFiltered.leftToMax j₀ j) (e.symm ((c.ι.app j).1.cellMap x)), hkey,
        ← hsw (IsFiltered.rightToMax j₀ j) x]
    uniq := fun s m w => by
      apply WGraphHom.ext
      intro i
      show m.toFun i = (s.ι.app j₀).toFun (e.symm i)
      calc m.toFun i
          = m.toFun ((c.ι.app j₀).1.cellMap (e.symm i)) := by
            rw [show (c.ι.app j₀).1.cellMap (e.symm i) = i from e.apply_symm_apply i]
        _ = (s.ι.app j₀).toFun (e.symm i) :=
            congrArg (fun (f : (K ⋙ Quotient.{u}).obj j₀ ⟶ s.pt) =>
              f.toFun (e.symm i)) (w j₀) }

instance Quotient.preservesFilteredColimits :
    Limits.PreservesFilteredColimits (Quotient.{u}) :=
  ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} hc =>
    ⟨Quotient.mapCocone_isColimit K c hc⟩⟩⟩⟩

/-- **Corollary (universal form of "no infinite tail beats optimality").**

For any filtered diagram `D : I ⥤ WGraphPQ` (a diagram of *quotient morphisms* of
partitioned weighted graphs), the quotient of the colimit is canonically
isomorphic to the colimit of the pointwise quotients.

This is the categorical version of Xie–Tamon's result that taking an infinite
tail of `K_n + path-n` cannot strictly improve over the best finite truncation:
the partition quotient (which records the spectral content) commutes with the
limiting procedure.

This is a one-liner via Mathlib's `preservesColimitIso`, using the
`Quotient.preservesFilteredColimits` instance above (over the quotient-morphism
subcategory `WGraphPQ`). -/
noncomputable def quasi_infinite_limit
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (D : Functor I WGraphPQ.{u})
    [HasColimit D] [HasColimit (D ⋙ Quotient.{u})] :
    Quotient.{u}.obj (colimit D) ≅ colimit (D ⋙ Quotient.{u}) :=
  preservesColimitIso (Quotient.{u}) D

/-! ## 7. Lift theorem in categorical form.

A "primitive" is a property of weighted graphs that lifts through the Quotient
functor: if it holds of the quotient (i.e. the cell-level dynamics) then it
lifts to a *cell-uniform* refinement on the original.

We model a primitive as a natural transformation `IsPrimitive : Quotient.op ⥹ Prop`,
meaning: a contravariantly natural assignment of a `Prop` along the Quotient
functor. The condition "lifts to cell-uniform states" is the universal lifting
property along `Quotient`.

Three concrete instances we want to subsume eventually:
  * **PST (perfect state transfer)**: a primitive on the cell-quotient lifts
    to a uniform PST on cell-symmetric input states;
  * **Mixing time**: bounds on the cell-quotient mixing time lift to bounds on
    cell-symmetric mixing;
  * **Search**: Grover-type search on the cell-quotient lifts to search of any
    designated cell.

We give only the *statement type* in this scaffold. -/

/-- The space of weighted-graph predicates that lift from quotients to
cell-uniform states. Concretely: a contravariantly-functorial Prop-valued
assignment whose lifting along `Quotient` factors through the cell-uniform
sub-presheaf. -/
structure LiftablePrimitive : Type (u + 1) where
  /-- The base predicate on weighted-graph objects. -/
  pred : WGraphObj.{u} → Prop
  /-- Naturality: a morphism in `WGraph` preserves `pred` from target to source
    (i.e. `pred` is contravariant on isometric embeddings). -/
  natural : ∀ {X Y : WGraphObj.{u}} (f : WGraphHom X Y),
    pred Y → pred X
  /-- The lift axiom: if `pred` holds of the quotient of a partitioned graph
    then it holds in the cell-uniform sense on the original. We leave the
    statement of "cell-uniform sense" as an existential over the cell-symmetric
    subspace — to be expanded in Tower 6. -/
  lift : ∀ (X : WGraphPObj.{u}), pred (Quotient.{u}.obj X) →
    -- placeholder: "cell-uniform" version of `pred` on `X.base`
    pred X.base

/-- **Lift theorem in categorical form** (statement-only). Every liftable
primitive is the data of a natural transformation `Quotient.op ⥹ Prop` —
encoded here as the existence of a `LiftablePrimitive` structure for every
property satisfying the contravariant naturality and the lifting axiom.

This subsumes the three concrete instances (PST, mixing, search) listed above. -/
theorem liftTheorem (P : LiftablePrimitive.{u}) :
    ∀ X : WGraphPObj.{u}, P.pred (Quotient.{u}.obj X) → P.pred X.base := by
  intro X h
  exact P.lift X h

/-! ## 8. Connection to graphons (statement-only).

We expect a functor `WGraph ⥤ Graphon` (sigma-finite, cut-norm topology) that
sends a finite weighted graph to its associated step-graphon (uniform counting
measure on vertices, adjacency matrix as the step kernel).

That functor should *also* preserve filtered colimits in the weak cut-norm
topology: a directed union of weighted graphs has step-graphon equal to the
cut-norm limit of the step-graphons.

Citation: Borgs–Chayes–Lovász–Sós–Vesztergombi (BCLSV), arXiv:1003.5588,
"Convergent sequences of dense graphs II. Multiway cuts and statistical
physics", which formalizes the cut-norm convergence of step-graphons. -/

namespace GraphonEmbedding

/-- Placeholder type for a (sigma-finite) graphon: a square-integrable
symmetric kernel `[0,1]² → ℂ`. The actual definition lives in a graphon
library. -/
structure Graphon : Type 1 where
  -- placeholder
  dummy : Unit := ()

/-- The placeholder `Graphon` type is a **subsingleton** (it has a single field
of type `Unit`, so any two graphons are equal): this scaffold's `Graphon` is
the *punctual* stub of the real graphon space.  The real (cut-norm) graphon
space is a rich metric space and is **not** a subsingleton — its construction
lives in a graphon library.  Everything below that reads off this type's
structure (functoriality, colimit preservation) is therefore the **stub-level**
truth, holding for the degenerate reason that the placeholder is punctual —
not yet the BCLSV content. -/
theorem graphon_subsingleton : Subsingleton Graphon :=
  ⟨fun a b => by cases a; cases b; rfl⟩

/-- The step-graphon associated to a finite weighted graph (statement-only,
construction deferred — every graph maps to the single placeholder graphon). -/
noncomputable def stepGraphon (X : WGraphObj.{u}) : Graphon := { dummy := () }

/-- **Punctual category structure on the placeholder `Graphon`.**  Since
`Graphon` is a subsingleton (`graphon_subsingleton`), the natural category
structure on the stub is the *punctual* (codiscrete) one: a unique morphism
between any two graphons.  This is exactly the category structure of the real
graphon space restricted to the stub (where there is only one object up to
equality); the real graphon category carries the cut-norm topology and rich
hom-sets, deferred to a graphon library.  We make it an `instance` local to this
`GraphonEmbedding` namespace so that the embedding can be packaged as a
`CategoryTheory.Functor` below. -/
instance graphonCat : CategoryTheory.Category Graphon where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- **The embedding functor** sending a finite weighted graph to its
step-graphon.  Into the punctual stub `Graphon` the morphism action and the
`map_id`/`map_comp` laws are forced (unique homs); the measure-preserving
functoriality (identifying the vertex set with `[0,1]`) is the content
deferred to a graphon library. -/
noncomputable def stepGraphonFunctor : WGraphObj.{u} ⥤ Graphon where
  obj := stepGraphon
  map _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The step-graphon assignment is functorial**: `stepGraphon` is the
object-action of a functor `WGraph ⥤ Graphon`, namely `stepGraphonFunctor`.
This is the stub-level content, with the BCLSV measure-preserving
functoriality (up to identification of the vertex set with `[0,1]`) deferred
to a graphon library. -/
theorem stepGraphon_functorial :
    ∃ F : WGraphObj.{u} ⥤ Graphon, F.obj = stepGraphon :=
  ⟨stepGraphonFunctor, rfl⟩

/-- A functor into the punctual stub `Graphon` sends **every** cocone to a
colimit cocone (the unique-hom property makes any cocone both the comparison and
its uniqueness witness).  This is the engine of
`stepGraphon_preservesFilteredColimits_cutnorm`. -/
noncomputable def stepGraphon_punctualIsColimit
    {J : Type v} [CategoryTheory.Category.{w} J] (K : J ⥤ WGraphObj.{u})
    (c : Limits.Cocone K) :
    Limits.IsColimit ((stepGraphonFunctor.{u}).mapCocone c) where
  desc := fun _ => PUnit.unit
  fac := fun _ _ => rfl
  uniq := fun _ _ _ => rfl

/-- **The step-graphon embedding preserves filtered colimits.**

Scope: this holds at the **stub level** for a *degenerate* reason — the
placeholder `Graphon` is punctual (`graphon_subsingleton`), so the embedding
preserves *all* colimits (every cocone into a punctual category is colimiting —
`stepGraphon_punctualIsColimit`), filtered ones in particular.  It is **not**
the BCLSV 1003.5588 result: that is the statement that the embedding into the
*real* (non-degenerate, cut-norm-topologised) graphon space is continuous for
the cut-norm — i.e. a directed union of weighted graphs has step-graphon equal
to the cut-norm *limit* of the step-graphons.  That cut-norm convergence
requires the real graphon metric space and is deferred to a graphon library. -/
noncomputable instance stepGraphon_preservesFilteredColimits_cutnorm :
    Limits.PreservesFilteredColimits (stepGraphonFunctor.{u}) :=
  ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} _ => ⟨stepGraphon_punctualIsColimit K c⟩⟩⟩⟩

end GraphonEmbedding

/-! ## Summary

Conditional data definitions (the adjacency-preservation obligations are false
for arbitrary morphisms, by explicit counterexamples, so they are taken as
explicit hypotheses):
  * `sigmaDesc` — takes the cross-component independence hypothesis `hindep`
    (the coproduct only absorbs edge-disjoint families; `sigmaInclusion_indep`
    discharges it for the disjoint union);
  * `Quotient.map` — takes the quotient-adjacency preservation `hpres`
    (`symmQuotient` mixes in cell cardinalities, so preservation fails for
    cell-merging morphisms; holds for quotient/iso morphisms).

Quotient-morphism theory:
  * `Quotient.IsQuotientMorphism` — the quotient-morphism predicate
    (cell-injective, cardinality- and branching-preserving);
  * `Quotient.cellMap_adj_preserving` — preservation, proved from
    `IsQuotientMorphism` by transporting `symmQuotient` through a quotient
    morphism;
  * `WGraphPQ` (the **wide subcategory of quotient morphisms**) and the strict
    `Quotient` functor over it (its `map` consumes `cellMap_adj_preserving`).

Headline:
  * `WGraphPObj.restrictCells` (+ `restrictCells_cellCard`,
    `restrictCells_quotient`) — restriction of a partitioned weighted graph to
    a set of whole cells, the test object that detects surplus cells in a
    colimit vertex;
  * `Quotient.exists_bijective_leg` — a colimit vertex in `WGraphPQ` carries no
    surplus cells: some leg of maximal cell count has a bijective cell map
    (counting argument through the restricted competing cocone);
  * `Quotient.mapCocone_isColimit` — the filtered-colimit-preservation
    `IsColimit` data over `WGraphPQ`, built directly from that bijection.
    From it the thin wrapper `instance Quotient.preservesFilteredColimits` and
    the corollary `quasi_infinite_limit` are built.

Still-deferred statement-level content:
  * the `IsColimit` / `IsLimit` packaging for `UnionGraph`-style filtered
    colimits and `InverseLimitGraph`-style cofiltered limits.

Graphon embedding (`GraphonEmbedding`), at the stub level:
  * `graphon_subsingleton` — the placeholder `Graphon` is a subsingleton, the
    *punctual* stub of the real (non-degenerate, cut-norm) graphon space;
  * `graphonCat`, `stepGraphonFunctor` — the embedding packaged as a
    `CategoryTheory.Functor` into the punctual `Graphon`, and
    `stepGraphon_functorial` (`∃ F, F.obj = stepGraphon`) witnessing that
    `stepGraphon` is the object-action of a functor;
  * `stepGraphon_preservesFilteredColimits_cutnorm` — a
    `PreservesFilteredColimits` instance, holding at the stub level for the
    degenerate reason that `Graphon` is punctual (every cocone into it is
    colimiting, `stepGraphon_punctualIsColimit`); the BCLSV 1003.5588
    **cut-norm continuity** (a directed union has step-graphon equal to the
    cut-norm *limit*) needs the real graphon metric space and is deferred to a
    graphon library.

What is **stated precisely** (and used in downstream towers):
  * the category structure on `WGraph` and `WGraphP`;
  * the Quotient functor `Quotient : WGraphPQ ⥤ WGraph` on the quotient-morphism
    subcategory (its object map `Quotient.obj`/`Quotient.{u}.obj` still applies to
    bare `WGraphPObj`, as `WGraphPQ` is definitionally `WGraphPObj`);
  * the `LiftablePrimitive` structure capturing PST/mixing/search lifting in
    one categorical idiom;
  * the corollary `quasi_infinite_limit` as the universal form of
    Xie–Tamon's "no infinite tail beats optimality" result.
-/

end Graphplay
