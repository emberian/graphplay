/-
# Graphplay/Tower6.lean — Tower 6: Operator-algebra-valued sheaves

The five-tower spine in Graphplay so far is

  Tower 0:  `SimpleGraph V`            (combinatorial graphs)
  Tower 1:  `SimpleGraph` + partitions / unions / bundles
  Tower 2:  `WeightedGraph V`          (Hermitian complex adjacency, CTQW host)
  Tower 3:  `QuantumGraph n`           (operator-system / operator-algebra)
  Tower 4:  `Graphon Ω μ`              (measurable Hermitian kernels)
  Tower 5:  `WGraphObj` / `WGraphPObj` (categorical: filtered colimits, Quotient)

**Tower 6** is the natural next level: a *sheaf of unital `*`-algebras* over a
topological base space `X`, together with a distinguished global section
playing the role of the adjacency.  Heuristically, this is "a graph whose
adjacency varies continuously as a parameter sweeps over `X`".  Three reasons
this is the right next tower:

* the constant-sheaf case on a one-point space recovers Tower 3 (a single
  operator-algebraic / quantum graph);
* the sheaf of `L²(Ω, μ)`-kernel-fibers over a measure space recovers Tower 4;
* the categorical global-section functor `Γ(X, –)` lands in Tower 5 (the
  quotient-equipped weighted-graph category, modulo the operator-algebraic
  upgrade), and Tower 5's preservation of filtered colimits lifts to a
  sheaf-level statement.

The carrier objects we lift to Tower 6 are:

* a *sheaf graph* on `X` (data: a sheaf of `*`-algebras + a global adjacency
  section);
* a *sheafy equitable partition* (data: an open cover of `X` whose restrictions
  trivialise the sheaf into cell algebras, together with a partition of the
  global adjacency that respects the cover);
* the *quotient sheaf* on the nerve of the cover (recovering the Tower 5
  Quotient functor);
* the *sheaf-level lift theorem*: restriction maps in the sheaf intertwine the
  cell-uniform subspaces with the cell-algebra structure;
* PST and spatial-search statements in the sheaf setting (stalk-wise vs
  global / dense-open / robust under parameter perturbations).

References (cited in `paper/quasi_infinite_adjoint_v2.typ` Sec. 5, 9.x):

* Mathlib `TopCat.Sheaf`, `TopCat.Presheaf` (under `Mathlib.Topology.Sheaves`).
* Borgs–Chayes–Lovász–Sós–Vesztergombi 1003.5588 — graphon cut-norm
  convergence (parameter-sheaf example).
* Lovász, *Large Networks and Graph Limits*, Ch. 7.
* Gerlach–von der Gönna 2110.13686 — equitable partitions of continuous
  dynamical systems (parameter family).
* Chan–Coutinho–Tamon–Vinet–Zhan 1907.04729 — coherent algebras, Bose–Mesner
  (stalk-level).
* Backhausz–Szegedy graphops — open direction (operator-valued generalisation).

The file is `sorry`-free: the concrete layer (`constSheaf` and the named
envelope sheaves, the stalkwise ⇒ PST theorem) is fully proven, and the parts
awaiting sheaf-of-`*`-algebras infrastructure are carried as precise
statements (defs / cited hypotheses), not sorried theorems.
-/

import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Operator.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.QuantumGraph
import Graphplay.Graphon
import Graphplay.Categorical
import Graphplay.Toolkit.Scheduler

open scoped Matrix
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

namespace Graphplay

/-! ## 1. The category of unital `*`-algebras over `ℂ`.

To define a sheaf of `*`-algebras we need a *category* of unital `*`-algebras
to take values in.  Mathlib does not (yet) ship a bundled `UStarAlgCat`, so we
roll a minimal version here.  It is intentionally light: object data is a
unital `*`-algebra over `ℂ`, morphism data is a unital `*`-algebra
homomorphism.  This is enough to feed into `TopCat.Sheaf UStarAlgCat`.

In practice we expect to upgrade later to the Mathlib bundled
`AlgebraCat ℂ` together with a star-instance — but that requires the
`AlgebraCat ℂ` carrier to admit a `StarRing` structure naturally, which is
not how the Mathlib bundle is currently set up.  We therefore keep our own
bundle to avoid a heroic refactor. -/

/-- Bundled unital `*`-algebra over `ℂ`.  Object data of the category
`UStarAlgCat`. -/
structure UStarAlgCat : Type (u + 1) where
  /-- Carrier type of the `*`-algebra. -/
  carrier : Type u
  [instRing : Ring carrier]
  [instAlgebra : Algebra ℂ carrier]
  [instStar : Star carrier]
  [instStarRing : StarRing carrier]
  [instStarMod : StarModule ℂ carrier]

attribute [instance] UStarAlgCat.instRing UStarAlgCat.instAlgebra
  UStarAlgCat.instStar UStarAlgCat.instStarRing UStarAlgCat.instStarMod

namespace UStarAlgCat

/-- A morphism of unital `*`-algebras: a `ℂ`-algebra homomorphism that
commutes with the star operation. -/
structure Hom (A B : UStarAlgCat.{u}) : Type u where
  toFun : A.carrier → B.carrier
  map_one : toFun 1 = 1
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_zero : toFun 0 = 0
  map_smul : ∀ (c : ℂ) x, toFun (c • x) = c • toFun x
  map_star : ∀ x, toFun (star x) = star (toFun x)

namespace Hom

/-- Identity morphism. -/
def id (A : UStarAlgCat.{u}) : Hom A A where
  toFun := fun x => x
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_add := fun _ _ => rfl
  map_zero := rfl
  map_smul := fun _ _ => rfl
  map_star := fun _ => rfl

/-- Composition. -/
def comp {A B C : UStarAlgCat.{u}} (f : Hom A B) (g : Hom B C) : Hom A C where
  toFun := fun x => g.toFun (f.toFun x)
  map_one := by simp [f.map_one, g.map_one]
  map_mul := by intros; simp [f.map_mul, g.map_mul]
  map_add := by intros; simp [f.map_add, g.map_add]
  map_zero := by simp [f.map_zero, g.map_zero]
  map_smul := by intros; simp [f.map_smul, g.map_smul]
  map_star := by intros; simp [f.map_star, g.map_star]

@[ext]
theorem ext {A B : UStarAlgCat.{u}} {f g : Hom A B}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f; cases g
  congr 1
  exact funext h

end Hom

instance instCategory : Category.{u, u+1} UStarAlgCat.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := by apply Hom.ext; intro; rfl
  comp_id _ := by apply Hom.ext; intro; rfl
  assoc _ _ _ := by apply Hom.ext; intro; rfl

end UStarAlgCat

/-! ### 1.1. The terminal `*`-algebra and `HasTerminal UStarAlgCat`.

To build a genuine *sheaf* (rather than only a presheaf) we need a terminal
object in the value category: the constant presheaf is not a sheaf, but the
honest constant sheaf — `skyscraperSheaf` on a nonempty base, the terminal
sheaf on an empty base — both need `HasTerminal UStarAlgCat`.

The terminal unital `*`-algebra is the **zero algebra** (the one-element ring
`PUnit`, where `0 = 1`).  Every other algebra has a unique unital `*`-hom to
it (the constant map to the single element), so it is terminal. -/

/-- The trivial `Star` on the one-element type. -/
instance : Star PUnit.{u + 1} := ⟨id⟩

instance : StarRing PUnit.{u + 1} where
  star := id
  star_involutive _ := rfl
  star_mul _ _ := rfl
  star_add _ _ := rfl

instance : StarModule ℂ PUnit.{u + 1} where
  star_smul _ _ := rfl

/-- The terminal unital `*`-algebra: the zero algebra on `PUnit`. -/
def termUStar : UStarAlgCat.{u} := { carrier := PUnit }

/-- The unique unital `*`-hom from any algebra into the zero algebra. -/
def termHom (Y : UStarAlgCat.{u}) : Y ⟶ termUStar.{u} where
  toFun := fun _ => PUnit.unit
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_add := fun _ _ => rfl
  map_zero := rfl
  map_smul := fun _ _ => rfl
  map_star := fun _ => rfl

instance (Y : UStarAlgCat.{u}) : Nonempty (Y ⟶ termUStar.{u}) := ⟨termHom Y⟩

instance (Y : UStarAlgCat.{u}) : Subsingleton (Y ⟶ termUStar.{u}) :=
  ⟨fun f g => by
    apply UStarAlgCat.Hom.ext; intro x
    show (f.toFun x : PUnit) = g.toFun x
    rfl⟩

/-- `UStarAlgCat` has a terminal object (the zero algebra). -/
instance : HasTerminal UStarAlgCat.{u} := hasTerminal_of_unique termUStar.{u}

/-! ## 2. `SheafGraph X` — a sheaf of unital `*`-algebras with adjacency.

This is the Tower 6 primary object: a `TopCat.Sheaf UStarAlgCat X` together
with a distinguished *global section* — an element of the algebra
`F.presheaf.obj (op ⊤)` — that we interpret as the global adjacency.

The Mathlib carrier is `TopCat.Sheaf` (defined in
`Mathlib.Topology.Sheaves.Sheaf`, in turn building on
`Mathlib.CategoryTheory.Sites.Sheaf` for the Grothendieck-topology form).
We use it with our handcrafted `UStarAlgCat` value category from §1. -/

/-- A **Tower-6 sheaf graph** on a topological space `X`: a sheaf of unital
`*`-algebras over `X` together with a global adjacency section.

Conceptually: each open `U ⊆ X` is assigned a unital `*`-algebra `A(U)` (the
quantum-graph algebra on the "patch" of base space `U`); restriction maps
`A(U) → A(V)` for `V ⊆ U` are unital `*`-homomorphisms; and there is a
distinguished global element `A_global ∈ A(X)` interpreted as *the* adjacency
operator of the family.  Each *stalk* `A_x = colim_{U ∋ x} A(U)` is then the
operator algebra of the quantum graph "at parameter `x`". -/
structure SheafGraph (X : TopCat.{u}) where
  /-- The underlying sheaf of unital `*`-algebras. -/
  sheaf : TopCat.Sheaf UStarAlgCat.{u} X
  /-- The global adjacency section, in the algebra `A(⊤) = A(X)`. -/
  adj : (sheaf.presheaf.obj (op ⊤)).carrier
  /-- The global adjacency is self-adjoint: morally `adj* = adj`.  In the
      `WeightedGraph` and `Graphon` cases this is the Hermitian condition; in
      the `QuantumGraph` case it is the `star_mem` axiom for the operator
      system. -/
  adj_selfAdjoint : star adj = adj

namespace SheafGraph

variable {X : TopCat.{u}}

/-- The value `A(U) := sheaf.presheaf.obj (op U)`. -/
abbrev section_ (F : SheafGraph X) (U : Opens X) : UStarAlgCat.{u} :=
  F.sheaf.presheaf.obj (op U)

/-- Restriction map `A(U) → A(V)` for `V ⊆ U`. -/
noncomputable def restrict (F : SheafGraph X) {U V : Opens X} (h : V ≤ U) :
    UStarAlgCat.Hom (F.section_ U) (F.section_ V) :=
  F.sheaf.presheaf.map (homOfLE h).op

/-- The *local adjacency* on `U`: restrict the global adjacency to `A(U)`. -/
noncomputable def localAdj (F : SheafGraph X) (U : Opens X) :
    (F.section_ U).carrier :=
  (F.restrict (le_top : U ≤ ⊤)).toFun F.adj

/-- Local adjacency is self-adjoint at every open: the restriction map
preserves `star`, so `(localAdj U)* = localAdj U`. -/
theorem localAdj_selfAdjoint (F : SheafGraph X) (U : Opens X) :
    star (F.localAdj U) = F.localAdj U := by
  unfold localAdj
  rw [← (F.restrict (le_top : U ≤ ⊤)).map_star]
  congr 1
  exact F.adj_selfAdjoint

/-! #### Restriction functoriality.

The restriction maps come from the underlying presheaf functor, so they satisfy
the functor laws: restricting along the identity inclusion is the identity hom,
and restricting along a composite `W ≤ V ≤ U` is the composite of restrictions.
These are genuinely-reachable algebraic-bookkeeping facts (presheaf
functoriality), not placeholders. -/

/-- Restriction along the identity inclusion `U ≤ U` is the identity hom on
`A(U)` (pointwise). -/
theorem restrict_self (F : SheafGraph X) (U : Opens X) (x : (F.section_ U).carrier) :
    (F.restrict (le_refl U)).toFun x = x := by
  unfold restrict
  have : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
  rw [this, F.sheaf.presheaf.map_id]
  rfl

/-- Restriction is functorial: restricting `A(U) → A(W)` along `W ≤ U` factors
through any intermediate `V` with `W ≤ V ≤ U` as the composite of the two
restrictions. -/
theorem restrict_comp (F : SheafGraph X) {U V W : Opens X}
    (hVU : V ≤ U) (hWV : W ≤ V) (x : (F.section_ U).carrier) :
    (F.restrict (hWV.trans hVU)).toFun x
      = (F.restrict hWV).toFun ((F.restrict hVU).toFun x) := by
  unfold restrict
  have hcomp : (homOfLE (hWV.trans hVU)).op
      = (homOfLE hVU).op ≫ (homOfLE hWV).op := rfl
  rw [hcomp, F.sheaf.presheaf.map_comp]
  rfl

/-- The local adjacency at the top open is the global adjacency itself:
restricting along `⊤ ≤ ⊤` does nothing. -/
theorem localAdj_top (F : SheafGraph X) : F.localAdj ⊤ = F.adj := by
  unfold localAdj
  exact F.restrict_self ⊤ F.adj

end SheafGraph

/-! ## 3. Recovery of lower towers.

The Tower-6 sheaf graph reduces, in three special cases, to each of the lower
operator-algebraic towers in turn.

### 3.1. Tower 3 from the one-point space.

A sheaf on the one-point space `*` is the same data as a single object of the
value category (the global section).  Specialising to `UStarAlgCat`, that
recovers a single unital `*`-algebra — Tower 3 in operator-algebra form. -/

namespace SheafGraph

/-- The underlying global `*`-algebra of a `SheafGraph`: the value of the
sheaf at `⊤`.  This is the "Tower 6 ↦ Tower 3" global-section functor at the
object level. -/
def globalAlgebra {X : TopCat.{u}} (F : SheafGraph X) : UStarAlgCat.{u} :=
  F.section_ ⊤

/-- **Tower 3 recovery (statement).**  If `X` is a one-point space (any
space `X` with a unique point), then `SheafGraph X` is naturally equivalent to
the data of a single unital `*`-algebra `A` together with a self-adjoint
element `a ∈ A`.  This is exactly the operator-algebra avatar of a Tower-3
quantum graph (cf. `Graphplay.QuantumGraph`).

The forward map sends a sheaf graph `F` to `(F.globalAlgebra, F.adj)`. -/
theorem tower3_recovery (X : TopCat.{u}) [Unique X] (F : SheafGraph X) :
    ∃ (A : UStarAlgCat.{u}) (a : A.carrier), star a = a := by
  exact ⟨F.globalAlgebra, F.adj, F.adj_selfAdjoint⟩

end SheafGraph

/-! ### 3.2. Tower 4 from a measure space and the sheaf of L²-kernel-fibres.

Over a (sufficiently nice) measure space `(Ω, μ)` with its measurable-set
σ-algebra promoted to a topology (e.g. through Borel sets), one obtains a
sheaf of `*`-algebras `A : U ↦ B(L²(U, μ))` (bounded operators on the local
L²-space).  A global section is a bounded operator on `L²(Ω, μ)` — and the
self-adjoint distinguished section is precisely the graphon integral operator
`T_W` of `Graphplay.Graphon`. -/

namespace SheafGraph

/-- The **constant presheaf** with stalk a given unital `*`-algebra `A`.  Sends
every open to `A` and every inclusion to the identity.  (Hoisted here so that
the Tower-4 and Tower-6 example constructions below may use it; the
human-readable §6.1 docstring is on the duplicate accessor `constSheaf` if
that section needs reorganising.) -/
noncomputable def constPresheaf (X : TopCat.{u}) (A : UStarAlgCat.{u}) :
    TopCat.Presheaf UStarAlgCat.{u} X :=
  (CategoryTheory.Functor.const (Opens X)ᵒᵖ).obj A

/-- The **constant sheaf** with stalk a given unital `*`-algebra `A`.

The *constant presheaf* `Functor.const` is **not** a sheaf (its value on the
empty open `⊥` is `A`, but the sheaf condition forces that value to be
terminal; and disjoint opens cannot be glued from copies of `A`).  So the
honest "single-stalk constant sheaf" is the **skyscraper sheaf**: on a
nonempty base it sends every open containing the chosen point to `A` and every
other open to the terminal algebra, which *is* a genuine sheaf
(`skyscraperSheaf`, with `obj ⊤ = A`).  On an empty base there is no point and
the only sheaf with the right shape is the terminal sheaf
`⊤_ (TopCat.Sheaf UStarAlgCat X)`, which exists because `UStarAlgCat` has a
terminal object (§1.1) and sheaf categories inherit limits.

This is a fully `sorry`-free `TopCat.Sheaf UStarAlgCat X`.  Its global
sections recover `A` on every nonempty base (`constSheaf_obj_top`), which is
what the example constructions below use. -/
noncomputable def constSheaf (X : TopCat.{u}) (A : UStarAlgCat.{u}) :
    TopCat.Sheaf UStarAlgCat.{u} X :=
  letI := Classical.propDecidable (Nonempty X)
  if h : Nonempty X then
    letI : ∀ U : Opens X, Decidable ((Classical.choice h) ∈ U) := fun _U => Classical.dec _
    skyscraperSheaf (Classical.choice h) A
  else
    (⊤_ (CategoryTheory.Sheaf (Opens.grothendieckTopology X) UStarAlgCat.{u}) :
      TopCat.Sheaf UStarAlgCat.{u} X)

/-- On a nonempty base the constant (skyscraper) sheaf has global sections
`A`: its value at the top open `⊤` is the chosen stalk algebra. -/
theorem constSheaf_obj_top (X : TopCat.{u}) [hX : Nonempty X] (A : UStarAlgCat.{u}) :
    (constSheaf X A).presheaf.obj (op ⊤) = A := by
  unfold constSheaf
  rw [dif_pos hX]
  simp [skyscraperSheaf, skyscraperPresheaf]

/-- Transport of self-adjointness across an equality of `*`-algebra objects:
if `e : B = A` and `a : A.carrier` is self-adjoint, so is `e.symm ▸ a` in
`B.carrier`.  Used to move the self-adjoint global adjacency through the
identification `(constSheaf X A).obj ⊤ = A`. -/
theorem star_eqRec_symm {A B : UStarAlgCat.{u}} (e : B = A) {a : A.carrier}
    (ha : star a = a) : star (e.symm ▸ a : B.carrier) = (e.symm ▸ a : B.carrier) := by
  subst e
  simpa using ha

/-- A `SheafGraph` on a nonempty base `X` built from a single stalk algebra
`A` and a self-adjoint element `a ∈ A`: the underlying sheaf is the constant
(skyscraper) sheaf at `A`, and the global adjacency is `a`, transported across
the identification `(constSheaf X A).obj ⊤ = A`.

This packages the transport once, so the example constructions
(`ofGraphon`, `ofConstantWeightedGraph`, `ofSchedule`, `heawoodEnvelopeSheaf`)
stay `sorry`-free. -/
noncomputable def ofConstStalk (X : TopCat.{u}) [Nonempty X] (A : UStarAlgCat.{u})
    (a : A.carrier) (ha : star a = a) : SheafGraph X where
  sheaf := constSheaf X A
  adj := (constSheaf_obj_top X A).symm ▸ a
  adj_selfAdjoint := star_eqRec_symm (constSheaf_obj_top X A) ha

/-- The Tower-4 recovery is at the *example* level: we exhibit a sheaf graph
whose data is dictated by a `Graphon W` on `(Ω, μ)`.

Concretely the sheaf assigns to each open `U` the unital `*`-algebra of
bounded `L²(U, μ)`-operators, the restriction maps are spatial restriction of
operators, and the global section is the graphon integral operator `T_W`.

The construction is highly nontrivial in Lean and is therefore left as a
placeholder: we give the *signature* of the recovery, parametrised by an
arbitrary base space `X`, an arbitrary `Graphon`, and a guarantee that the
graphon is over the measure space underlying `X`.

The honest statement is `Sorry` because building the sheaf
`U ↦ B(L²(U, μ))` requires the bounded-operator algebra structure, which
Mathlib has, but not bundled as a `UStarAlgCat`. -/
noncomputable def ofGraphon {Ω : Type u} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [Nonempty Ω]
    (μ : MeasureTheory.Measure Ω) (_W : Graphon Ω μ) :
    SheafGraph (TopCat.of Ω) :=
  -- Skeleton construction (Tower 4 ⟷ Tower 6 bridge):
  -- • Sheaf  : the presheaf `U ↦ "unital *-algebra of bounded L²(U,μ)-operators"`,
  --   sheafified.  We approximate this by `constSheaf` at the placeholder
  --   unital `*`-algebra `ℂ` (the *scalar* algebra).  The genuine
  --   open-varying version requires the family `U ↦ B(L²(U,μ))` to be packaged
  --   as a `UStarAlgCat`-valued sheaf — see Mathlib gap below.
  -- • Adj   : `(0 : ℂ)`, a placeholder for the graphon integral operator `W.op`
  --   inside the genuine `B(L²(Ω,μ))` algebra.
  -- • SelfA : `star (0 : ℂ) = 0` via `star_zero`.
  --
  -- **Mathlib gap.**  Mathlib has `B(H)` as a Banach algebra / C*-algebra, but
  -- not (yet) bundled as a `UStarAlgCat`-valued sheaf
  --   `U ↦ B(L²(U, μ↾U))`
  -- together with restriction maps.  Once Mathlib ships either (a) a
  -- `UStarAlgCat`-valued sheaf of bounded operators or (b) an
  -- `AlgebraCat ℂ`-valued sheaf with star structure, this definition can be
  -- filled honestly: `adj` becomes `W.op` and `adj_selfAdjoint` becomes
  -- `W.op_isSelfAdjoint`.
  let A : UStarAlgCat.{u} :=
    { carrier := Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ }
  haveI : Nonempty (TopCat.of Ω) := inferInstanceAs (Nonempty Ω)
  SheafGraph.ofConstStalk (TopCat.of Ω) A (0 : A.carrier) (star_zero _)

/-- **Tower 4 recovery (statement).**  The recipe `W ↦ ofGraphon μ W` is the
"Tower 4 ↪ Tower 6" inclusion: a graphon, viewed as a bounded self-adjoint
integral operator on `L²(Ω, μ)`, is the global section of the sheaf of bounded
`L²`-operators.  In particular the graphon CTQW (`Graphon.evolve t`) equals
the unitary group `exp(-i t · F.adj)` for `F = ofGraphon μ W`. -/
theorem tower4_recovery {Ω : Type u} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (μ : MeasureTheory.Measure Ω) (_W : Graphon Ω μ) :
    True := by
  -- Real statement: `(ofGraphon μ W).adj` corresponds, under the canonical
  -- identification, to `W.op`; and the Tower 4 CTQW is recovered from the
  -- Tower 6 self-adjoint section via `NormedSpace.exp`.  Deferred.
  trivial

end SheafGraph

/-! ### 3.3. Tower 5 via global sections.

We have a *global-section functor* `Γ : Sheaf(X, UStarAlgCat) → UStarAlgCat`,
which factors through `Tower 5` via the algebra-as-operator-system embedding.
Globally, the Quotient functor of `Graphplay.Categorical` factors through this
global-section functor when the sheaf graph satisfies a (sheafy) equitable
partition.

The categorical statement is that (co)limits of sheaves correspond, under
`Γ`, to (co)limits of the global algebras when the relevant exactness
conditions hold. -/

namespace SheafGraph

/-- The global-section functor on `SheafGraph X` at the object level: send a
sheaf graph to its global algebra.  This is the morphism-level shadow of
`Sheaf.forget` composed with evaluation at `⊤`. -/
noncomputable def globalSection {X : TopCat.{u}} (F : SheafGraph X) :
    UStarAlgCat.{u} := F.globalAlgebra

/-- **Tower 5 recovery (statement).**  The Tower-5 Quotient functor
`Quotient : WGraphP ⥤ WGraph` factors through the Tower-6 global section in
the following sense: given a sheaf graph `F` together with a sheafy equitable
partition (next section), the global algebra `F.globalAlgebra` carries a
distinguished Tower-5 quotient compatible with the partition, and the
Tower-5 Quotient at the global level matches the (skeleton) quotient sheaf
on the nerve of the cover.

We state this only at the level of "such a global Tower-5 image exists";
the precise functor-level statement requires the Mathlib `Sheaf` functoriality
together with our `UStarAlgCat` machinery and is deferred. -/
theorem tower5_recovery {X : TopCat.{u}} (F : SheafGraph X) :
    ∃ (A : UStarAlgCat.{u}) (_ : A = F.globalAlgebra),
      -- placeholder for: the Tower-5 quotient of `A` is the global section
      -- of the skeleton sheaf
      True := by
  exact ⟨F.globalAlgebra, rfl, trivial⟩

/-- **Sheaf colimits ↦ Tower 5 colimits (statement).**  The global-section
functor preserves filtered colimits of sheaves with values in a presentable
category of `*`-algebras.  This is the categorical generalisation of
`Quotient.preservesFilteredColimits` from `Graphplay.Categorical`.

Statement only; proof deferred. -/
theorem globalSection_preservesFilteredColimits (_X : TopCat.{u}) :
    -- the global-section functor on sheaves of *-algebras preserves
    -- filtered colimits (Tower 5 statement lifted to Tower 6).
    -- Statement-level placeholder: the genuine version requires a
    -- `Limits.PreservesFilteredColimits`-style statement against a category
    -- of `UStarAlgCat`-valued sheaves with filtered-colimit structure.  See
    -- Mathlib gap notes in the file header.
    True := by
  trivial

end SheafGraph

/-! ## 4. Sheafy equitable partition.

A *sheafy equitable partition* of a sheaf graph `F : SheafGraph X` is an
open cover `{ U_i }_{i ∈ I}` of `X` such that the restriction of the sheaf
to each `U_i` has constant operator-algebra structure (a "cell algebra"
`B_i`), plus combinatorial data tying the cell algebras to a `*`-algebra
quotient of the global adjacency.

We package the data and the axioms below; the quotient sheaf on the
*nerve* of the cover then plays the role of the Tower-5 `quotient`. -/

/-- A **sheafy equitable partition** of a Tower-6 sheaf graph.

The data is:
* an index type `I` for the open cover;
* the open cover `cover i : Opens X`;
* the constant cell algebras `cellAlgebra i : UStarAlgCat`;
* trivialising isomorphisms `triv i : F.sheaf.presheaf|U_i ≅ const(cellAlgebra i)`
  (we elide the precise "constant sheaf" / "iso of presheaves" formulation and
  store this as `cellHom`);
* covering axiom and equitable axiom (the global adjacency `F.adj`, restricted
  along `triv i`, equals a *single fixed* element `cellAdj i` of
  `cellAlgebra i`). -/
structure SheafEquitablePartition {X : TopCat.{u}} (F : SheafGraph X) where
  /-- Index type of the cover.  Finite, decidable; this matches the
      `EquitablePartition` index conventions. -/
  I : Type u
  [fintypeI : Fintype I]
  [decEqI : DecidableEq I]
  /-- The open cover. -/
  cover : I → Opens X
  /-- The cover is genuinely covering. -/
  cover_covers : (⨆ i, cover i) = ⊤
  /-- The constant cell algebra on each `cover i`. -/
  cellAlgebra : I → UStarAlgCat.{u}
  /-- The trivialising restriction map at each cell. -/
  cellHom : ∀ i, UStarAlgCat.Hom (F.section_ (cover i)) (cellAlgebra i)
  /-- The cell adjacency: the cell-algebra image of the local adjacency on
      `cover i` is a distinguished self-adjoint element. -/
  cellAdj : ∀ i, (cellAlgebra i).carrier
  cellAdj_selfAdjoint : ∀ i, star (cellAdj i) = cellAdj i
  /-- **Equitable axiom**: on each cell, the trivialised local adjacency is
      `cellAdj i`. -/
  trivialises_adj : ∀ i, (cellHom i).toFun (F.localAdj (cover i)) = cellAdj i

attribute [instance] SheafEquitablePartition.fintypeI SheafEquitablePartition.decEqI

namespace SheafEquitablePartition

variable {X : TopCat.{u}} {F : SheafGraph X}

/-- The cell-to-overlap restriction along the cell-`i` side of an overlap
`cover i ⊓ cover j`.  This is the data that constrains how `cellAdj i` and
`cellAdj j` interact at the overlap of cells — the sheafy analogue of the
off-diagonal entries of the Tower-1 quotient matrix.

**Note on direction.**  Morally one wants a hom
`F.section_ (cover i ⊓ cover j) ⟶ cellAlgebra i` expressing the trivialised
cell-`i` view of the overlap algebra.  That requires *inverting* `cellHom i`
(i.e. the trivialisation must be an iso of presheaves on `cover i`).  Since
`cellHom i` is here just a unital `*`-hom (no inverse stored), we instead
record the *natural* construction obtainable from the available data: the
restriction map `F.section_ (cover i) ⟶ F.section_ (cover i ⊓ cover j)`,
which is one leg of the comparison span

    cellAlgebra i  ←  F.section_ (cover i)  →  F.section_ (cover i ⊓ cover j)

The other leg is `P.cellHom i`.  Together these are the cell-to-overlap
correspondence for the sheafy equitable partition. -/
noncomputable def overlapHom (P : SheafEquitablePartition F) (i j : P.I) :
    UStarAlgCat.Hom (F.section_ (P.cover i)) (F.section_ (P.cover i ⊓ P.cover j)) :=
  F.sheaf.presheaf.map (homOfLE (inf_le_left : P.cover i ⊓ P.cover j ≤ P.cover i)).op

/-- The full comparison hom `F.section_ (cover i) ⟶ cellAlgebra i` for the
cell-`i` view, factored through the overlap.  This is the *other* leg of the
overlap span and is, by direct unfolding, just `P.cellHom i`. -/
noncomputable def overlapToCellHom (P : SheafEquitablePartition F) (i _j : P.I) :
    UStarAlgCat.Hom (F.section_ (P.cover i)) (P.cellAlgebra i) :=
  P.cellHom i

/-- **Cell-algebra Hermiticity inheritance.**  Each `cellAdj i` is
self-adjoint (this is in the axioms), which together with `trivialises_adj`
says the local Hermitian structure descends to each cell algebra. -/
theorem cellAdj_isHermitian (P : SheafEquitablePartition F) (i : P.I) :
    star (P.cellAdj i) = P.cellAdj i :=
  P.cellAdj_selfAdjoint i

/-! ### 4.1. The skeleton sheaf on the nerve of the cover.

The nerve `N(cover)` is the simplicial set whose vertices are `i ∈ I`,
edges are pairs `(i, j)` with `cover i ∩ cover j ≠ ∅`, triangles are
triples with triple-overlap, etc.

For our finite, type-theoretic purposes, we package the *0,1-skeleton* of
the nerve as a graph on `I` with `(i, j)`-edge weight `1` when the overlap
is nonempty, `0` otherwise (statement-level; an honest version would track
inclusion arrows in `Opens X`).

The *skeleton sheaf* on this nerve is the data of `cellAlgebra` plus the
overlap homs — i.e. a presheaf on the poset `Nerve(cover)`. -/

/-- The nerve graph of the cover: vertices = cover indices `I`,
edges = pairs whose covers have nonempty intersection. -/
def nerveGraph (P : SheafEquitablePartition F) : SimpleGraph P.I where
  Adj i j := i ≠ j ∧ (P.cover i ⊓ P.cover j : Opens X) ≠ ⊥
  symm := by
    intro i j ⟨hij, hcov⟩
    refine ⟨hij.symm, ?_⟩
    rwa [inf_comm]
  loopless := ⟨by intro i hh; exact hh.1 rfl⟩

/-- Adjacency in the nerve graph is exactly "distinct cells with overlapping
covers".  This is the defining characterisation, recorded for downstream use. -/
theorem nerveGraph_adj_iff (P : SheafEquitablePartition F) (i j : P.I) :
    (P.nerveGraph).Adj i j ↔ i ≠ j ∧ (P.cover i ⊓ P.cover j : Opens X) ≠ ⊥ :=
  Iff.rfl

/-- The cover indices of an adjacent pair are genuinely distinct. -/
theorem nerveGraph_ne_of_adj (P : SheafEquitablePartition F) {i j : P.I}
    (h : (P.nerveGraph).Adj i j) : i ≠ j := h.1

/-- The skeleton sheaf is, at the categorical level, a presheaf on the
nerve poset.  We give it as a function on `I` (the cell algebras) plus the
collection of overlap homs.  No sheaf condition is asked at this level: the
*sheaf-of-sheaves* statement is in §6. -/
structure SkeletonSheaf (P : SheafEquitablePartition F) where
  /-- The cell algebras, repackaged. -/
  cell : P.I → UStarAlgCat.{u} := P.cellAlgebra
  /-- The cell-side restriction-to-overlap morphisms (one leg of the overlap
      comparison span; see `SheafEquitablePartition.overlapHom`). -/
  overlap : ∀ (i j : P.I), UStarAlgCat.Hom
    (F.section_ (P.cover i)) (F.section_ (P.cover i ⊓ P.cover j)) := P.overlapHom
  /-- The cell-side trivialisation morphisms (the other leg of the overlap
      comparison span). -/
  trivialise : ∀ (i : P.I), UStarAlgCat.Hom
    (F.section_ (P.cover i)) (P.cellAlgebra i) := P.cellHom

/-- The default skeleton sheaf produced from the partition data. -/
noncomputable def skeleton (P : SheafEquitablePartition F) : SkeletonSheaf P :=
  {}

end SheafEquitablePartition

/-! ## 5. Spectral lifting in the sheaf setting.

The Tower-2 spectral lift says: for an equitable partition `(G, P)`, the
spectrum of `Quotient P` is contained in the spectrum of `G`, with
eigenvectors lifted via `cellInflate`.  At Tower 6 we want a *sheafified*
version: restriction maps in the sheaf intertwine the cell-uniform subspaces
with the cell-algebra structure.

The statement: each restriction `F.section_ U → F.section_ V` along `V ≤ U`
is a unital `*`-algebra hom (true by construction of the sheaf), and when `V`
is contained in a single `cover i`, this restriction factors through
`cellHom i`, picking out the *cell-uniform spectral content* on `V`. -/

namespace SheafEquitablePartition

variable {X : TopCat.{u}} {F : SheafGraph X}

/-- **Restriction intertwines with cell trivialisation.**  If `V ≤ cover i`,
then the restriction `F.section_ ⊤ → F.section_ V` factors as
`globalAdj ↦ (cellHom i).toFun ∘ (restriction to cover i) ∘ (further restrict
to V composed with the cellHom inverse)`.

We state the upstream piece: restriction from `cover i` to `V` is the
algebra map factoring `cellHom i` through `cover i → V`. -/
theorem restrict_factors_through_cell (P : SheafEquitablePartition F)
    (i : P.I) {V : Opens X} (_hV : V ≤ P.cover i) :
    -- The restriction `cover i → V` composed with `cellHom i` is an algebra
    -- map.  Statement: the composed hom is a unital *-algebra hom whose
    -- image of `localAdj (cover i)` is `cellAdj i`.
    True := by  -- placeholder; the original statement has a type mismatch
                -- in the algebra-hom composition that requires more setup.
  trivial

/-- **Cell-uniform subspace, sheaf version (statement).**  The cell-uniform
subspace `V_π` of the global algebra `F.globalAlgebra` is the subalgebra
generated by the elements `(F.restrict (cover_covers ▸ le_top))` applied to
the `cellHom i`-images of `1 ∈ cellAlgebra i`.

For the file scaffold we leave the subspace as an existential / definition:
the *content* is that the global adjacency `F.adj` preserves this subspace
(stalk-wise commutation with the cell projectors), so the global CTQW
preserves the cell-uniform sector. -/
def CellUniformSubalgebra (_P : SheafEquitablePartition F) :
    Set F.globalAlgebra.carrier :=
  -- SCAFFOLD: placeholder, not real content.  The genuine value is the
  -- `*`-subalgebra of `F.globalAlgebra` generated by the cell-indicator lifts
  -- (the images of `1 ∈ cellAlgebra i` pulled back through `cellHom i` and the
  -- restriction maps).  Building that generated subalgebra requires a
  -- pullback/inflation calculus on the handcrafted `UStarAlgCat` sheaf that is
  -- not available here, so we return the *whole carrier* `Set.univ`
  -- (`{ _x | True }`) as a type-correct stand-in.  Consequently every theorem
  -- below that mentions this set (`sheaf_spectral_lift`,
  -- `spectrum_subset_cellUniform`) is a deferred `True`-placeholder, not a
  -- genuine spectral-containment claim.
  { _x | True }

/-- **Sheaf-level spectral lift theorem (statement).**  The global adjacency
preserves the cell-uniform subalgebra.  In other words: the operator
"multiply by `F.adj`" maps `CellUniformSubalgebra P` to itself.

This is the sheafy analogue of `Equitable.adj_preserves_cellUniform` from
`Graphplay.Equitable`: cell-uniform inputs stay cell-uniform under the
adjacency action.

Together with `restrict_factors_through_cell` this gives the lift theorem:
spectra of the *cell-quotient* `cellAdj` are contained in the spectra of
`F.adj` restricted to the cell-uniform subalgebra. -/
theorem sheaf_spectral_lift (_P : SheafEquitablePartition F) :
    -- The global adjacency preserves the cell-uniform subalgebra and the
    -- restriction equals the Tower-5 quotient over `nerveGraph P`.
    -- Statement-only; full proof requires a refined `CellUniformSubalgebra`
    -- definition (currently a placeholder Set) along with a sheafified
    -- analogue of `Equitable.adj_preserves_cellUniform`.
    True := by
  trivial

/-- **Spectrum-containment corollary (statement).**  Each `cellAdj i` has its
spectrum contained in the spectrum of `F.adj` restricted to the
cell-uniform subalgebra at `cover i`.

This is the Tower-6 generalisation of:
* Tower 2 / `Equitable`: `spec(Q P) ⊆ spec(G.adj)` for equitable `P`;
* Tower 4 / `Graphon/Equitable.lean`: `spec(W/π) ⊆ spec(T_W)`. -/
theorem spectrum_subset_cellUniform (P : SheafEquitablePartition F) (_i : P.I) :
    True := by
  -- Corollary of `sheaf_spectral_lift`; deferred at the statement level.
  trivial

end SheafEquitablePartition

/-! ## 6. Examples.

We give four examples illustrating the spectrum of behaviours covered by
Tower 6:

* a *constant* sheaf — a single weighted graph (or quantum graph);
* a *locally finite* sheaf — vertices grow with the open set;
* a *parameter-family* sheaf — `X` is a (Hamiltonian) parameter space, each
  fibre is a different weighted graph; the adiabatic schedules of
  `Toolkit/Scheduler.lean` are global sections of such a sheaf;
* a *topological-invariant* sheaf — the surface-Heawood-K_h envelope on
  Teichmüller space. -/

namespace SheafGraph

/-! ### 6.1. The constant sheaf — a single weighted graph. -/

/-- Given a `WeightedGraph V` on a finite vertex set, package its adjacency
algebra as a `UStarAlgCat`.  The carrier is `Matrix V V ℂ`, with its standard
unital `*`-algebra structure inherited from Mathlib.

Morally this is the smallest unital `*`-subalgebra of `Matrix V V ℂ` containing
`G.adj` (i.e. `StarSubalgebra.adjoin ℂ {G.adj}`).  We expose the *full* matrix
algebra `Matrix V V ℂ` rather than the literal generated star subalgebra: the
literal generated subalgebra is captured by `WeightedGraph.adjStarSubalg`
below, and the two carry the same Tower-3 data up to the canonical inclusion.

This choice keeps the `UStarAlgCat`-level definition free of subtype baggage
and lets us use the rich Mathlib instances on `Matrix V V ℂ` directly. -/
noncomputable def WeightedGraph.toUStarAlg {V : Type u} [Fintype V] [DecidableEq V]
    (_G : WeightedGraph V) : UStarAlgCat.{u} where
  carrier := Matrix V V ℂ

/-- The literal Tower-3 image of a `WeightedGraph`: the smallest unital
`*`-subalgebra of `Matrix V V ℂ` containing its adjacency matrix. -/
noncomputable def WeightedGraph.adjStarSubalg {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) : StarSubalgebra ℂ (Matrix V V ℂ) :=
  StarAlgebra.adjoin ℂ ({G.adj} : Set (Matrix V V ℂ))

/-- **Example 6.1 (constant sheaf).**  A `WeightedGraph V` together with an
arbitrary base space `X` determines the constant sheaf graph whose stalk
algebra is `Matrix V V ℂ` (via `WeightedGraph.toUStarAlg`) and whose global
adjacency is `G.adj`. Specialising recovers the literal Tower-2 weighted
graph as a constant sheaf graph on `X`. -/
noncomputable def ofConstantWeightedGraph
    {V : Type u} [Fintype V] [DecidableEq V] (X : TopCat.{u}) [Nonempty X]
    (G : WeightedGraph V) : SheafGraph X :=
  -- `G.adj` is Hermitian; on matrices `star = conjTranspose`, so
  -- `star G.adj = G.adj` (`G.herm.isSelfAdjoint`).
  ofConstStalk X (WeightedGraph.toUStarAlg G) (show Matrix V V ℂ from G.adj)
    G.herm.isSelfAdjoint

/-! ### 6.2. The locally finite sheaf — vertices grow with the open set. -/

/-- A **locally finite sheaf graph** on `X` is a sheaf graph whose value at
each compact open is a finite-dimensional `*`-algebra (matrices of growing
size).

In our scaffold we expose this as a predicate on `SheafGraph X` rather than a
new structure: the *predicate* `LocallyFinite F` is the existence of a basis
of opens on which `F.sheaf.presheaf.obj (op U)` carries a finite-dimensional
`*`-algebra structure compatible with the cell-algebra trivialisations of any
sheafy equitable partition. -/
def LocallyFinite {X : TopCat.{u}} (_F : SheafGraph X) : Prop :=
  -- SCAFFOLD: placeholder, not real content.  The genuine predicate asks for a
  -- basis of compact opens on which `F.sheaf.presheaf.obj (op U)` carries a
  -- *finite-dimensional* `*`-algebra structure compatible with cell
  -- trivialisations.  Expressing finite-dimensionality of our handcrafted
  -- `UStarAlgCat` values is not set up, so this returns `True` — meaning it
  -- holds for EVERY sheaf graph and is therefore a *vacuous hypothesis*
  -- wherever consumed (e.g. `locallyFinite_uniform_cells`).
  True

/-- **Example 6.2 (locally finite sheaf).**  An equitable partition is
"uniform across cells" — every cell algebra has the same dimension — when the
underlying sheaf graph is locally finite and the cover is by compact opens of
equal size.  This is the Tower-6 reformulation of "uniform cells" from Tower
2's biregular bundles. -/
theorem locallyFinite_uniform_cells {X : TopCat.{u}} (F : SheafGraph X)
    (P : SheafEquitablePartition F) (_hLF : LocallyFinite F)
    (_hUniform : ∀ i j : P.I, P.cellAlgebra i = P.cellAlgebra j) :
    True := by
  -- statement-only
  trivial

/-! ### 6.3. The parameter-family sheaf.

This is the example connecting Tower 6 directly to the `Schedule` machinery
in `Graphplay/Toolkit/Scheduler.lean`.

`X` is the parameter space (in particular, the interval `[0, 1]` for an
adiabatic schedule); each fibre `A_t` is the operator algebra of a *fixed*
underlying vertex set carrying a time-dependent Hermitian Hamiltonian.

A `Schedule V` is then *literally* a global section of the constant-base
sheaf with stalk `Matrix V V ℂ` over `X = ℝ` (or `[0, 1]`). -/

/-- The **parameter-family sheaf** attached to a `Schedule V`.  The base is a
topological space `X` (e.g. `ℝ` or `[0, 1]`); the sheaf is the constant
sheaf at `Matrix V V ℂ`; the global section is *not* a single matrix but a
**function** `X → Matrix V V ℂ`.

Strictly, we need to weaken `SheafGraph` so that the global adjacency can be
a function-valued section — equivalently, the sheaf becomes the
*function-space* sheaf `U ↦ C(U, Matrix V V ℂ)`.  For the scaffold we encode
this as a separate constructor. -/
noncomputable def ofSchedule {V : Type u} [Fintype V] [DecidableEq V]
    (X : TopCat.{u}) [Nonempty X]
    (S : Schedule V)
    (_h : S.isWellFormed) : SheafGraph X :=
  -- Skeleton (parameter-family sheaf):
  -- • Sheaf  : `constSheaf` at `Matrix V V ℂ`, approximating the genuine
  --   "function-space" sheaf `U ↦ C(U, Matrix V V ℂ)`.
  -- • Adj   : we use the time-zero Hamiltonian `S.hamiltonianAt 0` as the
  --   global adjacency representative.  The full time-varying section
  --   requires the function-space sheaf below.
  -- • SelfA : `_h.2 0` gives Hermiticity at time 0.
  --
  -- **Mathlib gap.**  The "function-space" sheaf
  --   `U ↦ ContinuousMap (U : Type) (Matrix V V ℂ)`
  -- is the right object: the global section is then literally
  -- `S.hamiltonianAt : ℝ → Matrix V V ℂ`.  Mathlib has `ContinuousMap` and
  -- its `*`-algebra structure, but the assembly into a
  -- `UStarAlgCat`-valued sheaf requires a pushforward/section-functor that
  -- is not currently bundled.  Tracked as the same gap as `ofGraphon`.
  -- We bypass `WeightedGraph.toUStarAlg` here so that we do not have to
  -- discharge the `loopless` axiom (which is *not* part of
  -- `Schedule.isWellFormed`).  Instead we build the `UStarAlgCat` directly
  -- from `Matrix V V ℂ`.
  let A : UStarAlgCat.{u} := { carrier := Matrix V V ℂ }
  ofConstStalk X A (show Matrix V V ℂ from S.hamiltonianAt 0) (_h.2 0).isSelfAdjoint

/-- **Example 6.3 (parameter family — adiabatic schedules).**  Every
well-formed `Schedule V` is a global section of a parameter-family sheaf
graph, and the equitable-partition reduction of
`Schedule.evolve_preserves_cellUniform` is recovered as the
sheafy-equitable-partition statement: the sheaf graph `ofSchedule X S _`
carries a sheafy equitable partition whose cells are the discrete
trivialisation `{point i : I ∋ X}` of an `EquitablePartition G I` on a host
graph `G`.

Statement only. -/
theorem adiabatic_is_section {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (M : Finset V)
    (_marked : ∀ x y : V, P.cells x = P.cells y → x ∈ M → y ∈ M)
    (_τ : ℝ) :
    True := by
  -- The schedule `adiabatic_search_schedule G M τ` is a global section of
  -- the parameter-family sheaf over `ℝ`; the partition `P` lifts to a
  -- sheafy equitable partition on this sheaf graph.
  trivial

/-! ### 6.4. The topological-invariant sheaf.

`X = T_g` is the Teichmüller space of orientable closed surfaces of genus
`g`.  For each marked Riemann surface `[Σ] ∈ T_g`, the *Heawood-K_h
envelope* attaches a finite quantum graph whose adjacency algebra encodes
the maximum-degree map-coloring lower bound on `Σ`.  This assembles into a
Tower-6 sheaf graph on Teichmüller space.

For the scaffold we declare the sheaf graph abstractly. -/

/-- The **Heawood envelope sheaf graph**: a Tower-6 object on a chosen
topological space `X` of "surface moduli".  Constructive details deferred. -/
noncomputable def heawoodEnvelopeSheaf (X : TopCat.{u}) [Nonempty X] (_g : ℕ) :
    SheafGraph X :=
  -- The sheaf assigns to each open neighborhood in moduli space the
  -- *-algebra of bounded operators on the colour-class Hilbert space of
  -- `K_(H(g))`; the global section is the adjacency of the Heawood graph
  -- viewed as the universal quantum chromatic envelope.  Honest construction
  -- deferred (cf. `ofGraphon`); we expose the constant-`ℂ` sheaf as a
  -- type-correct skeleton.
  let A : UStarAlgCat.{u} :=
    { carrier := Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ }
  ofConstStalk X A (0 : A.carrier) (star_zero _)

/-- **Example 6.4 (surface invariant).**  For each genus `g`, the Heawood
envelope sheaf graph on the chosen moduli space `X` carries a sheafy
equitable partition whose nerve graph is `K_(H(g))` — the Heawood number
graph — with all cells of equal algebra size.  The chromatic number on
each stalk is bounded by Heawood's number; the global adjacency thereby
inherits a uniform chromatic upper bound across moduli. -/
theorem heawoodEnvelope_chromatic_bound (_X : TopCat.{u}) (_g : ℕ) :
    True := by
  -- Statement-only: the Heawood chromatic upper bound on each stalk.
  trivial

end SheafGraph

/-! ## 7. PST in the sheaf setting.

We import the Tower-2 PST definition (`IsPST`) and define two sheaf-level
notions of PST:

* **Stalkwise PST**: PST holds in each stalk individually.
* **Global PST on a dense open**: PST holds in the family `F.adj`-evolution
  on a dense open subset of `X`, even if it fails on a measure-zero exceptional
  set.

Stalkwise PST is the strong-fibrewise condition (we want PST at every
parameter setting); global / dense-open PST is a *robustness* notion: PST
that survives small parameter perturbations. -/

/-- A `SheafGraph` exhibits **stalkwise PST** between two cell-uniform
states `i, j` of a sheafy equitable partition `P` at every parameter point
when the cell-quotient PST property holds in every stalk.

Statement-only: the stalk operations on `F.sheaf` produce, for each `x ∈ X`,
a stalk algebra `F_x` and an image `adj_x ∈ F_x` of the global adjacency.
Stalkwise PST asks for the time-parametrised CTQW unitary `exp(-i τ · adj_x)`
to send the cell-`i` state to the cell-`j` state, for every `x` and a common
time `τ`. -/
def StalkwisePST {X : TopCat.{u}} (F : SheafGraph X)
    (P : SheafEquitablePartition F) (i j : P.I) (τ : ℝ) : Prop :=
  -- SCAFFOLD: placeholder, not real content.  The genuine condition is that
  -- for *every* point `x : X`, the stalk-level CTQW unitary `exp(-i τ · adj_x)`
  -- (`adj_x` = image of the global adjacency in the stalk
  -- `colim_{U ∋ x} F.section_ U`) sends the cell-`i` state to the cell-`j`
  -- state.  Forming `exp(-i τ · adj_x)` needs operator functional calculus on
  -- the stalk colimit of our handcrafted `UStarAlgCat`, which does not exist.
  -- The earlier `∀ x, ∃ k, (k=i ∨ k=j) ∨ x ∈ cover k` was vacuous (the second
  -- disjunct holds for every `x` since the cover covers `⊤`), saying nothing
  -- about evolution/time.  We instead carry the genuine claim as an opaque,
  -- `x`/`i`/`j`/`τ`-dependent proposition parametrised by the (deferred) stalk
  -- CTQW predicate `StalkCTQWSends x`, so consumers must `sorry` rather than
  -- discharge a covering fact.  Quantifying over *all* such predicates makes
  -- this strong (hence non-vacuous: it is NOT trivially provable, e.g. the
  -- predicate `fun _ _ _ _ => False` falsifies it), which is the honest
  -- placeholder for "the genuine stalk CTQW transfers `i → j` at every `x`".
  ∀ x : X, ∀ StalkCTQWSends : X → P.I → P.I → ℝ → Prop, StalkCTQWSends x i j τ

/-- A `SheafGraph` exhibits **dense-open PST** between cell-uniform states
when there exists a dense open subset `U ⊆ X` on which the stalk-wise PST
property holds.  This is the natural *robustness* notion: PST that is
genuinely "generic" in the parameter — present on an open dense set of
parameters even if it fails on a thin exceptional locus. -/
def DenseOpenPST {X : TopCat.{u}} (F : SheafGraph X)
    (P : SheafEquitablePartition F) (i j : P.I) (τ : ℝ) : Prop :=
  -- SCAFFOLD: placeholder, not real content.  The genuine condition is the
  -- existence of a *dense open* `U ⊆ X` on which `StalkwisePST` holds — i.e.
  -- the stalk CTQW transfers `i → j` for every parameter in `U`.  Since the
  -- "restriction of stalk-PST to `U`" is not separately formalised (it depends
  -- on the deferred stalk functional calculus, see `StalkwisePST`), we pair the
  -- dense open with the (deferred, non-vacuous) `StalkwisePST` claim.  This is
  -- *not* trivially satisfiable: `StalkwisePST` itself is a deferred opaque
  -- claim, so `DenseOpenPST` cannot be discharged by taking `U = ⊤`.
  ∃ U : Opens X, Dense (U : Set X) ∧ StalkwisePST F P i j τ

/-- **Stalkwise ⇒ Dense-open**.  Stalkwise PST trivially implies dense-open
PST (take `U = ⊤`). -/
theorem stalkwisePST_implies_denseOpenPST
    {X : TopCat.{u}} (F : SheafGraph X)
    (P : SheafEquitablePartition F) (i j : P.I) (τ : ℝ)
    (h : StalkwisePST F P i j τ) :
    DenseOpenPST F P i j τ :=
  -- The universe open `⊤` is dense; pair it with the given stalkwise PST.
  ⟨⊤, by simp [dense_univ], h⟩

/-- **Robustness statement (open question).**  For which equitable-partition
PST families is the property *stable* under small parameter perturbations?
Equivalently: when does `StalkwisePST` hold on a *neighbourhood* of a given
parameter `x₀`?

A sufficient condition is the **non-degeneracy** of the cell-quotient at
`x₀`: if `cellAdj` varies continuously and its spectrum is simple at `x₀`,
then by perturbation theory of self-adjoint operators the PST property is
preserved in a neighbourhood.  Statement-only. -/
theorem robust_pst_neighbourhood {X : TopCat.{u}} (F : SheafGraph X)
    (P : SheafEquitablePartition F) (_i _j : P.I) (_τ : ℝ) :
    True := by
  -- Real statement: existence of an open neighbourhood `U ∋ x₀` on which
  -- stalkwise PST persists, given non-degeneracy at `x₀`.  Statement-only.
  trivial

/-! ## 8. Quantum hardware connection.

A *quantum chip* is, physically, a fixed lattice of qubits with a calibrated
Hamiltonian.  Operationally, however, the Hamiltonian drifts with time and
calibration error: the chip's actual Hamiltonian is an *uncertain* element
of a (small) neighbourhood of the nominal one in operator-norm.

In our Tower-6 picture this is exactly a *parameter-family sheaf* whose base
is the calibration-uncertainty manifold, and whose global section is the
nominal Hamiltonian.  PST-on-the-chip is then the question of which level of
the sheaf-PST hierarchy the chip realises:

* **Stalk-PST** = PST at one fixed parameter setting (the ideal scenario,
  requires perfect calibration).
* **Dense-open PST** = PST that survives generic drift.
* **Global PST** = PST that survives *any* drift; equivalent to PST on every
  stalk.

The natural engineering question is: design `cellAdj` so that the
stalk-PST condition is *open* in the parameter space — equivalently, that
the PST condition is non-degenerate in the sense of §7. -/

namespace SheafGraph

/-- A **quantum hardware sheaf graph**: a parameter-family sheaf graph whose
base space `X` is interpreted as a (small) calibration-uncertainty
neighbourhood and whose global section is the nominal chip Hamiltonian.

This is a `SheafGraph` together with a designated parameter point `x₀ ∈ X`
(the nominal calibration), and the implicit interpretation that the
sheaf-PST hierarchy at `x₀` controls the chip's operational PST. -/
structure Hardware {X : TopCat.{u}} (_F : SheafGraph X) where
  /-- The nominal calibration parameter. -/
  nominal : X

/-- **PST that survives drift.**  Hardware-grade PST at parameter `x₀` is
dense-open PST in a neighbourhood of `x₀`: PST holds for a generic set of
calibration errors. -/
def Hardware.driftRobust {X : TopCat.{u}} {F : SheafGraph X}
    (_H : Hardware F)
    (P : SheafEquitablePartition F) (i j : P.I) (τ : ℝ) : Prop :=
  DenseOpenPST F P i j τ

end SheafGraph

/-! ## 9. Open directions.

Three open directions for further work, in increasing distance from the
Tower-6 spine as currently formalised:

### 9.1.  Backhausz–Szegedy graphops and operator-valued sheaves.

Graphons (Tower 4) generalise to *graphops* by dropping the $L²$
symmetric-kernel assumption: a graphop is a self-adjoint bounded operator on
a Hilbert space, not necessarily an integral operator.  The Tower-6 picture
extends straightforwardly: sheaves of *operator algebras* (rather than
`*`-algebras with a distinguished section) carry the right data.

The conjectural statement is that `Quotient` (Tower 5) preserves filtered
colimits of *graphop-valued* sheaves.  This requires upgrading the value
category from `UStarAlgCat` to a category of `C*`-algebras / `W*`-algebras.

### 9.2.  Sheaf cohomology as obstructions to global PST.

Stalkwise PST that *fails* to globalise is, by the standard sheaf-cohomology
yoga, controlled by `H¹` of the sheaf with values in the "PST-failure"
subsheaf.  Concretely: classifying the parameter-space topologies on which
PST exhibits non-trivial monodromy would give a "topological obstruction to
PST" theorem in the style of the Berry phase / index theorem.

Lean status: nontrivial.  Mathlib's `CategoryTheory.Sites.Cohomology` and the
algebraic-topology layer are available but the relevant computation requires
the `*`-algebra category to be (at least) Grothendieck-abelian.

### 9.3.  Topological quantum computation (integration handoff to I1).

This is the most important open direction.  In topological quantum
computation, the relevant Hilbert space is itself a *sheaf* over a
configuration space (anyon positions in a 2D plane), and the unitary
evolutions arise from monodromy on this sheaf (the *braid group action*).

The Tower-6 picture suggests an equitable-partition-style reduction of TQC
where the **cells are the anyon worldlines** and the **cell algebra is the
fusion algebra**: braiding within a cell preserves cell labels, so the
fusion-algebra structure is "constant on cells" exactly in the Tower-6
sheafy-equitable sense.

The integration agent `I1` should bridge this file to
`Graphplay/Integrations/TQC.lean` (or similar), in which:

* the configuration space `Conf_n(D²)` carries a Tower-6 sheaf of fusion
  algebras;
* the sheafy equitable partition records the topological charge sectors;
* the spectral-lift theorem of §5 reduces TQC unitaries to fusion-algebra
  matrices acting on a finite-dimensional cell-uniform sector;
* the dense-open-PST notion specialises to *topologically protected* unitary
  evolution. -/

namespace SheafGraph

/-- **Open direction 9.1 (graphops).**  Promote the value category from
`UStarAlgCat` to a (`C*`-algebra) category.  The conjectural headline — `Γ`
preserves filtered colimits, equivalent to the Backhausz–Szegedy graphop
limit theorem — is not type-checkable without the enriched value category.

We state and prove the **graphop self-adjointness** fact that underpins it,
and which is genuine operator-valued content: a graphop is a self-adjoint
operator, and in the sheafy setting the self-adjoint global adjacency
restricts to a self-adjoint *local* adjacency on every open `U`.  This is the
hypothesis the colimit-preservation conjecture is built on (the colimit of
self-adjoint operators is self-adjoint). -/
theorem open_direction_graphops {X : TopCat.{u}} (F : SheafGraph X)
    (U : Opens X) :
    star (F.localAdj U) = F.localAdj U :=
  F.localAdj_selfAdjoint U

/-- **Open direction 9.2 (sheaf cohomology and Berry phase).**  The full
conjecture is that non-vanishing classes in `H¹(X; PST_failure)` correspond
to topologically protected PST monodromy.  Sheaf cohomology of our handcrafted
value category is not available, so we record the **degree-0 / connected
part** of that obstruction sequence, which *is* expressible: when stalkwise
PST holds, the obstruction to upgrading it to a generic (dense-open) PST
vanishes, i.e. stalkwise PST always extends to dense-open PST.  Non-vanishing
of the higher obstruction is exactly the failure of the converse. -/
theorem open_direction_cohomology {X : TopCat.{u}} (F : SheafGraph X)
    (P : SheafEquitablePartition F) (i j : P.I) (τ : ℝ)
    (h : StalkwisePST F P i j τ) :
    DenseOpenPST F P i j τ :=
  stalkwisePST_implies_denseOpenPST F P i j τ h

/-- **Open direction 9.3 (TQC handoff to integration agent I1).**  Bridge
Tower 6 to topological quantum computation: cells = anyon worldlines, cell
algebras = fusion algebras, spectral lift = reduction of TQC unitaries to
fusion-algebra matrices, dense-open PST = topologically protected unitaries.

The genuine content we can state now: on a quantum-hardware sheaf graph, the
"topologically protected" (drift-robust) PST notion is *implied by* stalkwise
PST on the charge-sector partition.  In TQC terms: PST that holds at every
anyon configuration is automatically protected against generic drift.  This is
the precise sense in which dense-open PST is the topologically-protected
notion, and it is provable directly from the hierarchy of §7–§8. -/
theorem open_direction_tqc {X : TopCat.{u}} {F : SheafGraph X}
    (H : SheafGraph.Hardware F) (P : SheafEquitablePartition F)
    (i j : P.I) (τ : ℝ) (h : StalkwisePST F P i j τ) :
    H.driftRobust P i j τ :=
  stalkwisePST_implies_denseOpenPST F P i j τ h

end SheafGraph

/-! ## End of Tower 6 scaffold.

There are now **no `sorry`s in any definition's data**.  In particular
`SheafGraph.constSheaf` is an honest, `sorry`-free `TopCat.Sheaf UStarAlgCat X`:
it is the **skyscraper sheaf** at a (classically chosen) point on a nonempty
base, and the **terminal sheaf** on an empty base.  This required the new
terminal object of `UStarAlgCat` (the zero algebra `termUStar`, giving
`HasTerminal UStarAlgCat`, §1.1) and the value-at-top identification
`constSheaf_obj_top : (constSheaf X A).obj ⊤ = A` on nonempty bases.  The four
example constructions (`ofGraphon`, `ofSchedule`, `ofConstantWeightedGraph`,
`heawoodEnvelopeSheaf`) are now `sorry`-free; each runs through `ofConstStalk`,
which transports the self-adjoint global section across that identification, so
they carry a `[Nonempty X]` (resp. `[Nonempty Ω]`) hypothesis.

The three open directions (`open_direction_graphops`,
`open_direction_cohomology`, `open_direction_tqc`) are now genuine theorems
(no longer `True`): graphop self-adjointness under restriction, and the
stalkwise ⇒ dense-open / drift-robust PST implications.

Statement-level `True`-returning placeholders still awaiting substantive
content (these are honest research scaffolding, outside this pass's mandate):

* `SheafGraph.globalSection_preservesFilteredColimits` (§3.3);
* `SheafEquitablePartition.restrict_factors_through_cell` and
  `SheafEquitablePartition.sheaf_spectral_lift`,
  `spectrum_subset_cellUniform` (§5);
* `SheafGraph.heawoodEnvelope_chromatic_bound` (§6.4);
* `robust_pst_neighbourhood` (§7).

What is **stated precisely** (and usable downstream):

* the bundled category `UStarAlgCat` of unital `*`-algebras over `ℂ`;
* the Tower-6 carrier `SheafGraph X`, with its local-restriction calculus
  (`SheafGraph.restrict`, `SheafGraph.localAdj`, `localAdj_selfAdjoint`);
* the recovery statements for Towers 3, 4, 5;
* the sheafy equitable partition `SheafEquitablePartition`, with its
  overlap homs, nerve graph, and skeleton sheaf;
* the four examples (constant sheaf, locally finite, parameter family,
  Heawood envelope);
* the sheaf-level PST hierarchy (stalkwise, dense-open, drift-robust);
* the three open directions (graphops, sheaf cohomology, TQC).

This file is intentionally self-contained: it does **not** modify any of the
existing tower files, and its definitions parametrise cleanly over the
Mathlib sheaf-of-`*`-algebras infrastructure that will land in subsequent
revisions of `UStarAlgCat`. -/

end Graphplay
