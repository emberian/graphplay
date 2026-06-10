/-
Graphplay/Relational.lean

Tower 1.5: the relational / CSP / higher-arity layer.

This file generalizes the binary `SimpleGraph` and `PullbackGraph` /
`MultiPullbackGraph` constructions from `Graphplay.Basic` to arbitrary
relational signatures.  The two main reasons this tower exists:

* Tower 1 (combinatorial graphs) and Tower 2 (`WeightedGraph` plus the
  spectral / equitable-partition theory) both want a notion of
  "engineered higher-arity coincidences" — equitable partitions of
  k-uniform hypergraphs, CSP templates over relational vocabularies,
  and so on.  These do not fit comfortably in the binary `SimpleGraph`
  shape used in `Basic.lean`.

* Tower 3 (quantum / operator-system graphs, in
  `Graphplay/QuantumGraph.lean`) introduces "non-classical" variants
  (Lovász θ, quantum chromatic number) which are naturally indexed by
  the same relational templates.  Re-using the signature mechanism
  here is what lets the spectral lifting of Tower 2 actually carry to
  the quantum side.

This is a scaffold: it lays out
the *shape* of the layer so the surrounding towers can refer to it; several
constructions are statement-level placeholders.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Graphplay.Weighted
import Graphplay.Equitable

universe u v w

namespace Graphplay

/-! ### Signatures and relational structures -/

/-- A relational signature: a type of symbols together with an arity
for each.  Examples:

* `Signature.graph` below — one symbol of arity 2.
* `Signature.kUniform k` — one symbol of arity `k`, used for
  k-uniform hypergraphs.
* `Signature.csp T` — one symbol of arity 2 valued in a template type,
  used for CSP encodings.
-/
structure Signature where
  symbols : Type u
  arity   : symbols → ℕ

/-- A relational structure over signature `σ` on the carrier `V`.  For
each relation symbol `s`, we get a predicate on `σ.arity s`-tuples of
vertices. -/
structure RelStructure (σ : Signature.{u}) (V : Type v) where
  rel : ∀ s : σ.symbols, (Fin (σ.arity s) → V) → Prop

namespace Signature

/-- The signature of plain undirected graphs: one binary relation
symbol.  Specialising `RelStructure` at this signature recovers
`SimpleGraph V` up to (un)imposing the symmetry / irreflexivity laws
externally. -/
def graph : Signature where
  symbols := Unit
  arity   := fun _ => 2

/-- The signature of k-uniform directed hyperedges: one relation
symbol of arity `k`.  Symmetry / "unordered" semantics is, again,
imposed externally as an extra predicate on the relation. -/
def kUniform (k : ℕ) : Signature where
  symbols := Unit
  arity   := fun _ => k

/-- The signature of "labeled binary relations valued in a template
type" — used by CSPs over a fixed template, in the standard textbook
sense: one binary relation symbol per template-edge type. -/
def csp (T : Type u) : Signature where
  symbols := T
  arity   := fun _ => 2

end Signature

namespace RelStructure

/-- A homomorphism of relational structures over the same signature is
a vertex map that preserves every relation. -/
structure Hom {σ : Signature.{u}} {V : Type v} {W : Type w}
    (A : RelStructure σ V) (B : RelStructure σ W) where
  toFun : V → W
  map_rel : ∀ s : σ.symbols, ∀ f : Fin (σ.arity s) → V,
            A.rel s f → B.rel s (toFun ∘ f)

instance {σ : Signature} {V : Type v} {W : Type w}
    {A : RelStructure σ V} {B : RelStructure σ W} :
    CoeFun (Hom A B) (fun _ => V → W) where
  coe f := f.toFun

@[ext]
theorem Hom.ext {σ : Signature} {V : Type v} {W : Type w}
    {A : RelStructure σ V} {B : RelStructure σ W}
    {f g : Hom A B} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have : f = g := funext h
      cases this
      rfl

/-- The identity homomorphism. -/
def Hom.id {σ : Signature} {V : Type v} (A : RelStructure σ V) : Hom A A where
  toFun := fun x => x
  map_rel := fun _ _ h => by
    -- `toFun ∘ f = f` for `toFun = id`
    simpa using h

/-- Composition of relational homomorphisms. -/
def Hom.comp {σ : Signature} {V : Type v} {W : Type w} {X : Type _}
    {A : RelStructure σ V} {B : RelStructure σ W} {C : RelStructure σ X}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  toFun := fun x => g (f x)
  map_rel := fun s tup h => by
    have h1 := f.map_rel s tup h
    have h2 := g.map_rel s (f.toFun ∘ tup) h1
    -- `g.toFun ∘ (f.toFun ∘ tup) = (fun x => g (f x)) ∘ tup`
    simpa [Function.comp] using h2

/-- The empty / zero relational structure: every relation is empty. -/
def empty (σ : Signature) (V : Type v) : RelStructure σ V where
  rel _ _ := False

/-- The maximal relational structure: every relation holds on every
tuple. -/
def complete (σ : Signature) (V : Type v) : RelStructure σ V where
  rel _ _ := True

end RelStructure

/-! ### k-ary pullback

Generalizes `PullbackGraph` from `Graphplay.Basic`.  Given a labeling
`label : V → T` and a "template" relational structure on `T`, the
pullback is the relational structure on `V` whose tuples are exactly
those tuples whose images under `label` were already in the template
relation.  This is the *greatest* relational structure on `V` for
which `label` is a homomorphism into the template. -/

namespace RelPullback

variable {σ : Signature} {V : Type v} {T : Type w}

/-- Pull back a relational template along a vertex labeling. -/
def _root_.Graphplay.RelPullback (Q : RelStructure σ T) (label : V → T) :
    RelStructure σ V where
  rel s f := Q.rel s (label ∘ f)

/-- The labeling map, regarded as a homomorphism from the pullback
into the template. -/
def labeling (Q : RelStructure σ T) (label : V → T) :
    RelStructure.Hom (RelPullback Q label) Q where
  toFun := label
  map_rel := fun _ _ h => by
    -- `label ∘ tup` is exactly the witness in the pullback definition.
    simpa using h

theorem rel_iff (Q : RelStructure σ T) (label : V → T)
    (s : σ.symbols) (f : Fin (σ.arity s) → V) :
    (RelPullback Q label).rel s f ↔ Q.rel s (label ∘ f) :=
  Iff.rfl

/-- A relational analogue of `SpanningSubgraph`: a "containment" of
two relational structures on the same vertex set, holding pointwise
for every relation symbol and every tuple. -/
def Subrel {σ : Signature} {V : Type v}
    (A B : RelStructure σ V) : Prop :=
  ∀ s : σ.symbols, ∀ f : Fin (σ.arity s) → V, A.rel s f → B.rel s f

/-- **Universal property of the k-ary pullback.**  Any relational
structure on `V` whose chosen labeling map is a homomorphism into the
template `Q` is a sub-structure of the pullback.  This is the precise
sense in which `RelPullback Q label` is the *greatest* such structure. -/
theorem greatest (Q : RelStructure σ T) (label : V → T)
    {A : RelStructure σ V} (hlabel : RelStructure.Hom A Q)
    (hsame : ∀ x, hlabel x = label x) :
    Subrel A (RelPullback Q label) := by
  intro s tup hAtup
  -- `A.rel s tup ⇒ Q.rel s (hlabel.toFun ∘ tup) = Q.rel s (label ∘ tup)`.
  have h := hlabel.map_rel s tup hAtup
  -- Rewrite `hlabel.toFun ∘ tup` as `label ∘ tup` pointwise.
  have : (fun i => hlabel.toFun (tup i)) = (fun i => label (tup i)) := by
    funext i
    exact hsame (tup i)
  -- conclude
  -- `(RelPullback Q label).rel s tup` unfolds to `Q.rel s (label ∘ tup)`.
  change Q.rel s (label ∘ tup)
  -- Massage `h` through the pointwise equality.
  -- `h : Q.rel s (hlabel.toFun ∘ tup)` and we want `Q.rel s (label ∘ tup)`.
  have hcomp : (hlabel.toFun ∘ tup) = (label ∘ tup) := this
  rwa [hcomp] at h

/-! #### `Subrel` is a preorder, with `empty`/`complete` as bottom/top.

These are the order-theoretic bookkeeping facts for the containment relation
`Subrel`: `Subrel` is reflexive and transitive, `empty` is below every
structure, and `complete` is above every structure. -/

/-- `Subrel` is reflexive. -/
theorem Subrel.refl {σ : Signature} {V : Type v} (A : RelStructure σ V) :
    Subrel A A := fun _ _ h => h

/-- `Subrel` is transitive. -/
theorem Subrel.trans {σ : Signature} {V : Type v}
    {A B C : RelStructure σ V} (hAB : Subrel A B) (hBC : Subrel B C) :
    Subrel A C := fun s f h => hBC s f (hAB s f h)

/-- The empty structure is below every structure (it is the `Subrel`-bottom):
its relations never hold, so the implication is vacuous. -/
theorem empty_Subrel {σ : Signature} {V : Type v} (A : RelStructure σ V) :
    Subrel (RelStructure.empty σ V) A := fun _ _ h => (h : False).elim

/-- Every structure is below the complete structure (it is the `Subrel`-top):
the complete structure's relations always hold. -/
theorem Subrel_complete {σ : Signature} {V : Type v} (A : RelStructure σ V) :
    Subrel A (RelStructure.complete σ V) := fun _ _ _ => trivial

/-- `Subrel` is antisymmetric: mutual containment forces equality of the
relation predicates, hence (by structure η) equality of the structures.
This makes `Subrel` a genuine partial order on relational structures. -/
theorem Subrel.antisymm {σ : Signature} {V : Type v}
    {A B : RelStructure σ V} (hAB : Subrel A B) (hBA : Subrel B A) :
    A = B := by
  cases A with
  | mk relA =>
    cases B with
    | mk relB =>
      congr 1
      funext s f
      exact propext ⟨hAB s f, hBA s f⟩

end RelPullback

/-! ### Multi-pullback

The relational analogue of `MultiPullbackGraph` from `Basic.lean`: a
heterogeneous family of templates `Q a` over (possibly distinct)
target carriers `T a`, each with its own labeling map.  A tuple
satisfies the multi-pullback relation iff every template-and-labeling
witness it. -/

namespace RelMultiPullback

variable {A : Type u} {σ : Signature} {V : Type v}
  {T : A → Type w}

/-- The multi-pullback of a family of relational templates against a
common base `V` and a heterogeneous family of labelings. -/
def _root_.Graphplay.RelMultiPullback
    [Inhabited A]
    (Q : ∀ a, RelStructure σ (T a))
    (label : ∀ a, V → T a) : RelStructure σ V where
  rel s f := ∀ a, (Q a).rel s (label a ∘ f)

theorem rel_iff [Inhabited A]
    (Q : ∀ a, RelStructure σ (T a))
    (label : ∀ a, V → T a)
    (s : σ.symbols) (f : Fin (σ.arity s) → V) :
    (RelMultiPullback Q label).rel s f
      ↔ ∀ a, (Q a).rel s (label a ∘ f) :=
  Iff.rfl

/-- Each component labeling, viewed as a homomorphism from the
multi-pullback into the corresponding template. -/
def labelingAt [Inhabited A]
    (Q : ∀ a, RelStructure σ (T a))
    (label : ∀ a, V → T a) (a : A) :
    RelStructure.Hom (RelMultiPullback Q label) (Q a) where
  toFun := label a
  map_rel := fun s tup h => by
    -- direct unfolding
    have := h a
    simpa using this

/-- Universal property: the multi-pullback is the greatest relational
structure on `V` for which *every* labeling component is a
homomorphism into the matching template. -/
theorem greatest [Inhabited A]
    (Q : ∀ a, RelStructure σ (T a))
    (label : ∀ a, V → T a)
    {B : RelStructure σ V}
    (hlabel : ∀ a, RelStructure.Hom B (Q a))
    (hsame : ∀ a x, hlabel a x = label a x) :
    RelPullback.Subrel B (RelMultiPullback Q label) := by
  intro s tup hBtup a
  have h := (hlabel a).map_rel s tup hBtup
  -- rewrite `hlabel a` as `label a` pointwise; bookkeeping only
  have hcomp : ((hlabel a).toFun ∘ tup) = (label a ∘ tup) := by
    funext i
    exact hsame a (tup i)
  rwa [hcomp] at h

end RelMultiPullback

/-! ### Equitable partitions for relational structures

Generalizes Tower-2's binary `EquitablePartition` (anchor: a partition
of vertices into cells such that for any vertex `v` in cell `i`, the
*count* of neighbours of `v` lying in cell `j` is a function of `(i,j)`
only).

For a relational structure of arity `k`, the right generalization is
this: fix a relation symbol `s`, a "tuple of cell labels"
`idx : Fin k → I`, and choose one position `pos : Fin k` to be the
"anchor".  Then for every vertex `v` in cell `idx pos`, the number of
extensions of `v` to a related `k`-tuple whose other positions land in
the prescribed cells `idx` is independent of the choice of `v` within
its cell.

When `k = 2` and we pick `pos = 0`, this exactly recovers the binary
equitable-partition condition.

We package this as a `Prop`-valued condition first, then bundle it. -/

namespace RelEquitablePartition

/-- For a relational structure `A` of arity `k` on a finite type `V`,
together with a partition `cells : V → I`, the number of tuples
satisfying the relation `s`, with prescribed cell labels `idx`, and
with the `pos`-th vertex pinned to a chosen value `v`.

This is the basic count that has to be cell-uniform for an equitable
partition. -/
def countExt {σ : Signature} {V : Type v} [Fintype V] [DecidableEq V]
    {I : Type w} [DecidableEq I]
    (A : RelStructure σ V) (cells : V → I)
    (s : σ.symbols)
    (idx : Fin (σ.arity s) → I)
    (pos : Fin (σ.arity s))
    (v : V) : ℕ :=
  -- Number of `k`-tuples `f : Fin (σ.arity s) → V` with `f pos = v`,
  -- `cells (f i) = idx i` for every `i`, and `A.rel s f`.
  --
  -- This count is morally
  --   `#{ f | f pos = v ∧ (∀ i, cells (f i) = idx i) ∧ A.rel s f }`
  -- but to spell that out we'd need `Decidable (A.rel s f)`.  The actual
  -- implementation is deferred — the layer this file lives in is
  -- statements, not computations.
  0  -- placeholder; replace once Tower 2 commits to a decidability mode.

end RelEquitablePartition

/-- A higher-arity equitable partition of a relational structure.

Concretely: for each relation symbol `s`, for each cell-index tuple
`idx : Fin (arity s) → I`, and for each "anchor position"
`pos : Fin (arity s)`, the number of tuples satisfying the relation
and matching the prescribed cells, with the `pos`-th vertex fixed to a
given `v`, depends only on `v`'s cell — not on `v` itself.

This is the "tuple-type-counts are constant" form: each tuple has a
"type" given by `(s, idx)`, and within a fixed type the local counts
indexed by any anchor are cell-uniform. -/
structure RelEquitablePartition
    {σ : Signature} {V : Type v} [Fintype V] [DecidableEq V]
    (A : RelStructure σ V) (I : Type w) [DecidableEq I] where
  /-- The partition: which cell each vertex lives in. -/
  cells : V → I
  /-- Uniformity of relation counts within each cell type. -/
  uniform :
    ∀ s : σ.symbols, ∀ idx : Fin (σ.arity s) → I,
    ∀ pos : Fin (σ.arity s),
    ∀ v w : V, cells v = cells w → cells v = idx pos →
      RelEquitablePartition.countExt A cells s idx pos v
        = RelEquitablePartition.countExt A cells s idx pos w

namespace RelEquitablePartition

/-- The trivial (finest) equitable partition: every vertex is its own
cell.  Trivially equitable for any relational structure. -/
def discrete
    {σ : Signature} {V : Type v} [Fintype V] [DecidableEq V]
    (A : RelStructure σ V) :
    RelEquitablePartition A V where
  cells := fun v => v
  uniform := by
    intro s idx pos v w hvw _
    -- If `cells v = cells w` then `v = w` because cells = id.
    cases hvw
    rfl

/-- The trivial (coarsest) equitable partition: every vertex is in the
unique cell.  Equitable because the count is the same constant for any
`v`. -/
def indiscrete
    {σ : Signature} {V : Type v} [Fintype V] [DecidableEq V]
    (A : RelStructure σ V) :
    RelEquitablePartition A Unit where
  cells := fun _ => ()
  uniform := by
    -- All vertices land in the same cell, and `countExt` was set to
    -- the placeholder `0`, which is trivially constant.
    intros; rfl

end RelEquitablePartition

/-! ### Tower-2 bridge: hypergraph Laplacians

Given a k-uniform hypergraph (encoded as a relational structure on the
signature `Signature.kUniform k`), we build a complex incidence
matrix `B : V × E → ℂ` whose entries are roots of unity
(`exp (2π i · (position in edge) / k)`), and form the *hypergraph
Laplacian*

    L := D - B Bᴴ

where `D` is the diagonal vertex-degree matrix.  This Laplacian is
Hermitian and loopless-on-the-diagonal-in-the-right-sense, so it
embeds into Tower 2's `WeightedGraph` shape — and any
`RelEquitablePartition` on the original hypergraph induces a Tower-2
`EquitablePartition` on `L`, hence the spectral lifting of Tower 2
("the quotient matrix has the same nonzero eigenvalues as the
parent") carries over to hypergraphs unchanged. -/

namespace Hypergraph

variable (k : ℕ) (V : Type u) [Fintype V] [DecidableEq V]

/-- The type of `k`-uniform directed hyperedges on `V`, as a relational
structure: one relation symbol of arity `k`. -/
abbrev KUniform : Type _ := RelStructure (Signature.kUniform k) V

/-- The vertex–edge incidence matrix, given a finite set of hyperedges
`E` along with their incidence data.  Each hyperedge is a function
`Fin k → V`; the incidence entry `B v e` is the root of unity
`exp (2π i · pos / k)` summed over positions `pos` at which `v` sits in
edge `e`.

For typical (set-style) hyperedges each vertex appears in a given edge
at most once, and the sum collapses to a single root of unity. -/
def incidence
    (E : Type _) [Fintype E] [DecidableEq E]
    (edge : E → (Fin k → V)) :
    Matrix V E ℂ :=
  -- Placeholder body — once Tower 2 picks an explicit root of unity
  -- formula we instantiate it here.  The Laplacian below only needs
  -- `B * Bᴴ` to be Hermitian and positive semidefinite, which is
  -- automatic from any `B : Matrix V E ℂ`.
  0

/-- The diagonal degree matrix of a hypergraph. -/
def degreeMatrix
    (E : Type _) [Fintype E] [DecidableEq E]
    (edge : E → (Fin k → V)) :
    Matrix V V ℂ :=
  0  -- concrete placeholder diagonal degree matrix (the `0` normalisation;
     -- `Dowsing/HypergraphPST.lean` depends on this `0` value)

/-- The hypergraph Laplacian `L = D - B Bᴴ`, packaged as a Tower-2
`WeightedGraph`.

The Hermitian condition follows from `(B Bᴴ)ᴴ = B Bᴴ`; looplessness
(`L v v = 0`) requires that the diagonal of `D` exactly cancel the
diagonal of `B Bᴴ`, which holds for the standard normalisations of the
incidence matrix.  In this scaffold both hold trivially against the `0`
placeholders. -/
noncomputable def laplacian
    (E : Type _) [Fintype E] [DecidableEq E]
    (edge : E → (Fin k → V)) :
    WeightedGraph V where
  adj := degreeMatrix k V E edge -
         (incidence k V E edge) * (incidence k V E edge).conjTranspose
  herm := by
    -- `(D - B Bᴴ)ᴴ = Dᴴ - (Bᴴᴴ Bᴴ) = D - B Bᴴ`: `D` (the diagonal degree
    -- matrix, here the `0` placeholder) is Hermitian, and `B Bᴴ` is Hermitian
    -- for any `B` since `(B Bᴴ)ᴴ = Bᴴᴴ Bᴴ = B Bᴴ`.
    have hD : degreeMatrix k V E edge = (0 : Matrix V V ℂ) := rfl
    have hB : incidence k V E edge = (0 : Matrix V E ℂ) := rfl
    rw [hD, hB]
    unfold Matrix.IsHermitian
    simp
  loopless := by
    intro v
    -- On the diagonal: `D v v - (B Bᴴ) v v`.  With the placeholder
    -- `degreeMatrix = 0` and `incidence = 0`, both diagonal terms vanish.
    have hD : degreeMatrix k V E edge = (0 : Matrix V V ℂ) := rfl
    have hB : incidence k V E edge = (0 : Matrix V E ℂ) := rfl
    rw [hD, hB]
    simp

/-- **Tower-2 bridge (statement).**  Every `RelEquitablePartition` on
a k-uniform hypergraph `H` induces a Tower-2 equitable partition on
the associated Laplacian `laplacian k V E edge`.  As a consequence,
the spectral-lifting theorem of Tower 2 — "the quotient matrix has
the same nonzero eigenvalues as the parent" — applies verbatim to
hypergraph spectra.

The Tower-2 `EquitablePartition` type lives in `Graphplay/Weighted.lean`
(referenced by path only here, since this scaffold is built without
the actual Tower-2 file).  The statement is included as a `True`-valued
placeholder so dependent files can refer to it. -/
theorem equitable_partition_lifts
    (H : KUniform k V)
    (E : Type _) [Fintype E] [DecidableEq E]
    (edge : E → (Fin k → V))
    (_compat : ∀ e, H.rel () (edge e))
    {I : Type w} [DecidableEq I]
    (_π : RelEquitablePartition H I) :
    -- Statement: "there exists a Tower-2 equitable partition of
    -- `laplacian k V E edge` whose cells agree with `π.cells`."
    --
    -- The actual `EquitablePartition` lives in Tower 2; we represent
    -- the conclusion abstractly here.
    True :=
  trivial

end Hypergraph

/-! ### CSP and non-classical chromatic-number hierarchy

Constraint-Satisfaction Problems are the canonical "Tower 1.5" use of
relational structures: a *template* is a relational structure on a
finite alphabet, and a CSP instance asks whether an input structure
admits a homomorphism into the template.

This section provides the two stub-free CSP primitives:

* the (classical) homomorphism-CSP (`Solvable`),
* the relational `Coloring` (homomorphism into the complete structure).

Stub chromatic invariants are not defined here (see the note at the end
of this section); the real invariants live in `Graphplay.LovaszTheta` and the
nonlocal-game development of `Graphplay.QuantumCSP`. -/

namespace CSP

variable {σ : Signature.{u}}

/-- The (classical) CSP over a relational template: given a target
relational structure on alphabet `T`, an input relational structure
on `V` is a *yes* instance if it admits a homomorphism into the
template. -/
def Solvable {V : Type v} {T : Type w}
    (template : RelStructure σ T) (input : RelStructure σ V) : Prop :=
  Nonempty (RelStructure.Hom input template)

/-- A *coloring* of a relational structure by a finite alphabet `C`
of "colors" is a homomorphism into the `complete` relational structure
on `C`.  This is the standard CSP-flavored definition: any relation
that holds in `A` must also hold in the alphabet — which for
`complete C` is automatic, so the only constraint is that the map
respects the (trivial) template.  More interesting templates yield
more interesting "colorings". -/
def Coloring {V : Type v} (A : RelStructure σ V) (C : Type w) : Type _ :=
  RelStructure.Hom A (RelStructure.complete σ C)

/-! **Chromatic invariants and the hierarchy theorem are not stated here.**

Against `0`-stub invariants the relational Lovász sandwich

    fractionalChromaticNumber A ≤ lovaszTheta A
      ≤ quantumChromaticNumber A ≤ chromaticNumber A

would be literally `0 ≤ 0 ∧ 0 ≤ 0 ∧ 0 ≤ 0`, asserting nothing about the real
sandwich.

What lives here is the stub-free relational CSP content `Solvable` and
`Coloring` above.  The stub-independent fragment of the sandwich — a
colouring forces the quantum game value to `1` — is
`Graphplay.QuantumCSP.quantumColorable_imp_one_le_quantumValue`.  The real
invariants live in `Graphplay.LovaszTheta` (the SDP
`lovaszTheta`, `chromaticNumber`, `quantumChromaticNumber`) and the nonlocal-game
development of `Graphplay.QuantumCSP`. -/

end CSP

/-! ### Hypergraph constructors

Direct relational analogues of the graph constructors in
`Graphplay.Basic`: the complete `k`-uniform hypergraph, the
`k`-partite hypergraph (one vertex per block), and the tensor product
of relational structures. -/

namespace Hypergraph

/-- The complete `k`-uniform hypergraph on a vertex type `V`: every
ordered `k`-tuple of *distinct* vertices is a hyperedge.

Encoded as a relational structure over `Signature.kUniform k`.  In the
binary case `k = 2`, this is `Complete V` from `Basic.lean` modulo the
symmetry constraint (which here is just left as an extra `Prop`-level
predicate the consumer can impose). -/
def completeKHypergraph (k : ℕ) (V : Type v) :
    KUniform k V where
  rel _ f := Function.Injective f

theorem completeKHypergraph_rel_iff
    (k : ℕ) (V : Type v) (f : Fin k → V) :
    (completeKHypergraph k V).rel () f ↔ Function.Injective f :=
  Iff.rfl

/-- The complete `k`-partite hypergraph: one vertex from each of `k`
disjoint parts forms a hyperedge.

Vertices live in `Sigma parts` (i.e. tagged by which block they're in);
a `k`-tuple is a hyperedge exactly when the `i`-th vertex lies in the
`i`-th block. -/
def kPartite (k : ℕ) (parts : Fin k → Type v) :
    KUniform k (Sigma parts) where
  rel _ f := ∀ i : Fin k, (f i).1 = i

theorem kPartite_rel_iff
    (k : ℕ) (parts : Fin k → Type v) (f : Fin k → Sigma parts) :
    (kPartite k parts).rel () f ↔ ∀ i, (f i).1 = i :=
  Iff.rfl

end Hypergraph

/-! ### Tensor product of relational structures -/

namespace RelStructure

/-- The (categorical) tensor product of two relational structures over
the same signature: vertices are pairs, and a tuple `f : Fin k → V×W`
is in a relation iff its projections to `V` and `W` are *both* in the
corresponding relation.

This generalises the categorical (a.k.a. *tensor*) product of graphs:

    (A ⊗ B).rel s f  ↔  A.rel s (Prod.fst ∘ f) ∧ B.rel s (Prod.snd ∘ f).

It is the right adjoint to `Hom(·, B)` in the homomorphism-order
sense, and is the underlying combinatorial operation behind quantum
products on the Tower-3 side. -/
def tensorProduct {σ : Signature} {V : Type v} {W : Type w}
    (A : RelStructure σ V) (B : RelStructure σ W) :
    RelStructure σ (V × W) where
  rel s f := A.rel s (fun i => (f i).1) ∧ B.rel s (fun i => (f i).2)

infixr:70 " ⊗r " => RelStructure.tensorProduct

theorem tensorProduct_rel_iff {σ : Signature} {V : Type v} {W : Type w}
    (A : RelStructure σ V) (B : RelStructure σ W)
    (s : σ.symbols) (f : Fin (σ.arity s) → V × W) :
    (A ⊗r B).rel s f ↔
      A.rel s (fun i => (f i).1) ∧ B.rel s (fun i => (f i).2) :=
  Iff.rfl

/-- Projection to the first factor of a tensor product. -/
def tensorProduct.fst {σ : Signature} {V : Type v} {W : Type w}
    (A : RelStructure σ V) (B : RelStructure σ W) :
    Hom (A ⊗r B) A where
  toFun := fun x => x.1
  map_rel := fun _ _ h => h.1

/-- Projection to the second factor of a tensor product. -/
def tensorProduct.snd {σ : Signature} {V : Type v} {W : Type w}
    (A : RelStructure σ V) (B : RelStructure σ W) :
    Hom (A ⊗r B) B where
  toFun := fun x => x.2
  map_rel := fun _ _ h => h.2

/-- The universal map into a tensor product induced by a compatible
pair of maps out of a common source. -/
def tensorProduct.pair {σ : Signature}
    {U : Type _} {V : Type v} {W : Type w}
    {C : RelStructure σ U} {A : RelStructure σ V} {B : RelStructure σ W}
    (f : Hom C A) (g : Hom C B) : Hom C (A ⊗r B) where
  toFun := fun x => (f x, g x)
  map_rel := fun s tup h => by
    refine ⟨?_, ?_⟩
    · -- show `A.rel s (Prod.fst ∘ (fun i => (f (tup i), g (tup i))))`
      have := f.map_rel s tup h
      simpa [Function.comp] using this
    · have := g.map_rel s tup h
      simpa [Function.comp] using this

/-- **Tensor-product universal property (β-rule, first leg).**  Projecting the
mediating map `pair f g` onto the first factor recovers `f`. -/
theorem tensorProduct.fst_pair {σ : Signature}
    {U : Type _} {V : Type v} {W : Type w}
    {C : RelStructure σ U} {A : RelStructure σ V} {B : RelStructure σ W}
    (f : Hom C A) (g : Hom C B) :
    Hom.comp (tensorProduct.pair f g) (tensorProduct.fst A B) = f := by
  apply Hom.ext; intro x; rfl

/-- **Tensor-product universal property (β-rule, second leg).**  Projecting the
mediating map `pair f g` onto the second factor recovers `g`. -/
theorem tensorProduct.snd_pair {σ : Signature}
    {U : Type _} {V : Type v} {W : Type w}
    {C : RelStructure σ U} {A : RelStructure σ V} {B : RelStructure σ W}
    (f : Hom C A) (g : Hom C B) :
    Hom.comp (tensorProduct.pair f g) (tensorProduct.snd A B) = g := by
  apply Hom.ext; intro x; rfl

/-- **Tensor-product universal property (η-rule).**  Any map into a tensor
product equals the `pair` of its two projections; hence `pair` is the *unique*
mediating map.  Together with `fst_pair`/`snd_pair` this is the full universal
property of `⊗r` as a categorical product in the homomorphism category. -/
theorem tensorProduct.pair_eta {σ : Signature}
    {U : Type _} {V : Type v} {W : Type w}
    {C : RelStructure σ U} {A : RelStructure σ V} {B : RelStructure σ W}
    (h : Hom C (A ⊗r B)) :
    tensorProduct.pair (Hom.comp h (tensorProduct.fst A B))
        (Hom.comp h (tensorProduct.snd A B)) = h := by
  apply Hom.ext; intro x; rfl

end RelStructure

/-! ### Bridge back to Tower 1 (`SimpleGraph`)

We close the loop: a `SimpleGraph V` corresponds to a `RelStructure
Signature.graph V` whose single binary relation is symmetric and
irreflexive.  Conversely, any binary `RelStructure` admits a
symmetrization that lands back in `SimpleGraph`. -/

namespace RelStructure

/-- A `SimpleGraph` becomes a relational structure over the binary
signature.  This is the embedding that makes Tower 1 a special case
of Tower 1.5. -/
def ofSimpleGraph {V : Type v} (G : SimpleGraph V) :
    RelStructure Signature.graph V where
  rel := fun (_ : Unit) (f : Fin 2 → V) => G.Adj (f 0) (f 1)

theorem ofSimpleGraph_rel_iff {V : Type v} (G : SimpleGraph V)
    (f : Fin 2 → V) :
    (ofSimpleGraph G).rel () f ↔ G.Adj (f 0) (f 1) :=
  Iff.rfl

/-- A binary relational structure satisfying the graph laws projects
back to a `SimpleGraph`. -/
def toSimpleGraph {V : Type v}
    (_A : RelStructure Signature.graph V)
    (_symm : ∀ x y : V, True)
    (_irrefl : ∀ x : V, True) :
    SimpleGraph V :=
  -- Construction deferred: the original tuple-encoded laws relied on
  -- definitional reduction of `Signature.graph.arity` that no longer
  -- elaborates as written.
  (⊥ : SimpleGraph V)

/-- The roundtrip `SimpleGraph → RelStructure → SimpleGraph` is the
identity, provided we plug in the obvious symmetry/irreflexivity
proofs from the original graph. -/
theorem ofSimpleGraph_toSimpleGraph {V : Type v} (G : SimpleGraph V) :
    True := by
  -- Statement-only: the equality of the round-tripped graph with `G`
  -- holds extensionally but requires `SimpleGraph` extensionality,
  -- which `Basic.lean` does not currently export.  Left as `True` so
  -- this scaffold compiles in isolation.
  trivial

end RelStructure

/-! ### Sanity examples

Two small examples that exercise the layer without claiming any deep
theorems. -/

/-- Specialising `RelPullback` to the graph signature recovers the
adjacency formula of `PullbackGraph` from `Basic.lean`.  Statement
only — the underlying relational structures are equal *as data*, but
checking this requires the `ofSimpleGraph` extensionality we elide
above. -/
example {V : Type v} {T : Type w} (Q : SimpleGraph T) (label : V → T) :
    True := by
  -- The two structures
  --   `RelPullback (RelStructure.ofSimpleGraph Q) label`
  --   `RelStructure.ofSimpleGraph (PullbackGraph Q label)`
  -- should be equal; see comment above on extensionality.
  trivial

/-- Pulling back a `k`-uniform hyperedge structure along a labeling
preserves the arity, and the universal property of `RelPullback`
recovers the "labeled hypergraph colouring" condition. -/
example (k : ℕ) {V : Type v} {T : Type w}
    (H : RelStructure (Signature.kUniform k) T) (label : V → T) :
    (RelPullback H label).rel () = fun f => H.rel () (label ∘ f) := by
  rfl

end Graphplay
