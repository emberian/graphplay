universe u v w

namespace Graphplay

/-- A small local equivalence type, enough to state universal properties without
pulling in a category theory library. -/
structure Bijection (A : Type u) (B : Type v) where
  toFun : A -> B
  invFun : B -> A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- A simple undirected graph on a vertex type. -/
structure SimpleGraph (V : Type u) where
  Adj : V -> V -> Prop
  symm : ∀ {x y : V}, Adj x y -> Adj y x
  irrefl : ∀ x : V, ¬ Adj x x

/-- A graph homomorphism preserves adjacency. -/
structure Hom {V : Type u} {W : Type v}
    (G : SimpleGraph V) (H : SimpleGraph W) where
  toFun : V -> W
  map_adj : ∀ {x y : V}, G.Adj x y -> H.Adj (toFun x) (toFun y)

infixr:25 " ⟶g " => Hom

/-- The spanning-subgraph relation for graphs on the same vertex type. -/
def SpanningSubgraph {V : Type u} (G H : SimpleGraph V) : Prop :=
  ∀ {x y : V}, G.Adj x y -> H.Adj x y

instance {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W} :
    CoeFun (G ⟶g H) (fun _ => V -> W) where
  coe f := f.toFun

namespace Hom

@[ext]
theorem ext {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    {f g : G ⟶g H} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfun : f = g := funext h
      cases hfun
      rfl

/-- The identity homomorphism. -/
def id {V : Type u} (G : SimpleGraph V) : G ⟶g G where
  toFun := fun x => x
  map_adj := fun h => h

/-- Composition of homomorphisms. -/
def comp {V : Type u} {W : Type v} {X : Type w}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph X}
    (f : G ⟶g H) (g : H ⟶g K) : G ⟶g K where
  toFun := fun x => g (f x)
  map_adj := fun h => g.map_adj (f.map_adj h)

end Hom

/-- The complete graph on a type of colors. -/
def Complete (C : Type u) : SimpleGraph C where
  Adj x y := x ≠ y
  symm := by
    intro x y h hxy
    exact h hxy.symm
  irrefl := by
    intro x h
    exact h rfl

theorem sigma_mk_ne {I : Type u} {C : I -> Type v} {i : I} {a b : C i}
    (h : a ≠ b) : Sigma.mk i a ≠ Sigma.mk i b := by
  intro hs
  cases hs
  exact h rfl

/-- A coloring by colors `C` is a homomorphism into the complete graph on `C`. -/
abbrev Coloring {V : Type u} (G : SimpleGraph V) (C : Type v) : Type (max u v) :=
  G ⟶g Complete C

/-- The edgeless graph on a vertex type. -/
def EmptyGraph (V : Type u) : SimpleGraph V where
  Adj _ _ := False
  symm := by
    intro _ _ h
    cases h
  irrefl := by
    intro _ h
    cases h

/-- Pull back a template graph along a vertex label map.

This is the greatest graph on `V` for which `label` is a homomorphism into the
template `Q`.  Ordinary color completion is the special case `Q = Complete C`. -/
def PullbackGraph {V : Type u} {T : Type v}
    (Q : SimpleGraph T) (label : V -> T) : SimpleGraph V where
  Adj x y := Q.Adj (label x) (label y)
  symm := by
    intro x y h
    exact Q.symm h
  irrefl := by
    intro x h
    exact Q.irrefl (label x) h

def PullbackGraph.labeling {V : Type u} {T : Type v}
    (Q : SimpleGraph T) (label : V -> T) :
    PullbackGraph Q label ⟶g Q where
  toFun := label
  map_adj := by
    intro x y h
    exact h

theorem PullbackGraph.adj_iff {V : Type u} {T : Type v}
    (Q : SimpleGraph T) (label : V -> T) (x y : V) :
    (PullbackGraph Q label).Adj x y ↔ Q.Adj (label x) (label y) :=
  Iff.rfl

/-- The template pullback is maximal among graphs whose chosen label map is a
homomorphism into the template. -/
theorem PullbackGraph.greatest {V : Type u} {T : Type v}
    (Q : SimpleGraph T) (label : V -> T) {G : SimpleGraph V}
    (hlabel : G ⟶g Q) (hsame : ∀ x, hlabel x = label x) :
    SpanningSubgraph G (PullbackGraph Q label) := by
  intro x y hxy
  change Q.Adj (label x) (label y)
  rw [← hsame x, ← hsame y]
  exact hlabel.map_adj hxy

/-- Simultaneous selected colorability: an edge is allowed exactly when every
template constraint allows the corresponding pair of labels.  The index type is
assumed inhabited so that irreflexivity follows from at least one constraint. -/
def MultiPullbackGraph {A : Type u} [Inhabited A] {V : Type v}
    {T : A -> Type w} (Q : ∀ a, SimpleGraph (T a))
    (label : ∀ a, V -> T a) : SimpleGraph V where
  Adj x y := ∀ a, (Q a).Adj (label a x) (label a y)
  symm := by
    intro x y h a
    exact (Q a).symm (h a)
  irrefl := by
    intro x h
    exact (Q default).irrefl (label default x) (h default)

theorem MultiPullbackGraph.greatest {A : Type u} [Inhabited A] {V : Type v}
    {T : A -> Type w} (Q : ∀ a, SimpleGraph (T a))
    (label : ∀ a, V -> T a) {G : SimpleGraph V}
    (hlabel : ∀ a, G ⟶g Q a)
    (hsame : ∀ a x, hlabel a x = label a x) :
    SpanningSubgraph G (MultiPullbackGraph Q label) := by
  intro x y hxy a
  change (Q a).Adj (label a x) (label a y)
  rw [← hsame a x, ← hsame a y]
  exact (hlabel a).map_adj hxy

/-- The arbitrary indexed coproduct of a family of graphs.

Vertices are tagged vertices `Sigma V`; adjacency only occurs inside one tag.
This is the precise version of the "bag of factors" used below. -/
def SigmaGraph {I : Type u} {V : I -> Type v}
    (G : ∀ i, SimpleGraph (V i)) : SimpleGraph (Sigma V) where
  Adj x y := ∃ (i : I) (a b : V i),
    x = Sigma.mk i a ∧ y = Sigma.mk i b ∧ (G i).Adj a b
  symm := by
    intro x y h
    rcases h with ⟨i, a, b, hx, hy, hab⟩
    exact ⟨i, b, a, hy, hx, (G i).symm hab⟩
  irrefl := by
    intro x h
    rcases h with ⟨i, a, b, hx, hy, hab⟩
    cases hx
    cases hy
    exact (G i).irrefl a hab

/-- Include one component into the indexed coproduct. -/
def SigmaGraph.inclusion {I : Type u} {V : I -> Type v}
    (G : ∀ i, SimpleGraph (V i)) (i : I) :
    G i ⟶g SigmaGraph G where
  toFun := fun x => Sigma.mk i x
  map_adj := by
    intro x y h
    exact ⟨i, x, y, rfl, rfl, h⟩

/-- Assemble a family of homomorphisms out of the components into one map out of
the coproduct. -/
def SigmaGraph.desc {I : Type u} {V : I -> Type v} {W : Type w}
    (G : ∀ i, SimpleGraph (V i)) {H : SimpleGraph W}
    (f : ∀ i, G i ⟶g H) : SigmaGraph G ⟶g H where
  toFun := fun x => f x.1 x.2
  map_adj := by
    intro x y h
    rcases h with ⟨i, a, b, hx, hy, hab⟩
    cases hx
    cases hy
    exact (f i).map_adj hab

/-- Restrict a homomorphism out of the coproduct to each component. -/
def SigmaGraph.restrict {I : Type u} {V : I -> Type v} {W : Type w}
    (G : ∀ i, SimpleGraph (V i)) {H : SimpleGraph W}
    (f : SigmaGraph G ⟶g H) (i : I) : G i ⟶g H :=
  Hom.comp (SigmaGraph.inclusion G i) f

theorem SigmaGraph.desc_restrict {I : Type u} {V : I -> Type v} {W : Type w}
    (G : ∀ i, SimpleGraph (V i)) {H : SimpleGraph W}
    (f : ∀ i, G i ⟶g H) :
    SigmaGraph.restrict G (SigmaGraph.desc G f) = f := by
  funext i
  apply Hom.ext
  intro x
  rfl

theorem SigmaGraph.restrict_desc {I : Type u} {V : I -> Type v} {W : Type w}
    (G : ∀ i, SimpleGraph (V i)) {H : SimpleGraph W}
    (f : SigmaGraph G ⟶g H) :
    SigmaGraph.desc G (SigmaGraph.restrict G f) = f := by
  apply Hom.ext
  intro x
  cases x
  rfl

/-- The coproduct universal property:
maps out of the bag are the same as compatible maps out of each factor. -/
def SigmaGraph.homEquiv {I : Type u} {V : I -> Type v} {W : Type w}
    (G : ∀ i, SimpleGraph (V i)) (H : SimpleGraph W) :
    Bijection (SigmaGraph G ⟶g H) (∀ i, G i ⟶g H) where
  toFun := SigmaGraph.restrict G
  invFun := SigmaGraph.desc G
  left_inv := SigmaGraph.restrict_desc G
  right_inv := SigmaGraph.desc_restrict G

/-- A heterogeneous family of colorings induces a coloring of the whole bag by
the sigma-sum of the factor color sets. -/
def SigmaGraph.coloring {I : Type u} {V : I -> Type v} {C : I -> Type w}
    (G : ∀ i, SimpleGraph (V i))
    (color : ∀ i, Coloring (G i) (C i)) :
    Coloring (SigmaGraph G) (Sigma C) where
  toFun := fun x => Sigma.mk x.1 (color x.1 x.2)
  map_adj := by
    intro x y h
    rcases h with ⟨i, a, b, hx, hy, hab⟩
    cases hx
    cases hy
    exact sigma_mk_ne ((color i).map_adj hab)

/-- If all factors share one color set, the arbitrary bag reuses those colors. -/
def SigmaGraph.coloringShared {I : Type u} {V : I -> Type v} {C : Type w}
    (G : ∀ i, SimpleGraph (V i))
    (color : ∀ i, Coloring (G i) C) :
    Coloring (SigmaGraph G) C :=
  SigmaGraph.desc G color

/-- The complete multipartite completion induced by a vertex coloring.  Vertices
with different colors are connected, and vertices with the same color are not. -/
def ColorCompletion {V : Type u} {C : Type v} (color : V -> C) :
    SimpleGraph V where
  Adj x y := color x ≠ color y
  symm := by
    intro x y h hxy
    exact h hxy.symm
  irrefl := by
    intro x h
    exact h rfl

/-- Any proper coloring embeds the original graph into its complete multipartite
color completion by the identity map on vertices. -/
def Coloring.toColorCompletion {V : Type u} {C : Type v} {G : SimpleGraph V}
    (color : Coloring G C) : G ⟶g ColorCompletion color.toFun where
  toFun := fun x => x
  map_adj := by
    intro x y h
    exact color.map_adj h

/-- The completion induced by `color` is itself colored by `color`. -/
def ColorCompletion.coloring {V : Type u} {C : Type v} (color : V -> C) :
    Coloring (ColorCompletion color) C where
  toFun := color
  map_adj := by
    intro x y h
    exact h

/-- A coloring makes the original graph a spanning subgraph of its color
completion. -/
theorem Coloring.spanningSubgraph_colorCompletion {V : Type u} {C : Type v}
    {G : SimpleGraph V} (color : Coloring G C) :
    SpanningSubgraph G (ColorCompletion color.toFun) := by
  intro x y h
  exact color.map_adj h

/-- The color completion is the greatest graph on the same vertices for which
the specified vertex map is a coloring. -/
theorem ColorCompletion.greatest {V : Type u} {C : Type v}
    (color : V -> C) {G : SimpleGraph V}
    (hcolor : Coloring G C) (hsame : ∀ x, hcolor x = color x) :
    SpanningSubgraph G (ColorCompletion color) := by
  intro x y hxy
  change color x ≠ color y
  rw [← hsame x, ← hsame y]
  exact hcolor.map_adj hxy

theorem ColorCompletion.adj_iff {V : Type u} {C : Type v}
    (color : V -> C) (x y : V) :
    (ColorCompletion color).Adj x y ↔ color x ≠ color y :=
  Iff.rfl

theorem Coloring.not_adj_of_same_color {V : Type u} {C : Type v}
    {G : SimpleGraph V} (color : Coloring G C) {x y : V}
    (h : color x = color y) : ¬ G.Adj x y := by
  intro hxy
  exact color.map_adj hxy h

theorem ColorCompletion.not_adj_of_same_color {V : Type u} {C : Type v}
    (color : V -> C) {x y : V} (h : color x = color y) :
    ¬ (ColorCompletion color).Adj x y := by
  intro hxy
  exact hxy h

theorem ColorCompletion.adj_of_ne_color {V : Type u} {C : Type v}
    (color : V -> C) {x y : V} (h : color x ≠ color y) :
    (ColorCompletion color).Adj x y :=
  h

/-- A bag whose cross-fiber edges are engineered by a template graph on the bag
index type. -/
def TemplateJoin {I : Type u} (Q : SimpleGraph I) (V : I -> Type v) :
    SimpleGraph (Sigma V) :=
  PullbackGraph Q (fun x : Sigma V => x.1)

def TemplateJoin.labeling {I : Type u} (Q : SimpleGraph I) (V : I -> Type v) :
    TemplateJoin Q V ⟶g Q :=
  PullbackGraph.labeling Q (fun x : Sigma V => x.1)

theorem TemplateJoin.adj_iff {I : Type u} {V : I -> Type v}
    (Q : SimpleGraph I) (x y : Sigma V) :
    (TemplateJoin Q V).Adj x y ↔ Q.Adj x.1 y.1 :=
  Iff.rfl

theorem TemplateJoin.no_intra {I : Type u} {V : I -> Type v}
    (Q : SimpleGraph I) {i : I} (x y : V i) :
    ¬ (TemplateJoin Q V).Adj (Sigma.mk i x) (Sigma.mk i y) := by
  intro h
  exact Q.irrefl i h

theorem TemplateJoin.cross {I : Type u} {V : I -> Type v}
    {Q : SimpleGraph I} {i j : I} (hij : Q.Adj i j)
    (x : V i) (y : V j) :
    (TemplateJoin Q V).Adj (Sigma.mk i x) (Sigma.mk j y) :=
  hij

/-- The engineered join is maximal among graphs on the same bag whose tag map is
a homomorphism into the chosen template. -/
theorem TemplateJoin.greatest {I : Type u} {V : I -> Type v}
    {Q : SimpleGraph I} {G : SimpleGraph (Sigma V)}
    (hlabel : G ⟶g Q)
    (hsame : ∀ x, hlabel x = x.1) :
    SpanningSubgraph G (TemplateJoin Q V) :=
  PullbackGraph.greatest Q (fun x : Sigma V => x.1) hlabel hsame

/-- The complete join of a bag of vertex types: all cross-bag edges and no
within-bag edges. -/
def CompleteJoin {I : Type u} (V : I -> Type v) : SimpleGraph (Sigma V) :=
  ColorCompletion (fun x : Sigma V => x.1)

theorem CompleteJoin.adj_iff_tag_ne {I : Type u} {V : I -> Type v}
    (x y : Sigma V) :
    (CompleteJoin V).Adj x y ↔ x.1 ≠ y.1 :=
  Iff.rfl

theorem CompleteJoin.no_intra {I : Type u} {V : I -> Type v}
    {i : I} (x y : V i) :
    ¬ (CompleteJoin V).Adj (Sigma.mk i x) (Sigma.mk i y) := by
  intro h
  exact h rfl

theorem CompleteJoin.cross {I : Type u} {V : I -> Type v}
    {i j : I} (hij : i ≠ j) (x : V i) (y : V j) :
    (CompleteJoin V).Adj (Sigma.mk i x) (Sigma.mk j y) :=
  hij

def CompleteJoin.coloring {I : Type u} {V : I -> Type v} :
    Coloring (CompleteJoin V) I :=
  ColorCompletion.coloring (fun x : Sigma V => x.1)

/-- Any graph on a sigma-bag colored by its tag projection is a spanning subgraph
of the complete join of the bag. -/
theorem CompleteJoin.greatest {I : Type u} {V : I -> Type v}
    {G : SimpleGraph (Sigma V)}
    (hcolor : Coloring G I)
    (hsame : ∀ x, hcolor x = x.1) :
    SpanningSubgraph G (CompleteJoin V) :=
  ColorCompletion.greatest (fun x : Sigma V => x.1) hcolor hsame

/-- Increasing unions on one ambient vertex type.  This is a lightweight
colimit-like construction for chains of graph approximants. -/
def UnionGraph {V : Type u} (G : Nat -> SimpleGraph V) : SimpleGraph V where
  Adj x y := ∃ n, (G n).Adj x y
  symm := by
    intro x y h
    rcases h with ⟨n, hxy⟩
    exact ⟨n, (G n).symm hxy⟩
  irrefl := by
    intro x h
    rcases h with ⟨n, hxx⟩
    exact (G n).irrefl x hxx

/-- Include a finite/staged approximant into the edge-union graph. -/
def UnionGraph.stage {V : Type u} (G : Nat -> SimpleGraph V) (n : Nat) :
    G n ⟶g UnionGraph G where
  toFun := fun x => x
  map_adj := by
    intro x y h
    exact ⟨n, h⟩

/-- A map out of an edge-union graph can equivalently be seen as one vertex map
that preserves adjacency at every stage. -/
structure UnionGraph.CoconeMap {V : Type u} {W : Type v}
    (G : Nat -> SimpleGraph V) (H : SimpleGraph W) where
  toFun : V -> W
  map_stage : ∀ n, ∀ {x y : V}, (G n).Adj x y -> H.Adj (toFun x) (toFun y)

instance {V : Type u} {W : Type v} {G : Nat -> SimpleGraph V} {H : SimpleGraph W} :
    CoeFun (UnionGraph.CoconeMap G H) (fun _ => V -> W) where
  coe f := f.toFun

/-- Assemble a stagewise-compatible map into a map out of the union. -/
def UnionGraph.desc {V : Type u} {W : Type v}
    (G : Nat -> SimpleGraph V) {H : SimpleGraph W}
    (f : UnionGraph.CoconeMap G H) : UnionGraph G ⟶g H where
  toFun := f.toFun
  map_adj := by
    intro x y h
    rcases h with ⟨n, hxy⟩
    exact f.map_stage n hxy

/-- Restrict a map out of the union to a single vertex map preserving every stage. -/
def UnionGraph.restrict {V : Type u} {W : Type v}
    (G : Nat -> SimpleGraph V) {H : SimpleGraph W}
    (f : UnionGraph G ⟶g H) : UnionGraph.CoconeMap G H where
  toFun := f.toFun
  map_stage := by
    intro n x y hxy
    exact f.map_adj ⟨n, hxy⟩

theorem UnionGraph.desc_restrict {V : Type u} {W : Type v}
    (G : Nat -> SimpleGraph V) {H : SimpleGraph W}
    (f : UnionGraph G ⟶g H) :
    UnionGraph.desc G (UnionGraph.restrict G f) = f := by
  apply Hom.ext
  intro x
  rfl

theorem UnionGraph.restrict_desc {V : Type u} {W : Type v}
    (G : Nat -> SimpleGraph V) {H : SimpleGraph W}
    (f : UnionGraph.CoconeMap G H) :
    UnionGraph.restrict G (UnionGraph.desc G f) = f := by
  cases f
  rfl

/-- A second universal property: maps out of a countable edge-union are exactly
stagewise-compatible maps out of every finite approximant. -/
def UnionGraph.homBijection {V : Type u} {W : Type v}
    (G : Nat -> SimpleGraph V) (H : SimpleGraph W) :
    Bijection (UnionGraph G ⟶g H) (UnionGraph.CoconeMap G H) where
  toFun := UnionGraph.restrict G
  invFun := UnionGraph.desc G
  left_inv := UnionGraph.desc_restrict G
  right_inv := UnionGraph.restrict_desc G

/-- A fixed coloring of every finite stage colors the union graph. -/
def UnionGraph.coloring {V : Type u} {C : Type v}
    (G : Nat -> SimpleGraph V) (color : V -> C)
    (ok : ∀ n, ∀ {x y : V}, (G n).Adj x y -> color x ≠ color y) :
    Coloring (UnionGraph G) C where
  toFun := color
  map_adj := by
    intro x y h
    rcases h with ⟨n, hxy⟩
    exact ok n hxy

/-- A thread through an inverse system of vertex types. -/
structure Thread (V : Nat -> Type u) (bond : ∀ n, V (n + 1) -> V n) : Type u where
  val : ∀ n, V n
  compat : ∀ n, bond n (val (n + 1)) = val n

/-- The inverse-limit graph of a sequence of graphs and bonding maps.  Two
threads are adjacent when they are adjacent at every finite coordinate. -/
def InverseLimitGraph {V : Nat -> Type u}
    (G : ∀ n, SimpleGraph (V n)) (bond : ∀ n, V (n + 1) -> V n) :
    SimpleGraph (Thread V bond) where
  Adj x y := ∀ n, (G n).Adj (x.val n) (y.val n)
  symm := by
    intro x y h n
    exact (G n).symm (h n)
  irrefl := by
    intro x h
    exact (G 0).irrefl (x.val 0) (h 0)

/-- Projection from the inverse-limit graph to any finite coordinate. -/
def InverseLimitGraph.proj {V : Nat -> Type u}
    (G : ∀ n, SimpleGraph (V n)) (bond : ∀ n, V (n + 1) -> V n) (n : Nat) :
    InverseLimitGraph G bond ⟶g G n where
  toFun := fun x => x.val n
  map_adj := by
    intro x y h
    exact h n

/-- A coloring at one finite coordinate colors the inverse-limit graph through
the corresponding projection. -/
def InverseLimitGraph.coloringAt {V : Nat -> Type u} {C : Type v}
    (G : ∀ n, SimpleGraph (V n)) (bond : ∀ n, V (n + 1) -> V n)
    (n : Nat) (color : Coloring (G n) C) :
    Coloring (InverseLimitGraph G bond) C :=
  Hom.comp (InverseLimitGraph.proj G bond n) color

/-- Existence of a coloring by `C`. -/
abbrev Colorable {V : Type u} (G : SimpleGraph V) (C : Type v) : Prop :=
  Nonempty (Coloring G C)

theorem colorable_of_hom {V : Type u} {W : Type v} {C : Type w}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ⟶g H) (hH : Colorable H C) : Colorable G C := by
  rcases hH with ⟨color⟩
  exact ⟨Hom.comp f color⟩

/-- If `G` is not `C`-colorable, there is no homomorphism from `G` into any
`C`-colorable graph.  This is the obstruction to reading "free `C`-colorable
quotient" as an ordinary reflector with a unit `G -> L G`. -/
theorem no_hom_from_uncolorable_to_colorable {V : Type u} {W : Type v} {C : Type w}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : ¬ Colorable G C) (hH : Colorable H C) :
    ¬ Nonempty (G ⟶g H) := by
  intro hf
  rcases hf with ⟨f⟩
  exact hG (colorable_of_hom f hH)

inductive Three where
  | a
  | b
  | c

def Triangle : SimpleGraph Three :=
  Complete Three

theorem Three.a_ne_b : Three.a ≠ Three.b := by
  intro h
  cases h

theorem Three.a_ne_c : Three.a ≠ Three.c := by
  intro h
  cases h

theorem Three.b_ne_c : Three.b ≠ Three.c := by
  intro h
  cases h

/-- The triangle is not two-colorable. -/
theorem triangle_not_bool_colorable : ¬ Colorable Triangle Bool := by
  intro h
  rcases h with ⟨color⟩
  have hab : color Three.a ≠ color Three.b := color.map_adj Three.a_ne_b
  have hac : color Three.a ≠ color Three.c := color.map_adj Three.a_ne_c
  have hbc : color Three.b ≠ color Three.c := color.map_adj Three.b_ne_c
  cases ha : color Three.a <;> cases hb : color Three.b <;> cases hc : color Three.c
  all_goals simp [ha, hb, hc] at hab hac hbc

/-- Concrete obstruction: no unit map can send the triangle into a bipartite
candidate object. -/
theorem triangle_has_no_unit_to_bool_colorable {V : Type u} {H : SimpleGraph V}
    (hH : Colorable H Bool) : ¬ Nonempty (Triangle ⟶g H) :=
  no_hom_from_uncolorable_to_colorable triangle_not_bool_colorable hH

end Graphplay
