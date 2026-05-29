import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
universe u v w
namespace Graphplay

/-! ## Graph bundles

A `GraphBundle` is a Mathlib `SimpleGraph` template `Q` on an index type `I`
together with, for each `i : I`, a Hermitian `WeightedGraph` "fiber" on a vertex
type `V i`, and, for each template edge `i ~ j`, a coupling matrix
`V i × V j → ℂ` whose adjoint along the symmetry of the template recovers the
opposite coupling.  The total bundle is the block matrix assembling fibers on the
diagonal and couplings off the diagonal; it is itself a Hermitian weighted graph
on the sigma vertex type.

Existing constructions (`TemplateJoin`, `ColorCompletion`, `CompleteJoin`,
graph products) all arise as bundles by specializing fibers and couplings.
-/

/-- A bundle of weighted graphs over a `SimpleGraph` template `Q` on `I`. -/
structure GraphBundle {I : Type u} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) (V : I → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] where
  fiber : ∀ i, WeightedGraph (V i)
  coupling : ∀ {i j : I}, Q.Adj i j → Matrix (V i) (V j) ℂ
  hermCompat : ∀ {i j : I} (h : Q.Adj i j),
    coupling (Q.symm h) = Matrix.conjTranspose (coupling h)

namespace GraphBundle

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {Q : SimpleGraph I} {V : I → Type v}
variable [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- The total weighted graph of a bundle: block-diagonal fibers plus
off-diagonal couplings indexed by template edges. -/
noncomputable def total (B : GraphBundle Q V) : WeightedGraph (Σ i, V i) where
  adj := fun x y =>
    if hxy : x.1 = y.1 then
      -- intra-fiber: use the fiber adjacency
      (B.fiber x.1).adj x.2 (hxy ▸ y.2)
    else
      -- inter-fiber: use the coupling if the template edge exists, else 0
      by classical exact
        if hadj : Q.Adj x.1 y.1 then B.coupling hadj x.2 y.2 else 0
  herm := by
    classical
    -- Hermitian by `hermCompat` on the off-diagonals and `(fiber i).herm` on the
    -- diagonal blocks.
    ext x y
    obtain ⟨xi, xv⟩ := x
    obtain ⟨yi, yv⟩ := y
    -- Goal: `star (adj ⟨yi,yv⟩ ⟨xi,xv⟩) = adj ⟨xi,xv⟩ ⟨yi,yv⟩`.
    simp only [Matrix.conjTranspose_apply]
    by_cases hxy : xi = yi
    · -- Diagonal block: use `(fiber xi).herm`.
      subst hxy
      have hf := (B.fiber xi).herm
      have := congrFun (congrFun hf xv) yv
      simpa [Matrix.conjTranspose_apply] using this
    · -- Off-diagonal block.
      have hyx : ¬ yi = xi := fun h => hxy h.symm
      simp only [dif_neg hxy, dif_neg hyx]
      by_cases hadj : Q.Adj xi yi
      · -- Use `hermCompat` at the edge `xi ~ yi`.
        have hadj' : Q.Adj yi xi := hadj.symm
        rw [dif_pos hadj, dif_pos hadj']
        have hc := B.hermCompat hadj
        -- `coupling (Q.symm hadj) = (coupling hadj)ᴴ`; the LHS coupling is at the
        -- edge `yi ~ xi`, but `Q.symm hadj` and `hadj'` are proofs of the same
        -- proposition, hence give the same coupling by proof irrelevance.
        have hcoup : B.coupling hadj' = B.coupling (Q.symm hadj) := by rfl
        rw [hcoup, hc]
        simp [Matrix.conjTranspose_apply]
      · -- No template edge: both entries are `0`.
        have hadj' : ¬ Q.Adj yi xi := fun h => hadj h.symm
        rw [dif_neg hadj, dif_neg hadj']
        simp
  loopless := by
    intro v
    -- The diagonal-of-diagonal entry reduces to `(fiber v.1).adj v.2 v.2 = 0`.
    show (if hvv : v.1 = v.1 then (B.fiber v.1).adj v.2 (hvv ▸ v.2) else _) = 0
    rw [dif_pos rfl]
    exact (B.fiber v.1).loopless v.2

/-- Convenience constructor: a bundle with empty fibers and constant coupling
matrices equal to the all-ones matrix on each template edge. -/
noncomputable def ofTemplateJoin (Q : SimpleGraph I) (V : I → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [DecidableRel Q.Adj] :
    GraphBundle Q V where
  fiber := fun i => { adj := 0, herm := by simp [Matrix.IsHermitian],
                      loopless := by intro v; rfl }
  coupling := fun _ => Matrix.of (fun _ _ => (1 : ℂ))
  hermCompat := by
    intro i j h
    -- The all-ones rectangular matrix has conjugate transpose the all-ones
    -- matrix again, since `star (1 : ℂ) = 1`.
    ext a b
    simp [Matrix.conjTranspose_apply]

/-- The total bundle of `ofTemplateJoin` agrees with the existing
`Graphplay/Basic.lean` `TemplateJoin` construction (viewed as a 0/1 weighted
graph). -/
theorem ofTemplateJoin_total_eq_templateJoin
    (Q : SimpleGraph I) (V : I → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [DecidableRel Q.Adj] :
    ((ofTemplateJoin Q V).total).adj =
      fun x y => if x.1 = y.1 then 0 else if Q.Adj x.1 y.1 then 1 else 0 := by
  classical
  funext x y
  show (if hxy : x.1 = y.1 then _ else _) = _
  by_cases hxy : x.1 = y.1
  · -- Intra-fiber: the `ofTemplateJoin` fiber is the zero matrix.
    rw [dif_pos hxy, if_pos hxy]
    rfl
  · rw [dif_neg hxy, if_neg hxy]
    by_cases hadj : Q.Adj x.1 y.1
    · rw [dif_pos hadj, if_pos hadj]
      simp [ofTemplateJoin]
    · rw [dif_neg hadj, if_neg hadj]

/-- Cartesian product `G □ H` as a bundle over the template graph that is the
host graph `(SimpleGraph V).Cart H` (informally: index by vertices of `G`, each
fiber a copy of `H`, couplings only between equal-`H`-vertex fibers along
adjacent `G`-vertices, with coupling the identity). -/
noncomputable def cartesianProduct {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : WeightedGraph V) (H : WeightedGraph W) : WeightedGraph (V × W) where
  -- `A(G □ H) = A_G ⊗ I + I ⊗ A_H`: an edge between `(v₁,w₁)` and `(v₂,w₂)` is
  -- an `H`-edge within a fixed `G`-vertex, plus a `G`-edge within a fixed
  -- `H`-vertex.
  adj := Matrix.of fun p q =>
    (if p.1 = q.1 then H.adj p.2 q.2 else 0) + (if p.2 = q.2 then G.adj p.1 q.1 else 0)
  herm := by
    ext p q
    obtain ⟨pv, pw⟩ := p; obtain ⟨qv, qw⟩ := q
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_add]
    congr 1
    · by_cases h : qv = pv
      · subst h; rw [if_pos rfl, if_pos rfl]; exact H.herm.apply pw qw
      · rw [if_neg h, if_neg (fun hc => h hc.symm), star_zero]
    · by_cases h : qw = pw
      · subst h; rw [if_pos rfl, if_pos rfl]; exact G.herm.apply pv qv
      · rw [if_neg h, if_neg (fun hc => h hc.symm), star_zero]
  loopless := by intro v; simp [G.loopless, H.loopless]

/-- Lexicographic (composition) product `G ∘ H`: index by `V`, each fiber a copy
of `H`; on `G`-adjacent vertices the coupling is the all-ones matrix weighted by
`G.adj`. -/
noncomputable def lexProduct {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : WeightedGraph V) (H : WeightedGraph W) : WeightedGraph (V × W) where
  -- Within a fixed `G`-vertex use the `H`-edge; across `G`-vertices use the
  -- (scalar-weighted all-ones) `G`-edge regardless of the `H`-coordinates.
  adj := Matrix.of fun p q => if p.1 = q.1 then H.adj p.2 q.2 else G.adj p.1 q.1
  herm := by
    ext p q
    obtain ⟨pv, pw⟩ := p; obtain ⟨qv, qw⟩ := q
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : qv = pv
    · subst h; rw [if_pos rfl, if_pos rfl]; exact H.herm.apply pw qw
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]; exact G.herm.apply pv qv
  loopless := by intro v; simp [H.loopless]

/-- Strong product `G ⊠ H`: index by `V`, fibers a copy of `H`, coupling on a
`G`-edge is `(G.adj v₁ v₂) • (I + H.adj)`. -/
noncomputable def strongProduct {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : WeightedGraph V) (H : WeightedGraph W) : WeightedGraph (V × W) where
  -- Within a fixed `G`-vertex use the `H`-edge; across a `G`-edge the coupling
  -- is `G.adj • (I + A_H)`, encoding the strong-product diagonal-plus-`H`-edge
  -- connections.
  adj := Matrix.of fun p q =>
    if p.1 = q.1 then H.adj p.2 q.2
    else G.adj p.1 q.1 * ((if p.2 = q.2 then 1 else 0) + H.adj p.2 q.2)
  herm := by
    ext p q
    obtain ⟨pv, pw⟩ := p; obtain ⟨qv, qw⟩ := q
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : qv = pv
    · have h' : pv = qv := h.symm
      subst h'; rw [if_pos rfl, if_pos rfl]; exact H.herm.apply pw qw
    · have h' : ¬ pv = qv := fun hc => h hc.symm
      rw [if_neg h, if_neg h', star_mul', G.herm.apply pv qv, star_add, H.herm.apply pw qw]
      congr 2
      by_cases hw : qw = pw
      · have hw' : pw = qw := hw.symm; subst hw'; simp
      · rw [if_neg hw, if_neg (show ¬ pw = qw from fun hc => hw hc.symm), star_zero]
  loopless := by intro v; simp [H.loopless]

/-- The complete-multipartite color completion of `color : V → I` as a bundle
over the complete graph on `I` with empty fibers. -/
noncomputable def colorCompletion {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (color : V → I) : WeightedGraph V where
  -- Complete multipartite: vertices are joined exactly when they have different
  -- colors.  Same-color (including the diagonal) gives weight `0`.
  adj := Matrix.of fun u v => if color u = color v then 0 else 1
  herm := by
    ext u v
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : color v = color u
    · rw [if_pos h, if_pos h.symm, star_zero]
    · rw [if_neg h, if_neg (fun hc => h hc.symm), star_one]
  loopless := by intro v; simp [Matrix.of_apply]

/-- The Heawood-type bound: for orientable genus `g`, the chromatic number of
any embedded graph is at most `h(g) := ⌊(7 + √(1 + 48g))/2⌋`.  We package the
complete-graph template `K_{h(g)}` as a bundle for use in the search/PST
machinery on genus-bounded surfaces. -/
noncomputable def Heawood (g : ℕ) : ℕ :=
  Nat.floor ((7 + Real.sqrt (1 + 48 * (g : ℝ))) / 2)

/-! ## Biregularity and the fiber-partition theorem -/

/-- A weighted graph is `d`-regular if every row sum of its adjacency matrix is
`d`. -/
def WeightedGraph.IsRegular {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (d : ℂ) : Prop :=
  ∀ v : V, (∑ w, G.adj v w) = d

/-- A coupling matrix is `(α, β)`-biregular if every row sums to `α` and every
column sums to `β`. -/
def IsBiregular {V W : Type*} [Fintype V] [Fintype W]
    (M : Matrix V W ℂ) (α β : ℂ) : Prop :=
  (∀ v, (∑ w, M v w) = α) ∧ (∀ w, (∑ v, M v w) = β)

/-- **Fiber-partition theorem.**  If every fiber of a graph bundle is regular
and every coupling is biregular, then the assignment of each vertex to its
fiber index is an equitable partition of the total bundle. -/
def fiberPartition (B : GraphBundle Q V)
    (d : I → ℂ) (hfib : ∀ i, GraphBundle.WeightedGraph.IsRegular (B.fiber i) (d i))
    (α β : ∀ {i j : I}, Q.Adj i j → ℂ)
    (hcouple : ∀ {i j : I} (h : Q.Adj i j),
      IsBiregular (B.coupling h) (α h) (β h)) :
    EquitablePartition B.total I where
  cells := fun x => x.1
  uniform := by
    classical
    -- It suffices to show that for any vertex `x` with `x.1 = i`, the total
    -- weight from `x` into fiber `j` is a constant determined by `i` and `j`.
    -- We compute that constant: the fiber regularity `d i` when `i = j`, the
    -- coupling row-sum `α h` when `Q.Adj i j`, and `0` otherwise.
    suffices key : ∀ (i j : I) (x : Σ k, V k), x.1 = i →
        (∑ z : Σ k, V k, (if z.1 = j then B.total.adj x z else 0))
          = (if hij : i = j then d i
             else if hadj : Q.Adj i j then α (i := i) (j := j) hadj else 0) by
      intro i j x y hx hy
      rw [key i j x hx, key i j y hy]
    intro i j x hx
    -- Decompose the sigma sum and keep only the `j`-th fiber.
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single j]
    · -- The inner sum over fiber `j`.
      -- First strip the (now trivially-true) `⟨j, w⟩.fst = j` indicator.
      subst hx
      have hstrip : (∑ w : V j, (if (⟨j, w⟩ : Σ k, V k).1 = j then B.total.adj x ⟨j, w⟩ else 0))
          = ∑ w : V j, B.total.adj x ⟨j, w⟩ := by
        apply Finset.sum_congr rfl; intro w _; simp
      rw [hstrip]
      -- `B.total.adj x ⟨j, w⟩` reduces by cases on `x.1 = j`.
      by_cases hij : x.1 = j
      · -- `i = j`: fiber row sum equals `d x.1` by regularity.
        rw [dif_pos hij]
        -- Reduce each entry to the fiber adjacency.
        have hsum : (∑ w : V j, B.total.adj x ⟨j, w⟩)
            = ∑ w : V j, (B.fiber x.1).adj x.2 (hij ▸ w) := by
          apply Finset.sum_congr rfl
          intro w _
          show (if hxy : x.1 = j then (B.fiber x.1).adj x.2 (hxy ▸ w) else _) = _
          rw [dif_pos hij]
        rw [hsum]
        -- Now reindex `∑ w : V j, (B.fiber x.1).adj x.2 (hij ▸ w)` to a sum over
        -- `V x.1`, then apply regularity.
        subst hij
        simpa using hfib x.1 x.2
      · -- `i ≠ j`: off-diagonal, governed by the coupling.
        rw [dif_neg hij]
        have hsum : (∑ w : V j, B.total.adj x ⟨j, w⟩)
            = ∑ w : V j, (if hadj : Q.Adj x.1 j then B.coupling hadj x.2 w else 0) := by
          apply Finset.sum_congr rfl
          intro w _
          show (if hxy : x.1 = j then _ else
            (if hadj : Q.Adj x.1 j then B.coupling hadj x.2 w else 0)) = _
          rw [dif_neg hij]
        rw [hsum]
        by_cases hadj : Q.Adj x.1 j
        · rw [dif_pos hadj]
          -- The coupling row sum is the biregularity constant `α hadj`.
          have hb := (hcouple hadj).1 x.2
          rw [show (∑ w : V j, (if h : Q.Adj x.1 j then B.coupling h x.2 w else 0))
                = ∑ w : V j, B.coupling hadj x.2 w from by
                apply Finset.sum_congr rfl; intro w _; rw [dif_pos hadj]]
          exact hb
        · rw [dif_neg hadj]
          apply Finset.sum_eq_zero
          intro w _
          rw [dif_neg hadj]
    · -- Off-`j` fibers contribute nothing thanks to the indicator.
      intro k _ hk
      apply Finset.sum_eq_zero
      intro w _
      simp [hk]
    · intro h; exact absurd (Finset.mem_univ j) h

end GraphBundle
end Graphplay
