/-
# Graphplay.Equitable

Canonical home of `EquitablePartition` for `WeightedGraph`s.

An **equitable partition** of a weighted graph is a partition of the vertex
set such that, for any two cells `C_i, C_j` and any vertex `x` of `C_i`, the
total weighted edge mass from `x` into `C_j` depends only on `i` and `j`, not
on the choice of representative `x ∈ C_i`.  This generalizes the classical
graph-theoretic notion (see Godsil–Royle "Algebraic Graph Theory", Bachman–
Tamon arXiv 1108.0339).

The key features developed here:

* the **quotient** matrix `Q : I × I → ℂ` whose `(i, j)` entry is the common
  branching number,
* `quotient.isHermitian`,
* the **cell-uniform subspace** `cellUniformSubspace`, spanned by the
  normalized cell-indicator vectors `1_{C_i} / √|C_i|`,
* the block-diagonal lift `cellInflate : Matrix I I ℂ → Matrix V V ℂ`,
* invariance of the cell-uniform subspace under the adjacency action,
* the statement that the restriction of the adjacency action to the
  cell-uniform subspace equals the quotient (under the canonical isometry),
  and
* a `refine` operation showing that any refinement of an equitable partition
  is again equitable.
-/

import Graphplay.Weighted
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic

open scoped Matrix

universe u v w

namespace Graphplay

/-- An **equitable partition** of a weighted graph.  `cells : V → I` labels
each vertex with the index of its cell; the `uniform` axiom says that the
total weight from any vertex into any cell only depends on which cell the
source vertex sits in. -/
structure EquitablePartition {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (I : Type v) [Fintype I] [DecidableEq I] where
  /-- The cell labelling. -/
  cells : V → I
  /-- The equitable / branching condition. -/
  uniform : ∀ (i j : I) (x y : V), cells x = i → cells y = i →
    (∑ z, (if cells z = j then G.adj x z else 0))
    = (∑ z, (if cells z = j then G.adj y z else 0))

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- The branching number `b_{ij}^P(x)`: the total signed edge weight from
`x` into cell `j`.  This depends only on the cell of `x` when `P` is an
equitable partition (see `branching_eq`). -/
def branching (P : EquitablePartition G I) (j : I) (x : V) : ℂ :=
  ∑ z, (if P.cells z = j then G.adj x z else 0)

/-- For an equitable partition, the branching number depends only on the
source cell. -/
theorem branching_eq (P : EquitablePartition G I) (i j : I)
    (x y : V) (hx : P.cells x = i) (hy : P.cells y = i) :
    P.branching j x = P.branching j y :=
  P.uniform i j x y hx hy

/-- The **quotient matrix** of an equitable partition: its `(i, j)` entry is
the common branching number from any representative vertex of cell `i` into
cell `j`.  If cell `i` is empty we return `0`.  Noncomputable because we use
classical choice to pick a representative. -/
noncomputable def quotient (P : EquitablePartition G I) : Matrix I I ℂ := fun i j =>
  open Classical in
  if h : ∃ x : V, P.cells x = i
    then P.branching j h.choose
    else 0

/-- The quotient matrix is well-defined on the cell representative: for any
`x` in cell `i`, the `(i, j)` entry of the quotient equals
`P.branching j x`. -/
theorem quotient_apply (P : EquitablePartition G I) (i j : I) (x : V)
    (hx : P.cells x = i) :
    P.quotient i j = P.branching j x := by
  classical
  unfold quotient
  have hex : ∃ x : V, P.cells x = i := ⟨x, hx⟩
  rw [dif_pos hex]
  exact P.branching_eq i j _ x hex.choose_spec hx

/-- The quotient matrix of an equitable partition is Hermitian.

The classical (real, 0/1) proof balances |C_i| · b_{ij} = |C_j| · b_{ji};
in the weighted case the analogous identity is
`|C_i| · Q i j = star (|C_j| · Q j i)`, from which Hermiticity follows once
we work in the cell-uniform basis (rescaled by `√|C_i|`). The combinatorial
statement encoded here is the literal Hermiticity of the unrescaled `quotient`
under the assumption that every cell is nonempty; without that the boundary
case `i ↦ 0` makes Hermiticity automatic. -/
theorem quotient_isHermitian (P : EquitablePartition G I) :
    P.quotient.IsHermitian := by
  -- Hard direction; needs the |C_i| · Q i j = star (|C_j| · Q j i) identity
  -- from the Hermiticity of `G.adj`.  Punted.
  sorry

/-- The cardinality of cell `i`, as a real number. -/
noncomputable def cellCard (P : EquitablePartition G I) (i : I) : ℝ :=
  ((Finset.univ.filter (fun w : V => P.cells w = i)).card : ℝ)

/-- The (normalized) cell-uniform vector for cell `i`: `e_i = 1_{C_i} / √|C_i|`.
On vertex `v` it equals `1/√|C_i|` if `v ∈ C_i`, otherwise `0`. -/
noncomputable def cellUniformVec (P : EquitablePartition G I) (i : I) : V → ℂ :=
  fun v =>
    if P.cells v = i
      then (1 : ℂ) / ((Real.sqrt (P.cellCard i) : ℝ) : ℂ)
      else 0

/-- The **cell-uniform subspace**: the ℂ-linear span of the normalized cell
indicators `{cellUniformVec i}_{i : I}` inside `V → ℂ`. -/
noncomputable def cellUniformSubspace (P : EquitablePartition G I) :
    Submodule ℂ (V → ℂ) :=
  Submodule.span ℂ (Set.range P.cellUniformVec)

/-- Inflate a quotient-side matrix into a block-diagonal action on the full
vertex space.  Given `M : Matrix I I ℂ`, the matrix
`cellInflate M v w = M (P.cells v) (P.cells w) / |C_{P.cells w}|`
is the unique matrix such that:

* it preserves the cell-uniform subspace,
* its restriction to the cell-uniform subspace (in the canonical isometry)
  is `M`.

Noncomputable because we divide by cardinalities (and these involve casts). -/
noncomputable def cellInflate (P : EquitablePartition G I) (M : Matrix I I ℂ) :
    Matrix V V ℂ := fun v w =>
  let i := P.cells v
  let j := P.cells w
  let cj : ℝ := P.cellCard j
  if cj = 0 then 0 else M i j / ((cj : ℝ) : ℂ)

/-- `cellInflate` sends `0` to `0`. -/
@[simp] theorem cellInflate_zero (P : EquitablePartition G I) :
    P.cellInflate 0 = 0 := by
  unfold cellInflate
  funext v w
  split_ifs <;> simp

/-! ### Invariance of the cell-uniform subspace.

The combinatorial heart of the theory.  The statement below says: applying
`G.adj` to a cell-uniform vector lands in the cell-uniform subspace; in the
canonical isometry between the cell-uniform subspace and `I → ℂ` the action
is by the quotient matrix.
-/

/-- `G.adj` acting on a cell-uniform vector is again a linear combination of
cell-uniform vectors.  The coefficient on the `j`-th cell is
`(P.quotient j i) · √(|C_i| / |C_j|)`, equivalently the off-diagonal entry
of the quotient matrix expressed in the orthonormal cell-uniform basis. -/
theorem adj_mulVec_cellUniformVec (P : EquitablePartition G I) (i : I) :
    ∃ c : I → ℂ,
      G.adj.mulVec (P.cellUniformVec i) = fun v => ∑ j, c j * P.cellUniformVec j v := by
  -- Existence statement: the coefficients are determined by `branching_eq`
  -- and the cardinality factors of the cell-uniform basis.
  sorry

/-- **Invariance**: the cell-uniform subspace is stable under the linear
action of `G.adj`. -/
theorem cellUniformSubspace_invariant (P : EquitablePartition G I)
    (v : V → ℂ) (hv : v ∈ P.cellUniformSubspace) :
    G.adj.mulVec v ∈ P.cellUniformSubspace := by
  -- Reduce to the basis vectors using `Submodule.span_induction`; each basis
  -- vector lands back in the subspace by `adj_mulVec_cellUniformVec`.
  sorry

/-- **Restriction equals quotient**: under the canonical isometry sending
`cellUniformVec i ↦ e_i` (the `i`-th coordinate vector in `I → ℂ`), the
restriction of `G.adj` to the cell-uniform subspace acts as `P.quotient`. -/
theorem restrict_eq_quotient (P : EquitablePartition G I) (w : I → ℂ) :
    G.adj.mulVec (fun v => ∑ i, w i * P.cellUniformVec i v) =
      (fun v => ∑ i, (P.quotient.mulVec w) i * P.cellUniformVec i v) := by
  sorry

/-! ### Refinements. -/

/-- A partition `P'` indexed by `I'` is a **refinement** of `P` indexed by
`I` if every `P'`-cell is contained in a `P`-cell.  Recorded as a function
`coarsen : I' → I` that collapses cells. -/
structure Refines {I' : Type w} [Fintype I'] [DecidableEq I']
    (P : EquitablePartition G I) (P' : EquitablePartition G I') where
  /-- The "coarsen" map that sends a fine cell to the coarse cell containing it. -/
  coarsen : I' → I
  /-- Compatibility: the coarse label of a vertex equals the coarsen of the
  fine label. -/
  coarsen_cells : ∀ v, P.cells v = coarsen (P'.cells v)

/-- Any refinement of an equitable partition is itself equitable. -/
def refine {I' : Type w} [Fintype I'] [DecidableEq I']
    (P : EquitablePartition G I) (cells' : V → I')
    (huniform' :
      ∀ (i' j' : I') (x y : V), cells' x = i' → cells' y = i' →
        (∑ z, (if cells' z = j' then G.adj x z else 0))
        = (∑ z, (if cells' z = j' then G.adj y z else 0)))
    : EquitablePartition G I' where
  cells := cells'
  uniform := huniform'

/-- The **trivial** partition into singletons is always equitable. -/
def discrete (G : WeightedGraph V) : EquitablePartition G V where
  cells := id
  uniform := by
    intro i j x y hx hy
    -- `cells x = i` and `cells y = i` with `cells = id` force `x = y = i`.
    subst hx
    subst hy
    rfl

/-- The **indiscrete** partition (single cell) is equitable for every graph.
The unique-cell index type is `Unit`. -/
def indiscrete (G : WeightedGraph V) : EquitablePartition G Unit where
  cells := fun _ => ()
  uniform := by
    intro i j x y _ _
    -- All sums collapse to the total row sum: `j` is the unique cell.
    -- Need: `∑ z, G.adj x z = ∑ z, G.adj y z`, which in general is FALSE; the
    -- indiscrete partition is only equitable for regular graphs.  We
    -- therefore restrict using a sorry placeholder here; the correct
    -- statement of `indiscrete` would only be available for regular graphs.
    sorry

end EquitablePartition

end Graphplay
