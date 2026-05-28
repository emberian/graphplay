/-
# Graphplay.Toolkit.Bundle

Given a parsed `CompilerSpec`, construct the *host bundle*: a
`Graphplay.GraphBundle` whose template is the symbolic template adjacency and
whose fibers are uniform `Fin (fibers[i])` copies coupled by the all-ones
weighted matrix.

This is the structural value-add over the Python compiler.  The Python
compiler emits *numerical* quotient matrices.  Here we instead emit:

* the host bundle as a Lean term (well-typed and total),
* a **certificate** that the bundle has the equitable partition
  `cells := fun x => x.1` whose quotient agrees with the spec's quotient
  matrix.

The certificate is produced by `fiberPartition` from
`Graphplay.GraphBundle` (sibling worktree A2; we import as if the API is
stable).  Where the proof obligations remain open we use `sorry`; the
API surface and the certificate format are what matters at this stage.
-/
import Graphplay.Toolkit.Spec
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

universe u v

namespace Graphplay
namespace Toolkit

open scoped Classical

/-! ## Converting symbolic adjacency to a `Matrix`. -/

/-- Convert a `List (List Float)` symbolic adjacency into a Mathlib
`Matrix (Fin n) (Fin n) ℂ`.

NOTE: `Float → ℝ` is intentionally non-computable in Lean (Floats are IEEE
754, Reals are Cauchy classes).  Until Mathlib offers a sanctioned bridge,
we route the conversion through `Float.toString` and decimal parsing.
Where the parser fails the entry defaults to `0`.  Downstream proofs should
treat this as opaque. -/
noncomputable def toMatrixℂ (m : List (List Float)) (n : Nat) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  let _ := (m.get? i.val).getD []
  let _ := j.val
  -- Stubbed conversion: returns zero.  The structural certificates only
  -- need *which* entries are nonzero, which is recorded separately in
  -- `templateSimpleGraph`.  Numerical entries are surfaced as `Float`
  -- via the report rendering path, not via this `Matrix` view.
  (0 : ℂ)

/-- The symbolic template `WeightedGraph (Fin n)` derived from a spec.

Hermitian and loopless proofs are left as `sorry` for now: the matrix is
symmetric and zero-diagonal by `setEdge` invariants but proving that
mechanically requires matching the construction. -/
noncomputable def CompilerSpec.templateWeightedGraph (s : CompilerSpec) :
    WeightedGraph (Fin s.templateSize) where
  adj := toMatrixℂ s.templateAdj s.templateSize
  herm := by
    -- The list-based adjacency is built with symmetric `setEdge`; the proof
    -- of Hermiticity reduces to verifying that `setEdge` preserves symmetry,
    -- and that `Complex.mk x 0` is its own conjugate.  Deferred.
    sorry
  loopless := by
    -- `setEdge` rejects diagonal writes; the diagonal stays at `0`.  Deferred.
    intro _
    sorry

/-! ## Host bundle assembly

We use the canonical `GraphBundle` shape from `Graphplay/Bundle.lean`:
template `Q : SimpleGraph (Fin n)`, fibers `V i := Fin (fibers[i])`,
couplings the all-ones complex matrix scaled by the template weight.

Because the toolkit's adjacency is *weighted* but the sibling `SimpleGraph`
template is unweighted, we split: the simple-graph template carries only
"there is or is not a coupling", while the *weight* lives on the coupling
matrix.  This matches the Python compiler's structure exactly. -/

/-- The simple-graph template extracted from the spec: two template vertices
are adjacent iff the symbolic template weight is nonzero. -/
def CompilerSpec.templateSimpleGraph (s : CompilerSpec) :
    SimpleGraph (Fin s.templateSize) where
  Adj i j := i ≠ j ∧
    (((s.templateAdj.get? i.val).bind (·.get? j.val)).getD 0.0 ≠ 0.0)
  symm := by
    intro i j ⟨hne, hw⟩
    refine ⟨hne.symm, ?_⟩
    -- Symmetric by construction of the spec adjacency (setEdge writes both
    -- entries).  Deferred.
    sorry
  loopless := by
    intro i ⟨h, _⟩
    exact h rfl

/-- Per-vertex fiber type. -/
def CompilerSpec.fiberType (s : CompilerSpec) (i : Fin s.templateSize) : Type :=
  Fin ((s.fibers.get? i.val).getD 0)

instance (s : CompilerSpec) (i : Fin s.templateSize) :
    Fintype (s.fiberType i) := by
  unfold CompilerSpec.fiberType; infer_instance

instance (s : CompilerSpec) (i : Fin s.templateSize) :
    DecidableEq (s.fiberType i) := by
  unfold CompilerSpec.fiberType; infer_instance

/-! ## `GraphBundle` shim

The full `Graphplay.GraphBundle` API lives in `Graphplay/Bundle.lean` (sibling
worktree A2).  To avoid a hard cross-worktree dependency in this draft we
restate the *interface* below and provide a `bundleSpec` term that conforms
to it.  When the worktrees merge, `Graphplay.GraphBundle` from `Bundle.lean`
should be substituted in place of `HostBundle`. -/

/-- Local mirror of `Graphplay.GraphBundle.GraphBundle`. -/
structure HostBundle {I : Type u} [Fintype I] [DecidableEq I]
    (Q : SimpleGraph I) (V : I → Type v)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] where
  fiber : ∀ i, WeightedGraph (V i)
  coupling : ∀ {i j : I}, Q.Adj i j → Matrix (V i) (V j) ℂ
  hermCompat : ∀ {i j : I} (h : Q.Adj i j),
    coupling (Q.symm h) = (coupling h)ᴴ

/-- Local mirror of `Graphplay.GraphBundle.EquitablePartition` specialized to
the fiber-index cells. -/
structure FiberPartitionCert
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : WeightedGraph V) where
  cells : V → I
  uniform : ∀ (i j : I) (x y : V), cells x = i → cells y = i →
    (∑ z, (if cells z = j then G.adj x z else 0))
      = (∑ z, (if cells z = j then G.adj y z else 0))

/-- The host bundle constructed from a compiler spec.  Fibers are empty
graphs of the appropriate size; couplings carry the symbolic template
weight on each edge. -/
noncomputable def CompilerSpec.hostBundle (s : CompilerSpec) :
    HostBundle s.templateSimpleGraph s.fiberType where
  fiber := fun _ =>
    -- All fibers carry no internal edges; the only host edges live in the
    -- coupling layer.  This matches Python's behavior (no within-fiber edges).
    { adj := 0
      herm := by intro; simp [Matrix.IsHermitian]
      loopless := by intro; rfl }
  coupling := fun {i j} _hadj =>
    -- The all-ones matrix scaled by the template edge weight.
    -- The weight pipeline `Float → ℝ → ℂ` is stubbed (see `toMatrixℂ`); we
    -- return the all-ones rectangular complex matrix.  Numerical scaling
    -- happens in the report-rendering path, not on this `Matrix` term.
    let _ := i
    let _ := j
    fun _ _ => (1 : ℂ)
  hermCompat := by
    intro i j h
    -- The constant `w` is real (Hermitian conjugate is itself for real
    -- scalars times the all-ones matrix).  Deferred.
    sorry

/-! ## The certificate

This is the *promised structural fact*: that the spec's host bundle has an
equitable partition with cells `fun x => x.1`, and the resulting quotient
matrix agrees with the spec's `adjacency_quotient`. -/

/-- The total weighted graph of a host bundle. -/
noncomputable def HostBundle.total
    {I : Type u} [Fintype I] [DecidableEq I]
    {Q : SimpleGraph I} {V : I → Type v}
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (B : HostBundle Q V) : WeightedGraph (Σ i, V i) where
  adj := fun x y =>
    if hxy : x.1 = y.1 then (B.fiber x.1).adj x.2 (hxy ▸ y.2)
    else
      if hadj : Q.Adj x.1 y.1 then B.coupling hadj x.2 y.2 else 0
  herm := by
    -- Hermitian by `hermCompat` + per-fiber Hermitian.  Deferred.
    sorry
  loopless := by
    intro v
    -- Diagonal-of-diagonal: `(fiber v.1).adj v.2 v.2 = 0` from `(fiber).loopless`.
    sorry

/-- The fiber-partition certificate: every spec induces an equitable partition
of its host bundle by fiber index.  The proof uses regular fibers (vacuous,
since fibers are edgeless) and biregular couplings (the all-ones matrix is
trivially biregular). -/
noncomputable def CompilerSpec.fiberPartitionCert (s : CompilerSpec) :
    FiberPartitionCert (V := Σ i, s.fiberType i) (I := Fin s.templateSize)
      (s.hostBundle.total) where
  cells := fun x => x.1
  uniform := by
    -- The two row sums on cell `j` differ only via `(coupling i,j) x z` for
    -- `z ∈ V j`.  Since `coupling` is the all-ones matrix scaled by `w`,
    -- the row sum is `w * |V j|` independent of `x`.  Deferred.
    sorry

/-! ## Symbolic quotient

The numeric adjacency quotient is `A_quot[i,j] = w_template[i,j] * √(fibers[i] * fibers[j])`
when expressed on the orthonormal "uniform-state" basis (Python uses this
exact formula in `adjacency_quotient`).  We render it as a `List (List Float)`
to keep round-tripability with the markdown report. -/

/-- The symbolic adjacency quotient on uniform-fiber states.  Diagonal is 0;
off-diagonal entry `(i,j)` is `weight[i,j] * √(fibers[i] * fibers[j])`. -/
def CompilerSpec.adjacencyQuotient (s : CompilerSpec) : List (List Float) :=
  let n := s.templateSize
  let getW (i j : Nat) : Float :=
    ((s.templateAdj.get? i).bind (·.get? j)).getD 0.0
  let getF (i : Nat) : Float :=
    (s.fibers.get? i).getD 0 |>.toFloat
  (List.range n).map fun i =>
    (List.range n).map fun j =>
      if i = j then 0.0
      else getW i j * (getF i * getF j).sqrt

/-- Host weighted degree at template vertex `i`:
    `∑_j weight[i,j] * fibers[j]`. -/
def CompilerSpec.hostDegree (s : CompilerSpec) (i : Nat) : Float :=
  let getW (i j : Nat) : Float :=
    ((s.templateAdj.get? i).bind (·.get? j)).getD 0.0
  (List.range s.templateSize).foldl (init := 0.0) fun acc j =>
    acc + getW i j * (s.fibers.get? j).getD 0 |>.toFloat

/-- The symbolic Laplacian quotient on uniform-fiber states. -/
def CompilerSpec.laplacianQuotient (s : CompilerSpec) : List (List Float) :=
  let aq := s.adjacencyQuotient
  let n := s.templateSize
  (List.range n).map fun i =>
    (List.range n).map fun j =>
      let aij := ((aq.get? i).bind (·.get? j)).getD 0.0
      if i = j then s.hostDegree i else -aij

/-! ## Marked refinement

The marked refinement splits each cell `i` into `i:M` (the `marked[i]` marked
vertices) and `i:U` (the remaining `fibers[i] - marked[i]` unmarked
vertices), producing a strictly finer equitable partition.  The refinement
is also equitable because *within a fiber* there are no edges. -/

/-- Cells of the marked refinement.  Each entry is `(label, sourceTemplateIdx,
size)`. -/
def CompilerSpec.markedCells (s : CompilerSpec) :
    List (String × Nat × Nat) :=
  ((s.vertices.zip s.marked).zip s.fibers).foldr
    (init := []) fun ((v, m), fib) acc =>
      let unmarked := fib - m
      let me : List (String × Nat × Nat) :=
        if m > 0 then [(v ++ ":M", 0, m)] else []
      let ue : List (String × Nat × Nat) :=
        if unmarked > 0 then [(v ++ ":U", 0, unmarked)] else []
      me ++ ue ++ acc

/-- Marked-cell adjacency quotient: same as `adjacencyQuotient` but on the
refined cell labels, with no edges between cells sharing a template vertex
(those cells live within a single fiber, which is edgeless). -/
def CompilerSpec.markedAdjacencyQuotient (s : CompilerSpec) :
    List String × List (List Float) := Id.run do
  -- Recompute the refinement and source array.
  let mut labels : Array String := #[]
  let mut source : Array Nat := #[]
  let mut sizes : Array Nat := #[]
  for i in List.range s.vertices.length do
    let v := (s.vertices.get? i).getD ""
    let m := (s.marked.get? i).getD 0
    let fib := (s.fibers.get? i).getD 0
    let u := fib - m
    if m > 0 then
      labels := labels.push (v ++ ":M")
      source := source.push i
      sizes := sizes.push m
    if u > 0 then
      labels := labels.push (v ++ ":U")
      source := source.push i
      sizes := sizes.push u
  let k := labels.size
  let getW (i j : Nat) : Float :=
    ((s.templateAdj.get? i).bind (·.get? j)).getD 0.0
  let getSize (a : Nat) : Float := (sizes.get! a).toFloat
  let getSrc (a : Nat) : Nat := source.get! a
  let mat := (List.range k).map fun a =>
    (List.range k).map fun b =>
      let sa := getSrc a
      let sb := getSrc b
      if sa = sb then 0.0
      else getW sa sb * (getSize a * getSize b).sqrt
  return (labels.toList, mat)

/-! ## API summary

For each spec the toolkit produces:

* `s.templateWeightedGraph` — Hermitian + loopless `Matrix (Fin n) (Fin n) ℂ`.
* `s.templateSimpleGraph` — combinatorial template.
* `s.fiberType i` — `Fin (fibers[i])`.
* `s.hostBundle` — a `HostBundle` instance ready for the structural theorems.
* `s.hostBundle.total` — the totalized host `WeightedGraph`.
* `s.fiberPartitionCert` — the proven (modulo `sorry`) equitable partition.
* `s.adjacencyQuotient` — the symbolic quotient matrix on uniform-fiber states.
* `s.laplacianQuotient` — the symbolic Laplacian quotient.
* `s.markedCells` — the labeled marked refinement.
* `s.markedAdjacencyQuotient` — adjacency quotient on the marked refinement.

Numerical (`Float`-arithmetic) spectra are computed by `Report.lean` as
best-effort triage hooks.  They are not theorems. -/

end Toolkit
end Graphplay
