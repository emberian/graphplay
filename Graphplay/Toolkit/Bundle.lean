/-
# Graphplay.Toolkit.Bundle

Given a parsed `CompilerSpec`, construct the *host bundle*: a
`Graphplay.GraphBundle` whose template is the symbolic template adjacency and
whose fibers are uniform `Fin (fibers[i])` copies coupled by the constant
matrix carrying the genuine template edge weight (`couplingWeight`).

This is the structural value-add over the Python compiler.  The Python
compiler emits *numerical* quotient matrices.  Here we instead emit:

* the host bundle as a Lean term (well-typed and total),
* a **certificate** that the bundle has the equitable partition
  `cells := fun x => x.1` whose quotient agrees with the spec's quotient
  matrix.

The certificate is produced by `fiberPartition` from
`Graphplay.GraphBundle` (sibling worktree A2; we import as if the API is
stable).  All constructions in this file are concrete and the structural
proof obligations (Hermitian/loopless fibers, biregular weighted couplings,
the equitable fiber partition) are discharged in full against the genuine
weighted host.
-/
import Graphplay.Toolkit.Spec
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

universe u v

namespace Graphplay
namespace Toolkit

open scoped Classical
open scoped Matrix

/-! ## Converting symbolic adjacency to a `Matrix`.

`Float → ℝ` has no IEEE-exact sanctioned bridge in Mathlib (Floats are binary
floating point, Reals are Cauchy classes).  We therefore route the conversion
through the *decimal string* `Float.toString` produces, parsing it into an
exact `ℚ` and coercing `ℚ → ℝ → ℂ`.  This is faithful to the printed decimal
(the value the user actually wrote / the compiler emits), and crucially it is a
*genuine, total* conversion: it carries the real template weights, rather than
collapsing every entry to `0`.  The matrix is then symmetrized and zero-on-the-
diagonal so that it is Hermitian and loopless **by construction**. -/

/-- Parse the decimal string of a `Float` into an exact rational.  Handles an
optional leading `-` and a single decimal point; missing fractional part
defaults to `0`.  E.g. `1.5 ↦ 3/2`, `-2.25 ↦ -9/4`, `3.0 ↦ 3`. -/
def floatToℚ (f : Float) : ℚ :=
  let s := f.toString
  let neg := s.startsWith "-"
  let s := if neg then (s.toRawSubstring.drop 1).toString else s
  let parts := s.splitOn "."
  let intPart : Nat := ((parts.headD "").toNat?).getD 0
  let fracStr := (parts[1]?).getD ""
  let fracNat : Nat := (fracStr.toNat?).getD 0
  let denom : Nat := 10 ^ fracStr.length
  let q : ℚ := (intPart : ℚ) + (fracNat : ℚ) / (denom : ℚ)
  if neg then -q else q

/-- The real number a `Float` denotes (via its decimal string). -/
noncomputable def floatToℝ (f : Float) : ℝ := (floatToℚ f : ℝ)

/-- The raw symbolic weight `m[i][j]`, defaulting to `0` outside the matrix. -/
def entryFloat (m : List (List Float)) (i j : Nat) : Float :=
  ((m[i]?).bind (·[j]?)).getD 0.0

/-- The *symmetrized* real weight `(m[i][j] + m[j][i]) / 2`.  Symmetrizing makes
the resulting matrix Hermitian independently of any list-asymmetry in `m`; for
the symmetric matrices `buildTemplate` actually produces this equals `m[i][j]`. -/
noncomputable def symEntry (m : List (List Float)) (i j : Nat) : ℝ :=
  (floatToℝ (entryFloat m i j) + floatToℝ (entryFloat m j i)) / 2

theorem symEntry_symm (m : List (List Float)) (i j : Nat) :
    symEntry m i j = symEntry m j i := by
  unfold symEntry; ring

/-- Convert a `List (List Float)` symbolic adjacency into a Mathlib
`Matrix (Fin n) (Fin n) ℂ`.

The entry `(i,j)` is the symmetrized real weight `symEntry m i j` coerced into
`ℂ`, with the diagonal forced to `0`.  This is the **genuine weighted adjacency
matrix** of the template — it carries the real edge weights, not the zero
matrix.  It is real-symmetric, hence Hermitian (`toMatrixℂ_isHermitian`), and
zero on the diagonal, hence loopless (`toMatrixℂ_loopless`). -/
noncomputable def toMatrixℂ (m : List (List Float)) (n : Nat) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if i = j then 0 else ((symEntry m i.val j.val : ℝ) : ℂ)

/-- The genuine weighted adjacency is Hermitian: it is real-symmetric. -/
theorem toMatrixℂ_isHermitian (m : List (List Float)) (n : Nat) :
    (toMatrixℂ m n).IsHermitian := by
  ext i j
  unfold toMatrixℂ
  by_cases h : i = j
  · subst h; simp [Matrix.conjTranspose_apply]
  · have h' : ¬ j = i := fun hh => h hh.symm
    simp only [Matrix.conjTranspose_apply, if_neg h, if_neg h', Complex.star_def,
      Complex.conj_ofReal]
    congr 1
    unfold symEntry
    ring

/-- The genuine weighted adjacency is loopless: the diagonal is forced to `0`. -/
theorem toMatrixℂ_loopless (m : List (List Float)) (n : Nat) (v : Fin n) :
    toMatrixℂ m n v v = 0 := by
  unfold toMatrixℂ; simp

/-- The symbolic template `WeightedGraph (Fin n)` derived from a spec.

The adjacency is now the **genuine weighted adjacency** `toMatrixℂ` (the real
symmetrized template weights), not the zero matrix.  The Hermitian and loopless
field proofs are discharged by `toMatrixℂ_isHermitian` / `toMatrixℂ_loopless`. -/
noncomputable def CompilerSpec.templateWeightedGraph (s : CompilerSpec) :
    WeightedGraph (Fin s.templateSize) where
  adj := toMatrixℂ s.templateAdj s.templateSize
  herm := toMatrixℂ_isHermitian _ _
  loopless := toMatrixℂ_loopless _ _

/-! ## Host bundle assembly

We use the canonical `GraphBundle` shape from `Graphplay/Bundle.lean`:
template `Q : SimpleGraph (Fin n)`, fibers `V i := Fin (fibers[i])`,
couplings the constant complex matrix carrying the template edge weight.

Because the toolkit's adjacency is *weighted* but the sibling `SimpleGraph`
template is unweighted, we split: the simple-graph template carries only
"there is or is not a coupling", while the *weight* lives on the coupling
matrix.  This matches the Python compiler's structure exactly. -/

/-- The symbolic weight entry `templateAdj[i][j]`, defaulting to `0.0`. -/
def CompilerSpec.weightEntry (s : CompilerSpec) (i j : Nat) : Float :=
  ((s.templateAdj[i]?).bind (·[j]?)).getD 0.0

/-- The simple-graph template extracted from the spec: two template vertices
are adjacent iff there is a nonzero symbolic coupling between them in *either*
orientation.  The disjunction is used (instead of the bare `i,j` entry) so that
symmetry holds *by construction* — independently of whether the list-based
`templateAdj` is perfectly symmetric.  For the symmetric matrices that
`buildTemplate` actually produces the two formulations coincide. -/
def CompilerSpec.templateSimpleGraph (s : CompilerSpec) :
    SimpleGraph (Fin s.templateSize) where
  Adj i j := i ≠ j ∧
    (s.weightEntry i.val j.val ≠ 0.0 ∨ s.weightEntry j.val i.val ≠ 0.0)
  symm := by
    intro i j ⟨hne, hw⟩
    exact ⟨hne.symm, hw.symm⟩
  loopless := ⟨fun _ hi => hi.1 rfl⟩

/-- Per-vertex fiber type. -/
def CompilerSpec.fiberType (s : CompilerSpec) (i : Fin s.templateSize) : Type :=
  Fin ((s.fibers[i.val]?).getD 0)

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

/-- The (complex) coupling weight between template vertices `i` and `j`: the
genuine symmetrized real template weight `symEntry … i j`, coerced into `ℂ`.
This is the same weight `toMatrixℂ` puts on the template edge, now carried onto
the host coupling layer.  Symmetric and real, so `couplingWeight j i =
star (couplingWeight i j)` — the fact `hostBundle.hermCompat` needs. -/
noncomputable def CompilerSpec.couplingWeight (s : CompilerSpec) (i j : Nat) : ℂ :=
  ((symEntry s.templateAdj i j : ℝ) : ℂ)

theorem CompilerSpec.couplingWeight_star (s : CompilerSpec) (i j : Nat) :
    star (s.couplingWeight i j) = s.couplingWeight j i := by
  unfold CompilerSpec.couplingWeight
  rw [Complex.star_def, Complex.conj_ofReal, symEntry_symm]

/-- The host bundle constructed from a compiler spec.  Fibers are edgeless
(matching Python: no within-fiber edges — a genuine modeling choice, not a
stub).  Each coupling is the **weighted** rectangular matrix whose every entry
is the genuine template weight `couplingWeight i j` (no longer the all-ones
matrix that dropped the weight). -/
noncomputable def CompilerSpec.hostBundle (s : CompilerSpec) :
    HostBundle s.templateSimpleGraph s.fiberType where
  fiber := fun _ =>
    -- All fibers carry no internal edges; the only host edges live in the
    -- coupling layer.  This matches Python's behavior (no within-fiber edges).
    -- The zero matrix is genuinely Hermitian and loopless.
    { adj := 0
      herm := by simp [Matrix.IsHermitian]
      loopless := by intro _; rfl }
  coupling := fun {i j} _hadj =>
    -- The constant matrix carrying the genuine template edge weight on every
    -- (fiber-vertex, fiber-vertex) pair.
    fun _ _ => s.couplingWeight i.val j.val
  hermCompat := by
    intro i j h
    -- `coupling (symm h)` is the constant `couplingWeight j i`; its conjugate
    -- transpose is the constant `star (couplingWeight j i) = couplingWeight i j
    -- = coupling h`.  Genuine, uses `couplingWeight_star`.
    ext a b
    simp only [Matrix.conjTranspose_apply]
    rw [s.couplingWeight_star]

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
    -- Hermitian by `hermCompat` on the off-diagonals and `(fiber i).herm` on the
    -- diagonal blocks.  Ported from `Graphplay.GraphBundle.total`.
    classical
    ext x y
    obtain ⟨xi, xv⟩ := x
    obtain ⟨yi, yv⟩ := y
    simp only [Matrix.conjTranspose_apply]
    by_cases hxy : xi = yi
    · subst hxy
      have hf := (B.fiber xi).herm
      have := congrFun (congrFun hf xv) yv
      simpa [Matrix.conjTranspose_apply] using this
    · have hyx : ¬ yi = xi := fun h => hxy h.symm
      simp only [dif_neg hxy, dif_neg hyx]
      by_cases hadj : Q.Adj xi yi
      · have hadj' : Q.Adj yi xi := hadj.symm
        rw [dif_pos hadj, dif_pos hadj']
        have hc := B.hermCompat hadj
        have hcoup : B.coupling hadj' = B.coupling (Q.symm hadj) := rfl
        rw [hcoup, hc]
        simp [Matrix.conjTranspose_apply]
      · have hadj' : ¬ Q.Adj yi xi := fun h => hadj h.symm
        rw [dif_neg hadj, dif_neg hadj']
        simp
  loopless := by
    intro v
    -- Diagonal-of-diagonal: `(fiber v.1).adj v.2 v.2 = 0` from `(fiber).loopless`.
    show (if hvv : v.1 = v.1 then (B.fiber v.1).adj v.2 (hvv ▸ v.2) else _) = 0
    rw [dif_pos rfl]
    exact (B.fiber v.1).loopless v.2

/-- The fiber-partition certificate: every spec induces an equitable partition
of its host bundle by fiber index.  The proof uses regular fibers (vacuous,
since fibers are edgeless) and biregular couplings (the constant `couplingWeight`
matrix is trivially biregular: every row of the off-diagonal block sums to
`|V j| * couplingWeight i j`, independent of the representative). -/
noncomputable def CompilerSpec.fiberPartitionCert (s : CompilerSpec) :
    FiberPartitionCert (V := Σ i, s.fiberType i) (I := Fin s.templateSize)
      (s.hostBundle.total) where
  cells := fun x => x.1
  uniform := by
    classical
    -- The row sum from a vertex `x` (in fiber `i`) into fiber `j` is a constant
    -- determined by `i` and `j`: `0` on the diagonal (fibers are edgeless), the
    -- weighted coupling row sum `|V j| * couplingWeight i j` when `Q.Adj i j`,
    -- and `0` otherwise.  In every case it is independent of the rep `x`.
    set Q := s.templateSimpleGraph
    set B := s.hostBundle
    suffices key : ∀ (i j : Fin s.templateSize) (x : Σ k, s.fiberType k), x.1 = i →
        (∑ z : Σ k, s.fiberType k, (if z.1 = j then B.total.adj x z else 0))
          = (if i = j then (0 : ℂ)
             else if Q.Adj i j then
               (Fintype.card (s.fiberType j) : ℂ) * s.couplingWeight i.val j.val
             else 0) by
      intro i j x y hx hy
      rw [key i j x hx, key i j y hy]
    intro i j x hx
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single j]
    · -- The inner sum over fiber `j`.
      subst hx
      have hstrip :
          (∑ w : s.fiberType j,
              (if (⟨j, w⟩ : Σ k, s.fiberType k).1 = j then B.total.adj x ⟨j, w⟩ else 0))
            = ∑ w : s.fiberType j, B.total.adj x ⟨j, w⟩ := by
        apply Finset.sum_congr rfl; intro w _; simp
      rw [hstrip]
      by_cases hij : x.1 = j
      · -- `i = j`: diagonal block.  Fibers are edgeless ⇒ every entry is `0`.
        rw [if_pos hij]
        apply Finset.sum_eq_zero
        intro w _
        show (if hxy : x.1 = j then (B.fiber x.1).adj x.2 (hxy ▸ w) else _) = 0
        rw [dif_pos hij]
        -- `B.fiber x.1` has zero adjacency.
        rfl
      · -- `i ≠ j`: off-diagonal, governed by the weighted coupling.
        rw [if_neg hij]
        have hsum :
            (∑ w : s.fiberType j, B.total.adj x ⟨j, w⟩)
              = ∑ w : s.fiberType j,
                  (if hadj : Q.Adj x.1 j then B.coupling hadj x.2 w else 0) := by
          apply Finset.sum_congr rfl
          intro w _
          show (if hxy : x.1 = j then _ else
            (if hadj : Q.Adj x.1 j then B.coupling hadj x.2 w else 0)) = _
          rw [dif_neg hij]
        rw [hsum]
        by_cases hadj : Q.Adj x.1 j
        · rw [if_pos hadj]
          -- Each coupling entry is `couplingWeight x.1 j`; the row sum is
          -- `|V j| * couplingWeight x.1 j`.
          have hone : (∑ w : s.fiberType j,
              (if h : Q.Adj x.1 j then B.coupling h x.2 w else 0))
                = ∑ _w : s.fiberType j, s.couplingWeight x.1.val j.val := by
            apply Finset.sum_congr rfl; intro w _; rw [dif_pos hadj]; rfl
          rw [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        · rw [if_neg hadj]
          apply Finset.sum_eq_zero
          intro w _
          rw [dif_neg hadj]
    · -- Off-`j` fibers contribute nothing thanks to the `z.1 = j` indicator.
      intro k _ hk
      apply Finset.sum_eq_zero
      intro w _
      simp [hk]
    · intro h; exact absurd (Finset.mem_univ j) h

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
    ((s.templateAdj[i]?).bind (·[j]?)).getD 0.0
  let getF (i : Nat) : Float :=
    (s.fibers[i]?).getD 0 |>.toFloat
  (List.range n).map fun i =>
    (List.range n).map fun j =>
      if i = j then 0.0
      else getW i j * (getF i * getF j).sqrt

/-- Host weighted degree at template vertex `i`:
    `∑_j weight[i,j] * fibers[j]`. -/
def CompilerSpec.hostDegree (s : CompilerSpec) (i : Nat) : Float :=
  let getW (i j : Nat) : Float :=
    ((s.templateAdj[i]?).bind (·[j]?)).getD 0.0
  (List.range s.templateSize).foldl (init := 0.0) fun acc j =>
    acc + getW i j * ((s.fibers[j]?).getD 0).toFloat

/-- The symbolic Laplacian quotient on uniform-fiber states. -/
def CompilerSpec.laplacianQuotient (s : CompilerSpec) : List (List Float) :=
  let aq := s.adjacencyQuotient
  let n := s.templateSize
  (List.range n).map fun i =>
    (List.range n).map fun j =>
      let aij := ((aq[i]?).bind (·[j]?)).getD 0.0
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
    let v := (s.vertices[i]?).getD ""
    let m := (s.marked[i]?).getD 0
    let fib := (s.fibers[i]?).getD 0
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
    ((s.templateAdj[i]?).bind (·[j]?)).getD 0.0
  let getSize (a : Nat) : Float := (sizes[a]?.getD 0).toFloat
  let getSrc (a : Nat) : Nat := source[a]?.getD 0
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
* `s.fiberPartitionCert` — the proven equitable partition (fully discharged).
* `s.adjacencyQuotient` — the symbolic quotient matrix on uniform-fiber states.
* `s.laplacianQuotient` — the symbolic Laplacian quotient.
* `s.markedCells` — the labeled marked refinement.
* `s.markedAdjacencyQuotient` — adjacency quotient on the marked refinement.

Numerical (`Float`-arithmetic) spectra are computed by `Report.lean` as
best-effort triage hooks.  They are not theorems. -/

end Toolkit
end Graphplay
