/-
# Graphplay.Integrations.EquitableCertChecker — a **computable equitability
checker** over exact rational arithmetic, with a proved bridge into
`EquitablePartition`.

`Graphplay.Equitable` develops the spectral theory of equitable partitions
(Godsil–Royle "Algebraic Graph Theory" ch. 9; Bachman–Tamon arXiv 1108.0339)
for `WeightedGraph`s over ℂ — but ℂ is not decidable, so none of it can be
*checked on data*.  This file closes that gap in the `LDTKindChecker` style
(computable `Finset` checker + a proved iff bridge + verdicts by `decide`):

* **`isEquitable? A cell : Bool`** — for a rational matrix
  `A : Matrix (Fin n) (Fin n) ℚ` and a cell labelling `cell : Fin n → Fin r`,
  decide whether every two rows in the same cell have equal row sums into every
  target cell.  Row-profiles are materialized once into a `List (List ℚ)` via
  `List.ofFn` (the `acIterate` memoization style), so kernel reduction forces
  each per-row-per-cell sum once instead of re-deriving it per comparison.

* **`isEquitable?_iff`** — checker `true` **iff** the `Prop`-level branching
  condition (the literal `uniform` field of `EquitablePartition`, read over ℚ).
  This is the load-bearing theorem: the `Bool` the kernel computes *is* the
  mathematical equitability condition, not a look-alike.

* **`certifiedPartition`** — the transport: from a checker-`true` verdict,
  an `EquitablePartition G (Fin r)` for any `WeightedGraph` whose adjacency is
  the complex cast `A.map ((↑) : ℚ → ℂ)`.  Casting preserves the row-sum
  equalities (`Rat.cast_sum` + `apply_ite`), so the ℚ certificate yields the
  ℂ object the spectral theory consumes.  `ratWeightedGraph` packages a
  symmetric zero-diagonal rational matrix as such a `WeightedGraph`, with both
  side conditions decidable — so a concrete certificate is three `decide`s.

* **The cube demonstration** — the 3-cube `Q₃` as an 8×8 two-block matrix:
  the antipodal-pair-free split into two 4-cycles linked by a perfect matching
  is equitable (`decide`), with quotient `!![2,1;1,2]`; breaking one in-block
  edge flips the verdict to `false` (`decide`), so the checker discriminates —
  the entries are load-bearing, not just the block shape.  The certified
  partition feeds `restrict_eq_symmQuotient`: the adjacency action on the
  2-dimensional cell-uniform subspace collapses to the 2×2 symmetric quotient.

Verdicts use `decide +kernel` (`Rat.add` is `@[irreducible]`, which blocks the
elaborator-side evaluator but not the kernel); this is still plain kernel
reduction — no `native_decide`, no new axioms.

The companion generated module `Graphplay.Integrations.GQACertSmolLM2`
(emitted by `experiments/export_gqa_cert.py`) instantiates this checker on the
measured head-axis tying structure of SmolLM2-135M's grouped-query attention,
upgrading the `experiments/gqa_defect.json` defect-0 measurement to a
kernel-checked certificate.
-/

import Graphplay.Equitable
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.List.GetD

open scoped Matrix

namespace Graphplay
namespace Integrations
namespace EquitableCert

open scoped BigOperators

variable {n r : ℕ}

/-! ## 1.  The computable checker. -/

/-- The row sum of `A` from row `x` into cell `j`: `∑_{z : cell z = j} A x z`.
Written with the same `if`-guard shape as `EquitablePartition.uniform`, so the
bridge below is definitional on each summand. -/
def cellRowSum (A : Matrix (Fin n) (Fin n) ℚ) (cell : Fin n → Fin r)
    (x : Fin n) (j : Fin r) : ℚ :=
  ∑ z, if cell z = j then A x z else 0

/-- The **memoized row-profile table**: row `x` of the table is the length-`r`
list of `cellRowSum`s of `x` into each target cell.  Materializing the whole
`n × r` table with `List.ofFn` (the `acIterate` style) means kernel reduction
of the checker forces each sum once; the comparison phase then only reads
list literals. -/
def rowProfiles (A : Matrix (Fin n) (Fin n) ℚ) (cell : Fin n → Fin r) :
    List (List ℚ) :=
  List.ofFn fun x : Fin n => List.ofFn fun j : Fin r => cellRowSum A cell x j

/-- **The equitability checker.**  `true` iff any two rows lying in the same
cell have identical row-profiles — i.e. equal total mass into every target
cell.  This is exactly the branching/uniformity condition of an equitable
partition, decided over exact rational arithmetic. -/
def isEquitable? (A : Matrix (Fin n) (Fin n) ℚ) (cell : Fin n → Fin r) : Bool :=
  decide (∀ x y : Fin n, cell x = cell y →
    (rowProfiles A cell).getD x.val [] = (rowProfiles A cell).getD y.val [])

/-! ## 2.  The bridge: checker `true` ↔ the `Prop`-level branching condition. -/

/-- Reading the profile table at a row index recovers that row's profile
function: the `getD` always hits (`x.val < n`), and `List.getElem_ofFn`
re-abstracts it. -/
theorem rowProfiles_getD (A : Matrix (Fin n) (Fin n) ℚ) (cell : Fin n → Fin r)
    (x : Fin n) :
    (rowProfiles A cell).getD x.val []
      = List.ofFn fun j : Fin r => cellRowSum A cell x j := by
  have hx : (x : ℕ) < (rowProfiles A cell).length := by
    simp [rowProfiles]
  rw [List.getD_eq_getElem _ _ hx]
  simp [rowProfiles]

/-- **The bridge.**  The checker returns `true` **iff** the matrix satisfies
the equitable branching condition — stated in the exact shape of
`EquitablePartition.uniform`, over ℚ.  The hypotheses `cell x = i`, `cell y = i`
are essential: rows in *different* cells are allowed (and, for any interesting
partition, required) to have different profiles. -/
theorem isEquitable?_iff (A : Matrix (Fin n) (Fin n) ℚ) (cell : Fin n → Fin r) :
    isEquitable? A cell = true ↔
      ∀ (i j : Fin r) (x y : Fin n), cell x = i → cell y = i →
        (∑ z, if cell z = j then A x z else 0)
          = (∑ z, if cell z = j then A y z else 0) := by
  unfold isEquitable?
  rw [decide_eq_true_iff]
  constructor
  · intro h i j x y hx hy
    have hp := h x y (hx.trans hy.symm)
    rw [rowProfiles_getD, rowProfiles_getD, List.ofFn_inj] at hp
    exact congrFun hp j
  · intro h x y hxy
    rw [rowProfiles_getD, rowProfiles_getD, List.ofFn_inj]
    funext j
    exact h (cell x) j x y rfl hxy.symm

/-! ## 3.  Transport into the ℂ spectral theory. -/

/-- A symmetric, zero-diagonal rational matrix **is** a `WeightedGraph` after
casting to ℂ: rational entries are their own conjugates (`star_ratCast`), so
symmetry gives Hermiticity.  Both hypotheses are decidable for concrete `A`. -/
def ratWeightedGraph (A : Matrix (Fin n) (Fin n) ℚ)
    (hsymm : ∀ i j : Fin n, A j i = A i j) (hdiag : ∀ i : Fin n, A i i = 0) :
    WeightedGraph (Fin n) where
  adj := A.map (fun q => (q : ℂ))
  herm := by
    show (A.map fun q => (q : ℂ))ᴴ = A.map fun q => (q : ℂ)
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_ratCast]
    exact_mod_cast hsymm i j
  loopless := fun v => by simp [Matrix.map_apply, hdiag v]

@[simp] theorem ratWeightedGraph_adj (A : Matrix (Fin n) (Fin n) ℚ)
    (hsymm : ∀ i j : Fin n, A j i = A i j) (hdiag : ∀ i : Fin n, A i i = 0) :
    (ratWeightedGraph A hsymm hdiag).adj = A.map (fun q => (q : ℂ)) := rfl

/-- **The transport.**  A checker-`true` verdict on `(A, cell)` yields an
`EquitablePartition` — the object all of `Graphplay.Equitable`'s spectral
collapse theory consumes — for any `WeightedGraph` whose adjacency is the
complex cast of `A`.  The cast preserves the certified row-sum equalities
because `(↑) : ℚ → ℂ` is a ring hom (`Rat.cast_sum`) and commutes with the
`if`-guard. -/
def certifiedPartition (A : Matrix (Fin n) (Fin n) ℚ) (cell : Fin n → Fin r)
    (G : WeightedGraph (Fin n)) (hG : G.adj = A.map (fun q => (q : ℂ)))
    (h : isEquitable? A cell = true) :
    EquitablePartition G (Fin r) where
  cells := cell
  uniform := by
    intro i j x y hx hy
    have hq := (isEquitable?_iff A cell).mp h i j x y hx hy
    have key : ∀ w : Fin n,
        (∑ z, if cell z = j then G.adj w z else 0)
          = ((∑ z, if cell z = j then A w z else 0 : ℚ) : ℂ) := by
      intro w
      rw [Rat.cast_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : cell z = j <;> simp [hz, hG, Matrix.map_apply]
    rw [key x, key y, hq]

/-- The transport specialized to `ratWeightedGraph`: three `decide`s (symmetry,
zero diagonal, equitability) certify a partition of a concrete rational graph. -/
def certifiedPartitionOfRat (A : Matrix (Fin n) (Fin n) ℚ) (cell : Fin n → Fin r)
    (hsymm : ∀ i j : Fin n, A j i = A i j) (hdiag : ∀ i : Fin n, A i i = 0)
    (h : isEquitable? A cell = true) :
    EquitablePartition (ratWeightedGraph A hsymm hdiag) (Fin r) :=
  certifiedPartition A cell _ rfl h

/-- Matrix literal from a row-major list of lists (the shape
`export_gqa_cert.py` emits).  Out-of-range reads default to `0`, but for an
`n × n` literal with `n` rows of length `n` every read hits. -/
def matOfLists (n : ℕ) (rows : List (List ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (rows.getD i.val []).getD j.val 0

/-! ## 4.  Synthetic verdict: the 3-cube as a two-block 8×8 certificate.

`Q₃` split into the "bottom" 4-cycle `{0,1,2,3}` and the "top" 4-cycle
`{4,5,6,7}`, joined by the perfect matching `i ↔ i+4`.  Every vertex has
exactly 2 neighbours in its own cell and 1 in the other, so the 2-cell
partition is equitable with quotient `!![2,1; 1,2]` — but the matrix is *not*
block-constant, so a checker that merely detected constant blocks would reject
it.  Removing the single edge `0–1` breaks vertex 0's in-cell count and the
verdict flips to `false`: the certificate depends on the actual entries. -/

/-- The 3-cube `Q₃`: two 4-cycles (`0-1-2-3`, `4-5-6-7`) plus the matching
`i ↔ i+4`. -/
def cubeA : Matrix (Fin 8) (Fin 8) ℚ := matOfLists 8
  [[0,1,0,1, 1,0,0,0],
   [1,0,1,0, 0,1,0,0],
   [0,1,0,1, 0,0,1,0],
   [1,0,1,0, 0,0,0,1],
   [1,0,0,0, 0,1,0,1],
   [0,1,0,0, 1,0,1,0],
   [0,0,1,0, 0,1,0,1],
   [0,0,0,1, 1,0,1,0]]

/-- `Q₃` with the in-block edge `0–1` deleted — the negative control. -/
def cubeBrokenA : Matrix (Fin 8) (Fin 8) ℚ := matOfLists 8
  [[0,0,0,1, 1,0,0,0],
   [0,0,1,0, 0,1,0,0],
   [0,1,0,1, 0,0,1,0],
   [1,0,1,0, 0,0,0,1],
   [1,0,0,0, 0,1,0,1],
   [0,1,0,0, 1,0,1,0],
   [0,0,1,0, 0,1,0,1],
   [0,0,0,1, 1,0,1,0]]

/-- The two-block cell labelling: bottom square ↦ 0, top square ↦ 1. -/
def cubeCell : Fin 8 → Fin 2 := fun i => if i.val < 4 then 0 else 1

set_option maxRecDepth 100000

/-- The two-block split of `Q₃` is equitable — kernel-computed verdict. -/
theorem cube_isEquitable : isEquitable? cubeA cubeCell = true := by decide +kernel

/-- Deleting one edge destroys equitability — the checker discriminates on
entries, not on block shape. -/
theorem cubeBroken_not_equitable : isEquitable? cubeBrokenA cubeCell = false := by
  decide +kernel

/-- `Q₃` as a `WeightedGraph` (symmetry and looplessness by `decide`). -/
def cubeGraph : WeightedGraph (Fin 8) :=
  ratWeightedGraph cubeA (by decide +kernel) (by decide +kernel)

/-- The certified equitable partition of the cube: the checker verdict
transported into the spectral theory. -/
def cubePartition : EquitablePartition cubeGraph (Fin 2) :=
  certifiedPartition cubeA cubeCell cubeGraph rfl cube_isEquitable

/-- **The instantiated collapse.**  On the 2-dimensional cell-uniform subspace
of the certified partition, the 8×8 cube adjacency acts as its 2×2 symmetric
quotient (`restrict_eq_symmQuotient`): an 8-fold dimension reduction whose
hypothesis was established by kernel computation, not by hand. -/
theorem cube_collapse (w : Fin 2 → ℂ) :
    cubeGraph.adj.mulVec (fun v => ∑ i, w i * cubePartition.cellUniformVec i v)
      = fun v => ∑ i,
          (cubePartition.symmQuotient.mulVec w) i * cubePartition.cellUniformVec i v :=
  cubePartition.restrict_eq_symmQuotient w

/-! ## 5.  End-of-file inventory.

**BUILT:**
  * §1 — `cellRowSum`, `rowProfiles` (memoized `n × r` table), **`isEquitable?`**
    (the `Bool` checker over exact ℚ arithmetic).
  * §2 — `rowProfiles_getD`, **`isEquitable?_iff`** (checker ↔ the literal
    `EquitablePartition.uniform` condition over ℚ).
  * §3 — `ratWeightedGraph` (symmetric zero-diagonal ℚ matrix → `WeightedGraph`),
    **`certifiedPartition`** / `certifiedPartitionOfRat` (checker-`true` →
    `EquitablePartition` over ℂ), `matOfLists`.
  * §4 — `cubeA`/`cubeCell` with **`cube_isEquitable`** (`decide`),
    `cubeBroken_not_equitable` (negative control, `decide`), `cubeGraph`,
    `cubePartition`, and **`cube_collapse`** (the spectral collapse applied to
    the kernel-certified partition).

**SCOPE:**
  * The checker certifies the *branching condition*; spectral consequences
    (quotient Hermiticity, subspace invariance, the collapse) are inherited
    from `Graphplay.Equitable`, not re-proved.
  * `decide +kernel` is used because core marks `Rat.add` `@[irreducible]`
    (blocking the elaborator-side evaluator); the proof is still pure kernel
    reduction with the standard axioms.
-/

end EquitableCert
end Integrations
end Graphplay
