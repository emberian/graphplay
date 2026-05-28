/-
# Graphplay.StdLib.Computable

Aggregator for the **computable rational companions** of the StdLib
graph families.  The symbolic, ℂ-valued definitions in
`Graphplay.StdLib.{Path, Hypercube, Hamming, Cayley, CompleteMultipartite}`
are `noncomputable` (they live over `ℂ`), so they cannot be `#eval`ed
directly.  This file collects their **rational** `*ℚ` counterparts —
the same 0/1 adjacency matrices but with `ℚ` entries — and bundles
smoke tests across all five families.

A `Matrix _ _ ℚ` can be lifted to `Matrix _ _ ℂ` via
`Matrix.map (algebraMap ℚ ℂ)` whenever the spectral / Hermitian theory
needs the complex picture.
-/

import Graphplay.StdLib.Path
import Graphplay.StdLib.Hypercube
import Graphplay.StdLib.Cycle
import Graphplay.StdLib.Hamming
import Graphplay.StdLib.CompleteMultipartite

open scoped Matrix

namespace Graphplay
namespace StdLib

/-! ## Computable bridge predicate (statement only) -/

/-- A StdLib entry is **computably bridged** if there exists a
`ℚ`-valued adjacency presentation that agrees with the symbolic
`ℂ`-valued one after the canonical ring embedding `ℚ ↪ ℂ`.

This is a statement-level predicate; concrete witnesses live with each
family (e.g. `Path.adjMatrixℚ`, `Hypercube.adjMatrixℚ`,
`Cycle.adjMatrixℚ`, plus the Hamming/CompleteMultipartite analogues
that follow directly from their definitions). -/
def IsComputableStdLibEntry
    (V : Type) [Fintype V] [DecidableEq V]
    (adjℂ : Matrix V V ℂ) : Prop :=
  ∃ adjℚ : Matrix V V ℚ,
    adjℂ = adjℚ.map (fun q => (q : ℂ))

/-! ## Computable Hamming adjacency (q-ary)

The symbolic `Hamming n q` lives over `ℂ`; here is its computable
0/1 ℚ-valued companion on `Fin n → Fin q`. -/

/-- Computable companion to `Hamming n q`: 0/1 adjacency in `ℚ`. -/
def Hamming.adjMatrixℚ (n q : ℕ) :
    Matrix (Fin n → Fin q) (Fin n → Fin q) ℚ :=
  fun x y => if hammingDistFn x y = 1 then (1 : ℚ) else 0

/-! ## Computable complete-multipartite adjacency

The symbolic `CompleteMultipartite parts` lives over `ℂ`; here is its
0/1 ℚ-valued companion. -/

/-- Computable companion to `CompleteMultipartite parts`. -/
def CompleteMultipartite.adjMatrixℚ (parts : List ℕ) :
    Matrix (CompleteMultipartiteV parts) (CompleteMultipartiteV parts) ℚ :=
  fun x y => if x.1 ≠ y.1 then (1 : ℚ) else 0

/-! ## Smoke-test bundle — all five families -/

-- Path family
#eval (Path.adjMatrixℚ 4) ⟨0, by decide⟩ ⟨1, by decide⟩          -- 1
#eval Matrix.trace (Path.adjMatrixℚ 4)                            -- 0

-- Cycle family
#eval Cycle.numVertices 5                                         -- 5
#eval Cycle.numEdges 5                                            -- 5
#eval (Cycle.adjMatrixℚ 5) ⟨0, by decide⟩ ⟨4, by decide⟩         -- 1

-- Hypercube family
#eval Hypercube.numEdges 3                                        -- 12
#eval (Hypercube.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨1, by decide⟩     -- 1
#eval (Hypercube.adjMatrixℚ 3) ⟨0, by decide⟩ ⟨7, by decide⟩     -- 0

-- Hamming family: H(2, 3) — strings of length 2 over alphabet of size 3
#eval (Hamming.adjMatrixℚ 2 3
        (fun i => if i.val = 0 then ⟨0, by decide⟩ else ⟨0, by decide⟩)
        (fun i => if i.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩))
-- expected: 1 (strings (0,0) and (1,0) differ in exactly one coordinate)

-- CompleteMultipartite family: K_{2,2} — adjacent iff parts differ
#eval (CompleteMultipartite.adjMatrixℚ [2, 2]
        ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
        ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩)
-- expected: 1 (parts 0 and 1 differ)

#eval (CompleteMultipartite.adjMatrixℚ [2, 2]
        ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
        ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩)
-- expected: 0 (same part)

end StdLib
end Graphplay
