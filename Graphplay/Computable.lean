/-
# Graphplay.Computable

A **computable numerics substrate** for `#eval`-able spectral demos.

Lean's `Complex` is a `noncomputable Field`, which means we cannot directly
`#eval` any matrix arithmetic in `ℂ`.  This module provides a parallel,
*computable* world built on:

* `GaussianRat` — Gaussian rationals `ℚ[i]` as `{re im : ℚ}` with computable
  ring operations (the exact substrate for spectra algebraic over ℚ).
* `Matrix.toGaussianRat` / `GaussianRat.toComplex` — bridges from / to
  Mathlib's `ℂ`.
* A tiny computable linear-algebra layer (multiply, trace, determinant via
  expansion, inverse via Gauss–Jordan) suitable for dimensions ≤ 8.

For numerical (rather than exact) work, see `Graphplay.Computable.Float`.

This file is consciously self-contained: it imports `Mathlib.Data.Rat.Defs`
and `Mathlib.Data.Complex.Basic` only.  No spectral theory leaks in here.

Smoke tests live in `#eval` comments at the bottom.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Complex.Basic

namespace Graphplay

/-! ## Gaussian rationals

`GaussianRat` is the exact computable substrate.  Closed under +, -, *, and
(when nonzero) inversion; not a `Field` instance — we only build what
`#eval` needs and provide the lift `toComplex` for theorem-side use. -/

/-- A Gaussian rational `re + im * i`. -/
structure GaussianRat where
  re : ℚ
  im : ℚ
deriving Repr, DecidableEq, Inhabited

namespace GaussianRat

@[inline] def zero : GaussianRat := ⟨0, 0⟩
@[inline] def one  : GaussianRat := ⟨1, 0⟩
@[inline] def I    : GaussianRat := ⟨0, 1⟩

@[inline] def add (a b : GaussianRat) : GaussianRat :=
  ⟨a.re + b.re, a.im + b.im⟩

@[inline] def neg (a : GaussianRat) : GaussianRat := ⟨-a.re, -a.im⟩

@[inline] def sub (a b : GaussianRat) : GaussianRat :=
  ⟨a.re - b.re, a.im - b.im⟩

@[inline] def mul (a b : GaussianRat) : GaussianRat :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

@[inline] def conj (a : GaussianRat) : GaussianRat := ⟨a.re, -a.im⟩

/-- Squared modulus `|a|² = re² + im²`. Always a rational. -/
@[inline] def normSq (a : GaussianRat) : ℚ := a.re * a.re + a.im * a.im

/-- Multiplicative inverse; returns `0` if input is `0` (so we keep totality
in the computable world). Mathematically correct only on nonzero inputs. -/
@[inline] def inv (a : GaussianRat) : GaussianRat :=
  let n := a.normSq
  if n = 0 then ⟨0, 0⟩
  else ⟨a.re / n, -a.im / n⟩

@[inline] def div (a b : GaussianRat) : GaussianRat := a.mul b.inv

@[inline] def ofRat (q : ℚ) : GaussianRat := ⟨q, 0⟩
@[inline] def ofInt (n : ℤ) : GaussianRat := ⟨(n : ℚ), 0⟩
@[inline] def ofNatGR (n : ℕ) : GaussianRat := ⟨(n : ℚ), 0⟩

instance : Zero GaussianRat := ⟨zero⟩
instance : One  GaussianRat := ⟨one⟩
instance : Add  GaussianRat := ⟨add⟩
instance : Sub  GaussianRat := ⟨sub⟩
instance : Mul  GaussianRat := ⟨mul⟩
instance : Neg  GaussianRat := ⟨neg⟩
instance : Inv  GaussianRat := ⟨inv⟩
instance : Div  GaussianRat := ⟨div⟩
instance : OfNat GaussianRat n := ⟨ofNatGR n⟩
instance : Coe ℚ GaussianRat := ⟨ofRat⟩
instance : Coe ℤ GaussianRat := ⟨ofInt⟩

/-- Decidable test for `q = 0` on `GaussianRat`. -/
@[inline] def isZero (a : GaussianRat) : Bool :=
  decide (a.re = 0) && decide (a.im = 0)

/-- Bridge to `ℂ` (noncomputable, for theorem-side use only). -/
noncomputable def toComplex (a : GaussianRat) : ℂ :=
  ⟨(a.re : ℝ), (a.im : ℝ)⟩

/-- Convenience pretty-printer for `#eval`. -/
def toStr (a : GaussianRat) : String :=
  let r := s!"{a.re}"
  let i := s!"{a.im}"
  if a.im = 0 then r
  else if a.re = 0 then i ++ "i"
  else r ++ " + " ++ i ++ "i"

instance : ToString GaussianRat := ⟨toStr⟩

end GaussianRat

/-! ## Tiny computable matrix layer

We work with `List (List α)`: row-major, square or rectangular.  This is
*not* `Mathlib.Matrix`; the latter is `Fintype`-indexed and not
`#eval`-friendly.  For small demos (≤ 8 × 8) the list representation is
adequate.  The functions live in the `Graphplay` namespace with a `cm`
prefix to keep dot-notation off the underlying `List` type. -/

/-- Number of rows of a `List (List α)`-matrix. -/
@[inline] def cmRows (M : List (List α)) : Nat := M.length

/-- Number of columns (assumes rectangular; `0` if empty). -/
@[inline] def cmCols : List (List α) → Nat
  | [] => 0
  | r :: _ => r.length

/-- Entry at `(i, j)`, using `default` outside bounds. -/
@[inline] def cmGet [Inhabited α] (M : List (List α)) (i j : Nat) : α :=
  (M.getD i []).getD j default

/-- The `n × n` identity matrix. -/
def cmId (α : Type _) [Zero α] [One α] (n : Nat) : List (List α) :=
  (List.range n).map fun i =>
    (List.range n).map fun j => if i = j then (1 : α) else (0 : α)

/-- Pointwise map. -/
@[inline] def cmMap (f : α → β) (M : List (List α)) : List (List β) :=
  M.map (fun r => r.map f)

/-- Transpose; assumes rectangular. -/
def cmTranspose [Inhabited α] (M : List (List α)) : List (List α) :=
  let n := cmCols M
  (List.range n).map fun j => M.map (fun row => row.getD j default)

/-- Entrywise addition. -/
def cmAdd [Add α] (A B : List (List α)) : List (List α) :=
  A.zipWith (fun ra rb => ra.zipWith (· + ·) rb) B

/-- Entrywise subtraction. -/
def cmSub [Sub α] (A B : List (List α)) : List (List α) :=
  A.zipWith (fun ra rb => ra.zipWith (· - ·) rb) B

/-- Naive O(n³) multiplication. -/
def cmMul [Add α] [Mul α] [Zero α] [Inhabited α]
    (A B : List (List α)) : List (List α) :=
  let Bt := cmTranspose B
  A.map fun ra =>
    Bt.map fun cb =>
      (ra.zipWith (· * ·) cb).foldl (· + ·) (0 : α)

/-- Trace = sum of diagonal entries. -/
def cmTrace [Add α] [Zero α] [Inhabited α] (M : List (List α)) : α :=
  (List.range (cmRows M)).foldl (fun acc i => acc + cmGet M i i) (0 : α)

/-- Drop one row and one column (used by `cmDet` and the eliminator). -/
def cmMinor (M : List (List α)) (i j : Nat) : List (List α) :=
  (M.eraseIdx i).map (·.eraseIdx j)

/-- Determinant by cofactor expansion, using an explicit size argument to
make termination painless.  `cmDetAux n M` assumes `M.length = n`; the
public entrypoint `cmDet` supplies `M.length`. -/
def cmDetAux [Add α] [Sub α] [Mul α] [Zero α] [One α] [Neg α] [Inhabited α] :
    Nat → List (List α) → α
  | 0, _ => (1 : α)
  | 1, M => (M.headD []).getD 0 (0 : α)
  | k+2, M =>
    let row0 := M.headD []
    let n := cmCols M
    (List.range n).foldl (fun acc j =>
      let sign : α := if j % 2 = 0 then (1 : α) else -(1 : α)
      let cof := cmDetAux (k+1) (cmMinor M 0 j)
      acc + sign * (row0.getD j (0 : α)) * cof) (0 : α)

/-- Determinant by cofactor expansion along the first row.  O(n!) — fine
for `n ≤ 6`, OK at 7, painful at 8. -/
@[inline] def cmDet [Add α] [Sub α] [Mul α] [Zero α] [One α] [Neg α] [Inhabited α]
    (M : List (List α)) : α :=
  cmDetAux M.length M

/-- Scale a row by a scalar. -/
def cmScaleRow [Mul α] (M : List (List α)) (i : Nat) (c : α) : List (List α) :=
  M.mapIdx fun k r => if k = i then r.map (c * ·) else r

/-- Add `c * (row src)` to `row dst`. -/
def cmAddRowMul [Add α] [Mul α] (M : List (List α))
    (dst src : Nat) (c : α) : List (List α) :=
  let s := M.getD src []
  M.mapIdx fun k r =>
    if k = dst then r.zipWith (fun a b => a + c * b) s else r

/-- Swap two rows. -/
def cmSwapRows (M : List (List α)) (i j : Nat) : List (List α) :=
  let ri := M.getD i []
  let rj := M.getD j []
  M.mapIdx fun k r =>
    if k = i then rj
    else if k = j then ri
    else r

/-! ## Inversion via Gauss–Jordan elimination

For ≤ 8×8 we form `[M | I]`, reduce to `[I | M⁻¹]`, and return the right
half.  If a pivot column has no nonzero entry, we return `none`. -/

/-- Augment `M` (n×n) with the identity on the right, producing an n×(2n)
matrix. -/
def cmAugmentIdent [Zero α] [One α] (M : List (List α)) : List (List α) :=
  let n := cmRows M
  M.mapIdx fun i r =>
    r ++ (List.range n).map (fun j => if i = j then (1 : α) else (0 : α))

/-- Right half of an n×(2n) matrix. -/
def cmRightHalf (M : List (List α)) : List (List α) :=
  let n := cmRows M
  M.map (·.drop n)

/-- One step of Gauss–Jordan: clear column `k` using row `k`.
Returns `none` if no row ≥ k has a nonzero entry in column `k`. -/
def cmGaussStepGR (M : List (List GaussianRat)) (k : Nat) :
    Option (List (List GaussianRat)) :=
  let n := cmRows M
  match (List.range (n - k)).find? (fun off => ¬ (cmGet M (k + off) k).isZero) with
  | none => none
  | some pivotOff =>
    let M := if pivotOff = 0 then M else cmSwapRows M k (k + pivotOff)
    let pivot := cmGet M k k
    let M := cmScaleRow M k pivot.inv
    some <| (List.range n).foldl (fun A i =>
      if i = k then A
      else
        let c := cmGet A i k
        if c.isZero then A else cmAddRowMul A i k (-c)) M

/-- Inverse of an n×n `GaussianRat` matrix via Gauss–Jordan.
Returns `none` if singular. -/
def cmInvGR (M : List (List GaussianRat)) :
    Option (List (List GaussianRat)) := Id.run do
  let n := cmRows M
  let mut aug : List (List GaussianRat) := cmAugmentIdent M
  for k in [0:n] do
    match cmGaussStepGR aug k with
    | none => return none
    | some A => aug := A
  return some (cmRightHalf aug)

/-! ## Bridges to / from `Mathlib.Matrix`

`Matrix.toGaussianRat` is the inverse direction of `GaussianRat.toComplex`
at the matrix level, available *only* when entries are real rationals (we
provide a generic `(Fin n → Fin m → ℚ)` flattener). -/

/-- Convert a `Fin n → Fin m → ℚ` matrix into our row-major form. -/
def Matrix.toCMatrixℚ {n m : Nat} (M : Fin n → Fin m → ℚ) : List (List ℚ) :=
  (List.finRange n).map fun i => (List.finRange m).map fun j => M i j

/-- Lift a rational matrix to `GaussianRat` (imaginary parts zero). -/
def cmRatToGR (M : List (List ℚ)) : List (List GaussianRat) :=
  cmMap GaussianRat.ofRat M

/-- Lift a `GaussianRat` matrix to `ℂ` (noncomputable). -/
noncomputable def cmToComplex (M : List (List GaussianRat)) : List (List ℂ) :=
  cmMap GaussianRat.toComplex M

/-! ## Smoke tests (uncomment to `#eval`)

```
#eval (GaussianRat.I * GaussianRat.I).toStr            -- "-1"
#eval (GaussianRat.ofRat (1/2) + GaussianRat.I).toStr  -- "1/2 + 1i"
#eval cmId GaussianRat 3
#eval
  let A : List (List GaussianRat) :=
    [[⟨1,0⟩, ⟨2,0⟩], [⟨3,0⟩, ⟨4,0⟩]]
  (cmDet A).toStr                                       -- "-2"
#eval
  let A : List (List GaussianRat) :=
    [[⟨1,0⟩, ⟨2,0⟩], [⟨3,0⟩, ⟨4,0⟩]]
  ((cmInvGR A).getD []).map (·.map GaussianRat.toStr)
#eval
  -- Path P_2 adjacency: tr = 0, det = -1.
  let P2 : List (List GaussianRat) := [[⟨0,0⟩, ⟨1,0⟩], [⟨1,0⟩, ⟨0,0⟩]]
  ((cmDet P2).toStr, (cmTrace P2).toStr)               -- ("-1", "0")
```
-/

end Graphplay
