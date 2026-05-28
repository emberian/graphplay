/-
# Graphplay.Computable.Float

`Float` bridges for the `GaussianRat` substrate.  Where `Graphplay.Computable`
keeps everything **exact** (rational arithmetic, no rounding), this module
adds the **numerical** approximation layer: convert a `GaussianRat` matrix
to a `Float × Float`-entry matrix, do power-iteration / Rayleigh-quotient
style numerics, and read off an approximate spectrum.

All `Float` operations are noncomputable-by-the-Lean-purist standard, but
`#eval` runs them happily in practice.  These functions are *triage tools*,
not certificates: any numerical claim derived here must be cross-checked
against the symbolic substrate or against Mathlib's `Matrix.spectrum`.

Power iteration / QR for full spectra is comment-only — implementing a
properly-pivoted QR in `Float` belongs in a numerical library, not here.
-/

import Graphplay.Computable

namespace Graphplay

/-! ## Float complex (compact pair)

We deliberately avoid building a full `FComplex` algebra — Lean's tooling
for that is sparse and we only need a handful of operations.  Just use
`Float × Float` as `(re, im)` and provide helpers. -/

namespace FC

/-- Real part. -/
@[inline] def re (z : Float × Float) : Float := z.1
/-- Imaginary part. -/
@[inline] def im (z : Float × Float) : Float := z.2

@[inline] def zero : Float × Float := (0.0, 0.0)
@[inline] def one  : Float × Float := (1.0, 0.0)

@[inline] def add (a b : Float × Float) : Float × Float :=
  (a.1 + b.1, a.2 + b.2)

@[inline] def sub (a b : Float × Float) : Float × Float :=
  (a.1 - b.1, a.2 - b.2)

@[inline] def mul (a b : Float × Float) : Float × Float :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

@[inline] def conj (a : Float × Float) : Float × Float := (a.1, -a.2)

@[inline] def normSq (a : Float × Float) : Float := a.1 * a.1 + a.2 * a.2

@[inline] def absF (a : Float × Float) : Float := (normSq a).sqrt

@[inline] def scale (c : Float) (a : Float × Float) : Float × Float :=
  (c * a.1, c * a.2)

/-- Format like `"a+bi"`. -/
def toStr (z : Float × Float) : String :=
  if z.2 == 0.0 then s!"{z.1}"
  else if z.1 == 0.0 then s!"{z.2}i"
  else s!"{z.1} + {z.2}i"

end FC

/-! ## Bridges from exact substrate -/

namespace GaussianRat

/-- Convert an integer to a Float, handling sign. -/
@[inline] def intToFloat (n : ℤ) : Float :=
  match n with
  | Int.ofNat k => k.toFloat
  | Int.negSucc k => -((k + 1).toFloat)

/-- Convert a rational to a `Float` via `num / den`. -/
@[inline] def ratToFloat (q : ℚ) : Float := intToFloat q.num / q.den.toFloat

/-- Convert a Gaussian rational to a `Float × Float` pair `(re, im)`. -/
def toFloat (a : GaussianRat) : Float × Float :=
  (ratToFloat a.re, ratToFloat a.im)

/-- Float modulus of a Gaussian rational; useful for printing magnitudes. -/
def toFloatAbs (a : GaussianRat) : Float :=
  FC.absF (a.toFloat)

end GaussianRat

/-! ## Matrix-level bridges -/

/-- Convert a `GaussianRat` matrix to entrywise `Float × Float`. -/
def cmToFloatMatrix (M : List (List GaussianRat)) :
    List (List (Float × Float)) :=
  cmMap GaussianRat.toFloat M

/-- A real `Float` matrix from real parts only — useful when the input is
known to be real-symmetric (Hermitian adjacency matrices, etc.). -/
def cmToRealFloatMatrix (M : List (List GaussianRat)) : List (List Float) :=
  cmMap (fun a => (GaussianRat.toFloat a).1) M

/-! ## Float-matrix arithmetic

Lightweight; we only need what power iteration consumes. -/

/-- Apply a real-Float `n × n` matrix to a Float vector. -/
def cmApplyF (M : List (List Float)) (v : List Float) : List Float :=
  M.map fun row => (row.zipWith (· * ·) v).foldl (· + ·) 0.0

/-- ℓ²-norm of a Float vector. -/
def cmNormF (v : List Float) : Float :=
  (v.foldl (fun s x => s + x * x) 0.0).sqrt

/-- Normalize a Float vector to unit ℓ² norm (returns input unchanged on
zero input). -/
def cmNormalizeF (v : List Float) : List Float :=
  let n := cmNormF v
  if n == 0.0 then v else v.map (· / n)

/-- Inner product `⟨u, v⟩` for real Float vectors. -/
def cmDotF (u v : List Float) : Float :=
  (u.zipWith (· * ·) v).foldl (· + ·) 0.0

/-! ## Numerical eigenvalue triage

`cmPowerIteration` returns an approximate dominant eigenvalue / eigenvector
pair of a real symmetric matrix.  No convergence guarantee — the caller
picks the number of iterations.  For a full spectrum we would need QR with
shifts, which we intentionally leave as a comment-only sketch. -/

/-- Power iteration on a real symmetric `Float` matrix: returns `(λ, v)`
with `M v ≈ λ v` after `iters` steps, starting from the all-ones vector. -/
def cmPowerIteration (M : List (List Float)) (iters : Nat := 64) :
    Float × List Float :=
  let n := cmRows M
  let v0 : List Float := List.replicate n 1.0
  let v0 := cmNormalizeF v0
  let v := (List.range iters).foldl (fun u _ =>
    cmNormalizeF (cmApplyF M u)) v0
  let lam := cmDotF v (cmApplyF M v)
  (lam, v)

/-- **Stub.**  Full QR-with-shifts eigenvalue decomposition.

```
def cmQrEigenvalues (M : List (List Float)) (iters : Nat) :
    List (Float × Float)
```

Properly implementing this requires Householder reflectors, Wilkinson
shifts, and deflation — best left to a dedicated numerics layer.  The
expected signature is recorded above for future implementers. -/
example : True := trivial

/-! ## Smoke tests (uncomment to `#eval`)

```
#eval (GaussianRat.mk (3/2) (-1/4)).toFloat        -- (1.5, -0.25)
#eval
  -- P_3 path adjacency, real symmetric, spectrum {-√2, 0, √2}.
  let P3 : List (List Float) :=
    [[0.0, 1.0, 0.0],
     [1.0, 0.0, 1.0],
     [0.0, 1.0, 0.0]]
  (cmPowerIteration P3 80).1                       -- ≈ 1.4142135…
#eval
  -- C_4 cycle adjacency, spectrum {-2, 0, 0, 2}.
  let C4 : List (List Float) :=
    [[0.0, 1.0, 0.0, 1.0],
     [1.0, 0.0, 1.0, 0.0],
     [0.0, 1.0, 0.0, 1.0],
     [1.0, 0.0, 1.0, 0.0]]
  (cmPowerIteration C4 80).1                       -- ≈ 2.0
```
-/

end Graphplay
