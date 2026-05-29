/-
# Graphplay.ForMathlib — upstream-bound infrastructure

This namespace is the **staging area for results that are not specific to
Graphplay's quantum-walk story but are general mathematical infrastructure that
Mathlib currently lacks.**  The intent is that everything under
`Graphplay/ForMathlib/` is eventually polished into Mathlib pull requests.

Rules of the road for contributors / agents:

* If you are filling a `sorry` whose content is *graphplay-specific* (the
  equitable-partition spectral lift, PST transport, bundle equitability, …),
  prove it **in place** in its own module.
* If you are filling a `sorry` whose content is *general infrastructure*
  (Hilbert–Schmidt integral operators on `L²`, a bundled category of operator
  systems / unital `*`-algebras and its UCP morphisms, sheaves valued in such a
  category, generic `Matrix.IsHermitian` spectral helpers, …), **extract it as a
  named lemma/def here** with canonical Mathlib-style naming, and have the
  graphplay module use it.  This keeps the upstream-bound surface separate and
  PR-ready.

Each file in this directory should carry, at the top, a one-line note on the
target Mathlib file it is destined for, e.g.
`-- target: Mathlib/Analysis/InnerProductSpace/HilbertSchmidt.lean`.

Current planned modules (created on demand):

* `ForMathlib/HilbertSchmidt.lean` — kernel integral operators on `L²(μ)`, their
  boundedness (Hilbert–Schmidt norm bound), self-adjointness from a Hermitian
  kernel.  Unblocks `Graphplay/Graphon.lean :: Graphon.op`.
* `ForMathlib/OperatorSystem.lean` — bundled category of finite-dimensional
  operator systems with UCP morphisms; Choi-matrix characterisation of complete
  positivity.  Unblocks `Graphplay/OperatorSystem.lean`.
* `ForMathlib/StarAlgSheaf.lean` — sheaves valued in a bundled category of unital
  `*`-algebras; the constant-sheaf construction and its sheaf condition.
  Unblocks `Graphplay/Tower6.lean :: constSheaf`.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian

open scoped Matrix

namespace Graphplay.ForMathlib

/-- A Hermitian matrix is a self-adjoint element of the `*`-ring of matrices.

This is the small but genuinely reusable bridge between Mathlib's two
formulations of "self-adjointness" for matrices: the bespoke
`Matrix.IsHermitian` predicate (`Aᴴ = A`) and the general algebraic
`IsSelfAdjoint` predicate (`star A = A`).  On `Matrix V V R` the star
operation *is* the conjugate transpose, so the two notions agree
definitionally; packaging the conversion as a named lemma lets the
operator-algebraic towers (`QuantumGraph`, `Tower6`) treat a Hermitian
adjacency as a self-adjoint algebra element without re-deriving it.

Target: `Mathlib/LinearAlgebra/Matrix/Hermitian.lean`. -/
theorem isSelfAdjoint_of_isHermitian
    {V : Type*} {R : Type*} [Fintype V] [NonUnitalNonAssocSemiring R] [StarRing R]
    {A : Matrix V V R} (h : A.IsHermitian) : IsSelfAdjoint A :=
  h

/-- The converse: a self-adjoint matrix (in the algebraic `star` sense) is
Hermitian.  Together with `isSelfAdjoint_of_isHermitian` this records the
definitional equivalence `Matrix.IsHermitian A ↔ IsSelfAdjoint A`. -/
theorem isHermitian_of_isSelfAdjoint
    {V : Type*} {R : Type*} [Fintype V] [NonUnitalNonAssocSemiring R] [StarRing R]
    {A : Matrix V V R} (h : IsSelfAdjoint A) : A.IsHermitian :=
  h

end Graphplay.ForMathlib
