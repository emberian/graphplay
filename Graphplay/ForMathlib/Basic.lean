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

namespace Graphplay.ForMathlib

/-- Sentinel so the namespace is non-empty before any infrastructure lands.
Replace usages as real lemmas are added. -/
theorem forMathlib_namespace_anchor : True := trivial

end Graphplay.ForMathlib
