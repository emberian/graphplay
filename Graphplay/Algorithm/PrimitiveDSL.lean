/-
# Graphplay.Algorithm.PrimitiveDSL

The end-to-end front-end of the Lean toolkit's compiler.  A user
supplies a `PrimitiveSpec` (a JSON-friendly record naming a primitive,
a hardware target, and a list of parameters); the toolkit produces a
`CompilerOutput` carrying a host weighted graph, an equitable
partition into cells, a Hamiltonian schedule, and a machine-checkable
certificate of which primitive the host realises.

This file orchestrates the steps:

1.  **Spec parsing.**  Done upstream (`Graphplay.Toolkit.Spec`); we
    accept the parsed structure here.
2.  **Quotient choice.**  Pick the smallest known-family quotient
    whose spectrum supports the requested primitive, via the
    `Graphplay.Algorithm.StdLibMatch` recogniser.
3.  **Bundle inflation.**  Use `Graphplay.Bundle` to inflate the
    quotient template into the requested host vertex count.
4.  **Chiral optimisation.**  Run `Graphplay.Algorithm.ChiralOpt` to
    pick the best chiral signing of the bundle for the target.
5.  **Certificate emission.**  Package the result, including a
    schedule and a `ProvenPrimitive` witness.

All numerical evaluation is `IO`-bound and `sorry`-marked; the API
surface is stable.  Statements outnumber proofs by a wide margin.
Computability is aspirational throughout.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.Bundle
import Graphplay.Chiral
import Graphplay.PST
import Graphplay.Mixing
import Graphplay.Search
import Graphplay.Toolkit.Hardware
import Graphplay.Toolkit.Scheduler
import Graphplay.Toolkit.Spec
import Graphplay.Algorithm.ChiralOpt
import Graphplay.Algorithm.StdLibMatch

open Classical

universe u v

namespace Graphplay
namespace Algorithm

/-! ## Primitive kinds

The five canonical primitives the compiler emits proofs for.  Each
matches a separate `Graphplay/*` content file (PST.lean, Mixing.lean,
Search.lean, etc.). -/

/-- Which named quantum-walk primitive the user asked for. -/
inductive PrimitiveKind where
  /-- Perfect state transfer between two endpoints. -/
  | PST
  /-- Uniform mixing on the cell-uniform subspace. -/
  | Mix
  /-- Spatial search against a marked set. -/
  | Search
  /-- Fractional revival. -/
  | FR
  /-- Sampling from a stationary or quasistationary distribution. -/
  | Sample
deriving Repr, Inhabited, DecidableEq

/-! ## Parameter records

A `PrimitiveParam` is a string-keyed numeric value pair, matching the
JSON parameter blob.  The list is positional only at the schema level;
the compiler reads named fields out of it. -/

/-- A single key/value parameter for a primitive spec.  Mirrors a JSON
field. -/
inductive PrimitiveParam where
  /-- Floating-point parameter. -/
  | float (key : String) (value : Float)
  /-- Integer parameter. -/
  | nat (key : String) (value : Nat)
  /-- String-valued parameter. -/
  | str (key : String) (value : String)
  /-- List of indices (e.g. marked vertices). -/
  | natList (key : String) (value : List Nat)
deriving Repr, Inhabited

namespace PrimitiveParam

/-- The key (name) of a parameter. -/
def key : PrimitiveParam → String
  | .float k _   => k
  | .nat k _     => k
  | .str k _     => k
  | .natList k _ => k

end PrimitiveParam

/-- Look up a parameter by name; returns `none` if absent. -/
def PrimitiveSpec.lookupParam? (params : List PrimitiveParam) (k : String) :
    Option PrimitiveParam :=
  params.find? (·.key = k)

/-! ## The top-level spec

A `PrimitiveSpec` is the front-door object.  Its three fields mirror
the JSON schema in `tools/search_compiler.py` (now superseded by the
Lean toolkit) and `Graphplay.Toolkit.Spec.CompilerSpec`. -/

/-- A user-facing compiler input: which primitive, on what hardware,
with what parameters.  JSON-friendly. -/
structure PrimitiveSpec where
  /-- The primitive the user wants compiled. -/
  primitive : PrimitiveKind
  /-- Hardware capabilities (qubit count, layout, allowed phases, …). -/
  hardware : HardwareSpec
  /-- Free-form parameter list (target indices, tolerances, scan
  ranges, schedule durations, …). -/
  parameters : List PrimitiveParam
  /-- Optional human-readable label, copied to the report. -/
  label : String := ""

/-- Convenience: a totally default spec (PST on unconstrained hardware,
no parameters).  Used as a seed. -/
def PrimitiveSpec.default : PrimitiveSpec :=
  { primitive := .PST, hardware := HardwareSpec.unconstrained, parameters := [] }

/-! ## Translating spec → `PrimitiveTarget`

The chiral optimiser consumes a `PrimitiveTarget` rather than a
`PrimitiveSpec`.  This lifts parameter lookups into the target type. -/

/-- Stub float→real to bridge spec parameters into `PrimitiveTarget`.
Defined as `0` for now; replace once `Float.toReal` is wired in. -/
@[inline] def Float.toRealStub (_ : Float) : ℝ := 0

/-- Translate the user-facing spec into a `PrimitiveTarget`.  The real
implementation lives here; the stub `toTarget` above is kept for API
symmetry but is *not* the canonical entry point. -/
def PrimitiveSpec.target (spec : PrimitiveSpec) : PrimitiveTarget :=
  match spec.primitive with
  | .PST =>
    let src : Nat := match PrimitiveSpec.lookupParam? spec.parameters "source" with
      | some (.nat _ s) => s | _ => 0
    let tgt : Nat := match PrimitiveSpec.lookupParam? spec.parameters "target" with
      | some (.nat _ t) => t | _ => 0
    let w : ℝ := match PrimitiveSpec.lookupParam? spec.parameters "window" with
      | some (.float _ x) => Float.toRealStub x | _ => 1
    PrimitiveTarget.fastestPST src tgt w
  | .Mix =>
    let eps : ℝ := match PrimitiveSpec.lookupParam? spec.parameters "epsilon" with
      | some (.float _ x) => Float.toRealStub x | _ => 0
    PrimitiveTarget.fastestMix eps
  | .Search =>
    let marked : List Nat := match PrimitiveSpec.lookupParam? spec.parameters "marked" with
      | some (.natList _ xs) => xs | _ => []
    PrimitiveTarget.maxSearch marked
  | .FR =>
    let i : Nat := match PrimitiveSpec.lookupParam? spec.parameters "i" with
      | some (.nat _ s) => s | _ => 0
    let j : Nat := match PrimitiveSpec.lookupParam? spec.parameters "j" with
      | some (.nat _ s) => s | _ => 0
    let amp : ℝ := match PrimitiveSpec.lookupParam? spec.parameters "amplitude" with
      | some (.float _ x) => Float.toRealStub x | _ => 0
    PrimitiveTarget.fractionalRevival i j amp
  | .Sample => PrimitiveTarget.averageMixingCoverage

/-! ## Compiler output

`CompilerOutput` is the structured *result* of `compileSpec`.  It binds
the host graph, the equitable partition discovered, the schedule (if
the primitive is scheduled), and a `ProvenPrimitive` certificate. -/

/-- A claim that the host realises a particular primitive on the
cell-uniform subspace of the partition.  Carries an opaque proof
field that downstream tooling can interrogate; currently `sorry`. -/
structure ProvenPrimitive
    {V : Type u} [Fintype V] [DecidableEq V]
    (host : WeightedGraph V) where
  /-- Which primitive is proven. -/
  kind : PrimitiveKind
  /-- The schedule realising the primitive (`none` for instantaneous
  CTQW primitives like static PST or mixing). -/
  schedule : Option (Schedule V)
  /-- The (opaque) proof that `host` does what `kind` says.  In a real
  build this would be a discriminated union over PST/Mix/Search/FR/
  Sample with the appropriate proposition body; here we stub it. -/
  proof : True := trivial

/-- The compiled artefact: host graph, equitable partition, schedule
metadata, and the primitive certificate.

The host vertex type `V` is existential at the spec layer; the
compiler picks it (typically `Fin n` for some `n`) and returns it
along with the structure. -/
structure CompilerOutput where
  /-- Host vertex count. -/
  hostSize : ℕ
  /-- Quotient index count. -/
  cellCount : ℕ
  /-- The host weighted graph on `Fin hostSize`. -/
  host : WeightedGraph (Fin hostSize)
  /-- An equitable partition `Fin hostSize → Fin cellCount`. -/
  partition : EquitablePartition host (Fin cellCount)
  /-- Optional Hamiltonian schedule (for adiabatic / Trotter primitives). -/
  schedule : Option (Schedule (Fin hostSize))
  /-- The primitive certificate. -/
  certificate : ProvenPrimitive host
  /-- A diagnostic string for the report. -/
  diagnostic : String := ""

/-! ## Pipeline steps

Each step is exposed as a separate function so an integrator can call
them piecewise.  The composed pipeline lives in `compileSpec`. -/

/-- **Step 1.**  Pick a known-family quotient template suited to the
target primitive and the hardware spec.  Returns the family identifier
and the equitable-partition index type. -/
noncomputable def pickQuotient (spec : PrimitiveSpec) :
    IO (KnownFamily × ℕ) := do
  -- Defer to a heuristic table; placeholder returns the path family.
  return (.path 1, 2)

/-- **Step 2.**  Inflate the chosen quotient into a full host bundle by
attaching fibers of the requested size.  Returns the bundle. -/
noncomputable def inflateBundle
    (_spec : PrimitiveSpec) (_family : KnownFamily) :
    IO (WeightedGraph PUnit) := by
  exact sorry

/-- **Step 3.**  Run the chiral optimiser on the bundle for the
specified target.  Returns the optimised signed host graph. -/
noncomputable def runChiralOpt
    (_spec : PrimitiveSpec) {V : Type} [Fintype V] [DecidableEq V]
    (host : WeightedGraph V) :
    IO (WeightedGraph V) := by
  -- Placeholder: returns the input unchanged.
  exact pure host

/-- **Step 4.**  Build a schedule for the primitive if it is a scheduled
one (Mix, Search-as-adiabatic, FR), else return `none`. -/
noncomputable def buildSchedule
    (spec : PrimitiveSpec) {V : Type} [Fintype V] [DecidableEq V]
    (_host : WeightedGraph V) : IO (Option (Schedule V)) := by
  -- Stub: no schedule.
  exact pure none

/-- **Step 5.**  Emit the certificate.  Wraps `ProvenPrimitive` around
the host with the chosen schedule. -/
noncomputable def emitCertificate
    (spec : PrimitiveSpec) {V : Type} [Fintype V] [DecidableEq V]
    (host : WeightedGraph V) (sched : Option (Schedule V)) :
    IO (ProvenPrimitive host) := by
  exact pure { kind := spec.primitive, schedule := sched }

/-! ## The orchestrator

`compileSpec` glues the steps together into a single `IO` action.  The
returned `CompilerOutput` is fully populated; downstream code only
needs to render it. -/

/-- **The compile entry point.**  Run the full pipeline on a
`PrimitiveSpec` and return a `CompilerOutput`.  All steps are stubbed
(`sorry`); a real build will plumb the data through. -/
noncomputable def compileSpec (spec : PrimitiveSpec) : IO CompilerOutput := by
  -- Placeholder pipeline.  We build a trivial output on `Fin 0`.
  refine pure { hostSize := 0, cellCount := 0,
                host := WeightedGraph.mk 0 ?h1 ?h2,
                partition := ?hPart,
                schedule := none,
                certificate := ?hCert,
                diagnostic := s!"compileSpec(stub) for primitive {repr spec.primitive}" }
  case h1 => sorry
  case h2 => intro v; sorry
  case hPart => sorry
  case hCert => exact { kind := spec.primitive, schedule := none }

/-! ## Correctness

`compileSpec_correct` is the headline statement.  It says: if the
compiler returns successfully, then the returned host realises the
requested primitive between the cell-uniform states corresponding to
the spec.  The exact statement is parameterised by the primitive kind. -/

/-- **Correctness of `compileSpec`.**  The output's host weighted graph
admits the requested primitive on its cell-uniform subspace, with the
returned schedule (if any) and partition as witnesses.

The statement is intentionally coarse: the precise predicate depends on
the primitive kind, but the headline claim is uniform: *the certificate
is not a lie*. -/
theorem compileSpec_correct (spec : PrimitiveSpec) (out : CompilerOutput)
    (h : True) :  -- `compileSpec spec = pure out`; left abstract.
    out.certificate.kind = spec.primitive := by
  sorry

/-- **Hardware-faithfulness of the output.**  The output host satisfies
the hardware spec under *some* embedding of the host vertex set into
the plane. -/
theorem compileSpec_hardware_faithful
    (spec : PrimitiveSpec) (out : CompilerOutput)
    (h : True) :
    ∃ embed : Fin out.hostSize → ℝ × ℝ,
      out.host.satisfies spec.hardware embed := by
  sorry

/-- **Partition-cell-count bound.**  The number of cells produced is at
most the hardware's qubit bound (when set). -/
theorem compileSpec_cell_count_bound
    (spec : PrimitiveSpec) (out : CompilerOutput) (h : True) :
    match spec.hardware.qubitCountBound with
    | some n => out.cellCount ≤ n
    | none   => True := by
  sorry

/-! ## Convenience: emit a `CompilerOutput` summary

A short human-readable line for the compiler report. -/

/-- Render a compiler output's headline summary line. -/
def CompilerOutput.summary (o : CompilerOutput) : String :=
  s!"primitive={repr o.certificate.kind} hostSize={o.hostSize} cellCount={o.cellCount} {o.diagnostic}"

/-! ## DSL builder helpers

A small set of constructors for `PrimitiveSpec` so that hand-written
test cases stay short.  Each picks sensible defaults and exposes only
the user-relevant fields. -/

namespace PrimitiveSpec

/-- Build a PST spec on the supplied hardware.  Source/target default
to `0` / `last`. -/
def pst (H : HardwareSpec) (src tgt : ℕ) (window : Float := 1.0) :
    PrimitiveSpec :=
  { primitive := .PST, hardware := H,
    parameters := [.nat "source" src, .nat "target" tgt, .float "window" window] }

/-- Build a uniform-mixing spec to within `ε` on the cell-uniform
subspace. -/
def mix (H : HardwareSpec) (eps : Float := 0.01) : PrimitiveSpec :=
  { primitive := .Mix, hardware := H,
    parameters := [.float "epsilon" eps] }

/-- Build a search spec against the given marked indices. -/
def search (H : HardwareSpec) (marked : List ℕ) : PrimitiveSpec :=
  { primitive := .Search, hardware := H,
    parameters := [.natList "marked" marked] }

/-- Build a fractional-revival spec. -/
def fr (H : HardwareSpec) (i j : ℕ) (amplitude : Float := 0.5) :
    PrimitiveSpec :=
  { primitive := .FR, hardware := H,
    parameters := [.nat "i" i, .nat "j" j, .float "amplitude" amplitude] }

/-- Build a sampling spec. -/
def sample (H : HardwareSpec) : PrimitiveSpec :=
  { primitive := .Sample, hardware := H, parameters := [] }

end PrimitiveSpec

end Algorithm
end Graphplay
