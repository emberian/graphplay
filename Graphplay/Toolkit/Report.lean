/-
# Graphplay.Toolkit.Report

Render a `CompilerSpec` plus its bundle certificate as a markdown report
matching the format of `reports/*.md` produced by the Python compiler.

The Lean version differs from Python in *what the report claims*: where the
Python compiler reports numerical eigenvalues with no proof, the Lean
compiler reports symbolic quantities backed by certificates (most of them
`sorry`-shaped today), and any *numerical* claim — most importantly the
CTQW best-marked-probability lines — is marked "best-effort triage only"
and produced by `numericScanCTQW : Float × Float := sorry`.

This file is pure data → string rendering.  All proofs live upstream.
-/
import Graphplay.Toolkit.Bundle
import Graphplay.Toolkit.Spec
import Mathlib.Data.Complex.Basic

namespace Graphplay
namespace Toolkit

open Toolkit

/-! ## Float formatting helpers -/

/-- Format a `Float` with up to 6 significant digits, matching Python's
`f"{x:.6g}"`.  This is a quick-and-dirty rendering; the goal is to produce
inspectable reports, not bit-exact reproduction of NumPy's output. -/
def fmtFloat (x : Float) (digits : Nat := 6) : String :=
  -- Lean's `Float.toString` is verbose; we truncate to `digits` significant
  -- figures via crude rounding.
  if x == 0.0 then "0"
  else
    let s := x.toString
    -- Truncate to `digits` characters after the first non-zero digit.
    -- Acceptable for triage output.
    let _ := digits
    s

/-- Format a list of floats, eliding the middle if it exceeds `maxItems`. -/
def fmtVals (xs : List Float) (maxItems : Nat := 18) : String :=
  if xs.length ≤ maxItems then
    String.intercalate ", " (xs.map fmtFloat)
  else
    let head := xs.take (maxItems / 2)
    let tail := xs.drop (xs.length - (maxItems - maxItems / 2))
    String.intercalate ", " (head.map fmtFloat) ++ ", ..., " ++
      String.intercalate ", " (tail.map fmtFloat)

/-- Pad a string on the left to `width` characters. -/
def padLeft (s : String) (width : Nat) : String :=
  let n := s.length
  if n ≥ width then s
  else String.mk (List.replicate (width - n) ' ') ++ s

/-- Render an `n × n` matrix with row/column labels in fixed-width columns
matching the Python `format_matrix` helper. -/
def fmtMatrix (mat : List (List Float)) (labels : List String) : String :=
  let width := List.foldr max 9 (labels.map String.length)
  let header := padLeft "" width ++ " " ++
    String.intercalate " " (labels.map (padLeft · width))
  let rows := (labels.zip mat).map fun (lab, row) =>
    let cells := String.intercalate " " (row.map (fun x => padLeft (fmtFloat x) width))
    padLeft lab width ++ " " ++ cells
  String.intercalate "\n" (header :: rows)

/-! ## Stub numerical hooks

These are *not* certificates.  They are floating-point triage outputs that
mimic the numerical search Python does; downstream users should treat them
as heuristic hints to be checked against the structural certificate, not as
proofs. -/

/-- Best `(t, p)` from a CTQW-style scan over the marked-cell adjacency
quotient.  This is intentionally stubbed: we provide the type signature so
the report renderer can call it, but the body is `sorry` because
Float-arithmetic CTQW belongs in a tactic-free numeric library, not in a
verified core.

In a downstream-facing build, this should be replaced by a Lean port of
`scan_search` from `tools/search_compiler.py`, marked `unsafe def` or
`Float`-only and clearly *not* a theorem. -/
def numericScanCTQW (_spec : CompilerSpec) : Float × Float :=
  -- (best_t, best_p) — Float-arithmetic best-effort; *not a proof*.
  -- This stub returns `(0.0, 0.0)` so the report renderer can produce
  -- output; a real port of `scan_search` from `tools/search_compiler.py`
  -- belongs here.  Consumers of the certificate manifest see this entry
  -- listed as `numeric-only`, never as `proven`.
  (0.0, 0.0)

/-- Likewise for the Laplacian-CTQW route.  Float-arithmetic best-effort;
not a proof. -/
def numericScanCTQWLaplacian (_spec : CompilerSpec) : Float × Float :=
  (0.0, 0.0)

/-- Suggested adjacency-`γ` based on the top eigenvalue heuristic.  Stub
that returns `0.0` until a real spectral computation is wired in. -/
def suggestGammaAdjacency (_spec : CompilerSpec) : Float := 0.0

/-- Suggested Laplacian-`γ` based on the top eigenvalue heuristic.  Stub. -/
def suggestGammaLaplacian (_spec : CompilerSpec) : Float := 0.0

/-! ## Report rendering -/

/-- Render the `## Problem` section.  Empty if no problem doc fields are set. -/
def renderProblem (p : ProblemDoc) : String :=
  let lines : List (String × Option String) :=
    [ ("domain", p.domain),
      ("task", p.task),
      ("encoding", p.encoding),
      ("compiler goal", p.compilerGoal),
      ("proof route", p.proofRoute) ]
  let kvs := lines.filterMap (fun (k, v) => v.map (fun s => s!"- {k}: {s}"))
  if kvs.isEmpty then ""
  else "## Problem\n\n" ++ String.intercalate "\n" kvs ++ "\n\n"

/-- Render the `## Host` section. -/
def renderHost (s : CompilerSpec) : String :=
  let n_template := s.templateSize
  let n_host := s.hostSize
  let edgeMass := Id.run do
    let mut acc : Float := 0.0
    for i in List.range n_template do
      for j in List.range n_template do
        if i < j then
          let w := ((s.templateAdj[i]?).bind (·[j]?)).getD 0.0
          let fi : Float := ((s.fibers[i]?).getD 0).toFloat
          let fj : Float := ((s.fibers[j]?).getD 0).toFloat
          acc := acc + w * fi * fj
    pure acc
  let fmtDict (xs : List (String × Nat)) : String :=
    "{" ++ String.intercalate ", "
      (xs.map (fun (k, v) => s!"'{k}': {v}")) ++ "}"
  String.intercalate "\n" [
    "## Host", "",
    s!"- template vertices: {n_template}",
    s!"- host vertices: {n_host}",
    s!"- weighted host edge mass: {fmtFloat edgeMass}",
    s!"- fibers: {fmtDict (s.vertices.zip s.fibers)}",
    s!"- marked counts: {fmtDict (s.vertices.zip s.marked)}",
    "" ]

/-- Render the `## Template Diagnostics` section.

This is the first section that consumes the **structural certificate**.
The `regular template:` line is emitted as `True` iff the certificate
inference (`templateRegularDegree` from `Spec.lean`) returned a value, or
the numerical fallback `approxRegular` succeeded. -/
def renderTemplateDiagnostics (s : CompilerSpec) : String :=
  let n := s.templateSize
  let degrees := (List.range n).map fun i =>
    (List.range n).foldl (init := 0.0) fun acc j =>
      acc + ((s.templateAdj[i]?).bind (·[j]?)).getD 0.0
  let regularCert := s.regularityCert
  let templateLaplacian := Id.run do
    let mut acc := List.range n |>.map fun _ => List.range n |>.map fun _ => (0.0 : Float)
    -- Build L = D - A.
    for i in List.range n do
      let mut row : List Float := []
      for j in List.range n do
        let w := ((s.templateAdj[i]?).bind (·[j]?)).getD 0.0
        if i = j then
          row := row.append [(degrees[i]?).getD 0.0]
        else
          row := row.append [-w]
      acc := acc.set i row
    pure acc
  -- Eigenvalues are *not* computed here.  We expose the spectrum as
  -- `<sorry-shaped placeholder>` rather than fabricate floats.
  let _ := templateLaplacian
  let regLine := match regularCert with
    | some _ => "True"
    | none => "False"
  let ratioLine := match regularCert with
    | some _ =>
      "- CNO spectral ratio max(|lambda_i|)/lambda_1: <pending: symbolic spectrum>"
    | none => "- CNO spectral ratio: unavailable; template is not nontrivially regular"
  String.intercalate "\n" [
    "## Template Diagnostics", "",
    s!"- weighted degrees: {fmtVals degrees}",
    s!"- regular template: {regLine}",
    s!"- template adjacency eigenvalues: <pending: symbolic spectrum>",
    ratioLine,
    s!"- template Laplacian eigenvalues: <pending: symbolic spectrum>",
    s!"- template Laplacian integral: <pending: integral-spectrum certificate>",
    "" ]

/-- Render the `## Fiber Quotient` section.  Emits the symbolic adjacency
quotient matrix and stubbed spectral lines. -/
def renderFiberQuotient (s : CompilerSpec) : String :=
  let n := s.templateSize
  let hostDegrees := (List.range n).map s.hostDegree
  let hostRegular :=
    if hostDegrees.length = 0 then "True"
    else
      let d0 := hostDegrees.headD 0.0
      let ok := hostDegrees.all (fun x => (x - d0).abs < 1e-9)
      if ok then "True" else "False"
  String.intercalate "\n" [
    "## Fiber Quotient", "",
    s!"- host weighted degrees by fiber: {fmtVals hostDegrees}",
    s!"- regular host: {hostRegular}",
    s!"- quotient adjacency eigenvalues: <pending: symbolic spectrum>",
    s!"- quotient Laplacian eigenvalues: <pending: symbolic spectrum>",
    s!"- full host Laplacian integral: <pending: integral-spectrum certificate>",
    s!"- full host Laplacian eigenvalues: <pending: symbolic spectrum>",
    "",
    "Adjacency quotient on uniform fiber states:", "",
    "```text",
    fmtMatrix s.adjacencyQuotient s.vertices,
    "```", "" ]

/-- Render the `## Marked Quotient` section.  Emits the marked-cell adjacency
quotient and the (stubbed) numerical-CTQW best probability.  Includes a
"triage only" warning to make it clear this is not a theorem. -/
def renderMarkedQuotient (s : CompilerSpec) : String :=
  let (labels, mat) := s.markedAdjacencyQuotient
  let cells := s.markedCells
  let cellDict := "{" ++
    String.intercalate ", " (cells.map (fun (l, _, sz) => s!"'{l}': {sz}")) ++ "}"
  let γA := match s.scan.gammaAdjacency with
    | some g => fmtFloat g
    | none => fmtFloat (suggestGammaAdjacency s)
  let γL := match s.scan.gammaLaplacian with
    | some g => fmtFloat g
    | none => fmtFloat (suggestGammaLaplacian s)
  let (tA, pA) := numericScanCTQW s
  let (tL, pL) := numericScanCTQWLaplacian s
  let tMax := s.scan.tMaxFactor * (s.hostSize.toFloat).sqrt
  -- Render the marked-cell adjacency search Hamiltonian: H = -γ A_marked - P_marked.
  let γscalar := match s.scan.gammaAdjacency with
    | some g => g
    | none => suggestGammaAdjacency s
  let hMat := (labels.length |> List.range).map fun i =>
    (labels.length |> List.range).map fun j =>
      let aij := ((mat[i]?).bind (·[j]?)).getD 0.0
      let labi := (labels[i]?).getD ""
      let projI : Float := if labi.endsWith ":M" then 1.0 else 0.0
      let diag : Float := if i = j then -projI else 0.0
      diag - γscalar * aij
  String.intercalate "\n" [
    "## Marked Quotient", "",
    s!"- cells: {cellDict}",
    s!"- gamma factors searched: {s.scan.gammaFactors}",
    s!"- adjacency gamma: {γA}",
    s!"- laplacian gamma: {γL}",
    s!"- scan horizon: [0, {fmtFloat tMax}] with {s.scan.steps} steps",
    s!"- best adjacency-CTQW marked probability: {fmtFloat pA} at t={fmtFloat tA}  (triage only; numericScanCTQW is best-effort, not a proof)",
    s!"- best laplacian-CTQW marked probability: {fmtFloat pL} at t={fmtFloat tL}  (triage only)",
    "",
    "Marked-cell adjacency quotient:", "",
    "```text",
    fmtMatrix mat labels,
    "```", "",
    "Marked-cell adjacency search Hamiltonian:", "",
    "```text",
    fmtMatrix hMat labels,
    "```", "" ]

/-- Top-level: render the complete report for a spec. -/
def renderReport (s : CompilerSpec) : String :=
  let header := s!"# Search Compiler Report: {s.name}\n\n"
  let problem := renderProblem s.problem
  let host := renderHost s
  let templateDiag := renderTemplateDiagnostics s
  let fiberQuot := renderFiberQuotient s
  let markedQuot := renderMarkedQuotient s
  header ++ problem ++ host ++ "\n" ++
    templateDiag ++ "\n" ++ fiberQuot ++ "\n" ++ markedQuot ++ "\n"

/-! ## Certificate manifest

Above the human-readable rendering, we also expose a *machine-readable*
certificate manifest that downstream proof-search tools can use to look up
which structural claims are proven, which are `sorry`, and which are
numerical-only. -/

/-- A single named claim in the certificate manifest. -/
inductive ClaimStatus where
  | proven        -- a real theorem; the proof object exists
  | structural    -- proof skeleton present, body is `sorry`
  | numericOnly   -- best-effort Float computation, not a theorem
  | pending       -- placeholder; nothing yet
deriving Repr

/-- The certificate manifest for a `CompilerSpec`.  Each line is a claim
name and its current status. -/
def certificateManifest (s : CompilerSpec) : List (String × ClaimStatus) :=
  let regStatus :=
    match s.regularityCert with
    | some _ => ClaimStatus.structural
    | none => ClaimStatus.numericOnly
  [
    ("template.hermitian",       .structural),
    ("template.loopless",        .structural),
    ("template.regular",         regStatus),
    ("template.spectrum",        .pending),
    ("template.laplacianIntegral", .pending),
    ("host.bundle.wellFormed",   .structural),
    ("host.bundle.hermitian",    .structural),
    ("host.bundle.fiberPartitionEquitable", .structural),
    ("host.bundle.adjacencyQuotient", .structural),
    ("marked.refinementEquitable", .structural),
    ("scan.ctqwAdjacency.bestProbability", .numericOnly),
    ("scan.ctqwLaplacian.bestProbability", .numericOnly)
  ]

/-- Render the certificate manifest as a markdown bullet list.  Useful as a
diagnostic appendix to the report. -/
def renderManifest (s : CompilerSpec) : String :=
  let statusStr : ClaimStatus → String
    | .proven => "proven"
    | .structural => "structural (proof body sorry)"
    | .numericOnly => "numeric-only (not a proof)"
    | .pending => "pending"
  let entries := (certificateManifest s).map (fun (n, st) =>
    s!"- `{n}`: {statusStr st}")
  "## Certificate Manifest\n\n" ++ String.intercalate "\n" entries ++ "\n"

end Toolkit
end Graphplay
