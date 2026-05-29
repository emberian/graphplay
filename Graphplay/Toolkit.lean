/-
# Graphplay.Toolkit

Top-level orchestration: load a JSON spec from disk, compile it through the
toolkit pipeline (`Spec` → `Bundle` → certificate → `Report`), and emit a
markdown report.  This is the Lean replacement for `tools/search_compiler.py`.

The executable entry point lives in `Main.lean` (or in this module's `main`
below).  Usage:

```
$ graphplay-toolkit examples/rook_3x3_equal_fiber.json reports/rook_3x3_equal_fiber.md
```

Architectural notes:

* The `compileSpec` function takes filesystem paths to avoid pinning a
  particular I/O strategy; consumers can compose it inside larger flows.
* On parse error we throw an `IO.userError` whose message points to the
  spec field that failed.  No silent fallbacks.
* The output report **always** includes the `## Certificate Manifest`
  appendix.  This is the key differentiator from the Python compiler: we
  publish a machine-readable claim status alongside the human-readable
  diagnostics, so downstream proof-search tooling can tell which parts of
  the report are theorems versus floating-point hints.
-/
import Graphplay.Toolkit.Spec
import Graphplay.Toolkit.Bundle
import Graphplay.Toolkit.Report

namespace Graphplay
namespace Toolkit

/-- Compile a single JSON spec to a markdown report, writing the result to
`reportPath`.  If `reportPath` is `none`, the report is only printed to
stdout. -/
def compileSpec (jsonPath : System.FilePath)
    (reportPath : Option System.FilePath := none) : IO Unit := do
  let spec ← loadSpec jsonPath
  let body := renderReport spec ++ "\n" ++ renderManifest spec ++ "\n"
  IO.println body
  match reportPath with
  | some p => do
    let dir := p.parent.getD "."
    -- best-effort directory creation
    try IO.FS.createDirAll dir catch _ => pure ()
    IO.FS.writeFile p body
  | none => pure ()

/-- Print a tiny usage string for the executable. -/
def usage : String :=
  "graphplay-toolkit: compile engineered color-template search hosts.\n" ++
  "\n" ++
  "Usage: graphplay-toolkit <spec.json> [--report <out.md>]\n" ++
  "\n" ++
  "The spec JSON matches the input schema of tools/search_compiler.py.\n" ++
  "The report's structural sections are backed by Lean certificates\n" ++
  "(see the appended `## Certificate Manifest` for proof status); the\n" ++
  "CTQW marked-probability lines are numerical triage only.\n"

/-- Argv-dispatching `main`.  Mirrors the Python CLI's `argparse` interface
but trimmed to the minimum: one positional spec path, one optional `--report`
output path. -/
def main (args : List String) : IO UInt32 := do
  let rec parseArgs : List String →
      IO (Option System.FilePath × Option System.FilePath)
    | [] => pure (none, none)
    | ["--help"] => do IO.println usage; pure (none, none)
    | ["-h"] => do IO.println usage; pure (none, none)
    | ("--report" :: r :: rest) => do
      let (spec, _) ← parseArgs rest
      pure (spec, some (System.FilePath.mk r))
    | (spec :: rest) => do
      let (_, rep) ← parseArgs rest
      pure (some (System.FilePath.mk spec), rep)
  let (specPath, reportPath) ← parseArgs args
  match specPath with
  | none => do
    IO.println usage
    pure 1
  | some sp => do
    compileSpec sp reportPath
    pure 0

end Toolkit
end Graphplay
