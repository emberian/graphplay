import Graphplay.Toolkit

/-- IO-only entry point for the `graphplay-toolkit` executable.  Reads `argv`
(skipping the program name) and dispatches to `Graphplay.Toolkit.main`.

This entry point lives in a dedicated root module (rather than inside
`Graphplay/Toolkit.lean`) so that the root-level `main` is not pulled into the
`Graphplay` library via `import Graphplay`, which would collide with the
`main` of the `graphplay` demo executable. -/
def main (args : List String) : IO UInt32 :=
  Graphplay.Toolkit.main args
