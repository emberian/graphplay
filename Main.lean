import Graphplay

/-- Entry point for the `graphplay` demo executable.

Prints a short banner confirming the `Graphplay` library loaded, then echoes
the `graphplay-toolkit` usage string so the demo also documents the companion
compiler executable. -/
def main : IO Unit := do
  IO.println "graphplay: quasi-infinite graph constructions loaded"
  IO.println ""
  IO.println "Companion compiler executable (`graphplay-toolkit`):"
  IO.println ""
  IO.print Graphplay.Toolkit.usage
