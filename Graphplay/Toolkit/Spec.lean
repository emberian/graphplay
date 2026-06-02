/-
# Graphplay.Toolkit.Spec

Lean structures matching the JSON input schema of the Python search compiler
(`tools/search_compiler.py`).  This module is the *parsing front-end* of the
Lean toolkit: a JSON blob in, a `CompilerSpec` out, with a symbolic template
adjacency matrix (`WeightedGraph (Fin n)`) and proofs of regularity /
biregularity attached wherever the template guarantees them.

The Python compiler emits numerical diagnostics.  We instead expose:

* a symbolic template adjacency `Matrix (Fin n) (Fin n) ℂ`,
* a proof of `IsHermitian` and `loopless` (every template is undirected, no
  self-loops),
* an optional proof of `IsRegular` for templates that are structurally regular
  (`complete`, `cycle`, `cyclePowerLaw`, `hypercube`, `surfaceHeawood`,
  `cartesianProduct` of regulars, `complement` of a regular).

The certificate of regularity, when present, is consumed by `Bundle.lean` to
discharge the hypotheses of the *fiber-partition theorem* statement in
`Graphplay.Bundle`.

The JSON parser is implemented in terms of `Lean.Json` and produces helpful
error messages.  Where Python would silently allow `int|str` polymorphism, we
disambiguate at parse time and report which spec field was malformed.
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Graphplay.Weighted
import Graphplay.Equitable

universe u v

namespace Graphplay

namespace WeightedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A weighted graph is `d`-regular if every row of its adjacency matrix sums
to `d`.  Templates that are structurally regular carry this proof. -/
def IsRegular (G : WeightedGraph V) (d : ℂ) : Prop :=
  ∀ v : V, (∑ w, G.adj v w) = d

/-- Build a Hermitian zero adjacency.  Used by templates that are empty
(e.g. `path` of length 1 or trivial degenerate inputs). -/
def empty (V : Type u) [Fintype V] [DecidableEq V] : WeightedGraph V where
  adj := 0
  herm := by
    simp [Matrix.IsHermitian]
  loopless := by
    intro _
    rfl

end WeightedGraph

namespace Toolkit

/-! ## Spec data types -/

/-- The Heawood number `h(g) = ⌊(7 + √(1+48g))/2⌋` for orientable genus `g`,
plus the Klein-bottle exception.  Mirrors `heawood_number` in the Python
compiler. -/
inductive SurfaceHeawoodInput
  | orientableGenus (g : Nat)
  | nonorientableGenus (k : Nat) (kleinBottleException : Bool := true)
  | eulerGenus (eps : Nat) (kleinBottleException : Bool := false)
  | colors (n : Nat)
deriving Repr

/-- A `TemplateExpr` is the recursive symbolic spec of a template graph.

This mirrors the `kind` field of the JSON template spec.  Vertex names are
strings; the toolkit assigns them indices `Fin n` at compile time.  Weights
on edges default to `1.0` but the JSON spec allows scaling.

The constructors:
* `explicit` — an arbitrary edge list, weighted.
* `complete` — `K_n` weighted by a constant.
* `cycle` — `C_n` weighted by a constant.
* `path` — `P_n` weighted by a constant.
* `completeBipartite` — `K_{m,n}` weighted by a constant.
* `hypercube` — `Q_d` weighted by a constant.
* `complement` — bipartite complement of a sub-template at constant weight.
* `cartesianProduct` — the Cartesian product of two sub-templates.
* `surfaceHeawood` — `K_{h(g)}` for surface-genus-bounded chromatic templates.
* `cyclePowerLaw` — `C_n` with edge weights `scale / d(i,j)^α`.
-/
inductive TemplateExpr where
  | explicit (vertices : List String) (edges : List (String × String × Float))
  | complete (vertices : List String) (weight : Float)
  | cycle (vertices : List String) (weight : Float)
  | path (vertices : List String) (weight : Float)
  | completeBipartite (left : List String) (right : List String) (weight : Float)
  | hypercube (dim : Nat) (weight : Float)
  | complement (of : TemplateExpr) (weight : Float)
  | cartesianProduct (left : TemplateExpr) (right : TemplateExpr)
  | surfaceHeawood (input : SurfaceHeawoodInput) (weight : Float)
  | cyclePowerLaw (vertices : List String) (alpha : Float) (scale : Float)

instance : Inhabited TemplateExpr := ⟨.complete [] 0.0⟩

/-- Problem-statement metadata used to render the markdown `## Problem`
section.  All fields are optional. -/
structure ProblemDoc where
  domain : Option String := none
  task : Option String := none
  encoding : Option String := none
  compilerGoal : Option String := none
  proofRoute : Option String := none
deriving Inhabited, Repr

/-- Scan parameters for the numerical-CTQW best-effort hook.  These are *not*
used to produce verified certificates; they only influence the triage hint
emitted in the report. -/
structure ScanConfig where
  steps : Nat := 1600
  tMaxFactor : Float := 4.0
  gammaFactors : List Float := [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
  gammaAdjacency : Option Float := none
  gammaLaplacian : Option Float := none
deriving Inhabited, Repr

/-- A fully parsed spec: ready to compile to a host bundle and a report. -/
structure CompilerSpec where
  /-- Free-form name string from JSON `name` field. -/
  name : String
  /-- Optional problem statement metadata. -/
  problem : ProblemDoc
  /-- The recursive template AST. -/
  template : TemplateExpr
  /-- Names of the template vertices, post-flattening (length `= templateSize`). -/
  vertices : List String
  /-- The symbolic template adjacency: `vertices.length × vertices.length`. -/
  templateAdj : List (List Float)
  /-- Fiber size for each template vertex.  Length matches `vertices`. -/
  fibers : List Nat
  /-- Marked count for each template vertex.  `0 ≤ marked[i] ≤ fibers[i]`. -/
  marked : List Nat
  /-- Numerical-CTQW scan parameters (best-effort). -/
  scan : ScanConfig
deriving Inhabited

/-- The number of template vertices. -/
def CompilerSpec.templateSize (s : CompilerSpec) : Nat :=
  s.vertices.length

/-- The total number of host vertices `∑ fibers[i]`. -/
def CompilerSpec.hostSize (s : CompilerSpec) : Nat :=
  s.fibers.foldl (· + ·) 0

/-! ## Template construction primitives

These produce `(vertexNames, weightMatrix)` for a given `TemplateExpr`.  The
weight matrix is represented as a `List (List Float)` because we want JSON
round-trippability and not pay the cost of full `Matrix` formal machinery here.
The corresponding `Matrix V V ℂ` view is constructed in `Bundle.lean`. -/

/-- Symmetric write to a 2-D list-of-lists adjacency. -/
def setEdge (m : List (List Float)) (i j : Nat) (w : Float) : List (List Float) :=
  let setRow (row : List Float) (col : Nat) : List Float :=
    row.mapIdx (fun k x => if k = col then w else x)
  m.mapIdx (fun k row =>
    if k = i then setRow row j
    else if k = j then setRow row i
    else row)

/-- An `n × n` zero matrix as a `List (List Float)`. -/
def zeroMatrix (n : Nat) : List (List Float) :=
  (List.range n).map (fun _ => (List.range n).map (fun _ => (0.0 : Float)))

/-- Default-named vertices for size-`n` templates: `pre0, pre1, …`. -/
def defaultNames (pre : String) (n : Nat) : List String :=
  (List.range n).map (fun i => pre ++ toString i)

/-- Minimum of `(j - i) mod n` and `(i - j) mod n` — the cyclic distance. -/
def cyclicDist (n i j : Nat) : Nat :=
  let a := (j + n - i) % n
  let b := (i + n - j) % n
  if a ≤ b then a else b

/-- Compute Heawood number from the (open) `SurfaceHeawoodInput` form. -/
def heawoodNumber : SurfaceHeawoodInput → Nat
  | .colors n => n
  | .orientableGenus g =>
    -- `⌊ (7 + √(1+48g)) / 2 ⌋`; we approximate with `Float` then `toUInt64`.
    let disc : Float := (1.0 + 48.0 * (g.toFloat)).sqrt
    ((7.0 + disc) / 2.0).toUInt64.toNat
  | .nonorientableGenus k kbExc =>
    if k = 2 && kbExc then 6
    else
      let disc : Float := (1.0 + 24.0 * (k.toFloat)).sqrt
      ((7.0 + disc) / 2.0).toUInt64.toNat
  | .eulerGenus eps kbExc =>
    if eps = 0 then 4
    else if eps = 2 && kbExc then 6
    else
      let disc : Float := (1.0 + 24.0 * (eps.toFloat)).sqrt
      ((7.0 + disc) / 2.0).toUInt64.toNat

/-- Pair of `(vertexNames, n × n weight matrix)` produced by `buildTemplate`.
The weight matrix is stored row-major as `List (List Float)`. -/
abbrev TemplateData := List String × List (List Float)

/-- Recursively compile a `TemplateExpr` into vertex names and a symbolic
adjacency matrix.  This is the structural ancestor of Python's
`build_template` function. -/
partial def buildTemplate : TemplateExpr → TemplateData
  | .explicit vs es =>
    let n := vs.length
    let m₀ := zeroMatrix n
    let index : String → Nat := fun s =>
      (vs.findIdx? (· = s)).getD 0
    let m := es.foldl (init := m₀) fun acc ⟨u, v, w⟩ =>
      setEdge acc (index u) (index v) w
    (vs, m)
  | .complete vs w =>
    let n := vs.length
    let row (i : Nat) : List Float :=
      (List.range n).map (fun j => if i = j then 0.0 else w)
    (vs, (List.range n).map row)
  | .cycle vs w =>
    let n := vs.length
    let m := (List.range n).foldl (init := zeroMatrix n) fun acc i =>
      setEdge acc i ((i + 1) % n) w
    (vs, m)
  | .path vs w =>
    let n := vs.length
    let m := (List.range (n - 1)).foldl (init := zeroMatrix n) fun acc i =>
      setEdge acc i (i + 1) w
    (vs, m)
  | .completeBipartite left right w =>
    let nL := left.length
    let nR := right.length
    let n := nL + nR
    let vs := left ++ right
    let m := (List.range nL).foldl (init := zeroMatrix n) fun acc i =>
      (List.range nR).foldl (init := acc) fun acc j =>
        setEdge acc i (nL + j) w
    (vs, m)
  | .hypercube dim w =>
    let n := 2 ^ dim
    let toBin (i dim : Nat) : String :=
      let rec aux (i k : Nat) (acc : String) : String :=
        if k = 0 then acc
        else aux (i / 2) (k - 1) (toString (i % 2) ++ acc)
      aux i dim ""
    let vs := (List.range n).map (fun i => toBin i dim)
    let m := (List.range n).foldl (init := zeroMatrix n) fun acc i =>
      (List.range dim).foldl (init := acc) fun acc bit =>
        let j := i ^^^ (1 <<< bit)
        if i < j then setEdge acc i j w else acc
    (vs, m)
  | .complement of w =>
    let (vs, base) := buildTemplate of
    let n := vs.length
    let m := (List.range n).map fun i =>
      (List.range n).map fun j =>
        let curr := ((base[i]?).bind (fun r => r[j]?)).getD 0.0
        if i = j then 0.0
        else if curr == 0.0 then w
        else 0.0
    (vs, m)
  | .cartesianProduct l r =>
    let (vsL, mL) := buildTemplate l
    let (vsR, mR) := buildTemplate r
    let nL := vsL.length
    let nR := vsR.length
    let n := nL * nR
    let vs : List String := (vsL.flatMap fun a => vsR.map fun b => a ++ "," ++ b)
    -- left tensor I_R
    let m := (List.range nL).foldl (init := zeroMatrix n) fun acc ai =>
      (List.range nL).foldl (init := acc) fun acc aj =>
        let w := ((mL[ai]?).bind (fun r => r[aj]?)).getD 0.0
        if w == 0.0 then acc
        else (List.range nR).foldl (init := acc) fun acc b =>
          setEdge acc (ai * nR + b) (aj * nR + b) w
    -- I_L tensor right
    let m := (List.range nL).foldl (init := m) fun acc a =>
      (List.range nR).foldl (init := acc) fun acc bi =>
        (List.range nR).foldl (init := acc) fun acc bj =>
          let w := ((mR[bi]?).bind (fun r => r[bj]?)).getD 0.0
          if w == 0.0 then acc
          else setEdge acc (a * nR + bi) (a * nR + bj) w
    (vs, m)
  | .surfaceHeawood input w =>
    let n := heawoodNumber input
    let vs := defaultNames "c" n
    let row (i : Nat) : List Float :=
      (List.range n).map (fun j => if i = j then 0.0 else w)
    (vs, (List.range n).map row)
  | .cyclePowerLaw vs alpha scale =>
    let n := vs.length
    let m := (List.range n).foldl (init := zeroMatrix n) fun acc i =>
      (List.range n).foldl (init := acc) fun acc j =>
        if i < j then
          let d := cyclicDist n i j
          let w := scale / (d.toFloat).pow alpha
          setEdge acc i j w
        else acc
    (vs, m)

/-! ## Regularity certificate

For structurally regular templates (constant-weight complete, cycle,
hypercube, surfaceHeawood, cartesian-of-regulars), we expose a
`templateRegularDegree?` returning `some d` where `d : Float` is the common
weighted degree.  Downstream tools turn that into a regularity proof for the
host bundle via `Graphplay.GraphBundle.fiberPartition`.

If the template is not structurally regular (`explicit`, unequal `cyclePowerLaw`
fibers post-fact, `complement`, …) we fall back to *checking* regularity
numerically (`approxRegular`) and emitting a sorry-marked claim. -/

/-- Sum of row `i` of the symbolic adjacency. -/
def rowSum (m : List (List Float)) (i : Nat) : Float :=
  ((m[i]?).getD []).foldl (· + ·) 0.0

/-- Returns `some d` if every row sum equals `d` to floating-point tolerance,
else `none`.  Tolerance is fixed at `1e-9`. -/
def approxRegular (m : List (List Float)) : Option Float :=
  let n := m.length
  if _h : n = 0 then none
  else
    let d := rowSum m 0
    let ok := (List.range n).all fun i =>
      let r := rowSum m i
      let δ := r - d
      δ.abs < 1e-9
    if ok then some d else none

/-- Structural regularity inference from the AST.  Returns the *symbolic*
common weighted degree when the template is regular by construction. -/
def templateRegularDegree : TemplateExpr → Option Float
  | .complete vs w => some ((vs.length - 1).toFloat * w)
  | .cycle vs w => if vs.length ≥ 2 then some (2.0 * w) else none
  | .hypercube dim w => some ((dim.toFloat) * w)
  | .surfaceHeawood input w => some (((heawoodNumber input) - 1).toFloat * w)
  | .cartesianProduct l r => do
      let dl ← templateRegularDegree l
      let dr ← templateRegularDegree r
      pure (dl + dr)
  | .cyclePowerLaw vs _ _ =>
      -- Power-law cycle is regular for any α because of cyclic symmetry.
      let (_, m) := buildTemplate (.cyclePowerLaw vs 0.0 1.0)
      approxRegular m
  | _ => none

/-! ## JSON deserialization -/

open Lean (Json)

/-- Decode a single edge spec: `["u","v"]` or `["u","v", w]`.  Defaults the
weight to `1.0` if missing. -/
def parseEdge (j : Json) : Except String (String × String × Float) := do
  let arr ← j.getArr?
  match arr.toList with
  | [u, v] => do
    let us ← u.getStr?
    let vs ← v.getStr?
    pure (us, vs, 1.0)
  | [u, v, w] => do
    let us ← u.getStr?
    let vs ← v.getStr?
    let wn ← w.getNum?
    pure (us, vs, wn.toFloat)
  | _ => throw s!"edge must have length 2 or 3, got: {j.compress}"

/-- Helper: read a numeric JSON node as `Float`, accepting ints. -/
def jsonFloat? (j : Json) : Except String Float := do
  let n ← j.getNum?
  pure n.toFloat

/-- Read a JSON node as `Nat`, accepting ints (but not floats). -/
def jsonNat? (j : Json) : Except String Nat := do
  let n ← j.getNat?
  pure n

/-- Read named vertices from a template subobject: prefers `vertices` (a
list of strings), falls back to `n` + optional `prefix`. -/
def namedVertices (j : Json) : Except String (List String) := do
  match j.getObjVal? "vertices" with
  | .ok arr =>
    let xs ← arr.getArr?
    xs.toList.mapM (·.getStr?)
  | .error _ =>
    let n ← jsonNat? (← j.getObjVal? "n")
    let pre := (j.getObjValAs? String "prefix").toOption.getD "v"
    pure (defaultNames pre n)

/-- Optional weight field: returns `1.0` when absent. -/
def optWeight (j : Json) : Except String Float :=
  match j.getObjVal? "weight" with
  | .ok jw => jsonFloat? jw
  | .error _ => pure 1.0

/-- Recursively parse a template subobject. -/
partial def parseTemplate (j : Json) : Except String TemplateExpr := do
  let kind := (j.getObjValAs? String "kind").toOption.getD "explicit"
  match kind with
  | "explicit" => do
    let vsJ ← j.getObjVal? "vertices"
    let vsArr ← vsJ.getArr?
    let vs ← vsArr.toList.mapM (·.getStr?)
    let edgesJ := (j.getObjVal? "edges").toOption.getD (Json.arr #[])
    let edgesArr ← edgesJ.getArr?
    let edges ← edgesArr.toList.mapM parseEdge
    pure (.explicit vs edges)
  | "complete" => do
    let vs ← namedVertices j
    let w ← optWeight j
    pure (.complete vs w)
  | "cycle" => do
    let vs ← namedVertices j
    let w ← optWeight j
    pure (.cycle vs w)
  | "path" => do
    let vs ← namedVertices j
    let w ← optWeight j
    pure (.path vs w)
  | "complete_bipartite" => do
    let parseStrList (key : String) : Except String (List String) :=
      match j.getObjVal? key with
      | .ok jl => do
        let xs ← jl.getArr?
        xs.toList.mapM (·.getStr?)
      | .error _ => pure []
    let left₀ ← parseStrList "left"
    let right₀ ← parseStrList "right"
    let left := if left₀.isEmpty then
        match (j.getObjVal? "n_left").toOption with
        | some jn => match jsonNat? jn with
          | .ok n => defaultNames "L" n
          | .error _ => []
        | none => []
      else left₀
    let right := if right₀.isEmpty then
        match (j.getObjVal? "n_right").toOption with
        | some jn => match jsonNat? jn with
          | .ok n => defaultNames "R" n
          | .error _ => []
        | none => []
      else right₀
    let w ← optWeight j
    pure (.completeBipartite left right w)
  | "hypercube" => do
    let dim ← jsonNat? (← j.getObjVal? "dim")
    let w ← optWeight j
    pure (.hypercube dim w)
  | "complement" => do
    let of ← parseTemplate (← j.getObjVal? "of")
    let w ← optWeight j
    pure (.complement of w)
  | "cartesian_product" => do
    let l ← parseTemplate (← j.getObjVal? "left")
    let r ← parseTemplate (← j.getObjVal? "right")
    pure (.cartesianProduct l r)
  | "surface_heawood" => do
    let w ← optWeight j
    let input ← parseSurface j
    pure (.surfaceHeawood input w)
  | "cycle_power_law" => do
    let vs ← namedVertices j
    let α ← jsonFloat? (← j.getObjVal? "alpha")
    let s ← (match j.getObjVal? "scale" with
      | .ok js => jsonFloat? js
      | .error _ => pure 1.0)
    pure (.cyclePowerLaw vs α s)
  | other => throw s!"unknown template kind: {other}"
where
  parseSurface (j : Json) : Except String SurfaceHeawoodInput := do
    if let .ok jc := j.getObjVal? "colors" then
      let n ← jsonNat? jc
      return .colors n
    if let .ok jc := j.getObjVal? "orientable_genus" then
      let g ← jsonNat? jc
      return .orientableGenus g
    if let .ok jc := j.getObjVal? "nonorientable_genus" then
      let k ← jsonNat? jc
      let kbExc := (j.getObjValAs? Bool "klein_bottle_exception").toOption.getD true
      return .nonorientableGenus k kbExc
    if let .ok jc := j.getObjVal? "euler_genus" then
      let e ← jsonNat? jc
      let kbExc := (j.getObjValAs? Bool "klein_bottle_exception").toOption.getD false
      return .eulerGenus e kbExc
    throw "surface_heawood needs orientable_genus, nonorientable_genus, euler_genus, or colors"

/-- Parse the optional `problem` object. -/
def parseProblem (j : Json) : ProblemDoc :=
  match j.getObjVal? "problem" with
  | .error _ => {}
  | .ok p =>
    { domain := (p.getObjValAs? String "domain").toOption,
      task := (p.getObjValAs? String "task").toOption,
      encoding := (p.getObjValAs? String "encoding").toOption,
      compilerGoal := (p.getObjValAs? String "compiler_goal").toOption,
      proofRoute := (p.getObjValAs? String "proof_route").toOption }

/-- Parse the optional `scan` block. -/
def parseScan (j : Json) : ScanConfig :=
  match j.getObjVal? "scan" with
  | .error _ => {}
  | .ok s =>
    let steps := (s.getObjValAs? Nat "steps").toOption.getD 1600
    let tMaxFactor := match s.getObjVal? "t_max_factor" with
      | .ok x => (jsonFloat? x).toOption.getD 4.0
      | .error _ => 4.0
    let gammaFactors := match s.getObjVal? "gamma_factors" with
      | .ok arr => match arr.getArr? with
        | .ok xs =>
          xs.toList.filterMap (fun j =>
            match jsonFloat? j with | .ok x => some x | _ => none)
        | .error _ => [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
      | .error _ => [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
    let gammaA := match s.getObjVal? "gamma_adjacency" with
      | .ok x => match x with
        | .str "auto" => none
        | _ => (jsonFloat? x).toOption
      | .error _ => none
    let gammaL := match s.getObjVal? "gamma_laplacian" with
      | .ok x => match x with
        | .str "auto" => none
        | _ => (jsonFloat? x).toOption
      | .error _ => none
    { steps, tMaxFactor, gammaFactors,
      gammaAdjacency := gammaA, gammaLaplacian := gammaL }

/-- Top-level JSON entry: parse a `CompilerSpec` from a `Json` value. -/
def parseSpec (j : Json) : Except String CompilerSpec := do
  let name := (j.getObjValAs? String "name").toOption.getD "<unnamed>"
  let tj ← j.getObjVal? "template"
  let templateExpr ← parseTemplate tj
  let (vs, templateAdj) := buildTemplate templateExpr
  -- Fibers: int or per-vertex map.
  let fibers ← (match j.getObjVal? "fibers" with
    | .ok fj => parseFiberMap vs fj
    | .error _ => match j.getObjVal? "fiber_size" with
      | .ok fj => do
        let n ← jsonNat? fj
        pure (vs.map (fun _ => n))
      | .error _ => throw "spec missing 'fibers' or 'fiber_size'")
  if fibers.any (· = 0) then
    throw "all fiber sizes must be positive"
  -- Marked counts: optional per-vertex map; defaults to 0.
  let marked ← (match j.getObjVal? "marked" with
    | .ok mj => parseMarkedMap vs mj fibers
    | .error _ => pure (vs.map (fun _ => 0)))
  let problem := parseProblem j
  let scan := parseScan j
  pure { name, problem,
         template := templateExpr,
         vertices := vs,
         templateAdj,
         fibers, marked, scan }
where
  parseFiberMap (vs : List String) (fj : Json) :
      Except String (List Nat) := do
    match fj with
    | .num _ => do
      let n ← jsonNat? fj
      pure (vs.map (fun _ => n))
    | .obj _ =>
      vs.mapM fun v =>
        match fj.getObjVal? v with
        | .ok jn => jsonNat? jn
        | .error _ => throw s!"missing fiber size for vertex '{v}'"
    | _ => throw "fibers must be int or object"
  parseMarkedMap (vs : List String) (mj : Json) (fibers : List Nat) :
      Except String (List Nat) :=
    (vs.zip fibers).mapM fun (v, fib) => do
      match mj.getObjVal? v with
      | .ok jn => do
        let k ← jsonNat? jn
        if k > fib then throw s!"marked[{v}] > fibers[{v}]"
        else pure k
      | .error _ => pure 0

/-- Convenience: load a `CompilerSpec` from a file path. -/
def loadSpec (path : System.FilePath) : IO CompilerSpec := do
  let raw ← IO.FS.readFile path
  match Lean.Json.parse raw with
  | .ok j => match parseSpec j with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"spec parse error: {e}")
  | .error e => throw (IO.userError s!"json parse error: {e}")

/-! ## Symbolic certificates

These wrap the per-template structural facts that downstream report-rendering
relies on.  Where we cannot prove the fact in Lean today, we expose a
`sorry`-shaped placeholder so the API surface is stable. -/

/-- Structural certificate of regularity for a template.  `none` means we have
no structural proof; report code should fall back to numerical inference
(`approxRegular`).

This is a pure-data record: it records the symbolic common weighted degree.
The *genuine* correctness obligation — that every row of the symbolic
adjacency sums to `degree` — is stated separately as `CompilerSpec.IsRowRegular`
and discharged (where possible) by `CompilerSpec.regularityCert_sound`.  We
keep the certificate data and its proof obligation apart so that
`regularityCert` stays a total, `sorry`-free definition. -/
structure RegularityCert where
  /-- The symbolic common weighted degree. -/
  degree : Float

/-- Extract a regularity certificate, preferring the structural inference
when available, otherwise probing the numerical row sums. -/
def CompilerSpec.regularityCert (s : CompilerSpec) : Option RegularityCert :=
  match templateRegularDegree s.template with
  | some d => some { degree := d }
  | none => match approxRegular s.templateAdj with
    | some d => some { degree := d }
    | none => none

/-- The **exact regularity proposition**: every row of the symbolic template
adjacency sums to a single common value `d`.  This is the `Float`-level analogue
of `WeightedGraph.IsRegular` on the symbolic `templateAdj`.

⚠ This *exact* notion is an idealization that the certificate does NOT in general
witness (see `regularityCert_sound`'s landmine note): floating-point row sums of
`buildTemplate` need not be *bit-exactly* equal, and `approxRegular` only checks
agreement to a `1e-9` tolerance.  The genuinely-witnessed notion is the
approximate one, `IsApproxRowRegular`, below. -/
def CompilerSpec.IsRowRegular (s : CompilerSpec) (d : Float) : Prop :=
  ∀ i : Nat, i < s.templateSize → rowSum s.templateAdj i = d

/-- The **approximate regularity proposition** — the genuinely *checkable* notion
on `Float` adjacencies: every row sum of `templateAdj` agrees with the common
degree `d` to within the fixed `1e-9` tolerance.  This is exactly what
`approxRegular` verifies, and the honest content of a numerical regularity
certificate.  (Quantified over the matrix's own row count `templateAdj.length`,
which for a well-formed spec equals `templateSize`.) -/
def CompilerSpec.IsApproxRowRegular (s : CompilerSpec) (d : Float) : Prop :=
  ∀ i : Nat, i < s.templateAdj.length → (rowSum s.templateAdj i - d).abs < 1e-9

/-- **Soundness of the numerical regularity check (`approxRegular`).**  If
`approxRegular m` succeeds with degree `d`, then every row sum of `m` agrees with
`d` to within the `1e-9` tolerance.  This is the literal content of the check,
proven by unfolding it: `d = rowSum m 0` and the `List.all` guard is precisely
the per-row tolerance bound.  Fully proven, axiom-clean. -/
theorem approxRegular_sound (m : List (List Float)) (d : Float)
    (h : approxRegular m = some d) :
    ∀ i : Nat, i < m.length → (rowSum m i - d).abs < 1e-9 := by
  intro i hi
  unfold approxRegular at h
  by_cases hlen : m.length = 0
  · omega
  · rw [dif_neg hlen] at h
    simp only at h
    by_cases hok : ((List.range m.length).all fun j =>
        let r := rowSum m j; let δ := r - rowSum m 0; δ.abs < 1e-9) = true
    · rw [if_pos hok] at h
      have hd : d = rowSum m 0 := by injection h with h'; exact h'.symm
      subst hd
      rw [List.all_eq_true] at hok
      have := hok i (List.mem_range.mpr hi)
      simpa using this
    · rw [if_neg hok] at h
      exact absurd h (by simp)

/-- **Soundness of the regularity certificate (migrated to the genuinely-true
form).**  Whenever `regularityCert` *uses its numerical branch* — i.e. the
structural inference declined (`templateRegularDegree s.template = none`) and
`approxRegular s.templateAdj` produced the certificate — the symbolic template
adjacency really is row-regular of degree `c.degree`, to within tolerance
(`IsApproxRowRegular`).  Fully proven via `approxRegular_sound`.

⚠ LANDMINE FIXED (migrated; the original claim was false on two counts).  The
hypothesis-free `s.IsRowRegular c.degree` (exact equality, all branches) was a
false statement:

1. **Structural-branch decoupling.**  `templateRegularDegree` reads only
   `s.template`, never `s.templateAdj`; but `CompilerSpec` lets `templateAdj` be
   *any* matrix, decoupled from `template`.  Counterexample: `template =
   complete ["a","b"] 1.0` (so the structural degree is `1.0`) with `templateAdj
   = [[5.0]]` — the certificate is `⟨1.0⟩` yet `rowSum [[5.0]] 0 = 5.0 ≠ 1.0`.
2. **Float tolerance ≠ exact.**  Even on a well-formed spec, `approxRegular` only
   guarantees row sums *within `1e-9`*, and floating-point sums of identical
   weights are not bit-exactly equal, so the *exact* `IsRowRegular` fails.

Restricting to the numerical branch and weakening the conclusion to the
checkable `IsApproxRowRegular` removes both defects while keeping a non-vacuous
soundness guarantee (the certificate's degree really is the approximate common
row sum).  The structural-branch soundness — `templateAdj = buildTemplate
s.template` *and* `buildTemplate` is row-regular — is a separate, genuinely deep
`Float`-over-constructors obligation (the honest floor). -/
theorem CompilerSpec.regularityCert_sound (s : CompilerSpec) (c : RegularityCert)
    (hstruct : templateRegularDegree s.template = none)
    (h : s.regularityCert = some c) :
    s.IsApproxRowRegular c.degree := by
  -- In the numerical branch, `regularityCert = approxRegular s.templateAdj`.
  intro i hi
  rw [CompilerSpec.regularityCert, hstruct] at h
  -- `h : (match approxRegular s.templateAdj with | some d => some ⟨d⟩ | none => none) = some c`
  cases hap : approxRegular s.templateAdj with
  | none => rw [hap] at h; exact absurd h (by simp)
  | some d =>
    rw [hap] at h
    -- `some ⟨d⟩ = some c`, so `c.degree = d`.
    have hcd : c.degree = d := by injection h with h'; rw [← h']
    rw [hcd]
    exact approxRegular_sound s.templateAdj d hap i hi

end Toolkit

end Graphplay
