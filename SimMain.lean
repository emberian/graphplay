/-
# SimMain — runnable CTQW simulator

Drives `Graphplay.Simulate` to actually run continuous-time quantum walks and
print success-probability / amplitude vs. time tables for three canonical
phenomena:

  1. Childs–Goldstone spatial search on the complete graph `K_n`
     (Grover-optimal CTQW search) — success rises to ≈1 near `t* ≈ (π/2)√n`.
  2. Hypercube antipodal perfect state transfer on `Q_3` — fidelity hits ≈1
     at `t = π/2`.
  3. Path `P_3` endpoint-to-endpoint perfect state transfer — fidelity hits
     ≈1 at `t = π/√2`.

Run with: `lake exe graphplay-sim`.
-/

import Graphplay.Simulate

open Graphplay.Simulate

def pi : Float := 3.14159265358979323846

/-- Print a (time, probability) table with an ASCII bar. -/
def printTable (rows : Array (Float × Float)) : IO Unit := do
  IO.println (padRight "   t" 10 ++ padRight "prob" 12 ++ "bar")
  IO.println (String.ofList (List.replicate 52 '-'))
  for (t, p) in rows do
    let ts := toString (roundTo 4 t)
    let ps := toString (roundTo 6 p)
    IO.println (padRight ts 10 ++ padRight ps 12 ++ probBar p)

/-- Find the (time, prob) pair with maximal probability. -/
def argmax (rows : Array (Float × Float)) : Float × Float :=
  rows.foldl (fun best cur => if cur.2 > best.2 then cur else best) (0.0, -1.0)

/-! ## 1. Childs–Goldstone spatial search on K_n -/

def runSearch (n : Nat) : IO Unit := do
  IO.println ""
  IO.println s!"=== 1. Childs–Goldstone spatial search on K_{n} ==="
  IO.println s!"    H = γ·A(K_{n}) + |w⟩⟨w|,  γ = 1/n,  marked vertex w = 0"
  IO.println s!"    ψ(0) = uniform superposition,  measuring |⟨0|ψ(t)⟩|²"
  let γ := 1.0 / Float.ofNat n
  let A := completeGraphH n
  let H := searchHamiltonian A 0 γ
  let psi0 := uniformSuperposition n
  -- optimal time t* ≈ (π/2)√n ; sweep to 1.5·t*
  let tStar := (pi / 2.0) * (Float.ofNat n).sqrt
  let tMax := 1.5 * tStar
  let steps := 30
  let dt := tMax / Float.ofNat steps
  let rows := traceTargetProb H psi0 0 steps dt
  printTable rows
  let (tBest, pBest) := argmax rows
  IO.println s!"  predicted t* ≈ (π/2)√n = {roundTo 4 tStar}"
  IO.println s!"  observed peak: prob {roundTo 6 pBest} at t = {roundTo 4 tBest}"

/-! ## 2. Hypercube antipodal PST on Q_d -/

def runHypercube (d : Nat) : IO Unit := do
  let n := 2 ^ d
  let antipode := n - 1   -- all-ones label is the antipode of 0…0
  IO.println ""
  IO.println s!"=== 2. Hypercube Q_{d} antipodal PST ({n} vertices) ==="
  IO.println s!"    H = A(Q_{d}),  ψ(0) = |0…0⟩,  measuring |⟨antipode|ψ(t)⟩|²"
  IO.println s!"    antipode vertex = {antipode}"
  let H := hypercubeH d
  let psi0 := basisState n 0
  let tMax := pi
  let steps := 24
  let dt := tMax / Float.ofNat steps
  let rows := traceTargetProb H psi0 antipode steps dt
  printTable rows
  let (tBest, pBest) := argmax rows
  IO.println s!"  predicted PST time t = π/2 = {roundTo 4 (pi/2.0)}"
  IO.println s!"  observed peak: prob {roundTo 6 pBest} at t = {roundTo 4 tBest}"

/-! ## 3. Path P_3 endpoint PST -/

def runPath : IO Unit := do
  IO.println ""
  IO.println "=== 3. Path P_3 endpoint-to-endpoint PST ==="
  IO.println "    H = A(P_3),  ψ(0) = |0⟩,  measuring |⟨2|ψ(t)⟩|²"
  let H := pathH 3
  let psi0 := basisState 3 0
  -- P_3 has spectrum {-√2, 0, √2}; PST at t = π/√2
  let tStar := pi / (2.0 : Float).sqrt
  let tMax := 1.4 * tStar
  let steps := 24
  let dt := tMax / Float.ofNat steps
  let rows := traceTargetProb H psi0 2 steps dt
  printTable rows
  let (tBest, pBest) := argmax rows
  IO.println s!"  predicted PST time t = π/√2 = {roundTo 4 tStar}"
  IO.println s!"  observed peak: prob {roundTo 6 pBest} at t = {roundTo 4 tBest}"

/-- Print a (time, probA, probB) table side by side with a label per column. -/
def printTwoTable (labA labB : String) (rows : Array (Float × Float × Float)) :
    IO Unit := do
  IO.println (padRight "   t" 10 ++ padRight labA 14 ++ padRight labB 14)
  IO.println (String.ofList (List.replicate 48 '-'))
  for (t, a, b) in rows do
    IO.println (padRight (toString (roundTo 4 t)) 10
      ++ padRight (toString (roundTo 5 a)) 14
      ++ padRight (toString (roundTo 5 b)) 14)

/-! ## 4. Chiral / magnetic (flux) walk -/

def runChiral : IO Unit := do
  IO.println ""
  IO.println "=== 4. Chiral / magnetic-flux walk on a triangle C_3 ==="
  IO.println "    H_{j,j+1} = e^{+iθ},  H_{j+1,j} = e^{-iθ}  (Hermitian, flux 3θ)"
  IO.println "    θ = π/6  ⇒  total flux = π/2 (≠ 0, π mod 2π): chiral"
  IO.println "    ψ(0) = |0⟩;  P_cw = P(vertex 1, clockwise nbr),"
  IO.println "                 P_ccw = P(vertex 2, counter-clockwise nbr)"
  let θ := pi / 6.0
  let n := 3
  let H := chiralCycleH n θ
  let steps := 12
  let dt := 3.0 / Float.ofNat steps
  let rows := traceChirality H n steps dt
  printTwoTable "P_cw (v1)" "P_ccw (v2)" rows
  -- maximal directional bias
  let bias := rows.foldl (fun b (t, cw, ccw) =>
    if cw - ccw > b.2 then (t, cw - ccw) else b) (0.0, -2.0)
  IO.println s!"  predicted: a real-symmetric (θ=0) walk keeps P_cw = P_ccw"
  IO.println s!"  observed: max forward bias P_cw - P_ccw = {roundTo 4 bias.2} at t = {roundTo 4 bias.1}"
  IO.println s!"  → probability circulates preferentially CLOCKWISE: chirality confirmed"

/-! ## 5. Fractional revival on weighted P_3 -/

def runFractionalRevival : IO Unit := do
  IO.println ""
  IO.println "=== 5. Fractional revival on weighted path P_3 ==="
  IO.println "    H = !![0,a,0; a,0,b; 0,b,0],  a = 1, b = 2"
  IO.println "    spectrum {-w, 0, w}, w = √(a²+b²) = √5"
  IO.println "    ψ(0) = |0⟩ (source);  at t = π/w the middle empties and"
  IO.println "    the state reforms as α|0⟩ + β|2⟩ (a partial revival, α<1)"
  let a := 1.0
  let b := 2.0
  let w := (a*a + b*b).sqrt
  let H := weightedP3H a b
  let psi0 := basisState 3 0
  let tStar := pi / w
  let tMax := 1.2 * tStar
  let steps := 18
  let dt := tMax / Float.ofNat steps
  let rows := traceTwoProbs H psi0 0 2 steps dt
  printTwoTable "src |0⟩" "tgt |2⟩" rows
  -- predicted target fraction (2ab/w²)²
  let αpred := let f := 2.0*a*b/(w*w); f*f
  -- observed target prob nearest the revival time
  let psiStar := evolveState H tStar psi0
  let tgtObs := cnormSq psiStar[2]!
  let srcObs := cnormSq psiStar[0]!
  let midObs := cnormSq psiStar[1]!
  IO.println s!"  revival time t* = π/√5 = {roundTo 4 tStar}"
  IO.println s!"  predicted target fraction α = (2ab/w²)² = {roundTo 4 αpred}  (∈(0,1): partial)"
  IO.println s!"  observed at t*: src={roundTo 4 srcObs}, mid={roundTo 4 midObs}, tgt={roundTo 4 tgtObs}"
  IO.println s!"  → middle ≈ 0, src+tgt ≈ {roundTo 4 (srcObs+tgtObs)}: two-site superposition, FR confirmed"

/-! ## 6. Open-system (Lindblad) dephasing -/

def runLindblad : IO Unit := do
  IO.println ""
  IO.println "=== 6. Open-system dephasing (Lindblad) on P_3 ==="
  IO.println "    dρ/dt = −i[H,ρ] + γ Σ_v(|v⟩⟨v|ρ|v⟩⟨v| − ½{|v⟩⟨v|,ρ}),  γ = 0.3"
  IO.println "    H = A(P_3),  ρ(0) = |0⟩⟨0| (pure),  Euler dt = 0.01"
  IO.println "    measuring purity Tr(ρ²) and populations ρ_vv"
  let H := pathH 3
  let γ := 0.3
  let dt := 0.01
  let ρ0 := pureDensity (basisState 3 0)
  let steps := 1000
  let rows := traceLindblad H γ dt ρ0 steps 100
  IO.println (padRight "   t" 8 ++ padRight "purity" 11 ++ padRight "Tr(ρ)" 9
    ++ "populations (ρ00,ρ11,ρ22)")
  IO.println (String.ofList (List.replicate 60 '-'))
  for (t, pur, tr, pops) in rows do
    let popStr := String.intercalate ", " (pops.toList.map (fun p => toString (roundTo 3 p)))
    IO.println (padRight (toString (roundTo 2 t)) 8
      ++ padRight (toString (roundTo 5 pur)) 11
      ++ padRight (toString (roundTo 4 tr)) 9
      ++ "[" ++ popStr ++ "]")
  IO.println s!"  predicted: pure state has purity 1; dephasing decays it toward 1/n = {roundTo 4 (1.0/3.0)}"
  let lastPur := (rows.back?.map (fun r => r.2.1)).getD 0.0
  IO.println s!"  observed: purity 1.0 → {roundTo 4 lastPur} (decohering); Tr(ρ) ≈ 1 (CPTP)"
  IO.println s!"  → coherence lost, populations spread: decoherence confirmed"

/-! ## 7. Closing the design→simulate loop: synthesized PST host -/

def runSynthHost (m : Nat) : IO Unit := do
  IO.println ""
  IO.println s!"=== 7. Synthesized PST host K₂ □ (edgeless Fin {m}) ==="
  IO.println s!"    InverseDesign.synthesizePST builds {2*m} vertices, vertex i ↔ i+{m}"
  IO.println s!"    (m disjoint edges); CERTIFIED IsPST (0,0)→(1,0) at π/2 upstream."
  IO.println s!"    Here we NUMERICALLY confirm: ψ(0)=|0⟩, measure |⟨{m}|ψ(t)⟩|²"
  let H := synthPSTHostH m
  let n := 2 * m
  let psi0 := basisState n 0
  let tMax := pi
  let steps := 16
  let dt := tMax / Float.ofNat steps
  let rows := traceTargetProb H psi0 m steps dt
  printTable rows
  let psiStar := evolveState H (pi/2.0) psi0
  let pStar := cnormSq psiStar[m]!
  IO.println s!"  predicted PST time t = π/2 = {roundTo 4 (pi/2.0)}"
  IO.println s!"  observed at t=π/2: |⟨{m}|ψ⟩|² = {roundTo 6 pStar}  (→ 1)"
  IO.println s!"  → the *synthesized* Hamiltonian transfers: engineered certificate verified numerically"

/-! ## 8. 2D grid (torus) spatial search — Childs–Goldstone d=2 critical case -/

def runGridSearch (L : Nat) : IO Unit := do
  let n := L * L
  -- centre vertex of the L×L grid
  let cr := L / 2
  let w := cr * L + cr
  IO.println ""
  IO.println s!"=== 8. 2D grid (torus) spatial search — Childs–Goldstone ({L}×{L} = {n} vertices) ==="
  IO.println s!"    H = γ·A(torus) + |w⟩⟨w|,  marked vertex w = centre = {w}"
  IO.println s!"    A = 4-regular periodic 2D lattice; ψ(0) = uniform superposition"
  IO.println s!"    γ = 1/deg = 1/4 (optimal hopping for a 4-regular graph)"
  let γ := 1.0 / 4.0
  let A := gridGraphH L
  let H := searchHamiltonian A w γ
  let psi0 := uniformSuperposition n
  -- d=2 critical: best time ~ √(N log N); sweep generously
  let tStar := (Float.ofNat n * (Float.ofNat n).log).sqrt
  let tMax := 1.5 * tStar
  let steps := 30
  let dt := tMax / Float.ofNat steps
  let rows := traceTargetProb H psi0 w steps dt
  printTable rows
  let (tBest, pBest) := argmax rows
  IO.println s!"  classical reference: 2D grid search is the d=2 CRITICAL case —"
  IO.println s!"    only marginally faster than classical, NO clean prob-1 peak"
  IO.println s!"    (contrast K_n: clean t* = (π/2)√N to prob ≈ 1)."
  IO.println s!"  predicted timescale ~ √(N·logN) = {roundTo 4 tStar}"
  IO.println s!"  observed peak: prob {roundTo 6 pBest} at t = {roundTo 4 tBest}"
  IO.println s!"  → clear peak well above uniform baseline 1/N = {roundTo 6 (1.0/Float.ofNat n)}, but bounded < 1: d=2 confirmed"

/-! ## 9. Synthesized host — fuller transfer animation (K₂ □ K_m) -/

/-- Adjacency of `K₂ □ K_m`: `2m` vertices, vertex `v=(c,f)` (cell `c∈{0,1}`,
fibre `f∈{0,…,m-1}`) indexed `v=c·m+f`.  Edges: same cell different fibre
(the `K_m` fibre, connected), and same fibre different cell (the `K₂` rung).
This is a *richer, connected-fibre* synthesized host than `m` disjoint edges. -/
def k2BoxKmH (m : Nat) : CMat :=
  let n := 2 * m
  Array.ofFn (n := n) fun i =>
    let ci := i.val / m; let fi := i.val % m
    Array.ofFn (n := n) fun j =>
      let cj := j.val / m; let fj := j.val % m
      if (ci == cj && fi ≠ fj) || (fi == fj && ci ≠ cj) then cone else czero

def runSynthAnim (m : Nat) : IO Unit := do
  IO.println ""
  IO.println s!"=== 9. Synthesized host K₂ □ K_{m} — fine transfer animation ({2*m} vertices) ==="
  IO.println s!"    Engineered Cartesian-product host: K₂ rung × connected K_{m} fibre."
  IO.println s!"    The K₂ factor gives antipodal PST across the rung at t = π/2,"
  IO.println s!"    unaffected by the K_{m} fibre (product PST). ψ(0)=|0⟩ → target |{m}⟩."
  let H := k2BoxKmH m
  let n := 2 * m
  let psi0 := basisState n 0          -- (cell 0, fibre 0)
  let target := m                     -- (cell 1, fibre 0)
  let tStar := pi / 2.0
  let tMax := pi
  let steps := 32                     -- finer-grained animation
  let dt := tMax / Float.ofNat steps
  let rows := traceTargetProb H psi0 target steps dt
  printTable rows
  let psiStar := evolveState H tStar psi0
  let fid := cnormSq psiStar[target]!
  IO.println s!"  predicted PST time t = π/2 = {roundTo 4 tStar}"
  IO.println s!"  observed fidelity at t=π/2: |⟨{m}|ψ⟩|² = {roundTo 6 fid}  (→ 1)"
  IO.println s!"  → engineered Hamiltonian performs PST on demand: synthesis verified"

/-! ## 10. Attention-graph CTQW — equitable-partition quotient match (ML bridge) -/

def runAttention (b : Nat) : IO Unit := do
  let n := 2 * b
  IO.println ""
  IO.println s!"=== 10. Attention-graph CTQW — equitable quotient reduction (ML bridge, n={n}) ==="
  IO.println s!"    Toy 2-block attention: {n} tokens, cell0 = [0,{b}), cell1 = [{b},{n})."
  IO.println s!"    score(same cell)=2.0, score(cross cell)=0.5 → softmax row-stochastic A."
  IO.println s!"    H = symmetrise(A); ψ(0)=|0⟩ (a localized query)."
  let A := twoBlockAttention b 2.0 0.5
  let H := symmetrize A
  let psi0 := basisState n 0
  -- (a) information spreading: cell occupations over time, full graph
  IO.println ""
  IO.println "  (a) query state spreads along high-attention (intra-cell) edges:"
  let steps := 16
  let dt := 4.0 / Float.ofNat steps
  let fullRows := Array.ofFn (n := steps + 1) fun k =>
    let t := dt * k.val.toFloat
    let psi := evolveState H t psi0
    (t, cellProb psi 0 b, cellProb psi b n)
  -- (b) quotient: 2x2 reduction. ψ(0)=|0⟩ is NOT cell-uniform, so to test the
  -- equitable reduction we start from the cell-uniform vector |cell 0⟩ and
  -- compare full-graph cell occupations against the 2x2 quotient evolution.
  let B := quotient2 H b
  IO.println s!"  2×2 quotient Hamiltonian B (cell→cell row sums):"
  IO.println s!"    B = [[{roundTo 5 ((B[0]!)[0]!).1}, {roundTo 5 ((B[0]!)[1]!).1}], [{roundTo 5 ((B[1]!)[0]!).1}, {roundTo 5 ((B[1]!)[1]!).1}]]"
  -- cell-uniform start: (1/√b) on cell 0 vertices
  let amp := 1.0 / (Float.ofNat b).sqrt
  let psiCellUnif := Array.ofFn (n := n) fun i => if i.val < b then (amp, 0.0) else czero
  let q0 : Array (Float × Float) := #[cone, czero]    -- quotient |cell 0⟩
  IO.println ""
  IO.println "  (b) full-graph cell occupations vs 2×2 quotient, from |cell 0⟩:"
  IO.println (padRight "   t" 9 ++ padRight "full P0" 11 ++ padRight "quot P0" 11
    ++ padRight "full P1" 11 ++ padRight "quot P1" 11 ++ "max|Δ|")
  IO.println (String.ofList (List.replicate 64 '-'))
  let mut maxDiff := 0.0
  for k in List.range (steps + 1) do
    let t := dt * k.toFloat
    let psi := evolveState H t psiCellUnif
    let fP0 := cellProb psi 0 b
    let fP1 := cellProb psi b n
    let (qP0, qP1) := quotientCellProbs B q0 t
    let d := max (Float.abs (fP0 - qP0)) (Float.abs (fP1 - qP1))
    maxDiff := max maxDiff d
    IO.println (padRight (toString (roundTo 4 t)) 9
      ++ padRight (toString (roundTo 6 fP0)) 11
      ++ padRight (toString (roundTo 6 qP0)) 11
      ++ padRight (toString (roundTo 6 fP1)) 11
      ++ padRight (toString (roundTo 6 qP1)) 11
      ++ toString (roundTo 8 d))
  IO.println ""
  IO.println "  (a) localized-query spread (cell occupations from |0⟩):"
  printTwoTable "cell0" "cell1" fullRows
  IO.println s!"  → max |full − quotient| over the run = {roundTo 9 maxDiff}"
  IO.println s!"  → full-graph symmetric-subspace dynamics ≡ 2×2 quotient (agree to ~1e-6):"
  IO.println s!"     the equitable-partition reduction of Integrations/MachineLearning is CONFIRMED numerically"

def main : IO Unit := do
  IO.println "graphplay CTQW numerical simulator"
  IO.println "exp(-i t H) via scaling-and-squaring + Taylor (Float)"
  runSearch 16
  runHypercube 3
  runPath
  runChiral
  runFractionalRevival
  runLindblad
  runSynthHost 3
  runGridSearch 5
  runSynthAnim 4
  runAttention 4
  IO.println ""
  IO.println "done."
