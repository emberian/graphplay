/-
# Graphplay.Simulate

A **runnable** numerical continuous-time quantum walk (CTQW) simulator over
`Float`.  Where the rest of `Graphplay` proves PST / mixing / search theorems
symbolically, this module lets us *actually run* the time evolution
`ψ(t) = exp(-i t H) ψ(0)` and watch the amplitudes / success probabilities
evolve.

Everything here is computable `Float` code — no Mathlib `NormedSpace.exp`
(noncomputable).  The matrix exponential is done
by the standard **scaling-and-squaring + Taylor** method, which is fully
general and numerically robust for the small Hermitian Hamiltonians we use.

Complex numbers are `Float × Float` as `(re, im)`.  Matrices are
`Array (Array (Float × Float))` (row-major); state vectors are
`Array (Float × Float)`.
-/

namespace Graphplay.Simulate

/-! ## Complex Float scalar helpers -/

/-- Complex number as `(re, im)`. -/
abbrev C := Float × Float

@[inline] def cadd (a b : C) : C := (a.1 + b.1, a.2 + b.2)
@[inline] def csub (a b : C) : C := (a.1 - b.1, a.2 - b.2)
@[inline] def cmul (a b : C) : C :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
@[inline] def cconj (a : C) : C := (a.1, -a.2)
@[inline] def cscaleR (s : Float) (a : C) : C := (s * a.1, s * a.2)
@[inline] def cnormSq (a : C) : Float := a.1 * a.1 + a.2 * a.2
@[inline] def cabs (a : C) : Float := (cnormSq a).sqrt
@[inline] def czero : C := (0.0, 0.0)
@[inline] def cone : C := (1.0, 0.0)
/-- The imaginary unit `i`. -/
@[inline] def cI : C := (0.0, 1.0)

/-! ## Complex Float matrices -/

/-- A complex Float matrix (row-major). -/
abbrev CMat := Array (Array C)

/-- Number of rows. -/
@[inline] def CMat.rows (M : CMat) : Nat := M.size
/-- Number of columns (from the first row; 0 for an empty matrix). -/
@[inline] def CMat.cols (M : CMat) : Nat := if M.size == 0 then 0 else M[0]!.size

/-- Entrywise scale by a real Float. -/
def cmScaleR (s : Float) (M : CMat) : CMat :=
  M.map (fun row => row.map (cscaleR s))

/-- Entrywise scale by a complex scalar. -/
def cmScaleC (c : C) (M : CMat) : CMat :=
  M.map (fun row => row.map (cmul c))

/-- Entrywise matrix addition. -/
def cmAdd (A B : CMat) : CMat :=
  Array.zipWith (fun ra rb => Array.zipWith cadd ra rb) A B

/-- `n × n` complex identity. -/
def cidentity (n : Nat) : CMat :=
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j => if i == j then cone else czero

/-- Matrix product `A * B`. -/
def cmatmul (A B : CMat) : CMat :=
  let n := A.size
  let p := B.cols
  Array.ofFn (n := n) fun i =>
    let ra := A[i.val]!
    Array.ofFn (n := p) fun j =>
      -- ∑_k A[i,k] * B[k,j]
      (List.range ra.size).foldl
        (fun acc k => cadd acc (cmul ra[k]! (B[k]!)[j.val]!)) czero

/-- Matrix · vector. -/
def cmatVec (M : CMat) (v : Array C) : Array C :=
  M.map fun row =>
    (Array.zipWith cmul row v).foldl cadd czero

/-- Conjugate transpose `Mᴴ`. -/
def cconjTranspose (M : CMat) : CMat :=
  let n := M.rows
  let m := M.cols
  Array.ofFn (n := m) fun i =>
    Array.ofFn (n := n) fun j => cconj ((M[j.val]!)[i.val]!)

/-- Max-abs (∞-ish) norm of a matrix; used to pick the squaring level. -/
def cmMaxAbs (M : CMat) : Float :=
  M.foldl (fun s row => row.foldl (fun s' z => max s' (cabs z)) s) 0.0

/-! ## Matrix exponential: scaling and squaring + Taylor

We compute `exp(M)` for a general complex matrix `M` via

  `exp(M) = (exp(M / 2^k))^(2^k)`,

choosing `k` so that `‖M / 2^k‖` is small, then approximating the inner
exponential by its Taylor series `∑_{j=0}^{p} M^j / j!`.  Finally we square
the result `k` times. -/

/-- Taylor partial sum `∑_{j=0}^{p} M^j / j!`, computed by Horner-like
accumulation of the term `M^j / j!`. -/
def cmExpTaylor (M : CMat) (p : Nat) : CMat :=
  let n := M.rows
  let I := cidentity n
  -- term₀ = I, accumulate; termⱼ = termⱼ₋₁ * M / j
  let rec go (j : Nat) (term acc : CMat) : CMat :=
    match j with
    | 0 => acc
    | Nat.succ j' =>
      let jIdx := p - j + 1          -- current factorial index (1,2,3,…)
      let term' := cmScaleR (1.0 / jIdx.toFloat) (cmatmul term M)
      go j' term' (cmAdd acc term')
  go p I I

/-- `exp(M)` via scaling and squaring with a Taylor inner approximation.
`p` is the Taylor order; the squaring level `k` is chosen so that
`‖M‖ / 2^k ≤ 0.5`. -/
def cexpMat (M : CMat) (p : Nat := 12) : CMat :=
  let nrm := cmMaxAbs M
  -- choose k with nrm / 2^k ≤ 0.5  ⇔  2^k ≥ 2·nrm
  let rec chooseK (k : Nat) (scale : Float) : Nat :=
    if k ≥ 60 then k
    else if nrm ≤ scale then k
    else chooseK (k + 1) (scale * 2.0)
  let k := chooseK 0 0.5
  let Mscaled := cmScaleR (1.0 / (Float.ofNat (2 ^ k))) M
  let E0 := cmExpTaylor Mscaled p
  -- square k times
  (List.range k).foldl (fun E _ => cmatmul E E) E0

/-- `exp(-i · t · H)` for a (Hermitian) `H`.  This is the CTQW propagator. -/
def cexpHermTimes (H : CMat) (t : Float) : CMat :=
  -- M = -i t H  =  (0,-t) · H
  let M := cmScaleC (0.0, -t) H
  cexpMat M

/-! ## State evolution and measurement -/

/-- Evolve a state: `ψ(t) = exp(-i t H) ψ₀`. -/
def evolveState (H : CMat) (t : Float) (psi0 : Array C) : Array C :=
  cmatVec (cexpHermTimes H t) psi0

/-- Born-rule probabilities `|ψᵢ|²`. -/
def bornProbs (psi : Array C) : Array Float :=
  psi.map cnormSq

/-- Total probability `∑ |ψᵢ|²` (should stay ≈ 1 under unitary evolution). -/
def totalProb (psi : Array C) : Float :=
  (bornProbs psi).foldl (· + ·) 0.0

/-! ## Standard states -/

/-- Computational basis state `|j⟩` in dimension `n`. -/
def basisState (n j : Nat) : Array C :=
  Array.ofFn (n := n) fun i => if i.val == j then cone else czero

/-- Uniform superposition `(1/√n) ∑ |j⟩`. -/
def uniformSuperposition (n : Nat) : Array C :=
  let amp := 1.0 / (Float.ofNat n).sqrt
  Array.ofFn (n := n) fun _ => (amp, 0.0)

/-! ## Graph Hamiltonians (adjacency matrices) -/

/-- Complete graph `K_n` adjacency: 1 off-diagonal, 0 on the diagonal. -/
def completeGraphH (n : Nat) : CMat :=
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j => if i == j then czero else cone

/-- Path graph `P_n` adjacency: 1 between consecutive vertices. -/
def pathH (n : Nat) : CMat :=
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j =>
      if (i.val + 1 == j.val) || (j.val + 1 == i.val) then cone else czero

/-- Weighted path `P_3` adjacency with edge weights `a` (0–1) and `b` (1–2):
`!![0,a,0; a,0,b; 0,b,0]`.  Spectrum `{-w, 0, w}` with `w = √(a²+b²)`; at
`t = π/w` the middle vertex empties and the state is the two-site superposition
`α|0⟩ + β|2⟩` — a **fractional revival** with target fraction `(2ab/w²)²`. -/
def weightedP3H (a b : Float) : CMat :=
  #[ #[czero, (a, 0.0), czero],
     #[(a, 0.0), czero, (b, 0.0)],
     #[czero, (b, 0.0), czero] ]

/-- Hypercube `Q_d` adjacency on `2^d` vertices: vertices adjacent iff their
labels differ in exactly one bit (Hamming distance 1). -/
def hypercubeH (d : Nat) : CMat :=
  let n := 2 ^ d
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j =>
      let x := i.val ^^^ j.val            -- XOR of the two labels
      -- adjacent iff x is a single set bit, i.e. x ≠ 0 and (x & (x-1)) == 0
      if x ≠ 0 && (x &&& (x - 1)) == 0 then cone else czero

/-- Childs–Goldstone spatial-search Hamiltonian `H = γ·A + |w⟩⟨w|`,
where `A` is the graph adjacency, `w` the marked vertex, `γ` the hopping
rate. -/
def searchHamiltonian (A : CMat) (w : Nat) (γ : Float) : CMat :=
  let n := A.rows
  let H := cmScaleR γ A
  -- add the projector |w⟩⟨w| onto the (w,w) entry
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j =>
      let base := (H[i.val]!)[j.val]!
      if i.val == w && j.val == w then cadd base cone else base

/-! ## Chiral / magnetic walk Hamiltonians

A real-symmetric adjacency walk is *time-reversal symmetric*: probability cannot
prefer one direction around a cycle.  Adding a **magnetic flux** (Peierls phase)
`A_uv ↦ e^{iθ_uv} A_uv`, with `θ_vu = -θ_uv` to keep `H` Hermitian, breaks that
symmetry and produces **directional (chiral) transport** — the walker circulates
preferentially one way.  This is the discrete analogue of a charged particle in
a magnetic field threading the cycle. -/

/-- Directed-cycle **magnetic / chiral** Hamiltonian on `n` vertices.  Each cycle
edge `j → j+1` (mod `n`) carries phase `e^{iθ}` in the forward direction and
`e^{-iθ}` backward, so `H` is Hermitian.  With total flux `nθ ≠ 0 (mod 2π)` the
walk is chiral: occupation circulates preferentially in one direction. -/
def chiralCycleH (n : Nat) (θ : Float) : CMat :=
  let fwd : C := (Float.cos θ, Float.sin θ)      -- e^{+iθ}
  let bwd : C := (Float.cos θ, -(Float.sin θ))   -- e^{-iθ}
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j =>
      -- forward neighbour j = i+1 (mod n)
      if (i.val + 1) % n == j.val then fwd
      -- backward neighbour j = i-1 (mod n)
      else if (j.val + 1) % n == i.val then bwd
      else czero

/-! ## Trace of an evolution -/

/-- Evolve `ψ₀` under `H` over `steps` time steps of size `dt`, returning
for each step `(t, fullProbabilityVector)`.  Recomputes `exp(-i t H)` at each
sampled time from scratch (robust, simple). -/
def traceEvolution (H : CMat) (psi0 : Array C) (steps : Nat) (dt : Float) :
    Array (Float × Array Float) :=
  Array.ofFn (n := steps + 1) fun k =>
    let t := dt * k.val.toFloat
    let psi := evolveState H t psi0
    (t, bornProbs psi)

/-- The amplitude `⟨target|ψ(t)⟩` Born probability for a single target vertex,
sampled over a trace.  Returns `(t, |⟨target|ψ(t)⟩|²)`. -/
def traceTargetProb (H : CMat) (psi0 : Array C) (target : Nat)
    (steps : Nat) (dt : Float) : Array (Float × Float) :=
  Array.ofFn (n := steps + 1) fun k =>
    let t := dt * k.val.toFloat
    let psi := evolveState H t psi0
    (t, cnormSq psi[target]!)

/-- Trace two vertices' Born probabilities over time: `(t, |⟨a|ψ⟩|², |⟨b|ψ⟩|²)`.
Used for fractional revival (source vs target) traces. -/
def traceTwoProbs (H : CMat) (psi0 : Array C) (a b : Nat)
    (steps : Nat) (dt : Float) : Array (Float × Float × Float) :=
  Array.ofFn (n := steps + 1) fun k =>
    let t := dt * k.val.toFloat
    let psi := evolveState H t psi0
    (t, cnormSq psi[a]!, cnormSq psi[b]!)

/-- For a cyclic walk started at vertex `0`, the **directional bias**: total
probability on the "clockwise" half (vertices `1…⌊n/2⌋`, reachable going forward
first) vs the "counter-clockwise" half (vertices `n-1…`).  A real-symmetric walk
keeps these equal; a chiral walk makes them differ.  Returns
`(t, clockwiseProb, counterClockwiseProb)`. -/
def traceChirality (H : CMat) (n : Nat) (steps : Nat) (dt : Float) :
    Array (Float × Float × Float) :=
  let psi0 := basisState n 0
  let half := n / 2
  Array.ofFn (n := steps + 1) fun k =>
    let t := dt * k.val.toFloat
    let probs := bornProbs (evolveState H t psi0)
    -- clockwise = forward neighbours 1..half ; ccw = backward neighbours
    let cw := (List.range half).foldl (fun s d => s + probs[(1 + d) % n]!) 0.0
    let ccw := (List.range half).foldl (fun s d => s + probs[(n - 1 - d) % n]!) 0.0
    (t, cw, ccw)

/-! ## Synthesized PST host (`K₂ □ edgeless_m`)

The inverse-design toolkit (`Graphplay.Toolkit.InverseDesign.synthesizePST m w₀ τ`)
builds the host `K₂ □ (edgeless Fin m)` on `2m` vertices and *proves* PST between
`(0, w₀)` and `(1, w₀)` at `τ = π/2`.  Combinatorially the host is `m` disjoint
edges: in row-major order (cell bit `b` major, fiber index `w` minor) vertex
`i ∈ {0,…,m-1}` (cell 0) is joined only to vertex `i + m` (cell 1).  Here we build
exactly that adjacency as a `CMat` so we can *numerically confirm* the engineered
certificate: evolving `|i⟩` reaches `|i+m⟩` with fidelity → 1 at `t = π/2`. -/

/-- Adjacency `CMat` of the synthesized PST host `K₂ □ (edgeless Fin m)`:
`2m` vertices, vertex `i` ↔ `i + m` for each `i < m` (m disjoint edges). -/
def synthPSTHostH (m : Nat) : CMat :=
  let n := 2 * m
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j =>
      if (i.val + m == j.val) || (j.val + m == i.val) then cone else czero

/-! ## 2D periodic grid (torus) adjacency — Childs–Goldstone spatial search

The canonical CTQW spatial-search testbed.  On the `L × L` periodic square
lattice (a torus) with `N = L²` vertices, vertex `(i, j)` is joined to its four
neighbours `(i±1, j)` and `(i, j±1)` taken mod `L`, so every vertex has degree 4.
This is the dimension `d = 2` *critical* case: spatial search there is only
marginally faster than classical — there is no clean `t* = (π/2)√N` peak to
probability 1 as on the complete graph; instead the optimal probability is `O(1)`
but bounded away from 1, attained around `t ∼ √(N log N)`. -/

/-- Adjacency `CMat` of the `L × L` periodic 2D grid (torus) on `L²` vertices.
Vertex index `v = i·L + j` for row `i`, column `j`.  Neighbours are
`(i±1, j)` and `(i, j±1)` mod `L`; every vertex has degree 4 (for `L ≥ 3`). -/
def gridGraphH (L : Nat) : CMat :=
  let n := L * L
  -- decode vertex v ↦ (row, col); encode (row, col) ↦ v
  let enc := fun (i j : Nat) => (i % L) * L + (j % L)
  Array.ofFn (n := n) fun v =>
    let i := v.val / L
    let j := v.val % L
    -- the four neighbours' indices
    let up    := enc ((i + L - 1) % L) j
    let down  := enc ((i + 1) % L) j
    let left  := enc i ((j + L - 1) % L)
    let right := enc i ((j + 1) % L)
    Array.ofFn (n := n) fun w =>
      if w.val == up || w.val == down || w.val == left || w.val == right then
        cone else czero

/-! ## Attention-graph CTQW (the ML bridge)

A toy "attention matrix": a row-stochastic `n × n` matrix obtained by a softmax
over a translation- or block-symmetric score pattern.  Symmetrising it
`S = ½(A + Aᵀ)` gives a real-symmetric `CMat` usable as a CTQW Hamiltonian, so a
"query" state spreads along high-attention edges.

When the attention pattern has a **2-block symmetry** (an equitable partition into
two cells of equal size with constant inter/intra-cell row sums), the dynamics
restricted to the *cell-uniform* subspace is governed exactly by a `2 × 2`
**quotient** Hamiltonian — the equitable-partition reduction that
`Integrations/MachineLearning.lean` states.  We build both and confirm they agree
numerically. -/

/-- Softmax of a real row (numerically stabilised by subtracting the max). -/
def softmaxRow (xs : Array Float) : Array Float :=
  let m := xs.foldl (fun a x => max a x) (-1.0e30)
  let exps := xs.map (fun x => (x - m).exp)
  let z := exps.foldl (· + ·) 0.0
  exps.map (fun e => e / z)

/-- A toy **two-block attention** score matrix on `n = 2·b` tokens.  Tokens split
into two cells `{0,…,b-1}` and `{b,…,2b-1}`.  The score depends only on whether
the (query, key) pair are in the same cell (`sIn`) or different cells (`sOut`),
giving an equitable 2-partition: every row has the same same-cell / cross-cell
score profile.  Returns the row-stochastic softmax attention matrix as `CMat`
(real entries). -/
def twoBlockAttention (b : Nat) (sIn sOut : Float) : CMat :=
  let n := 2 * b
  let cell := fun (v : Nat) => v / b      -- 0 or 1
  Array.ofFn (n := n) fun i =>
    let scores := Array.ofFn (n := n) fun j =>
      if cell i.val == cell j.val then sIn else sOut
    let probs := softmaxRow scores
    probs.map (fun p => (p, 0.0))

/-- Symmetrise a real `CMat` to `S = ½(A + Aᵀ)` (a valid Hermitian Hamiltonian). -/
def symmetrize (A : CMat) : CMat :=
  let n := A.rows
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j =>
      let aij := (A[i.val]!)[j.val]!
      let aji := (A[j.val]!)[i.val]!
      cscaleR 0.5 (cadd aij aji)

/-- Total Born probability on a *cell* (set of vertex indices `[lo, hi)`). -/
def cellProb (psi : Array C) (lo hi : Nat) : Float :=
  (List.range (hi - lo)).foldl (fun s d => s + cnormSq psi[lo + d]!) 0.0

/-- For a 2-block equitable Hamiltonian `H` with cells of size `b`, the `2 × 2`
**quotient** Hamiltonian `B` acting on cell-uniform states.  Entry `B[r][c]` is
the common row-sum from a vertex of cell `r` into all vertices of cell `c`
(constant across the cell by equitability).  We read it off row `r·b` of `H`. -/
def quotient2 (H : CMat) (b : Nat) : CMat :=
  let rowSum := fun (rRep c : Nat) =>
    (List.range b).foldl (fun acc d => cadd acc ((H[rRep]!)[c * b + d]!)) czero
  #[ #[rowSum 0 0, rowSum 0 1],
     #[rowSum b 0, rowSum b 1] ]

/-- Evolve the `2`-dim quotient state under the `2 × 2` quotient Hamiltonian and
return the cell-occupation pair `(P₀, P₁)` at time `t`.  The cell-uniform vector
`|cell r⟩ = (1/√b)Σ_{v∈r}|v⟩` maps to the quotient basis vector `|r⟩`, and the
quotient amplitudes' squared moduli ARE the full-graph cell occupations. -/
def quotientCellProbs (B : CMat) (q0 : Array C) (t : Float) : Float × Float :=
  let q := evolveState B t q0
  (cnormSq q[0]!, cnormSq q[1]!)

/-! ## Open-system (Lindblad) density-matrix dynamics

For decoherence we leave pure-state land and evolve a **density matrix**
`ρ : CMat`.  Under a *dephasing* GKLS generator with jump operators `L_v = |v⟩⟨v|`
(the diagonal projectors) and rate `γ`,

  `dρ/dt = -i[H,ρ] + γ Σ_v ( |v⟩⟨v| ρ |v⟩⟨v| − ½{|v⟩⟨v|,ρ} )`.

For these diagonal `L_v` the dissipator acts very simply: it *kills off-diagonal
coherences* at rate `γ` while leaving populations (the diagonal) untouched.  We
Euler-step this generator.  Observables: **purity** `Tr(ρ²)` (starts at `1` for a
pure state, decays toward `1/n` as coherences vanish) and **populations**
(diagonal of `ρ`). -/

/-- Density matrix of a pure state `|ψ⟩⟨ψ|`. -/
def pureDensity (psi : Array C) : CMat :=
  let n := psi.size
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j => cmul psi[i.val]! (cconj psi[j.val]!)

/-- Commutator `[H, ρ] = Hρ − ρH`. -/
def commutator (H ρ : CMat) : CMat :=
  cmAdd (cmatmul H ρ) (cmScaleR (-1.0) (cmatmul ρ H))

/-- The **dephasing dissipator** `D(ρ) = γ Σ_v (|v⟩⟨v|ρ|v⟩⟨v| − ½{|v⟩⟨v|,ρ})`.
With `L_v = |v⟩⟨v|`, `Σ_v |v⟩⟨v|ρ|v⟩⟨v|` keeps only the diagonal of `ρ`, and
`Σ_v ½{|v⟩⟨v|,ρ} = ρ` (each entry `ρ_ij` gets `½(δ_iv+δ_jv)` summed to `1`).  So
`D(ρ)_ij = γ·(diag − ρ)_ij = −γ ρ_ij` off-diagonal, `0` on-diagonal: pure
coherence decay. -/
def dephasingDissipator (γ : Float) (ρ : CMat) : CMat :=
  let n := ρ.rows
  Array.ofFn (n := n) fun i =>
    Array.ofFn (n := n) fun j =>
      if i == j then czero
      else cscaleR (-γ) ((ρ[i.val]!)[j.val]!)

/-- One Euler step of the GKLS generator `ρ ↦ ρ + dt·(−i[H,ρ] + D(ρ))`. -/
def lindbladStep (H : CMat) (γ dt : Float) (ρ : CMat) : CMat :=
  let comm := commutator H ρ
  let drift := cmScaleC (0.0, -1.0) comm        -- −i[H,ρ]
  let diss := dephasingDissipator γ ρ
  let gen := cmAdd drift diss
  cmAdd ρ (cmScaleR dt gen)

/-- Purity `Tr(ρ²) = Σ_ij ρ_ij ρ_ji`.  Returns the real part (imaginary part is
`≈0` for a valid density matrix). -/
def purity (ρ : CMat) : Float :=
  let n := ρ.rows
  (List.range n).foldl (fun acc i =>
    (List.range n).foldl (fun acc2 j =>
      acc2 + (cmul (ρ[i]!)[j]! (ρ[j]!)[i]!).1) acc) 0.0

/-- Populations `ρ_vv` (the real diagonal). -/
def populations (ρ : CMat) : Array Float :=
  Array.ofFn (n := ρ.rows) fun i => ((ρ[i.val]!)[i.val]!).1

/-- Total population `Tr(ρ)` (should stay ≈1). -/
def traceRho (ρ : CMat) : Float :=
  (populations ρ).foldl (· + ·) 0.0

/-- Evolve a density matrix under the dephasing Lindbladian for `steps` Euler
steps of size `dt`, sampling `(t, purity, Tr(ρ), populations)` every `every`
steps (including `t = 0`). -/
def traceLindblad (H : CMat) (γ dt : Float) (ρ0 : CMat) (steps every : Nat) :
    Array (Float × Float × Float × Array Float) := Id.run do
  let mut ρ := ρ0
  let mut out : Array (Float × Float × Float × Array Float) := #[]
  for s in List.range (steps + 1) do
    if s % every == 0 then
      out := out.push (dt * s.toFloat, purity ρ, traceRho ρ, populations ρ)
    ρ := lindbladStep H γ dt ρ
  return out

/-! ## Pretty-printing helpers -/

/-- Round to `d` decimal places for compact tables. -/
def roundTo (d : Nat) (x : Float) : Float :=
  let f := Float.ofNat (10 ^ d)
  (x * f).round / f

/-- Pad a string on the right to width `w`. -/
def padRight (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')

/-- A crude ASCII bar of length proportional to `p ∈ [0,1]` (width 30). -/
def probBar (p : Float) : String :=
  let n := (p * 30.0).round.toUInt64.toNat
  let n := min n 30
  String.ofList (List.replicate n '#')

end Graphplay.Simulate
