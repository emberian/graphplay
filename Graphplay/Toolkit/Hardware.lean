/-
# Hardware constraint primitives

This file is **exploratory**: it sketches a vocabulary for talking about the
constraints imposed by a real quantum-hardware platform on a graph-walk
design, and explains how those constraints interact with the project's central
notion of an *equitable partition* (the structure used to reduce a noisy
scheduled walk on a large graph to a walk on a smaller quotient).

The references that motivate this file are:

* Sadowski 2014 (`1406.0339`) — planar networks for quantum spatial search.
  Their Apollonian-network example shows that *planarity is not free*: a
  hardware platform that can only realize planar layouts already restricts the
  set of graphs whose walks can be efficiently implemented, independently of
  their abstract search-time scaling.
* King et al. 2025 (`2501.08148`) — long-range tunneling.  Their finite-range
  models live on lattices in `ℝ^d` and require a coupling-distance bound.
  Their `1/r^α` long-range models are exactly the situation where
  `maxCouplingDistance = none`.
* Wong 2017 (`1706.06939`) — lackadaisical walks need engineered self-loops.
  Concretely, the *self-loop weight* is a piece of hardware design, even
  though graph theory tends to discard self-loops.  Our `HardwareSpec` carries
  enough information to distinguish "no self-loops allowed" from "self-loops
  at a chosen weight."

The headline statement is `WeightedGraph.satisfies_quotient`: hardware
constraints survive the equitable-partition lift.  This says, informally,
*"if you can build the big graph, you can build the quotient on the cell
indices"*.  The `quotientHWGraph` construction is concrete (built from the
Hermitian symmetric quotient); the geometric/topological *theorems* are deferred
via honest theorem-level `sorry`, as we are primarily laying out a vocabulary.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Graphplay.Weighted
import Graphplay.Equitable

universe u v

namespace Graphplay

/-! ## Hardware specifications

A `HardwareSpec` is a *recipe of constraints* a candidate graph design must
satisfy in order to be runnable on a particular platform.  Each field is
optional so that several specifications can be intersected by simply
combining the imposed constraints; an unset field means "the platform places
no constraint on this axis."

The axes deliberately correspond to physically distinct kinds of constraint:

* `maxCouplingDistance` — finite-range tunneling (Bose-Hubbard, Rydberg
  arrays, neutral atom lattices).
* `surfaceGenus` — topology of the substrate. `Some 0` is planar
  (superconducting flip-chips, photonic chips); `Some g` is a genus-`g`
  surface (some flux-qubit architectures wrap a torus).
* `qubitCountBound` — naive size limit imposed by the device.
* `allowedPhaseSet` — discrete set of complex phases the platform can realize
  on a single coupling.  For chiral hardware (synthetic gauge fields, flux
  ladders), this is a small subset of the unit circle, often
  `{1, e^{iπ/4}, e^{iπ/2}, …}`.
* `requiredRegularity` — degree-uniformity required by the control hardware.
  Useful when the analog control hardware can only address one tunneling
  amplitude per vertex.

The structure is intentionally lightweight; nothing forces the constraints to
be consistent.  Combining inconsistent constraints produces a
`HardwareSpec` that no graph satisfies, which is the expected behaviour. -/
structure HardwareSpec where
  /-- Maximum geometric coupling distance between two vertices that may be
  connected by an edge.  `none` means long-range couplings are permitted. -/
  maxCouplingDistance : Option ℝ
  /-- Genus of the orientable surface the layout must embed on.  `Some 0`
  means planar; `none` means topology is unconstrained. -/
  surfaceGenus : Option ℕ
  /-- Hard upper bound on the number of qubits.  `none` means unbounded. -/
  qubitCountBound : Option ℕ
  /-- Set of complex unit-modulus phases the hardware may apply to a single
  coupling.  `Set.univ` means any phase is allowed. -/
  allowedPhaseSet : Set ℂ
  /-- Required vertex degree (degree-regular layouts).  `none` means
  irregular layouts are permitted. -/
  requiredRegularity : Option ℕ

namespace HardwareSpec

/-- The empty spec imposes no constraints whatsoever.  Useful as a unit when
intersecting specs. -/
def unconstrained : HardwareSpec where
  maxCouplingDistance := none
  surfaceGenus := none
  qubitCountBound := none
  allowedPhaseSet := Set.univ
  requiredRegularity := none

/-- Intersect two specs.  A graph satisfies the result iff it satisfies both
inputs.  Numeric fields take the *tighter* of the two bounds (the minimum
distance, the minimum genus, the minimum qubit count), and the allowed-phase
set is intersected.  The regularity field is conservative: if the two specs
disagree on degree, the intersection has *no* satisfying graph and we record
that by collapsing to an impossible regularity. -/
def intersect (H K : HardwareSpec) : HardwareSpec := by
  exact
    { maxCouplingDistance := match H.maxCouplingDistance, K.maxCouplingDistance with
        | some r, some s => some (min r s)
        | some r, none   => some r
        | none,   some s => some s
        | none,   none   => none
      surfaceGenus := match H.surfaceGenus, K.surfaceGenus with
        | some g, some h => some (min g h)
        | some g, none   => some g
        | none,   some h => some h
        | none,   none   => none
      qubitCountBound := match H.qubitCountBound, K.qubitCountBound with
        | some m, some n => some (min m n)
        | some m, none   => some m
        | none,   some n => some n
        | none,   none   => none
      allowedPhaseSet := H.allowedPhaseSet ∩ K.allowedPhaseSet
      requiredRegularity := match H.requiredRegularity, K.requiredRegularity with
        | some d, some e => if d = e then some d else some 0  -- impossible degree
        | some d, none   => some d
        | none,   some e => some e
        | none,   none   => none }

/-! ### Constructor variants

These are the typical "starter packs" a user would assemble at the top of an
experiment file. -/

/-- Planar layout.  Distance, qubit count, phases, and regularity left
unconstrained. -/
def planarSpec : HardwareSpec where
  maxCouplingDistance := none
  surfaceGenus := some 0
  qubitCountBound := none
  allowedPhaseSet := Set.univ
  requiredRegularity := none

/-- Genus-`g` orientable surface layout.  `g = 0` recovers `planarSpec`. -/
def surfaceSpec (g : ℕ) : HardwareSpec where
  maxCouplingDistance := none
  surfaceGenus := some g
  qubitCountBound := none
  allowedPhaseSet := Set.univ
  requiredRegularity := none

/-- Nearest-neighbour: only couplings of geometric distance at most `radius`
are allowed.  This is the King-et-al. finite-range regime; the long-range
`1/r^α` regime corresponds to `maxCouplingDistance = none`. -/
def nearestNeighborSpec (radius : ℝ) : HardwareSpec where
  maxCouplingDistance := some radius
  surfaceGenus := none
  qubitCountBound := none
  allowedPhaseSet := Set.univ
  requiredRegularity := none

/-- Chiral hardware: only couplings whose phase lies in the finite (or
prescribed) set `phases` are allowed.  Typical examples:

* trivial real couplings: `phases = {1, -1}`
* π/4 flux ladder: `phases = {1, exp(iπ/4), exp(iπ/2), exp(i3π/4), -1, …}`
* tunable chiral platform: `phases = univ`. -/
def chiralAllowedSpec (phases : Set ℂ) : HardwareSpec where
  maxCouplingDistance := none
  surfaceGenus := none
  qubitCountBound := none
  allowedPhaseSet := phases
  requiredRegularity := none

/-- Degree-regular layout.  Useful for analog control hardware that only
addresses one tunneling amplitude per vertex. -/
def regularSpec (d : ℕ) : HardwareSpec where
  maxCouplingDistance := none
  surfaceGenus := none
  qubitCountBound := none
  allowedPhaseSet := Set.univ
  requiredRegularity := some d

/-- Bounded-size hardware. -/
def sizeBoundedSpec (n : ℕ) : HardwareSpec where
  maxCouplingDistance := none
  surfaceGenus := none
  qubitCountBound := some n
  allowedPhaseSet := Set.univ
  requiredRegularity := none

end HardwareSpec

/-! ## Satisfaction predicate

We treat satisfaction of a `HardwareSpec` as a predicate parameterised by an
embedding `embed : V → ℝ²` of the vertices into the plane (or, more
generally, a chosen layout).  We use `ℝ²` for concreteness; a real codebase
would parameterise over a chosen substrate manifold and is a natural place
for the project to grow.

The five conjuncts mirror the five `HardwareSpec` fields. -/

/-- A weighted graph `G`, given an explicit vertex embedding `embed`,
satisfies the hardware spec `H` when:

* edges only occur between embedded points within `maxCouplingDistance`;
* the geometric realisation embeds in a surface of genus `surfaceGenus`;
* the number of vertices does not exceed `qubitCountBound`;
* every non-zero edge weight has phase in `allowedPhaseSet`;
* every vertex has the required degree.

All conjuncts are stated with `sorry`-filled placeholders for the actual
geometric/topological content; the point is to fix the predicate's shape so
later files can quantify over it. -/
def WeightedGraph.satisfies
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (H : HardwareSpec) (embed : V → ℝ × ℝ) : Prop :=
  -- conjunction of all five constraint axes
  (∀ x y : V, G.adj x y ≠ 0 →
    match H.maxCouplingDistance with
    | some _ => True   -- placeholder: dist(embed x, embed y) ≤ r
    | none   => True) ∧
  (match H.surfaceGenus with
   | some _ => True    -- placeholder: the geometric realisation embeds on Σ_g
   | none   => True) ∧
  (match H.qubitCountBound with
   | some n => Fintype.card V ≤ n
   | none   => True) ∧
  (∀ x y : V, G.adj x y ≠ 0 → G.adj x y ∈ H.allowedPhaseSet) ∧
  (match H.requiredRegularity with
   | some _ => True    -- placeholder: |{y : G.adj x y ≠ 0}| = d for every x
   | none   => True)

/-- `unconstrained` is satisfied by every graph and embedding.  -/
theorem WeightedGraph.satisfies_unconstrained
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (embed : V → ℝ × ℝ) :
    G.satisfies HardwareSpec.unconstrained embed := by
  sorry

/-- Intersection of specs satisfied iff both are satisfied. -/
theorem WeightedGraph.satisfies_intersect
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (H K : HardwareSpec) (embed : V → ℝ × ℝ) :
    G.satisfies (H.intersect K) embed ↔ G.satisfies H embed ∧ G.satisfies K embed := by
  sorry

/-! ## Quotient hardware specs

This is the central "engineering reduction" content of the file.  Given an
equitable partition `P : V → I`, the *quotient* `WeightedGraph` on `I` carries
the cell-to-cell total weights.  When `G` satisfies a hardware spec `H`, the
quotient satisfies a *derived* spec `H.quotient` whose constraints are at
least as easy to meet — fewer qubits, smaller layouts, the same phase set.

The construction is intentionally conservative.  For instance:

* `qubitCountBound` is replaced by `Fintype.card I`, which is at most the
  original count by the partition's existence.
* `surfaceGenus` cannot increase under a quotient: a planar embedding of `G`
  gives a planar drawing of the quotient by contracting each cell to a
  representative point.  So we keep `surfaceGenus` unchanged.
* `maxCouplingDistance` *can* increase under a quotient — cell representatives
  can be further apart than the worst original coupling — so we record it as
  `none` (long-range), to be safe.  Refining this is a clear next research
  question.
* `allowedPhaseSet` should be replaced by its multiplicative-closure (since
  cell-to-cell weights are sums of original couplings), but for our scaffolding
  we keep the *same* set and note the closure question as future work.
* `requiredRegularity` cannot be preserved exactly under quotients (cells of
  different sizes contribute differently); we relax it to `none`. -/
def HardwareSpec.quotient (H : HardwareSpec) : HardwareSpec where
  maxCouplingDistance := none
  surfaceGenus := H.surfaceGenus
  qubitCountBound := H.qubitCountBound
  allowedPhaseSet := H.allowedPhaseSet
  requiredRegularity := none

/-- The quotient weighted graph induced by an equitable partition.  Its
off-diagonal `(i, j)` entry is the *symmetric* (Hermitian) quotient weight
`P.symmQuotient i j = √|C_i| · Q i j / √|C_j|` — the cell-to-cell coupling read
off in the orthonormal cell-uniform basis, which the equitable condition makes
independent of the chosen representative.  The diagonal is forced to `0`:
within-cell edges become self-loops on the quotient, and the `WeightedGraph`
model is loopless (the self-loop ledger is tracked separately; see the
`Self-loop ledger` open question below).

Concrete and `sorry`-free: Hermiticity off the diagonal comes from
`symmQuotient_isHermitian`, and the diagonal is zero by construction. -/
noncomputable def EquitablePartition.quotientHWGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) : WeightedGraph I where
  adj := Matrix.of fun i j => if i = j then 0 else P.symmQuotient i j
  herm := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : j = i
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
      -- `star (symmQuotient j i) = symmQuotient i j` from Hermiticity.
      exact congrFun (congrFun P.symmQuotient_isHermitian i) j
  loopless := by intro i; simp [Matrix.of_apply]

/-- **Engineering reduction theorem.**

If `G` satisfies a hardware spec `H` under the embedding `embed`, and if `P`
is an equitable partition of `G` into cells `I`, then there is an *induced
embedding* `embed_quotient : I → ℝ²` (e.g. the centroid of each cell) under
which the quotient graph `P.quotientHWGraph` satisfies the relaxed spec
`H.quotient`.

This is the slogan that "hardware constraints survive the
equitable-partition lift": if you can physically build the big walk, you can
physically build (an at most equally constrained version of) the small
quotient walk. -/
theorem WeightedGraph.satisfies_quotient
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : WeightedGraph V} {H : HardwareSpec} {embed : V → ℝ × ℝ}
    (hG : G.satisfies H embed)
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) :
    ∃ embed_quotient : I → ℝ × ℝ,
      (P.quotientHWGraph).satisfies H.quotient embed_quotient := by
  sorry

/-! ## Open questions / future work

Concrete research questions this file suggests:

1. **Phase-set closure.**  Is `H.allowedPhaseSet` closed under the sums and
   products needed to express *quotient* edge weights?  If not, what is the
   smallest hardware that realises the multiplicative closure?  See the
   chiral hardware tables in flux-ladder experiments.
2. **Quotient-stable distance bounds.**  Under what choice of `embed_quotient`
   does `maxCouplingDistance` remain bounded (not merely "none") after the
   quotient?  Conjecture: when the partition's cell diameters in the embedding
   are at most some `δ`, the quotient embedding inherits a distance bound of
   `radius + δ`.
3. **Genus preservation under contraction.**  A graph drawn on Σ_g whose
   cells are simply connected contracts to a graph drawn on Σ_g — formalising
   this is the natural next step.
4. **Self-loop ledger.**  Wong's lackadaisical walks carry per-vertex
   self-loops of weight `4/N`.  Self-loops sit outside the current
   `WeightedGraph` model (because `loopless` forbids them).  A natural
   extension is a parallel `LackadaisicalGraph` carrying a diagonal
   `selfWeights : V → ℂ`. -/

end Graphplay
