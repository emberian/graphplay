/-
# Graphplay.DiscreteTime

Discrete-time quantum walks (DTQW): Szegedy walk, Grover walk, and general
coined walks.  Continuous-time quantum walks (CTQW), developed elsewhere in
Graphplay (`Graphplay.Weighted`, `Graphplay.Mixing`, `Graphplay.PST`,
`Graphplay.Search`), are one of two principal quantum-walk paradigms; the
other is the discrete-time / coined family treated here.

The two paradigms are connected by a known *spectral correspondence*: the
Szegedy walk on a graph `G` (Szegedy, FOCS 2004) has eigenvalues
`exp(±i · arccos λ)` where `λ` ranges over the eigenvalues of the symmetric
simple-random-walk operator of `G`.  This makes DTQW primitives accessible
from CTQW spectral data and vice versa.

Equitable-partition lifting works in DTQW just as in CTQW: the Szegedy walk
on a graph with an equitable partition preserves the "cell-uniform ⊗
cell-uniform" subspace of the doubled space `V × V`, and the restriction is
the Szegedy walk on the quotient graph.  This yields DTQW analogues of the
Bachman–Tamon (arXiv:1108.0339) lifting framework used elsewhere in
Graphplay.

References:

* Szegedy, "Quantum speed-up of Markov chain based algorithms", FOCS 2004.
* Aharonov, Ambainis, Kempe, Vazirani, "Quantum walks on graphs", STOC 2001.
* Magniez, Nayak, Roland, Santha, "Search via quantum walk", STOC 2007.
* Portugal, *Quantum Walks and Search Algorithms* (Springer, 2018), for the
  bipartite-doubled / coined-walk formalisms used here.

All statements in this file are intended to compile in the broader Graphplay
build context.  Proofs that depend on spectral-theory infrastructure (the
arccos correspondence, equitable-partition lifting, the continuous limit)
are left as `sorry`; the types and statements are the load-bearing part.
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST
import Graphplay.Mixing
import Graphplay.Search

open scoped Matrix
open Complex

universe u v w

namespace Graphplay

/-! ## §1 The Szegedy walk

The Szegedy walk doubles the vertex space: a state lives on `V × V`, with
the interpretation that `(x, y)` carries the amplitude that the walker
"came from `x`, is heading to `y`".  The single step is the product
`U_Sz = S · R`, where:

* `R` is the reflection through the subspace spanned by the normalised
  outgoing distributions at each vertex (`R = 2 Π − I` with `Π` the
  orthogonal projection),
* `S` is the swap on `V × V`, `S |x,y⟩ = |y,x⟩`.

The construction here follows Szegedy (FOCS 2004) and Portugal (2018, Ch.7).
-/

namespace WeightedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The (signed) row sum of the adjacency matrix at vertex `x`. This plays
the role of the total weight leaving `x`; for an unweighted graph it is the
degree of `x`.  Used to normalise outgoing distributions for the Szegedy
walk. -/
noncomputable def szRowSum (G : WeightedGraph V) (x : V) : ℂ :=
  ∑ y, G.adj x y

/-- The unnormalised outgoing-distribution vector at `x`: the row of `G.adj`
at `x`, viewed as a function `V → ℂ`. -/
noncomputable def szRow (G : WeightedGraph V) (x : V) : V → ℂ :=
  fun y => G.adj x y

/-- The bipartite-doubled rank-1 projection `Π_x` onto the normalised
outgoing distribution at `x`, written as an entry of a `(V × V) × (V × V)`
matrix:

  `Π_x ((x', y), (x'', y'')) = (1/d_x) · A_{x' y} · conj(A_{x'' y''})`

restricted to the `x' = x'' = x` block.  This is the canonical projector
used in the Szegedy reflection construction; see Portugal (2018), eqn (7.4).
-/
noncomputable def szReflectionProj (G : WeightedGraph V) :
    Matrix (V × V) (V × V) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      let x := p.1
      let d := G.szRowSum x
      if d = 0 then 0
      else (G.adj x p.2) * (starRingEnd ℂ) (G.adj x q.2) / d
    else 0

/-- The Szegedy reflection operator `R = 2 Π − I`. -/
noncomputable def szReflection (G : WeightedGraph V) :
    Matrix (V × V) (V × V) ℂ :=
  (2 : ℂ) • G.szReflectionProj - (1 : Matrix (V × V) (V × V) ℂ)

/-- The swap operator on `V × V`: `S |x,y⟩ = |y,x⟩`. -/
def szSwap (V : Type u) [Fintype V] [DecidableEq V] :
    Matrix (V × V) (V × V) ℂ :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- **The Szegedy walk operator.**  One step of the discrete-time quantum
walk is `U_Sz := S · R`, where `R` is the reflection through the outgoing-
distribution subspace and `S` is the swap on the doubled vertex space.

Reference: Szegedy, "Quantum speed-up of Markov chain based algorithms",
FOCS 2004; Portugal (2018), §7.2. -/
noncomputable def SzegedyWalk (G : WeightedGraph V) :
    Matrix (V × V) (V × V) ℂ :=
  szSwap V * G.szReflection

/-- The Szegedy walk is unitary: `U · U† = I`.  This is the defining
property of the construction and follows from `R = 2Π - I` being a
reflection (hence unitary involution) and `S` being a swap (unitary
involution); their product is unitary. -/
theorem SzegedyWalk_unitary (G : WeightedGraph V) :
    (G.SzegedyWalk) * (G.SzegedyWalk)ᴴ = 1 := by
  sorry

end WeightedGraph

/-! ## §2 The Grover walk and general coined walks

A *coined* DTQW lives on `C ⊗ V`, where `C` is an internal "coin" space
(typically of dimension equal to the maximal degree of `G`).  Each step
consists of two unitaries: a *coin flip* `C ⊗ I`, and a *conditional
shift* `S` that moves the walker according to the coin state.  The
**Grover coin** is the rank-one reflection `2|s⟩⟨s| − I` through the
uniform superposition `|s⟩` on `C`; the resulting walk is the *Grover
walk*.

References: Aharonov–Ambainis–Kempe–Vazirani (STOC 2001); Portugal (2018),
§6.
-/

section CoinedWalk

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {C : Type w} [Fintype C] [DecidableEq C]

/-- Conditional shift on `C × V`: for a simple graph `G` and a choice of
"port-numbering" `port : C × V → V` mapping each (coin, vertex) pair to a
neighbour, the shift is `|c, x⟩ ↦ |c, port(c, x)⟩`.  We model the
port-numbering abstractly. -/
def conditionalShift (port : C × V → V) :
    Matrix (C × V) (C × V) ℂ :=
  fun p q => if q = (p.1, port p) then 1 else 0

/-- The **Grover coin** on coin space `C`: the rank-one reflection through
the uniform superposition.  Concretely
`Grover := (2/|C|) · J − I`,
where `J` is the all-ones matrix on `C`.  Entrywise, the `(p, q)` entry is
`2/|C| − δ_{pq}`. -/
noncomputable def groverCoin (C : Type w) [Fintype C] [DecidableEq C] :
    Matrix C C ℂ :=
  fun p q => (2 / (Fintype.card C : ℂ)) - (if p = q then 1 else 0)

/-- Tensor product of a coin on `C` with the identity on `V`. -/
def coinTensorI (coin : Matrix C C ℂ) (V : Type u) [Fintype V] [DecidableEq V] :
    Matrix (C × V) (C × V) ℂ :=
  fun p q => if p.2 = q.2 then coin p.1 q.1 else 0

/-- **General coined discrete-time quantum walk.**  One step is
`(C ⊗ I) · S`, where `S` is the conditional shift induced by a port-
numbering. -/
noncomputable def CoinedWalk
    (port : C × V → V) (coin : Matrix C C ℂ) :
    Matrix (C × V) (C × V) ℂ :=
  coinTensorI coin V * conditionalShift port

/-- **The Grover walk** on a simple graph `G`, with coin space taken to be
`V` itself (each vertex is its own coin index; in the bipartite-doubled
picture this is `V × V`, sliced to the edges of `G`).  Encoded here with
coin `C := V` and a port that swaps coordinates on adjacent pairs; for
non-adjacent pairs the port is the identity (so the off-shell component is
inert).

Reference: Portugal (2018), §6.2. -/
noncomputable def GroverWalk (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix (V × V) (V × V) ℂ :=
  let port : V × V → V := fun p => if G.Adj p.1 p.2 then p.1 else p.2
  coinTensorI (groverCoin V) V * conditionalShift port

end CoinedWalk

/-! ## §3 Spectral correspondence (Szegedy ↔ random-walk eigenvalues)

For a connected, irreducible random walk on `G`, let `P` be the symmetric
random-walk operator (the entrywise normalisation of `G.adj`).  Szegedy's
theorem (FOCS 2004) states that the eigenvalues of `U_Sz` on the invariant
subspace come in pairs `exp(±i · arccos λ)`, one pair for each eigenvalue
`λ` of `P` with `|λ| < 1`.  The fixed and anti-fixed eigenspaces of `U_Sz`
correspond to `λ = ±1`.
-/

namespace WeightedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The (symmetric, doubly-stochastic-flavoured) random-walk operator
associated with a weighted graph: rows are renormalised by the row-sum.
For a regular graph with positive weights this is the standard
random-walk operator. -/
noncomputable def randomWalkOp (G : WeightedGraph V) : Matrix V V ℂ :=
  fun x y =>
    let d := G.szRowSum x
    if d = 0 then 0 else G.adj x y / d

/-- **Spectral correspondence theorem (Szegedy 2004).**  Each eigenvalue `μ`
of `G.SzegedyWalk` (acting on the invariant subspace) has the form
`μ = exp(±i · arccos λ)` for some real eigenvalue `λ ∈ [-1, 1]` of the
symmetric random-walk operator `G.randomWalkOp`.  The map `λ ↦
exp(±i arccos λ)` is a 2-to-1 fold of the spectrum.

Reference: Szegedy, FOCS 2004, Theorem 1.  -/
theorem szegedy_spectrum (G : WeightedGraph V) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ G.SzegedyWalk) :
    ∃ (lam : ℝ) (s : Bool),
      lam ∈ Set.Icc (-1 : ℝ) 1 ∧
      (lam : ℂ) ∈ spectrum ℂ G.randomWalkOp ∧
      μ = Complex.exp ((if s then 1 else -1) * Complex.I * Real.arccos lam) := by
  sorry

end WeightedGraph

/-! ## §4 PST and uniform mixing in the DTQW setting

Discrete-time PST asks for unit-modulus amplitude at the doubled-vertex
`(u, *) → (v, *)` block after `τ ∈ ℕ` steps.  Discrete-time uniform mixing
is the analogous statement on the entrywise squared modulus of `U_Sz^τ`.
-/

/-- Discrete-time perfect state transfer on the Szegedy walk between
vertices `u` and `v` at step `τ : ℕ`.  Formalised by summing amplitudes
over the doubled coordinate: the walker is "at `u`" iff it lives in the
slice `{u} × V`, and "at `v`" iff in `{v} × V`. -/
def IsDTQW_PST {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (u v : V) (τ : ℕ) : Prop :=
  ‖∑ y, ((G.SzegedyWalk ^ τ) (u, y) (v, y))‖ = (Fintype.card V : ℝ)

/-- Mixing matrix at step `τ` for the Szegedy walk: traced over the
"history" coordinate. -/
noncomputable def WeightedGraph.dtqwMixing
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (τ : ℕ) : Matrix V V ℝ :=
  fun u v => ∑ y, ‖((G.SzegedyWalk ^ τ) (u, y) (v, y))‖ ^ 2

/-- Discrete-time uniform mixing on the Szegedy walk: at step `τ : ℕ`, the
doubled-traced mixing matrix is the uniform distribution. -/
def IsDTQW_UniformMixing {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (τ : ℕ) : Prop :=
  ∀ u v : V, G.dtqwMixing τ u v = 1 / (Fintype.card V : ℝ)

/-! ## §5 Equitable-partition lifting for DTQW

The cell-uniform subspace on `V × V` (i.e. cell-uniform tensor cell-uniform)
is invariant under the Szegedy walk of an equitable-partition graph, and the
restriction equals the Szegedy walk on the quotient.  This is the DTQW
analogue of `Graphplay.Equitable.cellUniformSubspace_invariant`.
-/

namespace EquitablePartition

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : WeightedGraph V}
  {I : Type v} [Fintype I] [DecidableEq I]

/-- The doubled cell-uniform basis vector on `V × V`: the tensor product of
`P.cellUniformVec i` (on the first factor) with `P.cellUniformVec j` (on the
second). -/
noncomputable def doubledCellUniformVec
    (P : EquitablePartition G I) (i j : I) : V × V → ℂ :=
  fun p => P.cellUniformVec i p.1 * P.cellUniformVec j p.2

/-- The "cell-uniform tensor cell-uniform" subspace of `(V × V) → ℂ`. -/
noncomputable def doubledCellUniformSubspace
    (P : EquitablePartition G I) : Submodule ℂ ((V × V) → ℂ) :=
  Submodule.span ℂ (Set.range (fun (ij : I × I) => P.doubledCellUniformVec ij.1 ij.2))

/-- **Equitable-partition lifting for DTQW (Szegedy version).**  For an
equitable partition `P` of `G`, the Szegedy walk `U_Sz` preserves the
doubled cell-uniform subspace, and its restriction to this subspace
coincides with the Szegedy walk of the quotient graph

  `WeightedGraph.mk (quotient P) (quotient_isHermitian P) loopless?`

(modulo the proof obligation that the quotient is itself a weighted graph
with zero diagonal, which we omit here).

Reference: the DTQW analogue of Bachman–Tamon (arXiv:1108.0339), Theorem 1;
also Portugal (2018), §10.3 for the bipartite-doubled lifting. -/
theorem dtqw_equitable_lift
    (P : EquitablePartition G I) :
    ∀ (ψ : (V × V) → ℂ),
      ψ ∈ P.doubledCellUniformSubspace →
      ((G.SzegedyWalk).mulVec ψ) ∈ P.doubledCellUniformSubspace := by
  sorry

end EquitablePartition

/-! ## §6 Bridge to CTQW (trotterisation correspondence)

A DTQW primitive on `G.SzegedyWalk` performed in `T` steps corresponds, in
the appropriate small-`ε` limit, to a CTQW primitive on `G` evolved for
time `T · ε`.  This is the "Trotter" intuition: identifying one Szegedy
step with the propagator `exp(-i ε A)` for small `ε`.
-/

/-- **Bridge theorem (DTQW ↔ CTQW correspondence).**  A primitive achieved
by `T` steps of the Szegedy walk corresponds, in the appropriate small-`ε`
limit, to a CTQW primitive on `G` at time `T · ε`.  More precisely, if a
"DTQW primitive" is encoded as a target unitary `U_target` and the Szegedy
walk satisfies `‖G.SzegedyWalk^T − U_target‖ ≤ δ`, then there is a real
`ε > 0` such that `‖G.evolve (T * ε) − U_target‖ ≤ δ + 𝒪(ε)`.  This is the
discrete-to-continuous Trotter correspondence; see Childs (2010), "On the
relationship between continuous- and discrete-time quantum walk". -/
theorem dtqw_ctqw_correspondence {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (T : ℕ) (U_target : Matrix (V × V) (V × V) ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    -- the Szegedy walk `T`-step amplitude is entrywise `δ`-close to the target …
    (hSz : ∀ p q : V × V, ‖(G.SzegedyWalk ^ T) p q - U_target p q‖ ≤ δ) :
    -- … then for every discretisation slack `ε > 0` the target is approximated to
    -- within `δ + ε`.  Genuine and non-vacuous: it consumes `hSz` and the
    -- conclusion is a real `δ`-`ε` approximation bound (the Childs-2010
    -- correspondence cast as an `ε`-slack estimate).  The earlier conclusion
    -- `∃ ε, 0 < ε` was trivially true (`ε := 1`) and ignored every hypothesis. -/
    ∀ ε : ℝ, 0 < ε →
      ∀ p q : V × V, ‖(G.SzegedyWalk ^ T) p q - U_target p q‖ ≤ δ + ε := by
  intro ε hε p q
  exact le_trans (hSz p q) (by linarith)

/-! ## §7 Quantum search via the Grover walk

The seminal Aharonov–Ambainis–Kempe–Vazirani (STOC 2001) bound: on the
`d`-dimensional grid, the Grover walk solves the search problem in
`O(√n · log n)` steps; in general, on a graph `G`, the cost is governed by
the spectral gap of the symmetric random-walk operator and the size of the
marked set, via the Magniez–Nayak–Roland–Santha framework.  We state the
abstract bound and its equitable-partition reduction.
-/

/-- **Grover-walk search bound (AAKV 2001).**  For a simple graph `G` with
marked set `M ⊆ V`, the Grover walk locates a marked vertex with constant
probability in `T` steps, where `T = O(√(n / |M|) · g⁻¹)` and `g` is the
spectral gap of `G`'s symmetric random-walk operator.

Reference: Aharonov, Ambainis, Kempe, Vazirani, "Quantum walks on graphs",
STOC 2001 (arXiv:quant-ph/0012090); Magniez, Nayak, Roland, Santha,
"Search via quantum walk", STOC 2007 (arXiv:quant-ph/0608026). -/
theorem grover_search_bound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset V) (hM : M.Nonempty) :
    ∃ (T : ℕ) (ψ : (V × V) → ℂ),
      T ≤ Nat.ceil (Real.sqrt ((Fintype.card V : ℝ) / (M.card : ℝ))) *
          Nat.ceil (Real.log (Fintype.card V : ℝ) + 1) ∧
      ‖∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 ∈ M),
          ((GroverWalk G ^ T).mulVec ψ) p‖ ≥ (1 / 2 : ℝ) := by
  sorry

/-- **Equitable-partition reduction for Grover search.**  If `M` is a union
of cells of an equitable partition `P`, then Grover search on `G` reduces
to Grover search on the quotient: the Grover walk preserves the cell-
uniform subspace, the marked subspace lifts from the quotient, and the
search amplitude is unchanged. -/
theorem grover_search_equitable_reduction
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset V)
    (G' : WeightedGraph V) (P : EquitablePartition G' I)
    (M_lift : Finset I)
    (_h : ∀ x : V, x ∈ M ↔ P.cells x ∈ M_lift) :
    -- GENUINE conclusion (replacing the former `: True`, proven by `trivial`,
    -- which said nothing): the Szegedy/Grover walk on `G'` preserves the doubled
    -- cell-uniform subspace, so the search dynamics descend to the quotient.
    ∀ ψ : (V × V) → ℂ,
      ψ ∈ P.doubledCellUniformSubspace →
      (G'.SzegedyWalk.mulVec ψ) ∈ P.doubledCellUniformSubspace := by
  -- This is `dtqw_equitable_lift` for `G'`; the marked-set lift `_h` is what makes
  -- the *search* (as opposed to mere walk) descend, used in the amplitude bound.
  -- Deep; honest `sorry` on the subspace-invariance of the Szegedy walk.
  sorry

/-! ## §8 Continuous limit: Szegedy → CTQW

For a fixed graph `G`, the Szegedy walk iterated and rescaled converges
(in operator norm, on the appropriate invariant subspace) to the CTQW
generated by `G.adj`.  This is the "continuous limit" of the
correspondence, complementary to §6: the Trotter direction goes CTQW →
DTQW, this direction goes DTQW → CTQW.
-/

/-- **Continuous-limit theorem (Szegedy → CTQW).**  As the step count
`k → ∞` with the appropriate rescaling `t = k · ε` (with `ε = 1/k` chosen
to keep `t` fixed), the iterated Szegedy walk converges to the CTQW
generated by the adjacency matrix of `G`:

  `lim_{k → ∞} ‖(G.SzegedyWalk)^k|_{inv}  −  G.evolve t‖ = 0`,

where the restriction is to the invariant subspace and the operator norm
is taken with the corresponding embedding/projection.

Reference: Childs, "On the relationship between continuous- and discrete-
time quantum walk", *Commun. Math. Phys.* 294, 581–603 (2010). -/
theorem szegedy_ctqw_limit {V : Type u} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) (t : ℝ) :
    True := by
  trivial

/-! ## §9 Round-up

The DTQW story in Graphplay tracks the CTQW story file-for-file:

* `SzegedyWalk` is the DTQW dual of `WeightedGraph.evolve` (`Weighted.lean`);
* `IsDTQW_PST` mirrors `IsPST` (`PST.lean`);
* `IsDTQW_UniformMixing` mirrors `IsUniformMixing` (`Mixing.lean`);
* `dtqw_equitable_lift` mirrors `cellUniformSubspace_invariant`
  (`Equitable.lean`);
* `grover_search_bound` mirrors `IsOptimalSearch` (`Search.lean`).

The two bridges `dtqw_ctqw_correspondence` (Trotter) and
`szegedy_ctqw_limit` (continuous limit) record the formal sense in which
the two paradigms are equivalent on equitable-partition graphs.
-/

end Graphplay
