/-
Graphplay/QuantumCSP.lean

Tower 3.5: **Quantum CSP / non-local game semantics**.

This file sits between `Graphplay.QuantumGraph` (operator-system quantum
graphs) and `Graphplay.Dowsing.NonCommutativeCoherent`
(Mancinska-Roberson quantum homomorphisms).  Its purpose is to expose
the *non-local-game* / *Tsirelson-correlation* face of quantum graph
parameters: this is the bridge by which the Tower-3 numerics
(`quantumChromaticNumber`, `lovaszTheta`) connect to
quantum-information-theoretic complexity (MIP* = RE,
Connes-embedding, etc.).

The headline references are:

* Mancinska-Roberson, "Quantum homomorphisms" (arXiv:1212.1724) — χ_q
  via the (V,k)-coloring game.
* Cubitt-Mancinska-Roberson-Severini-Stahlke-Winter,
  arXiv:1311.6850 — the operator-system formulation.
* Ji-Natarajan-Vidick-Wright-Yuen, "MIP* = RE" (arXiv:2001.04383) —
  separation of `QuantumValue` and `CommutingOperatorValue`.
* Tsirelson, "Quantum generalizations of Bell's inequality" (1980) —
  the `2√2` bound on CHSH.

Every nontrivial claim is `sorry`; this scaffold lays out the *shape*
of the loop closure between non-local-game value and the χ_q chain.

Canonical types: `RelStructure` (Relational.lean), `QuantumGraph`
(QuantumGraph.lean), `quantumChromaticNumber` (Relational.lean).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Graphplay.QuantumGraph
import Graphplay.Relational

universe u v w

namespace Graphplay

/-! ## 1. Non-local games as a structure

A two-player one-round non-local game is parametrized by

* a *question set* `V` (we use the vertex set of an underlying graph),
* an *answer set* `O`,
* a *verifier predicate* `verifier : V × V → O × O → Bool` that decides
  whether the pair of answers is winning for the pair of questions.

In the *uniform-question* model the referee samples `(v, w)` uniformly
from `V × V`; the players, who cannot communicate, return `a, b : O`
respectively, and win iff `verifier (v, w) (a, b) = true`.

(One can refine to a non-uniform `prob : V × V → ℝ≥0` distribution;
for the χ_q application the uniform distribution is what is used in
Mancinska-Roberson.)
-/

/-- A 2-player non-local game with question alphabet `V` and answer
alphabet `O`, defined by a Boolean verifier.  The implicit referee
distribution is uniform on `V × V`. -/
structure NonLocalGame (V O : Type*) [Fintype V] [Fintype O] where
  /-- Winning predicate: `true` iff the answer pair `(a, b)` is
  accepted for the question pair `(v, w)`. -/
  verifier : V × V → O × O → Bool

namespace NonLocalGame

variable {V O : Type*} [Fintype V] [Fintype O]

/-! ### Classical (deterministic / random) strategies -/

/-- A *deterministic* classical strategy: each player has a function
`V → O`.  Since the game is symmetric in the two players we record a
single function (the symmetric strategies are the optimal ones for the
graph-coloring game, but we allow asymmetric strategies via a pair). -/
structure ClassicalStrategy (V O : Type*) where
  alice : V → O
  bob   : V → O

/-- The winning probability of a classical (deterministic) strategy
under the uniform question distribution. -/
noncomputable def classicalWin (G : NonLocalGame V O)
    (σ : ClassicalStrategy V O) : ℝ :=
  -- (1 / |V|²) · #{ (v, w) : verifier (v, w) (σ.alice v, σ.bob w) }
  ((Finset.univ.filter (fun p : V × V =>
      G.verifier p (σ.alice p.1, σ.bob p.2))).card : ℝ)
    / ((Fintype.card V : ℝ) * (Fintype.card V : ℝ))

/-- The **classical value** of a non-local game: the supremum of the
winning probability over (deterministic) classical strategies.  By a
standard convexity argument this equals the supremum over shared-random
strategies. -/
noncomputable def ClassicalValue (G : NonLocalGame V O) : ℝ :=
  ⨆ σ : ClassicalStrategy V O, classicalWin G σ

/-! ### Tsirelson / tensor-product quantum strategies

A *Tsirelson-quantum strategy* (a.k.a. a `q`-correlation) consists of:

* a finite-dimensional Hilbert space `H_A ⊗ H_B`,
* a shared state `|ψ⟩ ∈ H_A ⊗ H_B`,
* for each question `v : V` and each player, a POVM `{E_v^a}_{a:O}` on
  the player's local Hilbert space,
* the produced correlation is
  `p(a, b | v, w) = ⟨ψ| E_v^a ⊗ F_w^b |ψ⟩`.

We model the local Hilbert spaces as `Fin n_A` / `Fin n_B`-indexed and
package the POVM as a function `V → O → Matrix _ _ ℂ`.
-/

/-- A POVM on `Fin n`: a family of Hermitian PSD matrices summing to
`1`.  We require Hermiticity explicitly; positivity / completeness are
left as predicates one can extend.  -/
structure POVM (n : ℕ) (O : Type*) [Fintype O] where
  effect : O → Matrix (Fin n) (Fin n) ℂ
  herm : ∀ a, (effect a).IsHermitian
  -- positivity left informal at this scaffold layer
  posSemidef_witness : ∀ _a : O, True
  sum_eq_one : ∑ a, effect a = 1

/-- A Tsirelson-quantum (a.k.a. `q`-correlation) strategy: shared state
on `Fin n_A ⊗ Fin n_B`, local POVMs indexed by `V` for each player.

The two Hilbert spaces are independent; the `state` lives on the
tensor product `Fin (n_A * n_B)`.  We avoid Mathlib's full tensor
machinery here and just use the lex-pairing `Fin (n_A * n_B) ≃ Fin n_A
× Fin n_B`. -/
structure QuantumStrategy (V O : Type*) [Fintype V] [Fintype O] where
  nA : ℕ
  nB : ℕ
  /-- Shared state as a unit vector in `ℂ^{n_A * n_B}`. -/
  state : Fin (nA * nB) → ℂ
  state_unit : ∑ i, ‖state i‖ ^ 2 = 1
  alicePOVM : V → POVM nA O
  bobPOVM   : V → POVM nB O

/-- The Tsirelson correlation produced by a quantum strategy.  This is
the standard `⟨ψ| E_v^a ⊗ F_w^b |ψ⟩` quantity, expressed in matrix
elements through the lex isomorphism.  Stated; proof is omitted. -/
noncomputable def QuantumStrategy.correlation
    (S : QuantumStrategy V O) (v w : V) (a b : O) : ℝ :=
  -- Reᴿ ⟨ψ| (E_v^a ⊗ F_w^b) |ψ⟩, where the tensor is on the
  -- `Fin (nA * nB) ≃ Fin nA × Fin nB` identification.
  -- Placeholder: the operator-norm of a single block; refined later.
  0

/-- The winning probability of a Tsirelson-quantum strategy. -/
noncomputable def quantumWin (G : NonLocalGame V O) (S : QuantumStrategy V O) :
    ℝ :=
  (1 / ((Fintype.card V : ℝ) ^ 2)) *
    ∑ p : V × V, ∑ q : O × O,
      if G.verifier p q then S.correlation p.1 p.2 q.1 q.2 else 0

/-- The **quantum value** (Tsirelson, tensor-product) of a non-local
game.  This is the value `ω^*` of MIP* fame.  The supremum is over
finite-dimensional strategies; whether the supremum is attained is
itself a deep question (it isn't, in general — see Slofstra,
arXiv:1606.03140). -/
noncomputable def QuantumValue (G : NonLocalGame V O) : ℝ :=
  ⨆ S : QuantumStrategy V O, quantumWin G S

/-! ### Commuting-operator value

A *commuting-operator strategy* uses a single Hilbert space and POVMs
`{E_v^a}, {F_w^b}` that *commute pairwise* (rather than acting on a
tensor product).  The associated value `ω^{co}` satisfies
`ω^* ≤ ω^{co}`, and equality of the two is equivalent to the
Connes embedding conjecture (which is **false**, by MIP* = RE; Ji,
Natarajan, Vidick, Wright, Yuen, arXiv:2001.04383).
-/

/-- A commuting-operator strategy: single Hilbert space of dimension
`n`, shared state, POVMs for both players whose effects pairwise
commute.  -/
structure CommutingOperatorStrategy (V O : Type*) [Fintype V] [Fintype O] where
  n : ℕ
  state : Fin n → ℂ
  state_unit : ∑ i, ‖state i‖ ^ 2 = 1
  alicePOVM : V → POVM n O
  bobPOVM   : V → POVM n O
  commute : ∀ v w a b,
    (alicePOVM v).effect a * (bobPOVM w).effect b
      = (bobPOVM w).effect b * (alicePOVM v).effect a

/-- The correlation produced by a commuting-operator strategy. -/
noncomputable def CommutingOperatorStrategy.correlation
    (S : CommutingOperatorStrategy V O) (v w : V) (a b : O) : ℝ :=
  0

/-- The winning probability of a commuting-operator strategy. -/
noncomputable def commutingWin (G : NonLocalGame V O)
    (S : CommutingOperatorStrategy V O) : ℝ :=
  (1 / ((Fintype.card V : ℝ) ^ 2)) *
    ∑ p : V × V, ∑ q : O × O,
      if G.verifier p q then S.correlation p.1 p.2 q.1 q.2 else 0

/-- The **commuting-operator value** `ω^{co}` of a non-local game. -/
noncomputable def CommutingOperatorValue (G : NonLocalGame V O) : ℝ :=
  ⨆ S : CommutingOperatorStrategy V O, commutingWin G S

/-- Classical strategies are quantum strategies (set `n_A = n_B = 1`,
state `= 1`, deterministic POVMs).  Hence `ω ≤ ω^*`.  -/
theorem ClassicalValue_le_QuantumValue (G : NonLocalGame V O) :
    ClassicalValue G ≤ QuantumValue G := by
  -- Embed a `ClassicalStrategy` as a 1-dimensional quantum strategy and
  -- bound the sup.
  sorry

/-- Every finite-dim Tsirelson-quantum strategy is also a commuting-op
strategy (use `H_A ⊗ H_B` as the single Hilbert space, lift the local
POVMs).  Hence `ω^* ≤ ω^{co}`.  -/
theorem QuantumValue_le_CommutingOperatorValue (G : NonLocalGame V O) :
    QuantumValue G ≤ CommutingOperatorValue G := by
  -- Each tensor-product strategy lifts to a commuting-operator strategy
  -- by `E_v^a ↦ E_v^a ⊗ I`, `F_w^b ↦ I ⊗ F_w^b`.  These commute.
  sorry

/-- **MIP* = RE separation (informal).**  There exists a non-local game
`G` such that `QuantumValue G < CommutingOperatorValue G`.  This is
the Ji-Natarajan-Vidick-Wright-Yuen 2020 theorem (arXiv:2001.04383);
equivalently, the Connes embedding conjecture is false.

We state existence as a scaffolded claim; the witness game is the
"compression-of-MIP* protocols" game of JNVWY §3, which lies far
outside this scaffold's scope. -/
theorem exists_quantum_lt_commuting :
    ∃ (V O : Type) (_ : Fintype V) (_ : Fintype O) (G : NonLocalGame V O),
      QuantumValue G < CommutingOperatorValue G := by
  sorry

end NonLocalGame

/-! ## 2. The graph-coloring non-local game

Mancinska-Roberson (arXiv:1212.1724) introduce, for a graph `G = (V, E)`
and a number of colors `k`, the **`(G, k)`-coloring game**:

* Referee sends Alice `v ∈ V`, Bob `w ∈ V` (uniformly).
* Each player outputs a color in `Fin k`.
* Win condition:
    - If `v = w`, the players must output the **same** color.
    - If `v ~ w` (adjacent in `G`), the players must output **different**
      colors.
    - Otherwise (`v ≠ w` and not adjacent), the players win automatically.

The classical value of this game is `1` iff `χ(G) ≤ k`; the quantum
value is `1` iff `χ_q(G) ≤ k`.
-/

open NonLocalGame

/-- The Mancinska-Roberson `(G, k)`-coloring game.  -/
def GraphColoringGame {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    NonLocalGame V (Fin k) where
  verifier := fun (v, w) (a, b) =>
    if v = w then decide (a = b)
    else if G.Adj v w then decide (a ≠ b)
    else true

/-- **Classical coloring game value = 1 iff χ(G) ≤ k.**  (Mancinska-
Roberson Prop 2.)  -/
theorem GraphColoringGame.classical_value_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ClassicalValue (GraphColoringGame G k) = 1
      ↔ ∃ c : G.Coloring (Fin k), True := by
  -- Forward: a perfect classical strategy with `alice = bob` is a proper
  -- coloring, since `v ≠ w` adjacent forces `c v ≠ c w` and `v = w`
  -- forces consistency.  Backward: any proper coloring `c` yields the
  -- strategy `alice = bob = c`.
  sorry

/-! ## 3. Quantum value and the quantum chromatic number

This is the **headline statement** of Mancinska-Roberson 1212.1724: the
quantum chromatic number of `G` is the least `k` for which Alice and
Bob have a *perfect* Tsirelson strategy in the coloring game.

Below we use the canonical `quantumChromaticNumber` from
`Graphplay.Relational` (which is currently a placeholder, but matches
the signature for the binary-relation case).
-/

/-- Embed a `SimpleGraph` as a `RelStructure` over the binary
signature so we can use the canonical `quantumChromaticNumber`.  This is
exactly the `RelStructure.ofSimpleGraph` embedding of `Graphplay.Relational`:
the single binary relation is `G.Adj (f 0) (f 1)`. -/
def _root_.SimpleGraph.toRelStructure
    {V : Type*} (G : SimpleGraph V) : RelStructure Signature.graph V :=
  RelStructure.ofSimpleGraph G

/-- **Mancinska-Roberson characterization of `χ_q`** (arXiv:1212.1724,
Theorem 1).  For a finite simple graph `G` and `k : ℕ`,

    χ_q(G) ≤ k  ↔  ω^*(GraphColoringGame G k) = 1.

This is the loop-closing statement: it links the
operator-system / Tower-3 chromatic invariant
(`quantumChromaticNumber`) to a *correlation-theoretic* / Tsirelson
quantity.  -/
theorem quantumChromaticNumber_via_game
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    CSP.quantumChromaticNumber G.toRelStructure ≤ k
      ↔ QuantumValue (GraphColoringGame G k) = 1 := by
  -- Mancinska-Roberson §3: a perfect Tsirelson strategy
  -- `{E_v^a}, {F_w^b}` for the (G,k)-coloring game is the same data as a
  -- projective representation of the *quantum graph homomorphism algebra*
  -- `Hom_q(G, K_k)`, which in turn is what `quantumChromaticNumber`
  -- numerically captures.
  sorry

/-- **Commuting-operator chromatic number.**  Define `χ_qc(G)` as the
least `k` with `CommutingOperatorValue (GraphColoringGame G k) = 1`.
By construction `χ_q(G) ≥ χ_qc(G)`, and the gap is governed by the
Connes embedding conjecture (false, by MIP* = RE). -/
noncomputable def commutingOperatorChromaticNumber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  -- Nat.find over `k` such that `CommutingOperatorValue (GraphColoringGame G k) = 1`
  0

/-- `χ_qc ≤ χ_q` (the values move oppositely to the inclusions of
strategy classes).  -/
theorem commutingOperatorChromatic_le_quantumChromatic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    commutingOperatorChromaticNumber G ≤ CSP.quantumChromaticNumber G.toRelStructure := by
  sorry

/-! ## 4. Quantum equitable partitions induce quantum strategies

The point of Tower 3.5: a *quantum equitable partition* (D5,
`NonCommutativeCoherent.lean`) of `G` produces a non-classical
Tsirelson strategy for the `(G, k)`-coloring game whenever the cells'
projector system supports a `k`-coloring of the *quotient* but **not**
of `G` itself.  This is the loop closure with L6 (the "phantom
symmetry → quantum coloring" speculation).
-/

/-- A *phantom symmetry witness* on `G`: data of an operator-system
homomorphism `M_{|V|}(ℂ) → M_k(ℂ)` lifting a classical
`k`-coloring of a quotient that does *not* lift to a classical
`k`-coloring of `G`.

(We do not formalize `QuantumEquitablePartition` here — that's
`NonCommutativeCoherent.lean`; we package what we need.) -/
structure PhantomSymmetry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) where
  /-- Witness operator-system map (sketch). -/
  data : Unit
  /-- The quotient admits a classical `k`-coloring. -/
  quotient_classical : True
  /-- `G` itself does *not* admit a classical `k`-coloring (so we're
  in the genuinely-quantum regime). -/
  no_classical_coloring : ¬ ∃ c : G.Coloring (Fin k), True

/-- **Phantom symmetry → quantum strategy.**  A `PhantomSymmetry G k`
witness produces a perfect Tsirelson-quantum strategy for the
`(G, k)`-coloring game, witnessing `χ_q(G) ≤ k < χ(G)`.

This is the *quantum advantage* phenomenon — the original example is
the orthogonality graph on `ℝ^4`, where `χ_q = 4 < χ = 5`
(Mancinska-Roberson §5, building on Cubitt-Mancinska-Roberson-Severini-
Stahlke-Winter).  -/
theorem phantomSymmetry_to_quantumStrategy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (_ : PhantomSymmetry G k) :
    QuantumValue (GraphColoringGame G k) = 1
      ∧ ClassicalValue (GraphColoringGame G k) < 1 := by
  sorry

/-! ## 5. The CHSH game as a sanity check

CHSH is the canonical Tsirelson example: two-question, two-output, with
the XOR-style verifier.  We package it as a non-local game on the
2-vertex set `Fin 2` (or rather on an "input" set of size 2, with the
graph being `K_2` together with two extra "input bits" — the actual
encoding into `NonLocalGame Fin 2 Fin 2` is the obvious one).

Tsirelson's bound:  `ω^*(CHSH) = (2 + √2) / 4 = cos²(π/8)`, whereas
`ω(CHSH) = 3/4`.  In the un-normalized "CHSH-correlator" form the
quantum bound is the more familiar `2√2`.
-/

/-- The CHSH non-local game.  Questions `x, y ∈ {0, 1}`, answers
`a, b ∈ {0, 1}`, win condition `a XOR b = x AND y`. -/
def CHSHGame : NonLocalGame (Fin 2) (Fin 2) where
  verifier := fun (x, y) (a, b) =>
    -- XOR of answers = AND of questions
    decide ((a.val + b.val) % 2 = (x.val * y.val) % 2)

/-- **CHSH classical bound.**  `ω(CHSH) = 3/4`.  -/
theorem CHSH_classical_value : ClassicalValue CHSHGame = 3 / 4 := by
  -- Brute force over the 16 deterministic strategies.
  sorry

/-- **Tsirelson's bound.**  `ω^*(CHSH) = (2 + √2) / 4 = cos²(π/8)`.

This is the win-probability form of Tsirelson's `2√2` bound on the
CHSH correlator (Tsirelson, "Quantum generalizations of Bell's
inequality", Lett. Math. Phys. 4 (1980), 93-100).  -/
theorem CHSH_quantum_value :
    QuantumValue CHSHGame = (2 + Real.sqrt 2) / 4 := by
  -- Optimal strategy: shared singlet, measurements at angles
  -- 0, π/4 for Alice and π/8, 3π/8 for Bob.  Matches the
  -- Tsirelson SDP bound; tight by Tsirelson 1980.
  sorry

/-- **Tsirelson bound on the CHSH correlator.**  In the
`±1`-correlator normalization `⟨A_xB_y⟩ ∈ [-1, 1]`, the CHSH expression
`⟨A_0B_0⟩ + ⟨A_0B_1⟩ + ⟨A_1B_0⟩ - ⟨A_1B_1⟩` is bounded by `2√2` over
all quantum strategies. -/
theorem CHSH_correlator_bound :
    ∀ S : QuantumStrategy (Fin 2) (Fin 2),
      |((1 : ℝ) - 2 * quantumWin CHSHGame S) * 8 + 4| ≤ 2 * Real.sqrt 2 + 2 := by
  -- The CHSH correlator and the win-probability are related by an
  -- affine map; the |·| ≤ 2√2 + ε form follows from the win-bound.
  sorry

/-! ## 6. Operator-system / coherent-algebra dictionary

The Tsirelson value of a non-local game is the value of an *operator-
system homomorphism* from the *game algebra* into `M_n(ℂ)` — this is
the Cleve-Liu-Slofstra / Mancinska-Roberson "synchronous strategy"
picture (arXiv:1606.02278, 1903.11491).

We make the bridge to `QuantumHom` (in
`NonCommutativeCoherent.lean`) explicit at the statement level.
-/

/-- The *game *-algebra* of a non-local game: an abstract algebra
generated by symbols `e_v^a` (Alice) and `f_w^b` (Bob) subject to:

* `(e_v^a)² = e_v^a = (e_v^a)*` (each is a projector),
* `∑_a e_v^a = 1` for every `v`, similarly for `f`,
* `e_v^a · f_w^b = 0` whenever `verifier (v, w) (a, b) = false`.

Its representations in `M_n(ℂ)` are exactly the perfect synchronous
quantum strategies.

We state the existence of this algebra as a scaffolded structure;
defining the universal *-algebra requires more `Mathlib.Algebra.Star`
machinery than we set up here. -/
structure GameAlgebra (V O : Type*) [Fintype V] [Fintype O]
    (G : NonLocalGame V O) where
  /-- Underlying carrier; left abstract. -/
  Carrier : Type
  /-- Star-algebra structure; left abstract. -/
  algebraic_structure : Unit

/-- **Synchronous strategies = ∗-representations of the game algebra**
(Paulsen-Severini-Stahlke-Todorov-Winter, arXiv:1407.6918, Thm 3.6).
A perfect synchronous quantum strategy for `G` exists iff there exists
a finite-dimensional tracial ∗-representation of `GameAlgebra G`. -/
theorem QuantumValue_eq_gameAlgebra_rep
    {V O : Type*} [Fintype V] [Fintype O] (G : NonLocalGame V O) :
    (QuantumValue G = 1)
      ↔ ∃ (A : GameAlgebra V O G), True := by
  sorry

/-- **Coloring game algebra = quantum-homomorphism operator system.**
The game algebra of `GraphColoringGame G k` is the same data as the
quantum-homomorphism operator system from `G`'s adjacency operator
system into the operator system `quantumKn k` of the complete quantum
graph on `k` colors (the `QuantumHom` of
`NonCommutativeCoherent.lean`).

This is the loop closure with D5: a non-local-game perfect strategy is
the same datum as a `QuantumHom`. -/
theorem coloringGameAlgebra_eq_quantumHom
    {V : Type*} [Fintype V] [DecidableEq V]
    (_G : SimpleGraph V) [DecidableRel _G.Adj] (_k : ℕ) :
    True := by
  -- Statement-only at this scaffold level; the actual equivalence is
  -- Mancinska-Roberson §4.
  trivial

/-! ## 7. Connections back to the χ_q chain

The Lovász ϑ ≤ ϑ_q ≤ χ_q ≤ χ chain of `Graphplay.Relational` lifts
naturally to *non-local game values*:

* `ω(GraphColoringGame G k) = 1`     ↔  `χ(G) ≤ k`.
* `ω^*(GraphColoringGame G k) = 1`   ↔  `χ_q(G) ≤ k`.
* `ω^{co}(GraphColoringGame G k) = 1`↔  `χ_{qc}(G) ≤ k`.
* `ϑ_q` (the quantum Lovász theta) lower-bounds `χ_q` and upper-bounds
  the independence variant `α_q`.
-/

/-- **Chromatic chain via game values.**  For finite simple `G`,

  `χ_qc(G) ≤ χ_q(G) ≤ χ(G)`,

with strict inequality possible for the first comparison (Slofstra
arXiv:1703.08618) and the second (Mancinska-Roberson §5, the
orthogonality-graph example).  -/
theorem chromatic_chain_via_games
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    commutingOperatorChromaticNumber G
        ≤ CSP.quantumChromaticNumber G.toRelStructure
      ∧ CSP.quantumChromaticNumber G.toRelStructure ≤ CSP.chromaticNumber G.toRelStructure := by
  sorry

/-! ## 8. Open problems and conjectures -/

/-- **Open (graphon-quantum-CSP).**  Does the chain
`ϑ ≤ ϑ_q ≤ χ_q ≤ χ` extend to graphons (continuous limits)?

A graphon `W : [0,1]² → [0,1]` has a well-defined `ϑ` (Lovász) by a
continuous SDP, and `χ_q` makes sense via the *graphon operator
system* (Tower 4 / `Graphplay.Graphon`).  We conjecture all three
intermediate quantities are well-defined and continuous in the cut
norm, and that the chain holds graphon-wise.

This connects to L9 ("continuous-spectrum / graphon spectrum lifting")
in `Graphplay.Graphon`: the continuous spectrum should govern `ϑ` for
graphons just as the discrete spectrum does for graphs (Hoffman /
Lovász-θ).  -/
theorem graphon_quantum_csp_open :
    -- Placeholder for the conjecture (no claim, just registration).
    True := by
  trivial

/-- **Open (Tsirelson uniformity).**  Does the supremum in
`QuantumValue` admit a uniform bound on the local dimension `n_A, n_B`
in terms of `|V|` and `|O|`?

Slofstra (arXiv:1606.03140) showed the supremum is *not always*
attained; whether dimension can be bounded for the *coloring* games in
particular is open (Mancinska-Roberson §6, "dimension witnesses"). -/
theorem tsirelson_dimension_witness_open :
    True := by
  trivial

/-- **Open (synchronous Tsirelson).**  Is the synchronous quantum value
`ω^s` (Tsirelson strategies with `E_v^a = F_v^a` and a maximally
entangled state) equal to the general quantum value for the
`GraphColoringGame`?

Paulsen-Severini-Stahlke-Todorov-Winter arXiv:1407.6918 showed that
`ω^s = ω^*` for the coloring game iff `χ_q` is realized by a
synchronous strategy; the converse and the general case remain open. -/
theorem synchronous_tsirelson_open :
    True := by
  trivial

end Graphplay
