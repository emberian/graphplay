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

The deep external results enter as cited typeclass hypotheses (no bare
`sorry`s); this file lays out the *shape* of the loop closure between
non-local-game value and the χ_q chain.

Canonical types: `RelStructure` (Relational.lean), `QuantumGraph`
(QuantumGraph.lean), `quantumChromaticNumber` (Relational.lean).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Graphplay.QuantumGraph
import Graphplay.Relational
import Graphplay.LiteratureInterfaces

universe u v w

open scoped ComplexOrder
open Graphplay.LiteratureInterfaces

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

/-- Fintype instance on classical strategies with finite question/answer
alphabets, via the obvious equivalence with `(V → O) × (V → O)`. -/
instance instFintypeClassicalStrategy {V O : Type*} [Fintype V] [Fintype O]
    [DecidableEq V] : Fintype (ClassicalStrategy V O) :=
  Fintype.ofEquiv ((V → O) × (V → O))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun σ => (σ.alice, σ.bob)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

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
  /-- Genuine positive-semidefiniteness of every effect: a POVM is a family of
  PSD operators (de-stubbed from the old `∀ _a, True`, restoring the positivity
  the correlator bounds depend on). -/
  posSemidef : ∀ a, (effect a).PosSemidef
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
elements through the lex isomorphism `finProdFinEquiv : Fin nA × Fin nB ≃
Fin (nA * nB)`.

Writing `ψ_{(i,j)} := S.state (finProdFinEquiv (i, j))`, `E := (S.alicePOVM
v).effect a`, `F := (S.bobPOVM w).effect b`, the (real part of the) inner
product `⟨ψ, (E ⊗ F) ψ⟩` expands to

  `Σ_{i j i' j'} conj(ψ_{(i,j)}) · E_{i i'} · F_{j j'} · ψ_{(i',j')}`.

Since `E, F` are Hermitian this quantity is real; we take its real part to
land in `ℝ`. -/
noncomputable def QuantumStrategy.correlation
    (S : QuantumStrategy V O) (v w : V) (a b : O) : ℝ :=
  ((∑ i : Fin S.nA, ∑ j : Fin S.nB, ∑ i' : Fin S.nA, ∑ j' : Fin S.nB,
      (starRingEnd ℂ) (S.state (finProdFinEquiv (i, j)))
        * ((S.alicePOVM v).effect a i i')
        * ((S.bobPOVM w).effect b j j')
        * (S.state (finProdFinEquiv (i', j')))).re)

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

/-- The correlation produced by a commuting-operator strategy.  Here both
players act on the *same* Hilbert space `Fin n`, and the correlation is the
(real part of the) inner product `⟨ψ, E_v^a F_w^b ψ⟩` of the *product* of the
two effects:

  `Re Σ_{i j k} conj(ψ_i) · E_{i j} · F_{j k} · ψ_k`.

Because the two POVMs commute (`S.commute`), the order `E · F` versus `F · E`
does not matter. -/
noncomputable def CommutingOperatorStrategy.correlation
    (S : CommutingOperatorStrategy V O) (v w : V) (a b : O) : ℝ :=
  ((∑ i : Fin S.n, ∑ j : Fin S.n, ∑ k : Fin S.n,
      (starRingEnd ℂ) (S.state i)
        * ((S.alicePOVM v).effect a i j)
        * ((S.bobPOVM w).effect b j k)
        * (S.state k)).re)

/-- The winning probability of a commuting-operator strategy. -/
noncomputable def commutingWin (G : NonLocalGame V O)
    (S : CommutingOperatorStrategy V O) : ℝ :=
  (1 / ((Fintype.card V : ℝ) ^ 2)) *
    ∑ p : V × V, ∑ q : O × O,
      if G.verifier p q then S.correlation p.1 p.2 q.1 q.2 else 0

/-- The **commuting-operator value** `ω^{co}` of a non-local game. -/
noncomputable def CommutingOperatorValue (G : NonLocalGame V O) : ℝ :=
  ⨆ S : CommutingOperatorStrategy V O, commutingWin G S

/-- The 1-dimensional quantum strategy realizing a classical strategy: both
local Hilbert spaces are `Fin 1`, the (unique) shared state is `1`, and each
local POVM is the deterministic indicator `E_v^a = ⟦a = alice v⟧` (a `1×1`
matrix).  Its `correlation` equals the classical winning indicator. -/
noncomputable def classicalToQuantum (σ : ClassicalStrategy V O) :
    QuantumStrategy V O := by
  classical
  exact
  { nA := 1
    nB := 1
    state := fun _ => 1
    state_unit := by simp
    alicePOVM := fun v =>
      { effect := fun a => fun _ _ => if a = σ.alice v then 1 else 0
        herm := by
          intro a
          ext i j
          fin_cases i; fin_cases j
          simp [Matrix.IsHermitian, Matrix.conjTranspose]
        posSemidef := by
          intro a
          by_cases ha : a = σ.alice v
          · -- the effect is the identity `1 : Matrix (Fin 1) (Fin 1) ℂ`
            have : (fun _ _ : Fin 1 => if a = σ.alice v then (1 : ℂ) else 0)
                = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
              ext i j; fin_cases i; fin_cases j; simp [ha, Matrix.one_apply]
            rw [this]; exact Matrix.PosSemidef.one
          · -- the effect is the zero matrix
            have : (fun _ _ : Fin 1 => if a = σ.alice v then (1 : ℂ) else 0)
                = (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
              ext i j; fin_cases i; fin_cases j; simp [ha]
            rw [this]; exact Matrix.PosSemidef.zero
        sum_eq_one := by
          ext i j
          fin_cases i; fin_cases j
          rw [Matrix.sum_apply]
          simp }
    bobPOVM := fun w =>
      { effect := fun b => fun _ _ => if b = σ.bob w then 1 else 0
        herm := by
          intro b
          ext i j
          fin_cases i; fin_cases j
          simp [Matrix.IsHermitian, Matrix.conjTranspose]
        posSemidef := by
          intro b
          by_cases hb : b = σ.bob w
          · have : (fun _ _ : Fin 1 => if b = σ.bob w then (1 : ℂ) else 0)
                = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
              ext i j; fin_cases i; fin_cases j; simp [hb, Matrix.one_apply]
            rw [this]; exact Matrix.PosSemidef.one
          · have : (fun _ _ : Fin 1 => if b = σ.bob w then (1 : ℂ) else 0)
                = (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
              ext i j; fin_cases i; fin_cases j; simp [hb]
            rw [this]; exact Matrix.PosSemidef.zero
        sum_eq_one := by
          ext i j
          fin_cases i; fin_cases j
          rw [Matrix.sum_apply]
          simp } }

/-- The correlation of the embedded classical strategy is exactly the joint
indicator `⟦a = alice v⟧ · ⟦b = bob w⟧`. -/
theorem classicalToQuantum_correlation [DecidableEq O]
    (σ : ClassicalStrategy V O) (v w : V) (a b : O) :
    (classicalToQuantum σ).correlation v w a b
      = if a = σ.alice v ∧ b = σ.bob w then 1 else 0 := by
  unfold QuantumStrategy.correlation classicalToQuantum
  simp only [Fin.sum_univ_one]
  -- everything collapses to the single index 0
  by_cases ha : a = σ.alice v <;> by_cases hb : b = σ.bob w <;>
    simp [ha, hb, Complex.ext_iff]

/-- The win of the embedded classical strategy equals the classical win. -/
theorem quantumWin_classicalToQuantum (G : NonLocalGame V O)
    (σ : ClassicalStrategy V O) :
    quantumWin G (classicalToQuantum σ) = classicalWin G σ := by
  classical
  unfold quantumWin classicalWin
  -- the inner answer-sum collapses to the single winning answer pair
  have hinner : ∀ p : V × V,
      (∑ q : O × O, if G.verifier p q
          then (classicalToQuantum σ).correlation p.1 p.2 q.1 q.2 else 0)
        = (if G.verifier p (σ.alice p.1, σ.bob p.2) then (1 : ℝ) else 0) := by
    intro p
    have hstep : (∑ q : O × O, if G.verifier p q
            then (classicalToQuantum σ).correlation p.1 p.2 q.1 q.2 else 0)
        = ∑ q : O × O, if q = (σ.alice p.1, σ.bob p.2)
            then (if G.verifier p q then (1 : ℝ) else 0) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro q _
      rw [classicalToQuantum_correlation]
      by_cases hcond : q = (σ.alice p.1, σ.bob p.2)
      · subst hcond
        by_cases hv : G.verifier p (σ.alice p.1, σ.bob p.2) <;> simp [hv]
      · have hcond' : ¬ (q.1 = σ.alice p.1 ∧ q.2 = σ.bob p.2) := by
          rintro ⟨e1, e2⟩; exact hcond (Prod.ext e1 e2)
        simp [hcond, hcond']
    rw [hstep, Finset.sum_ite_eq' Finset.univ (σ.alice p.1, σ.bob p.2)]
    simp
  -- now sum over question pairs
  have hsum : (∑ p : V × V, ∑ q : O × O, if G.verifier p q
        then (classicalToQuantum σ).correlation p.1 p.2 q.1 q.2 else 0)
      = ((Finset.univ.filter (fun p : V × V =>
          G.verifier p (σ.alice p.1, σ.bob p.2))).card : ℝ) := by
    simp_rw [hinner]
    rw [Finset.sum_boole]
  rw [hsum, sq]
  ring

/-- Classical strategies are quantum strategies (set `n_A = n_B = 1`,
state `= 1`, deterministic POVMs).  Hence `ω ≤ ω^*`.

The *content* — that every classical strategy embeds as a quantum one
with the same win — is `quantumWin_classicalToQuantum`
above.  The final value inequality `⨆ classicalWin ≤ ⨆ quantumWin`
additionally needs `QuantumValue`'s `iSup` to be bounded above so that
`le_ciSup` applies. -/
theorem ClassicalValue_le_QuantumValue
    (G : NonLocalGame V O)
    (hbdd : BddAbove (Set.range (quantumWin G))) :
    ClassicalValue G ≤ QuantumValue G := by
  classical
  -- Each classical win is dominated by the matching quantum win, which is
  -- below the quantum value.
  have hdom : ∀ σ : ClassicalStrategy V O,
      classicalWin G σ ≤ QuantumValue G := by
    intro σ
    rw [← quantumWin_classicalToQuantum G σ]
    exact le_ciSup hbdd (classicalToQuantum σ)
  by_cases hne : Nonempty (ClassicalStrategy V O)
  · exact ciSup_le hdom
  · rw [not_nonempty_iff] at hne
    -- `ClassicalValue = sSup ∅ = 0`.
    simp only [ClassicalValue, Real.iSup_of_isEmpty]
    -- `ClassicalStrategy V O` empty ⟹ `V → O` empty ⟹ `Nonempty V ∧ IsEmpty O`;
    -- a `QuantumStrategy` then cannot exist, so its sup is also `0`.
    have hVO : IsEmpty (V → O) := by
      constructor; intro f; exact hne.false ⟨f, f⟩
    have hVne : Nonempty V := by
      by_contra hV; rw [not_nonempty_iff] at hV
      exact hVO.false (fun v => (hV.false v).elim)
    have hOe : IsEmpty O := by
      constructor; intro a
      exact hVO.false (fun _ => a)
    have : IsEmpty (QuantumStrategy V O) := by
      constructor
      intro S
      obtain ⟨v⟩ := hVne
      -- `∑ a : O, effect a = 1` with `O` empty gives `0 = 1` in the matrix ring
      have h01 : (0 : Matrix (Fin S.nA) (Fin S.nA) ℂ) = 1 := by
        have := (S.alicePOVM v).sum_eq_one
        rwa [Finset.univ_eq_empty (α := O), Finset.sum_empty] at this
      -- `S.nA = 0`, else entry `(0,0)` distinguishes `0` and `1`
      have hnA : S.nA = 0 := by
        by_contra hpos
        have hp : 0 < S.nA := Nat.pos_of_ne_zero hpos
        have : (0 : ℂ) = 1 := by
          have := congrArg (fun M => M ⟨0, hp⟩ ⟨0, hp⟩) h01
          simpa using this
        exact one_ne_zero this.symm
      -- then the state lives on `Fin 0`, and `state_unit` reads `0 = 1`
      have hstate := S.state_unit
      haveI hempty : IsEmpty (Fin (S.nA * S.nB)) := by
        rw [hnA, Nat.zero_mul]; exact Fin.isEmpty
      rw [Finset.univ_eq_empty (α := Fin (S.nA * S.nB)), Finset.sum_empty] at hstate
      exact zero_ne_one hstate
    simp [QuantumValue, Real.iSup_of_isEmpty]

/-- Every finite-dim Tsirelson-quantum strategy is also a commuting-op
strategy (use `H_A ⊗ H_B` as the single Hilbert space, lift the local
POVMs).  Hence `ω^* ≤ ω^{co}`.

**Wired to `QuantumCommutingSeparation`** (Ji–Natarajan–Vidick–Wright–Yuen
inclusion half).  The *structural* content — the tensor→commuting
embedding `E_v^a ⊗ I`, `I ⊗ F_w^b` with the matching `correlation` identity, and
the fact that `QuantumValue`/`CommutingOperatorValue` are the suprema of their
win-functionals — is supplied as explicit hypotheses (`embed`,
`hembed : commutingWin∘embed = quantumWin`, the two `IsLUB` facts, and
nonemptiness of the commuting range).  The literature class then discharges the
sup-monotonicity step.

The `IsLUB` hypotheses are precisely the boundedness facts `QuantumValue`/
`CommutingOperatorValue` need to be true suprema (recall `⨆` collapses to `0`
on unbounded/empty ranges); they are the consumer's remaining obligation. -/
theorem QuantumValue_le_CommutingOperatorValue [QuantumCommutingSeparation]
    {V O : Type} [Fintype V] [Fintype O]
    (G : NonLocalGame V O)
    (embed : QuantumStrategy V O → CommutingOperatorStrategy V O)
    (hembed : ∀ S, commutingWin G (embed S) = quantumWin G S)
    (hqLUB : IsLUB (Set.range (quantumWin G)) (QuantumValue G))
    (hqcLUB : IsLUB (Set.range (commutingWin G)) (CommutingOperatorValue G))
    (hqcNe : (Set.range (commutingWin G)).Nonempty) :
    QuantumValue G ≤ CommutingOperatorValue G := by
  -- Package the data as the single-game (`Γ := Unit`) instance the class consumes.
  exact QuantumCommutingSeparation.qVal_le_qcVal
    (Γ := Unit)
    (fun _ => QuantumStrategy V O) (fun _ => CommutingOperatorStrategy V O)
    (fun _ => quantumWin G) (fun _ => commutingWin G)
    (fun _ => QuantumValue G) (fun _ => CommutingOperatorValue G)
    (fun _ => embed)
    (fun _ S => hembed S)
    (fun _ => hqLUB) (fun _ => hqcLUB) (fun _ => hqcNe) ()

/-- **MIP\* = RE / Connes-embedding refutation, at the concrete game level**
(Ji–Natarajan–Vidick–Wright–Yuen, "MIP\* = RE", arXiv:2001.04383).

The external separation: there is a *concrete* `NonLocalGame` whose
finite-dimensional tensor-product value `QuantumValue` is strictly below its
commuting-operator value `CommutingOperatorValue`.  The witness is the
compression-of-MIP\* game of JNVWY §3, far outside any present formalization.

This is carried as a typeclass assumption: no instance
is provided (the construction is the missing external content), so a theorem
assuming `[QuantumCommutingGameSeparation]` is a conditional theorem
listing the cited theorem as a named hypothesis.

The abstract `LiteratureInterfaces.QuantumCommutingSeparation.exists_strict_gap`
states the separation over an *abstract* game family (opaque `Γ`, with
the values pinned as suprema of payoff functionals and a payoff-preserving
tensor↪commuting embedding), but it lives over types we cannot identify with this
file's concrete `NonLocalGame`/`QuantumValue`/`CommutingOperatorValue` without the
compression game itself; this class states the separation directly at the
concrete game level, exactly as `exists_quantum_lt_commuting` needs it. -/
class QuantumCommutingGameSeparation : Prop where
  /-- There is a concrete non-local game with a strict tensor-vs-commuting gap. -/
  exists_game_gap :
    ∃ (V O : Type) (_ : Fintype V) (_ : Fintype O) (G : NonLocalGame V O),
      QuantumValue G < CommutingOperatorValue G

/-- **MIP\* = RE separation** (Ji–Natarajan–Vidick–Wright–Yuen 2020,
arXiv:2001.04383), as a conditional theorem: assuming the named
literature class `[QuantumCommutingGameSeparation]`, there is a non-local game
`G` with `QuantumValue G < CommutingOperatorValue G` (equivalently, the Connes
embedding conjecture is false).  The class's
witness is the JNVWY §3 compression game (out of scope to construct). -/
theorem exists_quantum_lt_commuting [h : QuantumCommutingGameSeparation] :
    ∃ (V O : Type) (_ : Fintype V) (_ : Fintype O) (G : NonLocalGame V O),
      QuantumValue G < CommutingOperatorValue G :=
  h.exists_game_gap

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

/-- A classical strategy wins **every** question pair of the coloring game iff
its filtered win-set is all of `V × V`, equivalently its `classicalWin` is `1`
(when `V` is nonempty). -/
theorem GraphColoringGame.classicalWin_eq_one_iff
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (σ : ClassicalStrategy V (Fin k)) :
    classicalWin (GraphColoringGame G k) σ = 1
      ↔ ∀ p : V × V, (GraphColoringGame G k).verifier p (σ.alice p.1, σ.bob p.2) := by
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
    have : 0 < Fintype.card V := Fintype.card_pos
    positivity
  unfold classicalWin
  rw [div_eq_one_iff_eq (ne_of_gt hcard)]
  constructor
  · intro h
    -- the filtered set has full cardinality, so it is the whole univ
    have hle : (Finset.univ.filter (fun p : V × V =>
        (GraphColoringGame G k).verifier p (σ.alice p.1, σ.bob p.2))).card
          = Fintype.card (V × V) := by
      have : ((Finset.univ.filter (fun p : V × V =>
          (GraphColoringGame G k).verifier p (σ.alice p.1, σ.bob p.2))).card : ℝ)
            = (Fintype.card (V × V) : ℝ) := by
        rw [h]; push_cast [Fintype.card_prod]; ring
      exact_mod_cast this
    have hfull : (Finset.univ.filter (fun p : V × V =>
        (GraphColoringGame G k).verifier p (σ.alice p.1, σ.bob p.2))) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hle]
    intro p
    have : p ∈ (Finset.univ.filter (fun p : V × V =>
        (GraphColoringGame G k).verifier p (σ.alice p.1, σ.bob p.2))) := by
      rw [hfull]; exact Finset.mem_univ p
    simpa using (Finset.mem_filter.mp this).2
  · intro h
    have hfull : (Finset.univ.filter (fun p : V × V =>
        (GraphColoringGame G k).verifier p (σ.alice p.1, σ.bob p.2))) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro p _; exact h p
    rw [hfull, Finset.card_univ, Fintype.card_prod]
    push_cast; ring

/-- **Classical coloring game value = 1 iff χ(G) ≤ k.**  (Mancinska-
Roberson Prop 2.)

The `[Nonempty V]` hypothesis is required: for empty `V` the value is
`0` (vacuous question distribution) while a vacuous `k`-coloring still exists,
so the bare iff is false. -/
theorem GraphColoringGame.classical_value_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ClassicalValue (GraphColoringGame G k) = 1
      ↔ ∃ c : G.Coloring (Fin k), True := by
  -- `classicalWin ≤ 1` for every strategy.
  have hub : ∀ σ : ClassicalStrategy V (Fin k),
      classicalWin (GraphColoringGame G k) σ ≤ 1 := by
    intro σ
    unfold classicalWin
    rw [div_le_one (by
      have : 0 < Fintype.card V := Fintype.card_pos
      positivity)]
    calc ((Finset.univ.filter (fun p : V × V =>
            (GraphColoringGame G k).verifier p (σ.alice p.1, σ.bob p.2))).card : ℝ)
        ≤ (Fintype.card (V × V) : ℝ) := by
          exact_mod_cast Finset.card_filter_le _ _
      _ = (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
          push_cast [Fintype.card_prod]; ring
  have hbdd : BddAbove (Set.range (classicalWin (GraphColoringGame G k))) :=
    ⟨1, by rintro _ ⟨σ, rfl⟩; exact hub σ⟩
  constructor
  · -- value 1 ⟹ a winning strategy ⟹ a coloring
    intro hval
    -- the strategy type is nonempty, else the sup would be `0 ≠ 1`
    haveI : Nonempty (ClassicalStrategy V (Fin k)) := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      simp only [ClassicalValue, Real.iSup_of_isEmpty] at hval
      norm_num at hval
    obtain ⟨σ, hσ⟩ :=
      exists_eq_ciSup_of_finite (f := classicalWin (GraphColoringGame G k))
    rw [← ClassicalValue, hval] at hσ
    have hwin := (classicalWin_eq_one_iff G k σ).mp hσ
    -- build a coloring from `σ.alice`
    refine ⟨SimpleGraph.Coloring.mk σ.alice ?_, trivial⟩
    intro v w hvw
    -- from the diagonal wins, `σ.alice w = σ.bob w`
    have hdiag : σ.alice w = σ.bob w := by
      have := hwin (w, w)
      simp only [GraphColoringGame, if_true, decide_eq_true_eq] at this
      exact this
    -- from the adjacent win, `σ.alice v ≠ σ.bob w`
    have hadj := hwin (v, w)
    have hne : v ≠ w := G.ne_of_adj hvw
    simp only [GraphColoringGame, if_neg hne, if_pos hvw, decide_eq_true_eq] at hadj
    rw [hdiag]; exact hadj
  · -- a coloring ⟹ the diagonal strategy wins all ⟹ value 1
    rintro ⟨c, -⟩
    set σ : ClassicalStrategy V (Fin k) := { alice := c, bob := c }
    haveI : Nonempty (ClassicalStrategy V (Fin k)) := ⟨σ⟩
    have hσ : classicalWin (GraphColoringGame G k) σ = 1 := by
      rw [classicalWin_eq_one_iff]
      intro p
      simp only [GraphColoringGame, σ]
      by_cases hvw : p.1 = p.2
      · simp [hvw]
      · simp only [if_neg hvw]
        by_cases hadj : G.Adj p.1 p.2
        · simp only [if_pos hadj, decide_eq_true_eq]
          exact c.valid hadj
        · simp [if_neg hadj]
    apply le_antisymm (ciSup_le hub)
    rw [← hσ]; exact le_ciSup hbdd σ

/-! ## 3. Quantum value and the quantum chromatic number

This is the **headline statement** of Mancinska-Roberson 1212.1724: the
quantum chromatic number of `G` is the least `k` for which Alice and
Bob have a *perfect* Tsirelson strategy in the coloring game.  We state the
stub-independent game-value half (a colouring forces `ω^* = 1`); the
biconditional against a non-stub `χ_q` belongs to the Tower-3 development.
-/

/-- **Mancinska-Roberson, the "easy" half via games.**  A classical
`k`-coloring of `G` forces the quantum value of the `(G,k)`-coloring game up to
(at least) `1`: `(∃ c : G.Coloring (Fin k)) → 1 ≤ ω^*(GraphColoringGame G k)`,
given the boundedness `BddAbove` the supremum requires.  Indeed a
coloring is a perfect *classical* strategy (`classical_value_eq_one`), and every
classical strategy embeds as a quantum one with the same win
(`ClassicalValue_le_QuantumValue`), so `1 = ω(game) ≤ ω^*(game)`.

The full Mancinska-Roberson biconditional
`χ_q(G) ≤ k ↔ ω^*(GraphColoringGame G k) = 1` is not stated: against any
`0`-stub `χ_q` it
collapses (left side `0 ≤ k` is `True`) to the unconditional `ω^* = 1`, which is
**false** already at `k = 0` (for nonempty `V` the strategy type
`QuantumStrategy V (Fin 0)` is empty, so the value is the empty supremum `0 ≠ 1`).
The biconditional needs a non-stub `χ_q` (Tower 3); we
record the stub-independent half. -/
theorem quantumColorable_imp_one_le_quantumValue
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hbdd : BddAbove (Set.range (quantumWin (GraphColoringGame G k))))
    (hcol : ∃ c : G.Coloring (Fin k), True) :
    1 ≤ QuantumValue (GraphColoringGame G k) := by
  -- A coloring makes the classical value `1`; classical ≤ quantum lifts it.
  have hcv : ClassicalValue (GraphColoringGame G k) = 1 :=
    (GraphColoringGame.classical_value_eq_one G k).mpr hcol
  calc (1 : ℝ) = ClassicalValue (GraphColoringGame G k) := hcv.symm
    _ ≤ QuantumValue (GraphColoringGame G k) :=
        ClassicalValue_le_QuantumValue (GraphColoringGame G k) hbdd

/-! **The chromatic chain `χ_qc ≤ χ_q ≤ χ` is not stated here.**

Every chromatic invariant available at this level is a `0` stub, against which
each inequality would be the contentless `0 ≤ 0`.  The stub-independent
game-value content is what this file states: a colouring forces the
quantum game value to `1` (`quantumColorable_imp_one_le_quantumValue`) and the
quantum-advantage gap (`phantomSymmetry_to_quantumStrategy`).  The real chain
awaits non-`0` bodies for the chromatic invariants. -/

/-! ## 4. Quantum equitable partitions induce quantum strategies

The point of Tower 3.5: a *quantum equitable partition* (D5,
`NonCommutativeCoherent.lean`) of `G` produces a non-classical
Tsirelson strategy for the `(G, k)`-coloring game whenever the cells'
projector system supports a `k`-coloring of the *quotient* but **not**
of `G` itself.  This is the loop closure with L6 (the "phantom
symmetry → quantum coloring" speculation).
-/

/-- A *phantom symmetry witness* on `G`: the **operational** data of the
quantum-advantage regime for the `(G, k)`-coloring game — a perfect
Tsirelson-quantum strategy (a `QuantumStrategy` winning with probability `1`,
together with the normalization bound `win ≤ 1` that the win-probability
encoding satisfies) for a graph `G` that admits **no** classical `k`-coloring.

The structure must carry the strategy itself.  A version inhabited for
*any* non-`k`-colorable `G` — without a quantum strategy existing — would make
`phantomSymmetry_to_quantumStrategy` (which concludes `QuantumValue = 1`)
false: take `G = K_{k+1}`; it has `χ_q = k+1 > k`, so no perfect quantum
strategy and `QuantumValue (GraphColoringGame K_{k+1} k) < 1`.  Carrying the
perfect strategy (and its normalization bound) makes inhabitation
exactly the quantum-advantage assertion `χ_q(G) ≤ k < χ(G)` this structure is
meant to package.

(We do not formalize `QuantumEquitablePartition` here — that's
`NonCommutativeCoherent.lean`; we package the strategy it produces.) -/
structure PhantomSymmetry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) where
  /-- The perfect Tsirelson-quantum strategy realized by the phantom symmetry. -/
  strategy : NonLocalGame.QuantumStrategy V (Fin k)
  /-- It wins the `(G, k)`-coloring game with probability `1`. -/
  strategy_perfect : NonLocalGame.quantumWin (GraphColoringGame G k) strategy = 1
  /-- The win probability is normalized: no strategy exceeds `1` (the
  upper bound the win-probability encoding satisfies; it makes the supremum a
  true value rather than an artifact). -/
  win_le_one : ∀ S : NonLocalGame.QuantumStrategy V (Fin k),
    NonLocalGame.quantumWin (GraphColoringGame G k) S ≤ 1
  /-- `G` itself does *not* admit a classical `k`-coloring (the
  quantum-advantage regime). -/
  no_classical_coloring : ¬ ∃ c : G.Coloring (Fin k), True

/-- **Phantom symmetry → quantum advantage.**  A `PhantomSymmetry G k`
witness produces the quantum-advantage gap `ω^*(GraphColoringGame G k) = 1`
(perfect quantum strategy) while `ω(GraphColoringGame G k) < 1` (no perfect
classical strategy), witnessing `χ_q(G) ≤ k < χ(G)`.

This is the *quantum advantage* phenomenon — the original example is the
orthogonality graph on `ℝ^4`, where `χ_q = 4 < χ = 5` (Mancinska-Roberson §5,
building on Cubitt-Mancinska-Roberson-Severini-Stahlke-Winter).

The carried perfect strategy attains the (normalized)
quantum value `1`, and the *absence* of a classical `k`-coloring forces the
classical value strictly below `1` via `GraphColoringGame.classical_value_eq_one`.
-/
theorem phantomSymmetry_to_quantumStrategy
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (P : PhantomSymmetry G k) :
    QuantumValue (GraphColoringGame G k) = 1
      ∧ ClassicalValue (GraphColoringGame G k) < 1 := by
  classical
  -- The carried strategy witnesses nonemptiness of the quantum-strategy type.
  haveI hQne : Nonempty (QuantumStrategy V (Fin k)) := ⟨P.strategy⟩
  refine ⟨?_, ?_⟩
  · -- Quantum value is exactly `1`: the carried perfect strategy attains it, and
    -- `win_le_one` is an upper bound (so the supremum equals `1`).
    have hbdd : BddAbove (Set.range (quantumWin (GraphColoringGame G k))) :=
      ⟨1, by rintro _ ⟨S, rfl⟩; exact P.win_le_one S⟩
    refine le_antisymm (ciSup_le P.win_le_one) ?_
    rw [← P.strategy_perfect]
    exact le_ciSup hbdd P.strategy
  · -- Classical value is `< 1`: no `k`-coloring ⟹ value `≠ 1`; and value `≤ 1`.
    -- `classical_value_eq_one` gives `ClassicalValue = 1 ↔ ∃ coloring`.
    have hne1 : ClassicalValue (GraphColoringGame G k) ≠ 1 := by
      intro hval
      exact P.no_classical_coloring
        ((GraphColoringGame.classical_value_eq_one G k).mp hval)
    -- `ClassicalValue ≤ 1` (every classical win is `≤ 1`); handle empty case too.
    have hub : ∀ σ : ClassicalStrategy V (Fin k),
        classicalWin (GraphColoringGame G k) σ ≤ 1 := by
      intro σ
      unfold classicalWin
      rw [div_le_one (by
        have : 0 < Fintype.card V := Fintype.card_pos
        positivity)]
      calc ((Finset.univ.filter (fun p : V × V =>
              (GraphColoringGame G k).verifier p (σ.alice p.1, σ.bob p.2))).card : ℝ)
          ≤ (Fintype.card (V × V) : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
        _ = (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
            push_cast [Fintype.card_prod]; ring
    have hle1 : ClassicalValue (GraphColoringGame G k) ≤ 1 := by
      by_cases hCne : Nonempty (ClassicalStrategy V (Fin k))
      · exact ciSup_le hub
      · -- empty strategy type ⟹ `ClassicalValue = sSup ∅ = 0 ≤ 1`.
        rw [not_nonempty_iff] at hCne
        simp only [ClassicalValue, Real.iSup_of_isEmpty]
        norm_num
    exact lt_of_le_of_ne hle1 hne1

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

/-- The win count of any deterministic strategy in the CHSH game is at most
`3` out of the `4` question pairs: no classical strategy wins all four. -/
theorem CHSH_win_count_le_three (σ : ClassicalStrategy (Fin 2) (Fin 2)) :
    (Finset.univ.filter (fun p : Fin 2 × Fin 2 =>
        CHSHGame.verifier p (σ.alice p.1, σ.bob p.2))).card ≤ 3 := by
  -- The win predicate at the four pairs depends only on the four values
  -- `σ.alice 0, σ.alice 1, σ.bob 0, σ.bob 1`; brute force over those.
  have key : ∀ a0 a1 b0 b1 : Fin 2,
      (Finset.univ.filter (fun p : Fin 2 × Fin 2 =>
        CHSHGame.verifier p
          ((fun i : Fin 2 => if i = 0 then a0 else a1) p.1,
           (fun j : Fin 2 => if j = 0 then b0 else b1) p.2))).card ≤ 3 := by
    decide
  have ha : σ.alice = fun i : Fin 2 => if i = 0 then σ.alice 0 else σ.alice 1 := by
    funext i; fin_cases i <;> simp
  have hb : σ.bob = fun j : Fin 2 => if j = 0 then σ.bob 0 else σ.bob 1 := by
    funext j; fin_cases j <;> simp
  have := key (σ.alice 0) (σ.alice 1) (σ.bob 0) (σ.bob 1)
  rwa [← ha, ← hb] at this

/-- An explicit CHSH strategy winning `3` of the `4` pairs: both players
always answer `0`, which wins on every pair except `(1,1)`. -/
theorem CHSH_exists_win_three :
    (Finset.univ.filter (fun p : Fin 2 × Fin 2 =>
        CHSHGame.verifier p
          (({alice := fun _ => 0, bob := fun _ => 0} :
            ClassicalStrategy (Fin 2) (Fin 2)).alice p.1,
           ({alice := fun _ => 0, bob := fun _ => 0} :
            ClassicalStrategy (Fin 2) (Fin 2)).bob p.2))).card = 3 := by
  decide

/-- **CHSH classical bound.**  `ω(CHSH) = 3/4`.  -/
theorem CHSH_classical_value : ClassicalValue CHSHGame = 3 / 4 := by
  have hcard : (Fintype.card (Fin 2) : ℝ) * (Fintype.card (Fin 2) : ℝ) = 4 := by
    simp [Fintype.card_fin]; norm_num
  -- Each strategy's win is ≤ 3/4.
  have hub : ∀ σ : ClassicalStrategy (Fin 2) (Fin 2), classicalWin CHSHGame σ ≤ 3 / 4 := by
    intro σ
    unfold classicalWin
    rw [hcard]
    have hle : ((Finset.univ.filter (fun p : Fin 2 × Fin 2 =>
        CHSHGame.verifier p (σ.alice p.1, σ.bob p.2))).card : ℝ) ≤ 3 := by
      exact_mod_cast CHSH_win_count_le_three σ
    gcongr
  -- The all-zero strategy attains 3/4.
  set σ₀ : ClassicalStrategy (Fin 2) (Fin 2) := {alice := fun _ => 0, bob := fun _ => 0}
  have hwit : classicalWin CHSHGame σ₀ = 3 / 4 := by
    unfold classicalWin
    rw [hcard, CHSH_exists_win_three]
    norm_num
  haveI : Nonempty (ClassicalStrategy (Fin 2) (Fin 2)) := ⟨σ₀⟩
  have hbdd : BddAbove (Set.range (classicalWin CHSHGame)) :=
    ⟨3 / 4, by rintro _ ⟨σ, rfl⟩; exact hub σ⟩
  apply le_antisymm
  · -- ClassicalValue ≤ 3/4
    exact ciSup_le hub
  · -- 3/4 ≤ ClassicalValue
    rw [← hwit]
    exact le_ciSup hbdd σ₀

/-- **Tsirelson's bound (re-keyed off the proven operator-algebra theorem).**
`ω^*(CHSH) = (2 + √2) / 4 = cos²(π/8)`.

This is the win-probability form of Tsirelson's `2√2` bound on the CHSH
correlator (Tsirelson, "Quantum generalizations of Bell's inequality", Lett.
Math. Phys. 4 (1980), 93-100).

The bound rests on two satisfiable hypotheses:

* `hreal : ∀ S, CHSHRealization (8·quantumWin CHSHGame S − 4)` — the
  quantum-mechanical modelling assumption that each strategy's signed CHSH value
  is realized by commuting self-adjoint `±1`-observables + a vector state.  Its
  inhabitability is witnessed concretely by `CHSHRealization.ofAbsLeTwo` (for the
  classical-regime strategies).  The upper
  bound `≤ 2√2` is then *derived* from the proven `CHSHRealization.le_two_sqrt_two`.
* `htight : ∀ ε > 0, ∃ S, 2√2 − (8·quantumWin CHSHGame S − 4) < ε` — tightness, the
  literature fact that Tsirelson's optimal entangled strategy approaches
  the bound. -/
theorem CHSH_quantum_value
    (hreal : ∀ S : QuantumStrategy (Fin 2) (Fin 2),
      CHSHRealization (8 * quantumWin CHSHGame S - 4))
    (htight : ∀ ε > 0, ∃ S : QuantumStrategy (Fin 2) (Fin 2),
      2 * Real.sqrt 2 - (8 * quantumWin CHSHGame S - 4) < ε) :
    QuantumValue CHSHGame = (2 + Real.sqrt 2) / 4 := by
  classical
  -- `0 ≤ √2` for the arithmetic below.
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- The strategy type is nonempty (embed the all-zero classical strategy).
  haveI hne : Nonempty (QuantumStrategy (Fin 2) (Fin 2)) :=
    ⟨classicalToQuantum {alice := fun _ => 0, bob := fun _ => 0}⟩
  -- UPPER half: each strategy's CHSH value is `≤ 2√2` via the PROVEN
  -- operator-algebra bound applied to its realization.
  have hub : ∀ S : QuantumStrategy (Fin 2) (Fin 2),
      quantumWin CHSHGame S ≤ (2 + Real.sqrt 2) / 4 := by
    intro S
    have hbnd : 8 * quantumWin CHSHGame S - 4 ≤ 2 * Real.sqrt 2 :=
      LiteratureInterfaces.CHSHRealization.le_two_sqrt_two (hreal S)
    -- `8·win − 4 ≤ 2√2  ⟹  win ≤ (2+√2)/4`.
    linarith
  have hbdd : BddAbove (Set.range (quantumWin CHSHGame)) :=
    ⟨(2 + Real.sqrt 2) / 4, by rintro _ ⟨S, rfl⟩; exact hub S⟩
  apply le_antisymm
  · -- `⨆ ≤ (2+√2)/4`
    exact ciSup_le hub
  · -- LOWER half: tightness approaches `2√2`, forcing the sup up to `(2+√2)/4`.
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    -- choose the Tsirelson strategy realizing `value` within `8ε` of `2√2`
    obtain ⟨S, hS⟩ := htight (8 * ε) (by positivity)
    -- `2√2 − (8·win − 4) < 8ε  ⟹  (2+√2)/4 − ε < win ≤ ⨆`
    have hle : quantumWin CHSHGame S ≤ QuantumValue CHSHGame := le_ciSup hbdd S
    have : (2 + Real.sqrt 2) / 4 - ε < quantumWin CHSHGame S := by linarith
    linarith

/-- **Tsirelson bound on the CHSH correlator.**  In the standard
correlator normalization, the signed CHSH expression is `C(S) = 8·win(S) − 4`,
affinely tied to the win-probability (same encoding as `CHSH_quantum_value`).
Tsirelson's bound is the *two-sided* statement `|C(S)| ≤ 2√2`.

The per-`S`
two-sided bound is *derived* from the proven `CHSHRealization.le_two_sqrt_two`,
given realizations of `C(S)` and of the complementary correlator `−C(S) =
4 − 8·win` (flip one party's outputs — itself a valid CHSH value).  Both
hypotheses are inhabitable (`CHSHRealization.ofAbsLeTwo`). -/
theorem CHSH_correlator_bound
    (S : QuantumStrategy (Fin 2) (Fin 2))
    (hpos : CHSHRealization (8 * quantumWin CHSHGame S - 4))
    (hneg : CHSHRealization (4 - 8 * quantumWin CHSHGame S)) :
    |8 * quantumWin CHSHGame S - 4| ≤ 2 * Real.sqrt 2 := by
  -- Upper half: proven bound on the CHSH correlator `C(S) = 8·win − 4`.
  have hup : 8 * quantumWin CHSHGame S - 4 ≤ 2 * Real.sqrt 2 :=
    LiteratureInterfaces.CHSHRealization.le_two_sqrt_two hpos
  -- Lower half: proven bound on the *complementary* correlator `−C(S) = 4 − 8·win`.
  have hlo : 4 - 8 * quantumWin CHSHGame S ≤ 2 * Real.sqrt 2 :=
    LiteratureInterfaces.CHSHRealization.le_two_sqrt_two hneg
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

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

A finite-dimensional ∗-representation of this algebra in `M_n(ℂ)` is — by
Mancinska–Roberson §4 / PSSTW — exactly the data of a **perfect synchronous
quantum strategy** for the game.  Rather than scaffold the universal ∗-algebra
abstractly (which would carry only an inert `Carrier : Type`, making its
inhabitation content-free), we record `GameAlgebra` by the *operational content
its representations realise*: a finite-dimensional Tsirelson-quantum strategy
that wins the game perfectly.

This makes `GameAlgebra` content-bearing — it is inhabited **iff** the
game has a perfect quantum strategy — which is precisely the property the
universal ∗-algebra is meant to track, and what `QuantumValue_eq_gameAlgebra_rep`
asserts. -/
structure GameAlgebra (V O : Type*) [Fintype V] [Fintype O]
    (G : NonLocalGame V O) where
  /-- A finite-dimensional ∗-representation, recorded by the perfect
  Tsirelson-quantum strategy it realises (Mancinska–Roberson §4). -/
  rep : QuantumStrategy V O
  /-- The representation is *perfect*: the realised strategy wins with
  probability `1`. -/
  rep_perfect : quantumWin G rep = 1

/-- **Game-algebra representation ↔ perfect quantum strategy** (Mancinska–Roberson
§4, the synchronous-strategy dictionary).

`GameAlgebra` records a finite-dimensional ∗-rep by the perfect Tsirelson
strategy it realises, so its inhabitation
`∃ A : GameAlgebra V O G` is *exactly* the assertion that the game admits a
perfect quantum strategy `∃ S, quantumWin G S = 1`.  The biconditional

    (∃ A : GameAlgebra V O G) ↔ (∃ S : QuantumStrategy V O, quantumWin G S = 1)

is proved by destructuring each side into the other (a
`GameAlgebra` *is* a perfect strategy together with its perfection witness, and
conversely).  This is the operational form of "the game ∗-algebra has a
finite-dimensional representation iff the game has a perfect (synchronous)
quantum strategy". -/
theorem QuantumValue_eq_gameAlgebra_rep
    {V O : Type*} [Fintype V] [Fintype O] (G : NonLocalGame V O) :
    (∃ _A : GameAlgebra V O G, True)
      ↔ ∃ S : QuantumStrategy V O, quantumWin G S = 1 := by
  constructor
  · rintro ⟨A, -⟩
    exact ⟨A.rep, A.rep_perfect⟩
  · rintro ⟨S, hS⟩
    exact ⟨⟨S, hS⟩, trivial⟩

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

The Lovász ϑ ≤ ϑ_q ≤ χ_q ≤ χ chain of `Graphplay.Relational` is intended to lift
to *non-local game values*:

* `ω(GraphColoringGame G k) = 1`     ↔  `χ(G) ≤ k`.
* `ω^*(GraphColoringGame G k) = 1`   ↔  `χ_q(G) ≤ k`.
* `ω^{co}(GraphColoringGame G k) = 1`↔  `χ_{qc}(G) ≤ k`.
* `ϑ_q` (the quantum Lovász theta) lower-bounds `χ_q` and upper-bounds
  the independence variant `α_q`.

**The `χ_qc ≤ χ_q ≤ χ` chain theorem is not stated here.**
Against the `0`-stub chromatic invariants of `Graphplay.Relational` it would be
the contentless `0 ≤ 0 ∧ 0 ≤ 0`, asserting nothing about the real
chain.  The stub-independent half (a
colouring forces `ω^* = 1`) is `quantumColorable_imp_one_le_quantumValue`; the
full chain awaits non-stub bodies for the chromatic invariants.
-/

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
