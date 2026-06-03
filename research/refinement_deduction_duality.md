# Refinement ⊣ Deduction: the abstract-interpretation duality between partition refinement and the Lattice Deduction Transformer

**For** the Axiom / Haller PL∩SAT scene. **From** the graphplay formalization effort. **Date** 2026-06-02.
**Companion to** `research/ldt_theory_for_authors.md`.

---

graphplay's WL/colour-refinement (= coarsest equitable partition = coarsest bisimulation) and the
Lattice Deduction Transformer's deduction (arXiv:2605.08605) are the two order-dual halves of one
Knaster–Tarski fixpoint story, and Cousot–Cousot abstract interpretation is the frame that contains
both:

| | **refinement (graphplay)** | **deduction (LDT)** |
|---|---|---|
| Lattice | partition lattice `Part(V)` (refinement order) | grid powerset `A = pos → ℘(V)` (pointwise ⊆) |
| Operator | `wlStep` — monotone, refining (splits cells) | `dedₚ = α∘(·∩‖p‖)∘γ` — monotone, reductive (removes candidates) |
| Fixpoint | from the trivial partition, ascending the refinement order | gfp from ⊤, descending the precision order |
| Builds | the coarsest sound abstraction (quotient automaton) | a value within a fixed abstraction (the solution set) |
| Acts by | distinguishing states | eliminating values |
| Termination | `wlRefine_stable`: ≤ |V| rounds (lattice height) | strict alive-count descent (lattice height) |

Refinement *distinguishes states* (builds the quotient); deduction *eliminates values* (descends to
the solution). They are dual instances of one theorem, on different lattices with operators moving in
opposite directions.

## 1. The duality, pinned

**Knaster–Tarski.** For a complete lattice and monotone `f`, the least and greatest fixpoints are
exchanged by the order-dual lattice (`lfp_L f = gfp_{L^op} f`); the proof principles are dual
(gfp ↦ coinduction, lfp ↦ inductive invariant). Bisimilarity is a gfp; behavioural distances are its
motivating examples (Baldan–Eggert–König–Padoan, *Fixpoint Theory – Upside Down*, LMCS 2023).

graphplay proves the operational form: `wlStep_isRefinement` (monotone in the refinement order),
`wlColorCount_mono` (height strictly increases until fixed), `wlRefine_stable` (stabilizes in ≤ |V|
rounds), `wlRefine_coarsestEquitable` (the fixpoint is the coarsest equitable partition).

**Cousot–Cousot.** A Galois connection `α ⊣ γ` between concrete and abstract complete lattices, a
sound abstract transformer `f^♯ ⊒ α∘f∘γ`, and fixpoint transfer `α(lfp f) ⊑ lfp f^♯` (dually gfp).

- LDT is a textbook instance: `α(S')(i) = {s(i):s∈S'}`, `γ(a) = {s : ∀i. s(i)∈a(i)}`, best transformer
  `dedₚ = α∘(·∩‖p‖)∘γ`, gfp-Kleene descent from ⊤. The abstraction is lossy by design (α∘γ forgets
  inter-cell correlation).
- Partition refinement is also an instance, proved in the literature: Ranzato–Tapparo (*Generalizing
  the Paige–Tarjan algorithm by abstract interpretation*, Inf. Comput. 2008) exhibit a Galois insertion
  between the partition lattice and the lattice of abstract domains, with generalized PT computing the
  coarsest strongly-preserving abstraction — the coarsest-bisimulation object graphplay formalizes.

So the unifying statement:

> Both WL-refinement and lattice-deduction are Kleene-fixpoint computations on complete lattices
> carrying Galois connections (Cousot–Cousot). graphplay's is the coarsest-sound-abstraction-building
> leg (Ranzato–Tapparo partition-domain insertion); LDT's is the value-narrowing-within-a-fixed-
> abstraction leg (over-approximation).

**CEGAR is the refine ⊣ deduce loop.** Start coarse; check inside the abstraction (deduce); on a
spurious counterexample, refine (split states) and repeat — the alternation of the two fixpoints
(Clarke–Grumberg–Jha–Lu–Veith, CAV 2000). The lineage is direct: D'Silva–Haller–Kroening's *Abstract
Conflict Driven Learning* (POPL 2013) — Haller is the LDT senior author — recast CDCL as abstract
interpretation combining gfp over-approximation with lfp under-approximation. LDT is its neural
descendant on the deduction leg; graphplay supplies a verified instance of the refinement leg.

## 2. The CSP rung: refine = propagate, on one hierarchy

On constraints the duality becomes a named, theorem-backed correspondence. Level-`k` Sherali–Adams,
`k`-WL colour refinement, and `C^k` counting-logic indistinguishability interleave in power
(Atserias–Maneva, SICOMP 2013), sharpened to a precise pebble-game match (Grohe–Otto). The
`k`-consistency algorithm — the canonical constraint-propagation procedure — solves exactly the
bounded-width CSPs, and its power equals `C^k` = `k`-WL (Atserias–Bulatov–Dawar; Barto–Kozik).

So on the CSP instance, "refine the partition" (k-WL) and "propagate to local consistency"
(k-consistency) are levels of one hierarchy. LDT's `dedₚ` is arc-/local-consistency narrowing;
graphplay's WL is the colour-refinement / `C^k` side; they meet in the Atserias hierarchy. This is a
correspondence of expressive-power hierarchies, on different carriers (k-WL refines vertex-tuples,
k-consistency narrows partial assignments).

## 3. The quantum leg is the refinement leg

The quantum content lifts on the refinement side. The CTQW restricted to the cell-uniform subspace is
the walk on the `r×r` symmetric quotient `Q̃ = D^{1/2} Q D^{-1/2}`, exact and spectrum-preserving
(`restrict_eq_symmQuotient`, `cellUniformPST_iff_quotientPST`, `spec Q̃ ⊆ spec A`) — a formalized
instance of the Krovi–Brun (2007) / Bachman–Tamon (2011) quotient-walk picture. The Szegedy
`√`-speedup (`SzegedyWalk_unitary`, `szDiscriminant_spec`, the `exp(±i·arccos λ)` Jordan fold) is the
spectral phenomenon attached to it.

The deduction leg lives on a Boolean candidate lattice with arc-consistency narrowing — a classical
CSP object. The duality is therefore asymmetric: the refinement leg carries a quantum-walk lift via
the equitable quotient; the deduction leg is classical CSP. The asymmetry is the precise statement.

The quotient is an exact subspace isometry (no information loss on the symmetric sector), the dual
species of LDT's lossy `α∘γ`. The lift `cellInflate : Matrix I I ℂ → Matrix V V ℂ` is a block-diagonal
linear lift; it is not the Galois connection — the partition-domain Galois insertion that does carry
the abstract-interpretation structure is the Ranzato–Tapparo one above.

## 4. The symmetry residue, proved in repo

The WL-stable / coarsest-equitable partition refines the orbit partition: in the refinement order
`WL-stable ⊑ orbit` (`wlStable_refines_orbit` — every automorphism preserves every WL colour, so each
orbit is a union of WL-cells; the orbit partition is always equitable, `orbitPartition_isEquitable`).
Combinatorial indistinguishability is finer than true symmetry; the gap can be proper (Cai–Fürer–
Immerman, FOCS 1989). The strict-gap witness is stated in repo but not machine-checked here.

## 5. The build

> **`Graphplay/Integrations/LatticeDeduction.lean` — `theorem soundDeduction_run_preserves_solutions`.**
> 1. `A := pos → Finset V` with pointwise `⊑`; `instCompleteLattice`.
> 2. `γ a := {s | ∀ i, s i ∈ a i}`; `α S i := S.image (· i)`; `GaloisConnection α γ`.
> 3. `soundNarrow (f : A → A) := ∀ a, f a ⊑ a ∧ (‖p‖ ∩ γ a) ⊆ γ (f a)`.
> 4. Instantiate `Tower8.TransitionCoalg` with carrier `A`, `step` = abstract narrow-or-branch; apply
>    `stepInv_preserved` with `Good a := (‖p‖ ∩ γ ⊤) ⊆ γ a` ⟹ every reachable Solve-state keeps every
>    true solution alive ⟹ a singleton-per-cell terminal is a solution.

This proves LDT's empirical-soundness claim ("returns a correct answer or abstains"), reusing the one
graphplay asset that fits — Tower-8's `stepInv_preserved` run-invariant. Layered on top, a verified
`AbstractInterpretation` interface (Galois connection + sound transformer + fixpoint transfer) with
the LDT grid-powerset and the Ranzato–Tapparo partition domain as two instances makes the
refinement⊣deduction duality itself a machine-checked statement: both are `AbstractInterpretation`.
A proof, not a press release. ( ◕‿◕ )

---

### Sources

- Tarski, *A lattice-theoretical fixpoint theorem*, Pacific J. Math. 5 (1955).
- Baldan, Eggert, König, Padoan, *Fixpoint Theory – Upside Down* (LMCS 2023), arXiv:2101.08184.
- Cousot & Cousot, *Abstract interpretation* (POPL '77).
- Clarke, Grumberg, Jha, Lu, Veith, *Counterexample-guided abstraction refinement* (CAV 2000; JACM 2003).
- D'Silva, Haller, Kroening, *Abstract Conflict Driven Learning* (POPL 2013).
- Ranzato & Tapparo, *Generalizing the Paige–Tarjan algorithm by abstract interpretation* (Inf. Comput. 2008), arXiv:cs/0612120.
- Atserias & Maneva, *Graph isomorphism, Sherali–Adams relaxations and counting logics* (SICOMP 2013).
- Grohe & Otto, *Pebble games and linear equations* (CSL 2012; JSL 2015), arXiv:1204.1990.
- Atserias, Bulatov, Dawar, *On the power of k-consistency* (ICALP 2007).
- Krovi & Brun, *Quantum walks on quotient graphs* (Phys. Rev. A 75, 062332, 2007), arXiv:quant-ph/0701173.
- Bachman, Tamon et al., *Perfect state transfer on quotient graphs* (2011), arXiv:1108.0339.
- *Lattice Deduction Transformers*, Davis, Haller, Alfarano, Santolucito, arXiv:2605.08605.
