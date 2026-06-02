# Soundness, completeness, and abstention in Lattice Deduction Transformers

**For** Liam Davis, Leopold Haller, Alberto Alfarano, Mark Santolucito.
**From** the graphplay formalization effort. **Date** 2026-06-02.

You wrapped a clean abstract-interpretation construction — the Galois connection α ⊣ γ,
the best transformer dedₚ, gfp Kleene descent — around a small looped transformer, and
defended it with the empirical line *"correct or abstains."* We machine-checked the theory
around that claim (Lean 4 / Mathlib). It says something sharper than the defense:

> **Soundness is free from output checking and training-independent. The real quantity is the
> abstention map — which problems your lattice can *complete* — and that map is the classical
> bounded-width CSP dichotomy.**

Theorem names below are clickable in the repo; the relevant files are listed at the end.

## 1. Soundness is not a property of the trained net

Model the entire trained loop as an arbitrary `solve : Abs → Abs`. Deploy it by reading off
the pinned assignment and returning it **only if it satisfies the constraints**, else abstain.
Then `checkedSolve_sound` holds for *any* `solve`, with no hypothesis on it: if it returns `s`,
then `s` is a genuine solution. The proof uses nothing about the net.

That is the SAT-solver guarantee, stated exactly: a `SAT` answer is believed because the
assignment is *checkable*, not because the search is *trusted*. Training cannot break soundness —
it can only change how often you abstain. `id_sound_but_useless` makes it sharp: the identity map
is a perfectly sound deduction that solves nothing.

If you want to trust the *intermediate trace* (early abstention, proof extraction, composing LDT
with another reasoner) rather than just the final answer, per-step soundness comes the same way —
from a verifier, not the net: `certifiedStep_sound` shows a certificate-checked narrowing is sound
for arbitrary `f`. Either way, soundness lives in the check.

## 2. The real quantity is completeness — and the lattice bounds it

Soundness being free, the question that matters is whether the loop reaches a checkable answer at
all: completeness, i.e. the abstention rate. This is where the projection lattice bites.
`ldt_lossy` is the machine-checked fact that per-cell candidate sets forget inter-cell correlation
(α ∘ γ ≠ id — your domain is a Galois *connection*, not an insertion). That lossiness is the entire
story of abstention.

And it has a name. dedₚ is arc-/k-consistency propagation, and *which* problems pure propagation
solves is the **bounded-width dichotomy**: local consistency solves exactly the bounded-width CSPs
(Feder–Vardi; Barto–Kozik), while affine/linear systems — XOR over GF(2) — are unbounded width:
invisible to deduction, solvable only by branching or linear algebra. So your deduction leg solves
precisely the bounded-width fragment; abstention on everything else is forced by the lattice, not by
any error. "Which problems generalize" is the bounded-width map, and it is a theorem.

## 3. Soundness ⟂ completeness, machine-checked

We built the canonical affine obstruction concretely. `acStep` is generalized arc consistency, and
it is sound for free (`acSoundStep` — the support test *is* the impossibility certificate). On the
XOR system `{x = y, y = z, x ⊕ y ⊕ z = 0}` (`xor_unique`: a unique solution `(0,0,0)`):

- `acStep_xor_stuck` — arc consistency makes **zero** progress from `⊤`;
- `acStep_xor_abstains` — so the solver abstains;
- `acStep_xor_sound_but_abstains` — one operator, simultaneously a **sound deduction** and
  **incomplete on a solvable problem**.

The same operator, same lattice, on a width-1 chain `{x₀ = false, x₀ = x₁}` returns the answer
(`acStep_chain_solves`); `ac_kind_discriminates` is the one-line conjunction. The difference is the
problem's **width**, not correctness — and it is the polymorphism algebra the dichotomy classifies,
which we also put in Lean: `xor_affine` (XOR carries the Maltsev operation `x ⊕ y ⊕ z`) and
`xor_no_majority` (it has none), versus `chain_semilattice` (the chain carries a meet). Affine wall
on one side, bounded width on the other.

## 4. Two axes, and the experiment that tests them

Every problem factors along two independent axes:

- **output-checkable** — a candidate answer is cheaply verifiable (NP / small certificate). This is
  what makes soundness free (§1), and it is a property of verification cost, nothing to do with the
  lattice.
- **deduction-solvable** — local consistency reaches an answer (bounded width). This is completeness
  (§2), a property of the problem's algebra, nothing to do with verification cost.

The XOR witness is checkable-yes, solvable-no, which is why the axes are orthogonal. Your puzzles
are both, which is why LDT generalizes — and the framework says which property does which work:
solve-rate tracks width, the never-confidently-wrong guarantee tracks checkability, and they are not
the same property.

**The experiment.** Train on kind-0 (AC-solvable: Horn-SAT, naked-singles Sudoku) and kind-2 (sparse
3-XOR with a planted unique solution). Ablate the branching/CLS head — deduction only. Measure the
abstention rate.

| condition | predicted abstention |
|---|---|
| kind-0, deduction-only | ≈ 0 |
| kind-2 (XOR), deduction-only | ≈ 1 — sound on every instance, solving none |

The sharp prediction is the second row: deduction-only on 3-XOR should abstain on essentially every
instance while remaining perfectly sound — `acStep_xor_sound_but_abstains` at scale. **If a
branch-ablated LDT solves 3-XOR at a nontrivial rate, the framework is wrong**: it would mean the
per-cell operator is doing linear algebra the bounded-width account forbids. We predict it does not;
if it does, that is the result worth knowing.

The whole picture lives in one Cousot frame: dedₚ's run-soundness is an instance of the general
fixpoint-transfer theorem (`Tower9.gfp_transfer`, `ldt_deduction_run_sound`), and refinement
(Weisfeiler–Leman) is its order-dual on the same interface.

---

**The gift, in one line.** Stop defending soundness — it is free from checking. Measure abstention,
train kind-0 versus kind-2, and watch the affine wall.

### References
- Davis, Haller, Alfarano, Santolucito. *Lattice Deduction Transformers.* arXiv:2605.08605, 2026.
- Cousot, Cousot. *Abstract interpretation.* POPL 1977.
- Feder, Vardi. *The computational structure of monotone monadic SNP and constraint satisfaction.*
  SICOMP 1998.
- Barto, Kozik. *Constraint satisfaction problems solvable by local consistency methods.* JACM 2014.
- Atserias, Maneva. *Graph isomorphism, Sherali–Adams relaxations and counting logics.* SICOMP 2013.
- D'Silva, Haller, Kroening. *Abstract Conflict Driven Learning.* POPL 2013.

### Machine-checked source (graphplay)
- `Graphplay/Integrations/LatticeDeduction.lean` — `alpha_gc_gamma`, `dedP_sound`,
  `dedRun_preserves_solutions`, `solved_state_is_correct`.
- `Graphplay/Integrations/LDTSoundness.lean` — `checkedSolve_sound`, `id_sound_but_useless`,
  `certifiedStep_sound`.
- `Graphplay/Integrations/LDTCompleteness.lean` — `acStep`, `xor_unique`,
  `acStep_xor_sound_but_abstains`, `acStep_chain_solves`, `ac_kind_discriminates`.
- `Graphplay/Integrations/LDTPolymorphism.lean` — `xor_affine`, `xor_no_majority`,
  `chain_semilattice`, `famCons_closed_meet`.
- `Graphplay/Integrations/LDTKindChecker.lean` — a runnable (`#eval`-able) classifier `acSolves?`.
- `Graphplay/Tower9.lean` — the Cousot interface: `gfp_transfer`, `ldt_lossy`,
  `ldt_deduction_run_sound`.
