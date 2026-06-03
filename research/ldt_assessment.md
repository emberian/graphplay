# Lattice Deduction Transformers — mechanics reference

**Paper:** *Lattice Deduction Transformers*, Liam Davis (Amherst), Leopold Haller (Axiom), Alberto
Alfarano (Axiom), Mark Santolucito (Barnard/Columbia). arXiv:2605.08605 v1, 9 May 2026.
Code: github.com/lcrh/lattice-deduction-transformers.
**Date:** 2026-06-02.

The two outward memos are `research/ldt_theory_for_authors.md` (the soundness/completeness/abstention
result) and `research/refinement_deduction_duality.md` (the refinement⊣deduction abstract-interpretation
duality and the Lean build). This file pins the LDT construction itself, for reference.

---

## The abstract domain

**Concrete** `C = ℘(S)`, `S = {1..k} → V` the fixed-length solution strings over vocabulary `V`,
ordered by ⊆. **Abstract** `A = {1..k} → ℘(V)`, the product over `k` positions of the per-cell candidate
powerset, ordered by pointwise inclusion (`a ⊑ b ⟺ ∀i. a(i) ⊆ b(i)`); meet/join pointwise. ⊤ = every
cell holds the full vocab; ⊥ = any `a` with an empty cell. Lower = more informative; deduction descends.

In code (`sudoku_extreme.py`, `dpll.py`): `state : [B, S, C]` of binary alive-bits, ⊤ = the puzzle input
(blanks all-ones, givens singletons), a solution is one-hot per cell, UNSAT = all-zeros. Meet = bitwise
AND, join = bitwise OR. Abstracting to `A` forgets inter-cell correlation (App. A.1, Fig. 5) — the
defining lossiness of an over-approximation domain.

## The Galois connection (App. A.1)

```
        α
  C  ⇄  A      α(S')(c) = { g(c) : g ∈ S' }        (per-cell projection; lower adjoint)
        γ      γ(a)     = { g ∈ G : ∀c. g(c) ∈ a(c) }   (upper adjoint)
```
with round-trip laws `S ⊆ γ(α(S))` and `α(γ(a)) ⊑ a` — standard over-approximation soundness, a Galois
connection (not an insertion: `α∘γ ≠ id`). γ is monotone.

## The deduction step and the loop

**Best abstract transformer** (App. A.2): `dedₚ(a) = α(γ(a) ∩ ‖p‖)`, where `‖p‖ ⊆ S` is the (sampled)
solution set of instance `p` — keeps candidates surviving in at least one valid solution. `dedₚ` is a
lower closure operator (monotone, reductive `dedₚ(a) ⊑ a`, idempotent); naked/hidden singles are weaker
sound under-approximations. The transformer is trained to approximate `dedₚ`; at inference the per-cell
sigmoids thresholded at `θ_elim` perform the narrowing.

**Two nested loops.** Inner: the looped transformer (`PowersetModel`, `n_loops=16`) — a 4-layer stack
unrolled with input re-injection and a LayerNorm'd outer residual; computes one `dedₚ`-approximation per
Solve-step. Outer (`Solve`): `repeat { (x', conflict, solved) ← step(x); x ← x' } until conflict or
solved`; `step` narrows, re-encodes, and branches if undetermined.

**Convergence is gfp Kleene iteration of `dedₚ` from ⊤** (App. A.2). Termination is well-foundedness:
the lattice is finite and each step strictly decreases the alive-candidate count (§4.2). Cousot–Cousot
fixpoint transfer `α(gfp f) ⊑ gfp f^♯` is invoked. No contraction constant, no spectral rate. Singleton
per cell ⇒ solved; multi-candidate cells remaining ⇒ branch.

## Conflict, backtracking, supervision

⊥ has a dual representation (§4.1): implicit (any empty candidate set) and explicit (a learned CLS-token
sigmoid trained to fire on unsatisfiable states). A conflict resets the chain to the puzzle original =
backtrack. Elimination sits on the soundness side (a wrong elimination is unrecoverable); the CLS head on
the completeness side (a missed conflict stalls search).

On-policy supervision (`train.py`): the BCE target is `state ⊓ α(surviving)` — literally
`α({y ∈ Y : y consistent with x})` — over a replay pool of partial lattice states advanced by the
model's own `dpll_step`, giving an emergent curriculum over lattice depths. `K` is the multi-solution
sample budget: K=1 (unique-solution Sudoku/Snowflake) recovers single-target SFT; K=512 (Maze, sampled
shortest paths) sharpens `α` toward `α(‖p‖)`. Solve-rate rises and inference-search drops with K,
saturating fast (Fig. 4b).

## Results (Tables 1–3)

Sudoku-Extreme: 800K → 100% accuracy, 15 min on 1×B200 (Sotaku 800K/2.7M → 98.9 in 2h40m; TRM 5M → 87.4;
HRM 27M → 55; frontier LLMs → 0). Median forward passes drop ×10 as train budget grows (Fig. 3a; forward
count tracks problem hardness and training budget, not a spectral gap). Snowflake (hex, variable-size)
800K → 100. Maze-Hard 30×30: 1.8M → 99.3 (K=1) / 99.9 (K=512); the few misses emit valid-but-suboptimal
paths. "Empirically sound" = returns a correct answer or abstains.

---

### References
- *Lattice Deduction Transformers*, Davis, Haller, Alfarano, Santolucito, arXiv:2605.08605, 2026.
- Cousot & Cousot, *Abstract interpretation* (POPL 1977).
- Feder & Vardi, *The computational structure of monotone monadic SNP and CSP* (SICOMP 1998).
- Barto & Kozik, *CSPs solvable by local consistency methods* (JACM 2014).
- D'Silva, Haller, Kroening, *Abstract Conflict Driven Learning* (POPL 2013).
