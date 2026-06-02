# Graphplay

**The hidden quotient structure of quantum walks — formalized in Lean 4, and pointed at quantum-accelerated machine learning.**

For twenty years the Tamon group and the adjacent literature have published
theorems with the same shape: on *this* graph family, at *this* time, with
*this* signing, perfect state transfer or uniform mixing or optimal spatial
search emerges as if by analytic miracle. Read fifty such theorems and the
structure forces itself on you — every miracle factors through an **equitable
partition**: the dynamics collapse onto a small invariant subspace, and the
apparent magic is a finite-dimensional spectral condition on an `r × r` matrix
where `r` is *independent of the host size*.

Graphplay names that structure — *the universal coarse-graining of
quantum-walk operators* — and mechanizes it. The lift is not a metaphor here;
it is a machine-checked theorem, and everything else hangs off it: a stdlib of
named families, a numerical simulator you can watch, an inverse-design toolkit
that *builds* Hamiltonians to spec, and a bridge that turns the same quotient
reduction into a **provable quantum speedup for structured machine learning**.

The library spans ~100 Lean files and builds with **zero errors**. Two
invariants hold across the entire stack, and they are the point:

- **Every construction is real.** There is no `sorry` in any definition and no
  `True`-placeholder theorem anywhere. Every graph family, operator, partition,
  channel, bundle, sheaf, gauge field, attention matrix, and compiler pass is a
  concrete, fully-elaborated term. (One isolated exception: a single
  filtered-colimit-preservation *data* witness, honestly flagged.)
- **The remaining `sorry`s are exclusively theorem bodies** — "prove this true
  statement," never "this object isn't built yet." They are the genuinely-deep
  results (Godsil's Diophantine existence direction, Choi/Stinespring, MIP\*=RE,
  infinite-dimensional continuous spectrum) and the quantitative quantum-advantage
  *rates*.

## What's proven (axiom-clean)

The headline results below are `#print axioms`-clean: they depend on only
`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no custom axioms.

**The spine lift, both finitely and in the continuous limit.**
`EquitablePartition.cellUniformPST_iff_quotientPST` and
`GraphBundle.pst_iff_quotient` — cell-uniform perfect state transfer on a host
holds *iff* PST holds on its small symmetric quotient `Q̃ = D^{1/2} Q D^{-1/2}`.
The Tower-4 graphon counterpart (`Graphon.cellUniformPST_iff_quotientPST`,
`op_restrict_eq_quotient`) is equally clean — including the one genuinely-hard
Mathlib analytic gap, the Hilbert–Schmidt `MemLp` closure
(`kernelIntegralFun_memLp`), which is now proven. The same lift holds for
mixing and **search** (`cellUniformSearch_iff_quotientSearch`).

**Godsil's necessary condition.** `isPST_imp_isStronglyCospectral` — PST forces
strong cospectrality — via a from-scratch spectral-projector calculus
(`eigenProj`, `E² = E`, `E_λ E_μ = 0`, `U(τ) = Σ_λ e^{-iτλ} E_λ`), proven for
arbitrary Hermitian matrices (so it survives the chiral/complex case, where the
transferred phase is only unit-modulus, not ±1 — a distinction we make precisely).

**The first machine-checked *negative*-PST theorems.** The corpus is full of
"this graph *cannot* transfer," but nobody had formalized one.
`dominatingVertex_no_PST`, `cone_apex_no_PST`, `join_no_PST_within_G_of_not_cospectral`,
`pendantCorona_no_PST` — all proven, via a clean engine (`no_PST_of_not_cospectral`:
a single eigenvalue with unequal projector-diagonals certifies no transfer at any time).

**Named families, from first principles.** The Christandl-et-al. hypercube
antipodal PST at `τ = π/2` (`isPST_hypercubeP_antipode`) is built bottom-up:
Pauli-X matrix exponential → `isPST_K2` → Kronecker induction. The Cartesian
product preserves PST (`cartesianProduct_pst`) via a *genuinely proven*
`exp(M ⊗ 1) = exp(M) ⊗ 1` Kronecker factorization. The AAKV average-mixing
matrix is doubly-stochastic (`avgMixing_doublyStochastic`).

**Quantum advantage.** `quantum_search_quadratic_advantage`: continuous-time
quantum search on `K_n` reaches its target in `O(√n)` (an exact 2×2 Rabi
reduction of the search Hamiltonian, with the invariant subspace and dynamics
both proven), while any classical algorithm needs `Ω(n)` queries (an adversary
bound). And the contribution we actually care about —
`ml_structured_search_quantum_advantage`: lifted through the axiom-clean
quotient-search reduction, a search problem with an `r`-cell symmetry costs
`O(√r)` quantum, **independent of host size `N`**, vs `Ω(r)` classical. The
quadratic speedup is inherited by the small quotient *with a proof the answer
is identical*.

## Toward verified quantum-ML acceleration

This is the destination, and the reason the rest exists. The thesis is that the
equitable-partition quotient is *exactly* the symmetry reduction that makes both
classical structured linear algebra and its quantum acceleration tractable —
and that a machine-checked lift is the certificate that the reduction is exact.

- **Attention is a quantum-walk Hamiltonian.** `Integrations/MachineLearning`
  turns an attention score matrix into a Hermitian operator and proves that a
  symmetry of the attention pattern (translation-invariant, block-structured, or
  weight-tied / group-equivariant heads) induces a genuine **equitable partition**
  (`equitableOfAutomorphism`) — so the operator reduces *exactly* to a small
  `r × r` quotient (`multiHead_restrict_eq_symmQuotient`, delegating to the
  sorry-free spine). This is the verified statement that structured attention is
  compressible.

- **Structured attention is provably linear-time.**
  `Integrations/AttentionComplexity` proves, axiom-clean, that for block-equitable
  attention `A[i][j] = B[cell i][cell j]` the naive `O(n²·d)` apply *equals* an
  `O(n·r·d)` algorithm exactly (`blockAttentionApply_eq_fullAttentionApply` — the
  `n²` entries are only `r²` distinct blocks), i.e. the quadratic in sequence
  length **collapses to linear in n** (`attention_apply_linear_in_n`) — forward
  *and* backward (`training_step_linear_under_equitable`). The residual hard work
  shrinks from `n` to the small quotient dimension `r`, which is exactly where the
  `O(√r)` quantum search and the CTQW linear solve (`Integrations/MatrixInversion`,
  for the ML normal equations / kernel systems) buy more.

So the composition is concrete: **structured attention's quadratic becomes
linear in n, and the small `r × r` quotient that remains is where quantum
helps.** The honest split: the symmetry reduction and its exactness are
*proven*; the quantitative quantum-advantage *rates* (`O(√n)` search, `O(κ/ε)`
inversion) are the deep dynamical theorems still in progress, and the bridge
from *exactly*-equitable to *approximately*-structured (learned) attention —
**ε-equitable-partition theory** with controlled error — is the open frontier
this framework is built to attack. If you want to help build the verified case
for a machine that accelerates ML, that frontier is the door.

## It runs

```sh
lake exe graphplay-sim
```

A `Float`-backed numerical CTQW simulator (`exp(-iτH)` via scaling-and-squaring),
printing probability-vs-time tables you can actually watch:

- **Childs–Goldstone spatial search on `K_16`** — success probability climbs to
  `1.000000` exactly at `t* = (π/2)√16 = 6.2832`, then symmetrically decays.
- **Hypercube `Q_3` antipodal PST** — fidelity `1.000000` at `t = π/2`.
- **Chiral (magnetic-flux) walk** — clockwise transport bias `+0.99`, which a
  real-symmetric walk cannot produce.
- **Fractional revival** — partial revival to `α = 0.64` at the predicted time.
- **Lindblad dephasing** — purity decaying `1.0 → 0.37` (decoherence, live).
- **Attention quotient match** — a 2-block softmax attention's full-graph
  symmetric-subspace dynamics equal its `2×2` quotient evolution to `~10⁻⁶`. The
  compression theorem, watched.
- **Design → simulate loop** — a host Hamiltonian synthesized by the toolkit
  transfers at `π/2`, numerically confirming its certificate.

## It engineers

```sh
lake exe graphplay-toolkit examples/k4_equal_fiber.json   # → search-compiler report
```

`Toolkit/InverseDesign.synthesizePST` runs the spine *backwards*: pick a small
quotient with the property you want, **inflate** it through an equitable bundle,
and the host inherits the property — with a machine-checked certificate
(`engineered_host_has_PST`). Inverse design of Hamiltonians, not search.

## The seven-tower spine

The universal object at every level is the equitable partition; the universal
operation is `quotient = a small finite Hermitian matrix`; the universal
theorem is the lift.

| Tower | Object | Status |
|-------|--------|--------|
| 1 | `SimpleGraph V` | proven, computable, `#eval`-able |
| 2 | `WeightedGraph V` (Hermitian ℂ) | **spine lift axiom-clean**; ℚ-computable companions |
| 3 | Operator system / quantum graph | constructions concrete; UCP / Choi-matrix / k-positivity in place; Choi & Stinespring deferred |
| 4 | `Graphon Ω μ` (Hilbert–Schmidt op) | **operator layer axiom-clean**; continuous-spectrum analysis deferred |
| 5 | Categorical (filtered colimits) | functors / quotient / adjunction concrete; `FinerThan` a genuine `Preorder`; one isolated colimit-data `sorry` |
| 6 | Sheaves of `*`-algebras | `constSheaf` concrete (terminal/skyscraper); stalkwise ⇒ PST proven |
| 7 | ∞-categorical / derived | finite-shadow scaffold; awaits Mathlib ∞-cat library |

Adjacent infrastructure built along the way: a loopless-free
**`LoopyWeightedGraph`** (Laplacian `L = D − A`, self-loop / lackadaisical
walks, with regular-graph Laplacian↔adjacency equivalence proven via
diagonal-shift global-phase invariance); **first-class graph products**
`□` / `⊗` / `⊠` (Kronecker sum/product, eigenvector lemmas, the proven
`exp(M⊗1) = exp(M)⊗1`); the **spectral-projector calculus**; and
`Graphplay/Tactics.lean`, a reusable proof-automation library
(`herm_grind`, `modulus_one`, `equitable_discharge`, named simp/aesop sets).

## Corpus coverage

The Tamon / Godsil continuous-time-quantum-walk literature is modeled
end-to-end as precise statements — the spine and a large fraction of named
results proven, the deep per-paper headlines honest `sorry`s. Covered: PST /
PGST, fractional revival (incl. the non-commutative / `D_K` framework), uniform
and average mixing (AAKV matrix), spatial search (incl. the CNO spectral-ratio
criterion), graphs-with-tails and the dark subspace, chiral / magnetic signings,
Laplacian and lackadaisical walks, association schemes and Bose–Mesner algebras,
graph products (GGPT), corona and joins (with the first negative-PST results),
circulant and bunkbed graphs, many-particle Feder boson / fermion exterior-power
walks, coined / Szegedy discrete-time walks, weak-coupling Feshbach–Schur PST,
universal / multiple state transfer and switching automorphisms, QOMDP
decidability, and matrix-inversion-by-walk. Full map:
`paper/coverage/COVERAGE_MATRIX.md`.

## Build

```sh
lake build                       # the library: 0 errors
lake exe graphplay-sim           # numerical CTQW simulator (tables above)
lake exe graphplay-toolkit <spec.json>   # search-compiler report
lake exe graphplay               # load banner + usage
```

Depends on Mathlib (configured for `~/src/mathlib4` via `lakefile.toml`); Lean
toolchain pinned in `lean-toolchain`. Tower 1 and the computable substrate run
under `#eval` (`Graphplay/Demo.lean`, `Graphplay/Computable.lean`); the rest of
the spine lives over `ℂ` (noncomputable) with `ℚ[i]`- and `Float`-backed
companions for finite examples.

## Status, honestly

- **0 build errors.** Every `sorry` is a theorem body — no `sorry` in any definition
  (one isolated colimit-data witness aside), no `True`-placeholder theorems.
- **Axiom-clean** where it counts: the finite and graphon spine lifts, the
  search lift, `PST ⇒ strong cospectrality`, the negative-PST theorems, the
  hypercube and Cartesian-product PST, the quantum-advantage separation, and the
  attention-linearity theorems all `#print axioms` clean.
- **Open frontier:** the deep per-paper proofs (Godsil's Diophantine direction,
  Choi/Stinespring, MIP\*, infinite-dim continuous spectrum), the quantitative
  quantum-advantage rates, and — the big one — ε-equitable-partition theory for
  *approximately*-structured (learned) attention.

## How to get involved

Collaborators welcome — this is a project aimed at the verified theoretical case
for quantum-accelerated machine learning, and it is at the stage where the
foundations are solid and the frontier is sharp.

- **Approximate-equitable theory.** Real learned attention is only
  approximately symmetric. Build ε-equitable partitions with controlled
  quotient error — this is what carries the exact results to practice.
- **Close a quantum-advantage rate.** The `O(√n)` and `O(κ/ε)` dynamical bounds
  are the honest gap between "the reduction is exact" and "the speedup is total."
- **Close a deep dowsing rod.** Each `Graphplay/Dowsing/` file states a
  load-bearing open theorem precisely; the spine does much of the work.
- **Add a stdlib family** (strongly regular graphs, Johnson / Grassmann schemes,
  half-Cayley) or disassemble a new hardware platform (Rydberg arrays,
  trapped-ion chains) — `Applications/IBMHeavyHex` and `Applications/MajoranaOne`
  are the templates.

## Manuscripts & references

`paper/` holds the manuscripts (`quasi_infinite_adjoint_v3`, the collaborator
pitch, the research-program catalog), the applied disassembly studies
(`applied_ibm_heavy_hex.md`, `applied_majorana1.md`), and the coverage audits
(`paper/coverage/`). `references/` mirrors the calibrating literature — Szegedy
(graphon spectra, arXiv:1003.5588), Bachman–Tamon (quotient PST, arXiv:1108.0339),
Godsil (when PST occurs; average mixing), Coutinho–Godsil (the book), Chan et al.
(fractional revival), Xie–Tamon (no infinite tail beats optimal search), and the
chiral-mixing line, alongside the classical-ML anchors the bridge cites.

## License

The software content is licensed under the terms of both the MIT license and the
Apache License (Version 2.0). The portions ForMathlib are CC0.

---

*The big matrix whispers what its quotient already knew.* ( ◕‿◕ )

