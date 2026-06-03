# Graphplay

**The equitable-partition quotient of quantum walks, formalized in Lean 4.**

Read enough of the perfect-state-transfer / mixing / spatial-search literature
and one structure recurs: the dynamics collapse onto a small invariant subspace,
and the apparent miracle is a spectral condition on an `r × r` matrix whose size
is independent of the host. Graphplay mechanizes that collapse. The lift — host
dynamics hold *iff* the small symmetric quotient does — is a machine-checked
theorem, and a stdlib of named families, a numerical simulator, and an
inverse-design toolkit hang off it.

The library is ~100 Lean files and builds with zero errors.

## What's proven (axiom-clean)

The results below are `#print axioms`-clean: only `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx`, no custom axioms.

**The spine lift, finite and continuous.**
`EquitablePartition.cellUniformPST_iff_quotientPST` and
`GraphBundle.pst_iff_quotient`: cell-uniform perfect state transfer on a host
holds iff PST holds on its symmetric quotient `Q̃ = D^{1/2} Q D^{-1/2}`. The
graphon counterpart (`Graphon.cellUniformPST_iff_quotientPST`,
`op_restrict_eq_quotient`) is equally clean, including the Hilbert–Schmidt
`MemLp` closure (`kernelIntegralFun_memLp`). The same lift holds for mixing and
search (`cellUniformSearch_iff_quotientSearch`).

**Godsil's necessary condition.** `isPST_imp_isStronglyCospectral`: PST forces
strong cospectrality, via a from-scratch spectral-projector calculus
(`eigenProj`, `E² = E`, `E_λ E_μ = 0`, `U(τ) = Σ_λ e^{-iτλ} E_λ`) for arbitrary
Hermitian matrices — so it survives the chiral/complex case, where the
transferred phase is only unit-modulus, not ±1.

**The Godsil PST ⇔ ratio-condition bridge — under hypotheses.** Proven in both
directions *only* assuming the graph is real-symmetric (`IsSymm`) with full
eigenvalue support. The unconditional existence form is **false** (`K₂ ⊔ H` is a
counterexample); the forward direction is not unconditional and we do not claim
it as such.

**Machine-checked negative-PST theorems.** `dominatingVertex_no_PST`,
`cone_apex_no_PST`, `join_no_PST_within_G_of_not_cospectral`,
`pendantCorona_no_PST` — via `no_PST_of_not_cospectral`: a single eigenvalue with
unequal projector-diagonals certifies no transfer at any time.

**Named families, bottom-up.** The Christandl-et-al. hypercube antipodal PST at
`τ = π/2` (`isPST_hypercubeP_antipode`): Pauli-X exponential → `isPST_K2` →
Kronecker induction. Cartesian product preserves PST (`cartesianProduct_pst`) via
a proven `exp(M ⊗ 1) = exp(M) ⊗ 1`. The AAKV average-mixing matrix is
doubly-stochastic (`avgMixing_doublyStochastic`).

**A quadratic search separation, on `K_n`.** `quantum_search_quadratic_advantage`:
continuous-time quantum search on `K_n` reaches its target in `O(√n)` (an exact
2×2 Rabi reduction, invariant subspace and dynamics both proven), while any
classical algorithm needs `Ω(n)` (an adversary bound). Lifted through the
quotient-search reduction (`ml_structured_search_quantum_advantage`): a search
with an `r`-cell symmetry costs `O(√r)` quantum vs `Ω(r)` classical, independent
of host size. The quadratic speedup is inherited by the small quotient with a
proof the answer is identical.

## Structured attention reduces exactly

`Integrations/MachineLearning` turns an attention score matrix into a Hermitian
operator and proves that a symmetry of the attention pattern
(translation-invariant, block-structured, or weight-tied heads) induces a genuine
equitable partition (`equitableOfAutomorphism`) — so the operator reduces exactly
to a small `r × r` quotient (`multiHead_restrict_eq_symmQuotient`, delegating to
the spine). This is an exact symmetry reduction, not a rank bound on learned
attention.

`Integrations/AttentionComplexity` proves, axiom-clean, that for block-equitable
attention `A[i][j] = B[cell i][cell j]` the naive `O(n²·d)` apply *equals* an
`O(n·r·d)` algorithm (`blockAttentionApply_eq_fullAttentionApply`): the `n²`
entries are only `r²` distinct blocks, so the quadratic in sequence length
collapses to linear (`attention_apply_linear_in_n`), forward and backward
(`training_step_linear_under_equitable`).

The honest split: the symmetry reduction and its exactness are *proven* for
*exactly*-equitable attention. The quantitative quantum-advantage rates (`O(√n)`
search, `O(κ/ε)` inversion) are deep dynamical theorems still in progress. The
bridge from exactly-equitable to *approximately*-structured (learned) attention —
ε-equitable-partition theory with controlled quotient error — is open, and is the
intended direction.

## It runs

```sh
lake exe graphplay-sim
```

A `Float`-backed CTQW simulator (`exp(-iτH)` via scaling-and-squaring), printing
probability-vs-time tables:

- **Childs–Goldstone search on `K_16`** — success probability reaches `1.000000`
  at `t* = (π/2)√16 = 6.2832`, then decays.
- **Hypercube `Q_3` antipodal PST** — fidelity `1.000000` at `t = π/2`.
- **Chiral (magnetic-flux) walk** — clockwise transport bias `+0.99`, impossible
  for a real-symmetric walk.
- **Fractional revival** — partial revival to `α = 0.64` at the predicted time.
- **Lindblad dephasing** — purity decaying `1.0 → 0.37`.
- **Attention quotient match** — a 2-block softmax attention's symmetric-subspace
  dynamics equal its `2×2` quotient evolution to `~10⁻⁶`.

## It engineers

```sh
lake exe graphplay-toolkit examples/k4_equal_fiber.json
```

`Toolkit/InverseDesign.synthesizePST` runs the spine backwards: pick a small
quotient with the property you want, inflate it through an equitable bundle, and
the host inherits the property with a machine-checked certificate
(`engineered_host_has_PST`).

## The seven-tower spine

The universal object at every level is the equitable partition; the universal
operation is the quotient (a small finite Hermitian matrix); the universal
theorem is the lift. Deep external results (Choi, Stinespring, Villani strong
duality, BCLSV graphon limit, MIP\*=RE, FKLW, Lovász SDP duality, Birkhoff
contraction, HHL convergence) are honest **typeclass assumptions** — cited
hypotheses the conditioned results depend on, not theorems proven here.

| Tower | Object | Status |
|-------|--------|--------|
| 1 | `SimpleGraph V` | proven, computable, `#eval`-able |
| 2 | `WeightedGraph V` (Hermitian ℂ) | spine lift axiom-clean; ℚ-computable companions |
| 3 | Operator system / quantum graph | constructions concrete; UCP / Choi / k-positivity stated under cited assumptions |
| 4 | `Graphon Ω μ` (Hilbert–Schmidt op) | operator layer axiom-clean; continuous-spectrum analysis open |
| 5 | Categorical (filtered colimits) | functors / quotient / adjunction concrete; `FinerThan` a `Preorder`; one isolated colimit-data `sorry` |
| 6 | Sheaves of `*`-algebras | `constSheaf` concrete; stalkwise ⇒ PST proven |
| 7 | ∞-categorical / derived | finite-shadow scaffold; awaits Mathlib ∞-cat library |

Built along the way: a `LoopyWeightedGraph` (Laplacian `L = D − A`,
lackadaisical walks, regular-graph Laplacian↔adjacency equivalence proven);
graph products `□` / `⊗` / `⊠` with eigenvector lemmas and the proven
`exp(M⊗1) = exp(M)⊗1`; the spectral-projector calculus; and `Graphplay/Tactics.lean`
(`herm_grind`, `modulus_one`, `equitable_discharge`).

## Corpus coverage

The Tamon / Godsil CTQW literature is modeled as precise statements — the spine
and a large fraction of named results proven, the deep per-paper headlines honest
`sorry`s. Covered: PST / PGST, fractional revival (incl. the `D_K` framework),
uniform and average mixing (AAKV matrix), spatial search (incl. the CNO
spectral-ratio criterion), graphs-with-tails and the dark subspace, chiral /
magnetic signings, Laplacian and lackadaisical walks, association schemes and
Bose–Mesner algebras, graph products (GGPT), corona and joins (with negative-PST
results), circulant and bunkbed graphs, many-particle Feder boson/fermion walks,
coined / Szegedy discrete-time walks, weak-coupling Feshbach–Schur PST, universal
/ multiple state transfer, QOMDP decidability, and matrix-inversion-by-walk. Full
map: `paper/coverage/COVERAGE_MATRIX.md`.

## Hardware-disassembly studies — read these carefully

Two applied studies model named hardware but do **not** prove the topology their
names suggest:

- `Applications/IBMHeavyHex` formalizes a **complete-site subdivision `K_N`**
  carrying hardware labels. It is **not** the honeycomb degree-3 heavy-hex
  topology. The PST/quotient statements are about the `K_N` model, not the IBM
  lattice.
- `Applications/MajoranaOne` proves **only** the Hermiticity of a parity-projector
  Gram matrix. The earlier "spectral disassembly into a 2×2 effective Hamiltonian
  per tetron" was **retracted** and is not claimed.

## Build

```sh
lake build                       # the library: 0 errors
lake exe graphplay-sim           # numerical CTQW simulator
lake exe graphplay-toolkit <spec.json>
lake exe graphplay               # banner + usage
```

Depends on Mathlib (`~/src/mathlib4` via `lakefile.toml`); toolchain pinned in
`lean-toolchain`. Tower 1 and the computable substrate run under `#eval`
(`Graphplay/Demo.lean`, `Graphplay/Computable.lean`); the rest of the spine lives
over `ℂ` (noncomputable) with `ℚ[i]`- and `Float`-backed companions.

## Status, honestly

- **0 build errors.** No `sorry` in any definition (one isolated colimit-data
  witness aside); every other `sorry` is a theorem body.
- **Axiom-clean** where it counts: the finite and graphon spine lifts, the search
  lift, PST ⇒ strong cospectrality, the negative-PST theorems, the hypercube and
  Cartesian-product PST, the `K_n` search separation, and the attention-linearity
  theorems.
- **Conditioned, not proven:** the deep external results listed above are cited
  typeclass assumptions. The Godsil ratio-condition bridge holds only under
  `IsSymm` + full eigenvalue support.
- **Open:** the per-paper Diophantine direction, continuous-spectrum analysis, the
  quantitative quantum-advantage rates, and ε-equitable-partition theory for
  approximately-structured attention.

## How to get involved

- **Approximate-equitable theory.** Build ε-equitable partitions with controlled
  quotient error — this carries the exact results to learned attention.
- **Close a quantum-advantage rate.** The `O(√n)` and `O(κ/ε)` bounds are the gap
  between "the reduction is exact" and "the speedup is total."
- **Close a deep open theorem.** Each `Graphplay/Dowsing/` file states one
  precisely; the spine does much of the work.
- **Add a stdlib family** (strongly regular, Johnson / Grassmann schemes,
  half-Cayley).

## Manuscripts & references

`paper/` holds the manuscripts (`quasi_infinite_adjoint_v3`, the collaborator
pitch, the research-program catalog), the applied disassembly studies
(`applied_ibm_heavy_hex.md`, `applied_majorana1.md`), and the coverage audits.
`references/` mirrors the literature — Szegedy (arXiv:1003.5588), Bachman–Tamon
(arXiv:1108.0339), Godsil (when PST occurs; average mixing), Coutinho–Godsil (the
book), Chan et al. (fractional revival), Xie–Tamon.

## License

MIT and Apache 2.0. The portions ForMathlib are CC0.

---

*The big matrix whispers what its quotient already knew.* ( ◕‿◕ )
