# Graphplay

**The hidden quotient structure of quantum walks — formalized in Lean 4.**

For twenty years the Tamon group and adjacent literature have been
publishing theorems with the same shape: on *this* graph family, at *this*
time, with *this* signing, perfect state transfer or uniform mixing or
optimal spatial search emerges as if by analytic miracle. Read fifty such
theorems and the structure forces itself on you: every miracle factors
through an **equitable partition**, the dynamics restrict to a small
invariant subspace, and the apparent magic is a finite-dimensional
spectral condition on an `r × r` matrix where `r` is independent of host
size.

Graphplay names that structure — *the universal coarse-graining of
quantum-walk operators* — and mechanizes it across seven mathematical
settings (the **spine**), with a stdlib of named families, computable
companions over ℚ, two applied disassembly studies, and a research
program of eighteen open theorems.

The library currently spans 93 Lean files; `lake build` emits **zero
errors**. Two milestones now hold across the whole stack:

- **Every construction is real.** There is no `sorry` in any definition
  and no `True`-placeholder theorem anywhere — every graph family,
  operator, partition, channel, bundle, sheaf, and compiler pass is a
  concrete, fully-elaborated term. (One single irreducible exception: the
  filtered-colimit-preservation *data* witness `Quotient.mapCocone_isColimit`,
  honestly isolated.) The project also **builds two runnable executables**
  (`lake exe graphplay`, `lake exe graphplay-toolkit` — the latter compiles
  a real spec JSON into a search-compiler report).
- **The spine is machine-checked.** The finite equitable-partition → quotient
  → PST/mixing/search lift (Tower 2) *and* its graphon continuous-limit
  counterpart (Tower 4) are proven **end-to-end and axiom-clean** (`#print
  axioms` shows only `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`).

The remaining ~431 `sorry`s are now exclusively *theorem bodies* —
the deep per-paper results (Godsil existence via Dirichlet/Kronecker, Choi/
Stinespring, MIP*=RE, infinite-dimensional continuous-spectrum analysis,
association-scheme coincidences) — that the now-complete scaffolding sets
up precisely. **Constructions are done; the deep proofs are in progress.**

## The seven-tower spine

The universal object at every tower is the equitable partition; the
universal operation is `quotient = a small finite Hermitian matrix`. The
three load-bearing theorems repeat at every level:

1. `spec(quotient) ⊆ spec(host)`, with eigenvector lift.
2. PST / mixing / search / fractional revival lift from quotient to
   cell-uniform states.
3. (Tower 5) The Quotient functor preserves filtered colimits — the
   precise meaning of "quasi-infinite".

| Tower | Object                              | Status |
|-------|-------------------------------------|--------|
| 1     | `SimpleGraph V`                     | proven, computable, `#eval`-able |
| 2     | `WeightedGraph V` (Hermitian ℂ)     | **spine lift axiom-clean** (`cellUniformPST_iff_quotientPST`, `spec ⊆`); computable via ℚ companions |
| 3     | Operator system / quantum graph     | all constructions concrete; UCP/Choi/k-positivity in place; deep analytic theorems (Choi, Stinespring) deferred |
| 4     | `Graphon Ω μ` (Hilbert–Schmidt op)  | **operator layer axiom-clean** (`op_restrict_eq_quotient`, graphon `cellUniformPST_iff_quotientPST`, `evolve` group laws, HS `MemLp` closure); continuous-spectrum analysis deferred |
| 5     | Categorical (filtered colimits)     | functors/quotient/adjunction concrete; `FinerThan` is a genuine `Preorder` (lattice axioms shown false at full generality); colimit-preservation data the lone isolated `sorry` |
| 6     | Sheaves of `*`-algebras             | `constSheaf` concrete (terminal/skyscraper); stalkwise⇒PST proven |
| 7     | ∞-categorical / derived             | statement-level scaffold; finite-shadow predicates; awaits Mathlib ∞-cat library |

Adjacent to the towers, three new infrastructure layers were added: a
**loopless-free `LoopyWeightedGraph`** (Laplacian `L = D−A` and self-loop /
lackadaisical walks, with regular-graph Laplacian↔adjacency equivalence
proven via diagonal-shift invariance), **first-class graph products**
`□`/`⊗`/`⊠` (Kronecker-sum/product with eigenvector lemmas, the
genuinely-proven `exp(M⊗1)=exp(M)⊗1` factorization, and a machine-checked
**hypercube antipodal PST** at `τ=π/2` built from first principles), and a
reusable **proof-automation library** (`Graphplay/Tactics.lean`: custom
tactics `herm_grind`/`modulus_one`/`loopless_grind`/`equitable_discharge`,
named simp/aesop rule-sets, 18 proven helper lemmas).

## Entry points by audience

- **Curious newcomer** — `paper/graphplay_pitch.pdf` (6 pages: what it
  is, why it matters, why you might care).
- **Mathematician** — `paper/quasi_infinite_adjoint_v3.pdf` (16 pages:
  the main manuscript, equitable spine + graphon limit + chiral signing
  + categorical filtered-colimit theorem).
- **Research-program reader** — `paper/research_program.pdf` (13 pages:
  catalog of the eighteen dowsing-rod theorems and eight integrations).
- **Hardware engineer** — `paper/applied_majorana1.md` and
  `paper/applied_ibm_heavy_hex.md` (worked spectral-disassembly studies
  of Microsoft's Majorana-1 chip and IBM's heavy-hex lattice).
- **Lean-curious** — `Graphplay/Demo.lean` (Heawood graph colored on the
  torus, end-to-end, `#eval`-able) and `Graphplay/StdLib/` (named
  families with PST certificates).
- **Mathlib contributor** — `Graphplay/OperatorSystem.lean` is the
  cleanest upstream candidate: operator systems, k-positivity, UCP maps,
  Choi-matrix characterization — no Mathlib dependency cycle.
- **Cross-disciplinary reader** — `Graphplay/Integrations/` has bridges
  to TQFT, RMT, MERA, optimal transport, Hodge theory, lattice gauge,
  Weisfeiler–Leman, and mean-field games.

## Computability

Lean's `Complex` is a `noncomputable Field`, so general spectral
arithmetic does not `#eval`. Graphplay handles this honestly:

- Tower 1 (`SimpleGraph`) — fully decidable, `#eval` works.
- Tower 2+ statements live over `ℂ` and are noncomputable.
- `Graphplay/Computable.lean` provides `GaussianRat = ℚ[i]` with
  computable ring operations, matrix multiply, trace, determinant, and
  Gauss–Jordan inverse — the exact substrate for spectra algebraic over
  ℚ at dimensions ≤ 8.
- `Graphplay/Computable/Float.lean` provides a `Float`-backed
  approximate companion for larger numerical exploration.
- `Graphplay/Demo.lean` runs an end-to-end coloring of the Heawood graph
  on the torus, demonstrating the full pipeline on a real example:
  `#eval Graphplay.Demo.heawoodColorCount`.
- `Graphplay/CombinatorialMap.lean` gives the genus-bounded embedding
  primitives the demo and the applied studies depend on.

## Directory tour

### Core spine

- `Graphplay/Basic.lean` — Tower 1: indexed coproducts, edge-union,
  inverse-limit threads, template joins.
- `Graphplay/Weighted.lean`, `Equitable.lean`, `Spectral.lean` — Tower 2
  Hermitian complex adjacency, equitable partitions, quotient spectrum.
- `Graphplay/Bundle.lean`, `PST.lean`, `Mixing.lean`, `Search.lean` —
  constructive bundle engine and three classical lift primitives.
- `Graphplay/Loopy.lean`, `Loopy/Laplacian.lean`, `Loopy/Search.lean` —
  loopless-free Hermitian graphs: Laplacian `L = D−A`, self-loop /
  lackadaisical walks, and the regular-graph Laplacian↔adjacency
  walk/search equivalence (via diagonal-shift global-phase invariance).
- `Graphplay/Product.lean`, `Product/PST.lean` — first-class Cartesian
  `□` / tensor `⊗` / strong `⊠` products (Kronecker sum/product), the
  `exp(M⊗1)=exp(M)⊗1` factorization, and the GGPT Cartesian-product PST
  theorem (`StdLib/HypercubeProduct.lean` derives `Q_n` antipodal PST).
- `Graphplay/PST/DiagonalShift.lean` — CTQW amplitudes are invariant under
  scalar diagonal shifts of the Hamiltonian (global phase).
- `Graphplay/Tactics.lean`, `TacticsInit.lean` — proof-automation library:
  `herm_grind`, `modulus_one`, `loopless_grind`, `equitable_discharge`,
  named simp/aesop rule-sets, and 18 proven helper lemmas.
- `Graphplay/Chiral.lean` — magnetic / chiral signings.
- `Graphplay/QuantumGraph.lean`, `OperatorSystem.lean` — Tower 3
  operator systems, UCP maps, Choi matrices.
- `Graphplay/Graphon.lean`, `Graphon/{Equitable,PST,Limit,LimitReverse,Spectrum,Lindblad}.lean`
  — Tower 4 graphon limits and cell-uniform spectral identities
  (Szegedy 1003.5588; BCLSV).
- `Graphplay/Categorical.lean`, `Categorical/Topos.lean` — Tower 5
  `Quotient : WGraphP ⥤ WGraph`, `preservesFilteredColimits`, the
  universal Xie–Tamon statement.
- `Graphplay/Tower6.lean` — sheaves of unital `*`-algebras over a base
  space.
- `Graphplay/Tower7.lean` — ∞-categorical / derived scaffold
  (statements only).
- `Graphplay/Relational.lean` — Tower 1.5: `k`-ary CSP / hypergraph
  relational layer.

### PST foundations (γ-loop L1, L2, L3)

- `Graphplay/PST/Cospectrality.lean` — cospectral vertex pairs.
- `Graphplay/PST/GodsilRatio.lean` — Godsil's ratio condition.
- `Graphplay/PST/QuotientIff.lean` — quotient-level iff for PST.

### Algorithms (γ-loops L4, L6 + β)

- `Graphplay/Algorithm/WLRefinement.lean` — Weisfeiler–Leman refinement.
- `Graphplay/Algorithm/WLOrbit.lean` — orbit partition.
- `Graphplay/Algorithm/ChiralOpt.lean` — chiral-signing optimization.
- `Graphplay/Algorithm/StdLibMatch.lean` — match host to a stdlib entry.
- `Graphplay/Algorithm/PrimitiveDSL.lean` — end-to-end compiler DSL.

### Stdlib of named families — `Graphplay/StdLib/`

- `Path.lean` — paths `P_n`, including Christandl–Datta–Ekert–Landahl
  engineered weighted paths.
- `Hypercube.lean` — `Q_n` with the Möbius PST protocol.
- `Hamming.lean` — Hamming schemes and their Bose–Mesner algebras.
- `Cayley.lean` — abelian Cayley graphs and the
  Bašić–Petković–Stevanović characterization.
- `CompleteMultipartite.lean` — `K_{n_1,…,n_k}` quotients.

### Dowsing rods — `Graphplay/Dowsing/`

The eighteen-rod research program: each file states a load-bearing open
theorem precisely; proofs are deferred.

- `BundlePSTLift.lean` — bundle-level PST lifting from fibers.
- `ChiralBundlePST.lean` — chiral signing through a bundle (D1).
- `Conjecture93.lean` — Conjecture 9.3 of the v3 manuscript (D2).
- `ChiralGraphon.lean` — chiral signings on graphons (D3).
- `CoherentAlgebra.lean` — coherent algebra ↔ equitable partition (D4).
- `NonCommutativeCoherent.lean` — non-commutative coherent algebras (D5).
- `FractionalRevivalNC.lean` — fractional revival on non-commutative
  coherent algebras (D6).
- `HypergraphPST.lean` — hypergraph CTQW models and PST (D7).
- `NoiseEquitable.lean` — equitable structure under noise channels (D8).
- `FilteredColimitPST.lean` — generalized filtered-colimit PST (D9).

Companion notes: `paper/conjecture93_notes.md` (Conjecture 9.3 working
notes) and `paper/qri_dmt_coloring_review.md` (a QRI bridge review).

### Integrations — `Graphplay/Integrations/`

Eight cross-framework bridges connecting the spine to neighboring
formalisms.

- `TQFT.lean` — modular tensor categories, anyon sectors, Heawood
  envelopes.
- `RMT.lean` — random matrix theory and free probability; random
  graphons with deterministic equitable spectra.
- `TensorNetworks.lean` — MERA coarse-graining as equitable cell maps;
  PEPS; holographic codes.
- `OptimalTransport.lean` — Wasserstein geometry of graphons; Sinkhorn
  reweighting.
- `MeanFieldGames.lean` — graphon LQR control (Gao–Caines) and quantum
  mean-field games via cell-uniform invariant subspaces.
- `Hodge.lean` — combinatorial Hodge decomposition; persistent Hodge /
  TDA hooks.
- `LatticeGauge.lean` — chiral signings as discrete U(1) (and
  non-abelian) lattice gauge connections.
- `WLRefinement.lean` — WL refinement as equitable saturation; quantum
  isomorphism hooks.

### Engineering toolkit — `Graphplay/Toolkit/`

- `Spec.lean` — JSON spec parser → symbolic `WeightedGraph (Fin n)` with
  regularity certificates.
- `Bundle.lean` — fiber-partition certificate construction.
- `Report.lean` — markdown report emitter with machine-readable
  certificate manifest.
- `Hardware.lean` — hardware-constraint vocabulary.
- `Noise.lean` — noise-channel composition primitives.
- `Scheduler.lean` — compilation pipeline scheduler.

### Applied disassembly — `Graphplay/Applications/`

- `IBMHeavyHex.lean` — heavy-hexagonal lattice (Eagle, Heron, Osprey,
  Condor), bipartite-flag-qubit structure, planar embedding.
- `MajoranaOne.lean` — Microsoft's Majorana-1 topological-qubit chip
  (stretch demo from the public design).

Both files have companion markdown narratives in `paper/applied_*.md`.

## Build

```sh
lake build
```

Depends on Mathlib (configured for `~/src/mathlib4` via `lakefile.toml`).
Lean toolchain pinned in `lean-toolchain`.

Build the manuscripts:

```sh
typst compile paper/quasi_infinite_adjoint_v3.typ
typst compile paper/graphplay_pitch.typ
typst compile paper/research_program.typ
```

Run the executables:

```sh
lake exe graphplay                          # load banner + toolkit usage
lake exe graphplay-toolkit examples/k4_equal_fiber.json   # → search-compiler report
```

Try the demos:

```lean
#eval Graphplay.Demo.heawoodColorCount
-- and other #eval lines in Graphplay/Demo.lean and Graphplay/Computable.lean
```

## Status (honest)

- **0 errors**, **~431 `sorry` warnings** (all on theorem bodies), 93 Lean
  files. Down from ~634; the entire reduction was **eliminating every
  `sorry` in a definition** (152 → 1 irreducible) and every `True`-placeholder
  theorem (→ 0) — so what remains is genuinely "prove this true statement",
  never "this object isn't built yet".
- **Runnable.** `lake build` produces working executables; `lake exe
  graphplay` and `lake exe graphplay-toolkit <spec.json>` both run.
- Tower 1 is proven and `#eval`-able.
- **Tower 2 spine is axiom-clean end-to-end**: `spec(quotient) ⊆ spec(host)`,
  the cell-uniform/quotient PST iff (`QuotientIff.cellUniformPST_iff_quotientPST`),
  the bundle PST lift (`GraphBundle.pst_iff_quotient`), the Cartesian-product
  PST theorem, and the hypercube antipodal-PST theorem all `#print axioms`
  clean. ℚ-backed companions make finite examples runnable.
- **Tower 4 graphon operator layer is axiom-clean**: the Hilbert–Schmidt
  `MemLp 2` closure (the one genuinely-hard Mathlib analytic gap) is proven,
  `W.op` is self-adjoint with real spectrum, `op_restrict_eq_quotient` and the
  graphon `evolve` group laws hold, and the graphon `cellUniformPST_iff_quotientPST`
  / mixing / search headlines are clean. Infinite-dimensional continuous-spectrum
  facts (Reed–Simon decomposition, HS compactness) remain deferred.
- Tower 3 (operator systems, UCP/Choi) — all constructions concrete; deep
  analytic theorems (Choi's theorem, Stinespring dilation) deferred.
- Towers 5–7 — all constructions concrete; one isolated colimit-preservation
  data `sorry` (Tower 5); Tower 7 a finite-shadow scaffold awaiting Mathlib.
- The remaining theorem-`sorry`s are concentrated in the dowsing files
  (deep open conjectures), the integration files (cross-framework deep
  results), and the infinite-dimensional/association-scheme analytic layers.
  These are deliberate research handles, not bugs — and a `Graphplay/Tactics.lean`
  automation layer + the now-axiom-clean lifts make the next proving pass tractable.

## How to contribute

Pick one:

- **Close a dowsing rod.** Each file in `Graphplay/Dowsing/` is
  self-contained. Start with `BundlePSTLift` (closest to landing) or
  `Conjecture93` (highest payoff).
- **Add a stdlib family.** Strongly regular graphs, Johnson schemes,
  Grassmann schemes, half-Cayley graphs, and the Diaconis–Holmes
  swap-Markov family are all missing from `Graphplay/StdLib/`.
- **Upstream operator systems.** `Graphplay/OperatorSystem.lean` is the
  cleanest candidate for Mathlib contribution; the UCP-map and Choi-matrix
  layer is largely absent upstream.
- **Pick a hardware platform and disassemble it.** Rydberg arrays,
  trapped-ion chains, photonic Boson samplers, neutral-atom processors
  are all open. Use `Applications/IBMHeavyHex.lean` and
  `Applications/MajoranaOne.lean` as templates.
- **Mechanize an integration.** `Integrations/WLRefinement.lean` and
  `Integrations/RMT.lean` have the highest density of concrete
  statements awaiting proof.

## Reading the spine in code

For the universal lift theorem from first principles:

```
Graphplay/Weighted.lean    →  WeightedGraph definition
Graphplay/Equitable.lean   →  equitable partition + characteristic matrix
Graphplay/Spectral.lean    →  spec(A/π) ⊆ spec(A)
Graphplay/PST.lean         →  PST lift
Graphplay/Bundle.lean      →  bundle = canonical fiber partition
Graphplay/Categorical.lean →  Quotient.preservesFilteredColimits
```

For the graphon limit:

```
Graphplay/Graphon.lean             →  measurable kernel, Hilbert–Schmidt operator
Graphplay/Graphon/Equitable.lean   →  measurable equitable partition
Graphplay/Graphon/Spectrum.lean    →  spectral identity
Graphplay/Graphon/Limit.lean       →  finite ⟶ graphon convergence
Graphplay/Graphon/PST.lean         →  PST in the graphon limit
```

## Manuscripts

- `paper/quasi_infinite_adjoint_v3.{typ,pdf}` — main paper (16 pages).
- `paper/quasi_infinite_adjoint{,_v2}.{typ,pdf}` — earlier drafts kept
  for citation continuity.
- `paper/graphplay_pitch.{typ,pdf}` — 6-page collaborator pitch.
- `paper/research_program.{typ,pdf}` — 13-page open-problem catalog.
- `paper/spine_outline.md` — working spine index.
- `paper/conjecture93_notes.md` — Conjecture 9.3 working notes.
- `paper/applied_{majorana1,ibm_heavy_hex}.md` — applied disassembly
  studies.
- `paper/qri_dmt_coloring_review.md` — QRI bridge review.

## References

Nineteen arXiv PDFs plus extracted plain-text mirrors live in
`references/`. The calibrating reading list is:

- Szegedy, *Spectra of graphons and graph limits*, arXiv:1003.5588.
- Bachman et al., *PST on quotient graphs*, arXiv:1108.0339.
- Chan–Coutinho–Tamon–Vinet–Zhan, *Fractional revival and association
  schemes*, arXiv:1907.04729.
- Ide–Narimatsu, *Equitable-partition spatial search*, arXiv:2209.07688.
- Chan–Godsil–Tamon–Xie, *Spectral gap criterion for transfer*,
  arXiv:2204.04355.
- Bick–Sclosa, *Graphon dynamical systems and invariant subspaces*,
  arXiv:2110.13686.
- Xie–Tamon, *No infinite tail beats optimal spatial search*,
  arXiv:2301.07251.
- Levine–Mesapam–Mustico–Tamon–Tucker–Zhan, *Uniform mixing speedup via
  chiral signings*, arXiv:2605.04414.
- Duan–Severini–Winter, *Zero-error communication via quantum channels*,
  arXiv:1002.2514.
