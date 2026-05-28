# graphplay

**A combinatorial assembly language for quantum-walk-shaped problems.**

Graphplay is a typed, polymorphic, verified, categorically-organized
combinator calculus for compiling quantum-primitive specifications — perfect
state transfer (PST), mixing, search, sampling, transfer, fractional
revival — to host operators (simple graphs, weighted graphs, quantum graphs,
graphons), with proven correctness certificates. The instruction set has
eight primitives — `PARTITION`, `QUOTIENT`, `BUNDLE`, `SIGN`, `REFINE`,
`LIFT`, `COLIMIT`, `EMBED` — and the operands range over a five-tower spine
(set, simple graph, weighted/chiral, operator algebra / coherent algebra,
graphon, categorical / filtered-colimit), with two further towers
(sheaf-valued, ∞-categorical) for higher abstraction. The single
load-bearing theorem at every tower is the same:

> `spec(quotient) ⊂ spec(host)`, lifting PST / mixing / search across
> equitable partitions, bundle assemblies, signings, filtered colimits, and
> graphon limits.

## What's in the repo

### The spine — `Graphplay/`

- `Basic.lean` — original combinatorial core (Tower 1: indexed coproducts,
  edge-union, inverse-limit threads, color-completion, template joins).
- `Weighted.lean`, `Equitable.lean`, `Spectral.lean` — Tower 2 spine
  (Hermitian complex adjacency, equitable partitions, quotient spectrum).
- `Bundle.lean`, `PST.lean`, `Mixing.lean`, `Search.lean` — constructive
  bundle engine and the three classical lift primitives.
- `Chiral.lean`, `QuantumGraph.lean` — Tower 3 (magnetic / chiral signings,
  operator-system / coherent-algebra hosts).
- `Graphon.lean`, `Graphon/{Equitable,PST,Limit}.lean` — Tower 4 graphon
  limits and the cell-uniform spectral identity
  (Szegedy 1003.5588; BCLSV).
- `Categorical.lean` — Tower 5 (`Quotient : WGraphP ⥤ WGraph`,
  `preservesFilteredColimits`, the universal Xie–Tamon statement).
- `Relational.lean` — Tower 1.5: `k`-ary CSP / hypergraph relational layer.
- `Tower6.lean` — operator-algebra-valued sheaves over a base space.
- `Tower7.lean` — bicategorical / ∞-categorical scaffold (statements only;
  awaits Mathlib quasicategory + derived-category libraries).

### Dowsing rods — `Graphplay/Dowsing/`

Ten open-theorem files, each a hole or extension surfaced by the Tamon
corpus and adjacent literature. Statements are precise; almost all proofs
are deferred.

- `BundlePSTLift.lean` — bundle-level PST lifting from fibers.
- `ChiralBundlePST.lean` — chiral signing through a bundle.
- `ChiralGraphon.lean` — chiral signings on graphons.
- `CoherentAlgebra.lean` — Bose–Mesner / coherent-algebra hosts.
- `Conjecture93.lean` — Conjecture 9.3 of the paper (graphon limit +
  chiral speedup ⇔ algebra equality).
- `FilteredColimitPST.lean` — PST through filtered colimits (Tower 5).
- `FractionalRevivalNC.lean` — fractional revival on non-commutative
  coherent algebras (cf. Chan–Coutinho–Tamon–Vinet–Zhan 1907.04729).
- `HypergraphPST.lean` — hypergraph CTQW models and PST.
- `NoiseEquitable.lean` — equitable structure under noise channels.
- `NonCommutativeCoherent.lean` — non-commutative coherent-algebra theory.

### Integrations — `Graphplay/Integrations/`

Eight framework bridges connecting the spine to neighbouring formalisms.

- `TQFT.lean` — modular tensor categories, anyon sectors, Heawood envelopes.
- `RMT.lean` — random matrix theory and free probability (random graphons
  with deterministic equitable spectra).
- `TensorNetworks.lean` — MERA / PEPS / holographic codes; coarse-graining
  layers as equitable cell maps.
- `OptimalTransport.lean` — Wasserstein geometry of graphons.
- `MeanFieldGames.lean` — mean-field games on graphon hosts.
- `Hodge.lean` — combinatorial Hodge theory on the relational tower.
- `LatticeGauge.lean` — lattice gauge theory through chiral signings.
- `WLRefinement.lean` — Weisfeiler–Leman refinement as equitable saturation.

### Engineering layer — `Graphplay/Toolkit/`

The Lean replacement for the original Python compiler. Top-level entry in
`Toolkit.lean`.

- `Spec.lean` — JSON spec parser → symbolic `WeightedGraph (Fin n)` with
  attached regularity certificates.
- `Bundle.lean` — fiber-partition certificate construction.
- `Report.lean` — markdown report emitter with a certificate manifest
  appendix.
- `Hardware.lean` — exploratory hardware-constraint vocabulary.
- `Noise.lean` — noise-channel composition primitives.
- `Scheduler.lean` — compilation pipeline scheduler.

### Companion artifacts

- `paper/` — `quasi_infinite_adjoint{,_v2,_v3}.typ` manuscripts; the v3 §9
  *Research Program* lays out the ten dowsing-rod holes and the
  transfer-side companion plan. `spine_outline.md` is the working spine
  index.
- `references/` — 19 arXiv PDFs plus extracted plain-text mirrors covering
  the Tamon corpus and adjacent literature.
- `examples/`, `reports/`, `tools/search_compiler.py` — the legacy Python
  search compiler and its sample specs / output reports. Being replaced by
  `Graphplay.Toolkit`.

## Build

```sh
lake build
```

Depends on Mathlib (currently expected at `~/src/mathlib4`). Lean toolchain
pinned in `lean-toolchain`.

Build the manuscript:

```sh
typst compile paper/quasi_infinite_adjoint_v3.typ paper/quasi_infinite_adjoint_v3.pdf
```

Run the legacy Python compiler on an example (until the Lean toolkit
takeover is complete):

```sh
python3 tools/search_compiler.py examples/rook_3x3_equal_fiber.json \
  --report reports/rook_3x3_equal_fiber.md
```

## Status

- ~98% of the 43 Lean modules build green.
- The remaining gaps are almost entirely `sorry` holes — *statements* are
  precise; *proofs* are deferred. A small number of files (mainly in
  `Dowsing/` and `Tower7`) are still iterating on signatures.
- The certificate manifest emitted by `Graphplay.Toolkit.Report` makes the
  proven / unproven split machine-readable.

## Tamon-corpus integration

The spine is calibrated against this core reading list:

- Szegedy, *Spectra of graphons and graph limits.* arXiv:1003.5588.
- Bachman, Fratkin, Hayes, Knapp, Madsen, Tamon, *Perfect state transfer
  on quotient graphs.* arXiv:1108.0339.
- Chan, Coutinho, Tamon, Vinet, Zhan, *Fractional revival and association
  schemes.* arXiv:1907.04729.
- Ide, Narimatsu, *Equitable-partition spatial search.* arXiv:2209.07688.
- Chan, Godsil, Tamon, Xie, *Spectral gap criterion for transfer.*
  arXiv:2204.04355.
- Bick, Sclosa, *Graphon dynamical systems and invariant subspaces.*
  arXiv:2110.13686.
- Xie, Tamon, *Tail-transfer infinite-tail optimality.* arXiv:2301.07251.
- Bernard, Tamon, Vinet, Xie, *Tails and transfer.* (Companion note;
  forthcoming in the v3 manuscript bibliography.)

## Reading guide

- **Compiler / engineering angle:** start at `Graphplay/Toolkit.lean`, then
  `Toolkit/Spec.lean` and `Toolkit/Bundle.lean`.
- **Lift theorems, classical:** `Graphplay/Equitable.lean` →
  `PST.lean` → `Mixing.lean` → `Search.lean`.
- **Bundles and the eight-instruction view:** `Graphplay/Bundle.lean`,
  then `paper/quasi_infinite_adjoint_v3.typ` §§3–7.
- **Graphon limits:** `Graphplay/Graphon/Limit.lean` and the
  companion `paper/spine_outline.md`.
- **Categorical / filtered-colimit headline:** `Graphplay/Categorical.lean`
  (`Quotient.preservesFilteredColimits`, `quasi_infinite_limit`).
- **Open problems:** any file in `Graphplay/Dowsing/`; each one is
  self-contained.
- **Cross-field bridges:** any file in `Graphplay/Integrations/`.

## What's next

The research program — open problems, planned applied spectral-disassembly
case studies (e.g. IBM heavy-hex, Majorana-mode arrays), and the
transfer-side companion to the v3 manuscript — is laid out in
`paper/quasi_infinite_adjoint_v3.typ` §9 *Research Program*. The dowsing
rods in `Graphplay/Dowsing/` are the actionable surface of that plan; the
toolkit in `Graphplay/Toolkit/` is the engineering surface.
