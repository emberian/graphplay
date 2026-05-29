# Adjacent literature — acquisition + proof-leverage assessment

Literature fetched for Graphplay, prioritized by ability to *prove* (not merely
cite) the stated-but-sorried PST/cospectrality layer (`Graphplay/PST/`) and to
supply rigor for the upper towers. All new files live in `references/`.
Existing Tamon corpus (1108.0339, 1009.1340, 1907.04729, 2204.04355, 2301.07251,
2605.04414, 2209.08160, 2211.14704, 2512.08141, …) was NOT re-fetched.

The dominant finding: the entire `Graphplay/PST/Cospectrality.lean` +
`Graphplay/PST/GodsilRatio.lean` sorry-set is the content of **Coutinho's 2014
thesis, Chapter 2** plus **Godsil 2012 (1011.0231)**. We now hold the actual
proofs, not just the statements.

---

## Tier 1 — proof techniques for the PST / cospectrality layer

### Coutinho, *Quantum State Transfer in Graphs*, PhD thesis, U. Waterloo 2014 [`references/coutinho_thesis_2014.pdf` / `.txt`]
**What it contains:** The canonical graduate-level development of PST. Chapter 2
gives full proofs of: eigenvalue support `Φ_u` (§2.2), the cospectral ⇔ parallel
⇔ strongly-cospectral equivalence (Thm 2.5.1, Cor 2.5.2/2.5.3), the
quadratic-integer eigenvalue constraint (§2.3–2.4, incl. Godsil Thm 6.1 = Thm
2.4.3), the minimum-PST-time formula (Thm 2.4.4), and the algebra of spectral
idempotents `E_r` via `f(M)=∑f(θ_r)E_r` (Thm 2.1.6). Later chapters: distance-
regular graphs (Ch. 3), graph products/covers (Ch. 4), Laplacian PST (Ch. 7).
**How it helps graphplay:** *Supplies the proof technique* for nearly every
sorry in the PST layer.
- `isStronglyCospectral_iff` (`PST/Cospectrality.lean:168`) = thesis Cor 2.5.2 +
  Thm 2.5.1 (the cospectral-and-parallel decomposition; Cauchy–Schwarz
  saturation is exactly their "parallel" condition).
- `IsStronglyCospectral.symm/.refl/.of_aut` (`Cospectrality.lean:403/416/427`)
  are the easy lemmas in §2.5 (automorphism ⇒ parallel is their Lemma feeding
  Cor 2.5.3).
- `isPST_exists_iff_strongCospectral_and_godsilRatio` (`GodsilRatio.lean:239`)
  and `IsStronglyCospectral.isPST_iff_godsilRatio` (`Cospectrality.lean:228`):
  the forward half is thesis Prop 2.4.1; the eigenvalue-ratio/quadratic-integer
  structure is Thm 2.4.2/2.4.3.
- `pathEndpoints_isPST_iff` / `isPST_exists_path_iff` (Niven step): the cosine
  eigenvalue analysis is in Ch. 2's worked examples.
- The min-time and `IsGodsilRatio.ratios_rational` (`GodsilRatio.lean:189`)
  reformulation are Thm 2.4.4 and §2.4 directly.

### Godsil, "When can perfect state transfer occur?", arXiv:1011.0231 (Electron. J. Linear Algebra 23, 2012) [`references/1011.0231.pdf` / `.txt`]
**What it contains:** Proves that if PST occurs the spectral radius (more
precisely each supported eigenvalue, with ≤1 exception) is an integer or
quadratic irrational; finiteness of PST graphs of bounded valency; the
ratio-condition obstruction on the unit circle.
**How it helps graphplay:** *Proof technique* for the backward (Diophantine)
half of `isPST_exists_iff_strongCospectral_and_godsilRatio` and for the
quadratic-integer classification used by `isPST_exists_path_iff`
(`GodsilRatio.lean:302`, the `(n+1)∣6` / Niven corollary) and
`isPST_hypercube_antipode`. This is the primary source the GodsilRatio file
header already cites; we now have it locally.

### Coutinho & Godsil, "Perfect state transfer is poly-time", arXiv:1606.02264 (2021) [`references/1606.02264.pdf` / `.txt`]
**What it contains:** A classical poly-time decision algorithm for PST, built on
a constructive, finitary restatement of strong cospectrality + the ratio
condition (avoiding transcendence assumptions).
**How it helps graphplay:** *Supplies a decidable/algebraic reformulation* that
makes `eigenSupport` / `IsGodsilRatio` (`Cospectrality.lean:197`,
`GodsilRatio.lean:154`) computable rather than analytic — useful if those
predicates are to be `Decidable` or extracted. Secondary to the thesis for pure
proof leverage; primary if we want executable witnesses.

### Coutinho, Godsil, Guo, Vanhove, "Perfect state transfer on distance-regular graphs and association schemes", arXiv:1401.1745 (2015) [`references/1401.1745.pdf` / `.txt`]
**What it contains:** Necessary-and-sufficient PST criteria inside association
schemes / DRGs (Bose–Mesner algebra: PST iff a specific eigenvalue/idempotent
arithmetic condition), with new PST examples.
**How it helps graphplay:** *Supplies statements to capture* for the
Bose–Mesner / fractional-revival work — gap-map item #16 (Hamming/Kummer FR in
`Dowsing/FractionalRevivalNC.lean`) and the DRG specializations of the abelian-
Cayley corollary (`GodsilRatio.lean:356`). It is the scheme-theoretic home for
the quotient-of-vertex-transitive constructions behind phantom symmetry
(`exists_phantomSymmetric_isPST`).

### Godsil, "State Transfer on Graphs" (survey), arXiv:1102.4898 (2012/2017) [`references/1102.4898.pdf` / `.txt`]
**What it contains:** Broad survey of PST: cospectrality, periodicity,
integrality, products, covers, open problems.
**How it helps graphplay:** *Rigor/citation + roadmap.* Cleaner one-page proofs
of several thesis lemmas; good source text for the GodsilRatio/Cospectrality
docstrings and for prioritizing the cluster-1 gap list. Lower proof-leverage
than the thesis (it is a survey) but high orientation value.

---

## Tier 2 — operator-valued graph limits (Towers 4–6 rigor)

### Backhausz & Szegedy, "Action convergence of operators and graphs", arXiv:1811.00626 (Canad. J. Math. 2022) [`references/1811.00626.pdf` / `.txt`]
**What it contains:** The **graphop** framework: graphs/graphons/graphings are
all *self-adjoint positivity-preserving P-operators* `L^∞(Ω)→L^1(Ω)`; a unified
"action convergence" limit with a compactness theorem; graphops represented by
symmetric finite measures on `Ω²`.
**How it helps graphplay:** *Supplies the rigorous home* for the graphon/sheaf
operator side (`Graphplay/Graphon/PST.lean`, the `GraphonGodsilOpen` stub at
`GodsilRatio.lean:512`). The self-adjoint P-operator is the correct abstraction
under which our finite symmetric quotient `Q̃` and the graphon adjacency
operator `T_W` are one object — this is the citation/definition that makes the
"quasi-infinite adjoint" paper rigorous. Pairs with Mathlib's compact
self-adjoint spectral theorem (see below) for the spectral-measure analogue of
eigenvalue support.

### Kunszenti-Kovács, Szegedy et al., "Limits of action convergent graph sequences with unbounded (p,q)-norms", arXiv:2210.10720 (2022) [`references/2210.10720.pdf` / `.txt`]
**What it contains:** Companion extending graphop action-convergence to
unbounded-degree / unbounded-norm sequences.
**How it helps graphplay:** *Rigor/citation only* for now — relevant once the
Tower-6 operator limits must handle unbounded (e.g. infinite-tail / Jost) cases
from cluster-2 (`search_infinite_tail`).

---

## Tier 3 — search foundations + quantum homomorphisms (gap-map)

### Chakraborty, Novo & Roland, "On the optimality of spatial search by continuous-time quantum walk", arXiv:2004.12686 (Phys. Rev. A 2020) [`references/2004.12686.pdf` / `.txt`]
**What it contains:** **The necessary-and-sufficient condition** for CTQW
spatial search to be Grover-optimal: closed-form optimal-`r`, max amplitude, and
hitting time in terms of the Hamiltonian spectrum (gap `Δ` vs. overlap of the
marked state with the principal eigenvector); recovers all prior instance-
specific optimality results (complete graph, hypercube, SRG, complete
bipartite, high-dim lattices, cluster-partitioned graphs).
**How it helps graphplay:** *Supplies the proof technique AND statement* for the
single highest-leverage missing theorem — gap-map item **#1**, the CNO
spectral-ratio optimal-search theorem (`Search/CNO.lean`, SUMMARY.md §3). This
is the spatial-search analogue of our spectral lift and subsumes the entire
example table in cluster-3. Together with 1508.01327/2204.04355 (already held)
it gives both the general theorem and its instances.

### Childs & Goldstone, "Spatial search by quantum walk", arXiv:quant-ph/0306054 (Phys. Rev. A 70, 022314, 2004) [`references/quant-ph_0306054.pdf` / `.txt`]
**What it contains:** The original CTQW spatial-search algorithm; constant-gap
sufficient condition for optimality; `d>4` grid result.
**How it helps graphplay:** *Supplies the base statement* the CNO theorem
extends — the `H = -γA - |w⟩⟨w|` search Hamiltonian and its `√n` analysis. The
constant-spectral-gap sufficient condition is the easy case of `Search/CNO.lean`
and the natural first lemma to prove there before the full CNO necessary-and-
sufficient version.

### Mančinska & Roberson, "Graph Homomorphisms for Quantum Players", arXiv:1212.1724 (J. Combin. Theory B 118, 2016) [`references/1212.1724.pdf` / `.txt`]
**What it contains:** Quantum graph homomorphisms via the homomorphism game;
quantum chromatic/independence/clique numbers; Lovász-θ(complement) lower bound
on quantum chromatic number; vector/operator-system formulation.
**How it helps graphplay:** *Supplies statements to capture* for Tower 3 /
quantum CSP (the gap-map "quantum homomorphism" item). The vector-space
homomorphism formulation is the categorical lift target for `Graphplay`'s
homomorphism layer; lower proof-leverage than Tiers 1–2 for the PST spine but
the right reference for the quantum-CSP corner.

---

## Mathlib reuse opportunities (Tier 0 — research only, nothing downloaded)

Surveyed `/Users/ember/src/mathlib4`. Concrete lemmas to REUSE instead of
reproving:

**Hermitian spectral theorem — `Mathlib/Analysis/Matrix/Spectrum.lean`** (this
is the engine for the whole `eigenProjEntry` / `eigenSupport` layer):
- `Matrix.IsHermitian.eigenvectorBasis` (orthonormal eigenbasis),
  `eigenvectorUnitary`, `eigenvectorUnitary_apply/_col_eq/_mulVec` — already used
  by `Cospectrality.lean`/`GodsilRatio.lean`; these *fully* support
  `eigenProjEntry` and `eigU`.
- `spectral_theorem` (`A = U D Uᴴ`), `eigenvalues_eq`, `mulVec_eigenvectorBasis`
  — gives the `f(M)=∑f(θ_r)E_r` functional calculus (thesis Thm 2.1.6) for free.
- `eigenvalues_mem_spectrum_real`, `spectrum_real_eq_range_eigenvalues`,
  `spectrum_eq_image_range` — **directly proves** the sorried
  `eigenvalueSupport_subset_spectrum` (`GodsilRatio.lean:119`) and the `obtain …
  eigenvalues i` existence sorry in `Hom.preserves_stronglyCospectral`
  (`Cospectrality.lean:291`).
- `finite_real_spectrum` — backs `eigenvalueSupport_finite` (currently proven via
  `Set.finite_range`, but this is the canonical fact).
- `trace_eq_sum_eigenvalues`, `det_eq_prod_eigenvalues`, `charpoly_eq`,
  `roots_charpoly_eq_eigenvalues` — for spectral-moment / integrality arguments
  in the Niven/Godsil corollaries.

**Matrix exponential / unitary evolution — `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`:**
- `Matrix.IsHermitian.exp` and `IsSymm.exp` — the evolution `exp(itA)` is the
  object in `IsPST`; gives unitarity/Hermiticity-preservation for free.

**Compact self-adjoint operators — `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`:**
- `orthogonalFamily_eigenspaces`, `directSum_decompose`, `direct_sum_isInternal`,
  `orthogonalComplement_iSup_eigenspaces_eq_bot`, `finite_dimensional_eigenspace`,
  `eigenvalues` (sorted), `diagonalization_apply_self_apply` — the
  infinite-dimensional spectral theorem. This is the machinery the
  `GraphonGodsilOpen` stub (`GodsilRatio.lean:512`) and `Graphon/PST.lean` need:
  it provides the discrete eigenspace decomposition of the compact self-adjoint
  graphon operator `T_W`, i.e. the spectral-measure analogue of eigenvalue
  support. Pairs exactly with the Backhausz–Szegedy graphop framing.

**Laplacian — `Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean`:**
- `isHermitian_lapMatrix`, `isSymm_lapMatrix`, `posSemidef_lapMatrix`,
  `lapMatrix_mulVec_const_eq_zero`, `lapMatrix_toLinearMap₂'`,
  `card_connectedComponent_eq_finrank_ker_…`, `lapMatrix_ker_basis` — directly
  support the planned `Loopy.lean` / Laplacian-walk layer (gap #2): Hermiticity,
  PSD, the all-ones kernel vector, and the connected-components ⇔ kernel-rank
  fact (the algebraic-connectivity / Fiedler entry point for math0109191,
  gap #12). NB: there is **no** `algebraic connectivity`, `Fiedler`,
  `interlacing`/Cauchy-interlacing, or `equitable partition`/`divisor matrix`
  lemma in Mathlib — those remain ours to build (matches SUMMARY.md).

**AdjMatrix — `Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean`:**
- `isHermitian_adjMatrix`, `adjMatrix_pow_apply_eq_card_walk`,
  `adjMatrix_mulVec_const_apply_of_regular`, `trace_adjMatrix` (=0, the loopless
  fact noted as a blocker), `degree_eq_sum_if_adj`.

**Path graph / Niven — `Mathlib/Combinatorics/SimpleGraph/Hasse.lean` +
`Mathlib/Analysis/SpecialFunctions/Trigonometric/{Complex,Chebyshev/RootsExtrema}.lean`:**
- `SimpleGraph.pathGraph` (+ `pathGraph_adj`, `pathGraph_connected`) — fills the
  `pathWeightedGraph`/`pathGraph` stubs (`Cospectrality.lean:316`,
  `GodsilRatio.lean:288`) via `toWeighted`.
- `cos_eq_iff_quadratic` and the `Irrational (cos (rat·π))` lemma in
  `Chebyshev/RootsExtrema.lean` — the Niven-theorem ingredient for
  `isPST_exists_path_iff` (`GodsilRatio.lean:302`).
- `Mathlib/Topology/Instances/AddCircle/DenseSubgroup.lean`
  (`dense_addSubgroupClosure_pair_iff`, `denseRange_zsmul_iff`) and
  `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` — the Kronecker /
  simultaneous-approximation engine for the backward half of the Godsil
  existence theorem (`GodsilRatio.lean:239`).
- `Mathlib/RingTheory/Polynomial/Chebyshev.lean` — Chebyshev eigenvector basis
  for `isStronglyCospectral_pathEndpoints` (`Cospectrality.lean:331`).

---

## Top 3 to integrate first (ranked by proof-leverage)

1. **Coutinho thesis 2014 (`coutinho_thesis_2014.pdf`) + Godsil 1011.0231.**
   Together they are the *complete proof* of the `Graphplay/PST/` sorry-set:
   `isStronglyCospectral_iff` (thesis Cor 2.5.2/Thm 2.5.1), the cospectral⇔
   parallel lemmas, and both directions of the Godsil-ratio existence theorem
   (thesis §2.4 + Godsil's quadratic-integer Thm 6.1). Combined with Mathlib's
   `eigenvectorBasis`/`spectral_theorem`/`spectrum_real_eq_range_eigenvalues`,
   this is enough to discharge `eigenvalueSupport_subset_spectrum`,
   `isStronglyCospectral_iff`, `.symm/.refl/.of_aut`, and the forward half of
   the existence theorem now. Highest leverage by far.

2. **Chakraborty–Novo–Roland 2004.12686** for gap-map item **#1**
   (`Search/CNO.lean`) — the necessary-and-sufficient CTQW-search optimality
   condition, the single highest-leverage *missing* theorem per SUMMARY.md §3,
   with Childs–Goldstone `quant-ph_0306054` supplying the base case / easy
   constant-gap lemma to build first.

3. **Backhausz–Szegedy 1811.00626** (graphops) as the rigorous operator-limit
   foundation for Towers 4–6 — the `GraphonGodsilOpen` stub and `Graphon/PST.lean`
   — plugged into Mathlib's compact self-adjoint spectral theorem
   (`Analysis/InnerProductSpace/Spectrum.lean`). Lower immediate sorry-discharge
   than #1–#2 but it is the definitional home that makes the entire
   "quasi-infinite adjoint" upper-tower program well-posed.
