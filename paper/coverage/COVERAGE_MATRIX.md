# Coverage matrix — Graphplay vs. the Godsil/Tamon CTQW corpus

Systematic audit answering: *did we model and verify the relevant papers?* For
each paper: is it represented as a precise statement (**Modeled**), is its key
theorem closed (**Proven** / **honest-sorry** / **N**), and what **genuine gaps**
remain (results not represented at all).

**Method.** Cross-checked the 72 arXiv `.txt` mirrors in `references/` against the
live Lean tree (`lake build Graphplay` succeeds: 3897 jobs, no errors), the
build-log `declaration uses 'sorry'` scan (`/tmp/sorry-decls.txt`, 312
sorry-using declarations), and the four prior cluster audits + the
Godsil/Coutinho haul + adjacent-literature notes (all dated 2026-05-28; this
report **updates** them to the current state).

**Legend.** Modeled = a Lean `def`/`theorem` states the notion precisely.
Proven = theorem closed, body **not** `sorry` (verified against the build-log
scan). honest-sorry = statement present, proof deferred (genuinely deep / blocked
on Mathlib analysis). N = not represented. Paths are repo-relative under
`/Users/ember/dev/graphplay`.

**Top-line.** Of ~40 distinct corpus papers/results:
- **Spine fully proven** (sorry-free, axiom-clean): the equitable-partition →
  symmetric-quotient `Q̃` → spectral/PST lift, finite product PST, hypercube
  antipodal PST, abelian-Cayley/cycle PST iff, Laplacian/lackadaisical
  walk-equivalence. Core files `PST.lean`, `Equitable.lean`, `Bundle.lean`,
  `Product.lean`, `Product/PST.lean`, `PST/DiagonalShift.lean`,
  `StdLib/HypercubeProduct.lean`, `StdLib/Cycle.lean`, `Loopy/Laplacian.lean`,
  `Graphon/PST.lean`, `Graphon/Equitable.lean` carry **zero** sorry-decls.
- **Modeled-but-deferred** (statement present, honest-sorry): the
  cospectrality/Godsil-ratio existence iffs, the quotient/signed-quotient iffs,
  CNO spectral-ratio search, Bose–Mesner FR, path/Hamming/Cayley headline
  corollaries, many-body Feder/fermionic lifts.
- **Genuine gaps** (absent entirely): corona, join, double-cover, exterior/boson
  power as concrete families, weak-coupling/Feshbach–Schur, universal-PST +
  switching automorphisms, K-fractional-revival framework, Krawtchouk-chain +
  speed-limit, matrix-inversion, QOMDP decidability, circulant/bunkbed average
  mixing, Groverian shadow framework, algebraic-connectivity Heawood,
  spectral-regularity lemma, graphs-with-tails concrete ops, pair/plus states.

---

## Cluster 1 — PST core

| Paper (arXiv) | Lean location | Modeled? | Key thm proven? | Notes / gaps |
|---|---|---|---|---|
| **1108.0339** Bachman, PST on quotient graphs | `PST/QuotientIff.lean` (`cellUniformPST_iff_quotientPST` L258 **proven**); `PST.lean` `pst_lift`; `Equitable.lean`; `Spectral.lean`; `ManyBody.lean` `feder_bosonic_quotient_eq` | Y (core) | **Proven** (master iff + spine); honest-sorry on Feder lift bodies | Quotient iff is **now proven** end-to-end. `symmQuotient_isHermitian` proven. Feder boson `G^⊙k` now *represented* as `OccupationVector`/`feder_bosonic_quotient_eq` (honest-sorry) — upgrade from "absent" in May. Phantom-symmetry witness still abstract. |
| **1009.1340** Ge–Greenberg–Perez–Tamon, products & equitable | `Product.lean` (`cartesianProduct`/`tensorProduct`/`strongProduct` **proven** Hermitian + eigen-lemmas); `Product/PST.lean` `cartesianProduct_pst` **proven**; `Dowsing/BundlePSTLift.lean` `lexProduct_pst`/`tensorProduct_pst` (honest-sorry) | Y (products); N (cones) | **Proven** for Cartesian PST; honest-sorry for tensor/lex/strong | Cartesian-product PST fully proven (`exp(M⊗1)` factorization). **GAP**: irregular/Perron double-cone (Thm 7), glued double-cone (Thm 9), cylindrical-cone **negative** result (Thm 11). No negative-PST theorems anywhere. No `genLexProduct` connection matrix. |
| **1310.3885** Cameron, Universal State Transfer | — | **N** | N | **GAP**: no `IsUniversalPST`/`IsFlat` type-II / `SwAut` / monomial-switching infra. Oriented cycle `iΘ−iΘᵀ` absent (`StdLib/Cycle.lean` is unsigned only). |
| **1701.04145** Connelly, Universality in PST | — | **N** | N | **GAP**: entirely depends on the (absent) universal-ST infra; PST-time-set/spacing, type-II canonical form, cyclotomic dense-circulant results all absent. |
| **1211.0505** Brown–Godsil–…, PST on signed graphs | `Chiral.lean` (`signedBy_preserves_equitable` **proven**); `PST/QuotientIff.lean` `cellUniformPST_iff_quotientPST_signed` (honest-sorry) | ⚠️ partial | Proven for signed-equitable preservation; honest-sorry for signed quotient iff | Signed-equitable preservation proven. **GAP**: balanced/anti-balanced signing predicate; signed join `K₂⁻+G⁺` (`π/√(4+2n)`); double cover `A⁺⊗I+A⁻⊗X`; exterior power `⋀ᵏG`. Signed-quotient matrix still `NNReal.toReal 1` placeholder. |
| **2301.01473** Acuaviva, complex/chiral state transfer | `PST/GodsilRatio.lean` `isPST_exists_iff_strongCospectral_and_godsilRatio` (honest-sorry); `PST/Cospectrality.lean` | ⚠️ partial | honest-sorry | Existence iff stated. **GAP**: quarrel `q_r` phase data + quarrel-ratio condition (Thm 2.1); periodicity predicate; multiple/one-way PST; oriented-graph universal-PST classification; rooted products / loop families. |
| **1409.5840** Alvir, Laplacian quantum walk PST | `Loopy.lean` (`LoopyWeightedGraph`, `WeightedGraph.laplacian`); `Loopy/Laplacian.lean` `regular_laplacian_equiv_adj` **proven**; `Loopy/Search.lean` | ⚠️ partial | **Proven** for regular A/L equivalence + lackadaisical invariance | **Big upgrade from May (~5%):** Loopy layer now exists and the regular-graph A/L/lackadaisical modulus-equivalence is **proven**. **GAP**: complementation closure, `K₂+H` `≡2 mod 4` characterization, signless `D+A` double cone, normalized `𝓛` weak-product, almost-equitable partitions, Laplacian negative results. |

## Cluster 2 — fractional revival / speed / tails

| Paper (arXiv) | Lean location | Modeled? | Key thm proven? | Notes / gaps |
|---|---|---|---|---|
| **1907.04729** FR & association schemes | `Dowsing/FractionalRevivalNC.lean` (`IsFR`, `bose_mesner_fr_iff`); `QuantumGraph.lean` (`AssociationScheme`, `BoseMesner`); `StdLib/Hamming.lean` | ⚠️ partial | honest-sorry | `bose_mesner_fr_iff` has `True`-placeholder for spectral congruences. **GAP**: `(g,h)` invariants + Thm 3.5; Kummer/`α₂` Hamming characterization; DRG Prop 3.6; infinite families. **Watch:** stated Hamming FR time `π/(2n)` ≠ paper's `π/2^k`. |
| **2004.01129** Fundamentals of FR | `Dowsing/FractionalRevivalNC.lean` (`|K|=2` pair case only) | ⚠️ partial (pairs only) | honest-sorry | **GAP**: arbitrary-`K` framework — `IsKFR`, `D_K` periodicity, `P_min^K`, set support `Φ_K`, ratio condition (Thm 5.5), decomposability (Thm 7.2), **non-monogamy** headline. All absent (`IsKFR`/`DensityK` grep ABSENT). |
| **1801.09654** Chan, Quantum FR on graphs | (text not in corpus) `IsFR` pair predicate | ⚠️ indirect | N | Pair-FR shape present; `Cor 5.6` integral-spectrum time-rational not stated. Source PDF still missing from `references/`. |
| **1710.02705** Bernard, A graph with FR | `Dowsing/FractionalRevivalNC.lean` `fr_lift`; `StdLib/Hamming.lean` Krawtchouk scaffold | ⚠️ partial | honest-sorry | Cell-uniform FR lift = the abstract column-space projection. **GAP**: concrete `hypercubeFaceDiagonal` `(β/2)A₁+(α/2)A₂` construction + its balanced-antipodal-FR theorem. |
| **2209.08160** Breaking the speed limit (Xie–Kay–Tamon) | — (NB: `CarusoSpeedup.lean` anti-Zeno is a *different* open-system mechanism) | **N** | N | **GAP**: PST speed limit `J_max τ ≥ …`, θ-revival, monorail/dual-rail heralded protocol, fastest-FR `J_maxτ₀ ≥ Nθ/2`. Do **not** conflate with `CarusoSpeedup`. |
| **1609.01854** Note on speed of PST (Kay–Xie–Tamon) | `StdLib/Path.lean` (docstring mention only) | **N** | N | **GAP**: tridiagonal mirror-symmetry PST characterization; `J_max t₀ ≥ (π/4)√(N²−1)` odd-N bound (`Tr(SH²)` argument). No `speed_limit`/`mandelstam` anywhere (grep ABSENT). |
| **2211.14704** PST in graphs with tails | `Dowsing/FilteredColimitPST.lean` (`ConsistentPartitionSequence.pst_inherited` — **proven, sorry-free**) | ⚠️ abstract only | abstract master proven | Abstract filtered-colimit shadow now **sorry-free**. **GAP**: concrete ops — `oneSum`, `cone`, `rootedProduct`, eventually-free Jacobi, Golinskii decoupling `A=ℑ_v⊕J̃₀`, walk matrix / dark subspace, sedentariness, dual-rail (all grep ABSENT). |
| **2301.07251** No infinite tail beats search (Xie–Tamon) | `Search.lean` `search_infinite_tail` (L327, honest-sorry / trivial witness); `Dowsing/FilteredColimitPST.lean`; `Categorical.lean` | ⚠️ partial | honest-sorry | **GAP**: Jost-function spectral analysis, bound states `λ_±=n±√n`, `π/(2√n)` time, obliviousness theorem, Farhi–Gutmann lower bound (Thm 3). No `JostFunction`/`infiniteLollipop` (grep ABSENT). |
| **2512.08141** Strength of Weak Coupling (Kay–Tamon) | — | **N** | N | **GAP**: entire framework absent — Feshbach–Schur map, resolvent/condition number, γ-cospectrality, T.rex pendant edges, `IsHighFidelityST`, resonant tunneling, Anderson robustness, quantum hitting times (all grep ABSENT). |

## Cluster 3 — mixing / chiral / spatial search

| Paper (arXiv) | Lean location | Modeled? | Key thm proven? | Notes / gaps |
|---|---|---|---|---|
| **2605.04414** Uniform mixing in chiral QW | `Chiral.lean` (`unitaryHammingChiralK4Signing`, `signedBy_preserves_equitable` **proven**); `Mixing.lean` (`chiralMixingQuotient`/`chiralAverageMixingQuotient` — **proven**) | ⚠️ partial | Proven for cell-uniform chiral mixing lift | Quotient lifts proven. **GAP**: conical-reduction probabilistic uniform mixing; oriented (`±i`) signing predicate; circulant-distinct-eigenvalues ⇒ average uniform mixing (Thm 5); signed-`H(n,4)` `π/3√3`; nonabelian-Cayley No-Go (Cor 8). |
| **quant-ph/0209106** Mixing in CTQW (Ahmadi) | `StdLib/Hamming.lean` (`hamming_uniformMixing_iff_q_le_4` — honest-sorry) | ⚠️ partial | honest-sorry | `Kₙ`/`H(n,q)` boundary captured indirectly. **GAP**: explicit `K_n` iff `{2,3,4}`, balanced-multipartite-iff-`K₂,₂`, `K₂` mixing-times. |
| **quant-ph/0509163** Mixing & decoherence on cycles | `CarusoSpeedup.lean` (qualitative, different target); `Graphon/Lindblad.lean`; `Toolkit/Noise.lean` | **N** (for cycles) | N | **GAP**: TV-distance/`ε`-mixing-time notion; Gurvitz dephasing on `Cₙ`; small/large-Γ mixing-time bounds. |
| **quant-ph/0509059** Mixing on circulant bunkbeds | — | **N** | N | **GAP**: `Circulant` family + bounded-multiplicity average mixing (Thm 1); `join`, bunkbed `Pₘ□G` closure; cone non-mixing. No `Circulant`/`Bunkbed` (grep ABSENT). |
| **quant-ph/0608044** Universal mixing | — | **N** | N | **GAP**: `IsUniversalMixing`; weighted `P₃`/claw families; unweighted claw uniform mixing; `τ(G)` distinct-eigenvalue param + `p̄≥1/τ` no-go. |
| **quant-ph/0308073** Graphs resistant to uniform mixing | `Mixing.lean` (`averageMixing` abstract/sorry) | **N** | N | **GAP**: AAKV average-prob closed form; abelian-circulant No-Go (the result chiral 2605.04414 *violates*); `Cₙ` `(1/n)`-mixing; bunkbed memoryless. |
| **0808.2382** Mixing on generalized hypercubes | `StdLib/Hamming.lean` (`hamming_uniformMixing_iff_q_le_4`); `StdLib/Hypercube.lean` (`hypercube_uniformMixing`) | ⚠️ partial | honest-sorry | Headline `H(n,q)` `q≤4` + Moore–Russell captured (honest-sorry). **GAP**: additive-matching `Qₙ^η`, Cartesian-product uniform-mixing-iff (the lemma that would *derive* the Hamming result), bunkbed Fourier-support criterion. |
| **0708.2096** Non-uniform mixing on cycles | `StdLib/Cycle.lean` (eigenvalues only; **now sorry-free combinatorially**) | **N** | N | **GAP**: even-cycle non-uniform-mixing (Thm 7), divisor-reduction lemmas, cycle average `(1/n)`-mixing. Needs `CycleWG` as a `WeightedGraph`. |
| **2204.04355** Shadows and gaps in spatial search | `Search/CNO.lean` (related); `Search.lean` `IsOptimalSearch` (cruder predicate) | ⚠️ weak | honest-sorry | **GAP**: `shadow ε₁`, `S_k` params, Groverian-iff-`S₂/S₁²=Θ(1)` (Thm 6.1), `Ω(1/ε₁)` lower bound, distance-regular example table. `Groverian` term only appears unrelated (Tower6/ManyBody). |
| **1508.01327** Search optimal for almost all graphs (CNO) | `Search/CNO.lean` `optimal_search_of_spectral_ratio_lt_one` (L241, honest-sorry) | **Y** | honest-sorry | **Upgrade from May (~0%):** the constant-spectral-ratio sufficient condition is now **modeled** (`optimal_search_of_spectral_ratio_lt_one`, `optimal_search_of_quotient_ratio`, `complete_graph_optimal_search`), citing 2004.12686/Childs–Goldstone. **GAP**: Erdős–Rényi/random-regular a.s.-optimality. |
| **1406.0339** Search on planar networks (Sadowski) | `DiscreteTime.lean` (not the coined model) | **N** | N | **GAP**: discrete-time **coined** walk, Apollonian network, abstract-search framework. Lowest priority (orthogonal to CT core). |
| **1706.06939** Faster search by lackadaisical QW (Wong) | `Loopy/Laplacian.lean` + `Loopy/Search.lean` (self-loop CT walk — **proven** modulus invariance) | ⚠️ partial | **Proven** (CT self-loop invariance) | **Upgrade:** loopy/self-loop CT layer exists and lackadaisical *invariance* is proven. **GAP**: the discrete-time coined `C⁵` Grover-coin grid search runtime `O(√(N log N))` (different — coined, not CT). |

## Cluster 4 — joins / corona / structural / deterministic search / graphons

| Paper (arXiv) | Lean location | Modeled? | Key thm proven? | Notes / gaps |
|---|---|---|---|---|
| **0909.0431** PST in weighted join graphs | `Bundle.lean`/`Dowsing/BundlePSTLift.lean` (`templateJoin_pst_iff`, `colorCompletion_pst_iff` — honest-sorry) | ⚠️ partial | honest-sorry | Bundle/equitable skeleton subsumes join (J-coupling). **GAP**: weighted double-cone closed form (Thm 1 `δ/Δ`); half-join no-go (Thm 3); per-factor-time Cartesian closure. No `weightedDoubleCone`/`join` (grep ABSENT). |
| **0907.2148** PST, integral circulants & joins | `StdLib/Cayley.lean` (`cayley_abelian_PST_iff_rationalEigenvalues`, `cycle_PST_iff`, order≤32 enum — honest-sorry) | ⚠️ partial | honest-sorry | Integral-circulant/unitary-Cayley PST iff **modeled**. **GAP**: circulant-join `+_C` operator + `cos/sin(t√B)` lift (Thm 1); `ICG_{2n}` family; non-periodic double-cone (Cor 14). |
| **1605.05260** QST in coronas | — | **N** | N | **GAP**: no `corona` anywhere; no `IsPGST` predicate; no Kronecker-approximation. Biggest structural-operator hole (paired with 1508.05458). |
| **1508.05458** Laplacian ST in coronas | `Loopy.lean` (`laplacian` building block only) | **N** | N | **GAP**: corona + `IsLaplacianPGST`; no-Laplacian-PST (Thm 4.1); double-star/cocktail PGST. Loopy layer now *could* host the walk. |
| **1911.01953** Note on quantum Markov models | — | **N** | N | **GAP**: QOMDP, Moore/Mealy equivalence, approximate-optimal-policy decidability (Thm 6.8). Mathlib Banach-fixed-point makes value-iteration core tractable. |
| **2508.06611** Matrix inversion by QW (Kay–Tamon) | — | **N** | N | **GAP**: HHL embedding, weak-coupling perturbation, accuracy `O(γ^R κ^{R+1})`. Shares Krawtchouk-chain tooling with 2507. |
| **2507.18872** Optimising PST for timing insensitivity | `Dowsing/FractionalRevivalNC.lean` (FR kinematics only) | ⚠️ partial | honest-sorry | **GAP**: Krawtchouk chains, `J₁²=⟨1|H₀²|1⟩` figure-of-merit, Mandelstam–Tamm bound (Thm 1), T-Rex spectral engineering. No `krawtchoukChain` (grep ABSENT). |
| **2506.21108** Deterministic search on Laplacian-integral graphs | `StdLib/CompleteMultipartite.lean` (honest-sorry, **mis-attributed**); `Search.lean` (Childs–Goldstone line) | ⚠️ partial + mis-cited | honest-sorry | **Correctness issue persists:** `CompleteMultipartite.lean` describes this as complete-multipartite/single-marked; real result is *general Laplacian-integral CIQW* search. **GAP**: `Algorithm/DeterministicSearch.lean` (CIQW + Long-Grover + QPE phase shift). |
| **math0109191** Heawood alg-connectivity (Freitas) | `Bundle.lean` (`Heawood` def — chromatic side); `Examples/HeawoodOnTorus.lean` | ⚠️ partial | honest-sorry | Chromatic Heawood number present. **GAP**: the *algebraic-connectivity* statement `a(G)≤H(S)` (the actual theorem), Fiedler bound, Cheeger lemma, Ramanujan genus bound. No `algebraicConnectivity`/`Fiedler` (grep ABSENT). |
| **1003.5588** Limits of kernel operators (Szegedy) | `Graphon/Limit.lean` (cut-norm + convergence — honest-sorry); `Graphon/Spectrum.lean` | ⚠️ partial | honest-sorry | Spectral side captured on finite cell-uniform sector. **GAP**: spectral regularity lemma (Thm 2/3), eigenvector-clustering, quasirandom group actions, sphere-vs-circle dichotomy. |
| **2110.13686** Dynamical systems on graph limits (Bick–Sclosa) | `Graphon/Lindblad.lean` (tangential — linear quantum, not nonlinear) | **N** | N | **GAP**: nonlinear graphon flow, graphon automorphism group, Koopman operator, noninvertible symmetry, manifold graphons. |
| **2004.00677** Graphon LQR invariant subspaces (Gao–Caines) | `Integrations/MeanFieldGames.lean` (`GraphonLQR`, `MildSolution`, `mildSolution_exists_unique`, quotient LQR — honest-sorry) | ✅ best of graphon three | honest-sorry | (A5) invariant subspace = cell-uniform subspace **modeled**. **GAP**: explicit two-Riccati `nd×nd`/`n×n` decomposition + complexity; nodal-collaborative control; low-rank error bound. |

## Tier-1/2 Godsil–Coutinho spine sources (proof techniques + a few statements)

| Paper (arXiv) | Role / Lean location | Modeled? | Notes |
|---|---|---|---|
| **coutinho_thesis_2014** + **1011.0231** | Proof source for `PST/Cospectrality.lean` + `PST/GodsilRatio.lean` sorry-set | (technique) | The entire cospectrality/Godsil-ratio sorry-set is thesis Ch. 2 + Godsil 2012. Statements modeled; proofs honest-sorry pending formalization. |
| **2411.09157** Quotient graphs & stochastic matrices | Primary citation for `symmQuotient` `Q̃` | ✅ (the construction is proven) | `symmQuotient_isHermitian` etc. proven; pseudo-equitable extension unbuilt. |
| **2510.05306** QW on bounded infinite graphs | Engine for `Graphon.lean` bounded-operator equitable lift | ⚠️ partial | `Graphon/PST.lean`/`Equitable.lean` now sorry-free; `Graphon.lean` 1 sorry, `Spectrum`/`Limit` deferred. Twin-subgraph constructions unbuilt. |
| **1709.07975** Strongly cospectral vertices (Godsil–Smith) | Founding source for `Cospectrality.lean` | ✅ statements modeled | `isStronglyCospectral_iff`, `.of_aut` honest-sorry. |
| **1709.03591** New perspective on average mixing matrix | Backbone for `Mixing.lean` + `Dowsing/CoherentAlgebra.lean` | ⚠️ partial | Commutant-projection formula for M̂ not yet stated; `averageMixing` is bare sorry. |
| **1201.4822** Number-theoretic PGST (Pₙ) | Source for `IsGodsilRatio.ratios_rational` | (technique) | Kronecker-theorem technique to close the ratio condition; honest-sorry. |
| **2002.04666** PST on oriented graphs (Godsil–Lato) | Source for `Chiral.lean` + multiple-ST | ⚠️ partial | Multiple-state-transfer characterization (the universal-PST gap) unbuilt. |
| **1906.01591** Pair state transfer (Chen–Godsil) | Wants Loopy/Laplacian layer | ⚠️ partial | Loopy layer now exists; **GAP**: pair states `e_a−e_b`, plus states, path/cycle characterization (no `pairState` — grep ABSENT). |
| **2502.08103** PST between real pure states | Generalizes vertex PST | **N** | **GAP**: real-pure-state PST predicate; results (i)–(iii); spread bound. |
| **2305.10199** No PST in trees >3 vertices | Negative result to cite | **N** | **GAP**: no tree-PST no-go; Graphplay has no negative-PST results at all. |
| **2206.02995** Strong cospectrality in trees | Companion no-go | **N** | **GAP**: no-3-pairwise-strongly-cospectral-in-trees. |
| **1501.04396** PST in products & covers (Coutinho–Godsil) | Serves `Product.lean` | ⚠️ partial | Product PST proven for Cartesian; tensor-sum / covers honest-sorry/absent. |
| **1103.2578** Average mixing of CTQW (Godsil) | Computable targets for `Mixing.lean` | **N** | **GAP**: M̂ rationality; Pₙ `(2J+I+T)/(2n+2)`, cycle closed forms. |
| **1301.5889** Uniform mixing & assoc. schemes | `Mixing.lean` uniform side | **N** | **GAP**: Hadamard-in-scheme IUM; SRG classification; bipartite `4∣n`. |
| **2404.02236** Open problems survey (Coutinho–Guo) | Roadmap | (orientation) | Framing document; not a proof source. |
| **2509.09948** OP, QW & Prouhet–Tarry–Escott | Weighted-path / loopy regime | **N** | **GAP**: weighted-loop tridiagonal PST ≡ PTE hardness; OP three-term recurrence. Loopy layer could host. |
| **0806.2074** Periodic graphs (Godsil) | Periodicity ⇔ rational-ratio (PST prerequisite) | **N** | **GAP**: no `IsPeriodic` predicate (grep ABSENT); periodic-iff-rational-ratios; PST⇒involution. |
| **2110.07762** FR on non-cospectral vertices (Godsil–Zhang) | Constructions for `FractionalRevivalNC.lean` | **N** | **GAP**: unweighted non-cospectral-FR family; overlapping FR pairs. |
| **1606.02264** PST is poly-time (Coutinho–Godsil) | Decidable reformulation | (technique) | For making `eigenSupport`/`IsGodsilRatio` computable; optional. |
| **1401.1745** PST on DRGs & assoc. schemes | Statements for Bose–Mesner FR | ⚠️ partial | Feeds 1907.04729 FR + DRG corollaries; honest-sorry. |
| **1102.4898** State transfer survey (Godsil) | Rigor/roadmap | (orientation) | Survey. |
| **1811.00626** Action convergence of graphops (Backhausz–Szegedy) | Operator-limit home for Towers 4–6 | ⚠️ partial | Definitional home for `GraphonGodsilOpen` stub; not yet formalized as graphop P-operator. |
| **2210.10720** Unbounded-norm action convergence | Rigor for unbounded/tail limits | **N** | For infinite-tail/Jost Tower-6; citation only. |
| **2004.12686** CNO spatial-search optimality | Source for `Search/CNO.lean` | ✅ modeled | The CNO spectral-ratio theorem cited and modeled (honest-sorry). |
| **quant-ph_0306054** Childs–Goldstone spatial search | Base case for CNO | ✅ modeled | `searchHamiltonian` + `complete_graph_optimal_search`. |
| **1212.1724** Quantum graph homomorphisms (Mančinska–Roberson) | Tower-3 / quantum CSP | ⚠️ partial | `QuantumCSP.lean`, `QuantumGraph.lean`, `LovaszTheta.lean` (many honest-sorry). |

## Newly-acquired references NOT yet in any prior audit

| Paper (arXiv) | What it is | Lean location | Status |
|---|---|---|---|
| **1301.0973** Which exterior powers are balanced? (Mallory–Raz–Tamon–Zaslavsky) | Signed-graph exterior power `⋀ᵏΣ`, balance characterization | — | **GAP**. Directly the fermionic/exterior-power family (pairs with 1211.0505 Thm 13). `ManyBody.lean` has `FermionicNSpace` but not the balanced-exterior-power result. |
| **2209.07688** PST, equitable partition & CTQW search (Ide–Narimatsu) | Success prob + finding time of CTQW search via equitable partition + PST | `Search.lean` + `Equitable.lean` (spine subsumes the *method*) | ⚠️ partial — the equitable-quotient search method is exactly the proven spine + `search_quotient_reduction`; the specific success-prob/finding-time formulas not stated. Good low-effort modeling target. |
| **2312.06906** Quantum walks on join graphs (Kirkland–Monterde) | Strong cospectrality / periodicity / PST in adjacency **and** Laplacian join graphs; preservation under join | `Bundle.lean` joins (J-coupling, honest-sorry); `Loopy.lean` (Laplacian) | ⚠️ partial — join skeleton + Loopy layer exist; the join PST/periodicity characterization + preservation theorems not stated. Pairs with 0909.0431/0907.2148 join gaps. |
| **2501.08148** Optimal spatial search with long-range tunneling (King et al.) | CTQW search on lattices with long-range (power-law) hopping; physics-style | — | **GAP**. Orthogonal to the algebraic spine (power-law lattice Hamiltonians); low priority. |
| **qri_*** / **psyarxiv_8qvgy** / **8qvgy_v2** | QRI consciousness/valence papers | — | **Out of scope** (explicitly non-CTQW; the project's "QRI" adjacent material, not part of the Godsil/Tamon corpus). |

---

## GAPS — results/papers NOT represented at all (candidates for new files)

Grep-verified absent across the whole `Graphplay/` tree:

**Structural operators / families (highest breadth):**
1. **Corona** `G∘H` — `StdLib/Corona.lean` + `IsPGST` predicate + `ForMathlib/Kronecker.lean`. Serves **1605.05260, 1508.05458** entirely; PGST predicate also serves coronas elsewhere.
2. **Join / double-cone / double-cover / complement** — `StdLib/Join.lean`, `StdLib/DoubleCover.lean`. Serves **0909.0431, 0907.2148, 1009.1340 (Thm 7/9/11), 1211.0505, 2312.06906, 1409.5840**. Includes the project's first **negative-PST** theorems.
3. **Circulant / bunkbed** families — `StdLib/Circulant.lean`, `StdLib/Bunkbed.lean`. Serves **0509059, 0308073, 0708.2096**.
4. **Exterior power `⋀ᵏG` / concrete Feder boson family** — extend `ManyBody.lean`. Serves **1211.0505 (Thm 13), 1301.0973, 1108.0339 (Thm 8)**.

**Predicates / frameworks absent:**
5. **Universal PST + switching automorphisms** (`IsUniversalPST`, `IsFlat`, `SwAut`, monomial switching) — `PST/Universal.lean`, `SwitchingAutomorphism.lean`. Serves **1310.3885, 1701.04145, 2002.04666, 2301.01473**.
6. **Periodicity predicate** (`IsPeriodic`, periodic ⇔ rational-ratio) — `PST/Periodic.lean`. Serves **0806.2074** and is a prerequisite for several PST iffs.
7. **K-fractional-revival framework** (`IsKFR`, `D_K`, `P_min^K`, ratio condition, non-monogamy) — `Dowsing/SubsetFractionalRevival.lean`. Serves **2004.01129, 2110.07762**.
8. **Weak-coupling / Feshbach–Schur** (resolvent, γ-cospectrality, T.rex, `IsHighFidelityST`, resonant tunneling) — `Dowsing/WeakCoupling.lean`. Serves **2512.08141** (entirely).
9. **Krawtchouk chains + speed-limit + timing-insensitivity** (`krawtchoukChain`, Mandelstam–Tamm, T-Rex) — `StdLib/Chain.lean` + `Algorithm/TimingInsensitivePST.lean`. Serves **2507.18872, 1609.01854, 2209.08160**.
10. **Groverian shadow framework** (`shadow ε₁`, `S_k`, Groverian-iff) — `Search/Groverian.lean`. Serves **2204.04355**.
11. **Average-mixing spectral formula** (AAKV degenerate-eigenvalue closed form for M̂) — discharge the bare `averageMixing` sorry in `Mixing.lean`. Serves **0308073, 0708.2096, 1709.03591, 1103.2578, 0509059**.
12. **Pair / plus / real-pure states** (`e_a∓e_b`, real-pure-state PST) — `PST/PureState.lean`. Serves **1906.01591, 2502.08103**.
13. **Graphs-with-tails concrete ops** (`oneSum`, `cone`, `rootedProduct`, walk matrix, dark subspace, Jost function, sedentariness) — `StdLib/GraphsWithTails.lean` + `JostBoundState.lean`. Serves **2211.14704, 2301.07251**.
14. **QOMDP decidability** — `Integrations/QuantumMarkov.lean`. Serves **1911.01953**.
15. **Matrix inversion by QW** — `Algorithm/MatrixInversionQW.lean`. Serves **2508.06611**.
16. **Algebraic-connectivity Heawood / Fiedler** — `Spectral/AlgebraicConnectivity.lean`. Serves **math0109191**.
17. **Spectral-regularity lemma + graphop framework** — `Graphon/Regularity.lean`. Serves **1003.5588, 1811.00626, 2110.13686**.
18. **Coined / lackadaisical discrete-time walk + Apollonian/long-range lattices** — `CoinedWalk.lean`. Serves **1406.0339, 1706.06939 (DT part), 2501.08148**. Lowest priority (orthogonal to CT core).

## Correctness findings (carried forward — still open)

- **`StdLib/CompleteMultipartite.lean` mis-attributes 2506.21108**: describes it as a complete-multipartite/single-marked CTQW-Grover result; the real paper is *general Laplacian-integral CIQW* search for any marked fraction. Fix the citation.
- **`Dowsing/FractionalRevivalNC.lean` Hamming FR time**: stated `π/(2n)` does not match the paper's `π/2^k` (Kummer). Re-derive before relying on it.
- **`Search.lean` `search_infinite_tail`** (L327): a trivial finite-witness placeholder, not the honest Xie–Tamon `π/(2√n)` Jost analysis.

## Prioritized "what to model next" (top 5 highest value)

1. **Corona products + `IsPGST`** (`StdLib/Corona.lean` + `ForMathlib/Kronecker.lean`). Single biggest *structural-operator* hole; closes **1605.05260** and **1508.05458** entirely and unlocks PGST (needed corpus-wide). The Loopy/Laplacian layer (now proven) is ready to host the Laplacian-corona variant.
2. **Join / double-cone / double-cover + first negative-PST theorems** (`StdLib/Join.lean`, `StdLib/DoubleCover.lean`). Highest breadth: touches **0909.0431, 0907.2148, 1009.1340, 1211.0505, 2312.06906, 1409.5840**. Graphplay currently has *zero* negative-PST results — a structural blind spot.
3. **Universal-PST + switching-automorphism infra** (`PST/Universal.lean`, `SwitchingAutomorphism.lean`). Unblocks **1310.3885, 1701.04145, 2002.04666** and a large part of **2301.01473** at once; `IsPeriodic` (for **0806.2074**) is a small companion that several PST iffs already want.
4. **K-fractional-revival framework** (`Dowsing/SubsetFractionalRevival.lean`). The pair-FR base case is already present; building `IsKFR`/`D_K`/`P_min^K`/ratio-condition/non-monogamy closes **2004.01129** and **2110.07762** and is the natural extension of the proven cospectrality spine.
5. **Discharge the cospectrality/Godsil-ratio sorry-set** (`PST/Cospectrality.lean` L246/353/565, `PST/GodsilRatio.lean` L401/518/577). These are *modeled* statements whose proofs are now in hand (Coutinho thesis Ch. 2 + Godsil 1011.0231 + Mathlib `eigenvectorBasis`/`spectrum_real_eq_range_eigenvalues`). Highest *proof*-leverage: turns the central existence iffs from honest-sorry into genuine theorems, strengthening every downstream corollary (path, hypercube, Cayley).

*Lower-effort quick wins:* model **2209.07688** (success-prob/finding-time formulas — the proven equitable spine already does the heavy lifting) and the **average-mixing AAKV formula** (`Mixing.lean` currently a bare sorry; closing it cascades to five mixing papers).
