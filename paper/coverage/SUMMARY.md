# References coverage — consolidated gap map

Synthesis of the four cluster audits (`cluster1_pst_core.md`, `cluster2_fr_tails.md`,
`cluster3_mixing_search.md`, `cluster4_joins_structural.md`) against the Graphplay
Lean development. Goal: know exactly which theorems/constructions from the
non-QRI `references/` corpus we capture, and prioritize closing the rest.

## Headline

The spine (equitable partition → symmetric quotient `Q̃` → spectral/PST lift) is
now **genuinely proven** end to end: `quotient_handshake`,
`symmQuotient_isHermitian`, `adj_mulVec_cellUniformVec_eq`,
`restrict_eq_symmQuotient`, `adj_mulVec_cellInflateVec`, `spectrum_subset`,
`cellUniformSubspace_invariant`. So the *abstract* lift that subsumes the
Tamon-corpus quotient arguments is solid. The gaps below are mostly **specific
constructions and named families** the corpus develops on top of that lift, plus
three **structural blockers** in our base types.

## Structural blockers (highest leverage — each unblocks several papers)

1. **[RESOLVED — wave 5A]** `WeightedGraph` is loopless (`Weighted.lean:48`). Fixed
   by `Graphplay/Loopy.lean`: a `LoopyWeightedGraph` (Hermitian, *no* zero-diagonal),
   with the full `evolve` theory ported (genuinely proven — it only ever used
   `herm`), `IsLoopyPST`, `WeightedGraph.toLoopy`, and `WeightedGraph.laplacian`
   `= diag(Re(deg)) − A`. The symmetric quotient `Q̃` now lands directly in this
   layer, which **discharged the `BundlePSTLift.fiberQuotient.loopless` sorry**
   honestly (no diagonal-shift gymnastics). Still open downstream: Laplacian-walk
   *content* for 1409.5840 / 1706.06939 / 1508.05458 (the layer now *represents* them).

2. **[RESOLVED — wave 5B]** No first-class product operator. Fixed by
   `Graphplay/Product.lean`: `cartesianProduct` (Kronecker sum), `tensorProduct`
   (Kronecker product), `strongProduct`, each with genuine `herm`+`loopless`, the
   Kronecker-form adjacency identities, the **eigenvector-construction lemmas**
   (`λ+μ`, `λ·μ`, `λ+μ+λμ` on tensor-product eigenvectors), and product regularity.
   All `sorryAx`-free. Remaining: the full `spectrum`-set-equality (the eigenvector
   direction is proven; surjectivity onto the spectrum is not) and wiring these into
   the GGPT corollaries in `BundlePSTLift`.

3. **[RESOLVED — wave 3/CNO]** CNO spectral-ratio optimal-search theorem now lives in
   `Graphplay/Search/CNO.lean` (criterion + `optimal_search_of_bundle_quotient`
   proven; the deep CTQW analysis remains an honest sorry).

### Newly resolved beyond the original three
- **[wave 5D]** `EigenvalueSupport` was the full spectrum (ignored its vertex arg) —
  now the genuine per-vertex support `{λ | E_λ e_u ≠ 0}`, so Godsil's forward
  direction no longer over-claims.
- **[wave 5C]** Tower-4 analytic core: the graphon symmetric quotient
  (`crossMass_conj`, `quotient_handshake`, `symmQuotient_isHermitian`) is now
  fully `sorryAx`-free via the Hilbert–Schmidt Fubini closure; `Graphon.op` is wired
  to `kernelIntegralCLM` with genuine self-adjointness, and
  `kernelIntegralCLM_spectrum_real` is closed.
- **[wave 4]** `DiagonalShift.lean` (PST diagonal-shift invariance) and the
  Hilbert–Schmidt `kernel_integrable`/`kernelIntegralCLM_isSelfAdjoint` infra.

### Wave 6–8 results (built green, axiom-verified)
- **[wave 6A — DONE]** `noLeakage_of_equitable` + `quotientPST_of_cellUniformPST` closed
  ⇒ `cellUniformPST_iff_quotientPST` and `GraphBundle.pst_iff_quotient` are now
  **fully `sorryAx`-free**. The entire finite bundle-PST lift chain is axiom-clean.
- **[wave 7A — DONE]** `Product/PST.lean`: `evolve(G□H) = evolve(G)⊗evolve(H)` via the
  genuinely-proven `exp(M⊗1)=exp(M)⊗1` Kronecker factorization, then `cartesianProduct_pst`.
- **[wave 7B — DONE]** `Loopy/Laplacian.lean`: regular-graph Laplacian↔adjacency walk
  modulus-equivalence + lackadaisical (self-loop) invariance, all axiom-clean.
- **[wave 8A — DONE]** `StdLib/HypercubeProduct.lean`: hypercube antipodal PST at π/2
  (`isPST_hypercubeP_antipode`), machine-checked from first principles (Pauli-X
  diagonalization → `isPST_K2` → Kronecker induction). **Fully `sorryAx`-free.**
- **[wave 8B — DONE]** GGPT Cartesian-product PST corollary banked (honest periodicity
  hypothesis); `tensorProduct`/`conormalProduct`/`disjunctiveProduct` defs concretized.
  Tensor/strong/lex `_pst` left honest (need GGPT spectral-lattice conditions).
- **[wave 8C — DONE]** Graphon op-intertwining `op_cellIndicator_eq`,
  `cellUniformSubspaceInvariant`, `op_restrict_eq_quotient` closed (Graphon/Equitable
  3→0 sorries); graphon PST/mixing headlines reduced to ONE named gap
  `evolve_cellUniformIsometry_eq`. (These carry *inherited* `sorryAx` from `W.op`'s
  analytic core — see frontier below.)
- **[wave 8D — DONE]** `Loopy/Search.lean`: Laplacian/lackadaisical **search**
  diagonal-shift invariance, axiom-clean. CompleteMultipartite `herm` closed.

### Current frontier (highest-leverage remaining single proofs)
1. **The Hilbert–Schmidt L² Schur bound** `kernelIntegralFun_memLp` /
   `kernelIntegralFun_eLpNorm_le` (`ForMathlib/HilbertSchmidt.lean`). This is the ONE
   genuine Mathlib analytic gap that the ENTIRE Tower-4 operator layer inherits
   `sorryAx` from (`W.op`, `op_cellIndicator_eq`, the graphon iffs). Closing it
   (Cauchy–Schwarz + Tonelli on a finite measure) axiom-cleans all of Tower-4's op side.
2. **Graphon `evolve` group laws** (`Graphon.lean`: `evolve_zero`/`evolve_add`/
   `evolve_isUnitary`) + the one named gap `evolve_cellUniformIsometry_eq` ⇒ the graphon
   PST/mixing headlines go (inherited-)clean.
3. **Definitions, not proofs**, block the high-sorry files (NoiseEquitable, ManyBody,
   CoherentAlgebra, …): `cellProjector`, `noisyEvolve`, `fermionicHopSign`,
   `NParticleAdjacency` entries are `sorry`-valued *defs* / `True`-placeholders. Future
   yield there comes from BUILDING the concrete constructions, not closing theorems.

## Master gap list (ranked, with target module)

| # | Gap | Papers | Target module | Effort |
|---|-----|--------|---------------|--------|
| 1 | CNO spectral-ratio optimal-search theorem | 1508.01327, 2204.04355 | `Search/CNO.lean` | M |
| 2 | `LoopyWeightedGraph` + Laplacian walk layer | 1409.5840, 1706.06939, 1508.05458 | `Loopy.lean` | M |
| 3 | First-class `□`/tensor/strong products + spectral sum | many | `Product.lean` | M |
| 4 | Universal / multiple state transfer + switching automorphisms (flat/type-II, `SwAut`, PST-time spacing) | 1310.3885, 1701.04145, 2301.01473 | `PST/Universal.lean` | L |
| 5 | Many-particle quotients: Feder boson `G^⊙k`, fermionic `⋀ᵏ G` | 1009.1340, cluster-1 | extend `ManyBody.lean` | M |
| 6 | `K`-fractional-revival subset framework (`D_K` periodicity, `P_min^K`, ratio cond., non-monogamy) | 2004.01129, 1801.09654 | extend `Dowsing/FractionalRevivalNC.lean` | L |
| 7 | Feshbach–Schur weak-coupling PST (resolvent, γ-cospectrality, T.rex) | 2512.08141 | `PST/WeakCoupling.lean` | L |
| 8 | Speed-limit-breaking PST + **unitary** anti-Zeno / dual-rail monorail | 2209.08160 | `PST/SpeedLimit.lean` | M |
| 9 | Corona-product state transfer + PGST | 1605.05260, 1508.05458 | `Corona.lean` | M |
| 10 | Concrete graphs-with-tails ops (one-sum, cone, rooted product, dark subspace, decoupling) | 2211.14704, 2301.07251 | extend `Dowsing/FilteredColimitPST.lean` | M |
| 11 | Average-mixing spectral formula + circulant/cycle/bunkbed mixing-time results | 0708.2096, 0509163, 0509059, 0308073, 0808.2382 | extend `Mixing.lean` | M |
| 12 | Algebraic-connectivity Heawood (`a(G) ≤ H(S)`), Freitas | math0109191 | extend `Bundle.lean`/`Integrations` | M |
| 13 | Quantum Markov decidability (QOMDP / goal-state reachability) | 1911.01953 | `Integrations/QuantumMarkov.lean` | M |
| 14 | Matrix inversion by quantum walk (HHL simplification) | 2508.06611 | `Integrations/MatrixInversion.lean` | L |
| 15 | PST speed bound `J_max · τ ≥ …` (Yung) | 1609.01854, 2507.18872 | `PST/SpeedBound.lean` | S |
| 16 | Bose–Mesner FR `(g,h)`-invariants + Hamming Kummer characterization | 1907.04729 | extend `Dowsing/FractionalRevivalNC.lean` | M |

(S/M/L = small/medium/large effort.)

## Notable correctness findings (already actioned / to action)

- **FIXED**: `StdLib/CompleteMultipartite.lean` mis-attributed 2506.21108 as a
  complete-multipartite-specific result; it is "Deterministic quantum search on
  *all Laplacian integral* graphs" (complete multipartite is one instance).
- **Watch**: the Hamming fractional-revival time in `FractionalRevivalNC.lean`
  (`π/(2n)`) does not match the paper's `π/2^k` — re-derive before relying on it.
- Several `search_infinite_tail`-style statements are `True` placeholders; the
  honest Xie–Tamon bound (`π/(2√n)`, Jost/bound-state analysis) is unbuilt.

## Recommended build order

Blockers first (they unblock the most): **#2 (Loopy/Laplacian)** and **#3
(products)**, then **#1 (CNO)** which is the headline search theorem. Then the
family-specific work (#4, #5, #9, #11) can proceed in parallel since they sit on
the now-solid lift + the new base layers.
