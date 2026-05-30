# Vacuity / stub scan — StdLib + Toolkit + Graphon + core (read-only)

Scope (read-only audit; no `.lean` edited): `Graphplay/StdLib/{Path, Hypercube,
HypercubeProduct, Hamming, Cayley, CompleteMultipartite, Cycle, Computable}.lean`;
all `Graphplay/Toolkit/*.lean`; `Graphplay/{Computable, CombinatorialMap, Demo,
Simulate}.lean`; `Graphplay/Graphon.lean`; `Graphplay/Graphon/{Equitable, PST,
Limit, LimitReverse}.lean`. (Graphon/Spectrum, Graphon/Lindblad, Information,
StdLib/Corona, StdLib/Join explicitly out of scope — owned by other agents.)

Categories: A placeholder def · B trivial conclusion · C vacuous hypothesis ·
D stub-driven green vacuity · E false-as-stated · F degenerate quantification.

Worst-first (D, A, then B/C/F). Theorem-level `sorry`s that are honestly
*declared incomplete* (red, not green) are NOT flagged as vacuity — they are
noted only where the stated conclusion is also trivial/tautological.

| file:line | cat | name | why | suggested fix |
|---|---|---|---|---|
| Toolkit/Bundle.lean:48-56 | A/D | `toMatrixℂ` | The `Float→ℂ` bridge is hard-stubbed to `(0:ℂ)` for *every* entry; `toMatrixℂ_eq_zero : toMatrixℂ m n = 0 := rfl`. Every "numerical" matrix view of a spec is the zero matrix. Documented, but it is the root stub. | Wire a real `Float→ℝ→ℂ` (or `ℚ`) bridge; keep the combinatorial `templateSimpleGraph` for the nonzero pattern. |
| Toolkit/Bundle.lean:71-81 | D | `CompilerSpec.templateWeightedGraph` | `herm`/`loopless` proofs are *genuine only because* `adj = toMatrixℂ … = 0` (zero matrix is trivially Hermitian/loopless). Green, but asserts nothing about the actual template weights. | Same as above; once `toMatrixℂ` is real these proofs become substantive. |
| Toolkit/Bundle.lean:155-177 | D | `CompilerSpec.hostBundle` | Fibers are `adj := 0`; coupling is the all-ones `fun _ _ => 1` (template weight dropped, since the `Float→ℂ` bridge is stubbed). `hermCompat` is genuine but only because `star 1 = 1`. The "host bundle" carries no real weights. | Carry the symbolic weight onto the coupling once the bridge exists. |
| Toolkit/Bundle.lean:231-298 | D | `CompilerSpec.fiberPartitionCert` | Long *genuine* equitability proof, but it certifies the *all-ones / edgeless-fiber* host (Bundle stubs), not the weighted spec. The "proven equitable partition" is real for a graph that has lost its weights. | Re-prove against the weighted host once weights are wired; until then label as "structural shape only". |
| Graphon/LimitReverse.lean:202-221 | B | `ConsistentPartitionSequence.unique_mod_mpr` | Conclusion is literally `h𝒮 ∧ h𝒮'` — the two hypotheses re-stated; proof is `exact ⟨h𝒮, h𝒮'⟩`. Asserts nothing beyond its inputs (the real "uniqueness mod measure-preserving rearrangement" content lives only in the docstring). | State a genuine conclusion (e.g. the two sequences' quotient limits are equal as matrices, or a permutation/coupling witness) instead of echoing the hyps. |
| Graphon/LimitReverse.lean:155-173 | B | `stepFunction_approximation_rate` | Conclusion `∃ 𝒮 N, N ≥ 0 ∧ True`. `N ≥ 0` holds for every `Nat` (`Nat.zero_le`) and `True` is vacuous; the only nonvacuous payload is bare `∃ 𝒮`, supplied by a `sorry`. As stated the cut-norm `ε`-closeness claim is absent. | Replace `N ≥ 0 ∧ True` with the actual `cutNormDiff (step W Π_N) W ≤ ε` + "Π_N refines P.cells" inequalities. |
| Graphon/LimitReverse.lean:110-126 | B/C | `GraphonEquitablePartition.arises_from_consistent_sequence` | Body of the existential is `True`; only the binder `(h_lim : Tendsto … (nhds P.quotient))` carries content, so it is not fully vacuous, but the `True` payload should be a real identification. | Move the limit identification out of `True` into the statement (it is already half-there in `h_lim`); drop the `True`. |
| Toolkit/Noise.lean:307-315 | C/B | `optimal_noise_resilient_bundle` | `∃ N, ∀ M, M.card = N.card → M.symmetryScore P ≤ N.symmetryScore P`. Trivially witnessed by the maximal-score model, but `symmetryScore` (l.285-295) is itself a `Classical.propDecidable …|>.decide` count — its value is not computable/characterised, so the "optimal resilience" claim reduces to an unanalysed existential. `sorry`-proved. | Give `Matrix.preservesCellUniform` a real `Decidable` instance and prove the maximiser exists with a characterised score. |
| Demo.lean:85-91 | B/F | `heawoodColoringIsProper` | Checks `i ≠ j → color i ≠ color j` for *all* distinct pairs, ignoring `heawoodK7.Adj` entirely. For K₇ (complete) this coincides with properness, but the function never consults the graph — it is "all-distinct", not "proper w.r.t. adjacency". Green only because the demo graph is complete. | Test `heawoodK7.Adj i j → color i ≠ color j` so the check is graph-aware (and reusable for non-complete graphs). |
| StdLib/Cycle.lean:71 | A/F | `Cycle.degree` | `degree (_n : ℕ) (_v : Unit) : ℕ := 2` — ignores both arguments; the vertex domain is `Unit` (singleton), and the constant `2` is unverified against `Cycle n`'s actual adjacency (wrong for `n ≤ 2`). | Make `degree : Fin n → ℕ` computed from the adjacency, or at least restrict to `n ≥ 3` and prove it. |
| StdLib/Cycle.lean:60-68 | A | `Cycle.numVertices` / `Cycle.numEdges` | Stand-alone closed-form `Nat`s with no lemma tying them to `Cycle n`'s actual vertex/edge count (the `#eval`/`decide` smoke tests only check the formula evaluates, not that it equals the graph's count). | Add `numVertices n = Fintype.card (Fin n)` and an edge-count agreement lemma. |
| Graphon.lean:381-405 | B | `Graphon.isStep_iff_exists_finite_partition` | `IsStep W ↔ ⟨literal unfolding of IsStep⟩`, proved `Iff.rfl`. The RHS *is* the definition of `IsStep`, so the "characterisation theorem" is a definitional tautology (honestly flagged in its own docstring as `rfl`-style). | Either drop the theorem, or state a non-trivial characterisation (e.g. constant-on-rectangles ⇒ finite-rank operator) as the real content. |
| Toolkit/Spec.lean:47-56 | A | `WeightedGraph.empty` | `adj := 0` placeholder graph; legitimate as a "degenerate input" fallback but used as the regularity-degree base for empty templates. | Fine as a unit; just ensure no theorem treats it as a generic regular graph. |
| Toolkit/Hardware.lean:226-243 | C/D (acknowledged) | `WeightedGraph.satisfies` | 3 of 5 conjuncts (`maxCouplingDistance`, `surfaceGenus`, `requiredRegularity`) are `True` placeholders *even when the field is `some _`*. The file's own ⚠ comment flags this; downstream `satisfies_unconstrained` (l.249) is green partly because of these `True`s, and `satisfies_quotient` (l.332, `sorry`) inherits the weakness. | Replace the three `True` placeholders with the real geometric/topological predicates before any theorem leans on them. |

## Clean files (real defs, honest `sorry`-marked theorems, no green vacuity)

- **StdLib/Path.lean** — `Path`/`WeightedPath`/`CLWCouplings` are real; herm/loopless proven; PST theorems honestly `sorry`. `adjMatrixℚ` companions + `decide`/`native_decide` smoke tests genuine. Clean.
- **StdLib/Hypercube.lean** — `hammingDist`, `Hypercube`, antipode all real; herm/loopless proven from `hammingDist_comm`/`_self`; PST/mixing theorems honest `sorry`. Clean. (`numEdges = n·2^(n-1)` is an unverified closed form, minor — same caveat as Cycle, not separately flagged.)
- **StdLib/HypercubeProduct.lean** — Strong file. `isPST_K2`, `isPST_hypercubeP_antipode`, `cartesianProduct_pst_both` **genuinely proven** (Pauli-X diagonalisation, induction). 1 `sorry` is none in body. Clean.
- **StdLib/Hamming.lean** — `Hamming`, `krawtchouk`, all defs real; herm/loopless proven; mixing iff honest `sorry`. (Doc cites a future-dated "Levine–Tamon 2024 arXiv:2605.04414" — implausible arXiv id, but it is prose, not a Lean claim.) Clean.
- **StdLib/Cayley.lean** — `CayleyGraph`, `cycle`, `BasicParity`, `HasPSTPartner` real; herm/loopless proven via genuine symmetry arguments; PST/enumeration theorems honest `sorry`. `IsAbelianOfOrderLE32WithPST` is a real card-membership predicate. Clean.
- **StdLib/CompleteMultipartite.lean** — `CompleteMultipartite`, `laplacian`, `searchHamiltonian`, `IsDeterministicSearch` real; herm/loopless proven; Laplacian-spectrum / det-search theorems honest `sorry`. Clean.
- **StdLib/Computable.lean** — Aggregator; `IsComputableStdLibEntry` is a real predicate, companions + `#eval` smoke tests genuine. Clean.
- **Computable.lean** — Full computable `GaussianRat` + list-matrix algebra (det/inverse/Gauss–Jordan). All real, computable, no sorry. Clean.
- **CombinatorialMap.lean** — Real rotation-system / half-edge model; `facePerm`, `faces`, `eulerChar`, `genus`, `toSimpleGraph` honest; `ofPerVertexRotations` has substantive `left_inv`/`right_inv` proofs; `K2OnSphere` real. Topological theorems (`card_E_eq_two_mul_numEdges`, `eulerChar_eq`, `darts_partition_by_faces`, `numFaces_pos`) honest `sorry`. Clean.
- **Simulate.lean** — Fully runnable `Float` CTQW simulator (scaling-and-squaring exp, Lindblad, chiral, grid, attention, quotient). No real `sorry` (the one match is the word inside a doc comment). Clean.
- **Demo.lean** — Computable K₇ coloring demo; values concrete (no real `sorry`). Only caveat is the adjacency-blind properness check (flagged above).
- **Graphon.lean** — Real `Graphon` structure + `op`/`evolve` built on `ForMathlib.HilbertSchmidt`; `op_isSelfAdjoint`, `evolve_zero/_add/_isUnitary`, `toGraphon`, `opFun_toGraphon_single`, `isStep_toGraphon` **genuinely proven**. One honest `sorry` (`op_norm_le`). `isStep_iff` `rfl`-tautology flagged above. Otherwise clean.
- **Graphon/Equitable.lean** — Substantive. `crossMass_conj` (Fubini swap, full integrability domination), `quotient_handshake`, `symmQuotient_isHermitian`, `op_restrict_eq_quotient`, `exp_intertwine`, `evolve_restrict_eq_finite_evolve`, `spectrum_quotient_subset_spectrum_op` **all genuinely proven, no bare `sorry`**. This is the load-bearing Tower-4 keystone and it is solid.
- **Graphon/PST.lean** — **No `sorry`.** `cellUniformPST_iff_quotientPST`, `…Mixing…`, `cellUniformSearch_iff_quotientSearch`, `evolve_cellIndicator_matrixElement` are real, and crucially they rest on the *proven* `op_restrict_eq_quotient`/`exp_intertwine` (Equitable.lean), **not** on stubs. NOT category-D green-vacuity. Clean.
- **Graphon/Limit.lean** — Real `ConsistentPartitionSequence`, `cutNorm`/`cutNormDiff`, `quotient`; limit/convergence/Xie–Tamon theorems are genuine non-trivial statements, honestly `sorry`-marked. Clean (no vacuous conclusions; conclusions are real `IsCellUniformPST`/`¬IsCellUniformPST` etc.).
- **Toolkit/Report.lean** — Pure data→string rendering; numeric hooks (`numericScanCTQW`, `suggestGamma*`) are `:= (0.0,0.0)`/`0.0` stubs but *explicitly and repeatedly labelled "best-effort / not a proof"*, and the certificate manifest tags them `numericOnly`. Honest stubbing, not hidden vacuity. (The stubs ARE placeholder defs (cat A) but they are correctly self-disclosed and never feed a green "theorem".)
- **Toolkit/Spec.lean** — Real JSON parser, `buildTemplate`, `heawoodNumber`, `templateRegularDegree`, `approxRegular`. `RegularityCert`/`regularityCert` are total data; the genuine obligation is split out as `IsRowRegular` + `regularityCert_sound` (honest `sorry`, explicitly replacing the old `proof : True`). Good separation; clean apart from the `empty` placeholder noted above.
- **Toolkit/Scheduler.lean** — Real `Schedule` family + `cellRestrict`, `evolveTrotter`, `evolve`, `adiabatic_search_schedule`; the analysis theorems honest `sorry`. NB `adiabatic_search_reduction` (l.320) second conjunct is `rfl`-trivial (`endpoints = (0,τ)`) but the first conjunct (cell-uniform invariance) is a genuine `sorry`, so the theorem is not vacuous overall. Clean.
- **Toolkit/InverseDesign.lean** — Strong, end-to-end **genuinely proven** (no `sorry`/`axiom`): `engineered_host_has_PST`, `synthesizePST_correct`, `synthHostPartition` (real equitability proof), `synthHostPartition_quotient_eq_K2`. Rests on the proven `isPST_K2` + `cartesianProduct_pst`. Exemplary; not vacuous.

## Notes on D (most important category)
The Toolkit's "engineering payoff" theorems split into two cleanly-separated
groups:
- **InverseDesign.lean** payoffs are *real* (proven, rest on `isPST_K2` /
  `cartesianProduct_pst`).
- **Bundle.lean** payoffs (`templateWeightedGraph`, `hostBundle`,
  `fiberPartitionCert`) are *green-but-hollow*: every proof is genuine, but only
  because the `Float→ℂ` bridge `toMatrixℂ` is hard-zeroed and couplings are
  all-ones — so the certified objects have lost the spec's actual weights. This
  is the principal category-D cluster: invisible to `sorry` counts, real-looking
  proofs, but certifying a stripped graph. Rooted at `toMatrixℂ := 0`.

The Graphon Tower-4 chain (Equitable→PST) was the other prime D suspect and
came out **clean**: its green iff-theorems depend on genuinely-proven operator
intertwining, not on stubs.
