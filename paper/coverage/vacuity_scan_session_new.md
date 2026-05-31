# Vacuity / Honesty Scan — ML-advantage slice (new session)

READ-ONLY adversarial audit of the Lean files added/heavily-edited this session,
focused on the public-facing ML quantum-advantage headlines. Taxonomy: A
placeholder-def, B trivial-conclusion, C vacuous-hypothesis, D stub-driven-green,
E false-as-stated, F overclaim. Worst-first (D, F, A, then B/C/E).

Files audited: Integrations/{EquitableMechanism, NovelAttention, StructuredAttention,
TransformerDSL, AttentionComplexity, QuantumAdvantage, MachineLearning}.lean ;
Applications/{CompileML, SparseSearch}.lean ; Dowsing/DiracLimit.lean.

## Findings table (worst-first)

| file:line | cat | name | why hollow / overclaimed | suggested fix |
|---|---|---|---|---|
| Dowsing/DiracLimit.lean:629-649 | **B + F** | `coinedWalk_continuum_is_dirac` | **CRITICAL hollow.** Named "the coined walk's continuum limit is the Dirac evolution," but the *only* nontrivial conclusion clause is `∀ k, ‖(masslessDiracBloch c).H k − (masslessDiracBloch c).H k‖ ≤ ε` — i.e. `‖X − X‖ ≤ ε`, which is `0 ≤ ε`, **trivially true**. The statement mentions neither the coined walk `coin`/`S·C` propagator nor any approximation between it and `exp(-it H_Dirac)`. The hypotheses (`coin`, `hcoin : coinᴴ*coin=1`) are entirely unused. The `sorry` discharges a goal that is actually `True` after `simp`. So this proves nothing about coined walks OR the Dirac limit — pure name/content gap. | Restate with a real discrepancy term, e.g. the rescaled walk propagator vs `exp(-it H_Dirac)`; or downgrade to an honest `-- BLOCKED` axiom/`Prop`-level conjecture that does NOT masquerade as a proved theorem. At minimum drop the `‖X−X‖` placeholder so the name isn't backed by a tautology. |
| Applications/SparseSearch.lean:599-622 | **F** | `hypercube_sparse_search_advantage` | Headline of the file, named "…_advantage". Clauses (1) sparsity and (2) equitable reduction are genuinely proven, but clause (3) `IsOptimalCTQWSearch (Hypercube d) w` — the actual *advantage* (O(√N) timing) — is a `sorry` (line 622). So the theorem is **not sorry-free**, yet the name asserts the advantage. The advantage half is exactly the un-proven part. Docstring is honest about this. | Keep, but the *name* should not imply the timing is proven. Either split into `hypercube_sparse_equitable_reduction` (the proven structural core, axiom-clean) + a separately-named conjecture carrying the `sorry`, or rename to `…_advantage_modulo_CNO_timing`. Paper must not cite this as a proved quantum advantage. |
| Applications/SparseSearch.lean:999-1023 | **F (propagated)** | `buildable_lattice_no_advantage_low_dim` | "Honest contrast" headline. Its clause (2) `¬ IsOptimalCTQWSearch (lattice…)` is discharged via `lattice_search_dimension_threshold` (a `sorry`, line 960) and clause (3) hypercube-optimal via the sorried `hypercube_sparse_search_advantage`. So both dynamical halves rest on `sorry`. Only the regularity/card facts are real. | Same as above: the dynamical contrast is conjectural; name/cite accordingly. Structural (degree/card) facts are the genuine deliverable. |
| Applications/SparseSearch.lean:955-960 | F | `lattice_search_dimension_threshold` | Biconditional `IsOptimalCTQWSearch ↔ 4 < d` is entirely `sorry`. Honestly flagged in docstring, but it is a *headline biconditional* feeding two other "headline" theorems. | Fine as an honestly-sorried frontier theorem; just ensure paper labels it conjectural, not proved. |
| Integrations/MachineLearning.lean:493-501 | F (delegated) | `ridge_inversion_restricts_to_quotient` | Named a "complexity-reduction theorem"; delegates to `MatrixInversion.inversion_restricts_to_quotient` whose body is itself a `sorry` (the inverse-of-restriction core). So it is NOT machine-checked end-to-end. Docstring's HONESTY NOTE says this explicitly. | Honest as written; keep the "delegated, deep core sorried" framing in any paper claim. |
| Integrations/AttentionComplexity.lean:249-285 | F (partial) | `attention_quantum_composition` | The classical clause (block-apply correctness + linear cost) is genuinely proven; the quantum clause's final restriction-equality is a `sorry` (line 285) gated on `G.adj` invertibility / `ctqw_success`. Conjunction is presented as "the end-to-end composition." | Honest (docstring flags the quantum half as the only `sorry`). The proven classical-linear half is the real content. |
| Integrations/EquitableMechanism.lean:227-231 | **A** | `residualSingularValue` | Placeholder def `:= 0` standing in for σ_{k+1}(R). Used as the RHS bound of `corrected_equitable_attention`. Because it is `0`, the "error bound" `nrm(…) ≤ residualSingularValue …` is the bound `≤ 0` (a *strong* claim, not a weak one), but the theorem is `sorry`, so no green vacuity results — and the honest-scope text discloses it. Flag because a `:= 0` placeholder feeding a named "error bound" is exactly the A-pattern. | Honest given the `sorry` + disclosure; but if anyone later closes the `sorry`, the `:= 0` would make it FALSE (you can't approximate to error 0 with rank k<rankR). Add a guard comment so it isn't accidentally "proved." |
| Integrations/EquitableMechanism.lean:259-266 | F | `corrected_equitable_attention` | Eckart–Young error half is `sorry` (BLOCKED). Named as a "bound"; the cost/decomposition companions ARE proven. | Honest, well-disclosed. |
| Integrations/StructuredAttention.lean:398-404 | F | `circulant_spectral_cost` | FFT O(n log n) cost is `sorry`. But note the statement is **weak/existential** (`∃ C fftCost, 0<C ∧ fftCost n ≤ C·n·log n`) — once the `sorry` closes, the existential is trivially witnessable (e.g. fftCost ≡ 0). So this theorem, even when "proved," would assert almost nothing about FFT. Currently sorried, so D doesn't fire, but the statement is too weak to carry the named claim. | Strengthen to bind `fftCost` to the actual circulant apply, or drop the spectral-cost theorem and keep only the proven `circulant_banded_cost`. |
| Integrations/NovelAttention.lean:199-207 | F | `chiralAttention_mixing_speedup_hook` | Existential `∃ s τ_chiral τ_plain, 0≤τ_chiral ∧ τ_chiral<τ_plain`, name claims a "mixing speedup." The statement says nothing about mixing — any two ordered reals satisfy it; the meaning lives only in the (BLOCKED) docstring. Currently `sorry`. | Honestly disclosed, but the statement is vacuous-shaped (would be trivially true if closed). Either bind τ_chiral/τ_plain to actual mixing times or keep as a clearly-labelled conjecture. |
| Integrations/QuantumAdvantage.lean:745-754 | C-ish / F-narrative | `quantum_search_quadratic_advantage` (+ `_exact`, `ml_structured_search_quantum_advantage`) | **Sorry-free and genuine**, but note the name/narrative ("quadratic speedup, classical Ω(n)") vs statement gap: the classical side is only `∀ queried, card<n → ∃ w ∉ queried` (existence of an unexamined vertex), i.e. the *weakest* adversary form, NOT a success-probability Ω(n) lower bound. The randomized `classical_search_success_le` (a real k/n-flavoured bound) exists but is NOT the clause bundled into the headline. Quantum side uses the **idealized** off-diagonal `rabiEvolve` modulus `|sin|=1`; the genuine finite-n detuning is carried separately (`exactSearchAmplitude`). | No fix required for soundness — these are honest. For the paper: state the classical clause as "examining <n vertices leaves an uncertified candidate" (a certification/worst-case bound), not "Ω(n) query lower bound on success probability," and prefer the `_exact` variants for the finite-n amplitude. |
| Integrations/MachineLearning.lean:540-543 | (note) | `IsQuantumSolvable` | Genuine predicate (wraps `IsOptimalSearch`, amplitude ≥ 1/√2). Not vacuous. | none |
| Integrations/TransformerDSL.lean:122-126, all | clean | `denote`, `compile`, `compile_denote_commutes`, `compiler_guarantee` | `emptyGraph.adj := 0` is a legitimate additive unit (not a stub passed off as content). `compile_denote_commutes` is genuine (`restrict_eq_symmQuotient`). No vacuity. | none |

## Stub-driven-green (category D) check on HEADLINES

**No category-D findings.** I checked the predicates the headline theorems collapse
onto and they are genuine, non-trivial `Prop`s:

* `IsPST` (PST.lean:30) = `‖G.evolve τ u v‖ = 1` — real.
* `IsCellUniformPST` (PST.lean:39) = unit modulus of an actual cell-uniform evolution
  element — real.
* `IsOptimalSearch` (Search.lean:41) = amplitude into marked subspace `≥ 1/√2` — real.
* `IsOptimalCTQWSearch` (CNO.lean:128) = ∃ γ,τ,C with τ ≤ C√N and `IsOptimalSearch` — real.

Therefore CompileML's `compiled_cellUniform_realizes_target` /
`compiled_experiment_prediction` / `compile_recall_to_heron` and QuantumAdvantage's
`ml_structured_search_quantum_advantage(_exact)` are **NOT** green-because-of-a-stub;
their `rfl`/lift proofs go through genuine PST/amplitude predicates and the exactly-
computed `rabi_amplitude`. CompileML is sorry-free in its core (the one residual
`sorry` is upstream, in the noisy-deficit quantitative bound, and not in this slice).

## Clean files / clean headlines (positive signal for the paper)

* **Integrations/QuantumAdvantage.lean** — the flagship. `rabi_amplitude`,
  `rabi_amplitude_norm`, `completeGraph_2d_block`, `quantum_search_quadratic_advantage`,
  `quantum_search_quadratic_advantage_exact`, `ml_structured_search_quantum_advantage`,
  `…_exact`, `structured_search_advantage` are all **sorry-free** and the statements say
  what the names claim, modulo the two narrative nuances flagged above (idealized vs
  exact amplitude — both forms are present and honestly distinguished; classical clause
  is the certification form). The exact 2×2 block identity is genuinely proven via the
  exp-intertwining method. This is the honest core.
* **Integrations/AttentionComplexity.lean** — `blockAttentionApply_eq_fullAttentionApply`
  (the O(n²)→O(n·r) exact collapse), the cost theorems, `blockGrad_apply`,
  `training_step_linear_under_equitable` are genuine and sorry-free. Only
  `attention_quantum_composition`'s quantum half is sorried (disclosed).
* **Integrations/StructuredAttention.lean §1-2** — `segmentAttention_block`,
  `segment_apply_correct`, `segment_attention_exact_reduction`, `pooledTokens_equitable`,
  `pooledTokens_restrict_eq_quotient`, `circulant*_translation_invariant`,
  `circulantTranslationAut`, `circulant_banded_cost`, `banded_le_full` — genuine,
  axiom-clean. The "exact reduction" claim (§1) is real (it IS the `hblock` collapse).
  Only `circulant_spectral_cost` (FFT) is sorried.
* **Integrations/EquitableMechanism.lean §1b/§2/§3** — `matrix_rank_add_le`,
  `equitablePart_rank_le`, `no_cheap_exact_factorization`, `irreducibility_floor`,
  `discrete_irreducibility_floor` (the **EXACT irreducibility floor**) are genuine,
  axiom-clean rank algebra and say exactly what they claim (the ε=0 floor only — the
  ε-approximate version is correctly NOT claimed). `equitable_strictly_generalizes_orbit`,
  `exists_equitable_beyond_orbit`, `blockConstant_NTK_subset_spectrum` are genuine.
* **Integrations/TransformerDSL.lean** — fully genuine; compiler correctness is real.
* **Integrations/NovelAttention.lean §2-4** — `PSTRoutingAttention.transfers(_iff)`,
  `HierarchicalEquitableAttention.composes`, `quotientResidualAttention_cost`,
  `quotientResidual_le_full` are genuine. Only §1 `…_mixing_speedup_hook` is sorried.
* **Dowsing/DiracLimit.lean §1-6** — `offDiagonalBloch_eigenvalues`,
  `offDiagonalBloch_band_touch`, `honeycombFormFactor_dirac_point`,
  `heavyHexQuotient_isOffDiagonal`, `masslessDirac_linear_dispersion` are genuine,
  axiom-clean band algebra. Only the *cone local-linearity* (`…_dirac_cone` clause 3)
  and `coinedWalk_continuum_is_dirac` are sorried — and clause 3 is honestly the
  `HasDiracCone` analytic leaf. The `coinedWalk` one is the hollow finding above.

## Summary

The ML-advantage slice is, on balance, **honest** — every `sorry` is disclosed and
no green headline theorem is stub-driven (no category D). The genuine, sorry-free
deliverables (K_n √n-vs-n Rabi separation, O(n²)→O(n·r) attention collapse, exact
irreducibility floor, off-diagonal-Bloch ±|f| band algebra, equitable-quotient
restriction lifts) say what their names claim.

Two items need attention before going public:
1. `coinedWalk_continuum_is_dirac` (DiracLimit) — its proved content is `‖X−X‖≤ε`,
   a tautology; the name is unbacked. **Fix or relabel.**
2. `hypercube_sparse_search_advantage` / `buildable_lattice_no_advantage_low_dim`
   (SparseSearch) — named as proved advantages but the advantage clause is `sorry`.
   **Rename or split** so the paper doesn't cite a sorried timing as proved.
