# Vacuity / Stub Scan — `Graphplay/Integrations/`

READ-ONLY adversarial audit (no `.lean` edited). Taxonomy:
A = placeholder def, B = trivial conclusion, C = vacuous hypothesis,
D = stub-driven green vacuity, E = false-as-stated (survives via sorry/stub),
F = degenerate quantification.

Files scanned (13): TQFT, RMT, TensorNetworks, OptimalTransport, MeanFieldGames,
Hodge, LatticeGauge, WLRefinement, QuantumMarkov, MatrixInversion,
MachineLearning, AttentionComplexity, QuantumAdvantage.

Sorted worst-first (D and A clusters at top).

| file:line | cat | name | why vacuous/stub | suggested fix |
|---|---|---|---|---|
| Hodge.lean:834 | A | `harmonicEvolve` | `:= LinearMap.id` — the "harmonic CTQW propagator" is literally the identity (math-correct: L annihilates harmonics, so exp(-itL)=id on `harmonic X k`), but it makes the whole §7–8 dynamical layer content-free. | keep id, but state PST/encoding theorems on the FULL cochain space `Cochain X k` where `harmonicEvolve` is nontrivial, not on `harmonic X k`. |
| Hodge.lean:1037 | D | `IsHodgePST` | defined `∃ _t : ℝ, ‖Cochain.inner b a‖ = 1`; `t` is bound-and-unused, so "perfect state TRANSFER" collapses to a static inner-product-modulus condition — no evolution, no transfer. | define via `harmonicEvolve` on full space, or rename to `HarmonicOverlapUnit`; current name overclaims. |
| Hodge.lean:1002 | D | `harmonic_encoding_preserved` | `∀ t φ, harmonicEvolve 1 t φ = φ` proved by `rfl` (stub above); first conjunct `finrank = d` is just `henc`. Whole proof `⟨henc, fun _ _ => rfl⟩`. | as above; the "error channels act trivially" claim is vacuous because evolution is id. |
| Hodge.lean:1066 | D | `hodgePST_lift` | green only because `IsHodgePST` ignores `t` and `pullback` inner product = the sum `by rfl`; reduces to `hyp → (same hyp)`. | restate with genuine quotient↔host overlap (weighted by cell size, as the in-file NOTE admits) + real propagator. |
| Hodge.lean:864 | D | (`hodgeQuotient` harmonic-invariance conjunct) | same `harmonicEvolve = id` stub drives the `∀ t φ, ... = φ` clause to `rfl`. | as above. |
| MeanFieldGames.lean:165 | A | `MildSolution` | body is `∀ t, 0≤t→t≤T → True` — the controlled-dynamics solution predicate is identically `True`. | encode the Bochner-integral mild-solution equation; without it every downstream existence is vacuous. |
| MeanFieldGames.lean:170 | D/E | `mildSolution_exists_unique` | `∃ x, MildSolution ξ u x` with `MildSolution = True` is trivially true (any `x`); the `sorry` is gratuitous and the "exists+unique" claim is hollow. | depends on fixing `MildSolution`. |
| MeanFieldGames.lean:194 | D/E | `optimal_control_exists` | cost-optimality `cost x* u* ≤ cost x u` is gated by `MildSolution ξ u x = True`, so the constraint linking `x` to `u` is vacuous; as stated (no dynamics constraint) it is false-flavored, survives via `sorry`. | restore real `MildSolution`. |
| MeanFieldGames.lean:652 | A | `congestionFixedPoint` | `:= True` — the quantum-congestion best-response fixed-point predicate is identically True. | encode "ψ ∈ cellUniformSubspace is its own best response". |
| MeanFieldGames.lean:658 | D | `congestion_equilibrium_exists` | `∃ ψ ∈ cellUniformSubspace ∧ congestionFixedPoint(=True)` proved `⟨0, zero_mem, trivial⟩`; "equilibrium" = "0 ∈ subspace ∧ True". | depends on `congestionFixedPoint`. |
| MeanFieldGames.lean:677 | A | `chiralRoutingOptimal` | `:= True` placeholder predicate. | encode optimal phase-profile condition. |
| MeanFieldGames.lean:731 | B/D | `fidelity_lift` | conclusion reduced to `∃ _u, _u = liftPulse P û` (tautology `⟨liftPulse P û, rfl⟩`); intended "host fidelity = quotient fidelity" is gone. | state the fidelity-equality on the cell-uniform subspace. |
| WLRefinement.lean:323 | A | `stablePartition2` | `:= id` (admitted placeholder) — 2-WL stable partition of V×V is just the identity map. | use the colour-equivalence quotient of a 2-WL-stable colouring. |
| WLRefinement.lean:335 | E | `coherentAlgebra_eq_2WL_span` | with `stablePartition2 = id`, every (x,y) is its own cell, so the span of cell-indicators = ALL matrices ≠ `coherentAlgebra G`. False as stated; survives only via `sorry`. | fix `stablePartition2` first. |
| WLRefinement.lean:482 | A | `EigenvalueSupport` | `:= Set.univ` (admitted placeholder). | use per-eigenspace projector diagonal (the comment's honest def). |
| WLRefinement.lean:503 | E | `phantom_symmetries_exist` | requires `EigenvalueSupport G u ≠ EigenvalueSupport G v` = `univ ≠ univ`, UNSATISFIABLE; theorem is false-as-stated, survives via `sorry`. | fix `EigenvalueSupport`. |
| WLRefinement.lean:489 | D | `pst_requires_WL_and_eigenSupport` | condition (ii) `EigenvalueSupport u = v` is `univ = univ` (always true) given the stub, hollowing the conclusion (sorried). | fix `EigenvalueSupport`. |
| WLRefinement.lean:526 | A | `QuantumWLStable` | `:= coherentAlgebra G` (admitted placeholder; should be the larger non-commutative refinement). | implement non-commutative WL refinement fixpoint. |
| WLRefinement.lean:537 | D | `quantumWL_contains_coherent` | `coherentAlgebra G ≤ QuantumWLStable G` proved `le_refl` because both sides are literally equal (stub). | depends on `QuantumWLStable`. |
| WLRefinement.lean:729 | E/F | `OpenProblem2_quantum_strict_containment` | `coherentAlgebra G < QuantumWLStable G` = `X < X`, currently provably FALSE (unsatisfiable). In-file admits this. `def : Prop`, undischarged. | fix `QuantumWLStable`. |
| WLRefinement.lean:130 | F | `exists_WLStable` | proved by the discrete/identity colouring `c = e v` (every vertex its own colour) — the always-available trivial fixed point; intended "coarsest equitable partition" content absent. | strengthen to existence of the COARSEST stable colouring. |
| WLRefinement.lean:220 | F | `exists_KWLStable` | same trivial-injective-colouring proof for k-tuples. | as above (coarsest). |
| WLRefinement.lean:157 | A | `stablePartitionIndex` | `:= V` (admitted placeholder; should be the colour-quotient of V). | quotient by `colourEq`. |
| WLRefinement.lean:558 | C/D | `MancinskaRoberson_qIsomorphism` | hypothesis already supplies `Φ : QWL G ≃ₗ QWL H`; conclusion `Nonempty (QWL G ≃ₗ QWL H)` is `⟨Φ⟩` — assume X, conclude ∃X. | state quantum-iso → operator-system iso from independent data. |
| WLRefinement.lean:587 | B | `Babai_GI_quasipolynomial` | "GI quasipolynomial" reduced to `(univ : Set (W ≃ W)).Finite := Set.finite_univ` — no complexity content. | acknowledged unformalisable; consider removing the headline name. |
| RMT.lean:217 | A | `wignerGraphon` | `realise := fun _ => {kernel := 0, ...}`, `uniformBound := 0` — every realisation is the zero kernel; file's own comment admits it suppresses ALL Wigner statistics. | encode a genuine random off-diagonal kernel (or mark explicitly as the centred-mean degenerate rep). |
| RMT.lean:408,411 | A | `WStarProbSpace.isWStarAlgebra` / `.trace_isTracial` | `: True` structure fields (von Neumann + tracial axioms stubbed). | carry the actual W*/tracial axioms or a TODO marker, not `True`. |
| RMT.lean:817,838,857,797 | F | `open_problem_WL_RMT_universality`, `..._free_cumulant_expansion`, `..._quaternionic_graphplay`, `gse_quaternionic_graphplay_open` | each "open problem" Prop is substituted by a TRIVIALLY-true placeholder: `P.symmQuotient.IsHermitian` (true for ALL quotients) or `∫ semicircle = 1`; the actual open content is gone. `def : Prop`, undischarged but degenerate. | encode the real open statement, or drop to a comment. |
| TensorNetworks.lean:318,325 | D/B | `IsExactMERA` / `mera_exact_iff_equitable` | `IsExactMERA := Nonempty (EquitableMERA M)`, so the "headline" iff is `Iff.rfl` (definitional tautology). In-file admits the independent dynamical predicate is deferred. | introduce an independent `IsExactMERA` (ground-state-in-image) and state the real equivalence. |
| TensorNetworks.lean:377 | D | `holographic_code_equitable` | both sides `Nonempty (EquitableMERA H.mera)`; same tautology, reduced to `mera_exact_iff_equitable`. | as above. |
| TensorNetworks.lean:263 | A | `EquitableMERALayer.disentangler_preserves_cellUniform` | `: True` field (cell-uniform commutation stubbed). | encode `U • cellUniformSubspace ⊆ cellUniformSubspace`. |
| TensorNetworks.lean:554 | A | `TwoDEquitablePartition.twoD_compat` | `: True` field (row/column equitability stubbed). | encode per-row/col restriction equitability. |
| TensorNetworks.lean:430 | A | `InfiniteMERA.toCochain` (obj) | cochain objects carry `adj := 0` (edgeless), discarding all level-Hamiltonian edge content (in-file admits). | carry real adjacency in the equitable refinement variant. |
| TensorNetworks.lean:609,625,644 | D/F | `open_conjecture_gapped_equitable_tower`, `..._pyhp_equitable`, `..._graphon_mera_limit` | each "open conjecture" Prop is `∀ M, IsExactMERA M ↔ Nonempty (EquitableMERA M)` = a definitional tautology (provably true), not the intended conjecture. | restate against an independent `IsExactMERA`. |
| TensorNetworks.lean:489,509,564,580 | D | `exact_mera_groundstate_preparation`, `tensor_network_compiler`, `peps_exact_iff_two_d_equitable`, `peps_on_surface` | each weakened to a trivial projection (return the witness / `T.base` / a PUnit-fiber PEPS); honestly-weaker but content-light. | state the genuine circuit-depth / biconditional claims. |
| TQFT.lean:379 | A | `LevinWenBundle.pentagon` | `: True` (F-symbol/pentagon coherence stubbed). | encode pentagon/hexagon axiom. |
| TQFT.lean:394 | B/D | `levinWen_fiberLabel_total` | `∃ a, LW.fiberLabel i = a` proved `⟨LW.fiberLabel i, rfl⟩` — "a total function is total". | drop or replace with a sector-partition statement. |
| TQFT.lean:618 | D/B | `torus_modular_action` | "projective SL₂(ℤ) rep" weakened to `∃ ρS ρT, ρS = M.S ∧ ρT = M.T ∧ ρT diagonal` proved via `M.T_diag` — just restates ModularData fields; no group action, no relations. | state the actual projective rep using `M.modular_relations`. |
| TQFT.lean:236 | C | `braid_factors_through_cellUniform` | added `hLocal` hypothesis IS (per-generator) the conclusion; proof is `exact hLocal ...`. In-file flags this honestly as a correctness fix. | derive locality from braiding+equitability instead of assuming it. |
| LatticeGauge.lean:992 | F | `quantum_hall_conductance` | conclusion is `hallConductance s ∅ = 0` (EMPTY plaquette set) via `sum_empty`; hypotheses `B`, `_h` unused. Degenerate quantification. | state on a nonempty plaquette set with the TKNN normalisation. |
| OptimalTransport.lean:140 | D/F | `toTransportPlan` / `:155 toTransportPlan_subStochastic` | returns `W.chiralPart` (purely imaginary ⇒ marginal ≡ 0), so "sub-stochastic" holds only via `0 ≤ 1`; hypothesis `_hW : IsNonnegReal W` unused; carries no transport mass. | return a genuine (real, mass-carrying) sub-stochastic plan; use `_hW`. |
| OptimalTransport.lean:315 | D/B | `transportPlan_equitable_decomp` | `W = quotient + residualKernel` proved `simp [residualKernel]` because `residualKernel := W - quotient` by definition — `a = b + (a-b)`. | mild; fine as a defn-unfold lemma but not a "decomposition theorem". |
| MachineLearning.lean:272 | D/B | `attention_compression_bound` | "spectral compression bound" = `(symmQuotient.transpose).rank ≤ card I` via `Matrix.rank_le_card_width` — a universal fact for ANY I×I matrix; partition `P` is unused in the conclusion (only fixes the type). | state effective-rank of the FULL attention operator on symmetric inputs (the real compression). |
| MatrixInversion.lean:134 | A | `ctqwInverter` | `:= S.A⁻¹` — the "ideal CTQW inverter" just IS the inverse (the walk-implements-inversion content is asserted only in prose). | acceptable as ideal-limit defn, but flagged: it removes the walk. |
| MatrixInversion.lean:140 | D | `ctqwInverter_mulVec` | `(ctqwInverter).mulVec b = solution` is `rfl` because both sides are `A⁻¹ b` by the stub above. | inherent to the ideal-inverter modelling choice. |

## Clean / honest files

- **QuantumAdvantage.lean** — CLEAN. Genuinely proven flagship: Rabi amplitude
  (`rabi_amplitude`, `..._norm`), exact complete-graph 2×2 search block
  (`completeGraph_2d_block`), search upper/half bounds, pigeonhole classical
  lower bounds (`classical_search_lower_bound`, `..._two_candidates`), and the
  separation (`quantum_search_quadratic_advantage`, `quantum_cost_below_classical`).
  No `True`, no vacuous hypotheses; sorries are genuinely absent in the flagged decls.
- **AttentionComplexity.lean** — CLEAN. `blockAttentionApply_eq_fullAttentionApply`
  is real (uses `hblock`); cost equalities/inequalities are honest arithmetic;
  `training_step_linear_under_equitable` is gated by a satisfiable structural
  `hblock`. The one `sorry` (`attention_quantum_composition`) is an honest deep deferral.
- **QuantumMarkov.lean** — CLEAN. All defs carry real algebraic constraints
  (Kraus trace-preservation, POVM completeness, density-operator PSD); `prob_sum`,
  `apply_zero` are genuine; sorries (`classical_reachable_finite_horizon`,
  `qomdp_reachability_undecidable`, `equitable_reduces_to_quotient`) are honest
  deep-theorem deferrals with non-vacuous statements. Note: the file already
  CORRECTED a previously-false `¬∃ DecidablePred` undecidability phrasing.

## Summary counts

Total findings: **42** (across 9 files; 4 files clean: QuantumAdvantage,
AttentionComplexity, QuantumMarkov, and effectively-clean MatrixInversion modulo
the 2 ideal-inverter modelling flags).

By category (a finding may carry a slash; counted by primary letter):
- **A (placeholder def):** 14 — Hodge:834; MFG:165, 652, 677; WL:323, 482, 526, 157; RMT:217, 408, 411; TN:263, 554, 430; TQFT:379; MatInv:134  *(note: 16 A-rows; some share lines)*
- **B (trivial conclusion):** WL:587; TQFT:394; (+ B/D blends: MFG:731, TN:325, OT:315, ML:272, TQFT:618)
- **C (vacuous hypothesis):** WL:558; TQFT:236
- **D (stub-driven green vacuity — most important):** Hodge:1002, 1066, 864, 1037; MFG:170, 194, 658; WL:537, 489; TN:318/325, 377, 489/509/564/580; OT:140/155, 315; ML:272; MatInv:140
- **E (false-as-stated, survives via sorry/stub):** WL:335, 503, 729; MFG:194
- **F (degenerate quantification):** WL:130, 220, 729; RMT:817/838/857/797; TN:609/625/644; LG:992; OT:140

Worst offenders (genuinely hollow despite looking proven, fix first):
1. **Hodge §7–8 PST/encoding cluster** (harmonicEvolve = id ⇒ all dynamics trivial).
2. **MeanFieldGames `MildSolution := True`** (poisons the LQR existence/optimality theorems).
3. **WLRefinement stub trio** (`stablePartition2 := id`, `EigenvalueSupport := univ`,
   `QuantumWLStable := coherentAlgebra`) ⇒ two false-as-stated theorems
   (`coherentAlgebra_eq_2WL_span`, `phantom_symmetries_exist`) + degenerate green ones.
4. **TensorNetworks `IsExactMERA := Nonempty(EquitableMERA)`** ⇒ headline iff + 3 "open
   conjectures" are definitional tautologies.

Report path: `/Users/ember/dev/graphplay/paper/coverage/vacuity_scan_integrations.md`
