# Graphplay — Definitive Results Ledger

**Purpose.** Per-theorem axiom-status audit of every *headline* theorem, for the
paper and the Tamon email. This is the honesty firewall: a theorem is **AXIOM-CLEAN**
only if `#print axioms` reports *exactly* `[propext, Classical.choice, Quot.sound]`
(the three standard Lean/Mathlib foundational axioms). Any appearance of `sorryAx`
means the theorem **depends on an open `sorry`** and is **NOT clean** — recorded
below with the precise honest gap.

**Method.** `lake build Graphplay` (3929 jobs, completes successfully) then
`#print axioms <fully-qualified-name>` on each headline theorem via a scratch file
(`/tmp/AxCheck.lean`) run with `lake env lean`. Audit-only: no `.lean` file was
edited.

**Date:** 2026-06-02 (re-audited) · **Mathlib:** local checkout at `/Users/ember/src/mathlib4`
(v4.30.0-era) · **Lean toolchain:** as pinned by the project (leanprover/lean4 v4.30.0).

> **2026-06-02 (late) — the Godsil PST⇔ratio bridge is complete, and the residue is certified.**
> Full `lake build Graphplay` GREEN (3962 jobs); four commits (`593572c`→`91425c8`), every headline
> below self-verified `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
>
> - **Godsil's existence-of-PST theorem, both directions, machine-checked.** Perfect state transfer
>   is now characterised end-to-end. The honest condition is `IsGodsilPSTReady` — arithmetic
>   alignment of the eigenvalue support (`λ = b + a·k(λ)`) **plus** the parity sign `(−1)^{k(λ)}` on
>   the cross-projector entries — *not* the textbook `IsStronglyCospectral ∧ IsGodsilRatio`, which is
>   **false** (a simple-spectrum graph makes every pair strongly cospectral with a free cross-phase;
>   counterexample recorded in-file). `isPST_exists_of_isGodsilPSTReady` (**CLEAN**): the **backward**
>   half — PST at the *exact* time `τ=π/a`, a common-period construction, no Diophantine
>   approximation and no Mathlib gap. `isGodsilPSTReady_of_isPST_of_isSymm_of_fullSupport` (**CLEAN**,
>   in `Periodicity` to break the import cycle): the **forward** half, via the sign-pinning lemma
>   `cross_phase_sign_of_isPST_of_isSymm` (real-symmetric two-sided PST forces the cross phase to a
>   real `±1`) + periodicity. `isPST_exists_iff_isGodsilPSTReady_of_isSymm_of_fullSupport` (**CLEAN**):
>   the full iff. It **fires**: `path_P2_PST_residual` (K₂ at `π/2`) and `Tree.leaf_PST_T2` (K_{1,2}
>   at `π/√2`) are concrete PST closed *through* the bridge.
> - **CFI / Weisfeiler–Leman.** `cfi_1wl_indistinguishable` (**CLEAN**): the C₆ vs 2·K₃ pair — non-
>   isomorphic, both 2-regular, identical 1-WL stable colourings — formalised concretely (the
>   textbook phantom-symmetry witness).
> - **Capstone certification of the whole residue.** An adversarial sweep migrated **~30
>   false-as-stated theorems to TRUE** (each with a documented counterexample — e.g.
>   `braidGate_iff_chernMatched : ↔ True` → `↔ m=0`; Kantorovich strong duality given its Polish+lsc
>   hypotheses; `satisfies_quotient` given the two it silently dropped; a WL theorem refuted *using*
>   the new `path_P2_PST`) and **closed ~34** axiom-clean. Declaration-level `sorry`s **119 → 85**.
>   Two TRUE-but-hollow theorems were left honest and **flagged** rather than closed with their
>   degenerate witnesses; the PST-spine cluster honestly closed *nothing* where the path/hypercube
>   classification genuinely needs a deeper eigenvalue-explicitness bridge. **Every remaining `sorry`
>   is certified TRUE honest-floor** — cited-classical facts Mathlib lacks (MIP\*=RE,
>   QOMDP-undecidability, Villani strong duality, Niven irrationality, CFI k≥2).
>
> - **Inward close-out (the last reachable infra).** `kernelIntegralCLM_isCompactOperator`
>   (**HS ⟹ compact**) is now **fully axiom-clean — no `sorryAx` anywhere**: the density leaf
>   `exists_separable_tendsto_kernel` (L²⊗L² dense in L²(μ⊗μ)) is proved via the measurable-rectangle
>   `IsSetSemiring` + Mathlib's in-measure rectangle approximation. The **path endpoint-PST
>   classification** is closed on the no-PST side (`path_P4_no_PST`, `path_long_no_PST_residual`,
>   **CLEAN**) through a new, reusable eigenvalue + Krylov-controllability bridge
>   (`pathEigenvalue_mem_range` from `charpoly = Chebyshev U`, `path_endpoint_fullSupport` from a
>   unit-determinant Krylov matrix) feeding the Godsil forward bridge — and **corrected a folklore
>   slip**: unweighted `Path n` has endpoint PST iff **n ∈ {1,2}** (2–3 vertices, Coutinho), *not* a
>   longer list (the mistaken `P₆` PST target was numerically refuted — max amplitude ≈ 0.9997 — and
>   **not** proved). Two flagged-hollow OT theorems de-hollowed (`quantum_sampler_existence` under
>   `‖start‖=1, t>0`; `sinkhorn_rate_quotient_bound` pinned to the Birkhoff projective-metric
>   coefficient `tanh(Δ/4)`). Declaration-level `sorry`s now **81**, all certified honest-floor.
>
> **2026-06-02 re-audit.** Full `lake build` GREEN (7894 jobs, exit 0 — no `error:` lines;
> `Conjecture93` recovered, every remaining `sorry` an honest leaf). Three new CLEAN-headline
> groups this pass, each `#print axioms`-verified `[propext, Classical.choice, Quot.sound]`:
> - **DTQW Szegedy lifts** — `cellUniformSzegedyPST_iff_quotient`,
>   `cellUniformSzegedyMixing_iff_quotient` PROVEN in `DiscreteTime/Lifts.lean` (the
>   Doliwa-open discrete-time analogue; predicates re-keyed onto the honest *doubled* form
>   after a free-vertex-head fake-closure was caught; orphan `StdLib/SzegedyQuotientLift.lean`
>   deleted). **Residue RESOLVED (later same day):** the deep `szegedyQuotient_eq_quotientWalk`,
>   *as previously stated* (gated on `Q.adj = P.symmQuotient`), is **FALSE** — the compression
>   is the *lumped* cell-chain, not the symmQuotient-weighted walk (extra `1/√|C_b|`;
>   counterexample `K_{1,3}` with leaves split `{1}⊔{2,3}`, ‖Δ‖ = 0.237 ≠ 0). The
>   genuinely-correct decomposition `szegedyQuotient_factor` +
>   `szegedyQuotient_eq_quotientWalk_of_coinAmp` (under `hcoin : Q.szCoinAmp = compression
>   amplitude`, satisfied non-vacuously by the raw branching quotient `Q.adj = P.quotient`) is
>   PROVEN **axiom-clean**; the lifts never depended on the residue (re-verified).
> - **LDT soundness** — `alpha_gc_gamma` (graphplay's **first** `GaloisConnection`),
>   `dedRun_preserves_solutions`, `solved_state_is_correct` in
>   `Integrations/LatticeDeduction.lean`: verified soundness skeleton for Lattice Deduction
>   Transformers (arXiv:2605.08605), the Knaster–Tarski lfp/gfp DUAL of the refinement quotient.
> - **Tower-9** — `Graphplay/Tower9.lean`: the `AbstractInterpretation` interface (a Galois
>   connection + the Cousot `lfp_transfer`/`gfp_transfer` theorems) with BOTH legs as
>   instances — `ldtAbstraction` (deduction, a lossy *connection*: `ldt_lossy`, `α∘γ ≠ id`) and
>   `partitionAbstraction` (refinement, an exact *insertion*: `partition_is_insertion`,
>   `α∘γ = id`, via Mathlib `Setoid.gi`). `refinement_deduction_duality` machine-states the
>   same-interface/opposite-species duality; LDT run-soundness re-derives as a `gfp_transfer`
>   corollary. All axiom-clean. Honest scope: the specific `wlStep`-gfp =
>   `wlRefine_coarsestEquitable` identity is documented future work.
> - **LDT soundness/completeness deepening** — `Integrations/LDTSoundness.lean`:
>   `checkedSolve_sound` (soundness = output verification, holds for an *arbitrary* solver / any
>   trained net — training-independent, the SAT-solver guarantee), `id_sound_but_useless`
>   (soundness ⟂ power), `certifiedStep_sound`/`certifiedSoundStep` (proof-carrying per-step
>   soundness), `dedP_certified`. And `Integrations/LDTCompleteness.lean`: `acStep` (generalized
>   arc consistency, a `certifiedSoundStep` — sound for free), and the **machine-checked
>   incompleteness witness** `acStep_xor_sound_but_abstains` (one sound AC operator, stuck at ⊤
>   on a solvable XOR system → abstains) vs `ac_kind_discriminates` (same operator *solves* a
>   width-1 chain). All axiom-clean. Conclusion: soundness is free/training-independent; the real
>   bound is COMPLETENESS = problem width vs lattice expressiveness (bounded-width CSP dichotomy).
>   Author-facing writeup: `research/ldt_theory_for_authors.md`.
> - **LDT theory — full layer (all axiom-clean, self-verified `#print axioms`).**
>   `LDTSoundnessRun.lean`: sound refutation (`conflict_implies_unsat`), a training-checkable
>   soundness criterion (`sound_of_dominates_dedP`), the correct-or-abstains pair
>   (`never_confidently_wrong`, `no_false_refutation`), `SoundStep` compositionality (`comp_assoc`),
>   trace-level correctness (`certified_trace_correct`).  `LDTPolymorphism.lean`: the algebraic
>   signature of the kinds — `xor_affine` (Maltsev), `xor_no_majority`, `chain_semilattice` (+ the
>   defining identities) and `famCons_closed_meet` (a semilattice polymorphism closes the solution
>   set under meet).  `LDTHierarchy.lean`: the pair domain is strictly richer than per-cell
>   (`alpha_eq_top` vs `gammaPair_alphaPair_eq`, `pair_strictly_richer_than_cell`,
>   `pair_narrows_where_cell_stuck`).  `LDTKindChecker.lean`: a **runnable** (`#eval`) classifier
>   `acSolves?` (chain ⇒ `true`, XOR ⇒ `false`), verdicts proved by `decide` — fixed from a 35-min
>   hang to ~10s by memoizing the fixpoint iteration (the slowness was exponential thunk
>   re-evaluation, not the math).
> - **ML (walkformer track, behavioral):** the 1-WL irreducibility rank-floor is now *measured*
>   (`restrans/WALK_DISTILLATION_FINDINGS.md`): grafting pure walk operators onto a trained
>   pythia-70m recovers 0.93→0.69 of positional-head function vs 0.44→0.23 for content heads (a
>   3–4× expressibility gap by head type); honest caveat — the signal is recovered-fraction, not a
>   raw-perplexity cliff; NOT a universal compressor.
> - **Application honesty** — false hardware-fit claims relabeled true
>   (`heavyHexAsBundle_dataVertex_equiv`, `…_satisfies_dropCount`, dephasing `…_iff_singleton`).
>
> **2026-06-01 re-audit.** Full `lake build Graphplay` (3952 jobs) + `#print axioms` re-run
> on every headline theorem via scratch files (`/tmp/AxCheck*.lean`, run with `lake env
> lean`). **Build note:** one *non-headline* leaf, `Graphplay.Dowsing.Conjecture93`, is
> currently RED (a parallel agent's mid-refactor: unknown identifiers
> `conjecture93_weak_forward` / `fin1Cell_no_chiral_speedup`); Lake builds all other targets,
> and every headline below built and was axiom-checked successfully. This re-audit promotes
> three groups whose status changed since 2026-05-31:
> - **CHSH/Tsirelson** → now GENUINE & UNCONDITIONAL (the uninhabitable `[TsirelsonBound]`
>   class was deleted/fixed; `CHSH_correlator_bound` carries no typeclass);
> - **Tower-8** (equitable-partition = bisimulation) → exists, axiom-clean;
> - **hypercube PST + uniform mixing** → axiom-clean.
>
> **2026-05-31 re-audit (prior).** `#print axioms` was re-run on every headline theorem AND
> each was given an **adversarial statement-soundness read** — because a theorem can be
> perfectly axiom-clean yet **vacuous** (`#print axioms` does NOT catch a hollow
> statement). Both dimensions are now tracked. Several axiom-clean-but-hollow headline
> statements were found and corrected with real content (no `sorry` introduced); see the
> Statement-soundness table. **Process rule going forward: a result counts as a "headline"
> only if it passes BOTH `#print axioms` (no `sorryAx`) AND an adversarial non-vacuity read.**

---

## TOP-LINE SUMMARY

### Dimension 1 — Axiom status (`sorryAx`)

Of the previous ledger's **four** `sorryAx` headline gaps, **two are now CLOSED / CLEAN**:
- `corrected_equitable_attention` (complex+real Eckart–Young) — **CLOSED, CLEAN** (the spectral-theorem truncation bound is now proven).
- `bipartite_equitable_dirac_cone` (honeycomb Dirac cone) — **CLOSED, CLEAN** (all three conjuncts incl. local linearity now proven).

**New CLEAN headlines promoted 2026-06-01** (axiom-checked this re-audit):
- `CHSH_correlator_bound` + the Tsirelson stack (`CHSHRealization.le_two_sqrt_two`,
  `chshOp_norm_le`, `ofAbsLeTwo`, `CHSH_quantum_value`) — **GENUINE & UNCONDITIONAL**
  (the uninhabitable `[TsirelsonBound]` class was fixed; the correlator bound carries no
  typeclass). See the CHSH/Tsirelson section + its non-vacuity caveat.
- Tower-8 `equitable_isBisim`, `coarsest_equitable_isCoarsest_bisim`, `stepInv_preserved`
  (+ wrappers) — **CLEAN**, no `sorry` token in the file (deep converse carried as an
  explicit hypothesis, not a `sorry`).
- `hypercube_PST_antipodal` (origin→antipode PST at `τ=π/2`) and `hypercube_uniformMixing`
  (instantaneous uniform mixing at `τ=π/4`) — **CLEAN**.

That leaves the genuine axiom-status frontier (unchanged from 2026-05-31):

| Theorem | Status | Honest note |
|---------|--------|-------------|
| `lattice_search_dimension_threshold` | **`sorryAx` (OPEN)** | the `d>4` threshold needs the Childs–Goldstone spectral integral (quant-ph/0306054). Labeled in-file as a conjecture; **do NOT claim it.** Its dependent `buildable_lattice_dynamical_contrast` inherits the `sorryAx`. |
| `hypercube_search_optimal_timing` (general `d≥2`) | **CONDITIONAL (open hypothesis)** | NOT `sorryAx`, but axiom-clean *only modulo* the named OPEN hypothesis `HypercubeChainAmplitudeBound` (the Krawtchouk chain-amplitude bound), never discharged for `d≥2`. The `d=1` case `hypercube_search_optimal_d1` (`Q_1=K_2`) IS unconditionally CLEAN. Do not present general-`d` as proven-unconditional. |

The mathematical **spine, attention collapse, irreducibility floor, both Eckart–Young
theorems, JW intertwiner, path cospectrality, chiral-K₄ mixing, and NTK subset are
machine-verified CLEAN** (`[propext, Classical.choice, Quot.sound]` only).

### Dimension 2 — Statement soundness (the vacuity audit, NEW 2026-05-31)

An adversarial read found several headline statements that were axiom-clean but **hollow**.
All corrected with real content (no `sorry` introduced):

| Theorem | Was | Now |
|---------|-----|-----|
| `quantum_search_quadratic_advantage` (+ `_exact`, ML versions) | classical Ω(n) clause **VACUOUS** (`∀ Q, card Q < n → ∃ w ∉ Q` = pure pigeonhole, zero query content) | genuine **impossibility theorem** `no_correct_QLocal_certifier`: no `Q`-local correct certifier exists for `card Q < n−1`, via an indistinguishability lemma + a proven-nonempty algorithm class. Separation now honest on BOTH halves. |
| `IsOptimalCTQWSearch` timing budget | `∃ C, τ ≤ C·√N` — free unbounded `C`, non-constraining | fixed `τ ≤ π·√N` (K_n achieves `π/2·√N`); the timing conjunct is now load-bearing. |
| `discrete_irreducibility_floor` → `residual_rank_floor` | `rank A ≤ n+k` (trivially true) | `rank A ≤ rank(blockpart)+k` (genuinely below the `n` ceiling). |
| `hardCore_eq_XY_oneDim` | `∃ Hxy U, U·H=Hxy·U` — free `Hxy`, degenerate witness `U=1,Hxy=H` | non-degenerate (pins the genuine string-unitary + concrete conjugate). **CAVEAT: the conjugate's identity with the textbook XY Hamiltonian `Σ(XX+YY)` is still an OPEN computation — do not yet claim "hard-core = XY".** |
| `CHSH_correlator_bound` | false-as-stated (`12−16·win`); then briefly routed through the uninhabitable `[TsirelsonBound]` class (vacuously conditional) | corrected to `|8·win−4| ≤ 2√2` and **UNCONDITIONAL** — no typeclass; the bound is now *derived* from the proven operator-algebra theorem `CHSHRealization.le_two_sqrt_two` (= `chshOp_norm_le`) given inhabitable realization hypotheses. See the dedicated CHSH/Tsirelson section. |
| 3× WLRefinement-int, 4× ML-headline | false-over-arbitrary-objects / vacuous existentials | restated to canonical objects / real content (chiral-K₄ mixing, ALiBi geometric tail), proven. |

---

## DETAILED LEDGER BY AREA

Legend: **CLEAN** = `[propext, Classical.choice, Quot.sound]` only.
**sorryAx** = depends on an open `sorry`.

### Spine

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `EquitablePartition.cellUniformPST_iff_quotientPST` | `PST/QuotientIff.lean:407` | Cell-uniform PST on host `G` ⟺ ‖exp(−iτ Q̃)ⱼᵢ‖=1 on the symmetric quotient Q̃ (the keystone equivalence). | **CLEAN** | — |
| `EquitablePartition.restrict_eq_symmQuotient` | `Equitable.lean:425` | `G.adj` restricted to cell-uniform vectors acts exactly as `Q̃.mulVec` on the cell coefficients (the intertwining identity). | **CLEAN** | — |
| `EquitablePartition.spectrum_subset` | `Spectral.lean:134` | `spectrum Q̃ ⊆ spectrum G.adj` under nonempty-cells hypothesis `∀ i, 0 < cellCard i`. | **CLEAN** | — (hypothesis is honest, documented) |
| `search_quotient_reduction` | `Search.lean:243` | Search Hamiltonian on cell-uniform vectors reduces to `(−γ·Q̃ − markedDiag)` on the marked-refined quotient. | **CLEAN** | — |
| `WeightedGraph.cartesianProduct_pst` | `Product/PST.lean:241` | PST on `G` (u₁→u₂, τ) + periodicity of `H` at `w` ⇒ PST on `G □ H` at `(u₁,w)→(u₂,w)`. | **CLEAN** | — |

### QuantumAdvantage

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `QuantumAdvantage.quantum_search_quadratic_advantage` | `Integrations/QuantumAdvantage.lean` | ∃ quantum time ≤ 2√n hitting success 1, AND the **genuine** classical lower bound: no `Q`-local correct certifier exists for `card Q < n−1` (`no_correct_QLocal_certifier`, impossibility — NOT the old pigeonhole vacuity). | **CLEAN** | — (classical half de-vacuoused 2026-05-31). |
| `QuantumAdvantage.quantum_search_exact_amplitude` | `Integrations/QuantumAdvantage.lean:638` | Exact finite-`n` Rabi: ∃ t_q ≤ (π/2)√n with `exactSearchAmplitude n t_q ≥ √(1/2)` (no n→∞ idealization). | **CLEAN** | — |
| `QuantumAdvantage.ml_structured_search_quantum_advantage_exact` | `Integrations/QuantumAdvantage.lean:949` | Structured-ML search: exact O(√r) quantum amplitude ≥ √(1/2) AND classical < r query lower bound. | **CLEAN** | — |
| `QuantumAdvantage.completeGraph_2d_block` | `Integrations/QuantumAdvantage.lean:498` | Kₙ search evolution on the marked vertex equals the 2×2 reduced-block `exp(−iτ·reducedH)` entry. | **CLEAN** | — |

### CHSH / Tsirelson (NEW SECTION — promoted to GENUINE & UNCONDITIONAL 2026-06-01)

**Status change.** The CHSH/Tsirelson headlines were previously **vacuously
conditional**: the bound rested on a `[TsirelsonBound]` typeclass whose every field
was *provably uninhabitable* (it bounded an arbitrary functional by `2√2`, refutable
at `1000`). That class was rebuilt; the genuine bound now lives in a proven
operator-algebra theorem and the headline correlator bound carries **no typeclass at
all**. All entries below are axiom-checked CLEAN (`[propext, Classical.choice,
Quot.sound]`), verified 2026-06-01.

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `Graphplay.CHSH_correlator_bound` | `QuantumCSP.lean:870` | Two-sided Tsirelson bound `\|8·win(S)−4\| ≤ 2√2` on the signed CHSH correlator. **UNCONDITIONAL** (no `[TsirelsonBound]`); derived from `CHSHRealization.le_two_sqrt_two` given honest realizations of `±(8·win−4)`. | **CLEAN** | — (de-vacuoused; was briefly routed through the uninhabitable class). |
| `LiteratureInterfaces.CHSHRealization.le_two_sqrt_two` | `LiteratureInterfaces.lean:256` | **Tsirelson's bound, the real theorem.** Any quantum-realized CHSH value (4 commuting self-adjoint ±1 involutions + a norm-≤1 state) is `≤ 2√2`. Rests on the genuine operator-norm proof `chshOp_norm_le`. | **CLEAN** | — |
| `LiteratureInterfaces.chshOp_norm_le` | `LiteratureInterfaces.lean:165` | The operator-norm bound `‖A₀B₀+A₀B₁+A₁B₀−A₁B₁‖ ≤ 2√2` (the C\*-algebra core of Tsirelson). | **CLEAN** | — |
| `LiteratureInterfaces.CHSHRealization.ofAbsLeTwo` | `LiteratureInterfaces.lean:278` | **Inhabitability witness:** every value with `\|v\|≤2` has an explicit `CHSHRealization` (algebra `ℂ`, observables `1`, state `(v/2)·Re`). Proves the corrected interface is satisfiable. | **CLEAN** | — (covers the classical regime `win∈[0.25,0.75]`; see non-vacuity caveat). |
| `Graphplay.CHSH_quantum_value` | `QuantumCSP.lean:821` | `QuantumValue CHSHGame = (2+√2)/4 = cos²(π/8)` (win-probability form), given inhabitable realization + tightness hypotheses; upper half discharged via the proven `le_two_sqrt_two`. | **CLEAN** | — (hypotheses inhabitable, not the old uninhabitable universal). |

**Non-vacuity caveat (honest).** `CHSH_correlator_bound` / `CHSH_quantum_value` take
`CHSHRealization` *hypotheses*. Those hypotheses are genuinely **inhabitable** —
`ofAbsLeTwo` exhibits a concrete witness for every `\|v\|≤2` (the entire classical
regime), so this is **not** the old vacuity. The witness for the strictly-quantum tail
`v∈(2, 2√2]` (Tsirelson's optimal *entangled* strategy on `ℂ²⊗ℂ²`) is the **one
deferred `sorry`** in the `TsirelsonBound` *instance's* `value_tight` field
(`LiteratureInterfaces.lean:391`) — it needs a matrix-`C*`-algebra instance Mathlib
does not yet provide, on a *true* proposition. **Neither headline theorem routes
through that instance or its `sorry`** (both are axiom-clean). So: the *bound* is real,
unconditional, and proven; the only deferred piece is a constructive Lean *witness*
that the bound is *tight*. The class itself is now genuinely INHABITED (the `v=2`
realization discharges `value_tight` for all `ε > 2√2−2 ≈ 0.83`).

### Tower-8 — equitable partition = bisimulation (NEW SECTION 2026-06-01)

`Graphplay/Tower8.lean` (+ `Tower8/DistributedQuotient.lean`) identifies the
classical *equitable partition* with the *coarsest bisimulation* of the graph-as-Moore-
coalgebra (Milner–Park bisimulation / Paige–Tarjan relational-coarsest-partition / 1-WL
colour refinement). All entries axiom-checked CLEAN 2026-06-01. **There is no actual
`sorry` token in either file**; the genuinely-deep Paige–Tarjan *converse pairing* (that
an arbitrary abstract bisimulation on the vertex coalgebra is *itself* an equitable
partition) is **isolated as an explicit hypothesis** rather than left as `sorry` — see
the honesty note below.

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `EquitablePartition.equitable_isBisim` | `Tower8.lean:310` | **Keystone:** cell-equality `cells x = cells y` is a genuine bisimulation of the vertex coalgebra; the `obs_eq` obligation is *literally* `P.uniform`. | **CLEAN** | — |
| `Tower8.bisim_refines_wlStable` | `Tower8.lean:498` | Every equitable partition (hence its cell-bisimulation) refines the WL-stable colouring (= `WL.wlRefine_coarsestEquitable`). | **CLEAN** | — |
| `Tower8.wlStable_isBisim` | `Tower8.lean:527` | The WL classes themselves form a bisimulation (coarsest-ness, the other direction). | **CLEAN** | — |
| `Tower8.coarsest_equitable_isCoarsest_bisim` | `Tower8.lean:571` | **Paige–Tarjan = 1-WL** in its correct relational-coarsest-partition form: a bisimulation of `vertexCoalg P` that **refines the base cell partition** refines WL. | **CLEAN** | — (PROVED; see converse note). |
| `Tower8.TransitionCoalg.stepInv_preserved` | `Tower8.lean:372` | Safety preservation (mirror of dregg2 `stepComplete_preserves`): a one-step-invariant predicate holds along any reachable run. | **CLEAN** (no axioms at all) | — |
| `EquitablePartition.cellUniformPST_iff_quotientPST_bridge` | `Tower8.lean:453` | Re-exports the Tower-3 PST iff through the Tower-8 observational-quotient lens (thin wrapper, no new obligation). | **CLEAN** | — |

> **Tower-8 honesty note (the "one honest converse" gap).** The deep half of
> Paige–Tarjan is the *converse pairing*: that an arbitrary abstract bisimulation `R`
> on the vertex coalgebra (not assumed to come from an equitable partition) is in fact
> an equitable partition, so `bisim_refines_wlStable` applies. The vertex coalgebra has
> an **identity successor**, so an abstract bisimulation of it carries *only* the
> one-round `obs_eq` constraint — which is **strictly weaker** than equal WL colour (the
> same-degree relation on `P₄` is a bisimulation that does not refine WL). The naive
> "every bisimulation refines WL" is therefore **FALSE and is not claimed.**
> `coarsest_equitable_isCoarsest_bisim` instead adds the standard relational-coarsest-
> partition hypothesis (`hfine`: the candidate already refines the initial blocks `P`),
> satisfied by the cell-equality bisimulation and every finer one — the genuine,
> non-vacuous, PROVED content. The full converse formalization (turning an arbitrary
> `R`'s `obs_eq` into `P.uniform` and quotienting) is **TRUE but deferred**; it is the
> single honest gap of the rung, carried as an explicit hypothesis, **not** as a `sorry`.

### AttentionComplexity

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `AttentionComplexity.blockAttentionApply_eq_fullAttentionApply` | `Integrations/AttentionComplexity.lean:120` | Block (equitable) attention application equals full attention application exactly. | **CLEAN** | — |
| `AttentionComplexity.attention_apply_linear_in_n` | `Integrations/AttentionComplexity.lean:178` | Block attention apply-cost is linear (O(n·r·d)) in sequence length n. | **CLEAN** (only `propext`) | — |
| `AttentionComplexity.training_step_linear_under_equitable` | `Integrations/AttentionComplexity.lean:348` | One training step is O(n)-linear under the equitable-equivariance hypothesis. | **CLEAN** | — |

### StructuredAttention

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `StructuredAttention.segment_attention_exact_reduction` | `Integrations/StructuredAttention.lean:177` | Segment-pooled attention reduces exactly to the r-cell quotient action. | **CLEAN** | — |
| `StructuredAttention.pooledTokens_equitable` | `Integrations/StructuredAttention.lean:212` | **(this is a `def`, not a theorem)** — the pooled-token equitable partition construction. | **CLEAN** (defn well-formed) | n/a (not a proposition) |
| `StructuredAttention.circulant_banded_cost` | `Integrations/StructuredAttention.lean:361` | Circulant/banded attention cost bound (O(n·w·d)). | **CLEAN** (only `propext`) | — |

### EquitableMechanism

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `EquitableMechanism.no_cheap_exact_factorization` | `Integrations/EquitableMechanism.lean:342` | EXACT floor: `A = equitablePart + R`, `rank R ≤ k` ⇒ `rank A ≤ r+k` (irreducibility lower bound). | **CLEAN** | — |
| `EquitableMechanism.residual_rank_floor` (was `discrete_irreducibility_floor`) | `Integrations/EquitableMechanism.lean` | Sharp floor `rank A ≤ rank(blockpart)+k` (the old `≤ n+k` form was vacuous; now genuinely below `n`). | **CLEAN** | — (de-vacuoused 2026-05-31). |
| `EquitableMechanism.equitable_strictly_generalizes_orbit` | `Integrations/EquitableMechanism.lean:448` | Equitable partitions strictly generalize orbit (automorphism) partitions. | **CLEAN** | — |
| `EquitableMechanism.blockConstant_NTK_subset_spectrum` | `Integrations/EquitableMechanism.lean:512` | Block-constant NTK spectrum ⊆ host spectrum. | **CLEAN** | — |
| `EquitableMechanism.corrected_equitable_attention` (+ `_complex`) | `Integrations/EquitableMechanism.lean` | ε-approximate residual-corrected error bound (real + complex-Hermitian Eckart–Young). | **CLEAN** | — (now CLOSED via the spectral-theorem truncation bound). |

### NovelAttention

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `NovelAttention.chiralAttention_descends` | `Integrations/NovelAttention.lean:162` | Chiral attention descends to the quotient (def + descent lemma `_cells`). | **CLEAN** | — |
| `NovelAttention.PSTRoutingAttention.transfers` | `Integrations/NovelAttention.lean:251` | PST-routing attention transfers state perfectly between routed tokens. | **CLEAN** | — |
| `NovelAttention.quotientResidualAttention_cost` | `Integrations/NovelAttention.lean:421` | Quotient+residual attention cost bound O(n·(r+k)·d). | **CLEAN** (only `propext`) | — |

### Hypercube — PST + uniform mixing (StdLib, CLEAN 2026-06-01)

These are **exact, finite-`n`, unconditional** structural facts about the hypercube
`Qₙ`, distinct from the *search-timing* results below (which remain conditional/open).
Both axiom-checked CLEAN 2026-06-01.

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `StdLib.hypercube_PST_antipodal` | `StdLib/Hypercube.lean:405` | `Qₙ` (`n≥1`) has **PST** from origin to antipode at `τ = π/2` (Christandl et al.; via the `n`-fold `K₂` product model). | **CLEAN** | — |
| `StdLib.hypercube_uniformMixing` | `StdLib/Hypercube.lean:561` | `Qₙ` (`n≥1`) achieves **instantaneous uniform mixing** at `τ = π/4` — every evolution entry has squared modulus `1/2ⁿ = 1/card`. | **CLEAN** | — |

> Note: the **average**-mixing headline on `Qₙ` was found false-as-originally-stated
> (the average mixing matrix is *not* the flat `1/2ⁿ` matrix for `n≥2`); the file now
> carries the corrected non-vacuous content (`hypercube_avgReturn_gt_uniform`,
> `hypercube_not_averageUniformMixing`) plus one named honest `sorry`
> (`hypercube_averageMixing_diag`, the spectral Cesàro packaging) — those are
> *non-headline*; the two PST/mixing headlines above do not route through it.

### SparseSearch

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `SparseSearch.hypercube_sparse_search_reduction` | `Applications/SparseSearch.lean:602` | Qᵈ: (1) regular+log-sparse + (2) equitable reduction to Hamming chain (NO timing clause). | **CLEAN** | — (axiom-clean: `propext, Classical.choice, Quot.sound`). |
| `SparseSearch.hypercube_search_optimal_d1` | `Applications/SparseSearch.lean` | `IsOptimalCTQWSearch (Hypercube 1) w` — the **`d=1` regime** (`Q_1 = K_2`), UNCONDITIONAL. | **CLEAN** | — (axiom-clean: `propext, Classical.choice, Quot.sound`; via `complete_graph_optimal_search`). Genuinely discharged regime of the O(√N) advantage. |
| `SparseSearch.hypercube_search_optimal_timing` | `Applications/SparseSearch.lean` | `IsOptimalCTQWSearch (Hypercube d) w` (the O(√N) *timing* only), for general `d`. | **CONDITIONAL** | **OPEN HYPOTHESIS:** takes `HypercubeChainAmplitudeBound d w` (a named open Krawtchouk chain-amplitude conjecture, NEVER discharged for general `d`). The reduction itself is axiom-clean; the *hypothesis* is open. NOT a proven unconditional result for `d≥2`. |
| `SparseSearch.buildable_lattice_structural_contrast` | `Applications/SparseSearch.lean:1000` | Lattice `2d`-regular/`L^d` vertices + hypercube `e`-regular/`log₂N` (structural only). | **CLEAN** | — (axiom-clean). |
| `SparseSearch.buildable_lattice_dynamical_contrast` | `Applications/SparseSearch.lean:1030` | Lattice NOT optimal (d≤3) WHILE hypercube IS optimal (dynamical contrast). | **sorryAx** | **OPEN:** both dynamical clauses — lattice via `lattice_search_dimension_threshold` (d≤3 half) + hypercube via `hypercube_search_optimal_timing`. |
| `SparseSearch.lattice_search_dimension_threshold` | `Applications/SparseSearch.lean:955` | `IsOptimalCTQWSearch (latticeGraph d L) w ↔ 4 < d` (the dimension threshold). | **sorryAx** | **OPEN:** whole `↔` — needs Childs–Goldstone spectral integral / d>4 IR-convergence. `sorry` at line 960. |
| `SparseSearch.latticeGraph_isRegular` | `Applications/SparseSearch.lean:858` | The d-dim periodic lattice `Z_L^d` is `2d`-regular. | **CLEAN** | — |

### CompileML

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `Applications.CompileML.compiled_cellUniform_realizes_target` | `Applications/CompileML.lean:246` | Compiled cell-uniform spec realizes the target attention matrix. | **CLEAN** | — |
| `Applications.CompileML.compiled_experiment_prediction` | `Applications/CompileML.lean:325` | The compiled experiment's prediction matches the spec. | **CLEAN** | — |
| `Applications.CompileML.compile_recall_to_heron` | `Applications/CompileML.lean:402` | End-to-end recall task compiles to a Heron-class (heavy-hex) host. | **CLEAN** | — |

### TransformerDSL

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `TransformerDSL.Compilable.compile_denote_commutes` | `Integrations/TransformerDSL.lean:273` | Compiler correctness: `denote ∘ compile = denote` (the compile/semantics square commutes). | **CLEAN** | — |
| `TransformerDSL.Compilable.compiler_guarantee` | `Integrations/TransformerDSL.lean:335` | Compiled program is semantically equal AND meets the O(n·(r+d)) cost guarantee. | **CLEAN** | — |

### Applications — IBM Heavy-Hex

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `Applications.IBMHeavyHex.dataFlagQuotient_eigenvalues` | `Applications/IBMHeavyHex.lean:874` | The 2-cell data/flag quotient's eigenvalues (the `±2√(N−1)`-type spectrum). | **CLEAN** | — |
| `Applications.IBMHeavyHex.heavyHex_pst_lift` | `Applications/IBMHeavyHex.lean:1142` | PST on the heavy-hex chip lifts from the data/flag equitable quotient. | **CLEAN** | — |
| `Applications.IBMHeavyHex.dephasing_preserves_dataFlag` | `Applications/IBMHeavyHex.lean:1344` | Dephasing noise preserves the data/flag equitable partition. | **CLEAN** | — |
| `Applications.IBMHeavyHex.dataFlag_chiral_no_speedup` | `Applications/IBMHeavyHex.lean:1429` | Chiral signing of the data/flag graph yields no search speedup (negative result). | **CLEAN** | — |

### Applications — Majorana-1

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `Applications.MajoranaOne.TetronChip.sectorProjector_sum` | `Applications/MajoranaOne.lean:630` | Parity-sector projectors sum to the identity (completeness of the parity decomposition). | **CLEAN** | — |
| `Applications.MajoranaOne.TetronChip.parityQuantumEquitablePartition` | `Applications/MajoranaOne.lean:710` | **(`def`)** the parity-conserving quantum equitable partition. | **CLEAN** | n/a (construction) |
| `Applications.MajoranaOne.TetronChip.payoff2_parity_noise_preserves_partition` | `Applications/MajoranaOne.lean:1062` | Payoff-2 parity-conserving noise preserves the equitable partition. | **CLEAN** | — |

> Note: `MajoranaOne.lean` contains two open `sorry`s at lines 1007 and 1097, but
> these are in **non-headline** lemmas; none of the three headline Majorana
> theorems above route through them (verified: all three are axiom-clean).

### DiracLimit

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `DiracLimit.offDiagonalBloch_eigenvalues` | `Dowsing/DiracLimit.lean:324` | Off-diagonal Bloch Hamiltonian has eigenvalues `±‖f(k)‖`. | **CLEAN** | — |
| `DiracLimit.bipartite_equitable_dirac_cone` | `Dowsing/DiracLimit.lean` | Honeycomb off-diagonal block: (1) band touching at k=π + (2) `±‖f(k)‖` bands + (3) Dirac cone. | **CLEAN** | — (now CLOSED, all three conjuncts incl. the small-`k` local linearity). |
| `DiracLimit.coinedWalk_continuum_dirac_conjecture` | `Dowsing/DiracLimit.lean` | **(`def` — OPEN CONJECTURE, not a proved theorem)** the rescaled coined-walk generator's `2×2` spinor block converges (in op-norm) to the massless Dirac Bloch generator `−i·H_Dirac(k)`. Genuine non-tautological statement (compares two *different* matrices). | n/a (conjecture `Prop`, unasserted) | **OPEN:** quantum-walk → Dirac scaling limit (Meyer/Bisio–D'Ariano–Tosini), no Mathlib scaling-limit calculus. Replaces the former tautological `coinedWalk_continuum_is_dirac` (`‖X−X‖≤ε`). |

### Negative-PST

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `StdLib.dominatingVertex_no_PST` | `StdLib/Join.lean:337` | A vertex adjacent to all others (dominating) cannot have PST. | **CLEAN** | — |
| `StdLib.cone_apex_no_PST` | `StdLib/Join.lean:351` | The apex of a cone graph cannot have PST. | **CLEAN** | — |

---

## INTERPRETATION FOR THE TAMON EMAIL (honest framing)

1. **The mathematical spine is fully axiom-clean.** The five spine theorems
   (`cellUniformPST_iff_quotientPST`, `restrict_eq_symmQuotient`,
   `spectrum_subset`, `search_quotient_reduction`, `cartesianProduct_pst`) — the
   equitable-quotient ⟺ PST keystone and its lifts — carry only the three standard
   foundational axioms. No `sorry` anywhere in the spine.

2. **The quantum-advantage flagship is clean, finite-`n` exact, AND honest on both
   halves.** The quantum upper bound (`quantum_search_exact_amplitude`, `≥ √(1/2)` at
   `t ≤ (π/2)√n`) is axiom-clean. The classical lower bound is now a **genuine
   impossibility theorem** (`no_correct_QLocal_certifier`) — *not* the former pigeonhole
   vacuity. So the √n-vs-n separation is real on both sides.

3. **The attention/ML complexity-collapse results are clean.** The O(n²)→O(n·r)
   structural reduction, its correctness, the compiler-correctness square, and the
   training-step linearity are all axiom-clean.

4. **The CHSH/Tsirelson `2√2` bound is now GENUINE & UNCONDITIONAL.** The headline
   `CHSH_correlator_bound` (`|8·win−4| ≤ 2√2`) carries **no typeclass** — the prior
   uninhabitable `[TsirelsonBound]` class was rebuilt, and the bound is derived from the
   proven operator-algebra theorem `chshOp_norm_le` / `CHSHRealization.le_two_sqrt_two`.
   Its realization hypotheses are inhabitable (`ofAbsLeTwo`, the whole classical regime),
   so this is **not** the old vacuity; the only deferred piece is a constructive Lean
   *witness* that the bound is *tight* (Tsirelson's entangled `ℂ²⊗ℂ²` strategy), isolated
   as a single honest `sorry` in the `TsirelsonBound` *instance* — which neither headline
   routes through.

5. **Tower-8 (equitable partition = bisimulation) is clean.** The keystone
   `equitable_isBisim` (cell-equality is a bisimulation, proof = `P.uniform`), the
   Paige–Tarjan = 1-WL inclusion in its correct relational-coarsest-partition form
   (`coarsest_equitable_isCoarsest_bisim`), and the safety keystone `stepInv_preserved`
   are all axiom-clean, with **no `sorry` token** in the file. The deep Paige–Tarjan
   *converse pairing* is honestly carried as an explicit hypothesis (`hfine`), not as a
   `sorry` — see the Tower-8 honesty note. The **hypercube** PST (`τ=π/2`, origin→antipode)
   and instantaneous uniform mixing (`τ=π/4`) headlines are likewise CLEAN.

6. **The axiom-status frontier is now ONE genuine open `sorryAx` headline**
   (`lattice_search_dimension_threshold`, the Childs–Goldstone d>4 threshold) **plus
   one openly-CONDITIONAL headline** (`hypercube_search_optimal_timing` for `d≥2`,
   modulo the named open Krawtchouk chain-amplitude hypothesis; the `d=1` case is
   unconditionally clean). The previous "four open clauses" are down to these — Eckart–Young
   and the Dirac cone are now CLOSED. **Do not claim the lattice threshold or the
   general-`d` hypercube timing as proven.** Separately, the vacuity audit corrected
   several axiom-clean-but-hollow statements (classical LB, optimal-timing budget, rank
   floor, hard-core/XY) — see the Statement-soundness table. **`hardCore_eq_XY` is
   non-degenerate but does NOT yet prove the XY-Hamiltonian identity; do not claim it.**

---

## POSITIONING — prior art vs. OUR contribution (honest boundary)

**This is a "certificate-and-unification", NOT a "first-contact-novelty", contribution.
State it exactly this way.** The PST-quotient lift is not new mathematics:

- **PST / equitable-quotient lift** = **Bachman–Tamon, arXiv:1108.0339 (2011)**
  ("Perfect state transfer on quotient graphs"). The spine keystone
  `cellUniformPST_iff_quotientPST` and its CTQW lifts (PST, mixing, spectrum, search,
  Cartesian product) are the *mechanization* of that paper's content, not a new theorem.
- **DTQW / Szegedy quotient (aggregation–quantization) square** = **Doliwa et al.,
  arXiv:2603.14269 (2026)**. The discrete-time *subspace-invariance* / quotient square is
  theirs.

**OUR contribution is therefore exactly four things, and we claim only these:**

1. **Mechanization** — the full equitable-quotient ⇒ PST spine, machine-checked
   axiom-clean in Lean 4 + Mathlib (the five spine theorems carry only the three
   foundational axioms).
2. **Unification** — one `EquitablePartition` interface that simultaneously realizes the
   classical/CTQW lift (Bachman–Tamon), the discrete-time/Szegedy square (Doliwa et al.),
   the bisimulation/Paige–Tarjan rung (Tower-8), and the attention/ML complexity collapse,
   under a single mechanism.
3. **The DTQW PST / mixing lifts that the prior work leaves open** — the discrete-time
   analogues of the CTQW iff, now **PROVEN axiom-clean** in `Graphplay/DiscreteTime/Lifts.lean`:
   `cellUniformSzegedyPST_iff_quotient` and `cellUniformSzegedyMixing_iff_quotient` (both
   `#print axioms` = `[propext, Classical.choice, Quot.sound]`, verified 2026-06-02). PST /
   uniform-mixing of a cell-uniform Szegedy walk holds iff the *compression* `szegedyQuotient`
   has the transfer property — proven via the doubled cell-matrix element
   `doubledCellUniform_matrixElement` + the compression identity
   `doubledCellEmbedH_szegedyWalk_pow_doubledCellEmbed`.
   **Honesty correction in this pass:** the original predicates summed a *free vertex-head*
   `∑_y U((x',y),(x,y))`, which is **not** walk-invariant and does **not** equal the
   compression for general `U` — forcing the old bridge would have been a *fake closure*.
   The predicates `IsCellUniformSzegedy{PST,Mixing}` were re-keyed onto the honest **doubled
   form** (cell-resolved head marginal; non-vacuity checked — `IsCellUniformSzegedyPST i i 0`
   fails for `|I|>1`). **The deep residue is now RESOLVED — with a correctness catch.** The
   identification of the compression with the *quotient graph's intrinsic* Szegedy walk, *as
   previously stated* (`szegedyQuotient_eq_quotientWalk`, gated on `Q.adj = P.symmQuotient`), is
   **FALSE**: an adversarial reduction to a single per-edge scalar identity shows the compression
   is the **lumped Markov chain on cells**, carrying an extra `1/√|C_b|` distortion vs
   `symmQuotient` (counterexample: star `K_{1,3}`, leaves split `{1}⊔{2,3}`, magnitude-equitable,
   `‖szegedyQuotient − symmQuotientWalk‖ = 0.237 ≠ 0`). The genuinely-correct decomposition is
   PROVEN axiom-clean: `szegedyQuotient_factor` (`= S_I·(2·ψProj−1)`) and
   `szegedyQuotient_eq_quotientWalk_of_coinAmp` (`= Q.SzegedyWalk` under the honest per-edge
   hypothesis `hcoin : Q.szCoinAmp = compression amplitude`, satisfied non-vacuously by the raw
   branching quotient `Q.adj = P.quotient`). The §5 PST/mixing lifts never depended on this
   residue (re-verified axiom-clean). The redundant `sorry`-blocked orphan
   `Graphplay/StdLib/SzegedyQuotientLift.lean` was deleted.

   **(3″) Tower-9 abstract-interpretation interface (NEW 2026-06-02)** —
   `Graphplay/Tower9.lean`: makes the refinement⊣deduction duality a machine-checked object.
   `AbstractInterpretation` (Galois connection between complete lattices) + the Cousot
   `lfp_transfer`/`gfp_transfer` theorems; the LDT deduction leg (`ldtAbstraction`, a lossy
   *connection*) and the partition/equivalence leg (`partitionAbstraction`, an exact *insertion*
   via Mathlib `Setoid.gi`) as two instances; `refinement_deduction_duality` states the
   same-interface/opposite-species result; LDT run-soundness re-derives as a `gfp_transfer`
   corollary. All axiom-clean. The specific `wlStep`-gfp = `wlRefine_coarsestEquitable` identity
   is documented future work (the colour type grows each round).

   **(3′) LDT soundness (NEW 2026-06-02)** — `Graphplay/Integrations/LatticeDeduction.lean`:
   a verified soundness skeleton for Lattice Deduction Transformers (arXiv:2605.08605).
   `alpha_gc_gamma` is graphplay's **first** `GaloisConnection` (α⊣γ between per-cell candidate
   sets and concrete strings); `dedRun_preserves_solutions` lifts Tower-8 `stepInv_preserved`
   to whole-run soundness; headline `solved_state_is_correct`: a reachable *solved* state on a
   satisfiable instance has `cons = {s}`. All axiom-clean. Honestly a *connection*, not an
   *insertion* (α∘γ ≠ id); models the "returns a correct answer" half, not the abstain/branch
   completeness layer. Companion memo `research/refinement_deduction_duality.md` pins this as
   the **Knaster–Tarski lfp/gfp DUAL** of the WL refinement quotient (not an instance); the
   quantum deduction-dual is a NO.
4. **The verified certificate** — the per-theorem two-dimension audit in this ledger
   (axiom-status AND non-vacuity), which is itself the deliverable: precision as
   credibility.

**Framing rule:** lead with "we mechanize and unify the Bachman–Tamon / Doliwa quotient
picture and supply a machine-verified certificate", *not* "we discovered the quotient
lift". Novelty claims are limited to the *mechanization-grade* contributions: (3) the
discrete-time Szegedy PST/mixing lifts (now proven to the compression, with the one
intrinsic-quotient-walk residue honestly open), (3′) the LDT soundness skeleton, and the
verification artifact. None is new mathematics; all are first-machine-checked.

---

*Verification pass (re-run 2026-06-02): full `lake build` GREEN (7894 jobs, exit 0;
no `error:` lines — every remaining `sorry` is an honest leaf) + `#print axioms` on
each headline via `lake env lean` on scratch files outside `Graphplay/`. The DTQW lifts
(`cellUniformSzegedy{PST,Mixing}_iff_quotient`) and LDT soundness (`alpha_gc_gamma`,
`dedRun_preserves_solutions`, `solved_state_is_correct`) re-verified axiom-clean this pass.*
