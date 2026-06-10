# Graphplay — Definitive Results Ledger

**Purpose.** Per-theorem axiom-status and non-vacuity audit of every *headline* theorem.
This is the honesty firewall. A theorem is **CLEAN** only if `#print axioms` reports
exactly `[propext, Classical.choice, Quot.sound]` (the three standard Lean/Mathlib
foundational axioms) **and** it passes an adversarial non-vacuity read — a theorem can be
axiom-clean yet hollow, and both dimensions are tracked. `sorryAx` means the theorem
depends on an open `sorry`; **CONDITIONAL** means axiom-clean only modulo a named open
hypothesis.

**Method.** `lake build Graphplay` (GREEN, ~7900 jobs, exit 0), then
`#print axioms <fully-qualified-name>` on each headline via scratch files run with
`lake env lean` outside `Graphplay/`. Mathlib: local checkout (v4.30.0-era); Lean toolchain
leanprover/lean4 v4.30.0. Audit-only: no `.lean` file edited for the audit.

**Date:** 2026-06-02.

## Current state (the lines that are real)

- **Spine (CLEAN).** The equitable-quotient ⟺ PST keystone and its lifts:
  `cellUniformPST_iff_quotientPST`, `restrict_eq_symmQuotient`, `spectrum_subset`,
  `search_quotient_reduction`, `cartesianProduct_pst`. Symmetric normalized quotient
  `Q̃ = D^{1/2} Q D^{-1/2}`.

- **Godsil PST characterization (CLEAN, both directions).** For a real-symmetric host
  with full eigenvalue support, PST between `u` and `v` occurs iff `IsGodsilPSTReady u v`:
  arithmetic alignment of the eigenvalue support (`λ = b + a·k(λ)`) together with the
  parity sign `(−1)^{k(λ)}` on the cross-projector entries
  (`isPST_exists_iff_isGodsilPSTReady_of_isSymm_of_fullSupport`). The backward half
  (`isPST_exists_of_isGodsilPSTReady`) gives PST at the exact time `τ = π/a` by a
  common-period construction; the forward half
  (`isGodsilPSTReady_of_isPST_of_isSymm_of_fullSupport`, in `Periodicity` to break the
  import cycle) routes through the sign-pinning lemma `cross_phase_sign_of_isPST_of_isSymm`.
  Concrete instances closed through the bridge: `path_P2_PST_residual` (K₂ at `π/2`),
  `Tree.leaf_PST_T2` (K_{1,2} at `π/√2`). The real-symmetry and full-support hypotheses are
  load-bearing.

- **DTQW Szegedy lifts (CLEAN).** `cellUniformSzegedyPST_iff_quotient`,
  `cellUniformSzegedyMixing_iff_quotient` in `DiscreteTime/Lifts.lean` (the discrete-time
  analogue Doliwa et al. leave open). PST / uniform mixing of a cell-uniform Szegedy walk
  holds iff the compression `szegedyQuotient` has the transfer property, via the doubled
  cell-matrix element. The compression is the **lumped cell-chain**; its identification with
  the quotient graph's intrinsic Szegedy walk holds under the per-edge hypothesis
  `hcoin : Q.szCoinAmp = compression amplitude` (`szegedyQuotient_eq_quotientWalk_of_coinAmp`),
  satisfied by the raw branching quotient `Q.adj = P.quotient`. The §5 lifts do not depend on
  this identification.

- **CHSH / Tsirelson `2√2` (CLEAN, unconditional).** `CHSH_correlator_bound`
  (`|8·win−4| ≤ 2√2`) carries no typeclass; derived from the operator-algebra theorem
  `chshOp_norm_le` / `CHSHRealization.le_two_sqrt_two`. See the CHSH/Tsirelson section.

- **Tower-8 (CLEAN).** Equitable partition = coarsest bisimulation of the graph coalgebra =
  Paige–Tarjan relational-coarsest-partition = 1-WL refinement (`equitable_isBisim`,
  `coarsest_equitable_isCoarsest_bisim`, `stepInv_preserved`). No `sorry` token in the file;
  the converse pairing is carried as an explicit hypothesis `hfine` (the relational-coarsest
  refines-the-base-blocks condition).

- **LDT layer (CLEAN).** Soundness = output verification, training-independent and holding
  for an arbitrary solver (`checkedSolve_sound`, `solved_state_is_correct`); the real bound is
  COMPLETENESS = problem width vs lattice expressiveness. Machine-checked incompleteness witness
  `acStep_xor_sound_but_abstains` (a sound arc-consistency operator abstains on a solvable XOR
  system) vs `ac_kind_discriminates` (same operator solves a width-1 chain). `alpha_gc_gamma` is
  the first `GaloisConnection` in the corpus. Tower-9 packages the refinement⊣deduction duality
  via the Cousot `lfp_transfer`/`gfp_transfer` transfer theorems. Author writeup:
  `research/ldt_theory_for_authors.md`.

- **Hypercube structural facts (CLEAN).** `hypercube_PST_antipodal` (origin→antipode at
  `τ = π/2`) and `hypercube_uniformMixing` (instantaneous uniform mixing at `τ = π/4`), exact
  and unconditional.

- **CFI / Weisfeiler–Leman (CLEAN).** `cfi_1wl_indistinguishable`: the C₆ vs 2·K₃ pair —
  non-isomorphic, both 2-regular, identical 1-WL stable colourings.

**Open / conditional, not claimed as proven:**
- `lattice_search_dimension_threshold` (the `d>4` Childs–Goldstone threshold) — `sorryAx`.
- `hypercube_search_optimal_timing` for `d≥2` — CONDITIONAL on the named open Krawtchouk bound
  `HypercubeChainAmplitudeBound`; the `d=1` case (`Q₁=K₂`) is unconditionally CLEAN.
- `coinedWalk_continuum_dirac_conjecture` (quantum-walk → Dirac scaling limit) — open `def`.

Externals that the corpus depends on but does not prove are carried as named typeclass
assumptions (cited hypotheses the results are conditioned on), not as theorems: Villani strong
duality, the BCLSV graphon limit, MIP\*=RE, Choi, Stinespring, FKLW, Lovász SDP duality,
Birkhoff contraction, HHL convergence. Each is the citation it names.

**Declaration-level `sorry`s stand at 0** (2026-06-10, waves 21/21b: 28 closed, restated,
or demoted). The compiler emits zero `declaration uses 'sorry'` warnings on a full fresh
build. The deep cited-classical facts Mathlib lacks (CNO perturbation bound, Bose–Mesner
FR forward direction, Barry–Barry–Aaronson QOMDP reduction, T-rex weak-coupling resolvent
expansion, CFI gadget family) are carried as content-bearing cited typeclasses
(verbatim-statement fields) or never-asserted `def`-conjectures. Three statements were
*refuted* rather than proven and now stand as machine-checked negations
(`hammingGraph_two_no_nontrivial_fr`, `not_searchSuccess_optimal_time_of_gap_only`,
`HolonomyObstruction.unconditional_gauge_equivalence_false`), and one whole hypothesis
class was shown uninstantiable and redesigned (`EquitableSymmetry.no_nontrivial_cell` →
equivariance). The per-theorem tables below carry the audit of the earlier state; rows
marked sorryAx are superseded by this note.

---

## Statement-soundness table (the non-vacuity dimension)

`#print axioms` does not catch a hollow statement. These headline statements were each
axiom-clean but vacuous; each now carries real content (no `sorry` introduced). The honest
scope is the right column.

| Theorem | Honest statement now proven |
|---------|------|
| `quantum_search_quadratic_advantage` (+ `_exact`, ML versions) | classical lower bound is a genuine impossibility theorem `no_correct_QLocal_certifier`: no `Q`-local correct certifier exists for `card Q < n−1`, via an indistinguishability lemma + a proven-nonempty algorithm class. The √n-vs-n separation is real on both halves. |
| `IsOptimalCTQWSearch` timing budget | `τ ≤ π·√N` (K_n achieves `π/2·√N`); the timing conjunct is load-bearing. |
| `residual_rank_floor` (was `discrete_irreducibility_floor`) | `rank A ≤ rank(blockpart)+k`, genuinely below the `n` ceiling. |
| `hardCore_eq_XY_oneDim` | a non-degenerate intertwiner: the genuine string-unitary and a concrete conjugate of the hard-core Hamiltonian. The conjugate's identity with the textbook XY Hamiltonian `Σ(XX+YY)` is a separate open computation; the proven content is the intertwining, not "hard-core = XY". |
| `CHSH_correlator_bound` | `|8·win−4| ≤ 2√2`, unconditional, derived from `CHSHRealization.le_two_sqrt_two` / `chshOp_norm_le`. See the CHSH/Tsirelson section. |
| 3× WLRefinement-int, 4× ML-headline | restated to canonical objects with real content (chiral-K₄ mixing, ALiBi geometric tail), proven. |

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
| `QuantumAdvantage.quantum_search_quadratic_advantage` | `Integrations/QuantumAdvantage.lean` | ∃ quantum time ≤ 2√n hitting success 1, AND a classical impossibility lower bound: no `Q`-local correct certifier exists for `card Q < n−1` (`no_correct_QLocal_certifier`). | **CLEAN** | — |
| `QuantumAdvantage.quantum_search_exact_amplitude` | `Integrations/QuantumAdvantage.lean:638` | Exact finite-`n` Rabi: ∃ t_q ≤ (π/2)√n with `exactSearchAmplitude n t_q ≥ √(1/2)` (no n→∞ idealization). | **CLEAN** | — |
| `QuantumAdvantage.ml_structured_search_quantum_advantage_exact` | `Integrations/QuantumAdvantage.lean:949` | Structured-ML search: exact O(√r) quantum amplitude ≥ √(1/2) AND classical < r query lower bound. | **CLEAN** | — |
| `QuantumAdvantage.completeGraph_2d_block` | `Integrations/QuantumAdvantage.lean:498` | Kₙ search evolution on the marked vertex equals the 2×2 reduced-block `exp(−iτ·reducedH)` entry. | **CLEAN** | — |

### CHSH / Tsirelson

The `2√2` bound lives in the operator-algebra theorem `chshOp_norm_le`; the headline
correlator bound carries no typeclass. All entries CLEAN.

| Theorem | File | Statement (1-line) | Clean? |
|---------|------|--------------------|--------|
| `Graphplay.CHSH_correlator_bound` | `QuantumCSP.lean:870` | `\|8·win(S)−4\| ≤ 2√2` on the signed CHSH correlator, unconditional; derived from `CHSHRealization.le_two_sqrt_two` given realizations of `±(8·win−4)`. | **CLEAN** |
| `CHSHRealization.le_two_sqrt_two` | `LiteratureInterfaces.lean:256` | Tsirelson's bound: any quantum-realized CHSH value (4 commuting self-adjoint ±1 involutions + a norm-≤1 state) is `≤ 2√2`. | **CLEAN** |
| `chshOp_norm_le` | `LiteratureInterfaces.lean:165` | The operator-norm bound `‖A₀B₀+A₀B₁+A₁B₀−A₁B₁‖ ≤ 2√2` (the C\*-algebra core). | **CLEAN** |
| `CHSHRealization.ofAbsLeTwo` | `LiteratureInterfaces.lean:278` | Every value with `\|v\|≤2` has an explicit `CHSHRealization` (algebra `ℂ`, observables `1`, state `(v/2)·Re`) — the realization hypotheses are inhabited across the classical regime. | **CLEAN** |
| `Graphplay.CHSH_quantum_value` | `QuantumCSP.lean:821` | `QuantumValue CHSHGame = (2+√2)/4 = cos²(π/8)`, given inhabited realization + tightness hypotheses; upper half via `le_two_sqrt_two`. | **CLEAN** |

`CHSH_correlator_bound` and `CHSH_quantum_value` take `CHSHRealization` hypotheses, which
`ofAbsLeTwo` inhabits for every `|v|≤2` (the classical regime). A constructive Lean witness
that the bound is *tight* — Tsirelson's optimal entangled strategy on `ℂ²⊗ℂ²` for the tail
`v∈(2, 2√2]` — is the one deferred `sorry`, in the `TsirelsonBound` instance's `value_tight`
field (it needs a matrix-`C*`-algebra instance Mathlib lacks, on a true proposition). Neither
headline routes through that instance.

### Tower-8 — equitable partition = bisimulation

`Graphplay/Tower8.lean` (+ `Tower8/DistributedQuotient.lean`) identifies the equitable
partition with the coarsest bisimulation of the graph-as-Moore-coalgebra (Milner–Park /
Paige–Tarjan relational-coarsest-partition / 1-WL refinement). All entries CLEAN; no `sorry`
token in either file.

| Theorem | File | Statement (1-line) | Clean? |
|---------|------|--------------------|--------|
| `EquitablePartition.equitable_isBisim` | `Tower8.lean:310` | Keystone: cell-equality `cells x = cells y` is a bisimulation of the vertex coalgebra; the `obs_eq` obligation is `P.uniform`. | **CLEAN** |
| `Tower8.bisim_refines_wlStable` | `Tower8.lean:498` | Every equitable partition refines the WL-stable colouring (= `WL.wlRefine_coarsestEquitable`). | **CLEAN** |
| `Tower8.wlStable_isBisim` | `Tower8.lean:527` | The WL classes form a bisimulation (the other direction). | **CLEAN** |
| `Tower8.coarsest_equitable_isCoarsest_bisim` | `Tower8.lean:571` | Paige–Tarjan = 1-WL in relational-coarsest-partition form: a bisimulation of `vertexCoalg P` that refines the base cell partition refines WL. | **CLEAN** |
| `Tower8.TransitionCoalg.stepInv_preserved` | `Tower8.lean:372` | A one-step-invariant predicate holds along any reachable run (safety preservation). | **CLEAN** (no axioms at all) |
| `EquitablePartition.cellUniformPST_iff_quotientPST_bridge` | `Tower8.lean:453` | Re-exports the Tower-3 PST iff through the Tower-8 observational-quotient lens. | **CLEAN** |

> **Scope of `coarsest_equitable_isCoarsest_bisim`.** The vertex coalgebra has an identity
> successor, so an abstract bisimulation of it carries only the one-round `obs_eq` constraint.
> The theorem refines WL for any bisimulation that also refines the base cell partition
> (`hfine`) — the relational-coarsest-partition hypothesis, satisfied by the cell-equality
> bisimulation and every finer one. The full converse pairing (an arbitrary abstract
> bisimulation, with no `hfine`, recovered as an equitable partition) is carried as an
> explicit hypothesis, not a `sorry`.

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
| `EquitableMechanism.residual_rank_floor` | `Integrations/EquitableMechanism.lean` | Sharp floor `rank A ≤ rank(blockpart)+k`, below the `n` ceiling. | **CLEAN** | — |
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

> The average-mixing matrix of `Qₙ` is not the flat `1/2ⁿ` matrix for `n≥2`; the file carries
> the correct content (`hypercube_avgReturn_gt_uniform`, `hypercube_not_averageUniformMixing`)
> plus one honest `sorry` (`hypercube_averageMixing_diag`, the spectral Cesàro packaging). These
> are non-headline; the two PST/mixing headlines above do not route through them.

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
| `Applications.CompileML.compile_recall_to_heron` | `Applications/CompileML.lean:402` | End-to-end recall task compiles to a data/flag-subdivision host. | **CLEAN** | — |

### TransformerDSL

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `TransformerDSL.Compilable.compile_denote_commutes` | `Integrations/TransformerDSL.lean:273` | Compiler correctness: `denote ∘ compile = denote` (the compile/semantics square commutes). | **CLEAN** | — |
| `TransformerDSL.Compilable.compiler_guarantee` | `Integrations/TransformerDSL.lean:335` | Compiled program is semantically equal AND meets the O(n·(r+d)) cost guarantee. | **CLEAN** | — |

### Applications — IBM Heavy-Hex (data/flag subdivision quotient)

The formalized host is the **2-cell data/flag subdivision** carrying IBM hardware names:
every flag vertex subdivides a data–data edge, and the proven spectrum `±2√(N−1)`
(`dataFlagQuotient_eigenvalues`) is that of subdividing the complete graph K_N. The honest
content is the equitable-quotient lift on this data/flag bipartition, not the degree-3
honeycomb connectivity of the physical chip. The lift theorems below are about the data/flag
partition as formalized.

| Theorem | File | Statement (1-line) | Clean? |
|---------|------|--------------------|--------|
| `Applications.IBMHeavyHex.dataFlagQuotient_eigenvalues` | `Applications/IBMHeavyHex.lean:874` | The 2-cell data/flag subdivision quotient has spectrum `±2√(N−1)`. | **CLEAN** |
| `Applications.IBMHeavyHex.heavyHex_pst_lift` | `Applications/IBMHeavyHex.lean:1142` | PST lifts from the data/flag equitable quotient to the cell-uniform states. | **CLEAN** |
| `Applications.IBMHeavyHex.dephasing_preserves_dataFlag` | `Applications/IBMHeavyHex.lean:1344` | Dephasing noise preserves the data/flag equitable partition. | **CLEAN** |
| `Applications.IBMHeavyHex.dataFlag_chiral_no_speedup` | `Applications/IBMHeavyHex.lean:1429` | On the 2-cell data/flag quotient, chiral signing leaves the mixing-governing spectral radius invariant: no search speedup. | **CLEAN** |

### Applications — Majorana-1 (parity-sector quotient)

The proven content is the parity-sector structure: the joint-parity projectors form a
Hermitian, orthogonal, complete idempotent system, and parity-conserving noise preserves the
resulting partition. The spectral disassembly into a 2×2 effective Hamiltonian per tetron is
not formalized; the theorems below are exactly these parity-projector facts.

| Theorem | File | Statement (1-line) | Clean? |
|---------|------|--------------------|--------|
| `Applications.MajoranaOne.TetronChip.sectorProjector_sum` | `Applications/MajoranaOne.lean:630` | Joint-parity-sector projectors sum to the identity. | **CLEAN** |
| `Applications.MajoranaOne.TetronChip.parityQuantumEquitablePartition` | `Applications/MajoranaOne.lean:710` | (`def`) the parity-conserving quantum equitable partition. | **CLEAN** |
| `Applications.MajoranaOne.TetronChip.payoff2_parity_noise_preserves_partition` | `Applications/MajoranaOne.lean:1062` | Parity-conserving noise preserves the equitable partition. | **CLEAN** |

> `MajoranaOne.lean` has two open `sorry`s (lines 1007, 1097) in non-headline lemmas; none
> of the three headline theorems route through them.

### DiracLimit

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `DiracLimit.offDiagonalBloch_eigenvalues` | `Dowsing/DiracLimit.lean:324` | Off-diagonal Bloch Hamiltonian has eigenvalues `±‖f(k)‖`. | **CLEAN** | — |
| `DiracLimit.bipartite_equitable_dirac_cone` | `Dowsing/DiracLimit.lean` | Honeycomb off-diagonal block: band touching at k=π, `±‖f(k)‖` bands, and the small-`k` Dirac cone (all three conjuncts). | **CLEAN** | — |
| `DiracLimit.coinedWalk_continuum_dirac_conjecture` | `Dowsing/DiracLimit.lean` | (`def`, open conjecture) the rescaled coined-walk generator's `2×2` spinor block converges in op-norm to the massless Dirac Bloch generator `−i·H_Dirac(k)`. | n/a (unasserted `Prop`) | **OPEN:** quantum-walk → Dirac scaling limit (Meyer / Bisio–D'Ariano–Tosini); no Mathlib scaling-limit calculus. |

### Negative-PST

| Theorem | File | Statement (1-line) | Clean? | Open gap |
|---------|------|--------------------|--------|----------|
| `StdLib.dominatingVertex_no_PST` | `StdLib/Join.lean:337` | A vertex adjacent to all others (dominating) cannot have PST. | **CLEAN** | — |
| `StdLib.cone_apex_no_PST` | `StdLib/Join.lean:351` | The apex of a cone graph cannot have PST. | **CLEAN** | — |

---

## POSITIONING — prior art vs. our contribution

This is a certificate-and-unification contribution, not a first-contact-novelty one. The
PST-quotient lift is prior mathematics:

- **PST / equitable-quotient lift** = Bachman–Tamon, arXiv:1108.0339 (2011). The spine
  keystone `cellUniformPST_iff_quotientPST` and its CTQW lifts mechanize that paper.
- **DTQW / Szegedy quotient square** = Doliwa et al., arXiv:2603.14269 (2026). The
  discrete-time subspace-invariance / quotient square is theirs.

Our contribution is four things:

1. **Mechanization** — the full equitable-quotient ⇒ PST spine, axiom-clean in Lean 4 +
   Mathlib.
2. **Unification** — one `EquitablePartition` interface realizing the classical/CTQW lift
   (Bachman–Tamon), the discrete-time/Szegedy square (Doliwa et al.), the
   bisimulation/Paige–Tarjan rung (Tower-8), and the attention/ML complexity collapse.
3. **The discrete-time Szegedy PST/mixing lifts** the prior work leaves open —
   `cellUniformSzegedyPST_iff_quotient`, `cellUniformSzegedyMixing_iff_quotient` (CLEAN), proven
   to the compression `szegedyQuotient` via the doubled cell-matrix element. The compression is
   the lumped cell-chain; it equals the quotient graph's intrinsic Szegedy walk under the
   per-edge hypothesis `hcoin : Q.szCoinAmp = compression amplitude`
   (`szegedyQuotient_eq_quotientWalk_of_coinAmp`), satisfied by the raw branching quotient.
   Companions: Tower-9 (`Graphplay/Tower9.lean`) packages the refinement⊣deduction duality as
   the `AbstractInterpretation` interface with the Cousot transfer theorems; LDT soundness
   (`Graphplay/Integrations/LatticeDeduction.lean`) proves run-soundness via the first
   `GaloisConnection` in the corpus (a connection, not an insertion — it models the
   correct-answer half, not the completeness layer).
4. **The verified certificate** — the per-theorem axiom-status + non-vacuity audit in this
   ledger: precision as credibility.

Lead with "we mechanize and unify the Bachman–Tamon / Doliwa quotient picture and supply a
machine-verified certificate." None of the contributions is new mathematics; all are
first-machine-checked.

---

*Verification: full `lake build` GREEN (~7900 jobs, exit 0; every remaining `sorry` an honest
leaf) + `#print axioms` on each headline via `lake env lean` on scratch files outside
`Graphplay/`.*
