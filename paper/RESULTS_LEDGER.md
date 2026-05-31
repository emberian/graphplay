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

**Date:** 2026-05-31 (re-audited) · **Mathlib:** local checkout at `/Users/ember/src/mathlib4`
(v4.30.0-era) · **Lean toolchain:** as pinned by the project.

> **2026-05-31 re-audit.** `#print axioms` was re-run on every headline theorem AND
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

That leaves the genuine axiom-status frontier:

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
| `CHSH_correlator_bound` | false-as-stated (`12−16·win`) | corrected to `|8·win−4| ≤ 2√2`, proven via `TsirelsonBound`. |
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

4. **The axiom-status frontier is now ONE genuine open `sorryAx` headline**
   (`lattice_search_dimension_threshold`, the Childs–Goldstone d>4 threshold) **plus
   one openly-CONDITIONAL headline** (`hypercube_search_optimal_timing` for `d≥2`,
   modulo the named open Krawtchouk chain-amplitude hypothesis; the `d=1` case is
   unconditionally clean). The previous "four open clauses" are down to these — Eckart–Young
   and the Dirac cone are now CLOSED. **Do not claim the lattice threshold or the
   general-`d` hypercube timing as proven.** Separately, a 2026-05-31 vacuity audit
   corrected several axiom-clean-but-hollow statements (classical LB, optimal-timing
   budget, rank floor, hard-core/XY) — see the Statement-soundness table. **`hardCore_eq_XY`
   is non-degenerate but does NOT yet prove the XY-Hamiltonian identity; do not claim it.**

---

*Generated by audit-only verification pass (no `.lean` edits). Scratch axiom-check
files were created outside `Graphplay/` (`/tmp/AxCheck*.lean`).*
