# A Machine-Checked Theory of Equitable-Partition Quantum Walks

**Paper outline + drafted Introduction — v4.**
**Genre: formalization-and-unification (consolidate-and-expand), NOT a novelty paper.**
**Ground truth:** every theorem cited below is in `paper/RESULTS_LEDGER.md` (re-audited
2026-06-02: full `lake build` green, 7894 jobs; per-theorem `#print axioms` + adversarial
non-vacuity read). Nothing here is asserted beyond what that ledger records. Where a result
is honest-`sorry`, conditional, or de-overclaimed, this document says so in the same place
the ledger does.

> **Framing rule, load-bearing (from `graphplay-tino-outreach`):** *precision as
> credibility*. The audience includes Tino Tamon — senior author (Bachman–…–Tamon 2011) of
> the corpus we mechanize. We **lead with "we machine-verified your quotient-PST theorem and
> unified it with three neighbouring pictures"**, a collaboration hook, *not* a discovery
> claim. The equitable-quotient lift is **not** ours; the *mechanization*, the *unification
> under one interface*, the *discrete-time lifts the prior work left open*, and the *verified
> two-dimension certificate* are.

---

## 0. The precise one-paragraph contribution statement

> We present the first machine-checked, axiom-clean (Lean 4 + Mathlib) formalization of the
> equitable-partition quotient theory of quantum walks, and we unify under a **single
> `EquitablePartition` interface** four pictures that the literature has so far developed
> separately. (i) **Mechanization.** The keystone — *a graph has perfect state transfer iff
> its equitable quotient does* — is **Bachman–Fredette–Fuller–Landry–Opperman–Tamon–Tollefson
> (arXiv:1108.0339, 2011)**; we supply its first machine-checked proof
> (`cellUniformPST_iff_quotientPST`), together with the intertwining identity, the
> one-way spectral inclusion `spectrum Q̃ ⊆ spectrum A`, the search reduction, and the
> Cartesian-product lift, each carrying only the three standard foundational axioms
> `{propext, Classical.choice, Quot.sound}`. (ii) **Unification.** The *same* interface
> simultaneously realizes the classical/continuous-time (CTQW) quotient-PST lift (Bachman–Tamon),
> the discrete-time Szegedy aggregation–quantization square (**Doliwa–Siemaszko–Zalewski,
> arXiv:2603.14269, 2026**), the bisimulation / Paige–Tarjan / 1-WL refinement rung (classical
> concurrency + WL folklore), and an exact-attention complexity collapse in machine learning.
> (iii) **The discrete-time lifts the prior work leaves open.** Doliwa et al. prove the Szegedy
> commuting square but explicitly defer perfect state transfer ("deserves deeper studies"); we
> close the discrete-time PST and uniform-mixing analogues *to the compression*
> (`cellUniformSzegedyPST_iff_quotient`, `cellUniformSzegedyMixing_iff_quotient`, both
> axiom-clean), with one honest residue (`szegedyQuotient_eq_quotientWalk`, the identification
> of the compression with the quotient graph's *intrinsic* Szegedy walk) that the lifts
> provably do **not** depend on. (iv) **The verified certificate.** The deliverable is itself
> the per-theorem, two-dimension audit — axiom-status **and** non-vacuity — which is what makes
> the consolidation trustworthy. We claim *only* these four things. The equitable-quotient lift,
> the Szegedy square, the equitable ≡ bisimulation ≡ 1-WL equivalences, and the
> bisimulation-up-to certificate idea are all prior art, attributed below; and we are scrupulous
> that WL/equitable refinement is **strictly coarser than the spectrum** — our spectral inclusion
> is correctly one-way.

---

## 1. Section outline

| § | Title | Content | Primary ledger anchors |
|---|-------|---------|------------------------|
| 1 | **Introduction** | The consolidate-not-novelty thesis; what is mechanized vs. discovered; the certificate as deliverable. (Full prose in §3 of this file.) | — |
| 2 | **Background: equitable partitions & quotients** | Equitable partition of a (weighted) graph; the symmetric quotient `Q̃`; the cell-uniform subspace; the intertwining `restrict_eq_symmQuotient`; the one-way spectral inclusion (with the WL≠spectrum caveat stated up front). | `restrict_eq_symmQuotient`, `spectrum_subset` |
| 3 | **The spine: `cellUniformPST_iff_quotientPST`** | The keystone equivalence (Bachman–Tamon 2011), mechanized. The Hermitian symmetric quotient, the `exp(−iτQ̃)` transfer condition, the `‖·‖=1` characterization. Why it is axiom-clean. | `cellUniformPST_iff_quotientPST`, `search_quotient_reduction`, `cartesianProduct_pst` |
| 4 | **CTQW lifts** | What lifts through the spine in continuous time: PST on products, hypercube PST (origin→antipode, τ=π/2) and instantaneous uniform mixing (τ=π/4), the heavy-hex chip PST lift, search-Hamiltonian reduction. Honest boundary on the *open* timing/threshold results. | `hypercube_PST_antipodal`, `hypercube_uniformMixing`, `heavyHex_pst_lift`, `hypercube_sparse_search_reduction` |
| 5 | **DTQW Szegedy lifts** | The discrete-time analogue. Doliwa et al.'s square as prior art; our axiom-clean PST/mixing lifts *to the compression*; the doubled cell-uniform form (and the free-vertex-head fake-closure we caught and corrected); the single honest residue. | `cellUniformSzegedyPST_iff_quotient`, `cellUniformSzegedyMixing_iff_quotient`, `szegedyQuotient_eq_quotientWalk` (open) |
| 6 | **Tower-8: the bisimulation bridge** | Equitable partition = coarsest bisimulation of the graph-as-Moore-coalgebra = Paige–Tarjan relational-coarsest-partition = 1-WL colour refinement. Each leg classical; the *assembled mechanized chain* is the artifact. The one honest converse-pairing gap (carried as an explicit hypothesis, not a `sorry`). | `equitable_isBisim`, `coarsest_equitable_isCoarsest_bisim`, `wlStable_isBisim`, `stepInv_preserved` |
| 7 | **LDT duality: refinement ⊣ deduction** | The Knaster–Tarski lfp/gfp **dual** of the refinement quotient: Lattice Deduction Transformers (arXiv:2605.08605). graphplay's first `GaloisConnection`; run-soundness via Tower-8; the honest asymmetry (the quantum content lives only on the refinement leg). | `alpha_gc_gamma`, `dedRun_preserves_solutions`, `solved_state_is_correct` |
| 8 | **ML application: attention collapse + irreducibility floor** | Equitable structure ⇒ exact O(n²)→O(n·r) attention (fwd + bwd + training step); the structured-attention axes (segment/block, banded/circulant, head-tying); the compiler-correctness square; the sharp irreducibility lower bound (you cannot beat the floor). The precondition scope (dense *learned* attention degenerates: r=n). | `blockAttentionApply_eq_fullAttentionApply`, `attention_apply_linear_in_n`, `training_step_linear_under_equitable`, `segment_attention_exact_reduction`, `circulant_banded_cost`, `no_cheap_exact_factorization`, `residual_rank_floor`, `compile_denote_commutes` |
| 9 | **The verification methodology as deliverable** | The two-dimension audit: `#print axioms` (necessary) + adversarial non-vacuity read (catches axiom-clean-but-hollow). The audit found, and we fixed, ~12 false-as-stated theorems and 4 axiom-clean-but-vacuous headlines. The certificate *is* the contribution; precision is the currency. | The ledger itself; CHSH de-vacuity story as worked example |
| 10 | **Open frontiers** | The genuinely-open residues, marked as open: the lattice dimension threshold (Childs–Goldstone d>4 integral), the general-`d` hypercube search timing (open Krawtchouk bound), the intrinsic-Szegedy-quotient identity, the quantum-walk→Dirac scaling limit, the Tower-8 converse pairing, the (A′) succinct-certificate wedge, the Tower-9 abstract-interpretation interface. | `lattice_search_dimension_threshold` (sorryAx), `hypercube_search_optimal_timing` d≥2 (conditional), `coinedWalk_continuum_dirac_conjecture` (open) |
| 11 | **Related work** | Exact prior-art attribution: Bachman–Tamon, Doliwa et al., Krovi–Brun, Ide–Narimatsu, Martens/Paige–Tarjan, Cançado–Coutinho, Rattan–Seppelt, Hordan–Dym–Seppelt, Sangiorgi/Pous, Ranzato–Tapparo, Cousot–Cousot, the GQWformer/CTQWformer ML line. | (citations, not theorems) |

A short **Appendix** reproduces the full per-theorem ledger table (axiom-status + non-vacuity).

---

## 2. Theorem inventory (mapped to sections, pulled from the ledger)

**Legend.** CLEAN = `#print axioms` is exactly `{propext, Classical.choice, Quot.sound}` *and*
passed the adversarial non-vacuity read. **sorryAx** = depends on an open `sorry`.
**CONDITIONAL** = axiom-clean but only modulo a named open hypothesis. **def/conj** = a
definition or unasserted conjecture-`Prop`, not a proved theorem. Every row is a row in
`RESULTS_LEDGER.md`; line numbers are from the ledger / verified against source.

### Spine (§3) and Background (§2)

| Theorem | File:line | Status | Note |
|---------|-----------|--------|------|
| `EquitablePartition.cellUniformPST_iff_quotientPST` | `PST/QuotientIff.lean:412` | **CLEAN** | The keystone. = Bachman–Tamon 2011, mechanized. |
| `EquitablePartition.restrict_eq_symmQuotient` | `Equitable.lean:425` | **CLEAN** | Intertwining identity (cell-uniform subspace isometry). |
| `EquitablePartition.spectrum_subset` | `Spectral.lean:134` | **CLEAN** | `spectrum Q̃ ⊆ spectrum A`. **One-way** (WL ⊊ spectrum). |
| `search_quotient_reduction` | `Search.lean:243` | **CLEAN** | Search Hamiltonian reduces to the marked-refined quotient. |
| `WeightedGraph.cartesianProduct_pst` | `Product/PST.lean:241` | **CLEAN** | PST + periodicity ⇒ PST on `G □ H`. |

### CTQW lifts (§4)

| Theorem | File:line | Status | Note |
|---------|-----------|--------|------|
| `StdLib.hypercube_PST_antipodal` | `StdLib/Hypercube.lean:405` | **CLEAN** | `Qₙ` origin→antipode PST at τ=π/2. Exact, finite-`n`. |
| `StdLib.hypercube_uniformMixing` | `StdLib/Hypercube.lean:561` | **CLEAN** | `Qₙ` instantaneous uniform mixing at τ=π/4. |
| `Applications.IBMHeavyHex.heavyHex_pst_lift` | `Applications/IBMHeavyHex.lean:1142` | **CLEAN** | PST on the heavy-hex chip lifts from the data/flag quotient. |
| `Applications.IBMHeavyHex.dataFlagQuotient_eigenvalues` | `Applications/IBMHeavyHex.lean:874` | **CLEAN** | The 2-cell data/flag quotient spectrum. |
| `Applications.IBMHeavyHex.dephasing_preserves_dataFlag` | `Applications/IBMHeavyHex.lean:1344` | **CLEAN** | Dephasing noise preserves the partition. |
| `SparseSearch.hypercube_sparse_search_reduction` | `Applications/SparseSearch.lean:602` | **CLEAN** | Equitable reduction to the Hamming chain (NO timing clause). |
| `SparseSearch.hypercube_search_optimal_d1` | `Applications/SparseSearch.lean` | **CLEAN** | `d=1` (`Q₁=K₂`) optimal CTQW search, UNCONDITIONAL. |

### DTQW Szegedy lifts (§5)

| Theorem | File:line | Status | Note |
|---------|-----------|--------|------|
| `cellUniformSzegedyPST_iff_quotient` | `DiscreteTime/Lifts.lean:483` | **CLEAN** | Discrete-time PST lift to the compression. Doliwa-open. |
| `cellUniformSzegedyMixing_iff_quotient` | `DiscreteTime/Lifts.lean:519` | **CLEAN** | Discrete-time uniform-mixing lift to the compression. |
| `szegedyQuotient_eq_quotientWalk` | `DiscreteTime/Lifts.lean:582` | **sorryAx (OPEN)** | Compression = quotient's *intrinsic* Szegedy walk. The lifts above provably do **not** depend on it. |

### Tower-8 bisimulation bridge (§6)

| Theorem | File:line | Status | Note |
|---------|-----------|--------|------|
| `EquitablePartition.equitable_isBisim` | `Tower8.lean:310` | **CLEAN** | Cell-equality is a bisimulation; proof obligation *is* `P.uniform`. |
| `Tower8.bisim_refines_wlStable` | `Tower8.lean:498` | **CLEAN** | Equitable ⇒ refines WL-stable colouring. |
| `Tower8.wlStable_isBisim` | `Tower8.lean:527` | **CLEAN** | WL classes form a bisimulation (coarsest direction). |
| `Tower8.coarsest_equitable_isCoarsest_bisim` | `Tower8.lean:571` | **CLEAN** | Paige–Tarjan = 1-WL, correct relational-coarsest-partition form. |
| `Tower8.TransitionCoalg.stepInv_preserved` | `Tower8.lean:372` | **CLEAN** (no axioms at all) | Safety: one-step-invariant predicate holds along any run. |
| `cellUniformPST_iff_quotientPST_bridge` | `Tower8.lean:453` | **CLEAN** | Re-exports the spine through the coalgebraic-quotient lens. |

> **Tower-8 honest gap (carried as a hypothesis, NOT a `sorry`).** The deep half of
> Paige–Tarjan — that an *arbitrary* abstract bisimulation of the vertex coalgebra is itself an
> equitable partition — is **TRUE but deferred**. The naive "every bisimulation refines WL" is
> **FALSE** (the same-degree relation on P₄ is a bisimulation that does not refine WL) and is
> **not claimed**. `coarsest_equitable_isCoarsest_bisim` adds the standard relational-coarsest-
> partition hypothesis (`hfine`), giving the genuine PROVED content; there is **no `sorry`
> token** in the Tower-8 files.

### LDT duality (§7)

| Theorem | File:line | Status | Note |
|---------|-----------|--------|------|
| `LatticeDeduction.alpha_gc_gamma` | `Integrations/LatticeDeduction.lean:192` | **CLEAN** | graphplay's **first** `GaloisConnection` (α⊣γ). |
| `LatticeDeduction.dedRun_preserves_solutions` | `Integrations/LatticeDeduction.lean:345` | **CLEAN** | Lifts Tower-8 `stepInv_preserved` to whole-run soundness. |
| `LatticeDeduction.solved_state_is_correct` | `Integrations/LatticeDeduction.lean:391` | **CLEAN** | A reachable solved state on a satisfiable instance has `cons={s}`. |

> **LDT honesty.** A *connection*, not an *insertion* (`α∘γ ≠ id`); models the "returns a
> correct answer" half, **not** the abstain/branch completeness layer. The duality is
> **classical**: there is **no** honest quantum deduction-dual (amplitudes have no canonical
> complete-lattice order). Companion memo `research/refinement_deduction_duality.md` pins this
> as the Knaster–Tarski lfp/gfp **DUAL** of the WL refinement quotient — a *dual*, not an
> instance, and the asymmetry is the correct statement.

### ML application: attention collapse + irreducibility floor (§8)

| Theorem | File:line | Status | Note |
|---------|-----------|--------|------|
| `AttentionComplexity.blockAttentionApply_eq_fullAttentionApply` | `Integrations/AttentionComplexity.lean:120` | **CLEAN** | Block (equitable) attention = full attention, **exactly**. |
| `AttentionComplexity.attention_apply_linear_in_n` | `Integrations/AttentionComplexity.lean:178` | **CLEAN** (only `propext`) | Apply-cost O(n·r·d), linear in n. |
| `AttentionComplexity.training_step_linear_under_equitable` | `Integrations/AttentionComplexity.lean:348` | **CLEAN** | One training step is O(n)-linear under equitable-equivariance. |
| `StructuredAttention.segment_attention_exact_reduction` | `Integrations/StructuredAttention.lean:177` | **CLEAN** | Segment-pooled attention = r-cell quotient action, exactly. |
| `StructuredAttention.circulant_banded_cost` | `Integrations/StructuredAttention.lean:361` | **CLEAN** (only `propext`) | Banded/circulant cost O(n·w·d) (a *distinct* reduction axis). |
| `EquitableMechanism.no_cheap_exact_factorization` | `Integrations/EquitableMechanism.lean:342` | **CLEAN** | EXACT floor: `A = equitablePart + R`, `rank R ≤ k` ⇒ `rank A ≤ r+k`. |
| `EquitableMechanism.residual_rank_floor` | `Integrations/EquitableMechanism.lean` | **CLEAN** | Sharp floor `rank A ≤ rank(blockpart)+k` (was vacuous `≤ n+k`; de-vacuoused). |
| `EquitableMechanism.equitable_strictly_generalizes_orbit` | `Integrations/EquitableMechanism.lean:448` | **CLEAN** | Equitable ⊋ orbit (automorphism) partitions. |
| `EquitableMechanism.blockConstant_NTK_subset_spectrum` | `Integrations/EquitableMechanism.lean:512` | **CLEAN** | Block-constant NTK spectrum ⊆ host spectrum. |
| `EquitableMechanism.corrected_equitable_attention` (+ `_complex`) | `Integrations/EquitableMechanism.lean` | **CLEAN** | ε-approx residual-corrected bound; real + complex-Hermitian Eckart–Young (now CLOSED). |
| `TransformerDSL.Compilable.compile_denote_commutes` | `Integrations/TransformerDSL.lean:273` | **CLEAN** | Compiler correctness: `denote ∘ compile = denote`. |
| `TransformerDSL.Compilable.compiler_guarantee` | `Integrations/TransformerDSL.lean:335` | **CLEAN** | Semantic equality AND O(n·(r+d)) cost guarantee. |
| `Applications.CompileML.compile_recall_to_heron` | `Applications/CompileML.lean:402` | **CLEAN** | End-to-end recall task compiles to a Heron-class host. |
| `Applications.CompileML.compiled_experiment_prediction` | `Applications/CompileML.lean:325` | **CLEAN** | The compiled experiment's prediction matches the spec. |
| `QuantumAdvantage.quantum_search_exact_amplitude` | `Integrations/QuantumAdvantage.lean:638` | **CLEAN** | Exact finite-`n` Rabi: `≥ √(1/2)` at `t ≤ (π/2)√n`. |
| `QuantumAdvantage.ml_structured_search_quantum_advantage_exact` | `Integrations/QuantumAdvantage.lean:949` | **CLEAN** | Exact O(√r) amplitude AND classical `< r`-query lower bound. |

> **ML precondition scope (the honest §8 boundary).** The exact O(n²)→O(n·r) reduction needs
> *equitable structure*. It does **not** apply to vanilla dense **learned** attention (the
> finest equitable partition is discrete, r=n, and it degenerates). It **does** apply, by axis:
> segment/block-uniform + grouped/pooled (Set Transformer ISAB inducing points *are* the cells);
> banded/sliding-window/circulant (the distinct O(n·w) axis); head-tying GQA/MQA (defect ≡ 0 in
> real Llama/Mistral); positional RoPE/ALiBi restore equivariance. Dense-learned is the
> ε-equitable *frontier* (defect measurable, not a proved exact reduction).

### Supporting / context theorems cited in passing

| Theorem | File:line | Status | Used in |
|---------|-----------|--------|---------|
| `Graphplay.CHSH_correlator_bound` | `QuantumCSP.lean:870` | **CLEAN**, UNCONDITIONAL | §9 (worked de-vacuity example): `\|8·win−4\| ≤ 2√2`, no typeclass. |
| `LiteratureInterfaces.CHSHRealization.le_two_sqrt_two` | `LiteratureInterfaces.lean:256` | **CLEAN** | §9: Tsirelson's bound, the real operator-algebra theorem. |
| `DiracLimit.bipartite_equitable_dirac_cone` | `Dowsing/DiracLimit.lean` | **CLEAN** | §4 remark: honeycomb Dirac cone (now CLOSED, all 3 conjuncts). |
| `StdLib.dominatingVertex_no_PST` | `StdLib/Join.lean:337` | **CLEAN** | §4 remark: negative-PST (a dominating vertex cannot have PST). |
| `Applications.MajoranaOne.TetronChip.parityQuantumEquitablePartition` | `Applications/MajoranaOne.lean:710` | **CLEAN** (`def`) | §8 remark: parity-sector quantum equitable partition. |

---

## 3. Drafted Introduction (real prose, ~2 pages)

### 1. Introduction

Perfect state transfer (PST) on a graph is the statement that a quantum walker initialized at
one vertex arrives, at some later time and with probability one, at another. Since Christandl,
Datta, Ekert and Landahl identified PST on the hypercube and the path, the design of
PST graphs has been one of the organizing problems of algebraic quantum-walk theory, and a
recurring tool in that design is the **equitable partition**: a colouring of the vertices in
which the number of edges from a vertex to each colour class depends only on the vertex's own
class. An equitable partition collapses the walk onto a small **quotient graph** whose
adjacency matrix `Q̃` is, up to a symmetrization, an `r × r` matrix when there are `r` classes,
and the central structural fact — *proved by Bachman, Fredette, Fuller, Landry, Opperman,
Tamon, and Tollefson in 2011* — is that **a graph has PST if and only if its equitable quotient
does** (arXiv:1108.0339). The quotient is an exact reduction: the continuous-time walk
restricted to the colour-constant ("cell-uniform") subspace is, on the nose, the walk on `Q̃`.

This paper does not discover that theorem. **We mechanize it.** Our contribution is a complete,
machine-checked formalization in Lean 4 over Mathlib of the equitable-partition quotient theory
of quantum walks, in which the Bachman–Tamon equivalence is the keystone of a single, reusable
`EquitablePartition` interface, and in which four neighbouring pictures — continuous-time PST,
discrete-time Szegedy walks, classical bisimulation refinement, and a complexity reduction in
machine learning — are unified as instances of that one mechanism. Every headline theorem is
accompanied by a two-dimensional audit: its `#print axioms` status (it must rest on exactly the
three standard foundational axioms `propext`, `Classical.choice`, `Quot.sound`, and never on a
`sorry`) **and** an adversarial non-vacuity reading (a perfectly axiom-clean statement can still
be hollow). That audit, recorded per theorem, is itself a deliverable. The thesis of the paper
is *precision as credibility*: a consolidation of a literature is worth more, not less, when one
can say exactly which lines are proven, which are conditional, and which remain open — and prove
it to a machine.

We are deliberately a **consolidation-and-expansion** paper rather than a novelty paper, and we
state the prior-art boundary scrupulously, because overclaiming here would defeat the purpose.
The quotient-PST lift is Bachman–Tamon's. The discrete-time Szegedy aggregation–quantization
*square* — that lumping a Markov chain and then quantizing it agrees with quantizing and then
lumping — is **Doliwa, Siemaszko and Zalewski's (arXiv:2603.14269, 2026)**, who prove it
conditionally in general and unconditionally for the equitable-partition case. The identification
of an equitable partition with the coarsest **bisimulation** of the graph read as a coalgebra,
with the **Paige–Tarjan** relational-coarsest stable partition, and with the stable colouring of
**1-dimensional Weisfeiler–Leman**, is folklore across concurrency theory and the graph-isomorphism
literature (Paige–Tarjan 1987; Martens et al. 2021; Cançado–Coutinho 2026). The idea that a
behavioural equivalence admits a *succinct coinductive certificate* is Sangiorgi's
bisimulation-up-to. None of these is ours, and we attribute each at the point of use.

What *is* ours is fourfold, and we claim only this. **First, the mechanization.** The five
spine theorems — the keystone `cellUniformPST_iff_quotientPST`, the intertwining identity
`restrict_eq_symmQuotient`, the spectral inclusion `spectrum_subset`, the search reduction
`search_quotient_reduction`, and the Cartesian-product lift `cartesianProduct_pst` — are
machine-verified to carry only the three foundational axioms. To our knowledge this is the first
formal proof of the Bachman–Tamon equivalence. **Second, the unification.** The same
`EquitablePartition` interface that drives the CTQW spine also drives the discrete-time Szegedy
lifts, the Tower-8 bisimulation rung, and the attention-complexity collapse; assembling four
classically-separate pictures behind one interface, as one axiom-clean Lean development, is the
substance of the consolidation. **Third, the discrete-time lifts the prior work leaves open.**
Doliwa et al. build the Szegedy square but explicitly defer perfect state transfer, remarking
only that it "deserves deeper studies" and citing the continuous-time quotient-PST literature
in passing; no discrete-time PST-lift, mixing-lift, or search-lift appears in their paper. We
prove the discrete-time PST and uniform-mixing analogues — `cellUniformSzegedyPST_iff_quotient`
and `cellUniformSzegedyMixing_iff_quotient`, both axiom-clean — *to the compression* of the
Szegedy walk onto the cell-uniform subspace. We are precise about one residue and one correction.
The residue, `szegedyQuotient_eq_quotientWalk`, identifies that compression with the quotient
graph's *intrinsic* Szegedy walk (the step that would complete a literal "run it on the small
graph" story); it is genuinely deep — the square-root coin does not commute with cell-sums — and
remains an honest `sorry`, on which the lifts above **provably do not depend**. The correction:
an earlier version of these predicates summed a free vertex-head marginal that is not
walk-invariant, which would have been a *fake closure*; we re-keyed them onto the honest doubled
cell-uniform form and checked non-vacuity. A companion result, **`alpha_gc_gamma`**, is
graphplay's first `GaloisConnection`, the soundness skeleton of a Lattice Deduction Transformer
(arXiv:2605.08605); we show that lattice-deduction is the Knaster–Tarski least-/greatest-fixpoint
**dual** of the refinement quotient, with the quantum content living *only* on the refinement
leg — an asymmetry we state rather than paper over. **Fourth, the verified certificate.** The
per-theorem audit on both dimensions is the artifact that makes the rest trustworthy.

A consolidation is only as honest as its caveats, so we foreground three. The spectral inclusion
is **one-way**: `spectrum Q̃ ⊆ spectrum A`. Equitable (equivalently, WL) refinement is *strictly
coarser* than cospectrality (Rattan–Seppelt 2021; Hordan–Dym–Seppelt 2026), and we never imply
that an equitable partition captures the spectrum — the inclusion goes one direction only, by
design. The attention-complexity collapse requires *equitable structure*; applied to dense
**learned** attention its finest equitable partition is discrete (`r = n`) and the reduction
degenerates to no reduction — it bites on segment/pooled, banded/circulant, and head-tied
attention, where the structure is present by construction (in real grouped-query models the
defect is identically zero), and elsewhere it is a measurable *defect*, not a proved exact win.
And the bisimulation rung carries one honest converse-pairing gap, isolated as an explicit
hypothesis rather than a `sorry`, because the naive "every bisimulation refines WL" is simply
false and we do not assert it.

We arrived at these statements the hard way. An adversarial re-audit found, and we corrected,
roughly a dozen theorems that were *false as stated* and four headline claims that were
*axiom-clean yet vacuous* — a classical search lower bound that was pure pigeonhole with no query
content; a circular optimality argument; a rank bound that was trivially true; a CHSH/Tsirelson
bound briefly routed through an *uninhabitable* typeclass. Each was repaired with genuine content
and no new `sorry`, and the CHSH bound now stands unconditionally on a real operator-algebra
theorem. We narrate this in the methodology section not as an embarrassment but as the point: the
two-dimension certificate exists precisely because axiom-cleanliness alone does not catch a
hollow statement, and a formalization paper that did not run the non-vacuity gauntlet would be
quietly less trustworthy than one that did.

The remainder of the paper develops the equitable quotient (§2) and the spine (§3), then the
continuous-time (§4) and discrete-time Szegedy (§5) lifts, the bisimulation bridge (§6) and its
abstract-interpretation dual (§7), the machine-learning application (§8), and the verification
methodology itself (§9); §10 marks the genuinely-open frontiers and §11 places the work in the
literature. Throughout, the load-bearing convention is that a result is reported as *proven* only
where the machine agrees on both dimensions, and is otherwise marked **conditional**, **open**, or
**a definition** — exactly as the accompanying ledger records it.

> *( ˘▾˘ ) — a small note in the margin: the keystone is a gift back to the corpus it came from.*
> *We hand Tino's 2011 theorem back machine-checked, with three of its neighbours, and a map of*
> *what is still open.*

---

## 4. "What is NOT claimed" box (honest residues, conditionals, de-overclaimed items)

This box is the firewall. Each item is something a careless reading might attribute to us; we do
**not** claim it. Sourced from the ledger's frontier table, the Tower-8 honesty note, the DTQW
residue, and the vacuity-audit table.

### A. New mathematics we explicitly do NOT claim (prior art)
- **The equitable-quotient PST lift.** Bachman–Fredette–Fuller–Landry–Opperman–**Tamon**–Tollefson,
  arXiv:1108.0339 (2011/2012). We mechanize; we did not discover it.
- **The Szegedy aggregation–quantization square** (lump-then-quantize = quantize-then-lump, and
  its unconditional equitable-partition corollary). Doliwa–Siemaszko–Zalewski, arXiv:2603.14269
  (2026). The N-cube↔Ehrenfest and Platonic-solid worked reductions are theirs.
- **equitable ≡ bisimulation ≡ Paige–Tarjan ≡ 1-WL.** Each leg is classical
  (Paige–Tarjan 1987; Martens et al. 2021; Cançado–Coutinho 2026; Rattan–Seppelt). We assemble
  the chain in Lean; we do not claim any single edge.
- **The succinct coinductive certificate as a proof method.** Bisimulation-up-to (Sangiorgi;
  Pous). Not ours.
- **CTQW spatial-search via the equitable quotient.** Ide–Narimatsu, arXiv:2209.07688 (2022)
  compute search success/finding-time through the quotient on worked families; Krovi–Brun (2007)
  is the upstream quotient-walk anchor.

### B. Genuinely OPEN (marked open; do NOT present as proven)
- **`SparseSearch.lattice_search_dimension_threshold`** — `sorryAx`. The `d>4` lattice-search
  threshold needs the Childs–Goldstone spectral integral (quant-ph/0306054); labeled in-file as a
  conjecture. Its dependent `buildable_lattice_dynamical_contrast` inherits the `sorryAx`.
- **`SparseSearch.hypercube_search_optimal_timing` (general `d ≥ 2`)** — **CONDITIONAL**, not
  `sorryAx`: axiom-clean only modulo the named open hypothesis `HypercubeChainAmplitudeBound`
  (the Krawtchouk chain-amplitude bound), never discharged for `d ≥ 2`. The `d=1` case
  (`hypercube_search_optimal_d1`, `Q₁=K₂`) **is** unconditionally clean.
- **`szegedyQuotient_eq_quotientWalk`** — `sorryAx`. The compression-equals-intrinsic-quotient-
  walk identity (the √-coin / cell-sum non-commutation). **The DTQW PST/mixing lifts do not
  depend on it** (axiom-clean confirms).
- **`DiracLimit.coinedWalk_continuum_dirac_conjecture`** — an unasserted conjecture-`Prop`
  (a `def`, not a theorem): the rescaled coined-walk generator → massless Dirac Bloch generator.
  Open (no Mathlib scaling-limit calculus). It replaced a former *tautological* `‖X−X‖≤ε` version.
- **The Tower-8 converse pairing** — TRUE but deferred; carried as an explicit hypothesis (`hfine`),
  **not** a `sorry`. The naive "every bisimulation refines WL" is **FALSE** and is not claimed.
- **The (A′) succinct-certificate wedge** — an open *research direction*: a transition-system
  family where naming the bisimulation cell is cheap but classical cell-reachability is hard
  (the only regime where a bisimulation-quotient quantum win could be genuine, per Krovi–Brun 2007).
  Not a result.
- **Tower-9 (the abstract-interpretation interface)** — a planned construction (`OrderHom.lfp`
  packaging + a two-instance `AbstractInterpretation` over the Ranzato–Tapparo partition domain);
  **not built**. graphplay's only `GaloisConnection` today is `alpha_gc_gamma`.
- **A quantum deduction-dual** — effectively **NO**. The refinement⊣deduction duality is
  *classical*; only the refinement leg lifts to the quantum walk. We state the asymmetry; we do
  not claim a symmetric "quantum deduction."

### C. De-overclaimed items (axiom-clean now, but with a stated boundary)
- **CHSH / Tsirelson.** `CHSH_correlator_bound` (`|8·win−4| ≤ 2√2`) is **unconditional and
  carries no typeclass**; the bound is real and proven (`chshOp_norm_le` /
  `CHSHRealization.le_two_sqrt_two`). The one deferred piece is a constructive Lean *witness* that
  the bound is *tight* (Tsirelson's entangled ℂ²⊗ℂ² strategy), isolated as a single `sorry` in the
  `TsirelsonBound` *instance* — **neither headline routes through it**. (Earlier it was briefly,
  wrongly, routed through an *uninhabitable* class; that is fixed.)
- **`hardCore_eq_XY_oneDim`.** Non-degenerate (pins a genuine string-unitary + concrete conjugate),
  but **does NOT yet prove** the identity of the conjugate with the textbook XY Hamiltonian
  `Σ(XX+YY)` — that is an OPEN computation. **Do not claim "hard-core = XY."**
- **`residual_rank_floor`** — now the sharp `rank A ≤ rank(blockpart)+k` (genuinely below `n`);
  the earlier `≤ n+k` form was vacuous. We claim the sharp form only.
- **`quantum_search_quadratic_advantage`** — the classical lower bound is now a genuine
  impossibility theorem (`no_correct_QLocal_certifier`, no `Q`-local correct certifier for
  `card Q < n−1`), **not** the former pigeonhole vacuity. We claim the separation on both halves.
- **The attention collapse on dense LEARNED attention** — does **not** hold exactly (finest
  equitable partition is discrete, `r=n`). The exact O(n·r) result is claimed only where equitable
  structure is present by construction (segment/pooled, banded/circulant, head-tied); elsewhere the
  defect is *measurable*, not zero.
- **The hypercube `average`-mixing headline** — the average mixing matrix is **not** the flat
  `1/2ⁿ` matrix for `n ≥ 2` (found false-as-originally-stated); the file carries the corrected
  non-vacuous content plus one named honest `sorry` (`hypercube_averageMixing_diag`), which is
  *non-headline* and which the two PST/mixing headlines do not route through.

### D. Standing posture
A theorem is reported as **proven** here only if it passed **both** `#print axioms`
(`{propext, Classical.choice, Quot.sound}`, no `sorryAx`) **and** an adversarial non-vacuity read.
Anything that passed only the first is marked conditional or open above. The full per-theorem
ledger (`paper/RESULTS_LEDGER.md`, re-audited 2026-06-02, `lake build` green at 7894 jobs) is the
ground truth and is reproduced as an appendix.

---

## 5. Related-work attribution map (for §11)

| Claim in our paper | Prior art (we cite, do NOT claim) | Our delta |
|--------------------|-----------------------------------|-----------|
| PST iff on equitable quotient | Bachman–…–**Tamon**–Tollefson, arXiv:1108.0339 (2011) | First machine-checked proof. |
| Szegedy aggregation–quantization square | Doliwa–Siemaszko–Zalewski, arXiv:2603.14269 (2026); Krovi–Brun, quant-ph/0701173 (2007) | First mechanization; **+ the PST/mixing lifts they defer** (to the compression). |
| CTQW search via the quotient | Ide–Narimatsu, arXiv:2209.07688 (2022); Apers–Chakraborty–Novo–Roland (2020); Chakraborty et al. (2022) | The general verified lift behind their special cases. |
| equitable ≡ bisimulation ≡ coarsest partition | Paige–Tarjan (1987); Martens–Groote et al., arXiv:2105.11788 (2021) | Assembled as one axiom-clean Lean chain. |
| equitable ≡ 1-WL stable colouring | Cançado–Coutinho (CNMAC 2025 / arXiv:2411.09157); Atserias–Maneva (2013) | Same; the WL leg is mechanized, not claimed. |
| WL ⊊ spectrum (we stay one-way) | Rattan–Seppelt, arXiv:2103.02972 (2021); Hordan–Dym–Seppelt, arXiv:2605.23446 (2026) | We cite to show we honor the gap; `spectrum_subset` is correctly ⊆. |
| Succinct coinductive certificate | Sangiorgi; Pous; Madiot–Pous–Sangiorgi (CONCUR 2014) | A concrete mechanized certificate, not the up-to method. |
| Refinement ⊣ deduction (LDT) | Cousot–Cousot (POPL 1977); Tarski (1955); Ranzato–Tapparo (Inf. Comput. 2008); LDT arXiv:2605.08605 | First `GaloisConnection` in-repo; run-soundness; the lfp/gfp dual stated, with the quantum asymmetry. |
| Attention as a (quantum-)walk; structured attention | GQWformer (arXiv:2412.02285); CTQWformer (arXiv:2605.09486); Set Transformer / ISAB; GQA/MQA; ALiBi; RoPE | The *exact* O(n²)→O(n·r) reduction + verified compiler square; concurrent empirical ML work attributed. |
| CHSH/Tsirelson `2√2` | Tsirelson; standard C*-algebra | A clean unconditional Lean proof (used only as a methodology example). |

---

*This is `paper/PAPER_OUTLINE_v4.md`. It introduces no result not present in
`paper/RESULTS_LEDGER.md`. No `Graphplay/*.lean` file was read for novel claims beyond
verifying the cited theorem names/locations; none was edited.*
