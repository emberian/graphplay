# Related-Work Positioning: Graphplay vs. "Quantum Walk + Transformer" Literature

*Analyst pass, 2026-05-30. Sources read: arXiv:2412.02285 (GQWformer), arXiv:2605.09486
(CTQWformer), arXiv:2209.07688 (Ide–Narimatsu), arXiv:1403.2228 / PRL 112 210502
(Janmark–Meyer–Wong), plus a sweep for verified / quantum-hardware attention-speedup work.
Graphplay claims verified against the actual Lean source (file paths below).*

---

## TL;DR verdict

- **NOT scooped on the load-bearing claim.** No paper in this neighborhood claims, let
  alone *machine-checks*, an exact `O(n²) → O(n·r)` attention reduction via an
  equitable-partition quotient, a typed ML→chip **compiler** with a commuting-semantics
  proof, or a **falsifiable PST experiment** emitted for a real device. That whole stack
  is genuinely ours.
- **Scooped (and must attribute) on the underlying mathematics**, none of which we claim
  to have invented: (i) CTQW-based spatial search reduces to a small system via equitable
  partition / PST — **Ide–Narimatsu 2022** (closest prior work, our thesis's math spine);
  (ii) strongly-regular / hypercube graphs give full `Θ(√N)` search without global
  symmetry — **Janmark–Meyer–Wong 2014** (exactly our SparseSearch host story); (iii)
  using CTQW as a transformer inductive bias — **GQWformer 2024 / CTQWformer 2026**.
- **Sharpest single differentiator:** *everything in Graphplay is a Lean 4 theorem.* The
  related literature is empirical (ML papers) or pencil-and-paper (physics papers). Nobody
  else has a **machine-checked** `blockAttentionApply_eq_fullAttentionApply` +
  `compile_denote_commutes` + `compiled_experiment_prediction` triple — semantics-preserving,
  complexity-reducing, *and* hardware-falsifiable, all sorry-tracked.

---

## Per-paper summaries

### 1. GQWformer — arXiv:2412.02285 (Yu, Chen, Lv, Yang; Zhejiang Lab; Dec 2024)
- **(a) Problem.** Graph Transformer self-attention neglects structural inductive biases;
  they inject graph structure into attention via a quantum-walk-derived encoding.
- **(b) Method.** **Classical.** Quantum walks generate "node quantum states" computed
  classically and used as inductive biases. A GQW self-attention module + a GQW recurrent
  module. No quantum hardware.
- **(c) Headline.** Outperforms SOTA graph-classification baselines on five datasets.
- **(d) Formal verification.** None. Purely empirical.
- **(e) Complexity / hardware.** No `O(n²)→O(n·r)` claim, no equitable partition, no
  hardware compilation, no falsifiable physical experiment. Standard transformer cost.

### 2. CTQWformer — arXiv:2605.09486 (~May 2026; very recent)
- **(a) Problem.** Graph classification capturing global + temporal propagation structure.
- **(b) Method.** **Classical simulation.** CTQW simulated via matrix exponentials,
  explicitly `O(T·n³)`; final-time propagation probabilities become attention biases; a
  bidirectional recurrent module models temporal evolution. No quantum hardware.
- **(c) Headline.** "First hybrid CTQW-based Transformer"; beats CTQW kernels and GNNs
  (e.g. 92.54% MUTAG vs 88.55% AERK).
- **(d) Formal verification.** None.
- **(e) Complexity / hardware.** Maintains standard `O(Bn²h + Bnh²)` attention cost. **No**
  `O(n·r)` reduction, no equitable partition, no compiler, no falsifiable experiment.

### 3. Ide–Narimatsu — arXiv:2209.07688, "Perfect state transfer, Equitable partition and Continuous-time quantum walk based search" (Sep 2022) — **CLOSEST PRIOR WORK**
- **(a) Problem.** Compute success probability and finding time of CTQW-based spatial search.
- **(b) Method.** **Pencil-and-paper.** Two analytic tools — *equitable partition* and
  *perfect state transfer* — reduce the search dynamics to a small (≈ 2×2 / low-dim)
  effective system, from which success probability and finding time are read off.
- **(c) Headline.** Closed-form success-probability / finding-time on graphs (notably SRGs)
  via the equitable-partition reduction; PST framing of the search.
- **(d) Formal verification.** None (human proofs).
- **(e) Complexity / ML.** No transformers, no attention, no ML, no compiler. The
  mathematical heart — *CTQW search collapses to a small quotient via equitable partition,
  and this is the same phenomenon as PST* — is **exactly the math we formalize and reuse.**
  This is the paper we must cite as the source of our thesis's mathematical content.

### 4. Janmark–Meyer–Wong — PRL 112, 210502 / arXiv:1403.2228, "Global Symmetry is Unnecessary for Fast Quantum Search" (2014)
- **(a) Problem.** Does fast `Θ(√N)` CTQW search require global symmetry?
- **(b) Method.** Pencil-and-paper + numerics. Grover = CTQW on `Kₙ` with one marked
  vertex; evolution lives in a 2D invariant subspace. SRGs have only *local* symmetry →
  a 3D invariant subspace, yet still hit full `Θ(√N)`.
- **(c) Headline.** Global symmetry is unnecessary; known SRG families achieve the full
  quadratic speedup. (Underpins the "buildable sparse host still gets the speedup" story.)
- **(d) Formal verification.** None.
- **(e) Complexity / ML.** None; no attention/ML/compiler. This is the **physics
  justification for our SparseSearch hypercube/SRG claim** — must be cited there.

### 5. Sweep: any verified or quantum-hardware attention speedup? — **No collision found.**
- Quantum-self-attention papers exist (QASA arXiv:2504.05336; NISQ self-attention
  arXiv:2305.15680; arXiv:2512.02476): they replace dot-product attention with a
  *parameterized quantum circuit*, hybrid/NISQ, **empirical, no equitable reduction, no
  exact `O(n·r)` proof, no falsifiable PST compilation, no formal verification.**
- Lean/quantum verification efforts exist (Lean-QuantumInfo, CoqQ, Qafny, verified QPE/QEC):
  they verify *circuits/protocols*, **not** attention complexity, equitable quotients, or an
  ML→chip compiler. No overlap with our specific claims.

---

## Comparison table

| Axis | GQWformer | CTQWformer | Ide–Narimatsu '22 | Janmark–Meyer–Wong '14 | **Graphplay** |
|---|---|---|---|---|---|
| Goal | graph classification | graph classification | CTQW search prob/time | symmetry vs fast search | verified QW-ML accel + chip compiler |
| QW: hardware vs classical bias | classical bias | classical bias (`O(Tn³)` sim) | analytic (no execution) | analytic CTQW model | **genuine CTQW-on-chip target** (compiled schedule) + classical bias view |
| Complexity claim | none | none (`O(n²)` attn) | small-quotient reduction (search) | `Θ(√N)` search | **exact `O(n²)→O(n·r)` attention, machine-checked** |
| Hardware compilation | no | no | no | no | **yes — ML→heavy-hex/Majorana compiler** |
| Formal / machine-checked | no | no | no | no | **yes — Lean 4, sorry-tracked** |
| Attention focus | yes (bias) | yes (bias) | no | no | **yes (Hamiltonian + quotient + gradient)** |
| Falsifiable physical experiment | no | no | no | no | **yes — `compiled_experiment_prediction`** |

---

## Graphplay contributions, verified present in the Lean

- **Attention-as-CTQW-Hamiltonian + exact `O(n²)→O(n·r)` equitable reduction, machine-checked.**
  `Graphplay/Integrations/AttentionComplexity.lean`:
  `blockAttentionApply_eq_fullAttentionApply` (sorry-free correctness),
  `attention_apply_linear_in_n`, `blockCost_le_fullCost`,
  `blockGrad_apply` (sorry-free backward), `training_step_linear_under_equitable`.
  `Graphplay/Integrations/MachineLearning.lean`: attention → `WeightedGraph`
  (`symmetrizedAttention`), `symmScore_isHermitian`, the genuine
  symmetry⇒equitable theorem `branching_eq_of_aut`/`equitableOfAutomorphism`,
  `multiHead_restrict_eq_symmQuotient`. (`attention_compression_bound`,
  `attention_quantum_composition` carry honest `sorry`s on the *deep quantum-rate* clause —
  the structural reduction itself is proven.)
- **Verified quantum search advantage, exact finite-n.**
  `Graphplay/Integrations/QuantumAdvantage.lean`: exact 2×2 Rabi amplitude on `Kₙ`
  (`rabi_amplitude`, `rabi_amplitude_norm`), exact 2D invariance
  (`completeGraph_adj_mulVec_w/u`), oracle invariance, reduced-Hamiltonian intertwining.
- **Sparse buildable host (hypercube / SRG).**
  `Graphplay/Applications/SparseSearch.lean`: full bit-flip/Hamming machinery,
  `branching_eq_flipCount`, `flipCount_eq_of_dist_eq` (binomial branching = equitable
  partition of the hypercube). `strongly_regular_sparse_search` is an honest `sorry`
  (BLOCKED on spectral-ratio timing) — this is exactly the JMW result we lean on.
- **ML→chip compiler + falsifiable experiment.**
  `Graphplay/Applications/CompileML.lean`: `compileToHeavyHex`, `compileToMajorana`,
  `compiled_cellUniform_realizes_target`, `predictedKeyPopulation_eq_amplitude_sq`,
  `compiled_experiment_prediction`, `compiled_breakingScore_zero_blockDiagonal`,
  `compiled_positive_breakingScore_exists` (falsification witness), `compile_recall_to_heron`.
- **Functor-stack-as-typed-compiler.**
  `Graphplay/Integrations/TransformerDSL.lean`: `TransformerProgram` + `denote`,
  `compile`, `compile_denote_commutes` (PROVEN), `compiler_guarantee` (PROVEN,
  semantics-preserving + complexity-reducing), `compiled_apply_le_naive`.
- **Verified spectral disassembly of real chips.**
  `Graphplay/Applications/IBMHeavyHex.lean`, `Graphplay/Applications/MajoranaOne.lean`.

---

## ARE WE SCOOPED? — claim-by-claim

| Our claim | Verdict | Note |
|---|---|---|
| CTQW search reduces to a small system via equitable partition / PST | **Known — attribute** | Ide–Narimatsu 2022; Godsil/Coutinho lineage. We formalize, not originate. |
| SRG/hypercube buildable hosts still get `Θ(√N)` search | **Known — attribute** | Janmark–Meyer–Wong 2014. Our `strongly_regular_sparse_search` *is* their result. |
| CTQW as transformer inductive bias | **Known — attribute** | GQWformer 2024, CTQWformer 2026. We do *not* claim this framing as novel. |
| Attention ↔ symmetric CTQW-Hamiltonian + equitable quotient | **Ours (novel framing)** | Nobody casts attention as the token-graph Hamiltonian and quotients it. |
| **Exact `O(n²)→O(n·r)` attention reduction, machine-checked** | **Ours — flagship** | No prior work proves (or even informally claims) this exact reduction. |
| Forward+backward+training-step linear-in-n under maintained equitable structure | **Ours** | `training_step_linear_under_equitable`. |
| **Typed ML→chip compiler with commuting-semantics proof** | **Ours** | `compile_denote_commutes`, `compiler_guarantee`. No analog anywhere. |
| **Falsifiable on-device PST experiment emitted by the compiler** | **Ours** | `compiled_experiment_prediction` + breaking-score falsification witness. |
| Machine-checked quantum-search advantage at exact finite n | **Ours (as formalization)** | The physics is classical; the *Lean proof* is novel. |
| Verified spectral disassembly of IBM heavy-hex / Majorana-1 | **Ours** | No prior verified treatment of these specific chips. |

**Net:** the *mathematics* of our spine is prior art (Ide–Narimatsu, JMW, Godsil/Coutinho,
GQWformer/CTQWformer for the ML bias idea). The *verified-complexity-reduction + compiler +
falsifiable-experiment stack* is genuinely ours and uncontested.

---

## How to cite / how to frame §4 (honest novelty)

1. **Open §4 by conceding the math, then sharpen the wedge.** State plainly: the
   equitable-partition reduction of CTQW search and its PST equivalence are due to
   **Ide–Narimatsu (arXiv:2209.07688)**; the symmetry-free fast-search result on SRGs/
   hypercubes is **Janmark–Meyer–Wong (PRL 112, 210502)**; using a quantum walk as a
   transformer inductive bias is **GQWformer (2412.02285)** and **CTQWformer (2605.09486)**.
   We claim none of these.

2. **State the wedge in one sentence.** "Prior work either (i) computes a quantum walk
   *classically* as an attention bias (GQWformer, CTQWformer) or (ii) analyzes CTQW search
   reductions *on paper* (Ide–Narimatsu, JMW); we are the first to (a) cast attention itself
   as the token-graph CTQW Hamiltonian, (b) **machine-check** the exact `O(n²)→O(n·r)`
   equitable-quotient reduction of the attention apply (forward, backward, and training
   step), (c) expose it as a **typed ML→chip compiler with a proven commuting semantics**,
   and (d) emit a **falsifiable on-device PST experiment** from that compiler."

3. **Distinguish "we vs GQWformer/CTQWformer" explicitly** so reviewers don't conflate:
   they are *classical-bias ML accuracy* papers (no hardware, no proof, no complexity
   reduction); we are a *verified-complexity + hardware-compilation* paper. Different axis
   entirely — cite them as motivation/relation, not as competitors on our metric.

4. **Be scrupulous about the `sorry`s.** Frame the quantum-*rate* clauses
   (`attention_quantum_composition`, `strongly_regular_sparse_search`,
   `attention_compression_bound`) as honestly open; the load-bearing *structural* theorems
   (`blockAttentionApply_eq_fullAttentionApply`, `blockGrad_apply`, `compile_denote_commutes`,
   `compiler_guarantee`, `compiled_experiment_prediction`'s structural form) are sorry-free.
   This honesty is itself a differentiator vs the empirical literature.

5. **Suggested headline framing line for the abstract:**
   "We give the first machine-checked proof that structured attention compiles to a
   continuous-time quantum walk whose equitable quotient evaluates attention in `O(n·r)`
   instead of `O(n²)`, and we emit from the same compiler a falsifiable perfect-state-transfer
   experiment for IBM heavy-hex hardware."

*Report written read-only; no `.lean` edited; no git operations performed.*
