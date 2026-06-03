#set document(title: "Graphplay: A Machine-Checked Theory of Equitable-Partition Quantum Walks, with Verified Application to Attention Complexity and Hardware")
#set page(margin: 1in)
#set text(size: 11pt)
#set par(justify: true)

#let proven = text(fill: rgb("#0a6"))[#smallcaps[proven]]
#let opentag = text(fill: rgb("#a04"))[#smallcaps[open]]

#align(center)[
  #text(size: 17pt, weight: "bold")[Graphplay] \
  #v(0.25em)
  #text(size: 13pt, weight: "bold")[A Machine-Checked Theory of Equitable-Partition Quantum Walks, \
  with Verified Application to Attention Complexity and Hardware] \
  #v(0.45em)
  #text(size: 9.5pt)[Graphplayers Crew --- Graphplay v3]
]

#v(0.8em)

#heading("Abstract")

We present a Lean 4 formalization of the theory of continuous-time quantum
walks (CTQW) on graphs carrying an *equitable partition*, and three verified
consequences that, to our knowledge, have not appeared in machine-checked
form before. The mathematical spine --- a CTQW restricts to the
cell-constant subspace and acts there as the walk on a small symmetric
quotient $tilde(Q) = D^(1 slash 2) Q D^(-1 slash 2)$, lifting perfect state
transfer (PST), spectrum, search, and mixing --- is classical (Godsil;
Bachman--Tamon et al.; Ide--Narimatsu). Our contribution is a *certificate*:
the spine and its consequences are sorry-free Lean theorems with an explicit
proof ledger.

On top of the spine we prove three results that are genuinely ours. First, an
*exact* $O(n^2) -> O(n dot r)$ reduction of the attention operation under an
equitable token pattern, machine-checked for the forward pass, the backward
pass, and a full training step. Second, a *verified compiler*: a typed
transformer DSL whose denotation commutes with compilation to the quotient
host (`compile_denote_commutes`, `compiler_guarantee`, both sorry-free) ---
the functor stack *is* the compiler, and its correctness is a theorem. Third,
an *exact finite-$n$* quantum-search advantage --- amplitude
$sqrt((n-1) slash n)$ on the complete graph in time $O(sqrt(n))$ against a
matching classical lower bound --- lifted to structured machine-learning
search, together with the verified sparsity-and-equitable-reduction half of the
*sparse, buildable* hypercube search (the $O(sqrt(N))$ optimal timing is split
off as an open clause) and a stated $d > 4$ lattice threshold.

We then model two hardware-named hosts in Lean as equitable quotients. The
first is a complete-site subdivision graph carrying IBM data/flag labels,
whose data/flag quotient is a $2 times 2$ Hermitian matrix with eigenvalues
$plus.minus 2 sqrt(N-1)$. The second is a parity-projector construction
carrying Microsoft Majorana 1 labels, for which we prove the parity
projectors are Hermitian and sum to the identity. Finally we give a
falsifiable on-device protocol that the compiler emits for IBM Heron. Each
theorem states its hypotheses; the open frontier (Conjecture 9.3, the
relativistic enrichment, the $infinity$-categorical towers) is stated as
open.

#heading("1. Introduction")

#emph[The contribution.] This paper is a machine-checked theory of
equitable-partition quantum walks, together with its verified application to
two things people actually care about: the cost of attention in transformers,
and the structure of real quantum hardware. The whole development lives in
Lean 4; the load-bearing claims are sorry-free theorems, and we say
explicitly, theorem by theorem, which is which.

The organizing observation is old and robust: a continuous-time quantum walk
on a graph $G$ that carries an *equitable partition* $pi$ --- a coloring whose
cells have constant inter-cell degrees --- never leaves the cell-constant
subspace if it starts there, and on that subspace it evolves as the walk on a
small *quotient* operator. Two decades of the Tamon program, and Godsil before
it, show that PST, spatial search, and mixing on large graphs are very often
shadows of a tiny finite calculation seen through this lens. We take that body
of mathematics as given and known (Section 6 attributes it carefully). What we
add is a *certificate layer*: a uniform, axiom-clean Lean spine
(Section 2) and three verified consequences (Section 3) that the
pencil-and-paper and empirical literature states without proof or without
exactness.

#emph[Why a certificate.] The headline applications --- "structured attention
costs $O(n r)$, not $O(n^2)$", "this ML program compiles to that quantum walk
with the same semantics", "this search reaches the marked state in $O(sqrt(n))$
with amplitude exactly $sqrt((n-1) slash n)$" --- are the kind of claim that is
easy to assert and hard to get exactly right. By making each one the statement
of a Lean theorem that `lake build` checks, we turn the assertions into
artifacts. Some deep *rate* clauses (the spectral-gap timing of search on
sparse hosts, the $d > 4$ lattice convergence) remain open `sorry`s, marked as
such and not relied on downstream.

#emph[Structure.]
Section 2 states the verified spine and its lift theorems.
Section 3 gives the three novel verified results: the exact attention
reduction, the verified ML-to-host compiler, and the exact finite-$n$ search
advantage plus its sparse-host versions.
Section 4 models two hardware-named hosts as equitable quotients.
Section 5 gives the on-device experiment (a proposal, not a proof).
Section 6 is the related-work and novelty accounting: we are a
*certificate, not a first contact*.
Section 7 is the open frontier.

#emph[Intended frontend.] The verified backend described here is meant to sit
under a practical deep-learning compiler. Our target frontend is *catgrad*
(hellas.ai), whose open-hypergraph categorical SSA IR is a natural source
language: a Graphplay backend lowers catgrad's categorical IR to the host
representation of Section 3, so that the equitable-reduction and
hardware-compilation theorems apply to programs a practitioner actually
writes. The integration is design-stage; see the forward reference
`paper/catgrad_integration.md` (planned).

#heading("2. The Verified Spine")

#emph[2.1 Equitable partitions and the symmetric quotient.]
A weighted graph on a finite vertex set $V$ is a Hermitian
$A in CC^(V times V)$. A partition $pi$ of $V$ into nonempty cells
$C_1, dots, C_r$ is *equitable* for $A$ when, for every ordered pair of cells
$(C_j, C_k)$, the row sum $sum_(w in C_k) A_(v w)$ is independent of the choice
of $v in C_j$. Writing $D = "diag"(abs(C_1), dots, abs(C_r))$ and $Q$ for the
raw quotient of inter-cell row sums, the object we actually walk on is the
*symmetric (normalized) quotient*
$ tilde(Q) := D^(1 slash 2) Q D^(-1 slash 2), $
which is Hermitian even though $Q$ need not be. This normalization is the
technical pivot of the whole development --- it is what makes the lifted
operator self-adjoint, hence a legitimate Hamiltonian, in every tower.
Lean carriers: `Graphplay/Equitable.lean` (`symmQuotient`,
`symmQuotient_isHermitian`), `Graphplay/Weighted.lean`.

#emph[2.2 The restriction theorem.] The keystone is that the walk restricted
to the cell-uniform subspace *is* the walk on $tilde(Q)$. Concretely, for a
cell-uniform vector $sum_i w_i u_i$ (with $u_i$ the rescaled cell indicators),
$ A dot (sum_i w_i u_i) = sum_i (tilde(Q) w)_i u_i. $
This is `EquitablePartition.restrict_eq_symmQuotient` (#proven, sorry-free,
`Graphplay/Equitable.lean`). From it the rest of the spine follows.

#emph[2.3 The lift theorems.] Each is an axiom-clean Lean theorem.

#table(
  columns: 3,
  stroke: 0.5pt,
  inset: 6pt,
  align: (left, left, left),
  [*Lift*], [*Statement*], [*Lean (#proven)*],
  [Spectrum],
  [$"spec"(tilde(Q)) subset.eq "spec"(A)$; quotient eigenpairs inflate to cell-constant eigenpairs of $A$],
  [`spectrum_subset` \ (`Spectral.lean`)],
  [PST (iff)],
  [cell-uniform PST on $(A, pi)$ holds at time $tau$ #emph[iff] $tilde(Q)$ has PST at $tau$ --- both directions],
  [`cellUniformPST_iff_` \ `quotientPST` \ (`PST/QuotientIff.lean`)],
  [Search],
  [the marked-cell-refined search Hamiltonian restricts to the $(r{+}1)$-dim cell-uniform-plus-marked subspace],
  [`search_quotient_` \ `reduction` (`Search.lean`)],
  [Products],
  [Cartesian-product PST factors through the Kronecker-sum exponential],
  [`cartesianProduct_pst` \ (`Product/PST.lean`)],
)

The PST iff is the Lean form of Bachman--Tamon et al. (arXiv:1108.0339): a
graph has cell-uniform PST exactly when its symmetric quotient does. We prove
both directions sorry-free. The spectrum lift is Godsil's classical
inclusion. Together these are the instruction set the rest of the paper
compiles to.

#emph[2.4 Symmetry produces equitability.] A graph automorphism induces an
equitable partition by its orbits: `equitableOfAutomorphism`
(`Graphplay/Integrations/MachineLearning.lean`, #proven). This is the bridge
that lets a *symmetry* in a model (weight-tying, permutation-equivariance)
become a *quotient* we can reduce against --- the hook Section 3 uses for
attention.

#emph[2.5 The verified-results ledger.] A headline theorem is *axiom-clean*
when `#print axioms` reports only the standard Lean/Mathlib foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`. Of 42 headline
entries, 38 are axiom-clean; the remaining 4 each carry a single named open
clause with every other conjunct proven. The "open clause" column names the
precise gap and the missing infrastructure.

#set text(size: 9.5pt)
#table(
  columns: (auto, auto, auto),
  stroke: 0.5pt + luma(180),
  inset: 5pt,
  align: (left, left, left),
  table.header([*Area / theorem*], [*Status*], [*Open clause (if any)*]),

  table.cell(colspan: 3, fill: luma(238))[*Spine* (equitable-quotient ⟺ PST keystone + lifts)],
  [`cellUniformPST_iff_quotientPST`], [#proven], [—],
  [`restrict_eq_symmQuotient`], [#proven], [—],
  [`spectrum_subset`], [#proven], [—],
  [`search_quotient_reduction`], [#proven], [—],
  [`cartesianProduct_pst`], [#proven], [—],

  table.cell(colspan: 3, fill: luma(238))[*Quantum advantage* (search separation)],
  [`quantum_search_quadratic_advantage`], [#proven], [—],
  [`quantum_search_exact_amplitude`], [#proven], [—],
  [`ml_structured_search_quantum_advantage_exact`], [#proven], [—],
  [`completeGraph_2d_block`], [#proven], [—],

  table.cell(colspan: 3, fill: luma(238))[*Attention / ML* (complexity collapse + compiler)],
  [`blockAttentionApply_eq_fullAttentionApply`], [#proven], [—],
  [`attention_apply_linear_in_n`], [#proven], [—],
  [`training_step_linear_under_equitable`], [#proven], [—],
  [`segment_attention_exact_reduction`], [#proven], [—],
  [`circulant_banded_cost`], [#proven], [—],
  [`no_cheap_exact_factorization` (generic matrix-rank lower bound)], [#proven], [—],
  [`discrete_irreducibility_floor`], [#proven], [—],
  [`chiralAttention_descends`, `PSTRoutingAttention.transfers`], [#proven], [—],
  [`compile_denote_commutes`, `compiler_guarantee`], [#proven], [—],
  [`compiled_cellUniform_realizes_target`, `compile_recall_to_heron`], [#proven], [—],
  [`corrected_equitable_attention`], [#opentag], [whole statement: ε-approx residual bound needs Eckart--Young rank-$k$ SVD-truncation optimality (absent from Mathlib). The matching *exact* lower bound is the proven `no_cheap_exact_factorization`.],

  table.cell(colspan: 3, fill: luma(238))[*Applications* (sparse hosts + hardware-named quotients)],
  [`hypercube_sparse_search_reduction` (sparsity + reduction)], [#proven], [—],
  [`buildable_lattice_structural_contrast`], [#proven], [—],
  [`latticeGraph_isRegular`], [#proven], [—],
  [`dataFlagQuotient_eigenvalues` (IBM heavy-hex)], [#proven], [—],
  [`heavyHex_pst_lift`, `dephasing_preserves_dataFlag`], [#proven], [—],
  [`sectorProjector_sum` (Majorana-1 parity)], [#proven], [—],
  [`payoff2_parity_noise_preserves_partition`], [#proven], [—],
  [`compiled_experiment_prediction` (structural)], [#proven], [—],
  [`hypercube_search_optimal_timing`], [#opentag], [whole statement: $O(sqrt(N))$ optimal *timing* needs the CNO spectral-ratio core.],
  [`lattice_search_dimension_threshold`], [#opentag], [whole $<-->$: the $d > 4$ threshold needs the Childs--Goldstone spectral integral (IR-convergence).],
  [`buildable_lattice_dynamical_contrast`], [#opentag], [both dynamical clauses route through the two timing `sorry`s above.],

  table.cell(colspan: 3, fill: luma(238))[*Negative results* (no-go's)],
  [`dataFlag_chiral_no_speedup` (no chiral speedup)], [#proven], [—],
  [`dominatingVertex_no_PST`, `cone_apex_no_PST`], [#proven], [—],

  table.cell(colspan: 3, fill: luma(238))[*Dirac / relativistic enrichment* (frontier)],
  [`offDiagonalBloch_eigenvalues` (±‖f(k)‖ bands)], [#proven], [—],
  [`bipartite_equitable_dirac_cone`], [#opentag], [conjuncts (1) band-touching at $k=pi$ and (2) symmetric bands are *proven*; only conjunct (3)'s *local linearity* of the cone is `sorry` (small-$k$ Taylor remainder, no packaged Mathlib lemma).],
  [`coinedWalk_continuum_dirac_conjecture`], [#opentag], [an *open conjecture*, not a theorem: the rescaled coined-walk generator converges (op-norm) to the massless Dirac Bloch generator; no Mathlib scaling-limit calculus.],
)
#set text(size: 11pt)

Each non-clean entry routes through missing analysis infrastructure
(Eckart--Young SVD truncation; CNO / Childs--Goldstone spectral-timing;
small-angle Taylor remainder), and we condition only on the proven conjuncts.

#heading("3. Novel Verified Results")

This section contains the results that are ours. Each is a sorry-free Lean
theorem; the few deep rate clauses we depend on nowhere are flagged where they
appear.

#emph[3.1 Exact $O(n^2) -> O(n dot r)$ attention reduction.]
Cast single-head attention as application of a token-token score operator on
$n$ tokens of width $d$. If the score pattern is *equitable* with $r$ cells
(weight-tying, block structure, or an equivariance orbit via §2.4), the
$O(n^2 d)$ full application equals a *block* application that costs
$O(n r d + n d)$.

#block(fill: luma(245), inset: 8pt, radius: 4pt, width: 100%)[
The forward identity is exact, not approximate:
$ "blockAttentionApply" = "fullAttentionApply" $
(`blockAttentionApply_eq_fullAttentionApply`, #proven, sorry-free), with cost
`blockCost` $= n r d + n d$ linear in $n$ (`attention_apply_linear_in_n`,
#proven) and `blockCost_le_fullCost` for $r <= n$ (#proven).
]

The reduction is verified through *training*, not just inference:
- *Backward pass.* The block gradient computes the same gradient as the dense
  backward (`blockGrad_apply`, #proven).
- *Training step.* One full step (forward + backward + update) is linear in
  $n$ under a maintained equitable structure
  (`training_step_linear_under_equitable`, #proven).

Lean: `Graphplay/Integrations/AttentionComplexity.lean`. The structural
identity is exact and sorry-free; the reduction is conditioned only on it.

#emph[Scope of the precondition.]
The reduction fires when the attention is *equitable* in the relevant axis.
A content-dependent dense *learned* score matrix has, generically, no
nontrivial automorphism, so its finest equitable partition is the discrete one
($r = n$) and the reduction is the identity. The theorem bites where the score
pattern is structured.

Efficiency pressure has pushed *production* attention toward structured, hence
equitable, patterns. These split by *which* reduction each enables.

#table(
  columns: (auto, auto, auto, auto),
  inset: 6pt,
  align: (left, left, left, left),
  stroke: 0.5pt + luma(180),
  table.header(
    [*Structure*], [*Example*], [*Reduction*], [*Lean*],
  ),
  [Token-axis cell\ (segment/block-uniform,\ grouped/pooled)],
  [block-/segment-attention,\ pooled tokens],
  [$O(n^2) -> O(n r)$, exact:\ $A[i][j]$ depends only\ on token *cells*],
  [`blockAttentionApply`\ (this section), #proven],

  [Banded / Toeplitz\ (sliding-window, local)],
  [Mistral, Longformer],
  [$O(n w)$ via *translation*\ (circulant-equitable under\ the cyclic group) ---\ a *distinct* reduction],
  [`circulant_banded_cost`,\ #proven],

  [Head-axis\ (grouped-/multi-query)],
  [GQA / MQA: Llama,\ Mistral],
  [exact head-cell quotient],
  [`multiHead_restrict_`\ `eq_symmQuotient`, #proven],

  [Positional structure\ (relative schemes)],
  [RoPE (rotation-equiv.),\ ALiBi (distance-based)],
  [*restores* the translation/\ rotation equivariance that\ learned-absolute\ embeddings break],
  [in progress],
)

The token-axis block apply is exact when $A[i][j]$ depends only on the *cells*
of $i$ and $j$. The banded / Toeplitz case is a distinct reduction riding
*translation* (circulant-equitability under the cyclic group), an $O(n w)$ cost
that should not be conflated with the cell-structure $O(n r)$. The head-axis
case is the proven `multiHead_restrict_eq_symmQuotient` of §3.2. Relative
position (RoPE, ALiBi) restores the translation- and rotation-equivariance that
learned *absolute* embeddings break, so the architectural trend --- RoPE,
sliding-window attention, grouped-query attention --- moves production attention
toward the equitable regime.

For the residual dense-learned case the exact reduction does not fire; instead
the equitability *defect* --- distance from the realized score pattern to the
nearest equitable partition --- is measurable and bounds the resulting error.
The catgrad equitability-defect probe (see `paper/catgrad_integration.md`)
computes the equitable partition of a model's attention hypergraph and reports
the defect. The structured cases are formalized as explicit equitable partitions
in `Graphplay/Integrations/StructuredAttention.lean`: segment-uniform
($O(n r)$, `segment_attention_exact_reduction`, #proven axiom-clean), grouped/
pooled (the `pooledTokens_equitable` construction), and the banded translation
reduction ($O(n w)$, `circulant_banded_cost`, #proven axiom-clean); the FFT
spectral-cost step is an open `sorry`.

#emph[3.2 The functor stack is a verified compiler.]
We define a small typed transformer DSL (`TransformerProgram`) with a
denotational semantics `denote` and a compilation pass `compile` that targets
the symmetric quotient host. The compiler is correct by theorem.

#block(fill: luma(245), inset: 8pt, radius: 4pt, width: 100%)[
- `compile_denote_commutes` (#proven, *zero sorries*): the diagram commutes ---
  compiling then denoting equals denoting then evaluating on $tilde(Q)$.
- `compiler_guarantee` (#proven, *zero sorries*): the compiled program is
  *both* semantics-preserving *and* complexity-reducing (linear in $n$).
]

This is the wedge against the empirical "quantum-walk transformer" literature
(Section 6): there, the walk is a heuristic feature; here, the compiler from ML
semantics to walk host carries a machine-checked commuting-semantics proof.
Lean: `Graphplay/Integrations/TransformerDSL.lean`. The multi-head pooled head
restricts to the symmetric quotient
(`multiHead_restrict_eq_symmQuotient`, #proven,
`Integrations/MachineLearning.lean`). A concrete ML-to-device specialization
(`compiled_cellUniform_realizes_target`, `compile_recall_to_heron`, #proven)
lives in `Graphplay/Applications/CompileML.lean` and feeds Section 5.

#emph[3.3 Exact finite-$n$ quantum search advantage.]
On the complete graph $K_n$ with one marked vertex, the search dynamics live
in an exact $2$-dimensional invariant subspace (`completeGraph_2d_block`,
#proven). We extract the *exact* finite-$n$ amplitude:

#block(fill: luma(245), inset: 8pt, radius: 4pt, width: 100%)[
At evolution time $t_q <= (pi slash 2) sqrt(n)$, the exact search amplitude is
at least $sqrt((n-1) slash n) >= sqrt(1 slash 2)$
(`quantum_search_exact_amplitude`, #proven, sorry-free), against the classical
fact that fewer than $n$ queries cannot certify the marked element
(`classical_search_lower_bound`). The pair is
`quantum_search_quadratic_advantage` (#proven).
]

Lifting along §2.4: a structured ML search over $r$ configurations inherits the
exact advantage --- amplitude $>= sqrt(1 slash 2)$ in time $<= (pi slash 2)
sqrt(r)$ versus an $r$-query classical bound
(`ml_structured_search_quantum_advantage_exact`, #proven). The matching quantum
*optimality* (the $Omega(sqrt(N))$ side) is Bennett--Bernstein--Brassard--Vazirani;
we cite it and do not reprove it. Lean:
`Graphplay/Integrations/QuantumAdvantage.lean`.

#emph[3.4 Advantage on sparse, buildable hosts.]
The complete graph is not buildable. The point of this subsection is that the
*same* equitable-quotient route gives the advantage on hosts with bounded
degree.

- *Hypercube (proven half).* The Boolean hypercube $Q_d$ is $d$-regular with
  $d = log_2 N$ --- log-degree, hence physically realizable --- and its
  Hamming-distance partition into $d+1$ cells is equitable; the marked search
  Hamiltonian collapses to the $(d{+}1)$-dimensional binomial chain. Both the
  *sparsity* (regularity) and the *exact equitable reduction* to the Hamming
  chain are a single sorry-free theorem
  (`hypercube_sparse_search_reduction`, #proven, axiom-clean) --- and it carries
  *no* timing clause. The deep $O(sqrt(N))$ *optimal-timing* statement is split
  off as a *separate* theorem, `hypercube_search_optimal_timing`, whose entire
  content (`IsOptimalCTQWSearch (Hypercube d) w`) leans on the
  Childs--Goldstone / CNO spectral-ratio analysis (arXiv:2004.12686) and is an
  open `sorry`. We mark it #opentag and do not use it downstream.

- *Lattice threshold.* The $d$-dimensional lattice is $2d$-regular
  (`latticeGraph_isRegular`, #proven). The *structural* contrast between lattice
  and hypercube --- lattice $2d$-regular on $L^d$ vertices versus hypercube
  $e$-regular on $log_2 N$ vertices --- is sorry-free
  (`buildable_lattice_structural_contrast`, #proven, axiom-clean). The
  *dynamical* contrast (`buildable_lattice_dynamical_contrast`) --- that the
  lattice is not an optimal search host for $d <= 3$ while the hypercube is
  optimal --- is stated #opentag: both dynamical clauses route through open
  `sorry`s (the lattice half through `lattice_search_dimension_threshold`, the
  hypercube half through `hypercube_search_optimal_timing`). The threshold
  itself, `lattice_search_dimension_threshold` --- the advantage appears for
  $d > 4$ and fails below --- is a formalized $<-->$ statement whose equivalence
  is an open `sorry` (#opentag), pending the Childs--Goldstone spectral integral
  (the $d > 4$ IR-convergence of the lattice Green's function).

Lean: `Graphplay/Applications/SparseSearch.lean`. The *structural* reductions
are verified; the *dynamical timing* of search is where the open mathematics
lives, and the `sorry` sits there.

#heading("4. Modeling Hardware-Named Hosts as Equitable Quotients")

The spine runs in reverse: given a host Hamiltonian, read off its equitable
quotient. We carry out two such constructions in Lean. Both use device names
for orientation; each is a graph-theoretic model, not a fabricated chip.

#emph[4.1 A complete-site subdivision with data/flag labels.]
On the complete-site subdivision graph $K_N$ with a two-cell data/flag
labeling, the data/flag partition is equitable, and its symmetric quotient is
the $2 times 2$ Hermitian matrix with spectrum

#block(fill: luma(245), inset: 8pt, radius: 4pt, width: 100%)[
$ "spec"(tilde(Q)_("data/flag")) = { plus.minus 2 sqrt(N - 1) }, wide
  N = 2 n m $
(`dataFlagQuotient_eigenvalues`, #proven, sorry-free).
]

This is a degree-$(N{-}1)$ host, not the degree-3 honeycomb topology of the
physical heavy-hex lattice. On the $2 times 2$ quotient
(`Graphplay/Applications/IBMHeavyHex.lean`):
+ *PST* between the data and flag cells at the quotient PST time
  (`heavyHex_pst_lift`, #proven);
+ a data/flag-symmetric dephasing channel preserves the partition
  (`dephasing_preserves_dataFlag`, #proven), and the real data/flag quotient
  gives no search speedup (`dataFlag_chiral_no_speedup`, #proven).

#emph[4.2 Parity projectors with Majorana labels.]
For a parity-conserving model carrying Majorana 1 labels we construct the
parity-sector projectors and prove they are Hermitian and sum to the identity
(`sectorProjector_sum`, #proven), and that a parity-respecting noise model
preserves the resulting decomposition
(`payoff2_parity_noise_preserves_partition`, #proven). Lean:
`Graphplay/Applications/MajoranaOne.lean`. The proven content is the
resolution-of-identity for the parity projectors; no effective single-tetron
Hamiltonian is derived.

#heading("5. A Falsifiable On-Device Protocol")

This section is a proposal: a falsifiable experiment the compiler emits for
existing hardware.

#emph[The CompileML protocol on IBM Heron.] Compile a key--value recall task to
the data/flag CTQW host of §4.1 (`compile_recall_to_heron`, #proven, as a Lean
object).
The on-device protocol is:
+ *Prepare* a query-uniform initial state (uniform over the data cell);
+ *Evolve* under the native CTQW for time $pi slash (2 q)$, where $q$ is the
  quotient coupling;
+ *Measure* the key-uniform (flag-cell) population.

The compiler's prediction (`compiled_experiment_prediction`, #proven as the
structural identity) is that the measured key population equals the squared
quotient amplitude. Crucially, the protocol is *falsifiable*: if the device's
true coupling pattern breaks the data/flag partition, a nonzero
*BreakingScore* appears, and the predicted population deficit is proportional
to it (`compiled_breakingScore_zero_blockDiagonal`, and the falsification
witness `compiled_positive_breakingScore_exists`). The experiment thus tests
the partition hypothesis on the real chip rather than assuming it. Lean:
`Graphplay/Applications/CompileML.lean`. The intended path from a practitioner
program to this protocol runs through the catgrad frontend
(`paper/catgrad_integration.md`, planned).

#heading("6. Related Work and Novelty")

We are a *certificate, not a first contact*. The mathematics of our spine, and
of every physical phenomenon we lift, is prior art; our wedge is the
machine-checked exactness, the verified compiler, and the falsifiable
experiment.

#emph[The spine.] The equitable-partition-to-quotient lift, and PST-iff-quotient
in particular, is *Bachman--Fredette--Fuller--Landry--Opperman--Tamon--Tollefson*
(arXiv:1108.0339) on a base of *Godsil's* spectral and PST theory
(arXiv:1102.4898). The unification of equitable partition, PST, and CTQW search
is *Ide--Narimatsu* (arXiv:2209.07688) --- the single closest prior work to our
thesis, and the source of the mathematical content we formalize. We claim none
of this mathematics; we claim its Lean certificate.

#emph[Sparse-host search.] CTQW spatial search on $K_n$ and the hypercube is
*Childs--Goldstone* (quant-ph/0306054). That a *local* equitable symmetry
(not a global automorphism) suffices for fast search is *Janmark--Meyer--Wong*
(arXiv:1403.2228) --- exactly our "equitable, not automorphism" framing. The
success-probability/finding-time reduction via equitable partition is again
*Ide--Narimatsu* (arXiv:2209.07688). The $Omega(sqrt(N))$ optimality is
Bennett--Bernstein--Brassard--Vazirani. Our `hypercube_sparse_search_reduction`
(the sparsity-and-equitable-reduction half, axiom-clean) and the structural
lattice contrast (`buildable_lattice_structural_contrast`, axiom-clean) formalize
this corpus; the timing `sorry`s --- isolated in `hypercube_search_optimal_timing`
and `lattice_search_dimension_threshold` --- sit precisely on the analytic content
(arXiv:2004.12686) that these works supply on paper.

#emph[Attention as a quantum walk.] Marrying a quantum walk to transformer
attention is already done: *GQWformer* (arXiv:2412.02285) and *CTQWformer*
(arXiv:2605.09486). Both are *classical and empirical* --- the walk is an
inductive bias or a precomputed feature; neither claims, let alone proves, an
exact complexity reduction, and both retain $O(n^2)$ attention. The bare bridge
is theirs; we cite it as motivation, not competition.

#emph[Our wedge, in one sentence.] We (a) cast structured attention as the
equitable token-graph operator and machine-check its exact
$O(n^2) -> O(n r)$ reduction across forward, backward, and training step;
(b) expose that as a typed ML-to-host compiler with a proven commuting
semantics; and (c) emit from the same compiler a falsifiable on-device PST
experiment.

#heading("7. Open Frontier")

We are explicit that the following are #emph[not] proven. They are the program's
horizon, and we state them as open.

#emph[7.1 Conjecture 9.3 (Bose--Mesner $eq.triple$ chiral $eq.triple$ graphon).]
A consistent family $(G_n, pi_n)$ admits *both* a graphon quasi-infinite limit
*and* a strict chiral-signing mixing speedup #emph[iff] its Bose--Mesner algebra
eventually coincides with the partition-projector algebra $cal(P)(pi_n)$. The
Lean apparatus (`Graphplay/Dowsing/Conjecture93.lean`) builds *six genuine test
families* as real `WeightedGraph` objects with proven equitable
partitions --- $K_n^sigma$, the Heawood envelope, Hamming schemes,
$K_(n,n,n,n)$, $K_n + P_n$, and $"Cayley"(S_n)$ by transpositions. But *both
halves of the conjecture itself are `sorry`* (`Conjecture93_weak` and its
forward/reverse directions); the only family verdict proven outright is the
both-sides-false $"Cayley"(S_n)$ case ($"False" <-> "False"$). #opentag
We claim the *families and the statement*, not the theorem.

#emph[7.2 Relativistic / Dirac enrichment.] A Dirac-operator (first-order,
spinorial) enrichment of the spine is partly proven and partly open. For the
honeycomb off-diagonal Bloch block, the $plus.minus norm(f(k))$ band structure
(`offDiagonalBloch_eigenvalues`, #proven) and, in `bipartite_equitable_dirac_cone`,
the *band-touching at $k = pi$* and the *symmetric bands* are proven axiom-clean;
only that theorem's third conjunct --- the *local linearity* of the Dirac cone,
the small-$k$ Taylor expansion $f(pi + kappa) = -i q kappa + O(kappa^2)$ --- is an
open `sorry` (#opentag), no packaged Mathlib remainder lemma. The full
quantum-walk $-->$ continuum-Dirac scaling limit is stated as a genuine *open
conjecture*, `coinedWalk_continuum_dirac_conjecture` (#opentag) --- a
non-tautological op-norm convergence of the rescaled coined-walk generator to the
massless Dirac Bloch generator, awaiting a Mathlib scaling-limit calculus; it is
*not* a proved theorem.

#emph[7.3 The $infinity$-categorical towers.] Towers 6--7 (sheaves of weighted
graphs; stable-$infinity$-categorical Hermitian endomorphisms with coherent
idempotent partitions) are *definitional scaffolds only*. The key
colimit-preservation obligation (`Quotient.mapCocone_isColimit`) is an
irreducible `sorry` blocked on missing Mathlib $infinity$-categorical
infrastructure. These towers are *not proven* and we make no theorem-level claim
about them. #opentag

#emph[7.4 Externals carried as cited hypotheses.] Several results are
conditioned on deep external theorems we state as typeclass assumptions rather
than reprove: Lovász-$theta$ SDP strong duality, the Choi and Stinespring
representation theorems, the FKLW topological-order theorem, Villani strong
duality and Birkhoff contraction for the transport integration, the BCLSV
graphon cut-limit, MIP$""^* = "RE"$, and HHL convergence. Each names the cited
result and conditions the downstream statement on it. The Lovász sandwich
$alpha lt.eq theta lt.eq overline(chi)$, the Tsirelson bound $2 sqrt(2)$, and
the classical CHSH value $3 slash 4$ (`CHSH_classical_value`,
`Graphplay/QuantumCSP.lean`) are proven. Some Tower-4 spectral statements
carry `sorry`s on the measure side.

#emph[7.5 Toward the practical frontend.] The intended path to use is a
Graphplay backend under *catgrad* (hellas.ai): lower its open-hypergraph
categorical SSA IR to the host representation of Section 3 so that the verified
attention reduction and the hardware compiler apply to real models. This is
design-stage (`paper/catgrad_integration.md`, planned), and the
quantitative noisy-CTQW and Lindbladian extensions of the spine remain open
beyond the cell-uniform invariance already proven.

#v(0.6em)
#line(length: 100%, stroke: 0.4pt)
#v(0.3em)
#emph[A closing note.] Transfer at an integer time and search that finds in
$sqrt(N)$ steps both dissolve into small finite calculations seen through the
right partition; Lean checks the calculation. What we offer is a ledger: the
structure, the proof, and a clear mark on what remains open.

#heading("References")

#set par(justify: false)

#emph[Spine --- equitable partitions, PST, quotients:]
- C. Godsil. #link("https://arxiv.org/abs/1102.4898")[State transfer on
  graphs], arXiv:1102.4898.
- R. Bachman, E. Fredette, J. Fuller, M. Landry, M. Opperman, C. Tamon,
  A. Tollefson. #link("https://arxiv.org/abs/1108.0339")[Perfect state transfer
  on quotient graphs], arXiv:1108.0339 (QIC 12, 293).
- Y. Ide, A. Narimatsu. #link("https://arxiv.org/abs/2209.07688")[Perfect state
  transfer, equitable partition and continuous-time quantum walk based search],
  arXiv:2209.07688.

#emph[Search --- sparse hosts, optimality, timing:]
- A. Childs, J. Goldstone. #link("https://arxiv.org/abs/quant-ph/0306054")[Spatial
  search by quantum walk], quant-ph/0306054 (PRA 70, 022314).
- I. Janmark, D. Meyer, T. Wong.
  #link("https://arxiv.org/abs/1403.2228")[Global symmetry is unnecessary for
  fast quantum search], arXiv:1403.2228 (PRL 112, 210502).
- S. Chakraborty, L. Novo, J. Roland.
  #link("https://arxiv.org/abs/2004.12686")[On the optimality of spatial search
  by continuous-time quantum walk], arXiv:2004.12686 (PRA 102, 032214).
- C. Bennett, E. Bernstein, G. Brassard, U. Vazirani. #emph[Strengths and
  weaknesses of quantum computing], SIAM J. Comput. 26 (1997) (BBBV lower bound).

#emph[Attention as quantum walk (classical / empirical, concurrent):]
- Yu, Chen, Lv, Yang (Zhejiang Lab).
  #link("https://arxiv.org/abs/2412.02285")[GQWformer: A quantum-based
  transformer for graph representation learning], arXiv:2412.02285.
- #link("https://arxiv.org/abs/2605.09486")[CTQWformer: A CTQW-based transformer
  for graph classification], arXiv:2605.09486.
- S. Aaronson. #link("https://www.scottaaronson.com/papers/qml.pdf")[Quantum
  machine learning: read the fine print], Nature Physics 11 (2015).

#emph[Hardware:]
- IBM Quantum. #link("https://www.ibm.com/quantum/blog/heavy-hex-lattice")[The
  IBM Quantum heavy-hex lattice], 2021.
- #link("https://www.nature.com/articles/s41467-023-37725-0")[Observing and
  braiding topological Majorana modes on a superconducting processor], Nature
  Commun. 14 (2023).
- #link("https://www.nature.com/articles/s41467-025-57818-2")[Perfect state
  transfer on superconducting transmons with tunable couplers], Nature Commun.
  16 (2025).

#emph[Frontend (intended):]
- catgrad, hellas.ai --- open-hypergraph categorical deep-learning compiler.
  Graphplay-backend integration: `paper/catgrad_integration.md` (planned).

#emph[Companion material:]
- Graphplayers Crew. #emph[Graphplay research program]
  (`paper/research_program.typ`): the dowsing-rod open theorems, cross-disciplinary
  integrations, conjectural Towers 6--7, and the full Conjecture 9.3 analysis.
