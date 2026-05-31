#set document(title: "Graphplay: A Machine-Checked Theory of Equitable-Partition Quantum Walks")
#set page(margin: 0.85in)
#set text(size: 10.5pt)
#set par(justify: true)
#show raw: set text(size: 9pt)

#align(center)[
  #text(size: 18pt, weight: "bold")[Graphplay] \
  #v(0.25em)
  #text(size: 13pt, weight: "bold")[A machine-checked theory of equitable-partition quantum walks] \
  #v(0.35em)
  #text(size: 11pt, style: "italic")[Verified attention-complexity reduction, an ML#sym.arrow.r chip compiler,
  and falsifiable hardware experiments] \
  #v(0.5em)
  #text(size: 9.5pt)[Graphplay Crew --- pitch draft, May 2026]
]

#v(0.8em)

#heading("Abstract")

We give a Lean 4 + Mathlib formalization of equitable-partition quantum walks
and use it to prove five things that, to our knowledge, have not been proven
(let alone machine-checked) before. (1) Structured attention compiles to a
continuous-time quantum walk (CTQW) Hamiltonian whose equitable quotient
evaluates the attention map *exactly* --- not approximately ---
in $O(n dot r)$ work where the naive cost is $O(n^2)$; the correctness identity
`blockAttentionApply_eq_fullAttentionApply` is sorry-free. (2) A typed ML#sym.arrow.r chip
compiler whose semantics-preservation theorem `compile_denote_commutes` is
proven: the compiled quotient computes the same function the source program
denotes, and is strictly cheaper. (3) Verified quantum-search advantage on a
*sparse, physically buildable* host: the Boolean hypercube's
Hamming-distance equitable quotient collapses marked search to a
$(d{+}1)$-dimensional chain, with sparsity and the exact equitable reduction
proven axiom-clean (`hypercube_sparse_search_reduction`); we are honest that the
$O(sqrt(N))$ *optimal-timing* statement is a *separate* theorem
(`hypercube_search_optimal_timing`, an open `sorry`), as is the $d > 4$ lattice
threshold (`lattice_search_dimension_threshold`), both deferred to the
Chakraborty--Novo--Roland spectral criterion. (4) Verified spectral
disassembly of real chips --- IBM heavy-hex (`dataFlagQuotient_eigenvalues`)
and the Microsoft Majorana-1 parity sectors (`sectorProjector_sum`) --- as
equitable quotients. (5) A falsifiable on-device experiment
(`compiled_experiment_prediction`) emitted by the same compiler, predicting a
key population from a verified amplitude on IBM Heron hardware.

#emph[The honest claim.] The *mathematics* of equitable-quotient quantum walks
is not ours: it is Godsil, Bachman--Tamon, Ide--Narimatsu, Childs--Goldstone,
and Janmark--Meyer--Wong (#sym.section 4). The walk-as-attention idea is
concurrent classical work (GQWformer, CTQWformer). Our contribution is the
*certificate*: the first machine-checked, end-to-end stack from an exact
verified attention reduction, through a typed hardware compiler with a proven
commuting semantics, to a falsifiable on-chip prediction. We seek
collaborators.

#heading("1. Five results, stated precisely")

Everything below is a named Lean theorem. We mark each as #emph[proven]
(sorry-free), #emph[proven core / deferred clause] (the load-bearing identity is
sorry-free, an explicitly flagged dynamical/spectral clause is deferred), or
#emph[open].

#emph[Result 1 --- Exact $O(n^2) -> O(n dot r)$ attention. #text(fill: rgb("#1a7f37"))[proven].]
Cast a (symmetrized) attention pattern as a weighted token graph and suppose it
is block-constant under an equitable partition into $r$ cells. Then the
attention apply factors through the $r times r$ symmetric quotient and computes
the *same output vector* in $O(n dot r)$ instead of $O(n^2)$ work:
$
  "blockAttentionApply"(A, B, "cell", V) = "fullAttentionApply"(A, V).
$
This is `blockAttentionApply_eq_fullAttentionApply` in
`Graphplay/Integrations/AttentionComplexity.lean` --- sorry-free, with the
forward apply, the backward pass (`blockGrad_apply`), and a training step
(`training_step_linear_under_equitable`) all linear in $n$. The reduction is
*exact*: no rank truncation, no kernel approximation. (The separate
`attention_quantum_composition` carries an honest `sorry` on a deep
quantum-rate clause; the structural reduction does not depend on it.)
The precondition is honest and bounded: the exact reduction fires on
*equitable* attention --- block/segment, grouped-query (GQA/MQA), and
relative-position (RoPE, sliding-window) patterns that production transformers
already use for efficiency --- and not on fully-dense *learned* attention, for
which we instead measure the equitability defect rather than claim the
reduction (#sym.section 3.1, "Scope of the precondition").

#emph[Result 2 --- A verified ML#sym.arrow.r chip compiler. #text(fill: rgb("#1a7f37"))[proven].]
`Graphplay/Integrations/TransformerDSL.lean` defines a small typed language of
transformer programs with a denotational semantics `denote` and a compiler
`compile` into the quotient representation. The keystone is sorry-free:
$
  "denote"(P) = "denote"_("quotient")("compile"(P))
  quad ("compile_denote_commutes").
$
The functor `compiler_guarantee` packages this with the complexity drop
(`compiled_apply_le_naive`): the compiled program is *semantics-preserving and
strictly cheaper*. This is the "functor stack" --- a compiler whose
correctness is a theorem, not a test suite. (catgrad, the categorical
auto-differentiation framework from hellas.ai, is the intended practical
frontend for emitting these programs from real models.)

#emph[Result 3 --- Search advantage on a buildable sparse host.
#text(fill: rgb("#9a6700"))[proven core / deferred timing].]
`hypercube_sparse_search_reduction` (`Applications/SparseSearch.lean`) proves,
axiom-clean, that the Boolean hypercube $Q_d$ is (a) $d$-regular with $d = log_2 N$
--- log-degree, hence sparse and physically realizable, unlike $K_N$'s degree
$N{-}1$ --- and (b) that its Hamming-distance partition is equitable and
collapses marked CTQW search exactly to a $(d{+}1)$-dimensional chain (this
theorem carries *no* timing clause). The $O(sqrt(N))$ *optimal-timing* statement
is a *separate* theorem, `hypercube_search_optimal_timing`, whose whole content is
a single honest `sorry`, deferred to the Chakraborty--Novo--Roland spectral-ratio
criterion (arXiv:2004.12686) --- the same dynamical core deferred by the $K_n$
flagship. The structural lattice-vs-hypercube contrast is itself proven axiom-clean
(`buildable_lattice_structural_contrast`); the general lattice *threshold* is
stated as `lattice_search_dimension_threshold`: a $d$-dimensional lattice supports
the advantage iff $d > 4$ (Childs--Goldstone); the statement is written, its
*entire* equivalence deferred (as is the dynamical contrast
`buildable_lattice_dynamical_contrast`). The exact finite-$n$ $K_n$
amplitude `quantum_search_exact_amplitude` is fully proven.

#emph[Result 4 --- Verified disassembly of real chips. #text(fill: rgb("#1a7f37"))[proven].]
We model two real devices as equitable quotients and check the spectral data in
Lean. The IBM heavy-hex lattice has a 2-cell data/flag equitable partition;
`dataFlagQuotient_eigenvalues` (`Applications/IBMHeavyHex.lean`) computes the
quotient spectrum, from which cell-uniform PST timing on the chip's *native*
couplings is read off. Microsoft's Majorana-1 tetron has a joint-parity-sector
partition; `sectorProjector_sum` (`Applications/MajoranaOne.lean`) proves the
sector projectors resolve the identity, i.e. the parity sectors are a genuine
orthogonal decomposition. (Majorana-1 honesty: present hardware *simulates*
Majorana modes rather than realizing native topological qubits; this file is a
modeling exercise, flagged as such.)

#emph[Result 5 --- A falsifiable on-Heron experiment. #text(fill: rgb("#1a7f37"))[proven structural form].]
From the heavy-hex disassembly the compiler emits a concrete prediction:
`compiled_experiment_prediction` (`Applications/CompileML.lean`) ties a
predicted measured key-population to the squared amplitude of the verified
quotient walk (`predictedKeyPopulation_eq_amplitude_sq`). A companion witness
`compiled_positive_breakingScore_exists` exhibits a configuration whose
breaking-score is nonzero --- i.e. a *falsifier*: an experiment that, run on IBM
Heron, would disconfirm the prediction if the cell-uniform structure is broken.
A verified prediction with a built-in way to be wrong is the experimental teeth
of the whole stack.

#heading("2. The spine: equitable-quotient lifts, mechanized")

All five results ride on one structural skeleton, formalized once and reused.
Given an operator $A$ (an attention pattern, a search Hamiltonian, a chip
coupling matrix) and an *equitable partition* $pi$ with characteristic isometry
$P$ and symmetric quotient $A slash pi$:

+ #emph[Spectral lift.] $"spec"(A slash pi) subset.eq "spec"(A)$, with
  cell-constant eigenvectors lifting along $P$.
+ #emph[Dynamical restriction.] $exp(-i t A)$ commutes with the cell-uniform
  projector and acts on its range as $exp(-i t (A slash pi))$.
+ #emph[Primitive transport.] For cell-uniform initial/target data, PST /
  mixing / search holds on $(A, pi)$ #emph[iff] it holds on the small matrix
  $A slash pi$ --- this is `cellUniformPST_iff_quotientPST`
  (`PST/QuotientIff.lean`), our mechanization of the Bachman--Tamon
  quotient-iff theorem.

The point of the formalization is that *the same three lemmas* are reused
verbatim by the attention reduction (Result 1), the search collapse (Result 3),
and the chip disassemblies (Results 4--5). The library builds end-to-end on a
current Mathlib; the load-bearing theorems named in #sym.section 1 are
sorry-free or have explicitly-flagged single deferred clauses. Larger
"dowsing-rod" extension files (graphon limits, $infinity$-categorical towers)
carry precise statements with proofs in progress --- these are the research
frontier, not the load-bearing claims.

#heading("3. Why a certificate, in this domain, is the whole point")

Two failure modes plague quantum-walk-for-ML and quantum-hardware claims:
silently approximate "exact" reductions, and speedups that evaporate under
state-preparation/readout caveats (Aaronson, *Read the fine print*). A
machine-checked proof closes the first: `blockAttentionApply_eq_fullAttentionApply`
*cannot* be an approximation that was rounded into an equality, because Lean
would reject it. And by tracking every `sorry`, we make the second mode
auditable: the deferred clauses (CNO timing, the $d>4$ spectral half) are named
and isolated, so a reader sees exactly where the physics input is assumed rather
than proven. The honesty is itself the contribution: a transparent
proven/deferred ledger is something the empirical and pencil-and-paper
literature structurally cannot provide.

#heading("4. Honest novelty --- what is prior art, what is ours")

We are a *certificate*, not first contact. The mathematics is established and we
attribute it explicitly:

#table(
  columns: 2,
  stroke: 0.5pt,
  inset: 6pt,
  align: (left, left),
  [*Idea*], [*Source (prior art --- we formalize, not originate)*],
  [Quotient-iff PST under equitable partition],
  [Bachman--Tamon et al. 2012 (arXiv:1108.0339); Godsil survey 2011 (arXiv:1102.4898)],
  [CTQW search collapses to a small quotient via equitable partition + PST],
  [Ide--Narimatsu 2022 (arXiv:2209.07688) --- closest prior work to our spine],
  [$O(sqrt(N))$ spatial search on $K_n$ / hypercube],
  [Childs--Goldstone 2004 (quant-ph/0306054)],
  [Fast search needs only *local* (equitable), not global, symmetry],
  [Janmark--Meyer--Wong 2014 (PRL 112 210502 / arXiv:1403.2228)],
  [$d>4$ lattice search threshold],
  [Childs--Goldstone; CNO spectral criterion 2020 (arXiv:2004.12686)],
  [Quantum walk as transformer attention bias (classical)],
  [GQWformer 2024 (arXiv:2412.02285), CTQWformer 2026 (arXiv:2605.09486) --- #emph[concurrent]],
)

GQWformer and CTQWformer are concurrent *classical* attention-as-walk work:
they compute a walk classically as an inductive bias for graph classification,
with no exactness guarantee, no complexity reduction, no hardware, and no
proof. Our wedge is orthogonal to theirs along three axes simultaneously:

#block(inset: (left: 1em), [
*exactness* (the reduction is an identity, not a heuristic feature) #sym.times.o
*verification* (every claim is a Lean theorem, with a transparent sorry-ledger) #sym.times.o
*hardware* (a typed compiler emitting a falsifiable experiment for a named chip).
])

No prior work claims, let alone machine-checks, the exact $O(n^2) -> O(n dot r)$
equitable-attention reduction, the typed ML#sym.arrow.r chip compiler with a commuting
semantics, or the compiler-emitted falsifiable PST experiment. That stack is
ours and, as far as we can determine, uncontested.

#heading("5. Open problems and the research program")

We are explicit about what is *not* done:

#emph[Deferred dynamical/spectral clauses (named, isolated).] The $O(sqrt(N))$
CNO timing for hypercube/lattice search; the forward (spectral) half of
`lattice_search_dimension_threshold`. These reduce to the
Chakraborty--Novo--Roland ratio criterion, which we have stated but not yet
mechanized.

#emph[Conjectural with worked examples.] Conjecture 9.3 --- a consistent
sequence $(G_n, pi_n)$ admits both a graphon quasi-infinite limit and a strict
chiral mixing speedup iff its limit Bose--Mesner algebra coincides with the
limit partition-projector algebra. Weak version expected true, strong version
expected false; we have both-sides-false witnesses and one candidate
counterexample.

#emph[Frontier towers (scaffold).] The $infinity$-categorical / sheaf-theoretic
envelopes (quasi-infinite walks as filtered colimits; topological protection as
a sheaf $H^1$-class) have precise statements awaiting Mathlib infrastructure
(operator-system, sheaf-of-$C^*$-algebra, and $infinity$-category libraries) and
the Dirac/continuum limit. These are multi-year items, marked open.

#heading("6. How to get involved")

The repository builds with `lake build` on a current Mathlib. By audience:

- *CTQW / quantum-walk mathematicians.* Discharge a deferred spectral clause
  --- the CNO timing in `Applications/SparseSearch.lean` is the highest-value
  single hole and would complete the search-advantage headline.
- *ML / systems people.* Wire catgrad (hellas.ai) as the frontend: emit
  `TransformerProgram`s from real models so the verified compiler runs on
  production attention patterns.
- *Quantum-hardware engineers.* Run `compiled_experiment_prediction` on IBM
  Heron; adversarially read the heavy-hex and Majorana-1 disassemblies.
- *Mathlib contributors.* The operator-system / quantum-graph and graphon-
  spectrum infrastructure are clean upstream candidates.

Each is self-contained, and each is a paper, a Mathlib PR, or a worked example
we will fold into the spine.

#v(0.5em)
#line(length: 100%, stroke: 0.5pt)
#v(0.3em)

#text(size: 9.5pt)[#emph[Proven anchors:]
`blockAttentionApply_eq_fullAttentionApply`,
`compile_denote_commutes`, `compiler_guarantee`,
`quantum_search_exact_amplitude`, `cellUniformPST_iff_quotientPST`,
`dataFlagQuotient_eigenvalues`, `sectorProjector_sum`,
`compiled_experiment_prediction` (structural).
#emph[Proven core (axiom-clean):] `hypercube_sparse_search_reduction`,
`buildable_lattice_structural_contrast`.
#emph[Stated, open clause:] `hypercube_search_optimal_timing` (timing),
`lattice_search_dimension_threshold` ($d>4$), `buildable_lattice_dynamical_contrast`,
`corrected_equitable_attention` (ε-approx), `bipartite_equitable_dirac_cone`
(cone local-linearity).
#emph[Open:] Conjecture 9.3, $infinity$-categorical towers, CNO timing,
`coinedWalk_continuum_dirac_conjecture`, Dirac
limit. #emph[Contact:] open an issue on the repository. Collaborators welcome at
any level.]
