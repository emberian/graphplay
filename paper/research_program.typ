#set document(title: "Graphplay Research Program: Companion Catalog")
#set page(margin: 1in)
#set text(size: 11pt)
#set par(justify: true)

#align(center)[
  #text(size: 17pt, weight: "bold")[Graphplay Research Program] \
  #v(0.25em)
  #text(size: 13pt, weight: "bold")[A Companion Catalog of Dowsing-Rod Theorems, Integrations, and Higher Towers] \
  #v(0.35em)
  #text(size: 11pt)[Companion to #emph[Graphplay: A Combinatorial Assembly Language for Quantum Primitives] (v3)] \
  #v(0.45em)
  #text(size: 9.5pt)[Graphplayers Crew --- Graphplay v3 companion]
]

#v(1em)

#heading("Foreword: A Research Program in an Assembly-Language Key")

The main paper presents Graphplay as a typed compiler from quantum-walk
primitives (PST, mixing, search, fractional revival) to host Hamiltonians,
built around a single structural primitive: the equitable partition of a
Hermitian weighted graph and its small finite quotient matrix as the
universal compiled object. The Lean 4 development of the five-tower spine
--- Set, SimpleGraph, WeightedGraph, operator algebra / coherent algebra,
graphon, categorical filtered colimit --- supports the three load-bearing
theorems at each tower: spectral subset, cell-uniform restriction, and
finite-dimensional quotient reduction.

What the main paper's research-program section (§9) compresses into a
one-page list, this companion expands into a working catalog of *open
theorems*. Eighteen further Lean modules (ten "dowsing-rod" files under
`Graphplay/Dowsing/`, eight "integration" files under
`Graphplay/Integrations/`) plus the two higher towers `Tower6.lean` and
`Tower7.lean` constitute a research program: each file fixes a precise
statement that the spine *would prove* if certain identified holes
(coherent-algebra commutativity, sheaf-of-$*$-algebras infrastructure,
$infinity$-categorical Mathlib library) were closed. The proofs are sorried;
the statements are not, and they typecheck against the rest of Graphplay.

The metaphor we use throughout is the *dowsing rod*. A dowsing-rod file
picks out a thesis-sized open problem, formulates it as a Lean `theorem` (or
`def : Prop`) against the existing spine, and includes worked examples
sufficient to convince the reader that the statement is the right one. It
is the dual of a "proof skeleton": rather than asserting "we have proved
this," each file asserts "this is what would have to be proved, and here
are the surfaces along which the spine would carry the proof." The
falsifiable Conjecture 9.3 (Bose--Mesner $eq.triple$ chiral $eq.triple$
graphon) is the flagship dowsing-rod result; the other nine are siblings,
each at a comparable level of definiteness.

The integration files extend the metaphor outward: each is a research-program
seed pointing to a neighboring field (TQFT, RMT, tensor networks, optimal
transport, Hodge theory, lattice gauge theory, mean-field control,
Weisfeiler--Leman refinement) where the spine applies and where, we
contend, the equitable-partition idiom is currently underexploited. They are
not proofs; they are *integration points*, identifying the precise places at
which Graphplay's primitives meet --- and, we believe, generate --- nontrivial
content in the receiving field.

We present each item below in 1--2 paragraphs. The intended reader is
familiar with the spine of the main paper and wants a fast survey of the
catalog --- enough to decide where to dig next.

#v(1em)

#heading("1. Dowsing-Rod Theorems (D1--D10)")

#emph[The ten files under `Graphplay/Dowsing/` each formulate a single
thesis-sized open theorem at the boundary of the spine. Statements are
complete; proofs are sorried.]

#heading(level: 2, "D1. ChiralBundlePST.lean --- Chiral PST on Graph Bundles")

The headline theorem of this file is a chiral generalization of the
Bachman--Tamon bundle PST machinery (arXiv:1108.0339) that simultaneously
contains, as the singleton-base case, the uniform-mixing speedup of
Levine--Mesapam--Mustico--Tamon--Tucker--Zhan on chirally-signed complete
graphs (arXiv:2605.04414). Concretely: a `ChiralBundle Q V` is a
`GraphBundle` together with a chiral signing on each template edge and an
intra-fiber signing on each fiber, satisfying Hermitian compatibility on
reversed edges. The result
`pst_iff_quotient_signed_pst` asserts that, when the bundle has regular
fibers and biregular couplings, cell-uniform PST on the chirally-signed
*total* graph is equivalent to PST on the chirally-signed *quotient* graph.
The proof goes through the characteristic-isometry intertwining
$S^* exp(-i tau A_"signed") S = exp(-i tau A_"quot,signed")$ (Bachman--Tamon
§2, extended chirally as in Levine et al. Lemma 2.1) plus the existing
`EquitablePartition.pst_lift`.

The file's substantive corollary is *contrapositive lifting*: ANY base graph
$Q$ whose vertex fibers carry the same $K_n^sigma$ signing inherits the
Levine et al. $pi/(3 sqrt(3))$ uniform-mixing speedup at the cell-uniform
level. Three concrete bundle families are spelled out: the chiral
Hamming-attached path (`chiralHammingBundle n m`), the chiral Heawood
template bundle (`chiralHeawoodBundle g n`), and a chiral bipartite bundle.
A "phase-equitable refinement" lemma states that any chiral signing induces
a (potentially finer) equitable partition by grouping vertices with the same
outgoing-phase profile --- the chiral analogue of Bachman--Tamon's "twin
partition." Three open questions close the file: chiral product PST,
sharpness of the $pi/(3 sqrt(3))$ time on $K_n^sigma$, and chiral PGST on
Heawood bundles.

#heading(level: 2, "D2. BundlePSTLift.lean --- Universal Bundle PST Lift")

This file gives the uniform iff statement
`pst_iff_quotient` for cell-uniform PST on the total graph of a
`GraphBundle` versus PST on its fiber quotient, and shows that it
*strictly subsumes* the three classical product PST preservation theorems of
Ge--Greenberg--Perez--Tamon (GGPT, arXiv:1009.1340). The Cartesian product,
lexicographic product (regular second factor), and weak / tensor product all
fall out as immediate corollaries. Beyond GGPT, the file states bundle-PST
forms of products *not* covered by the original GGPT paper: the strong
product $G xor.big H$, the conormal product, the disjunctive product, the
`TemplateJoin` construction with constant fiber size, and `colorCompletion`
of any coloring $V -> I$ over a complete template.

Two additional headline statements appear. The *stratified bundle lift*
(`stratified_pst_lift`) extends the iff to bundles whose fibers fail
regularity, by passing through a finer equitable partition adapted to extra
symmetry. The *Bachman--Tamon--Feder reduction*
(`cartesianProduct_quotient_naturality`) states that the Cartesian product
of quotients is itself a quotient of the Cartesian product: a categorical
naturality square between `total` and `quotient`. This is, in particular,
the Tower-5 ingredient that recurs in D9 below as a filtered-colimit
preservation statement.

#heading(level: 2, "D3. ChiralGraphon.lean --- Chiral Graphons and Tower-4 Chiral Mixing")

The Tower-4 graphon framework already permits complex-valued Hermitian
kernels, so chirality is implicit; what was missing in the codebase, before
this file, was the *interaction* of chirality with the graphon equitable
partition. The file defines: (i) the chirality predicate
`IsChiral W := mu times.circle mu (\{(x, y) : "Im"(W(x,y)) eq.not 0 \}) > 0`,
making the real/imaginary decomposition explicit; (ii) measurable chiral
signings `GraphonSigning Ω` as unimodular Hermitian-compatible measurable
kernels, with entrywise action `Graphon.signedBy : Graphon -> GraphonSigning -> Graphon`;
(iii) the graphon analogue of cell-cross-constant signings; (iv) the
*chiral quotient* with explicit phase formula for cell pairs; (v) a
gauge-theoretic interpretation in which cross-constant signings are flat
$U(1)$ connections on the cell-partition graph (this is the seed of I7
below).

The headline statement is `chiralGraphonMixing_iff_quotientChiralMixing`:
optimal cell-uniform chiral mixing on a graphon equitable partition is
determined by a chiral phasing of the finite quotient. This is the
Tower-4 quasi-infinite limit of Levine et al. Theorems 1--2. Two explicit
limit families are recorded: the constant-phase graphon $K_n^sigma -> "constantChiral"$
as $n -> infinity$, and the iterated-Hamming chiral $H(n, 4) ->
"iteratedHammingChiral"$. Three open theorems close the file, including a
conjectural Anantharaman--Sabri-style chiral connection in
Benjamini--Schramm limits.

#heading(level: 2, "D4. CoherentAlgebra.lean --- Tower 3 Commutative Equivalence")

The guiding folklore equivalence here --- apparently never written down
formally --- is: *an equitable partition of a graph $G$ on $V$ is the same
data as a commutative unital $*$-subalgebra of `Matrix V V ℂ` that contains
the adjacency matrix $G."adj"$ and is closed under the Schur (entrywise)
product*. The file formalizes both directions of this dictionary. A
`IsCoherent S` structure asserts that the submodule $S subset.eq "Matrix" V V CC$
is unital, $*$-closed, and closed under both matrix multiplication and the
Schur product. The headline statement
`equitablePartition_iff_coherentSubalgebraContaining` makes the equivalence
precise: equitable partitions of $G$ correspond bijectively to commutative
coherent subalgebras containing $G."adj"$.

A second contribution is the *Weisfeiler--Leman refinement chain* recast as
a chain `WLAlgebra G n : ℕ -> Submodule ℂ ("Matrix" V V CC)`, with the
monotonicity `WLAlgebra_mono`, the stabilization `WLAlgebra_stabilises`,
and the comparison `stableWL_le_orbitAlgebra` against the orbit algebra of
$"Aut"(G)$. Theorem `BMAlgebra_characterization` packages the Bose--Mesner
algebra of an association scheme as the maximally symmetric case of a
commutative coherent algebra. The file ends with a quantum-chromatic-number
bridge `quantumChromatic_le_chromatic` that is the entry point to D5.

#heading(level: 2, "D5. NonCommutativeCoherent.lean --- Tower 3 Non-Commutative Quantum Equitable Partitions")

D5 generalizes D4 to the operator-system / quantum-graph case (Duan--Severini--Winter
arXiv:1002.2514, Mancinska--Roberson arXiv:1903.11491). A `QuantumGraph` is
a unital $*$-closed subspace $S subset.eq M_n(CC)$. A
`QuantumEquitablePartition n S I` is a unital $*$-subalgebra
$A subset.eq M_n(CC)$ containing $S$, together with a system of cell
projectors $\{p_i\}_(i in I)$ summing to $1$, all lying in $A$ --- the
non-commutative analogue of the partition projector $Pi_P$. The
*non-commutative coherent algebra* is then the smallest unital
$*$-subalgebra containing $S$, equivalently the fixed point of
non-commutative WL refinement (statement
`WLFix_isCoherentAlgebra`).

The headline statement `QuantumEquitablePartition.pst_lift` says that PST
on the quantum quotient implies cell-uniform PST on $S$. The
quantum-chromatic-number characterization
`quantumChromatic_le_iff_quantumHom` (Mancinska--Roberson) appears, as
does the quantum Cayley graph generic-non-commutativity statement
`quantumCayley_nonCommutative_generic`. Concrete examples: non-commutative
$K_n$ (off-diagonal operator system), quantum Hamming graphs as tensor
powers, quantum Cayley graphs for non-abelian groups. The file closes with
three open directions, including the GNW chain
$chi_f lt.eq theta lt.eq chi_q lt.eq chi$ and quantum graphon limits.

#heading(level: 2, "D6. FractionalRevivalNC.lean --- Fractional Revival on Coherent Algebras and Graphons")

Chan--Coutinho--Tamon--Vinet--Zhan (arXiv:1907.04729) characterize
fractional revival on graphs whose adjacency matrix lies in the Bose--Mesner
algebra of an association scheme: this is the commutative Tower-3 case.
This file extends FR theory to three increasingly non-classical settings.
Tower 2: FR on a `WeightedGraph` via `IsFR G u v τ α β` (matrix
elements of $U(tau)$ equal $alpha$ at the diagonal $u$ and $beta$ at the
target $v$, everything else zero), with cell-uniform FR through equitable
partitions and the lifting theorem
`EquitablePartition.fr_lift`. Tower 3 non-commutative: FR between
"cell-uniform state" projectors of a quantum graph
(`Graphplay.QuantumGraph`), with spectral characterization
`bose_mesner_fr_iff` and the commutative-reduction theorem
`ncfr_commutative_reduction`. Tower 4 graphon: FR between bump-state classes
on a measure space and the limit theorem `Graphon.fr_limit` bridging
finite FR sequences to their graphon limits.

Three explicit families bring the development down to earth: FR on Cartesian
products of cycles (Tamon clique example), FR on Hamming $H(n, q)$ via
`hammingGraph_fr_iff`, and the *chiral $K_n^sigma$ fractional revival
conjecture* `chiralKn_fr_conjecture` --- the statement that the Levine
et al. signing of $K_n$ admits $(alpha, beta)$-FR between any two distinct
vertices for explicit $alpha(n), beta(n)$ that we conjecture extend the
$pi/(3 sqrt(3))$ uniform-mixing time.

#heading(level: 2, "D7. HypergraphPST.lean --- Three CTQW Models on Hypergraphs and the Doubly-Equitable Conjecture")

CTQW on hypergraphs is unsettled: unlike on graphs, no single canonical
Hamiltonian dominates. The file packages all three of the standard
candidates as `WeightedGraph V` constructions: the *clique-expansion
Laplacian* (replace each $k$-hyperedge with the complete graph $K_k$ on its
support); the *Hodge / incidence Laplacian* $L = B B^*$ formed from the
complex vertex-edge incidence matrix of `Graphplay/Relational.lean`; and the
*tensor / higher-order line walk* on the higher-order line graph whose
vertices are $k$-tuples in a common hyperedge. The corresponding PST
predicates `IsHypergraphPST_clique`, `IsHypergraphPST_hodge`,
`IsHypergraphPST_tensor` are lifted through `RelEquitablePartition`
quotients in parallel with `Graphplay/PST.lean`.

The headline conjecture is the *cross-model coincidence theorem*
`cross_model_coincidence`: a hypergraph admits PST simultaneously in all
three models if and only if its incidence relation satisfies a *doubly
equitable* cell-uniformity condition (a `IsDoublyEquitable` structure that
asks for equitability on both vertices and hyperedges). Concrete testable
families: Steiner triple systems (`steinerTripleHodgePST_conjecture`),
complete $k$-uniform hypergraphs (`completeKUniformPST_conjecture`), and
partition designs from finite geometries. The file also lifts the chiral
machinery: signed incidence, signed Hodge Laplacian, and
`chiral_pst_lift_hodge`. A `Hypergraphon` (Tower-4 hypergraph) and its
equitable partition close the file with `hypergraphon_pst_lift`.

#heading(level: 2, "D8. NoiseEquitable.lean --- Commutant Criterion and Caruso Noise-Assisted Speedup")

A8 (`Graphplay/Toolkit/Noise.lean`) introduces the `NoiseModel` and the
cell-uniform-symmetric preservation predicate at the statement level. D8
sharpens this. Q1 (preservation): we give a clean commutant-based criterion
--- every Lindblad jump operator $L_k$ must lie in the *commutant of the
partition algebra* --- and characterize the *universal* case (preserves
every equitable partition of every host) via
`isUniversallyEquitable_iff_central`: the noise generators must lie in the
center $ZZ(M_n(CC)) = CC dot 1$. Equivalently the only universally
equitable noise is depolarizing. Q2 (Caruso noise-assisted speedup): we
define a *breaking score* for a noise model as the $L^2$ distance of its
commutant from the projector algebra of $P$, and state the *Caruso
conjecture* `caruso_leading_order_speedup`: optimal noise-assisted speedup
occurs at a non-trivial breaking score, strictly between fully symmetric and
fully disruptive noise.

Three concrete models are analyzed for their breaking scores: depolarizing
(universally equitable, score zero), site dephasing (equitable iff cells
are vertex orbits, theorem `dephasing_cellUniformSymmetric_iff_orbit`), and
boundary dephasing (not equitable for marked-refined partitions, explicit
positive breaking score in `boundaryDephasing_breakingScore`). The file
closes with `chiral_PST_open_mirror` and `openSystem_bachmanTamon`, the
open-system analogues of the Bachman--Tamon closed PST quotient theorem,
plus `ghost_symmetry_open_analogue`, an open-system version of the
Bick--Sclosa ghost-of-symmetry phenomenon (arXiv:2110.13686).

#heading(level: 2, "D9. FilteredColimitPST.lean --- Generalized Xie--Tamon: PST and Search Over Filtered Colimits")

Xie--Tamon (arXiv:2301.07251, *No Infinite Tail Beats Optimal Spatial
Search*) prove that the continuous-time spatial-search algorithm on $K_n$
remains optimal under attachment of an infinite path $P_infinity$. The
*categorical* reading of this result: the family $(K_n + P_m)_(m gt.eq 0)$,
equipped with the distance-from-$K_n$ equitable partition, is a *filtered
diagram* in the partitioned weighted-graph category `WGraphP` (Tower 5,
`Graphplay/Categorical.lean`). The Quotient functor preserves filtered
colimits, and the PST predicate is continuous in operator norm; composing:
PST holds in the limit quotient iff it holds with consistent times on
every finite quotient.

The file states the general
`ConsistentPartitionSequence.pst_inherited` theorem and exhibits a *concrete
family table* with seven entries: $K_n + "path"$ (Xie--Tamon themselves);
$K_n + "tree"$ (Bernard--Tamon--Vinet--Xie tail-tree, arXiv:2211.14704);
$K_n + ZZ^d$ multi-dimensional lattice; $K_n + "level-growth"$ geometric
clique-shell expansion; Hamming$(n, q)$-plus-path; surface-Heawood-plus-path
(`surfaceHeawood_plus_path_quotient_stabilizes`); and $K_n times "path"$
Cartesian. Three sharpenings: a *cofiltered* dual for infinite-state quantum
Markov chains (`InversePartitionSequence.pst_lifted`); a *quantitative
convergence-rate* refinement `ConsistentPartitionSequence.pst_rate_inheritance`;
and three *failure-mode* conjectures (`failure_mode_unbounded_spectrum`,
`failure_mode_continuous_spectrum`, `failure_mode_incoherent_times`)
identifying obstructions to the limit lift. A *chiral* filtered colimit
statement `ChiralConsistentPartitionSequence.pst_inherited` combines D1 with
the present setup.

#heading(level: 2, "D10. Conjecture93.lean --- The Flagship Falsifiable Conjecture")

D10 is the flagship dowsing-rod result and we treat it in its own section
below (see §3). In one sentence: a consistent sequence of finite weighted
graphs $(G_n, P_n)$ admits a graphon quasi-infinite limit and a
cross-constant chiral signing speedup on the same partition if and only if
the Bose--Mesner algebra of the family eventually coincides with the
partition-projector algebra. This is *the first conjecture in the program
that ties together Tower 2 (chiral), Tower 3 (Bose--Mesner / association
schemes), and Tower 4 (graphons) in one falsifiable iff*.

#v(0.5em)

#heading("2. Cross-Disciplinary Integrations (I1--I8)")

#emph[Each file under `Graphplay/Integrations/` is a research-program seed
pointing to a neighboring field where the spine applies and where the
equitable-partition idiom is, we contend, currently underexploited.]

#heading(level: 2, "I1. TQFT.lean --- Anyons, Modular Tensor Categories, and Surface Envelopes")

The guiding observation: the Heawood envelope $K_(h(g))$ of a graph
embedded on a closed surface of genus $g$ is a *discrete shadow* of the
underlying surface. An anyonic system on that surface has Hilbert space
organized as a representation of the modular tensor category (MTC) of the
surface, and that representation decomposes into *topological sectors*. The
file formalizes a `ModularData A` structure (Kitaev 2006, Appendix E)
carrying the $S$-matrix, $T$-matrix, twists, and quantum dimensions, with
the Verlinde formula `verlinde` and modular relations as sorried theorems.
The headline result `anyonic_equitable_partition` says: when a surface
graph carries an anyonic decoration, the corresponding sector decomposition
*is* an equitable partition in the sense of `Graphplay/Equitable.lean`.
Thus the Tower-3 quotient spine #emph[is] the categorical sector decomposition,
viewed combinatorially.

Three downstream results follow. `surface_pst_isotopy_invariant` makes PST
on a surface graph isotopy-invariant (a topological criterion on the
quotient). `levinWen_groundstate_eq_cellUniform` identifies the
ground-state subspace of a Levin--Wen string-net Hamiltonian on a trivalent
graph with the cell-uniform subspace of an explicit equitable partition.
`braid_gate_realizable` shows that braid gates in topological quantum
computation lift through the cell-uniform subspace, opening a path to
*braid-quotient compilation* of topological-quantum-computation primitives.
The Heawood--anyon match `openQ1_HeawoodMatchesAnyons` is left open: for
each genus $g$ the Heawood envelope predicts $h(g)$ vertices and the
Reshetikhin--Turaev TQFT predicts a finite anyon count.

#heading(level: 2, "I2. RMT.lean --- Wigner Plus Equitable: Thermalizing-Yet-PST Hosts")

The integration unexplored in the literature: classical random matrix theory
studies the random bulk spectrum of $n times n$ Hermitian matrices and
identifies universal limits (Wigner's semicircle, free convolutions);
Graphplay's `Graphon.op_restrict_eq_quotient` says that, *restricted to the
cell-uniform subspace*, the spectrum of a graphon operator is exactly the
deterministic spectrum of the finite quotient. Putting these together,
a `RandomGraphon` `R` almost surely admitting a fixed equitable partition
(captured by the `AlmostSurelyEquitable` structure) decomposes its spectrum
as
$ sigma(R."op") = underbrace(sigma(P."quotient"), "deterministic")
  union.sq underbrace(sigma(R."op"|"cellUniform"^perp), "random Wigner bulk"). $
The headline `thermalizing_yet_PST_host` then declares: there exist random
graphons whose orthogonal-to-quotient spectrum is GUE-distributed (hence
thermalizing in the QECEC / ETH sense) while the cell-uniform sector
remains deterministically PST-active --- an explicitly engineered hybrid
quantum host.

The technical scaffolding includes `wignerGraphon_spectrum_semicircle`
(graphon analogue of Wigner's law), `wignerLimit_free_of_equitable` (free
convolution of the random part with the deterministic quotient), and
`graphonOp_is_free_semicircular` (the cell-uniform subspace is a free
sub-W$*$-probability space of the ambient W$*$-probability space). Three
open directions: WL-RMT universality
(`open_problem_WL_RMT_universality`), a free-cumulant expansion of the
quotient spectrum, and the quaternionic / GSE Tower-2 extension
(`open_problem_quaternionic_graphplay`), the largest stated obstruction in
the program.

#heading(level: 2, "I3. TensorNetworks.lean --- MERA Exact iff Iterated Equitable; Holographic Codes")

A coarse-graining layer in a Multi-scale Entanglement Renormalization
Ansatz (MERA) of Vidal is *literally an equitable-partition cell map*. The
headline result `mera_exact_iff_equitable` makes this precise: a MERA is
*exact* for a local Hamiltonian $H$ iff each of its coarse-graining maps
$c_n : V_n -> V_(n+1)$ is the cell map of an equitable partition $P_n$ of
the effective Hamiltonian $H_n$ at level $n$. The disentangling unitaries
handle the part of $H_n$ that is *not* equitable; when there is no such
part, they reduce to identities and the MERA captures the exact ground
state. In categorical terms (matching `Graphplay.Categorical`), a MERA
tower is a sequence of objects of `WGraphP` with morphisms going *down*
under `Quotient`, i.e. a cochain whose bonding maps are the
`Quotient.map` images of partition-respecting morphisms.

Downstream: `holographic_code_equitable` identifies holographic
(Pastawski--Yoshida--Harlow--Preskill) quantum error-correcting codes as
equitable bundles over bulk-boundary skeletons. `equitable_infinite_mera_has_limit`
states the Tower-4 quasi-infinite limit for MERA towers --- an explicit
filtered colimit instance. `peps_exact_iff_two_d_equitable` extends to PEPS
and `peps_on_surface` to surface PEPS. The compiler-facing
`tensor_network_compiler` statement asserts that the MERA-of-an-equitable-host
correspondence is *constructive*: given an equitable partition and its
finite quotient, an exact MERA can be synthesized. Three open conjectures
include `open_conjecture_gapped_equitable_tower` (gapped local Hamiltonians
have MERA-exact equitable towers) and `open_conjecture_graphon_mera_limit`
(the graphon limit of a MERA tower is the graphon-MERA of `Graphon/Limit.lean`).

#heading(level: 2, "I4. OptimalTransport.lean --- Sinkhorn Respects Equitable; OT as a Design Primitive")

A nonnegative real symmetric graphon is *almost* a transport plan: the only
gap is marginal-correction, which Sinkhorn--Knopp / Cuturi address by
row/column rescaling or entropic regularization. The integration bridge:
equitable partitions of a graphon are *coarsened transport plans* (a finite
quotient matrix $B : I times I -> RR$ plus cell-uniform internal
structure). The headline results
`sinkhorn_preserves_equitable` and `sinkhorn_quotient_commutes` assert that
Sinkhorn iterates preserve the cell-uniform subspace when the source is an
equitable-partition graphon, and that the quotient gives a lower bound on
the rate (`sinkhorn_rate_quotient_bound`). The Wasserstein-distance-via-quotient
formula `wassersteinDistance_eq_quotient` says that, on cell-uniform
support, the graphon-level $W_2$ reduces to a finite Wasserstein on the
quotient measure.

The toolkit-facing claim is the *mixing-time $arrow.l.r$ transport-rate*
dictionary `mixing_sinkhorn_conjecture` and the constructive
`quantum_sampler_existence`: given a target transport plan with an
equitable structure, there exists a CTQW Hamiltonian whose cell-uniform
evolution is the corresponding Sinkhorn iterate. This makes OT a *design
primitive* for quantum sampler synthesis: the compiler emits, from a
prescribed transport plan, a host CTQW whose uniform-mixing dynamics
realizes the plan up to the $log n slash n$ entropic-mixing factor of the
conjecture.

#heading(level: 2, "I5. MeanFieldGames.lean --- Gao--Caines LQR as the Classical-Control Analog")

Three threads share a mathematical primitive: graphon LQR control
(Gao--Caines arXiv:2004.00677); mean-field control (Huang--Caines--Malhamé,
Lasry--Lions); and graphon equitable partitions (Graphplay Tower 4). The
underexploited observation: *the Gao--Caines invariant subspace is, in the
most common applicable cases, exactly the cell-uniform subspace of an
equitable graphon partition*. Their "Assumption (A5)" rests, in our
vocabulary, on `GraphonEquitablePartition`. Once this identification is
made, the Gao--Caines decomposition theorem reads as a *quotient LQR
theorem*: the finite-dimensional quotient LQR on the cell index $I$ is the
entire content of the large-network LQR. The file states this as
`equitable_LQR_reduction` with mild-solution existence and uniqueness
(`mildSolution_exists_unique`) and `optimal_control_exists`.

The quantum-side translation: replacing LQR by Schrödinger dynamics
(`schrodinger_cellUniform_invariant`) or Lindblad evolution
(`lindblad_cellUniform_invariant`) keeps the same reduction. The
`brachistochrone_reduction` statement asserts that the quantum
brachistochrone problem on a host with equitable structure reduces to
brachistochrone on the quotient --- the entry point to a verified
*pulse-synthesis* path for symmetric quantum chips. Three open directions:
non-stationary equitable LQR, stochastic graphon equitable evolution, and
chiral mean-field-game speedup (`chiral_MFG_speedup_open`).

#heading(level: 2, "I6. Hodge.lean --- Equitable Hodge Decomposition and Harmonic Qubit Encoding")

The combinatorial Hodge decomposition of Eckmann (1944/45) and the modern
treatment of Lim (*Hodge Laplacians on graphs*, SIREV 2020) says that the
cochain complex $C^0 -> C^1 -> dots.h.c -> C^k$ of a simplicial complex
decomposes any cochain into exact, coexact, and harmonic parts. The file
sets up the `SimplicialComplex` and `Cochain` types, defines the
`hodgeLaplacian` and the (sorried) `hodgeDecomp` and
`harmonic_iso_cohomology` statements, and then introduces the file's
contribution: the `EquitableCochain` structure --- an equitable partition
of the cochain complex respecting the coboundary --- and the
`hodgeQuotient` theorem asserting that the Hodge decomposition descends to
the quotient simplicial complex of an equitable cochain.

Three downstream theorems wire this into the spine and beyond.
`persistent_hodge_equitable` couples the equitable Hodge decomposition with
persistent homology / TDA (Carlsson 2009): persistence diagrams of an
equitable filtration are determined by the quotient filtration, opening
*equitable speedup for TDA*. `harmonic_encoding_preserved` encodes a
logical qubit in the harmonic subspace of an equitable cochain, with PST
realized as a Hodge isomorphism (`hodgePST_lift`); this is a topological /
homological avatar of cell-uniform PST. The harmonic-encoded qubit is
intrinsically robust to noise restricted to the exact/coexact components,
a complementary protection mechanism to the operator-algebraic noise
analysis of D8.

#heading(level: 2, "I7. LatticeGauge.lean --- Chiral = U(1) Lattice Gauge; Cross-Constant = Flat; Hofstadter Quantization")

The headline observations of this file are tight and verifiable. A
`ChiralSigning V` is *exactly* a $U(1)$ lattice gauge field on the complete
digraph on $V$: the equivalence `chiral_iff_u1Gauge` is constructive
(`U1GaugeField.toChiralSigning` and `ChiralSigning.toU1GaugeField`). The
gauge field's *Wilson loop* gives its curvature, and the
`ChiralSigning.CrossConstant` predicate of `Graphplay.Chiral` is equivalent
to *cell-flatness* of the gauge field --- vanishing curvature on every loop
inside a single equitable cell. The cross-cell curvature depends only on
the quotient cycle. This is the lattice gauge avatar of the chiral graphon
gauge-theoretic interpretation of D3.

The two flagship consequences are the Hofstadter family results:
`hofstadter_flux_quantization` says that when the Wilson loop around the
bundle's monodromy cycle is the $q$-th root of unity $e^(i 2 pi p slash q)$,
the cell-uniform spectrum of the bundle's adjacency lifts in *p/q quantized
chunks*; this is the Hofstadter butterfly analog for graph bundles. The
companion `hofstadter_chip_family` exhibits a family of equitable graph
bundles whose flux quantization produces a constructive target spectrum.
`equitable_hardware_design` then states the engineering corollary:
*equitable hardware design corresponds to flat connection chip design*,
realized in superconducting flux-qubit chips and synthetic-flux photonic
lattices. The non-abelian extension to $U(N)$ matrix-valued signings is
`matrix_gauge_field_preserves_equitable`, opening Yang--Mills-style lattice
gauge integration with the spine.

#heading(level: 2, "I8. WLRefinement.lean --- Equitable = WL Stable; PST = Phantom Symmetry")

The Weisfeiler--Leman (WL) refinement chain $"WL"_1 prec.eq "WL"_2 prec.eq
"WL"_3 prec.eq dots.h.c$ is the master algorithmic theory of graph
isomorphism. This file threads it through Graphplay's tower picture:
1-WL stable equals the orbit quotient by the coherent algebra (Tower 3
commutative dictionary, theorem `oneWL_stable_is_coarsest_equitable`);
2-WL generates the full coherent algebra
(`coherentAlgebra_eq_2WL_span`); $k$-WL gives higher-arity coherent
configurations (Cai--Fürer--Immerman, with the strict-hierarchy theorem
`CFI_strict_hierarchy`); WL on graphons converges in the cut metric to the
graphon's intrinsic equitable structure
(`graphonWL_limit_conjecture`); the quantum WL chain
`QuantumWLStable` reaches Mancinska--Roberson's quantum-isomorphism graph
algebra (`MancinskaRoberson_qIsomorphism`).

The two engineering corollaries are sharp. The *design budget*
`design_budget`: the WL-stable partition is the *finest* equitable
partition of $G$, so any equitable-partition-based PST scheme has at most
$\#"WL"_infinity(G)$ cells --- a hard upper bound on the quotient
dimensionality of any PST protocol. The *phantom-symmetry* phenomenon
`pst_requires_WL_and_eigenSupport` together with `phantom_symmetries_exist`
asserts that PST is *more* than WL: there are non-isomorphic but
WL-indistinguishable graphs that disagree on PST, witnessing that PST sees
information beyond combinatorial colour refinement. Babai's quasipolynomial
GI bound (`Babai_GI_quasipolynomial`) gives the complexity-theoretic hook
`PST_design_sub_WL`: equitable-PST design is a *sub-GI* problem.

#v(0.5em)

#heading("3. Higher Towers (6--7)")

#heading(level: 2, "Tower 6 --- Operator-Algebra-Valued Sheaves")

`Graphplay/Tower6.lean` lifts the Tower-3 quantum-graph picture to a
*sheaf of unital $*$-algebras over a topological base space $X$*, together
with a distinguished global adjacency section. Heuristically: a graph whose
adjacency varies continuously as a parameter sweeps over $X$. The carrier
objects are: a `SheafGraph X` (a sheaf of $*$-algebras plus a global
adjacency); a `SheafEquitablePartition` (an open cover trivializing the
sheaf into cell algebras, together with a partition of the global adjacency
respecting the cover); the *quotient sheaf* on the nerve of the cover; and
the sheaf-level lift theorem `sheaf_spectral_lift`. The categorical
global-section functor $Gamma(X, dot)$ preserves filtered colimits
(`globalSection_preservesFilteredColimits`), so Tower 5's quasi-infinite
limit lifts to the sheaf level.

Three lower towers are *recovered* as special cases. `tower3_recovery`: the
constant sheaf on a one-point space yields a single quantum graph (Tower 3).
`tower4_recovery`: the sheaf of $L^2(Omega, mu)$-kernel-fibers over a
measure space yields a graphon (Tower 4). `tower5_recovery`: the categorical
projection lands in the partitioned weighted-graph category (Tower 5). The
hardware-facing payoff is `Hardware.driftRobust` and
`robust_pst_neighbourhood`: a PST protocol that holds on an open
neighborhood of a parameter $x_0$ is robust under continuous hardware drift
in $x_0$, which is the operator-algebraic version of the noise-perturbation
guarantee. `adiabatic_is_section` recasts the adiabatic theorem as a section
of the sheaf graph.

#heading(level: 2, "Tower 7 --- $infinity$-Categorical and Bicategorical Truncation")

`Graphplay/Tower7.lean` is the highest abstraction tier in the program. The
five-tower spine is recast in the language of stable $infinity$-categories,
in which the strict equalities of Tower 3 (idempotent partition projectors)
are replaced by *coherent homotopies*. PST becomes an *equivalence in the
unitary $infinity$-groupoid* --- PST "up to phase" upgrades to an honest
isomorphism in the homotopy category, with phase data living as 2-morphisms.
Mathlib does not yet carry a complete quasicategory library; the file
therefore commits its content to the bicategory / $(2, 1)$-category level
(`Mathlib.CategoryTheory.Bicategory.Basic`), where the statements actually
typecheck. The `InfinityCategory` and `StableInfinityCategory` data are
opaque placeholders; the bicategorical content is concrete.

The headline statements are: `infinity_pst_lift` (an infinity-categorical
PST lift theorem); `bicategorical_lift` (the bicategorical truncation that
*is* expressible in current Mathlib); `coherent_quasi_infinite_limit` (the
filtered-colimit preservation theorem from Tower 5, lifted to the
$infinity$-coherent setting); `pst_as_Ext0` (PST as a derived $"Ext"^0$
computation in a derived Hermitian category); and `mtc_correspondence` (a
recasting of modular tensor categories as $(infinity, 1)$-Tower-7 objects,
connecting to I1 above). The flagship corollary is
`topological_invariance_corollary`: under the topological-invariance
conjecture `TopologicalInvarianceConjecture` (sorried), the
$infinity$-categorical PST predicate depends *only on the homotopy type of
the base*, not on the underlying graph. The file is honest about its limit:
*almost everything is sorried, because the supporting Mathlib library does
not yet exist*.

#v(0.5em)

#heading("4. The Flagship Conjecture 9.3")

#heading(level: 2, "Statement")

Let $cal(S) = (G_n, P_n)$ be a consistent sequence of finite weighted
graphs with equitable partitions of fixed cell index type $I$ and
consistent embeddings $iota_n : V_n arrow.r.hook V_(n+1)$ respecting cell
labels (a `ConsistentPartitionSequence I` in
`Graphplay/Graphon/Limit.lean`). Define:

- $"admitsGraphonLimit"(cal(S))$: there exists a graphon $W_infinity$ on
  $(Omega, mu)$ with an equitable partition $P_infinity$ of the same index
  type, such that the finite quotient matrices $cal(S)."quotient"(n)$
  converge to $P_infinity."quotient"$.

- $"admitsChiralSpeedupOnPartition"(cal(S))$: there exists a sequence
  $\{s_n\}$ of nontrivial chiral signings, each `CrossConstant` on
  $cal(S)."cells"(n)$, consistent under the embeddings (phases pull back),
  whose signed quotient exhibits a strictly faster cell-uniform mixing /
  PST time than the unsigned quotient.

- $"eventuallyAlgebraCoincidence"(cal(S))$: there exists $N$ such that for
  every $n gt.eq N$, the smallest coherent algebra containing
  $(G_n)."adj"$ equals the partition-projector algebra of $cal(S)."cells"(n)$.

The flagship conjecture, in its *weak* (cross-constant) form, is the iff:

#align(center)[
  $"admitsGraphonLimit"(cal(S))  and  "admitsChiralSpeedupOnPartition"(cal(S))
   <==> "eventuallyAlgebraCoincidence"(cal(S))$.
]

The Lean statement is `Conjecture93_weak` in `Graphplay/Dowsing/Conjecture93.lean`,
decomposed into the forward direction `conjecture93_weak_forward` (algebra
coincidence implies both halves) and the reverse direction
`conjecture93_weak_reverse` (both halves imply algebra coincidence). The
*strong* form `Conjecture93_strong` replaces the cross-constant signing
constraint by an arbitrary unitary signing; this version we conjecture is
*false*, with the candidate counterexample described below.

#heading(level: 2, "Why It Is Interesting")

This is the *first conjecture in the program that ties together Tower 2
(chiral), Tower 3 (Bose--Mesner / association schemes), and Tower 4
(graphons) in one falsifiable iff*. The forward direction says that a
graphon-limit family that also admits a chiral speedup is *rigid enough* to
behave like an association scheme: it pins down the precise sense in which
the Levine et al. (arXiv:2605.04414) chiral speedup is more than an
arbitrary unitary perturbation. The reverse direction is the
association-scheme statement: a family that is uniformly an association
scheme automatically admits both a graphon limit (the natural step-graphon
of the scheme classes) and a chiral speedup (any cross-constant signing on
the quotient).

The conjecture is consistent with --- and strictly strengthens --- the
fractional-revival-iff-Bose-Mesner picture of Chan--Coutinho--Tamon--Vinet--Zhan
(arXiv:1907.04729). If true, it gives a clean operational characterization
of *which families are "scheme-like" in the limit*: exactly those for which
the Bose--Mesner algebra is generated by partition projectors.

#heading(level: 2, "Worked Examples (Six Test Families)")

`Graphplay/Dowsing/Conjecture93.lean` records six families covering the
expected positive and negative cells of the truth table. We summarize each:

#emph[4.1 $K_n^sigma$ with constant phase (both halves hold).] Trivial
single-cell partition; Bose--Mesner algebra $= CC dot I + CC dot J$ equals
the partition-projector algebra. The Levine et al. $K_4$ unitary signing is
cross-constant on the unique cell pair.

#emph[4.2 Hamming $H(n, q)$ with distance partition (both halves hold).]
Algebra coincidence exact on every class. Any nontrivial phase on a single
distance class gives a cross-constant speedup signing.

#emph[4.3 $K_n + "path"_n$ Xie--Tamon family (both halves false).] Graphon
limit exists by explicit Xie--Tamon construction. However, the Bose--Mesner
algebra of $K_n + P_n$ strictly contains the partition-projector algebra:
the tridiagonal path tail has algebra dimension $n + 1$, while the
cell-pair-constant algebra on the distance partition has lower dimension.
The conjecture predicts no chiral speedup on this partition, and indeed
every cross-constant signing acts trivially or breaks the partition. *The
cleanest both-sides-false witness, and the family that motivated the
conjecture.*

#emph[4.4 $K_(n, n, n, n)$ four-color completion (both halves hold).]
Color partition; rank-2 Bose--Mesner algebra equals the projector algebra;
arbitrary quotient phases descend.

#emph[4.5 Heawood envelope $g -> infinity$ (both halves hold trivially).]
$K_(H(g))$ with single-cell partition reduces to $K_n$.

#emph[4.6 Cayley$(S_n)$ by transpositions (both halves false).] Conjugacy
partition. The Cayley Bose--Mesner contains the full group algebra
$CC[S_n]$ of dimension $n!$, while the projector algebra has dimension
$p(n)^2$. For $n gt.eq 5$ these differ. Any nontrivial cross-constant
signing on conjugacy classes is either trivial or breaks the partition.

#heading(level: 2, "Best Guess About Truth")

#emph[The weak conjecture is probably true.] Three reasons:
*(i)* No known explicit counterexample: every family checked falls into the
$"(LHS true, RHS true)"$ or $"(LHS false, RHS false)"$ cells; the impossible
$"(LHS true, RHS false)"$ case is unfilled.
*(ii)* Structural reason for the forward direction: if $(G_n, P_n)$ admits
a chiral speedup on the partition, then by `chiral_mixing_optimization` the
speedup is governed by a chiral phasing of the quotient, living in the
partition-projector algebra. Combined with graphon-limit commutativity
(limit operator commutes with cell projection), this should force algebra
coincidence in the limit.
*(iii)* 1907.04729 precedent: fractional revival on graphs from association
schemes (the canonical "both halves hold" case) is exactly where the
conjecture is known to hold by the literature.

#emph[The strong conjecture is probably false.] The cleanest candidate
counterexample uses a *non-cross-constant* unitary signing on
$K_n + "path"_n$ that introduces a phase-equitable refinement of the
distance partition (cf. the `signedBy_phaseRefined_equitable` lemma of D1).
Such a signing can produce a strictly faster cell-uniform mixing time
without making the underlying algebra match the projector algebra. The
explicit construction is open; the locus is identified.

#heading(level: 2, "Next Steps")

To prove (weak): discharge `tower3_equitable_partition` (Lemma 2 of
1907.04729) to characterize `partitionProjectorAlgebra` as
$\{M : Pi_P M = M Pi_P  and  Pi_P M Pi_P = M\}$; prove
`Bose-Mesner.isCoherentAlgebra` and the commutativity lemma; then run the
forward direction through `chiral_mixing_optimization` intertwining and the
reverse direction through graphon convergence.

To refute (weak): construct a partition sequence whose Bose--Mesner is
strictly larger than the partition-projector algebra at every stage, but
for which some cross-constant chiral signing still produces a strict
cell-uniform mixing improvement. The likeliest hunting ground:
*non-vertex-transitive graphs with non-symmetric distance distributions*
--- distance-regular-but-not-distance-transitive bipartite double covers of
non-self-paired association schemes.

To refute (strong): take any both-sides-false family and search for a
unitary signing that breaks `CrossConstant` but still descends through a
phase-refined partition. The chiral half becomes true under the strong
definition while RHS stays false --- a strong-version counterexample.

The concrete first computation we recommend is the Bose--Mesner algebra
dimension of $K_n + P_n$ vs its distance-projector algebra dimension, in
Lean, for $n = 3, 4, 5$. If the dimensions differ as predicted, that nails
down family 4.3 as a both-sides-false instance, providing the first
nontrivial confirmation of the conjecture.

#v(0.5em)

#heading("5. Open Boundary: What Is Not Yet Formalized")

The program has identified *open boundary* obstructions where the spine
predicts content but the supporting Mathlib (or, in some cases, mathematical)
infrastructure does not yet support the proof. We list the three largest.

#emph[Quaternionic / GSE Tower 2.] The Tower-2 weighted-graph layer uses
complex Hermitian adjacencies. The quaternionic / symplectic analogue --- a
Tower-2 layer over $HH$ with self-conjugate adjacency --- would extend
chiral signings to the Gaussian Symplectic Ensemble (GSE) and connect to
the I2 RMT integration via `gse_quaternionic_graphon_open`. The blocker is
not conceptual but engineering: Mathlib does not currently carry
quaternionic matrix infrastructure at the level of completeness of the
complex case. The statement `open_problem_quaternionic_graphplay` flags the
right type to define and the right theorems to port, but the proofs depend
on a Mathlib quaternionic-linear-algebra library that does not exist.

#emph[$infinity$-categorical Mathlib blockage.] Tower 7 lives at the
bicategorical / $(2,1)$-truncation precisely because Lean+Mathlib does not
yet support quasicategories or stable $infinity$-categories. The
$infinity$-categorical PST lift `infinity_pst_lift` and the derived
$"Ext"^0$ formulation `pst_as_Ext0` are recorded as `Prop`s about
hypothetical structures with `sorry`-ed existence, awaiting (i) a Mathlib
quasicategory library, (ii) a derived-category framework, and (iii) a
$*$-enriched stable $infinity$-category to host the unitary $infinity$-groupoid.
The bicategorical truncation `bicategorical_lift` is the highest layer that
typechecks today.

#emph[Sheaf-of-$*$-algebras infrastructure.] Tower 6 needs a category
`UStarAlgCat` of unital $*$-algebras over $CC$, ideally the Mathlib bundled
`AlgebraCat ℂ` carrying a `StarRing` instance naturally. The Mathlib
`AlgebraCat ℂ` bundle is not currently star-equipped, forcing the
`Graphplay.Tower6` file to maintain its own bundle. The
`SheafGraph` and `SheafEquitablePartition` machinery is fully written; the
existence-of-cell-uniform-stalks proofs depend on the Mathlib bundling that
is being deferred.

Lesser open boundaries identified throughout the program: graphops
(Backhausz--Szegedy generalization of graphons by removing the $L^2$
symmetric-kernel assumption; the quotient spine survives when the operator
commutes with the projection); open-system Lindbladian extensions of the
Bachman--Tamon quotient theorem (D8 `openSystem_bachmanTamon`); the
non-commutative coherent-algebra GNW chain
$chi_f lt.eq theta lt.eq chi_q lt.eq chi$ (D5
`OpenDirection.GNW_chain`); and time-dependent / non-stationary equitable
partitions (I5 `nonstationary_equitable_LQR_open`).

#v(0.5em)

#heading("6. Reading Guide")

For readers wanting to navigate the codebase, we map content to file
locations.

#emph[Spine (already in main paper).]
`Graphplay/Weighted.lean`, `Graphplay/Equitable.lean`,
`Graphplay/Spectral.lean`, `Graphplay/PST.lean`, `Graphplay/Mixing.lean`,
`Graphplay/Search.lean`, `Graphplay/QuantumGraph.lean`,
`Graphplay/Chiral.lean`, `Graphplay/Bundle.lean`,
`Graphplay/Categorical.lean`, `Graphplay/Graphon.lean` and the
`Graphplay/Graphon/*` files.

#emph[Dowsing-rod (this companion §1).]
- `Graphplay/Dowsing/ChiralBundlePST.lean` --- D1
- `Graphplay/Dowsing/BundlePSTLift.lean` --- D2
- `Graphplay/Dowsing/ChiralGraphon.lean` --- D3
- `Graphplay/Dowsing/CoherentAlgebra.lean` --- D4
- `Graphplay/Dowsing/NonCommutativeCoherent.lean` --- D5
- `Graphplay/Dowsing/FractionalRevivalNC.lean` --- D6
- `Graphplay/Dowsing/HypergraphPST.lean` --- D7
- `Graphplay/Dowsing/NoiseEquitable.lean` --- D8
- `Graphplay/Dowsing/FilteredColimitPST.lean` --- D9
- `Graphplay/Dowsing/Conjecture93.lean` --- D10 and §4 above; see also
  `paper/conjecture93_notes.md` for the detailed worked-example notebook.

#emph[Integrations (this companion §2).]
- `Graphplay/Integrations/TQFT.lean` --- I1
- `Graphplay/Integrations/RMT.lean` --- I2
- `Graphplay/Integrations/TensorNetworks.lean` --- I3
- `Graphplay/Integrations/OptimalTransport.lean` --- I4
- `Graphplay/Integrations/MeanFieldGames.lean` --- I5
- `Graphplay/Integrations/Hodge.lean` --- I6
- `Graphplay/Integrations/LatticeGauge.lean` --- I7
- `Graphplay/Integrations/WLRefinement.lean` --- I8

#emph[Higher towers (this companion §3).]
- `Graphplay/Tower6.lean` --- sheaves of $*$-algebras over a topological
  base; recovers Towers 3, 4, 5 as point-base, measure-base, and
  global-sections cases.
- `Graphplay/Tower7.lean` --- $infinity$-categorical / bicategorical
  truncation; the topological-invariance corollary.

#emph[Conjecture 9.3 apparatus.]
`Graphplay/Dowsing/Conjecture93.lean` carries the full statement-level
infrastructure (`Conjecture93_weak`, `Conjecture93_strong`, the forward and
reverse implications, the six test families, the sufficient conditions, the
failure modes, the chiral / strong distinction). The discursive notes are
in `paper/conjecture93_notes.md`. The status table is summarized in
`paper/quasi_infinite_adjoint_v3.typ` §9.

#emph[Cross-references.]
Spine theorems consumed by this companion include
`EquitablePartition.pst_lift` (Bachman--Tamon),
`Graphon.op_restrict_eq_quotient` (Tower 4 spectral lift),
`Quotient.preservesFilteredColimits` (Tower 5 universal Xie--Tamon),
`Chiral.signedBy_preserves_equitable` (Tower 2 chiral lift), and
`coherentAlgebra` and `BoseMesner` (Tower 3 algebras).

#v(1em)

#emph[Everything below the spine is, intentionally, an unfinished research
program. The companion's purpose is to make precise both what would be
gained and what would have to be proved.]
