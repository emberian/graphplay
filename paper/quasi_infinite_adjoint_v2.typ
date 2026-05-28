#set document(title: "Equitable Quotients Across Five Towers")
#set page(margin: 1in)
#set text(size: 11pt)
#set par(justify: true)

#align(center)[
  #text(size: 17pt, weight: "bold")[Equitable Quotients Across Five Towers] \
  #v(0.35em)
  #text(size: 12pt)[A Lean-Verified Spine for Quantum-Walk Search and Transfer, \
  with a Graphon Quasi-Infinite Limit] \
  #v(0.25em)
  #text(size: 9.5pt)[Anti Mathematics Online Research Crew; Graphplay v2 draft]
]

#v(0.6em)

#heading("Abstract")

We organize a body of continuous-time quantum-walk results --- perfect state
transfer, uniform mixing, spatial search --- around a single structural spine:
an equitable partition of a Hermitian weighted graph, with its small
finite quotient matrix as the universal "small object". The spine ascends a
five-tower hierarchy: sets, simple graphs, Hermitian weighted graphs (which
includes chiral and magnetic graphs), operator algebras and quantum graphs,
graphons, and finally a categorical framing in which the Quotient functor
preserves filtered colimits.

The headline novelty is at Tower 4: we lift the Bachman--Fredette--Fuller--
Landry--Opperman--Tamon--Tollefson theorem on perfect state transfer on
quotient graphs to the graphon limit. Together with a categorical
filtered-colimit-preservation theorem this gives a clean "quasi-infinite limit
theorem": a sequence of finite quantum-walk problems with bounded equitable
quotients has its search/transfer behavior controlled by a single graphon
quotient. The Xie--Tamon infinite-tail result is recovered as a one-line
corollary.

We also recover the four-color-completion compiler of our earlier note as a
single corner of a unifying `GraphBundle` construction, and we observe that
chiral signing optimizations factor through the quotient: searching for a
mixing-time speedup reduces to a finite signed problem on the template. The
Lean 4 development covers the spine and the bundle engine; graphon, chiral,
and categorical layers are scaffolded.

#heading("1. Introduction")

The Tamon program has shown, over roughly two decades, that the right way to
think about continuous-time quantum walks is through equitable partitions:
the existence of perfect state transfer between two vertices of a graph is
equivalent to the existence of perfect state transfer on the small quotient
graph induced by any compatible equitable partition
[bachman2011quotient]. Graph products are perfect-state-transfer
constructions in disguise [ge2010products]. The sharpest known characterization
of spatial-search optimality is also spectral, and is cleaner on quotients
[chan2022shadows]. Finally, optimality survives unbounded one-dimensional
probes [xie2023tail].

The previous version of this paper [amorc2025] reified a tiny slice of this
program into a Lean 4 artifact and a Python compiler prototype, organized
around the four-color completion of a planar graph. That version emphasized
the role of a chosen color quotient: once a coloring is fixed there is a
greatest graph compatible with it, and that greatest graph carries a
Laplacian-integral search criterion via
Li--Luo--Feng--Li [li2025deterministic].

This rewrite takes the same compiler stance but recognizes that color
completion is one corner of a much larger construction. We organize results
around a five-tower hierarchy, summarized by the diagram

$ "Set" -> "SimpleGraph" -> "WeightedGraph" -> "QuantumGraph" -> "Graphon" -> "Category". $

At every tower we maintain three load-bearing claims, all stated and (in the
finite case) mechanized in Lean:

+ The quotient spectrum is contained in the original spectrum:
  $"spec"(A slash pi) subset.eq "spec"(A)$, with explicit eigenvector lifts.
+ Continuous-time quantum walk on the original graph restricts to the
  cell-constant subspace, with the same evolution as the quotient walk; PST,
  uniform mixing, and spatial search on cell-uniform initial states therefore
  lift from quotient to host.
+ At Tower 5 the Quotient functor preserves filtered colimits, which lets us
  push finite results through to graphon limits without re-proof.

Three results are genuinely new. First, the spine theorems work at Tower 4:
we give graphon equitable partitions, prove the spectral-lift theorem for
the Hilbert--Schmidt integral operator, and lift PST and spatial-search
optimality to the graphon level. The closest ancestor is the
Bick--Sclosa treatment of dynamical systems on graph limits
[bick2024graphlimits], which gives an invariant-subspace view for real
dynamics; we give the unitary version. Second, chiral signings of bundles can
be optimized on the quotient: the recent uniform-mixing speedup
of Levine et al.~[levine2026chiral] fits naturally into this framework, and
its optimization problem reduces to a small signed problem on the template.
Third, the categorical filtered-colimit preservation theorem unifies the
finite-stage results with the graphon limit, formalizing the slogan
"quasi-infinite".

The rest of the paper specializes. Section 2 fixes the Tower-2 spine; Section
3 introduces the constructive engine that recovers products, joins, color
completions, and engineered template joins from a single definition. Section
4 climbs to Tower 3; Section 5 to Tower 4 and the headline limit theorem;
Section 6 to the categorical Tower 5. Section 7 collects two specializations
(chiral and relational). Section 8 returns to the engineering vision: a
search/transfer compiler that emits a Lean-checkable certificate.

#heading("2. The Spine: Equitable Partitions and the Universal Lift (Tower 2)")

A *weighted graph* on a finite vertex set $V$ is a Hermitian matrix
$A in CC^(V times V)$ with zero diagonal. The class includes simple graphs
(via 0/1 adjacency), signed and chiral graphs (unitary phases off the
diagonal), and weighted spin networks. The Lean carrier is
`Graphplay/Weighted.lean`.

#emph[Definition 2.1 (equitable partition).]
A partition $pi$ of $V$ into nonempty cells $C_1, ..., C_r$ is *equitable* for
$A$ if for every pair of cells $C_j, C_k$ the row sum
$ b_(j k) := sum_(w in C_k) A_(v w) $
is independent of $v in C_j$. The *quotient matrix* $A slash pi in CC^(r times r)$
has entries $(A slash pi)_(j k) = b_(j k)$. The *characteristic matrix*
$P in CC^(V times r)$ has $P_(v j) = 1$ if $v in C_j$ and $0$ otherwise.
This data lives in `Graphplay/Equitable.lean`.

The defining identity is $A P = P (A slash pi)$.

#emph[Theorem 2.1 (spectral lift).]
Let $pi$ be equitable for $A$. Then $"spec"(A slash pi) subset.eq "spec"(A)$,
and for every eigenvector $x$ of $A slash pi$ with eigenvalue $lambda$, the
vector $P x in CC^V$ is a (cell-constant) eigenvector of $A$ with the same
eigenvalue. (`Graphplay/Spectral.lean`.)

#emph[Theorem 2.2 (PST lift).]
Let $pi$ be equitable for $A$ and let $C_a, C_b$ be cells with
$|C_a| = |C_b|$. Identify cell-uniform states with the standard basis of
$CC^r$. If perfect state transfer occurs from $C_a$ to $C_b$ in the quotient
at time $tau$ --- that is, $|chevron.l e_b\, e^(-i tau A slash pi) e_a chevron.r| = 1$
--- then PST occurs between the cell-uniform states on $A$. This is the
content of [bachman2011quotient], formalized as `Graphplay/PST.lean`.

#emph[Theorem 2.3 (search lift).]
For a marked vertex $w in V$, let $pi_w$ be the refinement of $pi$ that
splits the cell containing $w$ into ${w}$ and its complement within the
original cell. Then $pi_w$ is equitable for the search Hamiltonian
$H_gamma = - gamma A - e_w e_w^*$, and the unitary $e^(-i t H_gamma)$
restricts to the (cell-uniform, ${w}$-aware) subspace, which has dimension
at most $r + 1$. The classical spatial-search optimality criterion
[chakraborty2020spatial] sharpened by [chan2022shadows] therefore reduces to
a small-matrix calculation on this subspace. The equitable-partition-for-search
idiom is due to [ide2022equitable]. Lean: `Graphplay/Search.lean`.

Theorem 2.1 is classical Godsil. Theorems 2.2 and 2.3 are the load-bearing
form we will lift through Towers 3, 4, 5. The Lean development covers all
three at Tower 2.

#emph[Example 2.4.]
The complete multipartite graph $K_(n_1, ..., n_r)$ has the color partition
as an equitable partition, with quotient matrix
$(A slash pi)_(j k) = n_k$ for $j != k$ and $0$ otherwise. The spectrum is
the spectrum of this small matrix together with internal zero modes,
recovering the calculation of [amorc2025].

#heading("3. The Constructive Engine: Bundles and Their Corners")

The universal construction at the spine is a bundle.

#emph[Definition 3.1 (graph bundle).]
A *graph bundle* `GraphBundle Q H B` is the data
$ Q : "WeightedGraph"(I), wide H : forall i in I, "WeightedGraph"(V_i), wide B : forall (i, j) " with " Q_(i j) != 0, V_i times V_j -> CC, $
subject to a Hermitian compatibility $B_(i j)(a, b) = overline(B_(j i)(b, a))$.
The *total graph* $"Tot"(Q, H, B)$ on $product.co_i V_i$ is given by
$ "Tot"(x, y) = cases(
  H_i(x, y) & "if " x, y "lie in the same fiber " V_i,
  Q_(i j) B_(i j)(x, y) & "if " x in V_i", " y in V_j", " i != j
). $
Lean: `Graphplay/Bundle.lean`.

Many earlier constructions are corners.

#emph[Proposition 3.2 (corners).]
+ With $H_i = 0$ and $B_(i j) = 1$ on Q-edges, `Tot(Q, H, B)` is the
  `TemplateJoin(Q, V)` of [amorc2025].
+ With $Q = K_2$, fibers $H_1, H_2$ arbitrary, and $B_(1 2) = 1$ on a chosen
  product subset, one recovers Cartesian, lexicographic, strong, and
  tensor products as cases. The PST-product theorems of
  [ge2010products] fall out as Tower-2 corollaries.
+ With $Q = K_C$ on a color palette and $H_i = 0$, one recovers the color
  completion `ColorCompletion c` of [amorc2025]; with $B_(i j) = 1$ this is
  complete multipartite.
+ With $Q$ a join graph in the sense of [kirkland2023join] and arbitrary
  fibers, one recovers their join construction; their PST-on-joins
  characterization is then a Tower-2 search-lift statement.

#emph[Theorem 3.3 (equitable iff fibers regular and couplings biregular).]
The cell partition $pi = {V_i}_(i in I)$ is equitable for $"Tot"(Q, H, B)$
if and only if
+ each fiber graph $H_i$ is regular (constant row sum $r_i$), and
+ each coupling $B_(i j)$ is *biregular*: $sum_(b in V_j) B_(i j)(a, b)$ is
  independent of $a in V_i$, and $sum_(a in V_i) B_(i j)(a, b)$ is
  independent of $b in V_j$.
When these conditions hold, the quotient matrix is
$(A slash pi)_(i j) = r_i delta_(i j) + Q_(i j) |V_j| beta_(i j)$ where
$beta_(i j)$ is the constant row sum of $B_(i j)$.

#emph[Corollary 3.4 (spectral inheritance).]
For equal-fiber bundles ($|V_i| = m$ for all $i$, $H_i = 0$, $B_(i j) = 1$):
$ "spec"("Tot"(Q, H, B)) = m dot "spec"(Q) " "union.dot" " "(internal zero modes)". $
In particular, the CNO spectral-ratio criterion
[chakraborty2020spatial] of [chan2022shadows] is inherited by the bundle from
the template.

The Lean artifact verifies Theorem 3.3 as `Bundle.equitable_iff_regular_biregular`
and Corollary 3.4 as `Bundle.spec_equal_fiber`. The engineering reading is
that the compiler's certificate is exactly the pair of regularity and
biregularity conditions in Theorem 3.3 --- both decidable, both Lean-checkable.

#heading("4. Tower 3: Operator-Algebra and Quantum-Graph Upgrade")

The next tower sits above weighted graphs. Let $cal(A) subset.eq M_V (CC)$ be
the unital $*$-subalgebra generated by $A$ and the identity. An equitable
partition $pi$ corresponds to an orthogonal projection $Pi = P (P^* P)^(-1) P^*$
onto the cell-constant subspace; the equitability condition is exactly
$Pi A Pi = A Pi$, i.e.\ $Pi in "Comm"(A)$. Lean carrier:
`Graphplay/QuantumGraph.lean`.

This is the right setting in which to discuss association schemes and quantum
graphs. The Bose--Mesner algebra of a commutative association scheme is the
maximally symmetric case; fractional revival on schemes
[chan2019fractional] is a Tower-3 phenomenon that descends to Tower 2 via the
characteristic projection of the scheme partition.

#emph[Definition 4.1 (quantum graph).]
A *quantum graph* on a finite-dimensional $C^*$-algebra $M subset.eq B(H)$ is
a self-adjoint $M$-bimodule of $B(H)$. An *equitable coarsening* is a unital
$*$-subalgebra $M_0 subset.eq M$ such that the orthogonal projection onto
the $M_0$-invariant vectors commutes with the bimodule's adjacency operator.

#emph[Theorem 4.2 (operator-algebra spine).]
Let $S$ be a quantum graph on $M$ with adjacency operator $A_S$, and let
$M_0$ be an equitable coarsening with projection $Pi$. Then $Pi A_S Pi$ is
the adjacency operator of a smaller quantum graph $S slash M_0$ on $M_0$, and
$ "spec"(A_(S slash M_0)) subset.eq "spec"(A_S). $
Moreover $e^(-i t A_S)$ commutes with $Pi$, so CTQW evolution on $S$
restricts to the $M_0$-invariant subspace and acts there as
$e^(-i t A_(S slash M_0))$.

Theorems 2.1--2.3 are the special case $M_0 = "diagonal subalgebra coarsened by " pi$.
Lean: `Graphplay/QuantumGraph.lean`. The fractional-revival
characterization of [chan2019fractional] on Hamming schemes is a Tower-3
restatement of a Tower-2 search-lift on the Hamming scheme partition, and is
visible in this language without re-proving.

#heading("5. Tower 4: Graphons and the Quasi-Infinite Limit Theorem")

We now lift the spine to graphon kernels. This is the headline section.

A *Hermitian graphon* is a measurable function $W : [0,1] times [0,1] -> CC$
with $W(x, y) = overline(W(y, x))$ and $W in L^2$. The induced integral
operator $T_W : L^2[0,1] -> L^2[0,1]$, $(T_W f)(x) = integral_0^1 W(x,y) f(y) "d" y$
is compact, self-adjoint, and Hilbert--Schmidt. The continuous-time quantum
walk on $W$ is the unitary group $U_W(t) := e^(-i t T_W)$. Carrier:
`Graphplay/Graphon/Basic.lean`, `Graphplay/Graphon/Hermitian.lean`.

#emph[Definition 5.1 (graphon equitable partition).]
A measurable partition $[0,1] = union.big.dot_(k=1)^r A_k$ is *equitable* for
$W$ if for all $j, k in {1, ..., r}$ the function
$ x |-> integral_(A_k) W(x, y) "d" y $
is constant almost everywhere on $A_j$. Call that constant
$tilde(b)_(j k)$. The *graphon quotient matrix* $W slash pi in CC^(r times r)$
has entries $(W slash pi)_(j k) = tilde(b)_(j k) / sqrt(|A_j| |A_k|)$ when
we normalize to the rescaled-indicator basis
$u_k := |A_k|^(-1 slash 2) bb(1)_(A_k)$. Lean:
`Graphplay/Graphon/Equitable.lean`. The closest finite ancestor is the
Bick--Sclosa invariant-subspace decomposition [bick2024graphlimits]; we record
the operator-theoretic version inspired by the LQR invariant-subspace
treatment of [gao2020graphon].

#emph[Theorem 5.2 (graphon spectral lift).]
If $pi$ is equitable for $W$, then $"spec"(W slash pi) subset.eq "spec"(T_W)$,
with eigenfunctions of $T_W$ given by $sum_k x_k u_k$ for eigenvectors $x$
of $W slash pi$. The orthogonal complement of $"span"{u_k}$ is invariant
under $T_W$ and gives the (possibly infinite) fiber-internal spectrum.
Lean: `Graphplay/Graphon/Spectral.lean`.

#emph[Theorem 5.3 (graphon PST and CTQW lift).]
For Hermitian $W$ with equitable partition $pi$, the unitary $U_W(t)$
preserves the finite-dimensional cell-constant subspace $V_pi := "span"{u_k}$
and acts there as $e^(-i t W slash pi)$. Consequently, if perfect state
transfer between two cell-uniform states occurs in the quotient at time
$tau$, it occurs in the graphon walk. This is a graphon-level generalization
of [bachman2011quotient].

#emph[Theorem 5.4 (graphon spatial-search lift).]
Let $S subset.eq [0,1]$ be a measurable marked set of positive measure. The
search Hamiltonian $H_(W, gamma, S) = - gamma T_W - "Proj"_(L^2(S))$ has the
refined partition $pi_S := pi join {S, S^c}$ as a (graphon) equitable
partition, and the search dynamics restrict to a Hamiltonian of finite
dimension at most $2 r$ on $V_(pi_S)$. The optimal-search criterion of
[chan2022shadows] therefore reduces to a finite spectral computation on
$W slash pi_S$.

#emph[Theorem 5.5 (quasi-infinite limit theorem).]
Let $(G_n, pi_n)_(n in NN)$ be a sequence of finite Hermitian weighted
graphs equipped with equitable partitions, all of size at most $r$.
Suppose:
+ The pixel-step graphons $W_(G_n)$ converge to a Hermitian graphon $W$ in
  the cut norm.
+ The cell-fraction vectors converge to a probability vector
  $(|A_1|, ..., |A_r|) in Delta^(r-1)$ with all $|A_k| > 0$.
+ The normalized quotient matrices $G_n slash pi_n$ converge to a Hermitian
  matrix $M in CC^(r times r)$ in Frobenius norm.

Then $W$ admits a measurable equitable partition $pi$ realizing the limit
cell fractions and with $W slash pi = M$. Moreover, every cell-uniform PST
or spatial-search problem on $(G_n, pi_n)$ has a well-defined limit on
$(W, pi)$, and the limit's value is the value of the finite Hermitian
problem on $M$. As a special case, recover [xie2023tail]: the limit of
$K_n$ plus a path of length $n$ is the disjoint union of a complete graphon
and an infinite path, with a 2-cell equitable partition; the resulting
$2 times 2$ search problem is exactly the Farhi--Gutmann complete-graph
search, and optimality is preserved. The transfer-side companion
[bernard2022tails] is recovered by the analogous 2-cell partition.

Lean: `Graphplay/Graphon/Limit.lean` (currently scaffolded; the proof reduces
to (a) cut-norm-implies-operator-norm convergence under bounded entries
[szegedy2010spectral], (b) Frobenius convergence of the quotient matrices,
and (c) continuity of finite spectral optimization problems).

#emph[Example 5.6 (cycle blowup).]
Fix a template weighted graph $Q$ on $r$ vertices. The sequence
$"Tot"(Q, 0, J)$ with equal fibers of size $n$, viewed as pixel-step
graphons, converges in cut norm to the block-constant graphon $W_Q$ with
cells of measure $1 slash r$ and value $Q_(j k)$ in block $(j, k)$. The
quotient at every stage is $n dot Q$ (up to a renormalization that absorbs
into the time parameter), and Theorem 5.5 gives the limit as the finite
search problem on $Q$. The compiler examples of [amorc2025] are exactly the
finite stages of such a sequence.

#heading("6. Tower 5: Categorical Framing")

Let $"EqWGr"$ be the category whose objects are pairs $(G, pi)$ with $G$ a
finite Hermitian weighted graph and $pi$ an equitable partition, and whose
morphisms $(G, pi) -> (G', pi')$ are pairs $(phi, theta)$ where $phi$ is a
weight-preserving cell-block map and $theta$ refines $pi$ to a partition
compatible with $phi$. Let $"Mat"_("fin")(CC)$ be the category of finite
Hermitian matrices.

Define $"Quot" : "EqWGr" -> "Mat"_("fin")(CC)$ by $"Quot"(G, pi) = G slash pi$.

#emph[Theorem 6.1 (filtered-colimit preservation).]
The functor $"Quot"$ preserves filtered colimits. Explicitly, given a
filtered diagram $(G_alpha, pi_alpha)$ in $"EqWGr"$ whose underlying
weighted graphs form a sequence with a graphon colimit $W$ (with respect to
the cut metric) and whose quotient matrices have a finite-dimensional
Frobenius limit $M$, the colimit pair $(W, pi)$ exists in the extended
graphon-equitable category and $W slash pi = M$. Lean:
`Graphplay/Categorical.lean`.

Theorem 6.1 unifies several earlier observations.

#emph[Corollary 6.2.]
The quasi-infinite limit theorem (Theorem 5.5) is the Tower-4 instance of
Theorem 6.1. The Tower-1 inverse-limit and edge-union universal properties
of [amorc2025] are Tower-1 and Tower-0 instances. The "failed reflector"
observation --- there is no left adjoint to "forget the coloring" --- is
recovered as the statement that the underlying-graph functor *does not* have
a colimit-preserving left adjoint; the relative left adjoint along a chosen
template $Q$ does exist and is the bundle construction of Section 3.

#heading("7. Chiral and Relational Specializations")

#emph[Chiral.] A *unitary signing* of a bundle $"Tot"(Q, H, B)$ is a Hermitian
phase decoration of off-diagonal blocks: $B_(i j) -> sigma_(i j) B_(i j)$
with $|sigma_(i j)| = 1$ and $sigma_(j i) = overline(sigma_(i j))$. Define
the *phase-equitable* partition condition by requiring biregularity of the
signed couplings. Lean: `Graphplay/Chiral.lean`.

#emph[Theorem 7.1 (chiral signing as optimization on the quotient).]
For a bundle with phase-equitable cell partition, the mixing-time
functional
$ M(sigma; t) := max_(v, w) |U_(sigma, t)(v, w)|^2 $
restricted to cell-uniform initial and final states equals the corresponding
quantity computed for the signed quotient $sigma_Q := (sigma_(i j))$ acting
on $Q$. In particular, optimizing $sigma$ over the (typically large) phase
space of bundle signings reduces to optimizing $sigma_Q$ over the much
smaller phase space $U(1)^(E(Q))$, modulo gauge.

#emph[Corollary 7.2.]
The uniform-mixing speedup of [levine2026chiral] on $K_n^sigma$ has a bundle
version: if a bundle has $K_n^sigma$ as its quotient and equal fibers, then
the corresponding chiral mixing speedup holds for the bundle on the
cell-uniform subspace. Open: characterize fiber-internal interference for
the full uniform-mixing problem on the bundle.

#emph[Relational / CSP.] A k-ary template is a relation $T subset.eq I^k$.
Given a label map $f : V -> I$, the pullback $f^* T$ is a $k$-uniform
hypergraph on $V$ whose edges are those k-tuples mapping into $T$. The
incidence matrix gives a Hermitian bipartite weighted graph on
$V union.dot E(f^* T)$, and equitable partitions of this incidence graph
recover the standard fractional/combinatorial CSP invariants. Lean:
`Graphplay/Relational.lean`. For $k = 2$ this is the pullback graph of
[amorc2025]; the $k > 2$ case appears not to have been treated through the
equitable lens.

#heading("8. Toolkit Vision: Search/Transfer Compiler with Certificates")

The previous note [amorc2025] described a Python prototype
(`tools/search_compiler.py`) that takes a template and emits adjacency and
Laplacian spectra, a CNO-style spectral-ratio diagnostic, and a
quotient-Hamiltonian scan. With the spine in place we promote the prototype
to a typed compiler whose signature is

$ "primitive" times "hardware" |-> ("host", "partition", "schedule", "certificate"). $

The *primitive* is one of PST, uniform mixing, or spatial search; the
*hardware* is a set of quotient constraints (which cells must exist; which
couplings are realizable; which signings are realizable). The *host* is a
`GraphBundle` (Section 3); the *partition* is an equitable partition of the
host whose quotient encodes the primitive; the *schedule* is the (possibly
time-dependent) Hamiltonian; the *certificate* is a term of a Lean type
`Certificate primitive host schedule` whose inhabitation is exactly the
relevant spine hypothesis (regularity, biregularity, signing
phase-equitability, or graphon equitability).

Concretely, `Graphplay/Toolkit/Certificate.lean` will define
`structure Certificate (p : Primitive) (B : Bundle) (S : Schedule) : Prop`
with field constructors corresponding to Theorems 3.3, 7.1, and 5.4 as
appropriate. The compiler emits both a JSON artifact and a Lean term; the
Lean term is checked by `lake build` before deployment, giving a
machine-verifiable bridge from a CSP-shaped engineering description to a
quantum-walk schedule.

The case studies of [amorc2025] (`rook_3x3_equal_fiber`,
`cycle8_powerlaw_alpha1`, `torus_heawood7_equal_fiber`) are precisely
equal-fiber bundles whose templates carry verifiable regularity certificates;
they become end-to-end Lean-checked instances of the compiler.

#heading("9. Connections and Open Directions")

*Graphops.* Backhausz--Szegedy graphops generalize graphons by removing the
$L^2$ symmetric-kernel assumption. The quotient spine survives when the
operator commutes with the projection $Pi$; the graphon Theorem 5.5 should
extend to graphops under mild compactness. Lean port open.

*Surface topology.* The Heawood map-color completion of [amorc2025] is now
visible as the special bundle with $Q = K_(H(g))$. The surface algebraic-
connectivity ceiling of Freitas [freitas2001heawood] becomes a Tower-2
spectral budget on $Q$. A topology-aware bundle (where fibers carry a
metric and $Q$ is a triangulation) would unify surface coloring with the
filtered-colimit picture.

*Bose--Mesner versus filtered colimits.* Conjecture: a family of finite
weighted graphs admits a graphon quasi-infinite limit (Theorem 5.5) and a
chiral signing speedup (Theorem 7.1) on a common partition if and only if
the Bose--Mesner algebra of that partition coincides with the algebra
generated by the characteristic projections of $pi$. This would tie the
chiral and graphon stories to the association-scheme literature in a clean
way; it is consistent with [chan2019fractional] but open in general.

*Open-system extensions.* The bundle-and-quotient picture survives unitary
perturbations whose generator is itself equitable. Lindbladian extensions,
time-dependent schedules, and noisy CTQW are not yet treated.

#heading("References")

#set par(justify: false)

#emph[Quantum-walk and spatial-search papers (Tamon corpus and immediate
neighbors):]

- #emph[bachman2011quotient.] R. Bachman, E. Fredette, J. Fuller,
  M. Landry, M. Opperman, C. Tamon, A. Tollefson.
  #link("https://arxiv.org/abs/1108.0339")[Perfect state transfer on quotient
  graphs], arXiv:1108.0339.
- #emph[ge2010products.] Y. Ge, B. Greenberg, O. Perez, C. Tamon.
  #link("https://arxiv.org/abs/1009.1340")[Perfect state transfer, graph
  products and equitable partitions], arXiv:1009.1340.
- #emph[chan2022shadows.] A. Chan, C. Godsil, C. Tamon, W. Xie.
  #link("https://arxiv.org/abs/2204.04355")[Of shadows and gaps in spatial
  search], arXiv:2204.04355.
- #emph[xie2023tail.] W. Xie, C. Tamon.
  #link("https://arxiv.org/abs/2301.07251")[No infinite tail beats optimal
  spatial search], arXiv:2301.07251.
- #emph[bernard2022tails.] P.-A. Bernard, C. Tamon, L. Vinet, W. Xie.
  #link("https://arxiv.org/abs/2211.14704")[Quantum state transfer in graphs
  with tails], arXiv:2211.14704.
- #emph[ide2022equitable.] Y. Ide, A. Narimatsu.
  #link("https://arxiv.org/abs/2209.07688")[Perfect state transfer,
  equitable partition and continuous-time quantum walk based search],
  arXiv:2209.07688.
- #emph[chan2019fractional.] A. Chan, G. Coutinho, C. Tamon, L. Vinet,
  H. Zhan. #link("https://arxiv.org/abs/1907.04729")[Fractional revival
  and association schemes], arXiv:1907.04729.
- #emph[kirkland2023join.] S. Kirkland, H. Monterde.
  #link("https://arxiv.org/abs/2312.06906")[Quantum walks on join graphs],
  arXiv:2312.06906.
- #emph[levine2026chiral.] L. Levine, J. J. Mesapam, B. Mustico, C. Tamon,
  G. Tucker, H. Zhan.
  #link("https://arxiv.org/abs/2605.04414")[Uniform mixing in chiral quantum
  walks], arXiv:2605.04414.

#emph[Graphon foundations:]

- #emph[bick2024graphlimits.] C. Bick, D. Sclosa.
  #link("https://arxiv.org/abs/2110.13686")[Dynamical systems on graph
  limits and their symmetries], arXiv:2110.13686.
- #emph[szegedy2010spectral.] B. Szegedy.
  #link("https://arxiv.org/abs/1003.5588")[Limits of kernel operators and
  the spectral regularity lemma], arXiv:1003.5588.
- #emph[gao2020graphon.] S. Gao, P. E. Caines.
  #link("https://arxiv.org/abs/2004.00677")[Subspace decomposition for
  graphon LQR: applications to VLSNs of harmonic oscillators], arXiv:2004.00677.

#emph[Spatial-search references kept from v1:]

- #emph[chakraborty2020spatial.] S. Chakraborty, L. Novo, A. Ambainis,
  Y. Omar. #link("https://arxiv.org/abs/1508.01327")[Spatial search by
  quantum walk is optimal for almost all graphs], arXiv:1508.01327.
- #emph[king2025longrange.] R. King et al.
  #link("https://arxiv.org/abs/2501.08148")[Optimal spatial searches with
  long-range tunneling], arXiv:2501.08148.
- #emph[li2025deterministic.] X. Li, S. Luo, Z. Feng, Y. Li.
  #link("https://arxiv.org/abs/2506.21108")[Deterministic quantum search on
  all Laplacian integral graphs], arXiv:2506.21108.
- #emph[sadowski2014planar.] P. Sadowski.
  #link("https://arxiv.org/abs/1406.0339")[Quantum spatial search on planar
  networks], arXiv:1406.0339.
- #emph[wong2017lazy.] T. Wong.
  #link("https://arxiv.org/abs/1706.06939")[Faster search by lackadaisical
  quantum walk], arXiv:1706.06939.
- #emph[freitas2001heawood.] M. A. A. de Freitas.
  #link("https://arxiv.org/abs/math/0109191")[A Heawood-type result for the
  algebraic connectivity of graphs on surfaces], arXiv:math/0109191.
- #emph[amorc2025.] AMORC.
  #emph[A.M.O.R.C. Toolkit Note: Engineered Color Templates for Spatial
  Search.] (Graphplay v1; this repository, `paper/quasi_infinite_adjoint.typ`.)
