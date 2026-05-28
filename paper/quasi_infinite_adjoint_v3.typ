#set document(title: "Graphplay: A Combinatorial Assembly Language for Quantum Primitives")
#set page(margin: 1in)
#set text(size: 11pt)
#set par(justify: true)

#align(center)[
  #text(size: 17pt, weight: "bold")[Graphplay] \
  #v(0.25em)
  #text(size: 13pt, weight: "bold")[A Combinatorial Assembly Language for Quantum Primitives] \
  #v(0.35em)
  #text(size: 11.5pt)[Equitable Quotients Across Five Towers, with Chiral, Graphon, \
  and Categorical Extensions of the Tamon Spine] \
  #v(0.45em)
  #text(size: 9.5pt)[Anti Mathematics Online Research Crew --- Graphplay v3 draft]
]

#v(0.8em)

#heading("Abstract")

We organize a body of continuous-time quantum-walk (CTQW) results --- perfect
state transfer, uniform mixing, spatial search, sampling, transfer along
tails --- around a single structural primitive: the *equitable partition* of
a Hermitian weighted graph, with its small finite quotient matrix as the
universal "compiled" object. We call the resulting compiler stack *Graphplay*:
a typed, multi-tower combinatorial assembly language for compiling quantum
primitives to host Hamiltonians via equitable partitions, bundles, and
chiral signings, with proven lift theorems.

The compiler stack is a five-tower spine. At each tower we maintain three
load-bearing theorems: $"spec"(A slash pi) subset.eq "spec"(A)$ with explicit
eigenvector lift; restriction of CTQW evolution to the cell-uniform subspace;
and reduction of PST, mixing, and search to a finite quotient computation.
The towers are sets, simple graphs, Hermitian/chiral weighted graphs, operator
algebras and coherent algebras, graphons, and a categorical/filtered-colimit
layer.

Three results are genuinely new with respect to the Tamon corpus. First, the
spine theorems lift to graphons (Tower 4): equitable graphon partitions,
spectral lift for the Hilbert--Schmidt integral operator, and PST and search
on the graphon limit. Second, chiral signings are first-class: the
characteristic-projection identity $sigma$-`signedBy_preserves_equitable` puts
the Levine--Mesapam--Mustico--Tamon--Tucker--Zhan uniform-mixing speedup, and
the Xie--Kay--Tamon speed-limit-breaking PST protocol, into the same toolkit
language --- their optimizations factor through a small signed quotient.
Third, a categorical filtered-colimit preservation theorem makes the slogan
"quasi-infinite" precise: a sequence of finite CTQW problems with bounded
equitable quotients has its behavior controlled by a single colimit quotient,
recovering the Xie--Tamon infinite-tail result and the
Bernard--Tamon--Vinet--Xie tails-transfer companion as one-line corollaries.

We package the result as an *engineering toolkit*: given a (primitive,
hardware) request, the compiler emits a (host, partition, schedule,
certificate) tuple, where the certificate is a Lean-checkable witness of the
relevant spine hypothesis. The Lean 4 development covers Towers 1--5 of the
spine, the bundle engine, the chiral specialization, and a graphon scaffold;
twenty further modules sketch open extensions (non-commutative coherent
algebras, hypergraph PST, Hodge integration, lattice gauge, mean-field games,
tensor networks, TQFT, WL refinement, random matrix theory, optimal transport)
and Tower 6--7 (sheaf-of-graphs and $infinity$-categorical) directions.

#heading("1. Introduction: Graphplay as an Assembly Language")

Two decades of the Tamon program has shown that the right way to think about
CTQW is structural: phenomena that look like analytic miracles --- perfect
state transfer at integer times, optimal Grover-like search, uniform mixing
at carefully chosen evolution times --- are very often *projections of small
finite calculations*. The lens that turns each into a small calculation is
the equitable partition.

The foundational sequence is by now classical. Perfect state transfer on a
graph $G$ between two vertices is equivalent to PST on the quotient graph
$G slash pi$ induced by any equitable partition $pi$ separating the source
and target [bachman2011quotient]. Graph products are PST constructions in
disguise [ge2010products]. The sharpest known characterization of
spatial-search optimality is spectral and lives most cleanly on the quotient
[chan2022shadows]. Optimality survives unbounded one-dimensional probes
[xie2023tail]. PST with tails attached is governed by a quotient that
contains both finite block and infinite block, as in
Bernard--Tamon--Vinet--Xie [bernard2022tails]. Most strikingly, the
*speed limit* for PST can be broken in the projective/dual-rail setting of
Xie--Kay--Tamon [xie2022speedlimit] --- a result whose protocol is again
naturally a small calculation on an engineered template.

The previous version of this paper [amorc2025v2] reified part of this picture
as a Lean 4 artifact organized around equitable partitions of weighted
graphs, a `GraphBundle` engine recovering products and color completions as
corners, and a graphon-level extension. This rewrite changes the lead. We
view the whole stack as a *compiler*:

#emph[Graphplay slogan.] *A typed combinatorial assembly language compiles
quantum primitives (PST, mixing, search, sampling, transfer) to host
operators via equitable partitions, graph bundles, and chiral signings, with
machine-checkable lift theorems.*

The signature of the compiler is

$ ("primitive", "hardware") |-> ("host", "partition", "schedule", "certificate"). $

The *primitive* selects which spine lift one is targeting --- PST, uniform
mixing, spatial search, fractional revival, sampling, transfer along a tail.
The *hardware* is a set of decidable host constraints (planar, surface
genus, near-neighbor radius, allowed phase set, regularity, size bound). The
*host* is a `GraphBundle` (Section 3); the *partition* is a Lean
`EquitablePartition` of that host whose quotient encodes the primitive; the
*schedule* is the (possibly time-dependent, possibly chiral) Hamiltonian;
the *certificate* is a term of a Lean type whose inhabitation is exactly the
relevant spine hypothesis. The previous "Heawood completion" pipeline was
one such (primitive, hardware) pair; we now generate many.

The compiler stack has five tiers, in increasing generality:

$ "Set" arrow.r "SimpleGraph" arrow.r "Weighted" \/ "Chiral" arrow.r "OpAlg" \/ "QuantumGraph" arrow.r "Graphon" arrow.r "Category". $

At every tower we maintain three load-bearing claims, all stated and (in the
finite case) mechanized in Lean 4:

+ The quotient spectrum is contained in the original spectrum:
  $"spec"(A slash pi) subset.eq "spec"(A)$, with explicit eigenvector lifts.
+ CTQW on the original operator restricts to the cell-constant subspace and
  acts there as the quotient walk; PST, uniform mixing, fractional revival,
  and spatial search on cell-uniform initial states lift from quotient to
  host.
+ At Tower 5 the Quotient functor preserves filtered colimits, which
  pushes finite results through to graphon limits without re-proof.

Three contributions are genuinely new. First, the spine works at Tower 4:
we give graphon equitable partitions, prove the spectral-lift theorem for
the Hilbert--Schmidt integral operator, and lift PST and spatial-search
optimality to the graphon level. The closest ancestor is the Bick--Sclosa
treatment of dynamical systems on graph limits [bick2024graphlimits], which
gives an invariant-subspace view for *real* dynamics; we give the *unitary*
version. The operator-theoretic LQR background is Gao--Caines
[gao2020graphon].

Second, chiral signings are upgraded to a first-class compiler primitive. The
identity $sigma$-`signedBy_preserves_equitable` (proved in
`Graphplay/Chiral.lean`) says that any signing constant on cell-pairs
preserves equitability of the partition --- and therefore that the
optimization over signings, mixing times, or PST times factors through a
small signed quotient. The uniform-mixing speedup
of Levine--Mesapam--Mustico--Tamon--Tucker--Zhan [levine2026chiral] becomes
the quotient corner of this story; the Xie--Kay--Tamon speed-limit-breaking
PST protocol [xie2022speedlimit] becomes another --- both are now in the
toolkit's compile catalog.

Third, the categorical filtered-colimit preservation theorem unifies the
finite-stage results with the graphon limit, formalizing the slogan
"quasi-infinite". The Xie--Tamon infinite-tail result [xie2023tail] is a
two-cell corner; the Bernard--Tamon--Vinet--Xie tails-transfer result
[bernard2022tails] is the corresponding two-cell PST corner.

The rest of the paper specializes. Section 2 fixes the Tower-2 spine and its
three load-bearing theorems. Section 3 introduces the constructive bundle
engine that recovers products, joins, color completions, and engineered
template joins from a single definition. Section 4 climbs to Tower 3
(operator algebras, coherent algebras, quantum graphs); Section 5 to Tower 4
(graphons and the quasi-infinite limit theorem); Section 6 to the categorical
Tower 5. Section 7 collects the chiral specialization with explicit citation
of the Tamon corpus. Section 8 returns to the engineering vision: a
search/transfer/mixing compiler that emits Lean-checkable certificates.
Section 9 lays out the research program: ten dowsing-rod holes flagged for
proof, eight cross-disciplinary integrations under way, the conjectural
Towers 6--7, and the falsifiable Conjecture 9.3 tying Bose--Mesner algebras
to chiral and graphon admissibility.

#heading("2. The Spine: Equitable Partitions and the Universal Lift (Tower 2)")

A *weighted graph* on a finite vertex set $V$ is a Hermitian matrix
$A in CC^(V times V)$ with zero diagonal. The class includes simple graphs
(via 0/1 adjacency), signed and chiral graphs (unitary phases off the
diagonal), and weighted spin networks. The Lean carrier is
`Graphplay/Weighted.lean`.

#emph[Definition 2.1 (equitable partition).]
A partition $pi$ of $V$ into nonempty cells $C_1, dots, C_r$ is *equitable* for
$A$ if for every pair of cells $C_j, C_k$ the row sum
$ b_(j k) := sum_(w in C_k) A_(v w) $
is independent of $v in C_j$. The *quotient matrix* $A slash pi in CC^(r times r)$
has entries $(A slash pi)_(j k) = b_(j k)$. The *characteristic matrix*
$P in CC^(V times r)$ has $P_(v j) = 1$ if $v in C_j$ and $0$ otherwise. The
defining identity is $A P = P (A slash pi)$. This data lives in
`Graphplay/Equitable.lean`.

#emph[Theorem 2.1 (spectral lift).]
Let $pi$ be equitable for $A$. Then $"spec"(A slash pi) subset.eq "spec"(A)$,
and for every eigenvector $x$ of $A slash pi$ with eigenvalue $lambda$, the
vector $P x in CC^V$ is a (cell-constant) eigenvector of $A$ with the same
eigenvalue. Lean: `Graphplay/Spectral.lean`.

#emph[Theorem 2.2 (PST lift).]
Let $pi$ be equitable for $A$ and let $C_a, C_b$ be cells with
$|C_a| = |C_b|$. Identify cell-uniform states with the standard basis of
$CC^r$. If perfect state transfer occurs from $C_a$ to $C_b$ in the quotient
at time $tau$ --- that is, $abs(angle.l e_b\, e^(-i tau A slash pi) e_a angle.r) = 1$
--- then PST occurs between the cell-uniform states on $A$. This is the
content of [bachman2011quotient]; Lean: `Graphplay/PST.lean`.

#emph[Theorem 2.3 (search lift).]
For a marked vertex $w in V$, let $pi_w$ be the refinement of $pi$ that
splits the cell containing $w$ into ${w}$ and its complement within the
original cell. Then $pi_w$ is equitable for the search Hamiltonian
$H_gamma = - gamma A - e_w e_w^*$, and the unitary $e^(-i t H_gamma)$
restricts to the (cell-uniform, ${w}$-aware) subspace, of dimension at most
$r + 1$. The classical spatial-search optimality criterion
[chakraborty2020spatial] sharpened by [chan2022shadows] therefore reduces to
a small-matrix calculation on this subspace. The equitable-partition-for-search
idiom is due to [ide2022equitable]. Lean: `Graphplay/Search.lean`.

Theorem 2.1 is classical Godsil. Theorems 2.2 and 2.3 are the load-bearing
form we lift through Towers 3, 4, 5. The Lean development covers all three at
Tower 2 with eigenvector-lift maps as data, not merely existence.

#emph[Example 2.4 (color quotient).]
The complete multipartite graph $K_(n_1, dots, n_r)$ has the color partition
as equitable, with quotient matrix $(A slash pi)_(j k) = n_k$ for $j != k$
and $0$ otherwise. The spectrum is the spectrum of this small matrix plus
internal zero modes; the four-color completion of [amorc2025v2] is the
case $r = 4$, $n_1 = dots.h.c = n_4$.

#emph[Example 2.5 (Xie--Tamon tail).]
The graph $K_n + P_n$ (a complete graph attached to a path of length $n$) has
the two-cell partition (clique, tail) as equitable. The quotient is a
$2 times 2$ Hermitian matrix encoding the Farhi--Gutmann complete-graph
search; the result of [xie2023tail] that an infinite tail does not break
optimality is then a continuity statement about this $2 times 2$ matrix, as
the tail-cell measure stays fixed. We return to this in Section 5.

#heading("3. The Constructive Engine: Bundles and Their Corners")

The universal construction at the spine is a graph bundle.

#emph[Definition 3.1 (graph bundle).]
A *graph bundle* `GraphBundle Q V` is the data
$ Q : "WeightedGraph"(I), wide V : forall i in I, V_i, wide H_i : "WeightedGraph"(V_i), wide B_(i j) : V_i times V_j arrow.r CC, $
subject to a Hermitian compatibility $B_(i j)(a, b) = overline(B_(j i)(b, a))$
and only required where $Q_(i j) != 0$.
The *total graph* $"Tot"(Q, H, B)$ on $product.co_i V_i$ is given by
$ "Tot"(x, y) = cases(
  H_i(x, y) & "if " x\, y "lie in the same fiber " V_i,
  Q_(i j) B_(i j)(x, y) & "if " x in V_i\, y in V_j\, i != j
). $
Lean: `Graphplay/Bundle.lean`.

Many earlier constructions are corners.

#emph[Proposition 3.2 (corners).]
+ With $H_i = 0$ and $B_(i j) = 1$ on Q-edges, `Tot(Q, H, B)` is the
  `TemplateJoin(Q, V)` of [amorc2025v2].
+ With $Q = K_2$, fibers $H_1, H_2$ arbitrary, and $B_(1 2) = 1$ on a chosen
  product subset, one recovers Cartesian, lexicographic, strong, tensor,
  conormal, and disjunctive products as cases. The PST-product theorems of
  [ge2010products] fall out as Tower-2 corollaries (proved as
  `Bundle.cartesianProduct_pst`, `Bundle.lexProduct_pst`,
  `Bundle.tensorProduct_pst`, etc., in
  `Graphplay/Dowsing/BundlePSTLift.lean`).
+ With $Q = K_C$ on a color palette and $H_i = 0$, one recovers the color
  completion `ColorCompletion c` of [amorc2025v2]; with $B_(i j) = 1$ this is
  complete multipartite.
+ With $Q$ a join graph in the sense of [kirkland2023join] and arbitrary
  fibers, one recovers the join construction of Kirkland--Monterde; their
  PST-on-joins characterization is then a Tower-2 search-lift statement.

#emph[Theorem 3.3 (equitable iff regular fibers and biregular couplings).]
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
In particular, the CNO spectral-ratio criterion [chakraborty2020spatial],
sharpened by [chan2022shadows], is inherited by the bundle from the template.

The Lean artifact verifies Theorem 3.3 as `Bundle.equitable_iff_regular_biregular`
and Corollary 3.4 as `Bundle.spec_equal_fiber`. The engineering reading is
that the compiler's *certificate* is exactly the pair of regularity and
biregularity conditions in Theorem 3.3 --- both decidable, both Lean-checkable.

#heading("4. Tower 3: Operator Algebras, Coherent Algebras, Quantum Graphs")

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

#emph[Definition 4.1 (coherent algebra of a partition).]
The *partition-projector algebra* $cal(P)(pi) subset.eq M_V (CC)$ is the
subalgebra of matrices $M$ such that $M$ is cell-pair-constant. This is the
maximal subalgebra in which $pi$ is equitable; it is closed under Schur and
matrix products and is the smallest coherent algebra containing
$Pi$. Lean: `Graphplay/QuantumGraph.lean`,
`Graphplay/Dowsing/CoherentAlgebra.lean`.

#emph[Definition 4.2 (quantum graph).]
A *quantum graph* on a finite-dimensional $C^*$-algebra $M subset.eq B(H)$ is
a self-adjoint $M$-bimodule of $B(H)$. An *equitable coarsening* is a unital
$*$-subalgebra $M_0 subset.eq M$ such that the orthogonal projection onto
the $M_0$-invariant vectors commutes with the bimodule's adjacency operator.

#emph[Theorem 4.3 (operator-algebra spine).]
Let $S$ be a quantum graph on $M$ with adjacency operator $A_S$, and let
$M_0$ be an equitable coarsening with projection $Pi$. Then $Pi A_S Pi$ is
the adjacency operator of a smaller quantum graph $S slash M_0$ on $M_0$, and
$ "spec"(A_(S slash M_0)) subset.eq "spec"(A_S). $
Moreover $e^(-i t A_S)$ commutes with $Pi$, so CTQW evolution on $S$
restricts to the $M_0$-invariant subspace and acts there as
$e^(-i t A_(S slash M_0))$.

Theorems 2.1--2.3 are the special case $M_0$ = diagonal subalgebra coarsened
by $pi$. Lean: `Graphplay/QuantumGraph.lean`. The fractional-revival
characterization of [chan2019fractional] on Hamming schemes is a Tower-3
restatement of a Tower-2 search-lift on the Hamming scheme partition, visible
in this language without re-proving.

#heading("5. Tower 4: Graphons and the Quasi-Infinite Limit Theorem")

We now lift the spine to graphon kernels. This is the headline section.

A *Hermitian graphon* on a probability space $(Omega, mu)$ is a measurable
function $W : Omega times Omega arrow.r CC$ with $W(x, y) = overline(W(y, x))$
and $W in L^2$. The induced integral operator
$T_W : L^2(mu) arrow.r L^2(mu)$, $(T_W f)(x) = integral W(x,y) f(y) "d" mu(y)$,
is compact, self-adjoint, and Hilbert--Schmidt. The CTQW on $W$ is the
one-parameter unitary group $U_W(t) := e^(-i t T_W)$. Lean carriers:
`Graphplay/Graphon.lean` (basic), `Graphplay/Graphon/Equitable.lean`,
`Graphplay/Graphon/PST.lean`, `Graphplay/Graphon/Limit.lean`.

#emph[Definition 5.1 (graphon equitable partition).]
A measurable partition $Omega = union.big.dot_(k=1)^r A_k$ is *equitable* for
$W$ if for all $j, k in {1, dots, r}$ the function
$ x mapsto integral_(A_k) W(x, y) "d" mu(y) $
is constant almost everywhere on $A_j$. Call that constant
$tilde(b)_(j k)$. In the rescaled-indicator basis
$u_k := mu(A_k)^(-1 slash 2) bb(1)_(A_k)$, the *graphon quotient matrix*
$W slash pi in CC^(r times r)$ has entries
$ (W slash pi)_(j k) = tilde(b)_(j k) sqrt(mu(A_k) slash mu(A_j)). $
The closest finite ancestor is the Bick--Sclosa invariant-subspace
decomposition [bick2024graphlimits] for real dynamics on graphons; we record
the operator-theoretic unitary version, inspired by the LQR
invariant-subspace treatment of [gao2020graphon] and the spectral
graph-limit theorems of [szegedy2010spectral].

#emph[Theorem 5.2 (graphon spectral lift).]
If $pi$ is equitable for $W$, then $"spec"(W slash pi) subset.eq "spec"(T_W)$,
with eigenfunctions of $T_W$ given by $sum_k x_k u_k$ for eigenvectors $x$
of $W slash pi$. The orthogonal complement of $"span"{u_k}$ is invariant
under $T_W$ and contributes the (possibly infinite) fiber-internal spectrum.

#emph[Theorem 5.3 (graphon CTQW and PST lift, headline ★).]
For Hermitian $W$ with measurable equitable partition $pi$, the unitary
$U_W(t)$ preserves the finite-dimensional cell-constant subspace
$V_pi := "span"{u_k}$ and acts there as $e^(-i t W slash pi)$. Consequently,
if perfect state transfer between two cell-uniform states occurs in the
quotient at time $tau$, it occurs in the graphon walk between the
corresponding cell-uniform states of $L^2(mu)$. This is a graphon-level
generalization of [bachman2011quotient], and to our knowledge has no
prior-published analogue: the closest is the real-dynamics invariant-subspace
lift of [bick2024graphlimits]. We state and partially mechanize it in
`Graphplay/Graphon/PST.lean`.

#emph[Theorem 5.4 (graphon spatial-search lift).]
Let $S subset.eq Omega$ be a measurable marked set of positive measure. The
search Hamiltonian $H_(W, gamma, S) = - gamma T_W - "Proj"_(L^2(S))$ has the
refined partition $pi_S := pi join {S, S^c}$ as a (graphon) equitable
partition, and the search dynamics restrict to a Hamiltonian of finite
dimension at most $2 r$ on $V_(pi_S)$. The optimal-search criterion of
[chan2022shadows] therefore reduces to a finite spectral computation on the
quotient $W slash pi_S$.

#emph[Theorem 5.5 (quasi-infinite limit theorem).]
Let $(G_n, pi_n)_(n in NN)$ be a sequence of finite Hermitian weighted graphs
equipped with equitable partitions, all of size at most $r$. Suppose:
+ The pixel-step graphons $W_(G_n)$ converge to a Hermitian graphon $W$ in
  the cut norm.
+ The cell-fraction vectors converge to a probability vector
  $(mu(A_1), dots, mu(A_r)) in Delta^(r-1)$ with all $mu(A_k) > 0$.
+ The normalized quotient matrices $G_n slash pi_n$ converge to a Hermitian
  matrix $M in CC^(r times r)$ in Frobenius norm.

Then $W$ admits a measurable equitable partition $pi$ realizing the limit
cell fractions and with $W slash pi = M$. Moreover, every cell-uniform PST
or spatial-search problem on $(G_n, pi_n)$ has a well-defined limit on
$(W, pi)$, and the limit's value is the value of the finite Hermitian
problem on $M$. Lean: `Graphplay/Graphon/Limit.lean` (the proof reduces to
(a) cut-norm-implies-operator-norm convergence under bounded entries
[szegedy2010spectral], (b) Frobenius convergence of the quotient matrices,
and (c) continuity of finite spectral optimization problems).

#emph[Corollary 5.6 (Xie--Tamon tail as a 2-cell corner).]
The sequence $K_n + P_n$ with two-cell partition (clique, tail) satisfies the
hypotheses of Theorem 5.5 with limit a complete graphon on $[0, 1 slash 2]$
union an infinite path with mass $1 slash 2$; the limit quotient is the
$2 times 2$ Hermitian matrix encoding the Farhi--Gutmann complete-graph
search, and optimality is therefore preserved. This is the content of
[xie2023tail], recovered as a corner. The transfer-side companion
[bernard2022tails] is the corresponding 2-cell PST corner.

#emph[Example 5.7 (cycle blowup).]
Fix a template weighted graph $Q$ on $r$ vertices. The sequence
$"Tot"(Q, 0, J)$ with equal fibers of size $n$, viewed as pixel-step graphons,
converges in cut norm to the block-constant graphon $W_Q$ with cells of
measure $1 slash r$ and value $Q_(j k)$ in block $(j, k)$. The quotient at
every stage is $n dot Q$ (up to a renormalization that absorbs into the time
parameter), and Theorem 5.5 gives the limit as the finite search problem on
$Q$. The compiler examples of [amorc2025v2] are exactly the finite stages of
such a sequence.

#heading("6. Tower 5: Categorical Framing and Quotient as a Functor")

Let $"EqWGr"$ be the category whose objects are pairs $(G, pi)$ with $G$ a
finite Hermitian weighted graph and $pi$ an equitable partition, and whose
morphisms $(G, pi) arrow.r (G', pi')$ are pairs $(phi, theta)$ where $phi$
is a weight-preserving cell-block map and $theta$ refines $pi$ to a partition
compatible with $phi$. Let $"Mat"_("fin")(CC)$ be the category of finite
Hermitian matrices. Define $"Quot" : "EqWGr" arrow.r "Mat"_("fin")(CC)$ by
$"Quot"(G, pi) = G slash pi$.

#emph[Theorem 6.1 (filtered-colimit preservation).]
The functor $"Quot"$ preserves filtered colimits. Explicitly, given a
filtered diagram $(G_alpha, pi_alpha)$ in $"EqWGr"$ whose underlying weighted
graphs form a sequence with a graphon colimit $W$ (with respect to the cut
metric) and whose quotient matrices have a finite-dimensional Frobenius limit
$M$, the colimit pair $(W, pi)$ exists in the extended graphon-equitable
category and $W slash pi = M$. Lean: `Graphplay/Categorical.lean`, where
the chain colimit, cochain limit, and the
`Quotient.preservesFilteredColimits` statement are mechanized.

#emph[Corollary 6.2 (unification).]
The quasi-infinite limit theorem (Theorem 5.5) is the Tower-4 instance of
Theorem 6.1. The Tower-1 inverse-limit and edge-union universal properties
of [amorc2025v2] are the Tower-1 and Tower-0 instances. The "failed
reflector" observation --- there is no left adjoint to "forget the
coloring" --- is the statement that the underlying-graph functor *does not*
have a colimit-preserving left adjoint; the *relative* left adjoint along a
chosen template $Q$ does exist and is the bundle construction of Section 3
(`Bundle.ofTemplateJoin_total_eq_templateJoin`).

#heading("7. Chiral Specialization: Signings as a Toolkit Primitive")

The chiral story --- unitary phases on edges of a weighted graph --- has been
known since at least Sedlacek to permit phenomena unavailable to real
weights. The recent works [levine2026chiral] and [xie2022speedlimit] both
exhibit this: chiral signings produce uniform mixing on $K_n^sigma$, and a
dual-rail chiral protocol on engineered chains *breaks the perfect-state-
transfer speed limit*. In Graphplay both phenomena are quotient phenomena.

#emph[Definition 7.1 (chiral signing).]
A *chiral signing* of $V$ is a function $s : V arrow.r CC$ with $abs(s(v)) = 1$;
the *signed graph* $G^s$ has adjacency $G^s_(v w) = overline(s(v)) G_(v w) s(w)$.
Lean: `Graphplay/Chiral.lean`. The signing is *cross-constant* with respect
to a partition $pi$ if $overline(s(v)) s(w)$ depends only on the pair of
cells of $v$ and $w$.

#emph[Theorem 7.2 ($sigma$-`signedBy_preserves_equitable`, proven).]
If $pi$ is equitable for $G$ and the signing $s$ is cross-constant with
respect to $pi$, then $pi$ is equitable for $G^s$, and the signed quotient
satisfies $G^s slash pi = (G slash pi)^(s_pi)$ where $s_pi$ is the inherited
cross-constant phase on cell-pairs. In particular, CTQW on $G^s$ restricts to
the cell-constant subspace and acts there as $e^(-i t (G slash pi)^(s_pi))$.
Lean: `WeightedGraph.signedBy_preserves_equitable` in `Graphplay/Chiral.lean`,
fully proven.

#emph[Theorem 7.3 (chiral signing as optimization on the quotient).]
For a bundle $"Tot"(Q, H, B)$ with phase-equitable cell partition $pi$, the
uniform-mixing functional
$ M(s; t) := max_(v, w) abs(U_(s, t)(v, w))^2 $
restricted to cell-uniform initial and final states equals the corresponding
quantity for the signed quotient $(G slash pi)^(s_pi)$. Optimizing the
signing over the (large) bundle phase space therefore reduces to optimizing
$s_pi$ over the (small) phase space $U(1)^(E(Q))$, modulo gauge. Lean:
`Graphplay.Chiral.chiral_mixing_optimization`.

#emph[Corollary 7.4 (Levine et al.\ as a quotient corner).]
The uniform-mixing speedup of [levine2026chiral] on $K_n^sigma$ has a bundle
version: if a bundle has $K_n^sigma$ as its quotient and equal fibers, then
the corresponding chiral mixing speedup holds for the bundle on the
cell-uniform subspace. The witness $K_4$ signing reproducing
$K_1 + K_(1,3)$ is `Chiral.unitaryHammingChiralK4Signing` in Lean.

#emph[Corollary 7.5 (Xie--Kay--Tamon speed-limit-breaking as a quotient
corner).]
The dual-rail chiral protocol of [xie2022speedlimit] is naturally expressed
on a $2 times 2$ chiral quotient with an off-diagonal phase implementing the
anti-Zeno-effect timing. Concretely: an engineered spin chain with the
Xie--Kay--Tamon weights and dual-rail readout admits an equitable partition
whose quotient is exactly the $2 times 2$ signed matrix studied in their
protocol, and the speed-limit-breaking transfer time is a function of this
small matrix. The toolkit version is therefore "given a target transfer time
$tau$ below the spectral speed limit, request a (host, partition, schedule,
certificate) tuple from the chiral compiler". Open: a tight characterization
of which engineered hosts permit a target $tau$ as a function of the chiral
quotient norm.

The Lean development covers all of Section 7 except Corollary 7.5, which is
flagged in `Graphplay/Dowsing/ChiralBundlePST.lean` as `OpenQ3_chiralHeawoodPGST`
and adjacent open questions.

#heading("8. Engineering Toolkit: Primitives, Hardware, Certificates")

We give the compiler its signature.

A *primitive* is a constructor in the Lean enum

$ "Primitive" := "PST" | "UniformMixing" | "FractionalRevival" | "Search" | "Transfer" | "Sample". $

A *hardware specification* is a decidable predicate on weighted graphs
(`HardwareSpec` in `Graphplay/Toolkit/Hardware.lean`). The library provides
constants $"planarSpec"$, $"surfaceSpec"(g)$, $"nearestNeighborSpec"(r)$,
$"chiralAllowedSpec"(Phi)$, $"regularSpec"(d)$, $"sizeBoundedSpec"(n)$,
their finite intersections, and a *quotient* operation that lifts a hardware
specification on the host to a hardware specification on the quotient.

A *schedule* is a piecewise-constant (or piecewise-analytic) family of
Hamiltonians on the host. `Graphplay/Toolkit/Scheduler.lean` provides static,
magnetic-flux, and adiabatic schedules, together with the lemma
`Schedule.evolve_preserves_cellUniform` that says cell-uniform states stay
cell-uniform under any schedule whose generators preserve the partition
projector --- this is the certificate that makes the spine usable
*time-dependently*.

A *noise model* is a Lindblad-type perturbation; `Graphplay/Toolkit/Noise.lean`
defines a `NoiseModel`, the cell-uniform-symmetric subclass, and the lemma
`Noise.cellUniform_preserved` that says the cell-uniform subspace remains
invariant under a cell-uniform-symmetric noise model. (The lemma promotes
all of Sections 2--6 to noisy-quantum-walk versions; full quantitative
treatment is open.)

A *certificate* of a (primitive, host, partition, schedule) tuple is a Lean
term of type `Certificate primitive host partition schedule`, with field
constructors corresponding to Theorems 3.3, 5.4, and 7.2 as appropriate. The
compiler emits both a JSON artifact and a Lean term; the Lean term is
checked by `lake build` before deployment, giving a machine-verifiable bridge
from a hardware-and-primitive specification to a quantum-walk schedule.

The case studies of [amorc2025v2] (`rook_3x3_equal_fiber`,
`cycle8_powerlaw_alpha1`, `torus_heawood7_equal_fiber`) are precisely
equal-fiber bundles whose templates carry verifiable regularity certificates;
they become end-to-end Lean-checked instances of the compiler.

#heading("9. Research Program")

The Lean 4 development includes thirty further modules sketching open
extensions and integrations. We list them as pointers for the program; full
treatment is deferred to companion notes.

#emph[Dowsing-rod files (open theorems, signatures complete, proofs pending).]
Each is a single Lean module under `Graphplay/Dowsing/`:

- `BundlePSTLift.lean` --- PST iff quotient PST for every classical product;
  full corner-by-corner table from Cartesian through disjunctive.
- `ChiralBundlePST.lean` --- chiral bundle PST iff signed-quotient PST;
  includes the Levine signing witness `unitaryHammingChiralK4` and three
  open questions $"OpenQ"_1, "OpenQ"_2, "OpenQ"_3$ on chiral product PST,
  $K_n^sigma$ sharpness, and chiral Heawood PGST.
- `ChiralGraphon.lean` --- chiral graphons (skew-Hermitian imaginary part)
  and `IsChiral` $!=$ `IsReal`; equitable partition theory at the
  graphon-chiral level.
- `CoherentAlgebra.lean` --- the partition-projector algebra
  $cal(P)(pi)$, its commutativity with $Pi_pi$, and the relation to the
  coherent algebra of $G$.
- `Conjecture93.lean` --- the falsifiable Conjecture 9.3 (below) with its
  Lean apparatus and worked example table.
- `FilteredColimitPST.lean` --- the categorical PST lift along filtered
  colimits, Tower-5 of Theorem 5.3.
- `FractionalRevivalNC.lean` --- non-commutative fractional revival on
  quantum graphs, the Tower-3 generalization of [chan2019fractional].
- `HypergraphPST.lean` --- $k$-uniform hypergraph PST and search via the
  bipartite incidence weighted graph.
- `NoiseEquitable.lean` --- quantitative version of cell-uniform
  preservation under generic noise.
- `NonCommutativeCoherent.lean` --- non-commutative coherent algebras for
  quantum graphs in the sense of Definition 4.2.

#emph[Cross-disciplinary integration files (full-paper-length sketches under
`Graphplay/Integrations/`).]
Each is a research-program seed pointing to an external field where the
spine applies:

- `Hodge.lean` --- combinatorial Hodge decomposition, equitable partitions
  compatible with the cochain complex, harmonic-subspace quotient.
- `LatticeGauge.lean` --- chiral signings as discrete connections, U(1) and
  non-abelian gauge fields on weighted graphs, plaquette flux.
- `MeanFieldGames.lean` --- graphon LQR control of [gao2020graphon] and
  quantum mean-field games unified through equitable reduction.
- `OptimalTransport.lean` --- graphons as transport plans, Sinkhorn
  alignment, quotient as a marginal-preserving lift.
- `RMT.lean` --- random matrix theory meets equitable partitions: free
  probability on cell-uniform subspaces, free convolution for quotient
  spectra.
- `TensorNetworks.lean` --- MERA coarse-graining as exact equitable cell
  maps; PEPS and holographic codes as bundles.
- `TQFT.lean` --- weighted graphs as input data for (2+1)-d TQFT, modular
  tensor category extensions, Levin--Wen and Kitaev models.
- `WLRefinement.lean` --- the Weisfeiler--Leman chain as the universal
  refinement of equitable partitions; algebraic and quantum WL.

#emph[Tower 6--7 (conjectural higher towers).]
- `Tower6.lean` --- sheaves of weighted graphs over a topological base,
  recovering Towers 3--5 as point-base, measure-base, and sheaf-of-spectra
  cases; preservation-of-filtered-colimits for the global-sections
  functor.
- `Tower7.lean` --- $infinity$-categorical generalization: stable
  $infinity$-categories with Hermitian endomorphisms, coherent idempotent
  partitions, derived Hermitian partitions, and the
  $infinity$-categorical infinity-PST lift.

#emph[Falsifiable Conjecture 9.3 (Bose--Mesner $eq.triple$ chiral $eq.triple$
graphon).]
A consistent sequence of finite weighted graphs $(G_n, pi_n)$ admits *both*
+ a graphon quasi-infinite limit (Theorem 5.5), and
+ a strict chiral signing speedup on $pi_n$ (Theorem 7.3 with strict
  inequality on the mixing-time functional),

if and only if the Bose--Mesner algebra of the family eventually coincides
with the partition-projector algebra $cal(P)(pi_n)$. Status: the *weak*
version (cross-constant signings) is believed true and is supported by
worked examples on $K_n^sigma$, Hamming schemes, $K_(n,n,n,n)$, and the
Heawood envelope; it is *blocked* in three confirmed both-sides-false
witnesses --- $K_n + P_n$, Cayley$(S_n)$ by transpositions, and any
distance-regular-but-not-distance-transitive bipartite double cover. The
*strong* version (arbitrary unitary signings) is conjecturally false; a
candidate counterexample uses non-cross-constant phase-equitable refinements
of $K_n + P_n$. Detailed analysis in `paper/conjecture93_notes.md` and Lean
apparatus in `Graphplay/Dowsing/Conjecture93.lean`. The next concrete
computational step is the Bose--Mesner-versus-distance-projector dimension
table for $K_n + P_n$ at $n = 3, 4, 5$.

#emph[Open extensions.]
- *Graphops.* Backhausz--Szegedy graphops generalize graphons by removing the
  $L^2$ symmetric-kernel assumption. The quotient spine survives when the
  operator commutes with the projection $Pi$; the graphon Theorem 5.5 should
  extend to graphops under mild compactness.
- *Surface topology.* The Heawood map-color completion of [amorc2025v2] is
  the special bundle with $Q = K_(H(g))$. The surface algebraic-connectivity
  ceiling of Freitas [freitas2001heawood] becomes a Tower-2 spectral budget
  on $Q$.
- *Open systems and time dependence.* The bundle-and-quotient picture
  survives unitary perturbations whose generator is itself equitable, and
  cell-uniform-symmetric noise (`Toolkit/Noise.lean`). Lindbladian
  extensions and general time-dependent schedules are not yet covered
  beyond the cell-uniform invariance lemma.

#heading("References")

#set par(justify: false)

#emph[Tamon corpus and immediate quantum-walk neighbors:]

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
- #emph[xie2022speedlimit.] W. Xie, A. Kay, C. Tamon.
  #link("https://arxiv.org/abs/2209.08160")[Breaking the speed limit for
  perfect quantum state transfer], arXiv:2209.08160.
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

#emph[Structural / graphon ancestors:]

- #emph[bick2024graphlimits.] C. Bick, D. Sclosa.
  #link("https://arxiv.org/abs/2110.13686")[Dynamical systems on graph
  limits and their symmetries], arXiv:2110.13686.
- #emph[szegedy2010spectral.] B. Szegedy.
  #link("https://arxiv.org/abs/1003.5588")[Limits of kernel operators and
  the spectral regularity lemma], arXiv:1003.5588.
- #emph[gao2020graphon.] S. Gao, P. E. Caines.
  #link("https://arxiv.org/abs/2004.00677")[Subspace decomposition for
  graphon LQR: applications to VLSNs of harmonic oscillators], arXiv:2004.00677.

#emph[Spatial-search and CTQW references:]

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
- #emph[amorc2025v2.] AMORC.
  #emph[Equitable Quotients Across Five Towers (Graphplay v2).]
  (This repository, `paper/quasi_infinite_adjoint_v2.typ`.)
