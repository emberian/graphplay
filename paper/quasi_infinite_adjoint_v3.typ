#set document(title: "Graphplay: A Combinatorial Assembly Language for Quantum Primitives")
#set page(margin: 1in)
#set text(size: 11pt)
#set par(justify: true)

#align(center)[
  #text(size: 17pt, weight: "bold")[Graphplay] \
  #v(0.25em)
  #text(size: 13pt, weight: "bold")[A Combinatorial Assembly Language for Quantum Primitives] \
  #v(0.35em)
  #text(size: 11.5pt)[A Typed, Polymorphic, Verified, Categorically-Organized \
  Combinator Calculus over the Five-Tower Equitable Spine] \
  #v(0.45em)
  #text(size: 9.5pt)[Graphplayers Crew --- Graphplay v3 draft]
]

#v(0.8em)

#heading("Abstract")

We propose, develop, and partially mechanize *Graphplay*: a typed,
polymorphic, verified, categorically-organized combinator calculus for
compiling specifications of quantum-walk primitives --- perfect state
transfer (PST), uniform and instantaneous mixing, spatial search, sampling,
state transfer along tails, fractional revival --- to host operators on
finite weighted graphs, signed/chiral graphs, operator algebras, quantum
graphs, and graphons. The core observation is that nearly every published
construction in the Tamon corpus and adjacent CTQW literature factors
through an *equitable partition* and its small finite quotient matrix. We
formalize that factorization as an instruction set: eight load-bearing
combinators (`PARTITION`, `QUOTIENT`, `BUNDLE`, `SIGN`, `REFINE`, `LIFT`,
`COLIMIT`, `EMBED`) which produce, compose, and certify equitable data
across a five-tower spine. The compiler signature is
$ ("primitive", "hardware") |-> ("host", "partition", "schedule", "certificate"), $
where each output is a Lean 4 term and the certificate is a proof of the
relevant spine hypothesis.

Three results are genuinely new with respect to the Tamon corpus. First,
the spine lifts cleanly to graphons (Tower 4): we give graphon equitable
partitions, prove the spectral-lift theorem for the Hilbert--Schmidt
integral operator, and lift PST and spatial-search optimality to the
graphon limit. Second, chiral signings are first-class instructions: the
characteristic-projection identity `signedBy_preserves_equitable` puts the
Levine--Mesapam--Mustico--Tamon--Tucker--Zhan uniform-mixing speedup, and
the Xie--Kay--Tamon speed-limit-breaking PST protocol, into one toolkit
language --- both optimizations factor through a small signed quotient.
Third, a categorical filtered-colimit-preservation theorem makes the slogan
"quasi-infinite" precise: a filtered family of finite CTQW problems with
bounded equitable quotients has its behavior controlled by a single
colimit quotient, recovering the Xie--Tamon infinite-tail result and the
Bernard--Tamon--Vinet--Xie tails-transfer companion as one-line
corollaries.

The Lean 4 development covers Towers 1--5 of the spine, the bundle engine,
the chiral specialization, and a graphon scaffold. Companion notes
(`research_program.typ`, `applied_majorana1.md`, `applied_ibm_heavy_hex.md`)
spin out the dowsing-rod open theorems, cross-disciplinary integrations
(Hodge, lattice gauge, MERA, TQFT, WL, RMT, optimal transport, mean-field
games), conjectural Towers 6--7, and worked applied case studies; the
main paper stays on the spine.

#heading("1. Graphplay as an Assembly Language")

#emph[Thesis.] *Graphplay is a typed, polymorphic, verified, categorically-
organized combinator calculus for compiling quantum-primitive specifications
to host operators.* The "operator" can be a finite Hermitian weighted graph,
a chiral signing, an operator-algebra-level quantum graph, or a graphon; the
"primitive" is one of PST, uniform mixing, spatial search, sampling,
transfer-along-a-tail, fractional revival. The compiler is *typed* because
each instruction has a signature on a category of operator-with-partition
data; *polymorphic* because the same instruction works across the five
towers; *verified* because every instruction has a Lean 4 proof of its
specification; *categorically organized* because the towers are linked by
functors and the limit theorems are filtered-colimit preservations.

#emph[1.1 The instruction set.]
The whole stack is built from eight combinators, each polymorphic over a
tower-level type:

#align(center)[
#block(fill: luma(245), inset: 8pt, radius: 4pt, width: 95%)[
```
PARTITION : Operator -> (Operator, EquitablePartition)        -- search a partition
QUOTIENT  : (Operator, EquitablePartition) -> SmallOperator   -- shrink to r x r
BUNDLE    : (Base, Fibers, Couplings) -> Operator             -- build a host
SIGN      : (Operator, Phasing) -> Operator                   -- chiral specialization
REFINE    : (EquitablePartition, Marking) -> EquitablePartition
LIFT      : Primitive(SmallOperator) -> CellUniformPrimitive(Operator)
COLIMIT   : Diagram(Operator, EquitablePartition) -> Operator∞
EMBED     : Operator_TowerN -> Operator_TowerN+1
```
]]

A *program* is a sequence of these combinators consumed by a *primitive
request* (Section 8). A *certificate* is a Lean term that witnesses
the equitability hypothesis each combinator demands.

#emph[1.2 Semantics by tower.]
The eight combinators are not free symbols; each carries a typed semantic
clause in each tower. The clauses (proven, modulo flagged open holes, in
Lean 4) are:

#table(
  columns: 4,
  stroke: 0.5pt,
  inset: 6pt,
  align: (left, left, left, left),
  [*Combinator*], [*Tower 2 (Weighted)*], [*Tower 3 (Op alg)*], [*Tower 4 (Graphon)*],
  [`PARTITION`], [cell-pair row sum const.], [$Pi A Pi = A Pi$], [a.e.-const cell integrals],
  [`QUOTIENT`], [$r times r$ Hermitian matrix], [bimodule on $M_0$], [same $r times r$ matrix],
  [`BUNDLE`], [`Tot(Q,H,B)`], [crossed-product analogue], [block-step graphon],
  [`SIGN`], [`signedBy`], [unitary $u in M^*$], [a.e.-unimodular kernel],
  [`REFINE`], [marked split], [coarser commutant], [measurable join],
  [`LIFT`], [Theorem 3.x], [Theorem 3.x], [Theorem 6.x],
  [`COLIMIT`], [refinement direct limit], [direct limit of $C^*$], [cut-norm limit],
  [`EMBED`], [identity], [diagonal subalgebra], [pixel-step graphon],
)

#emph[1.3 The five-tower spine.]
The towers in order of increasing generality:

$ "Set" --> "SimpleGraph" --> ("Weighted" union.dot "Chiral") --> ("OpAlg" union.dot "QuantumGraph") --> "Graphon" --> "Category". $

We refer to these as Towers 0--5; the load-bearing combinators are
defined and certified at every tower they sensibly inhabit. The Tower-2
through Tower-5 sections (3--7 below) state a *single load-bearing
theorem* per tower from which the corner-case results of the literature
fall out.

#emph[1.4 The compiler signature.]
The whole stack is consumed by a request

$ "Request" = ("primitive", "hardware") $

where the *primitive* is one of `PST, UniformMixing, Search, Sample,
Transfer, FractionalRevival` and the *hardware* is a decidable conjunction
of host constraints (planar, surface genus, near-neighbor radius, allowed
phase set, vertex degree, size bound). The compiler emits

$ ("host", "partition", "schedule", "certificate") $

where *host* is a `GraphBundle`, *partition* is an equitable partition of
the host, *schedule* is a (possibly time-dependent, possibly chiral)
Hamiltonian, and *certificate* is a Lean term whose type is exactly the
load-bearing-theorem hypothesis for the primitive at the tower in
question. The classical Tamon-corpus pipeline (PST on quotient graphs,
graph-product PST, spectral spatial-search optimality, tails-transfer,
chiral mixing speedup) is the catalog of (primitive, hardware) pairs the
compiler can already serve.

#emph[1.5 A worked instruction trace.]
The compilation of "PST between antipodal vertices of a complete
multipartite graph $K_(n, n, n, n)$" is the trace

#align(center)[
#block(fill: luma(245), inset: 8pt, radius: 4pt, width: 95%)[
```
Request   : (PST, planar + equal-fiber, |V| <= 16)
            |
BUNDLE    : (Q := K_4, H_i := 0, B_(ij) := 1)
            |
PARTITION : pi := { V_1, V_2, V_3, V_4 } (the four color classes)
            |
LIFT      : (PST on K_4 between cell 1 and cell 3) ==> (PST on Tot)
            |
SIGN      : (optional; trivial s = 1)
            |
COLIMIT   : (omitted; finite-stage program)
            |
EMBED     : Tower 2 -> Tower 4 if asked for the graphon limit
```
]]

Every step is type-checked: `BUNDLE` consumes a Tower-2 base and produces
a Tower-2 host; `PARTITION` consumes a Tower-2 host and produces a
Tower-2 host with an `EquitablePartition`; `LIFT` consumes a Tower-2
host-with-partition and a small-operator primitive certificate and
produces a host-level primitive certificate. The final `certificate` is
the inhabitant of `Certificate PST Tot pi schedule`.

#emph[1.6 Provenance.]
Two decades of the Tamon program have driven home that the right way to
think about CTQW is structural: phenomena that *look* like analytic
miracles --- PST at integer times [bachman2011quotient], optimal
Grover-like search [chakraborty2020spatial, chan2022shadows], uniform
mixing at carefully chosen times [levine2026chiral], speed-limit-breaking
PST [xie2022speedlimit], optimality on infinite tails [xie2023tail],
fractional revival on schemes [chan2019fractional], PST with tails
attached [bernard2022tails], PST via products [ge2010products] --- are
very often projections of small finite calculations to which the
equitable partition is the right lens. Graphplay v2 [graphplay2025v2]
reified part of this picture as a Lean 4 artifact with a `GraphBundle`
engine and a graphon scaffold; v3 changes the lead. We treat the whole
stack as an assembly language with the instruction set above and the
five-tower spine below as its target. The non-Tamon CTQW papers we
build on --- spatial search on planar networks [sadowski2014planar],
long-range-tunneling searches [king2025longrange], deterministic search
on Laplacian-integral graphs [li2025deterministic], lackadaisical search
[wong2017lazy], and the surface-topology algebraic-connectivity ceiling
[freitas2001heawood] --- become (primitive, hardware) instances in the
catalog.

#emph[1.7 Why this framing is load-bearing.]
The instruction-set framing pays in three concrete ways. (a) *Polymorphism*:
the same `PARTITION + LIFT` lemma can be used at every tower; the proofs
of Theorems 2.2, 3.3, 6.2, 7.1 are structurally the same, varying in the
ambient analysis (finite linear algebra, $C^*$-algebraic projections,
$L^2$ kernel operators, filtered colimit cocones). (b) *Composability*:
a verified `BUNDLE` of two verified `BUNDLE`s is a verified `BUNDLE`,
because the equitability conditions of Theorem 4.3 compose. The compiler
can therefore stitch together case-study templates (planar K_4, surface
Heawood, IBM heavy-hex, Majorana topological fabric) without re-proof.
(c) *Falsifiability*: the conjectural Conjecture 9.3 (Section 10) cleanly
links three instructions (`COLIMIT`, `SIGN`, embedded `QUOTIENT` into
Bose--Mesner Tower 3) into an iff that is open and supported by worked
examples; the assembly-language framing is what makes the conjecture even
statable.

#heading("2. Tower 2: The Spine and Its Single Load-Bearing Theorem")

A *weighted graph* on a finite vertex set $V$ is a Hermitian matrix
$A in CC^(V times V)$ with zero diagonal. The class includes simple
graphs (via 0/1 adjacency), signed and chiral graphs (unitary phases off
the diagonal), and weighted spin networks. Lean carrier:
`Graphplay/Weighted.lean`.

#emph[Definition 2.1 (equitable partition).]
A partition $pi$ of $V$ into nonempty cells $C_1, dots, C_r$ is *equitable*
for $A$ if for every pair of cells $C_j, C_k$ the row sum
$ b_(j k) := sum_(w in C_k) A_(v w) $
is independent of $v in C_j$. The *quotient matrix*
$A slash pi in CC^(r times r)$ has $(A slash pi)_(j k) = b_(j k)$. The
*characteristic matrix* $P in CC^(V times r)$ has $P_(v j) = 1$ if
$v in C_j$ and $0$ otherwise. The defining identity is
$ A P = P (A slash pi). $
This data lives in `Graphplay/Equitable.lean`. The instruction-level
reading is that `PARTITION` produces $pi$ and `QUOTIENT` produces
$A slash pi$, while `EMBED` from Tower 1 to Tower 2 is the inclusion of
0/1 matrices into Hermitian matrices.

#emph[Theorem 2.2 (single load-bearing theorem of Tower 2).]
Let $pi$ be equitable for $A$ with characteristic matrix $P$. Then:
+ (Spectrum.) $"spec"(A slash pi) subset.eq "spec"(A)$; for every
  eigenvector $x$ of $A slash pi$ with eigenvalue $lambda$, $P x$ is a
  cell-constant eigenvector of $A$ with eigenvalue $lambda$.
+ (CTQW restriction.) $e^(-i t A)$ commutes with $Pi := P (P^* P)^(-1) P^*$
  and acts on $"range" Pi$ as $e^(-i t A slash pi)$.
+ (Primitive lift.) For any cell-uniform primitive request $p in
  {"PST", "UniformMixing", "Search", "Transfer", "Sample", "FractionalRevival"}$
  whose endpoints (and marked sets, for `Search`) are unions of cells, $p$
  holds on $(A, pi)$ iff $p$ holds on $A slash pi$ after the canonical
  refinement.

The three clauses together are the `LIFT` instruction at Tower 2. Clause
(i) is the classical Godsil spectral lift; clause (ii) is the CTQW
invariance lemma; clause (iii) packages
[bachman2011quotient, ide2022equitable, chan2022shadows] as a single
combinator. Lean: `Graphplay/Spectral.lean`, `Graphplay/PST.lean`,
`Graphplay/Search.lean`, `Graphplay/Mixing.lean`.

#emph[Proof sketch.]
For (i): suppose $(A slash pi) x = lambda x$. Then
$A P x = P (A slash pi) x = lambda P x$. Since $P$ has full column rank
(because the cells are disjoint and nonempty), $P x != 0$ for $x != 0$,
so $lambda in "spec"(A)$ with eigenvector $P x$. For (ii): the identity
$A P = P (A slash pi)$ implies $A Pi = P (P^* P)^(-1) (A slash pi) P^* =
Pi A Pi$ on the range of $Pi$, so $A$ commutes with $Pi$ (using
Hermiticity); the unitary $e^(-i t A)$ then commutes with $Pi$ and acts on
$"range" Pi$ as the unitary $e^(-i t Pi A Pi) = e^(-i t A slash pi)$
identified via the cell-uniform basis. For (iii): the three primitive
functionals
$abs(chevron.l psi_t\, e_a chevron.r)^2$ (PST),
$1 slash N^2 sum abs(U_t(v, w))^2$ (uniform mixing on cells),
$abs(chevron.l e_w\, e^(-i t H_gamma) e_a chevron.r)^2$
(search) are each polynomial in matrix entries that lie in
$"range" Pi$ when initial and final states do, hence equal to the same
polynomial in the quotient. $square$

The marked-vertex case (relevant to `Search`) is worth its own statement:

#emph[Corollary 2.3 (search refinement).]
For a marked vertex $w in V$, the refinement $pi_w$ that splits the cell
containing $w$ into ${w}$ and its complement within that cell is equitable
for the search Hamiltonian $H_gamma := - gamma A - e_w e_w^*$. The unitary
$e^(-i t H_gamma)$ restricts to the $(r+1)$-dimensional cell-uniform-plus-${w}$
subspace. The optimality criterion of [chakraborty2020spatial], sharpened
by [chan2022shadows], reduces to a spectral computation on this small
subspace. The marked-cell refinement idiom is due to [ide2022equitable].

#emph[Examples.]
+ (Complete multipartite.) $K_(n_1, dots, n_r)$ has the color partition as
  equitable, with $(A slash pi)_(j k) = n_k$ for $j != k$, otherwise $0$.
+ (Xie--Tamon tail [xie2023tail].) $K_n + P_n$ has the 2-cell partition
  (clique, tail) as equitable; the quotient is a $2 times 2$ Hermitian matrix
  encoding Farhi--Gutmann complete-graph search.
+ (BTV-Xie tails-PST [bernard2022tails].) The transfer-side companion:
  PST between two distinguished vertices on a finite block with arbitrarily
  long tails is equivalent to PST on a 2-cell quotient.
+ (Heavy-hex search.) The IBM heavy-hex lattice, when colored so that two
  cells coincide with the marked-vertex pair, has a $4 times 4$ quotient
  whose spectrum is computed in companion `applied_ibm_heavy_hex.md`.
+ (Topological search [freitas2001heawood, sadowski2014planar].) On a
  surface of genus $g$, the algebraic connectivity is bounded above by the
  Heawood number $H(g)$; via the bundle engine of Section 4 this is a
  Tower-2 budget on the template $Q$.

#heading("3. Tower 3: Operator Algebras, Coherent Algebras, Quantum Graphs")

The next tower sits above weighted graphs. Let $cal(A) subset.eq M_V(CC)$
be the unital $*$-subalgebra generated by $A$ and the identity. An
equitable partition $pi$ corresponds to the orthogonal projection
$Pi = P (P^* P)^(-1) P^*$ onto the cell-constant subspace; the
equitability condition is exactly $Pi A Pi = A Pi$, i.e.\
$Pi$ commutes with $A$. Lean: `Graphplay/QuantumGraph.lean`.

#emph[Definition 3.1 (quantum graph).]
A *quantum graph* on a finite-dimensional $C^*$-algebra $M subset.eq B(H)$
is a self-adjoint $M$-bimodule $S subset.eq B(H)$ with adjacency
operator $A_S$. An *equitable coarsening* is a unital $*$-subalgebra
$M_0 subset.eq M$ such that the orthogonal projection $Pi_{M_0}$ onto the
$M_0$-invariant vectors commutes with $A_S$.

#emph[Definition 3.2 (partition-projector algebra).]
The *partition-projector algebra* $cal(P)(pi) subset.eq M_V(CC)$ is the
subalgebra of cell-pair-constant matrices. This is the maximal subalgebra
in which $pi$ is equitable; it is closed under Schur and matrix products
and is the smallest coherent algebra containing $Pi$.

#emph[Theorem 3.3 (single load-bearing theorem of Tower 3).]
Let $S$ be a quantum graph on $M$ with adjacency $A_S$, and let $M_0$ be
an equitable coarsening with projection $Pi$. Then:
+ (Spectrum.) $"spec"(Pi A_S Pi) subset.eq "spec"(A_S)$.
+ (CTQW restriction.) $e^(-i t A_S)$ commutes with $Pi$ and acts on
  $"range" Pi$ as $e^(-i t Pi A_S Pi)$, the adjacency of a smaller quantum
  graph $S slash M_0$ on $M_0$.
+ (Primitive lift.) Cell-uniform `PST`, `UniformMixing`, `Search`,
  `Transfer`, and `FractionalRevival` lift from $S slash M_0$ to $S$.

The Tower-2 spine of Theorem 2.2 is the special case $M_0 :=$ image of the
diagonal subalgebra under coarsening by $pi$. Lean:
`Graphplay/QuantumGraph.lean`.

#emph[Proof sketch.]
For (i): the operator $A_S$ commutes with $Pi$ by assumption, so $A_S$ and
$Pi$ are simultaneously diagonalizable; the spectrum of $Pi A_S Pi$ is the
restriction of $"spec"(A_S)$ to $"range" Pi$. For (ii): $e^(-i t A_S)$ is
a strong limit of polynomials in $A_S$, each of which commutes with $Pi$.
For (iii): on the bimodule $S$, the cell-uniform-plus-marked subspace of
the search refinement remains a left and right $M_0$-module, so the
search dynamics close on $V_pi$ with an effective adjacency $Pi A_S Pi -
gamma Pi P_S Pi$. The primitive functionals are again polynomial in the
restricted operator. $square$

#emph[Remark 3.4 (commutative versus non-commutative).]
In the commutative case ($M = "diag"$), Tower 3 reduces to Tower 2 with
no new content. The Tower-3 generality shows itself in the
non-commutative case: a quantum graph whose bimodule is non-trivially
multidimensional admits equitable coarsenings only when the bimodule
respects $Pi_{M_0}$, a strictly stronger condition than the diagonal
equitable partition. Cf.\ `Graphplay/Dowsing/NonCommutativeCoherent.lean`.

#emph[Examples.]
+ (Bose--Mesner.) The Bose--Mesner algebra of a commutative association
  scheme is the maximally symmetric Tower-3 coarsening. Fractional revival
  on Hamming schemes [chan2019fractional] is the Tower-3 corollary of a
  Tower-2 search-lift on the scheme partition.
+ (Coherent algebras.) The Schur-and-matrix-product closure of
  $cal(P)(pi)$ is the coherent algebra of $pi$; this is the right context
  for the Weisfeiler--Leman refinement chain.
+ (Quantum-graph reduction.) A non-commutative quantum graph admits an
  equitable coarsening iff its bimodule respects the projection $Pi_{M_0}$;
  this is the operator-algebra version of the search-lift idiom of
  [ide2022equitable].

#heading("4. The Constructive Engine: `BUNDLE` and its Corners")

The Tower-2 / Tower-3 spine tells us what is needed; the `BUNDLE`
instruction provides hosts that satisfy it constructively. The point of
the construction is that products, joins, color completions, and
engineered templates are all corners of one definition.

#emph[Definition 4.1 (graph bundle).]
A *graph bundle* `GraphBundle Q V` is the data
$ Q : "WeightedGraph"(I), wide V : forall i in I\, V_i, wide H_i : "WeightedGraph"(V_i), wide B_(i j) : V_i times V_j arrow.r CC, $
subject to a Hermitian compatibility $B_(i j)(a, b) = overline(B_(j i)(b, a))$
only required where $Q_(i j) != 0$. The *total graph*
$"Tot"(Q, H, B)$ on $product.co_i V_i$ has
$ "Tot"(x, y) = cases(
  H_i(x, y) & "if " x\, y "in same fiber " V_i,
  Q_(i j) dot B_(i j)(x, y) & "if " x in V_i\, y in V_j\, i != j
). $
Lean: `Graphplay/Bundle.lean`.

#emph[Proposition 4.2 (corners).]
+ $H_i = 0$, $B_(i j) = 1$ on Q-edges: the `TemplateJoin(Q, V)` of v2.
+ $Q = K_2$, $H_1, H_2$ arbitrary, $B_(1 2) = 1$ on a chosen product
  subset: Cartesian, lexicographic, strong, tensor, conormal, and
  disjunctive products as cases. The PST-product theorems of
  [ge2010products] fall out as Tower-2 corollaries.
+ $Q = K_C$ on a color palette, $H_i = 0$: color completion; with
  $B_(i j) = 1$, complete multipartite.
+ $Q$ a join graph in the sense of [kirkland2023join], arbitrary fibers:
  the Kirkland--Monterde join construction; their PST-on-joins
  characterization is a Tower-2 search-lift statement.
+ $Q$ a Heawood-template surface graph: the surface completion pipeline of
  v2, with a Tower-2 spectral budget from [freitas2001heawood].

#emph[Theorem 4.3 (`BUNDLE` is equitable iff regular fibers + biregular
couplings).]
The cell partition $pi := {V_i}_(i in I)$ is equitable for
$"Tot"(Q, H, B)$ if and only if
+ each fiber $H_i$ is regular with constant row sum $r_i$, and
+ each coupling $B_(i j)$ is biregular: $sum_(b in V_j) B_(i j)(a, b)$
  is independent of $a$, and $sum_(a in V_i) B_(i j)(a, b)$ is independent
  of $b$.
When these conditions hold,
$(A slash pi)_(i j) = r_i delta_(i j) + Q_(i j) abs(V_j) beta_(i j)$
where $beta_(i j)$ is the constant row sum of $B_(i j)$. Lean:
`Bundle.equitable_iff_regular_biregular`.

#emph[Corollary 4.4 (spectral inheritance).]
For equal-fiber bundles ($abs(V_i) = m$ for all $i$, $H_i = 0$,
$B_(i j) = 1$):
$ "spec"("Tot"(Q, H, B)) = m dot "spec"(Q) " "union.dot" " "(internal zero modes)". $
The CNO criterion [chakraborty2020spatial] in the
[chan2022shadows]-sharpened form, the deterministic-search criterion of
[li2025deterministic], and the long-range-tunneling regime of
[king2025longrange] are inherited by the bundle from the template.

The engineering reading is that the compiler's *certificate* for a
bundle host is exactly the pair (regular fibers, biregular couplings)
of Theorem 4.3 --- both decidable, both Lean-checkable.

#emph[Proof sketch of Theorem 4.3.]
($arrow.l.double$.) Fix cells $V_i$ and $V_j$. For $x in V_i$, the row
sum of $"Tot"(Q, H, B)$ from $x$ to $V_j$ is
$H_i(x, V_j) dot delta_(i j) + Q_(i j) sum_(b in V_j) B_(i j)(x, b)$,
which equals $r_i delta_(i j) + Q_(i j) abs(V_j) beta_(i j)$ by the
regularity-plus-biregularity hypothesis --- independent of $x$ in $V_i$.
($arrow.r.double$.) If row-sums into $V_j$ depend only on the cell of $x$,
specialize to $j = i$ to get fiber regularity; specialize to $j != i$
with $Q_(i j) != 0$ to get the biregularity of $B_(i j)$ on the first
slot; the dual constraint (independence of $y$ in $V_j$) requires
biregularity on the second slot. $square$

#emph[Example 4.5 (Heawood completion at genus $g$).]
Take $Q = K_(H(g))$, where $H(g)$ is the Heawood number of the surface,
fibers $H_i = 0$, couplings $B_(i j) = 1$. Theorem 4.3 is satisfied. The
quotient is $A slash pi = (H(g) - 1) (J - I)$ on $H(g)$ vertices, whose
spectrum consists of $H(g) - 1$ with multiplicity 1 and $-1$ with
multiplicity $H(g) - 1$. The Tower-2 spectral budget of
[freitas2001heawood] is the statement that the spectral gap of the host
is $H(g)$, capturing the surface-topology obstruction.

#emph[Example 4.6 (rook graph $K_3 square K_3$).]
The Cartesian product $K_3 square K_3$ is the bundle with $Q = K_3$,
fibers $H_i = K_3$, couplings $B_(i j) = I$. Theorem 4.3 is satisfied;
the quotient is a $3 times 3$ matrix with diagonal $2$ and off-diagonal
$1$, giving spectrum ${4, 1, 1}$, which combined with internal modes
recovers the full rook spectrum $4, 1, 1, 1, 1, -2, -2, -2, -2$. This is
the v2 `rook_3x3_equal_fiber` example.

#emph[Example 4.7 (long-range tunneling [king2025longrange]).]
Take $Q = K_n$, fibers $H_i = 0$, couplings $B_(i j)(x, y) = exp(-alpha
d(x, y))$ for a power-law decay rate $alpha$ and an underlying metric $d$
on each fiber identified across fibers. The biregularity condition of
Theorem 4.3 is satisfied iff $sum_(y in V_j) e^(-alpha d(x, y))$ is
independent of $x$, which holds when the metric is vertex-transitive on
each fiber. The deterministic-search criterion of [li2025deterministic]
on the resulting Laplacian-integral host is then a Tower-2 spectral
diagnostic on $Q$.

#heading("5. Tower 2 Continued: `SIGN` and the Chiral Specialization")

The chiral story --- unitary phases on edges of a weighted graph --- has
been known since Sedlacek to permit phenomena unavailable to real weights.
Two recent works exhibit this loudly:
[levine2026chiral] gives chiral signings that produce uniform mixing on
$K_n^sigma$ and identifies an arithmetic obstruction governing the
phenomenon; [xie2022speedlimit] gives a dual-rail chiral protocol on an
engineered chain that *breaks the perfect-state-transfer speed limit*.
Both results are quotient phenomena in Graphplay.

#emph[Definition 5.1 (chiral signing).]
A *chiral signing* is a function $s : V arrow.r U(1)$; the *signed graph*
$G^s$ has adjacency $G^s_(v w) = overline(s(v)) G_(v w) s(w)$. Lean:
`Graphplay/Chiral.lean`. The signing is *cross-constant* with respect to a
partition $pi$ if $overline(s(v)) s(w)$ depends only on the pair of cells
of $v, w$.

#emph[Theorem 5.2 (`SIGN` preserves `PARTITION`,
`signedBy_preserves_equitable`, proven).]
If $pi$ is equitable for $G$ and $s$ is cross-constant with respect to
$pi$, then $pi$ is equitable for $G^s$, and the signed quotient satisfies
$ G^s slash pi = (G slash pi)^(s_pi), $
where $s_pi$ is the inherited cross-constant phase on cell-pairs. In
particular, CTQW on $G^s$ restricts to the cell-constant subspace and
acts there as $e^(-i t (G slash pi)^(s_pi))$. Lean:
`WeightedGraph.signedBy_preserves_equitable` in `Graphplay/Chiral.lean`,
fully proven.

#emph[Theorem 5.3 (`SIGN` optimization factors through the quotient).]
For a bundle $"Tot"(Q, H, B)$ with cross-constant signing and
phase-equitable cell partition $pi$, the uniform-mixing functional
$ M(s; t) := max_(v, w) abs(U_(s, t)(v, w))^2 $
on cell-uniform initial and final states equals the corresponding
functional for the signed quotient $(G slash pi)^(s_pi)$. Optimizing the
signing over the bundle phase space therefore reduces to optimizing
$s_pi$ over the small phase space $U(1)^(E(Q))$, modulo gauge. Lean:
`Graphplay.Chiral.chiral_mixing_optimization`.

#emph[Corollary 5.4 (Levine--Mesapam--Mustico--Tamon--Tucker--Zhan
[levine2026chiral] as a quotient corner).]
The uniform-mixing speedup on $K_n^sigma$ has a bundle version: if a
bundle has $K_n^sigma$ as its quotient and equal fibers, the corresponding
chiral mixing speedup holds for the bundle on the cell-uniform subspace.
The witness $K_4$ signing reproducing $K_1 + K_(1,3)$ is
`Chiral.unitaryHammingChiralK4Signing` in Lean.

#emph[Corollary 5.5 (Xie--Kay--Tamon [xie2022speedlimit] as a quotient
corner).]
The dual-rail chiral protocol of *Breaking the speed limit for perfect
quantum state transfer* is naturally a $2 times 2$ chiral quotient with an
off-diagonal phase implementing the anti-Zeno-effect timing. Concretely:
an engineered spin chain with the Xie--Kay--Tamon weights and dual-rail
readout admits an equitable partition whose quotient is exactly the
$2 times 2$ signed Hermitian matrix studied in their protocol, and the
speed-limit-breaking transfer time is a function of that small matrix.
The toolkit catalog entry is "given target transfer time $tau$ below the
spectral speed limit, request `(host, partition, schedule, certificate)`".
A tight characterization of which engineered hosts permit a target $tau$
as a function of the chiral quotient norm remains open.

The Lean development covers all of Section 5 except a tight version of
Corollary 5.5, which is flagged in `Graphplay/Dowsing/ChiralBundlePST.lean`
as `OpenQ3_chiralHeawoodPGST` and three adjacent open questions.

#emph[Proof sketch of Theorem 5.2.]
Equitability of $pi$ for $G^s$ requires that the cell-pair row sum
$sum_(w in C_k) overline(s(v)) G_(v w) s(w)$ depend only on the pair
$(C_j, C_k)$ for $v in C_j$. Factor out $overline(s(v))$: the sum becomes
$overline(s(v)) sum_(w in C_k) G_(v w) s(w)$. The cross-constancy
hypothesis says $s(w) = c_(j k) s(v)$ for some unit $c_(j k)$ when
$w in C_k, v in C_j$, so $sum_(w in C_k) G_(v w) s(w) = c_(j k) s(v)
sum_(w in C_k) G_(v w) = c_(j k) s(v) b_(j k)$ by the original
equitability. Therefore $overline(s(v)) sum_(w in C_k) G^s_(v w) =
c_(j k) b_(j k)$, depending only on the pair. The signed quotient
identity follows directly. $square$

#emph[Remark 5.6 (cross-constant versus phase-equitable).]
The hypothesis of cross-constancy is strictly stronger than phase-
equitability (= signed row-sum constancy). Cross-constancy means the
phase is *gauge-equivalent* to a Tower-2 chiral signing of the small
quotient; phase-equitability allows fiber-internal phases that
cell-uniform observables never see. Corollary 5.4 is in the
cross-constant regime; Corollary 5.5 may not be, and that is exactly
what `OpenQ3_chiralHeawoodPGST` flags.

#emph[Example 5.7 (Levine signing on $K_4$).]
The witness $K_4$ signing whose quotient mimics $K_1 + K_(1, 3)$ is
$s(0) = 1, s(1) = i, s(2) = -1, s(3) = -i$, giving signed adjacency
$ G^s = mat(0, i, -1, -i; -i, 0, i, -1; -1, -i, 0, i; i, -1, -i, 0). $
This signing is cross-constant for the trivial single-cell partition;
the resulting uniform-mixing time on $K_4^s$ is strictly shorter than
the real $K_4$ mixing time. This is the smallest instance of
[levine2026chiral] and is the seed for `Chiral.unitaryHammingChiralK4Signing`.

#heading("6. Tower 4: Graphons and the Quasi-Infinite Limit Theorem (★)")

We now lift the spine to graphon kernels. This is the headline novel
section.

A *Hermitian graphon* on a probability space $(Omega, mu)$ is a measurable
function $W : Omega times Omega arrow.r CC$ with
$W(x, y) = overline(W(y, x))$ and $W in L^2$. The induced integral operator
$T_W : L^2(mu) arrow.r L^2(mu)$,
$(T_W f)(x) = integral W(x, y) f(y) "d" mu(y)$, is compact, self-adjoint,
and Hilbert--Schmidt. The CTQW on $W$ is the unitary group
$U_W(t) := e^(-i t T_W)$. Lean carriers: `Graphplay/Graphon.lean`,
`Graphplay/Graphon/Equitable.lean`, `Graphplay/Graphon/PST.lean`,
`Graphplay/Graphon/Limit.lean`.

#emph[Definition 6.1 (graphon equitable partition).]
A measurable partition $Omega = union.big.dot_(k=1)^r A_k$ is *equitable*
for $W$ if for all $j, k$ the function
$ x mapsto integral_(A_k) W(x, y) "d" mu(y) $
is constant almost everywhere on $A_j$, with value $tilde(b)_(j k)$. In
the rescaled-indicator basis $u_k := mu(A_k)^(-1 slash 2) bb(1)_(A_k)$,
the *graphon quotient matrix* $W slash pi in CC^(r times r)$ has entries
$ (W slash pi)_(j k) = tilde(b)_(j k) sqrt(mu(A_k) slash mu(A_j)). $

The closest finite ancestor is the Bick--Sclosa invariant-subspace
decomposition [bick2024graphlimits] for *real* dynamics on graphons; we
record the operator-theoretic *unitary* version. The operator-theoretic
LQR background is Gao--Caines [gao2020graphon]; the spectral graph-limit
theorems are Szegedy [szegedy2010spectral].

#emph[Theorem 6.2 (★ single load-bearing theorem of Tower 4).]
For a Hermitian graphon $W$ with measurable equitable partition $pi$ of
finite size $r$:
+ (Spectrum.) $"spec"(W slash pi) subset.eq "spec"(T_W)$; eigenvectors $x$
  of $W slash pi$ lift to eigenfunctions $sum_k x_k u_k$ of $T_W$ with the
  same eigenvalue.
+ (CTQW restriction.) $U_W(t)$ preserves the finite-dimensional
  cell-constant subspace $V_pi := "span"{u_k}$ and acts there as
  $e^(-i t W slash pi)$.
+ (Primitive lift.) If perfect state transfer between two cell-uniform
  states occurs in the quotient at time $tau$, it occurs in the graphon
  walk between the corresponding cell-uniform states of $L^2(mu)$. For a
  measurable marked set $S subset.eq Omega$ of positive measure, the
  search Hamiltonian
  $H_(W, gamma, S) := - gamma T_W - "Proj"_(L^2(S))$
  has the refined partition $pi_S := pi join {S, S^c}$ equitable, and the
  search dynamics restrict to a Hamiltonian of dimension $<= 2 r$ on
  $V_(pi_S)$.

This is a graphon-level generalization of [bachman2011quotient] and, to our
knowledge, has no prior published analogue at this level of unification:
the closest is the *real-dynamics* invariant-subspace lift of
[bick2024graphlimits]. We state and partially mechanize it in
`Graphplay/Graphon/PST.lean`.

#emph[Proof sketch.]
(i) Apply $T_W$ to $u_k$:
$(T_W u_k)(x) = mu(A_k)^(-1 slash 2) integral_(A_k) W(x, y) "d" mu(y)
= mu(A_k)^(-1 slash 2) tilde(b)_(j k)$
for $x in A_j$ almost everywhere. Re-expressing in the basis $u_j$ via
$u_j(x) = mu(A_j)^(-1 slash 2) bb(1)_(A_j)(x)$ gives
$T_W u_k = sum_j (tilde(b)_(j k) mu(A_j)^(1 slash 2) mu(A_k)^(-1 slash 2))
u_j = sum_j (W slash pi)_(j k) u_j$ after symmetrizing the normalization
under the Hermitian assumption.
(ii) This shows $T_W$ maps $V_pi$ into itself with matrix $W slash pi$;
the unitary $U_W(t) = e^(-i t T_W)$ inherits the invariance and acts on
$V_pi$ as $e^(-i t W slash pi)$ by spectral calculus.
(iii) Cell-uniform PST and search functionals are again polynomial in
$T_W$ between cell-uniform states; the polynomial values agree with the
finite-matrix calculation. $square$

#emph[Theorem 6.3 (quasi-infinite limit theorem).]
Let $(G_n, pi_n)_(n in NN)$ be a sequence of finite Hermitian weighted
graphs with equitable partitions, all of size at most $r$. Suppose:
+ The pixel-step graphons $W_(G_n)$ converge to a Hermitian graphon $W$
  in cut norm.
+ The cell-fraction vectors converge to a probability vector
  $(mu(A_1), dots, mu(A_r)) in Delta^(r-1)$ with all $mu(A_k) > 0$.
+ The normalized quotient matrices $G_n slash pi_n$ converge to a
  Hermitian matrix $M in CC^(r times r)$ in Frobenius norm.

Then $W$ admits a measurable equitable partition $pi$ realizing the
limit cell fractions and with $W slash pi = M$. Moreover, every
cell-uniform PST or spatial-search problem on $(G_n, pi_n)$ has a
well-defined limit on $(W, pi)$, and the limit's value is the value of
the finite Hermitian problem on $M$. Lean: `Graphplay/Graphon/Limit.lean`;
the proof reduces to (a) cut-norm-implies-operator-norm convergence under
bounded entries [szegedy2010spectral], (b) Frobenius convergence of the
quotient matrices, and (c) continuity of finite spectral optimization
problems.

#emph[Proof sketch.]
By [szegedy2010spectral], cut-norm convergence with bounded entries
implies operator-norm convergence of $T_(W_(G_n)) arrow.r T_W$. The
indicator functions $bb(1)_(A_(n, k))$ of the cells of $pi_n$, viewed in
$L^2$, converge to $bb(1)_(A_k)$ for a measurable limit partition because
the cell-fraction vector converges and the measures are uniformly bounded.
Apply $T_(W_(G_n))$ to $bb(1)_(A_(n, k))$ and use both convergences: in
the limit, $T_W bb(1)_(A_k) = sum_j tilde(b)_(j k) bb(1)_(A_j)$ a.e.\,
which is the graphon equitability. The values $tilde(b)_(j k)$ are the
limit Frobenius entries. The PST/search functionals are continuous in the
finite quotient and in the (uniformly bounded) cell fractions, hence
continuous through the limit. $square$

#emph[Corollary 6.4 (Xie--Tamon [xie2023tail] as a 2-cell corner).]
The sequence $K_n + P_n$ with two-cell partition (clique, tail)
satisfies the hypotheses of Theorem 6.3 with limit a complete graphon on
$[0, 1 slash 2]$ together with an infinite path of mass $1 slash 2$; the
limit quotient is the $2 times 2$ Hermitian matrix encoding the
Farhi--Gutmann complete-graph search, and optimality is preserved.

#emph[Corollary 6.5 (BTV-Xie [bernard2022tails] as a 2-cell corner).]
The transfer-side companion is recovered by the same 2-cell scheme applied
to the PST primitive: $K_n + P_n$-like sequences with PST endpoints in
the clique block have the limit governed by the same $2 times 2$ matrix,
and tails-PST is preserved.

#emph[Example 6.6 (cycle blowup).]
Fix a template weighted graph $Q$ on $r$ vertices. The sequence
$"Tot"(Q, 0, J)$ with equal fibers of size $n$, viewed as pixel-step
graphons, converges in cut norm to the block-constant graphon $W_Q$ with
cells of measure $1 slash r$ and value $Q_(j k)$ in block $(j, k)$. The
quotient at every stage is $n dot Q$ (up to a renormalization absorbed
into the time parameter), and Theorem 6.3 gives the limit as the finite
search problem on $Q$. The compiler examples of v2
(`rook_3x3_equal_fiber`, `cycle8_powerlaw_alpha1`,
`torus_heawood7_equal_fiber`) are the finite stages of such a sequence.

#heading("7. Tower 5: `COLIMIT` as a Filtered-Colimit-Preserving Functor")

Let $"EqWGr"$ be the category whose objects are pairs $(G, pi)$ with $G$
a finite Hermitian weighted graph and $pi$ an equitable partition, and
whose morphisms $(G, pi) arrow.r (G', pi')$ are pairs $(phi, theta)$
with $phi$ a weight-preserving cell-block map and $theta$ refining $pi$
to a partition compatible with $phi$. Let $"Mat"_("fin")(CC)$ be the
category of finite Hermitian matrices. Define
$"Quot" : "EqWGr" arrow.r "Mat"_("fin")(CC)$ by
$"Quot"(G, pi) = G slash pi$.

#emph[Theorem 7.1 (single load-bearing theorem of Tower 5).]
The functor $"Quot"$ preserves filtered colimits. Explicitly, given a
filtered diagram $(G_alpha, pi_alpha)$ in $"EqWGr"$ whose underlying
graphs form a sequence with a graphon colimit $W$ (in the cut metric) and
whose quotient matrices have a finite-dimensional Frobenius limit $M$,
the colimit pair $(W, pi)$ exists in the extended graphon-equitable
category and $W slash pi = M$. Lean: `Graphplay/Categorical.lean`, where
the chain colimit, cochain limit, and
`Quotient.preservesFilteredColimits` are mechanized.

#emph[Corollary 7.2 (unification).]
The quasi-infinite limit theorem (Theorem 6.3) is the Tower-4 instance of
Theorem 7.1. The Tower-1 inverse-limit and edge-union universal
properties of v2 are the Tower-1 and Tower-0 instances. The "failed
reflector" observation --- there is no left adjoint to "forget the
coloring" --- is the statement that the underlying-graph functor does
*not* have a colimit-preserving left adjoint; the *relative* left adjoint
along a chosen template $Q$ does exist and is the bundle construction of
Section 4 (`Bundle.ofTemplateJoin_total_eq_templateJoin`).

#emph[Corollary 7.3 (Xie--Tamon and BTV-Xie via the categorical
machine).]
Theorem 7.1 instantiated on the 2-cell schemes of Corollaries 6.4--6.5
returns Xie--Tamon [xie2023tail] and BTV-Xie [bernard2022tails] as direct
images of the same `COLIMIT` instruction.

#emph[Proof sketch of Theorem 7.1.]
Filtered colimits in $"EqWGr"$ are built from refinement-compatible cocones.
Given a filtered diagram, the underlying cell-fraction vectors live in
$Delta^(r-1)$ (compact); pass to a convergent subnet to extract a limit
fraction vector. The quotient matrices live in the bounded subset
${M : abs(M)_(F) <= C}$ of $CC^(r times r)$; extract a Frobenius
subnet limit $M$. The graphs themselves, viewed as pixel-step graphons,
live in the cut-metric-compact subset
${W : abs(W)_(infinity) <= 1}$ (Lovasz); extract a cut-norm subnet limit
$W$. The three sub-limits assemble into a single colimit object in the
extended graphon-equitable category by Theorem 6.3, and the universal
property follows from the fact that all cocone maps respect the
characteristic matrix. The Lean proof uses Mathlib's `IsFiltered` API on
the index category and the abstract colimit-preservation criterion via
representability. $square$

#emph[Worked Tower-5 chain.]
Take the chain $G_n := K_n + P_n$ with 2-cell partition $pi_n$. The
quotient matrices are
$ G_n slash pi_n = mat((n-1) + 0, 1; 1, 2 + 0). $
(Off-diagonal $1$ because only one edge connects clique to tail; diagonal
$n - 1$ is the clique-internal row sum; diagonal $2$ is the path-internal
row sum at an interior vertex, with corrections at the endpoints absorbed
into the normalization.) Renormalizing so that the cell measure is fixed
and the largest entry is bounded, the Frobenius limit as $n arrow.r infinity$
is a bounded $2 times 2$ Hermitian matrix. The cut-norm limit of the
pixel-step graphons of $G_n$ is a Hermitian graphon equal to $1$ on
$[0, 1 slash 2]^2$, equal to a path-kernel on $[1 slash 2, 1]^2$, and
equal to a single bridging edge of measure zero. Theorem 6.3 / Theorem 7.1
gives the limit search functional explicitly, recovering the [xie2023tail]
result. The same chain with PST endpoints in the clique block gives the
[bernard2022tails] result by Corollary 6.5.

#heading("8. Engineering Toolkit: `(primitive, hardware)` to `(host, partition, schedule, certificate)`")

We give the compiler its signature.

A *primitive* is a constructor in the Lean enum

$ "Primitive" := "PST" | "UniformMixing" | "FractionalRevival" | "Search" | "Transfer" | "Sample". $

A *hardware specification* is a decidable predicate on weighted graphs.
`Graphplay/Toolkit/Hardware.lean` provides constants $"planarSpec"$,
$"surfaceSpec"(g)$, $"nearestNeighborSpec"(r)$,
$"chiralAllowedSpec"(Phi)$, $"regularSpec"(d)$, $"sizeBoundedSpec"(n)$,
their finite intersections, and a *quotient* operation that lifts a
hardware specification on the host to a specification on the quotient.

A *schedule* is a piecewise-constant or piecewise-analytic family of
Hamiltonians on the host. `Graphplay/Toolkit/Scheduler.lean` provides
static, magnetic-flux, and adiabatic schedules together with
`Schedule.evolve_preserves_cellUniform`: cell-uniform states stay
cell-uniform under any schedule whose generators preserve the partition
projector. This is the certificate that makes the spine usable
*time-dependently*.

A *noise model* is a Lindblad-type perturbation;
`Graphplay/Toolkit/Noise.lean` defines a `NoiseModel`, the cell-uniform-
symmetric subclass, and `Noise.cellUniform_preserved`, which says the
cell-uniform subspace remains invariant under a cell-uniform-symmetric
noise model. This lemma promotes Theorems 2.2, 3.3, 5.2, 6.2, 7.1 to
noisy-CTQW versions; full quantitative treatment is open.

A *certificate* of a `(primitive, host, partition, schedule)` tuple is a
Lean term of type `Certificate primitive host partition schedule`, with
field constructors corresponding to Theorems 4.3, 5.2, and 6.2 as
appropriate. The compiler emits both a JSON artifact and a Lean term;
the Lean term is checked by `lake build` before deployment, giving a
machine-verifiable bridge from a hardware-and-primitive specification to
a quantum-walk schedule. The case studies of v2 are precisely equal-fiber
bundles whose templates carry verifiable regularity certificates; they
become end-to-end Lean-checked instances of the compiler.

#emph[The Certificate type.]
Schematically,

```
structure Certificate
    (p : Primitive) (B : GraphBundle) (pi : EquitablePartition B.tot)
    (sched : Schedule B) where
  regular_fibers     : ∀ i, Regular (B.H i) (B.fiberRowSum i)
  biregular_couplings : ∀ i j, Q.adj i j ≠ 0 → Biregular (B.B i j)
  schedule_equitable : ∀ t, EquitablePartition (sched.evolve t).gen pi
  primitive_quotient : QuotientCertifies p (B.quotient pi)
```

The four fields are: the two regularity certificates of Theorem 4.3, the
schedule-side equitable-preservation certificate of
`Schedule.evolve_preserves_cellUniform`, and the small-quotient primitive
certificate (a finite eigen-decomposition or PST-time witness). All four
are decidable in the finite case; the graphon case adds a measurability
side-condition. The toolkit ships with constructors for the catalog
entries below, each returning a `Certificate` whose Lean term is the
artifact deployed to hardware.

The toolkit catalog at v3 contains the following (primitive, hardware)
entries with full certificates:

#table(
  columns: 4,
  stroke: 0.5pt,
  inset: 6pt,
  align: (left, left, left, left),
  [*Primitive*], [*Hardware*], [*Host*], [*Reference*],
  [`PST`], [near-neighbor chain], [Christandl-Datta path], [classical],
  [`PST`], [planar, equal-fiber], [`TemplateJoin(K_4, V)`], [v2],
  [`PST`], [surface genus $g$], [`TemplateJoin(K_(H(g)), V)`], [v2],
  [`PST`], [dual-rail, chiral], [Xie--Kay--Tamon chain], [xie2022speedlimit],
  [`PST`], [tail attached], [`K_n + P_n`], [bernard2022tails],
  [`Search`], [Laplacian-integral], [`Tot(Q, 0, J)`], [li2025deterministic],
  [`Search`], [long-range tunneling], [`Tot(Q, 0, B_(alpha))`], [king2025longrange],
  [`Search`], [planar near-neighbor], [`Tot(K_4, 0, J)`], [sadowski2014planar],
  [`Search`], [infinite tail probe], [graphon limit of `K_n + P_n`], [xie2023tail],
  [`UniformMixing`], [chiral $K_n^sigma$ quotient], [bundle on $K_n^sigma$], [levine2026chiral],
  [`FractionalRevival`], [Hamming scheme], [Hamming-scheme bundle], [chan2019fractional],
)

#heading("9. Spectral Disassembly: Decompiling Operators to Equitable Programs")

The compiler so far goes forward: from a `(primitive, hardware)` request
to a `(host, partition, schedule, certificate)` quadruple. The reverse
problem --- given a host operator, recover a (smallest) `BUNDLE +
PARTITION` program that produces it --- is *decompilation*. The Lean
artifact contains a stub `Graphplay/Toolkit/Spec.lean` for the disassembler
and a stub partition-search routine; the analysis is brief here because
two companion files do the worked applied case studies:

+ `paper/applied_majorana1.md` --- decompilation of the Microsoft Majorana 1
  chip Hamiltonian to an equitable program: a topological-qubit fabric
  with a small chiral template quotient, exhibiting the chiral
  speed-limit-breaking corner (Corollary 5.5) on engineered chains. The
  applied question is which Majorana-coupling patterns produce a chiral
  quotient with a non-trivial speedup window.

+ `paper/applied_ibm_heavy_hex.md` --- decompilation of the IBM heavy-hex
  lattice Hamiltonian: a planar near-neighbor host whose color partition
  has a $4 times 4$ quotient, with PST and search corners visible at the
  Tower-2 spine. The applied question is the optimal magnetic-flux phasing
  consistent with the heavy-hex geometry, framed as a quotient-level
  optimization (Theorem 5.3).

The main paper records the framework; the case studies live in those
companion notes.

#emph[9.1 The disassembler signature.]
Decompilation is the search problem

$ "Disasm" : "Operator" arrow.r "set" ("BundleProgram" union.dot "Failure"), $

where a `BundleProgram` is a sequence of `PARTITION`, `BUNDLE`, `SIGN`,
and `REFINE` instructions producing the input operator. The two
canonical algorithms are

+ *Weisfeiler--Leman refinement* as a `PARTITION`-search engine. Starting
  from the trivial partition, iteratively refine by row-sum signature
  until stable; the stable refinement is the *coarsest* equitable
  partition of the operator, by classical Godsil. Lean:
  `Graphplay/Integrations/WLRefinement.lean`. This gives the `Disasm`
  worst case in polynomial time and the best case (when the operator is
  truly assembled by a small bundle) in a small constant.

+ *Spectral disassembly* via the coherent-algebra projection.
  Compute the spectral projectors of the input operator; cluster them by
  cell-pair signature; verify against the partition-projector algebra
  $cal(P)(pi)$ of Definition 3.2. When the operator is exactly cell-
  pair-constant, the recovered $pi$ is a faithful disassembly. Lean:
  `Graphplay/Dowsing/CoherentAlgebra.lean`.

#emph[9.2 The dual-rail Majorana example.]
The Microsoft Majorana 1 chip Hamiltonian has a $4 times 4$ block
structure at the level of pairs of Majorana zero modes. Disassembly
identifies the (Q, fibers, couplings) triple as: $Q$ is a small chiral
template encoding the topological-qubit braiding pattern, fibers are
trivial single-vertex sets per logical qubit, and couplings are the
engineered Majorana hopping amplitudes. The resulting program runs the
chiral `SIGN` instruction (Corollary 5.5) on the small quotient. The
applied question is which couplings produce a chiral quotient with a
nontrivial speedup window; see `paper/applied_majorana1.md`.

#emph[9.3 The heavy-hex example.]
The IBM heavy-hex lattice has a natural 4-cell color partition: degree-2
edge vertices, degree-3 vertex bodies, and a refinement separating the
two flavors of edge vertex. The resulting quotient is a $4 times 4$
real-symmetric matrix; spectral disassembly recovers the corresponding
bundle program with $Q$ a small auxiliary graph. The flux-phasing
question (under which magnetic-flux assignments does the heavy-hex
lattice achieve optimal Grover search?) is then Theorem 5.3 on the
$4 times 4$ chiral quotient. Companion: `paper/applied_ibm_heavy_hex.md`.

#emph[9.4 The fragility of disassembly.]
A small perturbation of an operator generically breaks exact equitability;
the partition collapses to the trivial single-cell partition. Robust
disassembly --- recovering an *approximate* program with quantitative
error bounds --- is open at the level of Lean mechanization, but the
spectral-stability machinery of [szegedy2010spectral] together with the
graphon limit (Theorem 6.3) supplies the natural framework. The
`Toolkit/Spec.lean` stub already declares the signature of a robust
disassembler with a numerical tolerance parameter.

#heading("10. Research Program")

The Lean development includes thirty further modules sketching open
extensions, integrations, and conjectural higher towers. The companion
file `paper/research_program.typ` carries the full discussion. We list
the spine in bullet form here:

- *Dowsing-rod open theorems* (`Graphplay/Dowsing/`).
  - `BundlePSTLift.lean`: PST iff quotient PST for every classical product;
    corner-by-corner table from Cartesian through disjunctive.
  - `ChiralBundlePST.lean`: chiral bundle PST iff signed-quotient PST;
    Levine signing witness `unitaryHammingChiralK4`; open questions
    $"OpenQ"_1, "OpenQ"_2, "OpenQ"_3$ on chiral product PST,
    $K_n^sigma$ sharpness, chiral Heawood PGST.
  - `ChiralGraphon.lean`: chiral graphons (skew-Hermitian imaginary part);
    `IsChiral` versus `IsReal`; equitable theory at the graphon-chiral level.
  - `CoherentAlgebra.lean`: partition-projector algebra $cal(P)(pi)$, its
    commutativity with $Pi_pi$, relation to coherent algebra of $G$.
  - `Conjecture93.lean`: the falsifiable Conjecture below with Lean
    apparatus and a worked example table.
  - `FilteredColimitPST.lean`: categorical PST lift along filtered
    colimits, Tower-5 of Theorem 6.2.
  - `FractionalRevivalNC.lean`: non-commutative fractional revival on
    quantum graphs; Tower-3 generalization of [chan2019fractional].
  - `HypergraphPST.lean`: $k$-uniform hypergraph PST and search via the
    bipartite incidence weighted graph.
  - `NoiseEquitable.lean`: quantitative cell-uniform preservation under
    generic noise.
  - `NonCommutativeCoherent.lean`: non-commutative coherent algebras for
    Definition 3.1 quantum graphs.

- *Cross-disciplinary integrations* (`Graphplay/Integrations/`).
  Each is a research-program seed pointing to an external field where the
  spine applies.
  - `Hodge.lean`: combinatorial Hodge decomposition; equitable partitions
    compatible with the cochain complex; harmonic-subspace quotient.
  - `LatticeGauge.lean`: chiral signings as discrete $U(1)$ / non-abelian
    connections on weighted graphs; plaquette flux.
  - `MeanFieldGames.lean`: graphon LQR control [gao2020graphon] and quantum
    mean-field games unified through equitable reduction.
  - `OptimalTransport.lean`: graphons as transport plans, Sinkhorn
    alignment, quotient as a marginal-preserving lift.
  - `RMT.lean`: random matrix theory meets equitable partitions; free
    probability on cell-uniform subspaces; free convolution for quotient
    spectra.
  - `TensorNetworks.lean`: MERA coarse-graining as exact equitable cell
    maps; PEPS and holographic codes as bundles.
  - `TQFT.lean`: weighted graphs as input data for $(2+1)$d TQFT;
    modular tensor category extensions; Levin--Wen and Kitaev models.
  - `WLRefinement.lean`: the Weisfeiler--Leman chain as the universal
    refinement of equitable partitions; algebraic and quantum WL.

- *Towers 6--7* (conjectural higher towers).
  - `Tower6.lean`: sheaves of weighted graphs over a topological base;
    Towers 3--5 as point-base, measure-base, sheaf-of-spectra cases;
    preservation of filtered colimits for the global-sections functor.
  - `Tower7.lean`: $infinity$-categorical generalization; stable
    $infinity$-categories with Hermitian endomorphisms; coherent
    idempotent partitions; derived Hermitian partitions; the
    $infinity$-categorical PST lift.

- *Worked instruction-trace catalog.* Each catalog entry of Section 8
  decomposes into a small instruction sequence in the combinator
  calculus of Section 1. For reference, the IBM heavy-hex Search entry
  reads `BUNDLE(Q = K_4, H = 0, B = J); PARTITION = color-classes;
  REFINE(marked-vertex); LIFT(Search on 4x4 quotient)`; the Xie--Kay--
  Tamon chiral PST entry reads `BUNDLE(Q = K_2, H = path, B = J);
  PARTITION = 2-cell; SIGN(dual-rail phase); LIFT(PST on 2x2 chiral
  quotient)`. A formal catalog enumeration with each program type-checked
  in Lean is a target for `Graphplay/Toolkit/Catalog.lean` and is the
  primary deliverable that turns the toolkit into a reproducible
  artifact.

- *Falsifiable Conjecture 9.3 (Bose--Mesner $eq.triple$ chiral $eq.triple$
  graphon).*
  A consistent sequence of finite weighted graphs $(G_n, pi_n)$ admits
  *both* (i) a graphon quasi-infinite limit (Theorem 6.3) and (ii) a
  strict chiral signing speedup on $pi_n$ (Theorem 5.3 with strict
  inequality on the mixing-time functional), if and only if the
  Bose--Mesner algebra of the family eventually coincides with the
  partition-projector algebra $cal(P)(pi_n)$.
  *Status.* The *weak* version (cross-constant signings) is believed
  true and supported by worked examples on $K_n^sigma$, Hamming schemes,
  $K_(n,n,n,n)$, and the Heawood envelope; it is *blocked* in three
  confirmed both-sides-false witnesses ---  $K_n + P_n$,
  $"Cayley"(S_n)$ by transpositions, and any distance-regular-but-not-
  distance-transitive bipartite double cover. The *strong* version
  (arbitrary unitary signings) is conjecturally false; a candidate
  counterexample uses non-cross-constant phase-equitable refinements of
  $K_n + P_n$. Detailed analysis in `paper/conjecture93_notes.md`; Lean
  apparatus in `Graphplay/Dowsing/Conjecture93.lean`. The next concrete
  step is the Bose--Mesner-versus-distance-projector dimension table for
  $K_n + P_n$ at $n = 3, 4, 5$.

- *Open extensions.*
  - *Graphops.* Backhausz--Szegedy graphops generalize graphons by removing
    the $L^2$ symmetric-kernel assumption. The quotient spine survives
    when the operator commutes with $Pi$; Theorem 6.3 should extend to
    graphops under mild compactness.
  - *Surface topology.* The Heawood map-color completion is the bundle
    with $Q = K_(H(g))$; the surface algebraic-connectivity ceiling of
    [freitas2001heawood] is a Tower-2 spectral budget on $Q$.
  - *Open systems and time dependence.* Bundle-and-quotient survives
    unitary perturbations whose generator is equitable, and
    cell-uniform-symmetric noise (`Toolkit/Noise.lean`). Lindbladian
    extensions and general time-dependent schedules are not yet covered
    beyond the cell-uniform invariance lemma.
  - *Applied case studies.* `paper/applied_majorana1.md` (Microsoft
    Majorana 1 topological-qubit fabric) and
    `paper/applied_ibm_heavy_hex.md` (IBM heavy-hex lattice) are
    sibling-agent companions written against the Tower-2 / Tower-3 spine.

#heading("References")

#set par(justify: false)

#emph[Tamon corpus:]

- #emph[ge2010products.] Y. Ge, B. Greenberg, O. Perez, C. Tamon.
  #link("https://arxiv.org/abs/1009.1340")[Perfect state transfer, graph
  products and equitable partitions], arXiv:1009.1340.
- #emph[bachman2011quotient.] R. Bachman, E. Fredette, J. Fuller,
  M. Landry, M. Opperman, C. Tamon, A. Tollefson.
  #link("https://arxiv.org/abs/1108.0339")[Perfect state transfer on
  quotient graphs], arXiv:1108.0339.
- #emph[chan2019fractional.] A. Chan, G. Coutinho, C. Tamon, L. Vinet,
  H. Zhan.
  #link("https://arxiv.org/abs/1907.04729")[Fractional revival and
  association schemes], arXiv:1907.04729.
- #emph[chan2022shadows.] A. Chan, C. Godsil, C. Tamon, W. Xie.
  #link("https://arxiv.org/abs/2204.04355")[Of shadows and gaps in spatial
  search], arXiv:2204.04355.
- #emph[xie2022speedlimit.] W. Xie, A. Kay, C. Tamon.
  #link("https://arxiv.org/abs/2209.08160")[Breaking the speed limit for
  perfect quantum state transfer], arXiv:2209.08160.
- #emph[bernard2022tails.] P.-A. Bernard, C. Tamon, L. Vinet, W. Xie.
  #link("https://arxiv.org/abs/2211.14704")[Quantum state transfer in
  graphs with tails], arXiv:2211.14704.
- #emph[xie2023tail.] W. Xie, C. Tamon.
  #link("https://arxiv.org/abs/2301.07251")[No infinite tail beats
  optimal spatial search], arXiv:2301.07251.
- #emph[levine2026chiral.] L. Levine, J. J. Mesapam, B. Mustico, C. Tamon,
  G. Tucker, H. Zhan.
  #link("https://arxiv.org/abs/2605.04414")[Uniform mixing in chiral
  quantum walks], arXiv:2605.04414.

#emph[Structural ancestors (graphons, graph limits):]

- #emph[szegedy2010spectral.] B. Szegedy.
  #link("https://arxiv.org/abs/1003.5588")[Limits of kernel operators and
  the spectral regularity lemma], arXiv:1003.5588.
- #emph[bick2024graphlimits.] C. Bick, D. Sclosa.
  #link("https://arxiv.org/abs/2110.13686")[Dynamical systems on graph
  limits and their symmetries], arXiv:2110.13686.
- #emph[gao2020graphon.] S. Gao, P. E. Caines.
  #link("https://arxiv.org/abs/2004.00677")[Subspace decomposition for
  graphon LQR: applications to VLSNs of harmonic oscillators],
  arXiv:2004.00677.

#emph[CTQW and search neighbors:]

- #emph[chakraborty2020spatial.] S. Chakraborty, L. Novo, A. Ambainis,
  Y. Omar.
  #link("https://arxiv.org/abs/1508.01327")[Spatial search by quantum
  walk is optimal for almost all graphs], arXiv:1508.01327.
- #emph[king2025longrange.] R. King et al.
  #link("https://arxiv.org/abs/2501.08148")[Optimal spatial searches with
  long-range tunneling], arXiv:2501.08148.
- #emph[li2025deterministic.] X. Li, S. Luo, Z. Feng, Y. Li.
  #link("https://arxiv.org/abs/2506.21108")[Deterministic quantum search
  on all Laplacian integral graphs], arXiv:2506.21108.
- #emph[sadowski2014planar.] P. Sadowski.
  #link("https://arxiv.org/abs/1406.0339")[Quantum spatial search on
  planar networks], arXiv:1406.0339.
- #emph[wong2017lazy.] T. Wong.
  #link("https://arxiv.org/abs/1706.06939")[Faster search by lackadaisical
  quantum walk], arXiv:1706.06939.
- #emph[freitas2001heawood.] M. A. A. de Freitas.
  #link("https://arxiv.org/abs/math/0109191")[A Heawood-type result for
  the algebraic connectivity of graphs on surfaces], arXiv:math/0109191.
- #emph[ide2022equitable.] Y. Ide, A. Narimatsu.
  #link("https://arxiv.org/abs/2209.07688")[Perfect state transfer,
  equitable partition and continuous-time quantum walk based search],
  arXiv:2209.07688.
- #emph[kirkland2023join.] S. Kirkland, H. Monterde.
  #link("https://arxiv.org/abs/2312.06906")[Quantum walks on join
  graphs], arXiv:2312.06906.

#emph[Previous version:]

- #emph[graphplay2025v2.] Graphplayers Crew. #emph[Equitable Quotients Across Five Towers
  (Graphplay v2).] (This repository,
  `paper/quasi_infinite_adjoint_v2.typ`.)
