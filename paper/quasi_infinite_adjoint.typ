#set document(title: "Toolkit Note: Engineered Color Templates for Spatial Search")
#set page(margin: 1in)
#set text(size: 11pt)
#set par(justify: true)

#align(center)[
  #text(size: 17pt, weight: "bold")[Toolkit Note] \
  #v(0.35em)
  #text(size: 12pt)[Engineered Color Templates for Spatial Search] \
  #v(0.25em)
  #text(size: 9.5pt)[Graphplayers Crew; Lean core plus compiler prototype]
]

#v(0.6em)

#heading("Abstract")

This note turns the improvised phrase "quasi-infinite adjoint" into a small
toolkit for graph-engineered spatial search. The global reflector into colorable
graphs fails, but a useful local replacement exists: once a label map or quotient
template is selected, there is a greatest graph compatible with it. The Lean
development verifies indexed graph bags, countable edge unions, inverse-limit
thread graphs, color completions, template pullbacks, engineered template joins,
and simultaneous multicolor constraints.

The addendum connects this machinery to quantum spatial search: the four-color
theorem gives every finite planar graph a complete multipartite four-color
completion. That completion is Laplacian integral, so the deterministic-search
theorem of Li, Luo, Feng, and Li applies to the completion, though not
automatically to the original planar graph. More generally, equal-fiber joins
over engineered regular templates inherit the template spectral ratio relevant
to Grover-optimal CTQW search.

#figure(
  image("assets/pipeline.svg", width: 100%),
  caption: [Compiler-shaped view of the construction.]
)

#heading("Formal Setting")

A simple graph on a vertex type $V$ is represented by an adjacency predicate
$"Adj" : V -> V -> "Prop"$ together with symmetry and irreflexivity.  A graph
homomorphism $G -> H$ is a vertex function preserving adjacency.  A coloring by
a color type $C$ is a homomorphism into the complete graph $K_C$, where
$x "Adj" y$ means $x != y$.

The Lean file uses a local `Bijection` structure rather than importing a full
category theory library.  This keeps the artifact small while still stating the
relevant adjoint-shaped equivalences explicitly.

#heading("The Bag Construction")

Given an index type $I$, vertex families $V_i$, and graphs $G_i$ on $V_i$, define

$ "vertices"("SigmaGraph"(G)) = sum_(i in I) V_i. $

Two tagged vertices are adjacent only when they have the same tag and the
underlying vertices are adjacent in that factor:

$ (i,a) "Adj" (j,b) <=> exists k, i = k and j = k and a "Adj"_(G_k) b. $

Lean verifies the universal property:

$ "Hom"(sum_(i in I) G_i, H) ~= product_(i in I) "Hom"(G_i, H). $

This is the most literal successful version of the "bag of factors" idea.  It is
arbitrary in the index type, so it can be finite, countable, or larger, depending
on the ambient universe.

#heading("Heterogeneous Color Factors")

If every factor has its own palette $C_i$ and coloring

$ "color"_i : G_i -> K_(C_i), $

then the whole bag is colored by the sigma-sum palette:

$ sum_(i in I) G_i -> K_(sum_(i in I) C_i), "   " (i,a) |-> (i, "color"_i(a)). $

If all factors share one palette $C$, the coproduct reuses that same palette.
This captures the heterogeneous case from the motivating conversation without
forcing all components to have the same chromatic number.

#heading("Countable Approximation")

For graphs $G_n$ on a shared vertex type $V$, Lean defines an edge-union graph:

$ x "Adj" y <=> exists n, x "Adj"_(G_n) y. $

A homomorphism out of this union is equivalent to one vertex map that preserves
adjacency at every stage:

$ "Hom"(union_n G_n, H) ~= { f : V -> W | forall n, f " preserves " "Adj"_(G_n) }. $

This is a lightweight colimit-style theorem for staged approximants.  It is a
reasonable formal proxy for "take the finite constructions and let them run
quasi-infinitely", while still avoiding unverified analytic claims about metric
or fractal dimension.

#heading("Inverse Threads")

For an inverse system of vertex types

$ dots -> V_2 -> V_1 -> V_0, $

Lean defines a thread as a sequence $x_n in V_n$ compatible with the bonding
maps.  The inverse-limit graph makes two threads adjacent when all finite
coordinates are adjacent.  Each coordinate projection is a graph homomorphism:

$ pi_n : lim G_n -> G_n. $

Consequently, any coloring of one finite coordinate induces a coloring of the
inverse-limit graph by composition with $pi_n$.

#heading("The Failed Reflector")

One tempting reading of "quasi-infinite adjoint" is: construct a free or largest
$C$-colorable graph associated to any graph $G$.  In the ordinary graph
homomorphism category, that version fails before it gets started.

Lean proves:

$ not "Colorable"(G,C) and "Colorable"(H,C) => not exists (G -> H). $

The reason is direct: if $G -> H$ and $H -> K_C$, then composition gives
$G -> K_C$, contradicting non-colorability of $G$.

The development also formalizes the concrete witness: the triangle is not
two-colorable, so there is no homomorphism from the triangle into any
Bool-colorable graph.  Thus an ordinary reflector with a unit $G -> L(G)$ into
the full subcategory of two-colorable graphs cannot exist.

#heading("Local Completion")

The successful adjoint-shaped object is local over a chosen vertex-color map.
Fix $c : V -> C$. Among all graph structures on $V$ for which $c$ is a coloring,
there is a greatest one:

$ K_c(x,y) <=> c(x) != c(y). $

In other words, $K_c$ is the cofree or maximal graph compatible with the color
map. If $G -> K_C$ is a coloring, then $G$ is a spanning subgraph of this
completion. Lean verifies this as `ColorCompletion.greatest`.

For a genuine bag $V = sum_(i in I) V_i$, the map $"tag"(i,a)=i$ gives

$ "CompleteJoin"(V_i) = K_("tag"). $

This graph has all cross-bag edges and no within-bag edges. Lean verifies:

- `CompleteJoin.no_intra`: vertices in the same bag are never adjacent;
- `CompleteJoin.cross`: vertices in different bags are always adjacent;
- `CompleteJoin.greatest`: any graph colored by the tag projection is a
  spanning subgraph of the complete join.

So the quasi-infinite construction is not merely "take a bag". It is:

$ "colored graph" -> "independent color fibers" -> "complete cross-fiber host". $

The host is canonical once the coloring is fixed, and the index set can be
arbitrary. For four-color planar graphs the index set is bounded by four; for
the earlier speculative infinite construction, the fibers may be infinite while
the color quotient remains finite.

#heading("Engineered Colorability")

The better generalization is to stop treating a palette as a complete graph.
Let $Q$ be any graph on a type $T$ of engineered modes, and let
$f : V -> T$ be a selected label map. Define

$ f^* Q (x,y) <=> Q(f(x), f(y)). $

Lean calls this `PullbackGraph Q f`. It is the greatest graph on $V$ for which
the chosen label map is a homomorphism into $Q$. Ordinary color completion is
the special case $Q = K_C$.

For bags, this becomes an engineered join. Given fibers $V_i$ over template
vertices $i in I$,

$ "TemplateJoin"(Q,V)( (i,a), (j,b) ) <=> Q(i,j). $

So a small template graph programs which bags are completely coupled. The old
`CompleteJoin` is the special case where $Q$ is complete; a bipartite template,
cycle template, hypercube template, expander template, or Laplacian-integral
template gives a different engineered host. Lean verifies the no-intra-fiber
rule, the cross-fiber rule, and maximality as `TemplateJoin.greatest`.

Multicolorability is the intersection version. Given many templates $Q_a$ and
many selected label maps $f_a : V -> T_a$, Lean defines `MultiPullbackGraph` by

$ x "Adj" y <=> forall a, Q_a(f_a(x), f_a(y)). $

This captures simultaneous constraints: planar color class, hardware zone,
allowed long-range tunneling family, parity, oracle class, or any other selected
coarse observable. The design problem changes from "is the graph colorable?" to
"which quotient templates do we want the Hamiltonian support to factor through?"

#figure(
  image("assets/templates.svg", width: 100%),
  caption: [Three views: ordinary four-color completion, a non-complete engineered template, and a fiber blowup.]
)

#heading("Spatial Search Link")

The fetched spatial-search papers make the relevant graph invariant clear. In
the Chakraborty--Novo--Ambainis--Omar CTQW model, the search Hamiltonian is

$ H_G = - P_w - gamma A_G, $

where $A_G$ is the adjacency matrix. Their optimality criterion is spectral: the
largest adjacency eigenvector should be the uniform state and the rest of the
normalized spectrum should be bounded away from it. King et al. use a Laplacian
search Hamiltonian

$ H_alpha = - gamma_0 L_alpha - P_w, $

and identify the Laplacian spectral gap/algebraic connectivity as the critical
resource for long-range tunneling search. Li--Luo--Feng--Li prove that any
Laplacian integral graph admits deterministic search with certainty when the
marked proportion is known in advance. Sadowski studies spatial search directly
on planar Apollonian networks and finds that planar sparsity alone is not enough
to make all marked-location cases operationally uniform.

This suggests a modest but real theorem.

#emph[Theorem (four-color Laplacian-integral envelope).]
Let $G = (V,E)$ be a finite loopless planar graph. Choose a four-coloring
$c : V -> {1,2,3,4}$, supplied by the four-color theorem. Define the completion
$K_c$ on the same vertex set by

$ x "Adj"_(K_c) y <=> c(x) != c(y). $

Then:

- $G$ is a spanning subgraph of $K_c$;
- $K_c$ is complete multipartite with at most four parts;
- $K_c$ is Laplacian integral;
- therefore the deterministic quantum search theorem for Laplacian integral
  graphs applies to $K_c$.

#emph[Proof.]
If $x "Adj"_G y$, then properness of $c$ gives $c(x) != c(y)$, so the identity
on vertices is a graph homomorphism $G -> K_c$. The definition of $K_c$ connects
exactly the vertices in distinct color classes, hence $K_c$ is complete
multipartite.

Let the nonempty color classes have sizes $n_1, ..., n_r$, with $r <= 4$ and
$N = n_1 + ... + n_r$. For the complete multipartite graph
$K_(n_1,...,n_r)$, a vector summing to zero inside part $i$ is a Laplacian
eigenvector with eigenvalue $N - n_i$, giving multiplicity $n_i - 1$. On the
subspace of vectors constant on each part, the Laplacian acts by
$a_i |-> N a_i - sum_j n_j a_j$, whose eigenvalues are $0$ once and $N$ with
multiplicity $r - 1$. Thus all Laplacian eigenvalues are integers:

$ "spec"(L(K_c)) = {0, N, N-n_1, ..., N-n_r}. $

So $K_c$ is Laplacian integral. Li--Luo--Feng--Li's deterministic-search theorem
applies to every Laplacian integral graph, hence to $K_c$.

The Lean artifact verifies the graph-theoretic part of this theorem:
`ColorCompletion` constructs $K_c$, `Coloring.toColorCompletion` proves the
identity homomorphism $G -> K_c$, and the same-color/different-color lemmas
prove the complete multipartite edge rule. The Laplacian spectrum calculation is
ordinary linear algebra and is not yet mechanized in this repository.

#heading("Beyond Planarity")

Planarity is only the genus-zero case. If a graph embeds on an orientable
surface of genus $g$, the Heawood map-color theorem gives the color bound

$ H(g) = floor((7 + sqrt(1 + 48 g)) / 2). $

For nonorientable genus $k$, the corresponding bound is

$ H_N(k) = floor((7 + sqrt(1 + 24 k)) / 2), $

with the usual Klein-bottle exception, where six colors suffice although the
formula gives seven. Thus every graph embedded on such a surface admits the same
kind of complete multipartite envelope, but with $H(g)$ or $H_N(k)$ bags instead
of four.

This gives a direct topological generalization:

$ "surface embedding" -> "Heawood color map" -> K_H " completion" -> "small quotient". $

For example, a toroidal graph has a seven-color envelope. The compiler exposes
this as `surface_heawood`; the example `torus_heawood7_equal_fiber.json` builds
the corresponding $K_7$ template join.

There is also a more quantum-native surface link. Freitas proves a Heawood-type
result for algebraic connectivity: for a nonplanar surface $S$, the supremum of
the algebraic connectivity over graphs embeddable in $S$ is the chromatic number
of the surface, with the known Klein-bottle caveat. Since the long-range
tunneling paper treats algebraic connectivity/spectral gap as a search resource,
surface topology can be read as a spectral-gap budget, not only as a coloring
bound.

So nonplanar topology gives two knobs:

- a color/template upper bound, via Heawood;
- a spectral-gap ceiling, via algebraic connectivity on surfaces.

The toolkit direction is to stop asking only whether a graph is planar. Instead,
ask which surface or coarse topology is available, choose a quotient template
compatible with that topology, then engineer a fiber blowup whose quotient
spectrum satisfies the desired search criterion.

#heading("Hamiltonian Reading")

After ordering vertices by color classes, the adjacency matrix of a planar
graph has zero diagonal color blocks:

$ A_G =
  mat(
    0, A_12, A_13, A_14;
    A_21, 0, A_23, A_24;
    A_31, A_32, 0, A_34;
    A_41, A_42, A_43, 0
  ). $

The four-color completion replaces each off-diagonal block $A_(i j)$ by an
all-ones rectangular block. In CTQW language, it is a graph-engineering move:
the planar Hamiltonian support is embedded into a four-sector long-range
Hamiltonian support with complete cross-color tunneling. This connects the
four-color theorem to spatial search without claiming that the original planar
graph is Grover-optimal or deterministic-search-ready.

There is a stronger reduction hidden here. Let the color classes have sizes
$n_1,...,n_r$, $r <= 4$, and let $e_v$ denote the standard basis state at
vertex $v$. Define

$ u_i = 1 / sqrt(n_i) sum_(v in V_i) e_v $

as the normalized uniform state on color class $i$. The span of these $r$ states
is invariant under both the adjacency and Laplacian of $K_c$. In this basis,

$ A_(K_c) u_j = sum_(i != j) sqrt(n_i n_j) u_i. $

Thus the unmarked walk on the complete color host collapses from $N$ dimensions
to the weighted complete graph on the color bags.

The same calculation works for an engineered template join. If $J =
"TemplateJoin"(Q,V)$, then

$ A_J u_j = sum_(i : Q(i,j)) sqrt(n_i n_j) u_i. $

So the uniform-fiber sector is not merely small; it is the weighted adjacency
matrix of the chosen template. If all fibers have the same size $m$, then this
sector is exactly $m A_Q$. For a $d$-regular template $Q$, the full adjacency
spectrum of the equal-fiber join consists of $m$ times the adjacency spectrum of
$Q$, together with additional zero modes internal to the fibers. Therefore, if
$Q$ has uniform principal eigenvector and all other adjacency eigenvalues satisfy
$abs(lambda_i) <= c d$ for some $c < 1$, then the equal-fiber join satisfies the
same spectral-ratio condition used by Chakraborty--Novo--Ambainis--Omar for
Grover-optimal CTQW spatial search. The bag construction therefore gives a
family of arbitrarily large search hosts controlled by a small engineered
template.

There is a parallel deterministic-search statement. If the fibers all have size
$m$ and the template $Q$ is Laplacian integral, then the equal-fiber template
join is Laplacian integral: the quotient Laplacian contributes $m$ times the
Laplacian spectrum of $Q$, and the internal fiber-difference modes contribute
integer eigenvalues $m d_i$. Thus Li--Luo--Feng--Li's deterministic-search
theorem applies to equal-fiber joins over Laplacian-integral templates. Complete
multipartite four-color completions are a special, more forgiving case where
the fiber sizes need not be equal.

For search with a single marked vertex $w in V_m$, refine the bag partition to

$ {w}, quad V_m - {w}, quad V_i " for " i != m. $

This refined partition is equitable for $K_c$. Consequently the search
Hamiltonians

$ - gamma A_(K_c) - P_w quad "and" quad - gamma L_(K_c) - P_w $

preserve the span of the normalized cell states. Since $r <= 4$, a
single-marked search on the four-color completion reduces to a Hamiltonian of
dimension at most five. With an arbitrary marked set $M$, splitting each color
bag into $V_i inter M$ and $V_i - M$ gives an invariant subspace of dimension at
most eight.

This is the more operational quantum link: four-coloring gives a bounded-sector
Hamiltonian reduction. The graph may have arbitrarily many vertices, or arise as
a countable/coherent limit of finite planar approximants, while the color-sector
quotient remains bounded by four before marking and by eight after marking.
That is the part that deserves the name quasi-infinite: the vertex space can
grow without changing the color-sector control problem.

The same observation gives a boundary condition for the long-range tunneling
paper: if all nonzero long-range couplings are treated as edges, then the
support graph is complete for $N > 4$, hence not planar and not four-colorable.
So four-color structure is a finite-range or thresholded-support invariant; it
does not survive an all-positive long-range completion except as a chosen
decomposition of the original planar skeleton.

#heading("Compiler Prototype")

The repository includes a small prototype compiler, `tools/search_compiler.py`.
It takes a JSON description of an engineered template, fiber sizes, and marked
counts. It emits:

- the template adjacency and Laplacian spectra;
- a CNO-style spectral-ratio diagnostic for regular templates;
- the exact uniform-fiber quotient matrices;
- the refined marked-cell quotient;
- an exploratory CTQW scan on the quotient Hamiltonian.

The compiler accepts explicit edge lists and constructors for complete graphs,
cycles, paths, complete bipartite graphs, hypercubes, complements, Cartesian
products, Heawood surface envelopes, and cycle power-law templates. This is the
first step toward a search-problem compiler: the user chooses quotient
observables and coupling templates, while the tool builds the maximal compatible
host and analyzes the small quotient Hamiltonian.

#table(
  columns: 5,
  [example], [template], [host], [ratio], [best adj. scan],
  [`k4_equal_fiber`], [complete $K_4$], [$64$], [$0.333$], [$0.994$],
  [`c5_equal_fiber`], [cycle $C_5$], [$100$], [$0.809$], [$0.991$],
  [`rook_3x3_equal_fiber`], [$K_3 square K_3$], [$90$], [$0.500$], [$0.990$],
  [`hypercube_q3_equal_fiber`], [$Q_3$], [$96$], [$1.000$], [$0.987$],
  [`torus_heawood7_equal_fiber`], [surface $K_7$], [$56$], [$0.167$], [$0.995$],
  [`cycle8_powerlaw_alpha1`], [weighted $C_8$ long range], [$80$], [$0.362$], [$0.995$],
  [`four_color_unequal`], [unequal $K_4$ fibers], [$64$], [n/a], [$0.989$],
)

These scans are not proofs of optimality. They are triage: they identify
templates whose quotient dynamics look promising, and they separate theorem
routes. Equal-fiber regular templates can use the adjacency spectral-ratio
route. Laplacian-integral templates can use the deterministic-search route.
Unequal complete multipartite color completions retain Laplacian integrality but
fall outside the simplest regular-template criterion.

#heading("End-to-End Examples")

The examples are deliberately small, but each is a complete compiler pass from
an applied search task to quotient diagnostics.

#figure(
  image("assets/case_studies.svg", width: 100%),
  caption: [Three small applied compiler examples. Yellow nodes indicate the marked quotient cell.]
)

#emph[Modular quantum processor calibration.]
The `rook_3x3_equal_fiber` instance models a 3-by-3 row/column interaction
fabric. Each tile is blown up to a fiber of possible physical variants, and the
search task is to locate one faulty module. The rook template is regular,
Laplacian integral, and has spectral ratio $0.5$; the quotient CTQW scan reaches
marked probability about $0.990$.

#emph[Long-range tunneling memory ring.]
The `cycle8_powerlaw_alpha1` instance models eight memory sectors arranged on a
ring with all-to-all cyclic couplings decaying as $1/r$. The weighted template is
regular and has spectral ratio about $0.362$, substantially better than the
sparse $C_8$ template. This is a tiny version of the long-range-tunneling design
question: tune the coupling law on the quotient, then blow it up into a larger
host.

#emph[Surface-embedded interaction fabric.]
The `torus_heawood7_equal_fiber` instance uses the Heawood seven-color envelope
for toroidal embeddings. It compiles surface topology into a $K_7$ template, then
blows up each color sector. The complete template is regular, Laplacian integral,
and strongly separated spectrally, with ratio about $0.167$.

#heading("Current Contents")

The verified construction is modest in claims but now has several reusable
pieces:

- arbitrary indexed coproducts of graph factors;
- heterogeneous and shared-palette color propagation;
- a countable edge-union universal property;
- inverse-limit thread graphs with projections and inherited colorings;
- a formal obstruction to the naive colorable-reflector idea;
- a four-color completion theorem connecting planar graphs to Laplacian
  integral deterministic-search host graphs;
- a maximal complete-join construction over color bags;
- engineered template joins and multicolor pullback constraints;
- a spectral-ratio inheritance theorem for equal-fiber template joins;
- a bounded-dimensional equitable quotient for search Hamiltonians on the
  four-color completion;
- surface-Heawood and power-law coupling constructors in the compiler prototype.

This gives a precise mathematical home for a large part of the phrase
"quasi-infinite adjoint": it is the coproduct/colimit/inverse-limit toolkit for
colorable graph components.  It does not yet construct graphs with a designed
fractal dimension.  To do that honestly, the next layer would need a metric or
growth structure on the approximants, then a verified dimension invariant.

The Toolkit addendum gives a concrete bridge to quantum spatial search:
four-colorability provides canonical Laplacian-integral completions for planar
instances, and those completions have bounded-dimensional color-sector search
quotients. The bridge is structural, not an optimality theorem for the original
graph.

The next generalization is relational rather than graph-only. A graph template
is a binary constraint. A full compiler should admit higher-arity CSP templates,
phase labels, weighted couplings, hardware locality constraints, noise models,
and oracle promise classes. In that setting "colorability" becomes one example
of a selected quotient relation, and the useful question becomes: which quotient
relations preserve a low-dimensional invariant search sector while still giving
large, resilient physical hosts?

#heading("Lean Artifact")

The formalization is in:

`Graphplay/Basic.lean`

It builds with Lean 4.30.0 using:

`lake build`

#heading("References Fetched")

- Chakraborty, Novo, Ambainis, Omar. #link("https://arxiv.org/abs/1508.01327")[Spatial search by quantum walk is optimal for almost all graphs], arXiv:1508.01327.
- King, Linnebacher, Orth, Rizzi, Morigi. #link("https://arxiv.org/abs/2501.08148")[Optimal spatial searches with long-range tunneling], arXiv:2501.08148.
- Li, Luo, Feng, Li. #link("https://arxiv.org/abs/2506.21108")[Deterministic quantum search on all Laplacian integral graphs], arXiv:2506.21108.
- Sadowski. #link("https://arxiv.org/abs/1406.0339")[Quantum spatial search on planar networks], arXiv:1406.0339.
- Wong. #link("https://arxiv.org/abs/1706.06939")[Faster Search by Lackadaisical Quantum Walk], arXiv:1706.06939.
- Weisstein. #link("https://mathworld.wolfram.com/Four-ColorTheorem.html")[Four-Color Theorem], MathWorld.
- Weisstein. #link("https://mathworld.wolfram.com/MapColoring.html")[Map Coloring], MathWorld.
- Freitas. #link("https://arxiv.org/abs/math/0109191")[A Heawood-type result for the algebraic connectivity of graphs on surfaces], arXiv:math/0109191.
