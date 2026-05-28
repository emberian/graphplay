#set document(title: "An A.M.O.R.C. Note on Quasi-Infinite Graph Color Bags")
#set page(margin: 1in)
#set text(size: 11pt)
#set par(justify: true)

#align(center)[
  #text(size: 17pt, weight: "bold")[An A.M.O.R.C. Note on Quasi-Infinite Graph Color Bags] \
  #v(0.35em)
  #text(size: 10pt)[Lean-verified graph constructions and a four-color search envelope]
]

#v(0.6em)

#heading("Abstract")

We formalize a conservative reading of the phrase "quasi-infinite adjoint" for
simple graphs. The useful construction is not a reflector into colorable graphs.
Instead, it is an arbitrary indexed coproduct of graph factors, with countable
edge unions and inverse-limit thread graphs as complementary infinite
constructions.  The Lean development proves the coproduct universal property,
propagation of heterogeneous colorings through a sigma-sum palette, a universal
property for countable edge unions, inherited colorings for inverse limits, and a
small obstruction theorem showing why a naive free colorable reflector fails.

The addendum connects this machinery to quantum spatial search: the four-color
theorem gives every finite planar graph a complete multipartite four-color
completion. That completion is Laplacian integral, so the deterministic-search
theorem of Li, Luo, Feng, and Li applies to the completion, though not
automatically to the original planar graph.

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

#heading("A.M.O.R.C. Addendum: Four-Color Search Envelope")

The fetched spatial-search papers make the relevant graph invariant clear. In
the Chakraborty--Novo--Ambainis--Omar CTQW model, the search Hamiltonian is

$ H_G = - P_w - gamma A_G, $

where $A_G$ is the adjacency matrix. Their optimality criterion is spectral: the
largest adjacency eigenvector should be the uniform state and the rest of the
normalized spectrum should be bounded away from it. King--Linnebacher--Orth--
Rizzi--Morigi use a Laplacian search Hamiltonian

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

The same observation gives a boundary condition for the long-range tunneling
paper: if all nonzero long-range couplings are treated as edges, then the
support graph is complete for $N > 4$, hence not planar and not four-colorable.
So four-color structure is a finite-range or thresholded-support invariant; it
does not survive an all-positive long-range completion except as a chosen
decomposition of the original planar skeleton.

#heading("What Was Actually Obtained")

The verified construction is aggressive in size but conservative in claims:

- arbitrary indexed coproducts of graph factors;
- heterogeneous and shared-palette color propagation;
- a countable edge-union universal property;
- inverse-limit thread graphs with projections and inherited colorings;
- a formal obstruction to the naive colorable-reflector idea.
- a four-color completion theorem connecting planar graphs to Laplacian
  integral deterministic-search host graphs.

This gives a precise mathematical home for a large part of the phrase
"quasi-infinite adjoint": it is the coproduct/colimit/inverse-limit toolkit for
colorable graph components.  It does not yet construct graphs with a designed
fractal dimension.  To do that honestly, the next layer would need a metric or
growth structure on the approximants, then a verified dimension invariant.

The A.M.O.R.C. addendum gives one concrete bridge to quantum spatial search:
four-colorability provides a canonical class of Laplacian-integral completions
for planar instances. The bridge is structural, not an optimality theorem for
the original graph.

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
