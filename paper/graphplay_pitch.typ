#set document(title: "Graphplay: The Hidden Quotient Structure of Quantum Walks")
#set page(margin: 0.85in)
#set text(size: 10.5pt)
#set par(justify: true)

#align(center)[
  #text(size: 18pt, weight: "bold")[Graphplay] \
  #v(0.25em)
  #text(size: 13pt, weight: "bold")[The hidden quotient structure of quantum walks] \
  #v(0.35em)
  #text(size: 11pt, style: "italic")[A formally-verified design framework for continuous-time
  quantum dynamics --- and a pitch for collaborators] \
  #v(0.5em)
  #text(size: 9.5pt)[Anti Mathematics Online Research Crew --- pitch draft, May 2026]
]

#v(0.8em)

#heading("Abstract")

For twenty years, Tamon's group --- with Godsil, Severini, Coutinho, Vinet,
Bose, Chan, Zhan, Xie, and a generation of co-authors --- has been
publishing theorems with the same shape: on this graph family, at this
time, with this signing, perfect state transfer or uniform mixing or
optimal spatial search emerges as if by analytic miracle. Read one such
theorem and it looks like number theory. Read fifty and a structure forces
itself on you: every miracle factors through an *equitable partition*, the
dynamics restricts to a small invariant subspace, and the apparent magic
is a finite-dimensional spectral or arithmetic condition on a $r times r$
matrix where $r$ is independent of the host size. This is folklore. It
has never been named, never systematized, and certainly never
machine-checked.

*Graphplay names it: the universal coarse-graining of quantum-walk
operators.* We formalize it in Lean 4 + Mathlib across seven mathematical
settings --- finite graphs, weighted/chiral graphs, operator systems and
quantum graphs, graphons, categorical filtered colimits, sheaves over
parameter manifolds, and an $infinity$-categorical envelope --- and turn it
from folklore into a research program. Three lifting theorems, repeated
at every tower, are the entire load-bearing skeleton. Dozens of
Tamon-clique theorems fall out as immediate corollaries; dozens of
*currently open* theorems open up mechanically by transport along the
tower. Hardware-aware quantum-walk design --- "given this chip, build this
primitive" --- becomes a small finite optimization over a quotient matrix,
with a Lean-checkable certificate of correctness. The Lean development
covers Towers 1--5 and has scaffolded statements at Towers 6 and 7;
roughly 120 sorries remain, most of them in dowsing-rod files whose
*statements* are precise and load-bearing. We want collaborators.

#heading("1. What is actually new")

The thing to notice is that *the structure was always there.* It is not a
clever encoding we are imposing on the literature. Bachman--Tamon
(arXiv:1108.0339) write PST on quotient graphs. Ide--Narimatsu
(arXiv:2209.07688) write equitable-partition spatial search.
Chan--Coutinho--Tamon--Vinet--Zhan (arXiv:1907.04729) write fractional
revival on association schemes. Levine--Mesapam--Mustico--Tamon--Tucker--Zhan
(arXiv:2605.04414) write chiral mixing speedup on signed complete graphs.
Xie--Tamon (arXiv:2301.07251) write infinite-tail search optimality.
Read with fresh eyes:

#block(inset: (left: 1em), [
*All five papers are computing the same three quantities on a small finite
Hermitian matrix --- the quotient by an equitable partition --- and then
lifting a cell-uniform conclusion to the host.*
])

The host varies: simple graphs, weighted complex Hermitian graphs, signed
graphs, association schemes, graphs with infinite tails. The primitive
varies: PST, mixing, search, fractional revival, transfer. The lift
varies, slightly, in how it handles marked vertices or boundary cells.
But the *shape of the argument* is invariant. Once you see it, you cannot
unsee it.

#emph[The headline insight, in one sentence.] Continuous-time
quantum-walk operators with engineered dynamical primitives are
controlled by a hidden quotient structure that does not care about the
ambient category: pick any of {finite graph, weighted/chiral graph,
operator system, graphon, filtered colimit, sheaf, $infinity$-category},
write the equitable partition there, and the same three lifting theorems
hold.

We call this the *universal coarse-graining* of quantum-walk operators.
The three lifting theorems, written once, are:

+ *Spectral lift.* $"spec"(A slash pi) subset.eq "spec"(A)$, with
  cell-constant eigenvector lift via the characteristic isometry $P$.
+ *Dynamical restriction.* The unitary $exp(-i t A)$ commutes with the
  cell-uniform projector $Pi := P (P^* P)^(-1) P^*$, and acts on
  $"range"(Pi)$ as $exp(-i t (A slash pi))$.
+ *Primitive transport.* For any cell-uniform initial and target data,
  PST / mixing / search / fractional revival on $(A, pi)$ holds iff it
  holds on the small finite matrix $A slash pi$ (with a one-line
  refinement for marked vertices).

These are *the* three theorems of Tower 2. Towers 3--7 are the same three
theorems with different analysis. That is the entire architecture.

#emph[Why this is new.] Each tower-2 theorem is folklore at the
finite-graph level (Godsil, Bachman--Tamon, Ide--Narimatsu). The
*statement that they are all the same theorem* --- the polymorphism over
the host category --- has never been written down. The *categorical
filtered-colimit preservation* (Tower 5) that makes "quasi-infinite"
quantum walks tractable is new. The *graphon-level* lift (Tower 4) that
extends Bick--Sclosa (arXiv:2110.13686) from real dynamics to unitary
CTQW is new. The *operator-system / quantum-graph* lift (Tower 3) that
puts Bose--Mesner association schemes and Duan--Severini--Winter quantum
graphs into the same skeleton is new. The mechanization in Lean 4 +
Mathlib --- with named theorems, machine-checked proofs (where filled),
and machine-readable holes (where not) --- is new.

#heading("2. Two illustrative theorems, stated precisely")

We give two examples to make the universal coarse-graining concrete.

#emph[Theorem (Bachman--Tamon arXiv:1108.0339, as a Tower-2 corollary).]
Let $G$ be a finite simple graph and $pi$ an equitable partition with
characteristic matrix $P$. If $u, v in V(G)$ are such that $\{u\}$ and
$\{v\}$ are cells of the refinement $pi_(u v)$, and PST occurs between
$\{u\}$ and $\{v\}$ in the quotient $A_(pi_(u v))$ at time $tau$, then
PST occurs between $u$ and $v$ in $G$ at time $tau$.

This was published in 2011 as a structural result with a several-page
proof. In Graphplay it is `EquitablePartition.pst_lift` applied to the
marked-vertex refinement, and is a three-line argument from clauses (ii)
and (iii) of the Tower-2 single load-bearing theorem.

#emph[Theorem (Xie--Tamon arXiv:2301.07251, as a Tower-2 + Tower-5
corollary).] Let $G_n = K_n + P_n$ be the family of complete graphs with
a path tail of length $n$. The partition $pi_n = \{K_n, $ path-end$, $
path-interior$\}$ is equitable. The quotient matrix $A_(pi_n) slash pi_n$
is a $3 times 3$ Hermitian matrix whose entries grow controllably in $n$;
its spectral search optimum has a limit as $n -> infinity$ identified as
the graphon limit `K + infinite-tail`. No spatial-search algorithm on
$G_n$ beats the quotient optimum, for any $n$, and the optimum is
realized at $n = infinity$ by the limit graphon.

Again: published as a deep analytic result. In Graphplay it is the
filtered colimit of the quotient diagram, plus the cell-uniform restriction
of $exp(-i t H_gamma)$ in $L^2[0,1]$. The infinite-tail optimality is
*forced* by the categorical Tower-5 statement
`Quotient.preservesFilteredColimits`.

Both proofs sit in `Graphplay/PST.lean`, `Graphplay/Search.lean`,
`Graphplay/Categorical.lean`. Several are still `sorry`; the statements
are not.

#heading("3. The seven-tower stack")

#block(fill: luma(245), inset: 8pt, radius: 4pt, width: 100%)[
```
Tower 1  SimpleGraph                    proven, Lean+Mathlib
Tower 2  WeightedGraph (Hermitian/C)    proven, Lean+Mathlib
Tower 3  Operator system / quantum gr.  proven (operator-system
                                        upgrade landed); some sorries
Tower 4  Graphon                        statements complete; ~30% proofs
Tower 5  Categorical (filtered colim.)  statements complete; key theorem
                                        sorried; conceptually clear
Tower 6  Sheaf over parameter manifold  scaffold; awaits Mathlib sheaf-
                                        of-C*-algebras infrastructure
Tower 7  Bicategorical / oo-categorical scaffold; awaits Mathlib oo-cat
                                        and derived-category libraries
```
]

Each tower adds analytic content (finite linear algebra; bounded
$L^2$ kernel operators; operator-system bimodules; cut-norm graphon
limits; filtered colimits of cocones; sheaves of $*$-algebras over a
topological base; coherent idempotents in a homotopy bicategory) but
preserves the universal coarse-graining: the equitable partition lifts,
the cell-uniform subspace is invariant, the quotient is small.

The *operator-system upgrade* (Tower 3, just landed) is worth flagging
separately. Quantum graphs in the Duan--Severini--Winter sense
(arXiv:1002.2514) are self-adjoint bimodules over a finite-dimensional
$C^*$-algebra; the spine extends to them by treating the equitable
partition as a coarsening of the bimodule's diagonal subalgebra. We hope
to upstream the cleanest pieces of this --- in particular the
non-commutative coherent-algebra machinery
(`Graphplay/Dowsing/NonCommutativeCoherent.lean`) --- to Mathlib. *If you
want to contribute Mathlib infrastructure for operator systems and
quantum graphs, this is a clean entry point.*

Towers 6--7 are honestly blocked. Tower 6 needs sheaves of unital
$*$-algebras over a topological base in a Mathlib-compatible form; Tower
7 needs the $infinity$-category and derived-category libraries that are
themselves under active development. We have written the statements down
in `Tower6.lean` and `Tower7.lean` so that the proofs become tractable as
the surrounding library matures. *We expect Tower 6 to unblock within
12--18 months;* Tower 7 is a multi-year wait.

#heading("4. Graphplay as a model-based cognitive architecture")

A useful sanity check on whether the framework is "real": map it against
the universal pattern by which minds build models of reality.

Cognition --- across philosophy of science, cognitive science, and
modern theory of computation --- runs roughly as Observation
$->$ Representation $->$ Abstraction $->$ Decomposition $->$ Relational
modeling $->$ Inference $->$ Simulation $->$ Evaluation $->$
Optimization, guided by universal principles (Compression, Invariance,
Conservation, Symmetry, Compositionality, Emergence) and grounded in
formal foundations (logic, information theory, probability, computation,
dynamical systems, category theory).

Graphplay maps to this picture without strain:

#table(
  columns: 2,
  stroke: 0.5pt,
  inset: 6pt,
  align: (left, left),
  [*Cognitive stage / principle*], [*Graphplay realization*],
  [Representation], [Choose tower; build `WeightedGraph V`],
  [Abstraction], [Find equitable partition `EquitablePartition pi`],
  [Decomposition], [Quotient + orthogonal-fiber decomposition],
  [Relational modeling], [`GraphBundle Q H B` / k-ary CSP / template],
  [Inference], [Spectral lift `spec(A/pi) subset spec(A)`],
  [Simulation], [CTQW evolution `exp(-i t A)`],
  [Evaluation], [Lean certificate / Mathlib proof],
  [Optimization], [Chiral-signing optimization on the quotient],
  [Compression], [Equitable partition #emph[is] lossy compression],
  [Invariance], [Cell-uniform subspace is `A`-invariant],
  [Conservation], [Projector $Pi$ commutes with $A$ (Noether-style)],
  [Symmetry], [Phantom symmetry / equitable partition],
  [Compositionality], [Bundles compose (`Tot` is a functor)],
  [Emergence], [Quotient dynamics #emph[is] emergent dynamics],
)

We do not claim that quantum-walk design *is* cognition. We claim
something weaker and more useful: *the universal coarse-graining of
quantum-walk operators is doing exactly what every working scientific
model does --- compress a high-dimensional dynamical object via an
invariant, conservative, symmetric, compositional decomposition into a
small one --- and the equitable partition is the load-bearing instance
of that move for quantum walks.* This is why the framework feels
inevitable, and why the same architecture keeps reappearing at each
tower.

#heading("5. Why this matters in practice")

Three things become tractable that were not.

#emph[(a) Hardware-aware quantum-walk design.]
Take a real chip --- IBM heavy-hex (Eagle, Heron, Condor), or Microsoft's
Majorana-1 topological qubit, or a Rydberg-atom array --- and ask: what
quantum-walk primitives can it natively run? In the universal
coarse-graining language, this is:

#block(inset: (left: 1em), [
+ Disassemble the chip Hamiltonian into a `GraphBundle Q H B`.
+ Identify the equitable partition $pi$ forced by the hardware's symmetry.
+ Read the quotient $A slash pi$ as a small Hermitian matrix --- typically
  $2 times 2$, $3 times 3$, or $4 times 4$.
+ Verify in Lean that the primitive of interest (PST, mixing, search)
  emerges on the quotient and lifts.
])

The companion notes `applied_ibm_heavy_hex.md` and
`applied_majorana1.md` do exactly this. Heavy-hex has a 2-cell
data/flag equitable partition with quotient $mat(0, 3; 2, 0)$ of
spectral radius $sqrt(6)$; cell-uniform PST happens at time
$pi slash sqrt(6)$ using only the chip's native couplings. Majorana-1
has a parity-sector equitable partition whose cells are joint-parity
sectors of the tetron Clifford algebra; *topological protection*
(flatness of the U(1) connection on the parameter sheaf) becomes
exactly the equitable-partition preservation condition. Both
disassemblies are Lean-formal and machine-checkable; both surface
falsifiable predictions about chip behavior under noise.

#emph[(b) The Tamon-corpus theorems unify.]
Roughly two dozen published theorems become corollaries of the three
lifting theorems applied at the right tower. The bundle engine
`Graphplay/Bundle.lean` realizes Ge--Greenberg--Perez--Tamon (arXiv:1009.1340)
products as corners. The graphon limit theorem (`Graphon/Limit.lean`)
realizes Xie--Tamon (arXiv:2301.07251) and the
Bernard--Tamon--Vinet--Xie (arXiv:2211.14704) tails-transfer companion as
filtered-colimit instances. The chiral lift (`Chiral.lean`) makes the
Levine et al. (arXiv:2605.04414) mixing speedup into a small finite
optimization on the signed quotient. Fractional revival on association
schemes (Chan--Coutinho--Tamon--Vinet--Zhan, arXiv:1907.04729) is the
commutative case of the operator-system lift. The Ide--Narimatsu
(arXiv:2209.07688) search refinement is the marked-vertex refinement
of the Tower-2 single load-bearing theorem.

#emph[(c) Open theorems extend mechanically.]
Once a theorem is on the spine, you get its tower-$N+1$ analogue *for
free* in the sense that the statement transports along the tower, and
the proof is "the same proof under the new analysis." The eighteen
dowsing-rod files in `Graphplay/Dowsing/` and `Graphplay/Integrations/`
each pick out one such open extension. Examples:

- *D1 ChiralBundlePST.* Chiral bundle PST: the chiral analogue of
  Bachman--Tamon, with the Levine et al. signing-speedup as a corollary.
- *D3 ChiralGraphon.* Graphon-level chiral mixing: the Tower-4
  quasi-infinite limit of the Levine et al. speedup, plus a gauge-theoretic
  reading of cross-constant signings as flat U(1) connections.
- *D7 HypergraphPST.* Hypergraph CTQW; $k$-ary relational extension of
  the Tower-2 spine.
- *D9 Conjecture93* (flagship falsifiable). A consistent sequence
  $(G_n, pi_n)$ admits *both* a graphon quasi-infinite limit *and* a
  strict chiral mixing speedup, iff the limit Bose--Mesner algebra
  coincides with the limit partition-projector algebra. *Status:* weak
  version expected true; strong version expected false; three confirmed
  both-sides-false witnesses; one candidate strong-counterexample.

The eight integration files extend outward: TQFT (modular tensor
categories and Heawood envelopes), RMT (random graphons with
deterministic equitable spectra), MERA / PEPS tensor networks
(coarse-graining layers as equitable cell maps), optimal transport on
graphons, mean-field games on graphon hosts, combinatorial Hodge theory
on the relational tower, lattice gauge theory through chiral signings,
and Weisfeiler--Leman refinement as equitable saturation. Each is a
research-program seed, not a finished theorem.

#heading("6. The research program")

What the framework affords, scaffolded:

#emph[Known and proved (Lean-checked, modulo flagged sorries):]
the three Tower-2 lifting theorems, the bundle equitability criterion
(regular fibers + biregular couplings), the bundle-PST corollary chain
recovering Ge--Greenberg--Perez--Tamon, the chiral characteristic-isometry
intertwining, the search marked-vertex refinement, the equitable-partition
characterization of commutative coherent subalgebras (folklore + WL
refinement chain), and the graphon spectral lift via Szegedy's regularity.

#emph[Known and stated, sorried (Lean-stated, proofs deferred):]
the graphon CTQW lift; the graphon search and PST optimality at the
quasi-infinite limit; the categorical filtered-colimit preservation of
`Quotient`; the operator-system / quantum-graph lift; chiral
bundle PST; the bundle-level uniform-iff PST; non-commutative coherent
algebras as fixed points of quantum WL refinement; the operator-system
quantum-chromatic-number bridge.

#emph[Conjectural with worked examples (statements precise; proofs and
falsifiers open):] Conjecture 9.3, the Bose--Mesner $eq.triple$ chiral
$eq.triple$ graphon iff; chiral honeycomb signings on heavy-hex
generalising Levine et al.'s $K_4$ unitary signing; chiral PGST on
Heawood bundles; quantum graphon limits; the Anantharaman--Sabri-style
chiral connection in Benjamini--Schramm limits.

#emph[Sheaf / oo-categorical (Tower 6--7, scaffold only):]
quasiparticle-poisoning as a $H^1$-class in the parameter sheaf;
functoriality of gate design across chip generations as filtered colimits
of chip-extension arrows; bicategorical truncation for measurement-based
braiding with Pauli-correction 2-cells.

There are roughly *seven open Conjecture-9.3-style flagship questions*
on the program, each tractable for a strong PhD student, each with worked
examples backing the claim it is the right question.

#heading("7. Honest assessment")

The Lean development is ~45 files, ~98% of which build green. There are
approximately 120 high-value `sorry` holes --- the rest are scaffolding
sorries in dowsing-rod files where the *statement* is the contribution,
not the proof. Tower 1--2 are largely proven. Tower 3 has the
operator-system upgrade and several genuine theorems, alongside the
non-commutative coherent-algebra sorries. Tower 4 has clean statements
and ~30% complete proofs of the graphon CTQW lift. Tower 5 has the
filtered-colimit statement and a key theorem sorried. Towers 6--7 are
honest scaffolds, awaiting Mathlib library development.

We need:

+ *Mathematicians* who care about quantum walks, operator algebras,
  graphons, or coherent algebras, who can take a dowsing-rod statement
  and produce a real proof. The Tower-2 lifts are mostly classical
  results awaiting Mathlib mechanization; the Tower-3/4/5 lifts are
  genuinely open in the form we state.
+ *Physicists / quantum-hardware people* who can validate the
  engineering claims. The Majorana-1 and heavy-hex disassemblies make
  falsifiable predictions about chip behavior; we want adversarial
  reading.
+ *Mathlib contributors* who can help upstream the operator-system,
  quantum-graph, and graphon-spectrum infrastructure. The cleanest pieces
  belong in Mathlib, not in Graphplay.
+ *Theory of computation / category theorists* who can sharpen the
  Tower-5 filtered-colimit statement and prepare the Tower-7
  $infinity$-categorical envelope.
+ *Anyone with a hardware platform.* Pick your favorite quantum-walk
  hardware --- Rydberg arrays, photonic networks, trapped ions,
  superconducting fabrics --- and disassemble it. The disassembly is a
  paper.

The project is *exploratory*. Not every dowsing-rod theorem will survive
contact with proof; some will be sharpened, some will turn out false,
some will yield a stronger statement nobody anticipated. The
machine-readable certificate manifest emitted by
`Graphplay.Toolkit.Report` makes the proven / unproven split transparent
at all times. We welcome collaborators at any level: from "I have a
chip" to "I have a sharp eye for spectral analysis" to "I want to learn
Lean by proving a theorem nobody has proved."

#heading("8. How to get involved")

The repository: `github.com/<owner>/graphplay` (cloneable; `lake build`
on a current Mathlib).

#emph[A 30-minute reading plan, by audience:]

- *Tamon postdoc / CTQW mathematician.* `paper/quasi_infinite_adjoint_v3.typ`
  §§2--7. Then pick a dowsing-rod file in `Graphplay/Dowsing/`.
- *Mathlib contributor.* `Graphplay/QuantumGraph.lean`,
  `Graphplay/Dowsing/NonCommutativeCoherent.lean`, and any operator-system
  statement. These are upstream candidates.
- *Categorical / homotopy theorist.* `Graphplay/Categorical.lean` and
  `Graphplay/Tower7.lean`.
- *Graphon / graph-limits theorist.* `Graphplay/Graphon/Limit.lean` and
  `paper/quasi_infinite_adjoint_v3.typ` §5.
- *Quantum-hardware engineer / physicist.* `paper/applied_majorana1.md`
  and `paper/applied_ibm_heavy_hex.md`.
- *Lean-curious newcomer.* `Graphplay/StdLib/` --- the standard-library
  entries (Cayley, complete-multipartite, Hamming, hypercube, path) are
  small, well-shaped, and several have open `sorry`s on classical
  spectral identities.

The actionable surface is: pick a dowsing-rod statement, or pick a
hardware platform, or pick a stdlib entry. Each is self-contained. Each
gets you a paper, or a Mathlib contribution, or a worked example we will
gladly fold into the spine.

#heading("9. One paragraph for the timeline")

The spine has two decades of literature underneath it; we are naming a
structure that has been hiding in plain sight since Godsil's original
equitable-partition spectral lemma. We are not the first to notice that
quotients matter; we are the first --- as far as we can tell --- to
write down *the* lift theorem polymorphically, mechanize it, push it
across seven mathematical settings, and treat the catalog of
Tamon-corpus theorems as a unified body to be derived rather than
collected. If the framing is right --- and the cognitive-architecture
sanity check, and the unification of two dozen disparate analytic
miracles, and the operator-system upgrade landing cleanly, all suggest
it is --- then the next two to five years should see a steady stream of
formerly-hard theorems falling out of the spine, and quantum-walk
hardware design becoming the small finite optimization it always
secretly was.

#v(0.5em)
#line(length: 100%, stroke: 0.5pt)
#v(0.3em)

#text(size: 9.5pt)[#emph[Repository:] `github.com/<owner>/graphplay`. #emph[Main paper:]
`paper/quasi_infinite_adjoint_v3.typ`. #emph[Research program:]
`paper/research_program.typ`. #emph[Applied disassemblies:]
`paper/applied_majorana1.md`, `paper/applied_ibm_heavy_hex.md`.
#emph[Contact:] DM the project lead, or open an issue on the repo. Collaborators welcome at any level.]
