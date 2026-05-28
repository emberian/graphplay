# A Structural Review of the QRI / Gómez-Emilsson "Rapid Graph-Coloring" Claim, from the Standpoint of Graphplay

**Author:** Graphplay maintainers
**Date:** 2026-05-28
**Status:** Internal review / candidate public-facing artifact (see §6).

## 0. Scope

A reader pointed us at a passage in a recent PsyArXiv preprint by Gallimore,
Hermansson, and Hoffman, *"Traces of the Other – Are DMT Entities Real? DMT
Phenomenology in the Framework of Conscious Realism"* (OSF preprint `8qvgy`,
v2), which quotes Andrés Gómez-Emilsson (Qualia Research Institute) on DMT
"entities" rapidly and error-free colouring "highly complex, non-Euclidean,
and often hyperbolic surfaces." The passage explicitly invokes the four-color
problem and frames the phenomenon as "parallel, constraint-satisfying
computation."

The user notes that Graphplay's `Heawood (g : ℕ)` (`Graphplay/Bundle.lean`,
line 118) is *exactly* the chromatic envelope for graphs embedded on an
orientable genus-`g` surface, and that the framework's equitable-partition /
bundle / lift machinery handles *exactly* the kind of cell-uniform reduction
that would make such a coloring CSP tractable.

This document reviews how much of that connection is real mathematics, how
much is a metaphor, and what one could honestly say about it in public.

---

## 1. Source summary

**The PsyArXiv preprint (Gallimore–Hermansson–Hoffman, 2026; `8qvgy_v2`).**
The paper is a serious-but-speculative philosophy-of-mind manuscript that
re-frames DMT entity encounters inside Donald Hoffman's "conscious realism /
conscious agent" framework. Its central thesis is that DMT does not generate
hallucinatory content from internal brain activity in the usual sense, but
rather perturbs the "qualia kernel" (the operator governing transitions
between experiential states) far enough that the user temporarily perceives
*conscious agents* normally outside the human "conscious realism slice." The
paper is careful: it does not claim DMT entities are real; it proposes
*operational, intersubjective experiments* that could falsify or constrain the
hypothesis. The Gómez-Emilsson coloring passage appears in §4.2 ("Extreme
Complexity and 'Otherness'"), as one of several phenomenological signatures
the authors interpret as evidence that the perceived entities operate over a
higher-dimensional / non-Euclidean state space than human cognition does.

**The Gómez-Emilsson coloring claim.** The cited reference [74] in the
PsyArXiv paper is actually Georges Gonthier's *Formal Proof — The Four-Color
Theorem* (Notices AMS, 2008) — that is, a citation for the four-color theorem
itself, not for Gómez-Emilsson's report. The actual Gómez-Emilsson sources
adjacent in the bibliography are refs [68]–[71]: a 2025 YouTube talk *"DMT
Entities Decoded by Coupled Oscillators"* (`youtu.be/gi08eVU_-f8`), the 2016
QRI blog post *"The Hyperbolic Geometry of DMT Experiences"*
(`qri.org/blog/hyperbolic-geometry-DMT`), the 2016 essay *"Algorithmic
Reduction of Psychedelic States"* (qualiacomputing.com), and the 2021 talk
*"The Theory of Neural Annealing."* I could not find an explicit written
passage in those four sources where Gómez-Emilsson reports the rapid
four-color-style coloring phenomenon as the PsyArXiv paper paraphrases it; it
appears most likely to come from the 2025 video talk (which I did not
transcribe). I therefore treat the coloring claim as **a paraphrase the
PsyArXiv authors attribute to Gómez-Emilsson, sourced verifiably to a video I
could not text-mine, and structurally consistent with the written QRI corpus**
— but I have not verified it word-for-word.

**The broader QRI framework.** Across the written sources I read
(*Hyperbolic Geometry of DMT*, *Algorithmic Reduction*, *Symmetry Theory of
Valence 2020 Overview*), QRI proposes:

1. Conscious experience has a geometric / topological structure that can be
   measured (informally) by introspection.
2. Under DMT and similar psychedelics this structure exhibits *hyperbolic
   curvature*: experiential "objects" support more relational structure than
   fits in 3D Euclidean phenomenal space.
3. Valence (pleasantness) of an experience tracks the *symmetry content* of
   its underlying neural / phenomenal representation (the Symmetry Theory of
   Valence, STV).
4. Cognitive processes are modeled as energy redistribution on a network of
   *coupled oscillators*, with "symmetry bundles" (sets of symmetry planes
   constraining a region of experience) playing the role of soft constraints.

The QRI program is openly speculative on the consciousness side but uses
formally-defined mathematical objects (hyperbolic manifolds, coupled
oscillator networks, symmetry groups) as scaffolding. It is *not* a
neuroscience research program; it is a phenomenology-first theoretical
program that hopes to be reducible to neuroscience eventually.

---

## 2. What's structurally in Graphplay that maps to this

### 2.1 Surface Heawood envelopes

`Graphplay/Bundle.lean` defines

```lean
noncomputable def Heawood (g : ℕ) : ℕ :=
  Nat.floor ((7 + Real.sqrt (1 + 48 * (g : ℝ))) / 2)
```

This is the Ringel–Youngs / Heawood bound: every graph that embeds on a
closed orientable surface of genus `g` is `Heawood g`-colorable (and for
`g ≥ 1` the bound is sharp, achieved by `K_{Heawood g}`). For `g = 0` it
returns 4 (the four-color theorem case); for `g = 1` it returns 7 (the torus);
for `g = 2`, 8; for `g = 10`, 13; and so on. The definition is paired with
the surface-genus hardware spec in `Graphplay/Toolkit/Hardware.lean`
(`surfaceSpec g`, line 147), which carries genus as a constraint on the
physical layout a graph algorithm is allowed to use.

### 2.2 Hyperbolic surfaces

Every closed orientable surface of genus `g ≥ 2` admits a hyperbolic
metric (Gauss–Bonnet: `χ < 0`). So `Heawood g` for `g ≥ 2` *is already* the
chromatic envelope of a hyperbolic surface. When the PsyArXiv paper says
"highly complex, non-Euclidean, and often hyperbolic surfaces" and frames
this as harder than the four-color problem, the corresponding object in
Graphplay is `Heawood g` for `g` large — a finite integer, bounded above by
`⌊(7 + √(1 + 48g)) / 2⌋ = Θ(√g)`. This is the key quantitative point: even
on a very high-genus, very hyperbolic surface, the chromatic number grows
only as `√g`. The combinatorial complexity of the surface is enormous, but
the number of *colors* needed is small.

### 2.3 Equitable partitions and cell-uniform reduction

`Graphplay/Equitable.lean` defines `EquitablePartition G I` — a partition of
the vertex set of a weighted graph `G` into cells indexed by `I` such that
every vertex in cell `i` sees the same number-weighted-sum of neighbors in
cell `j`. The associated *quotient matrix* `Q : I × I → ℂ` is a faithful
algebraic shadow of `G`'s adjacency: spectra lift, walks lift, search
Hamiltonians block-diagonalize on the cell-uniform subspace.

`Graphplay/Bundle.lean::fiberPartition` then says: if you have a
`GraphBundle` over a small template graph `Q` on `I` with regular fibers
and biregular couplings, the assignment of each vertex to its fiber-index
is automatically equitable, with `I` as the cell type. This is the formal
"reduce an `n`-vertex problem on the total graph to an `|I|`-vertex problem
on the quotient" theorem.

For the surface-coloring case: a coloring of a graph embedded on a surface
of genus `g` is exactly a homomorphism into `K_{Heawood g}`. Composed with
`Graphplay/Bundle.lean::colorCompletion`, every such coloring induces a
bundle structure whose template is `K_{Heawood g}` and whose cell type has
cardinality at most `Heawood g`. The Heawood number is therefore an upper
bound on the dimension of the cell-uniform sector in which any
coloring-related spectral problem lives.

### 2.4 Quantum-walk-shaped CSP solvers

`Graphplay/Search.lean` and the `searchHamiltonian` in
`Graphplay/StdLib/CompleteMultipartite.lean` define a Childs–Goldstone
spatial-search Hamiltonian `H = -γ·A − P_M`. Theorem
`completeMultipartite_deterministicSearch` (line 163) states (modulo
implementation work) that on the complete-multipartite color-completion of a
proper coloring, spatial search reaches a marked vertex with constant
amplitude. Composed with §2.3, this gives a *constructive* parallel
algorithm: project the surface-embedded coloring CSP to a `Heawood g`-cell
quotient, run CTQW search on the quotient, lift back. The cell-uniform
sector bound (≤ `Heawood g`-dimensional) is the dimension of the search
problem the walk actually has to solve.

In one sentence: **Graphplay contains a formal account of how coloring a
graph on a high-genus surface reduces to a quantum-walk problem in a state
space of dimension `O(√g)`, regardless of the number of vertices.**

### 2.5 Higher-arity / hypergraph generalization

`Graphplay/Dowsing/HypergraphPST.lean` (lines 67–200) extends the bundle and
PST machinery to `k`-uniform hypergraphs via clique-expansion and incidence
Laplacians. CSPs more general than 2-CSP (graph coloring) — e.g. "no `k`
adjacent regions share a color" or "every face has exactly `k` colors" —
are exactly the kinds of constraints these hypergraph operators encode.

---

## 3. Where the connection is tight, mathematically

The strongest defensible bridge is a **complexity-of-representation**
statement, not a complexity-of-computation statement:

> **Claim (informal).** Let `G` be a finite graph embedded on a closed
> orientable surface of genus `g`. Any proper coloring of `G` factors through
> `K_{H(g)}` where `H(g) = ⌊(7 + √(1 + 48g))/2⌋`. The induced bundle
> structure (`Graphplay/Bundle.lean::colorCompletion`) is equitable with at
> most `H(g)` cells, and any operator built from the coloring — adjacency,
> Laplacian, search Hamiltonian on color-marked subsets, hypergraph
> incidence Laplacian on color-bounded face hypergraphs — has its
> cell-uniform sector of dimension at most `H(g)`. Consequently any
> spectral / walk-based reasoning about the coloring takes place in a
> finite-dimensional algebraic object whose dimension is `O(√g)` and
> *independent of `|V(G)|`*.

This is in the same shape as the PsyArXiv paragraph's "parallel,
constraint-satisfying computation." It says: the apparent combinatorial
explosion of coloring a high-genus surface is, at the level of the operator
algebra controlling the colors, an `O(√g)`-dimensional problem. The
`n`-vertex blow-up is a fiber over the small quotient; it doesn't make the
*coloring decision* harder, only the *display* of the coloring more
elaborate.

Three things this claim does honestly:

1. It is structural: it is about the *algebra of the problem*, not about a
   specific algorithm or its runtime in any computational model.
2. It does not depend on any QRI hypothesis. It is a theorem-shaped object
   in pure combinatorics and operator theory, sitting between the
   Ringel–Youngs theorem (chromatic side) and Godsil–Royle / Higman's theorem
   on coherent algebras (equitable-partition side).
3. The relevant Graphplay files are `Graphplay/Bundle.lean` (`Heawood`,
   `fiberPartition`, `colorCompletion`), `Graphplay/Equitable.lean`
   (`EquitablePartition`, `quotient`), `Graphplay/StdLib/CompleteMultipartite.lean`
   (`CompleteMultipartite`, `completeMultipartite_deterministicSearch`),
   `Graphplay/Search.lean` (`searchHamiltonian`), and
   `Graphplay/Toolkit/Hardware.lean` (`surfaceSpec g`). All of these exist
   as `noncomputable def` / `theorem` declarations; some are still `sorry`-
   blocked, which we flag as an honesty point in §4.

Several of the supporting lemmas in `Graphplay/Bundle.lean` (notably
`fiberPartition.uniform`) are currently `sorry`-blocked; the structural
*statement* is formal Lean, but the *proof* is in progress. This is the
right kind of incompleteness for a public claim ("we have stated this as a
theorem and are filling in the proof") rather than the wrong kind ("we have
asserted this and have no Lean evidence at all").

---

## 4. Where the connection is speculative or strained

### 4.1 We have no theory of consciousness

Graphplay is a framework for operator algebras associated with weighted
graphs, equitable partitions, quantum walks, and (continuous-time and
discrete-time) spatial search. It says *nothing* about phenomenal
experience, about what it is like to be a coloring CSP, or about how brain
activity gives rise to color qualia. Mapping `Heawood g` to "what a brain on
DMT does" requires assumptions we do not make and cannot defend from inside
the framework:

- That conscious experience is implementable as a quantum walk (or any
  operator dynamics) on a graph in any meaningful sense.
- That the neural / phenomenal "graph" embeds on a definable surface.
- That hyperbolic phenomenology corresponds to a *literal* hyperbolic
  surface metric somewhere — Gómez-Emilsson himself is careful to say this
  is *not* his claim in *The Hyperbolic Geometry of DMT Experiences*: "We
  do not claim 'the substrate of consciousness' is becoming hyperbolic in
  any literal sense (though we do not discard that possibility)."

### 4.2 "Entities" and "agents" have no formal counterpart

The PsyArXiv paper's central object is the *conscious agent* (Hoffman) — a
Markov-kernel-shaped object specifying transitions between experiential
states. There is *no* analogous object in Graphplay. The framework's
"agents," if you squint, would be the marked sets in a spatial search, the
fibers of a bundle, or the cells of an equitable partition — but these are
combinatorial objects, not bearers of experience. Any mapping between
Graphplay-cells and DMT-entities is a free metaphor, not a derivation.

### 4.3 Phenomenological speedup ≠ cell-uniform reduction

Even taking the Gómez-Emilsson report at face value as a phenomenological
observation, we have no evidence that the underlying cognitive system
implements anything resembling our equitable-partition reduction. The
report is consistent with our framework (it is consistent with *any*
parallel CSP solver that bounds its search space by topological invariants),
but consistency is the floor, not the ceiling, of evidence. Many other
mechanisms — analog optimization, continuous neural attractor dynamics,
random-projection-style guessing — could equally produce "fast coloring on
exotic surfaces" if the surfaces are perceived rather than computed in our
sense.

### 4.4 The chromatic envelope grows; the report is qualitative

The PsyArXiv paragraph says the coloring becomes intractable for humans
"as the surface grows or departs from Euclidean geometry." Our framework's
`Heawood g = Θ(√g)` *does* grow — the small-cell-count claim is only small
relative to `|V(G)|`, not absolute. A genus-100 surface admits
9-chromatic graphs; a genus-10000 surface admits 70-chromatic graphs. The
phenomenological "almost instantaneous" coloring is reported regardless of
perceived complexity, but `Heawood` does not predict invariant speed —
it predicts only a sub-`|V|` scaling. The two could agree by coincidence and
disagree on closer inspection.

### 4.5 We did not verify the primary citation

As noted in §1, the coloring claim is most likely sourced from a 2025
YouTube talk by Gómez-Emilsson that I did not transcribe. The PsyArXiv
paragraph is a paraphrase, and refs [74] is a misdirection (Gonthier's
proof of the four-color theorem, not Gómez-Emilsson). A more careful pass
on the primary QRI source should precede any public claim that *the QRI
position* is X.

### 4.6 Honest verdict

**Graphplay provides a structural account of how rapid coloring of
high-genus surfaces could be a tractable problem.** It does *not* provide
an account of what is happening in conscious experience; nor does it
provide independent evidence about altered states. The two programs share
some of the same mathematical scaffolding (graphs, operators, symmetries,
hyperbolic spaces) but ask different questions and use different ground
truths.

---

## 5. Possible research bridges

These are speculative on purpose; they describe what could be done, not
what we are claiming has been done.

### 5.1 A QRI-style network model as a `GraphBundle` over a hyperbolic template

If a future QRI write-up specifies a network model of cognition as
"oscillators coupled along a hyperbolic graph," that object can be encoded
in Graphplay as a `GraphBundle Q V`:

- `Q : SimpleGraph I` is the *template* — a small graph capturing the
  topological / symmetry content of the proposed network (e.g. a
  triangle-group quotient, or the 1-skeleton of a hyperbolic tessellation
  in genus `g`).
- `V : I → Type` gives the fibers — for an oscillator network these would
  be (idealized) phase variables or local Hilbert spaces.
- The couplings encode the oscillator interactions.

The bundle's total graph has size `n · |I|`; the equitable-partition
quotient gives back a problem of dimension `|I|`. If `|I|` is bounded
(as it would be for any genus-`g` tessellation with finitely many cell
types), this is a constructive `n`-independence result for spectra,
walks, and search. This is a concrete, executable suggestion.

### 5.2 Symmetry theory of valence ↔ phantom-symmetry / equitable refinement

QRI's *Symmetry Theory of Valence* (STV) proposes valence tracks the
symmetry content of a neural representation. Graphplay's equitable
partitions, coherent algebras (`Graphplay/Dowsing/CoherentAlgebra.lean`),
and Weisfeiler–Leman refinement (`Graphplay/Algorithm/WLRefinement.lean`)
are *algorithms for detecting and quantifying symmetry in graphs*. There
is a structural parallel: both ask, "given a putative network of
relations, how symmetric is it under permutations preserving the
relations?" If STV were ever formulated as a precise statement about a
graph-theoretic object (e.g. "valence is proportional to the dimension of
the automorphism group of the dominant equitable partition"), it would
have a Lean-statable version. As of the 2020 overview, STV is not yet
that precise. The parallel is structural, not derivational.

### 5.3 One concrete prediction

If one takes the Gómez-Emilsson coloring report as a phenomenological
*data point* and one adopts (as a working hypothesis) that the cognitive
system implementing it does so via something cell-uniform-reduction-shaped,
then the framework predicts:

> The number of "color sectors" of activity supporting any such coloring
> percept is bounded by `Heawood g` for the perceived genus `g`, regardless
> of the visual complexity of the surface.

Operationally: if one could quantify the "number of distinct color
classes" stably present in a DMT-state introspective report, our framework
would predict that number stays in the `√g`-envelope. This is *not* a
prediction Graphplay makes about brains — it is a prediction Graphplay
makes about *any system that solves this CSP using the equitable-partition
reduction*. Whether brains-on-DMT are such a system is precisely the
contested empirical question.

If the report instead routinely featured arbitrarily many color classes
with no upper bound, the framework's reduction story would be wrong, and
some other mechanism would be the right model.

---

## 6. Honest assessment

1. **Graphplay is not a theory of consciousness.** It is an operator-algebra
   and combinatorics library, with formal-verification ambitions. It says
   nothing about qualia, agents, or experience as such.

2. **The structural bridge is real, narrow, and worth stating.** The
   `Heawood g` bound and the `fiberPartition` reduction together formalize
   exactly the question "how can coloring a complicated surface be a
   small-dimensional problem?" That is a real piece of mathematics. It
   sits comfortably next to the Ringel–Youngs theorem and the
   Bose–Mesner / coherent-algebra literature. It is not a QRI result and
   does not need QRI to be a result.

3. **The QRI / DMT framing is not load-bearing for the math.** It is also
   not undermined by the math. The two are compatible at the level of
   shared scaffolding (graphs, operators, symmetries, hyperbolic surfaces);
   they are not compatible (or incompatible) at the level of
   *what experience is*.

4. **We are not claiming any QRI hypothesis is correct.** We are claiming
   that *if* one wants a formally-verified mathematical model of "parallel
   CSP on hyperbolic surfaces with bounded color-sector dimension,"
   Graphplay is one such model. That is a service offer, not an
   endorsement.

5. **We did not verify the original Gómez-Emilsson primary source
   word-for-word** (most likely a 2025 video talk). The PsyArXiv paragraph
   that surfaced this connection cites Gonthier 2008 for the four-color
   theorem itself; the QRI attribution is to a parallel cluster of
   references [68]–[71] which we read in part. Future versions of this
   document should pin down the primary citation precisely.

### Shipability

This review is **shippable as a public-facing artifact only with edits**:

- §3 needs to either (a) finish the `sorry`-blocked proofs in
  `Graphplay/Bundle.lean::fiberPartition` and
  `Graphplay/Equitable.lean::quotient_apply`, or (b) be re-framed in the
  conditional ("we have stated this as a theorem; proof in progress").
  The current draft does the latter. Both are honest; (a) is stronger.
- §5.3's prediction needs to be re-phrased to not sound like a prediction
  *about brains*. It is a prediction about *the cell-uniform reduction
  mechanism*. Brains may or may not implement it.
- §1's identification of the primary Gómez-Emilsson source should be
  pinned down (probably by watching the 2025 YouTube talk and citing
  timestamps), or the document should explicitly say "we have not
  independently verified the primary source; we relied on the paraphrase
  in Gallimore et al. (2026) §4.2."

With those edits, this is a defensible bridge document: it gives QRI /
philosophy-of-mind readers a precise mathematical object to talk to, and it
gives Graphplay readers an outside-world phenomenon to point their
machinery at, without either side overstating its claims.

Without those edits, it should stay internal: the math is correct but the
framing leans further toward QRI's conclusions than the Graphplay framework
alone supports.

---

## References

- Gallimore, A. R.; Hermansson, N.; Hoffman, D. D. *Traces of the Other –
  Are DMT Entities Real? DMT Phenomenology in the Framework of Conscious
  Realism.* PsyArXiv preprint `8qvgy`, v2, 2026.
  `https://osf.io/preprints/psyarxiv/8qvgy_v2`. Local copy:
  `references/psyarxiv_8qvgy.pdf`.
- Gómez-Emilsson, A. *The Hyperbolic Geometry of DMT Experiences:
  Symmetries, Sheets, and Saddled Scenes.* QRI blog, 2016-12-12.
  `https://www.qri.org/blog/hyperbolic-geometry-DMT`. Local copy:
  `references/qri_hyperbolic_geometry_dmt.html`.
- Gómez-Emilsson, A. *Algorithmic Reduction of Psychedelic States.*
  Qualia Computing, 2016-06-20.
  `https://qualiacomputing.com/2016/06/20/algorithmic-reduction-of-psychedelic-states/`.
  Local copy: `references/qri_algorithmic_reduction.html`.
- Gómez-Emilsson, A. *The Symmetry Theory of Valence: 2020 Overview.*
  QRI blog, 2020-12-17.
  `https://www.qri.org/blog/symmetry-theory-of-valence-2020`. Local copy:
  `references/qri_stv.html`.
- Johnson, M. E. *Neural Annealing: Toward a Neural Theory of Everything.*
  Open Theory, 2019. `https://opentheory.net/2019/11/neural-annealing-toward-a-neural-theory-of-everything/`.
  Local copy: `references/qri_neural_annealing.html`.
- Gómez-Emilsson, A. *DMT Entities Decoded by Coupled Oscillators.*
  YouTube talk, 2025. `https://youtu.be/gi08eVU_-f8`. **Not transcribed
  for this review.**
- Gonthier, G. *Formal Proof — The Four-Color Theorem.* Notices of the AMS
  **55**(11), 1382–1393, 2008.
- Ringel, G.; Youngs, J. W. T. *Solution of the Heawood map-coloring
  problem.* Proc. Natl. Acad. Sci. USA **60**(2), 438–445, 1968.

**Graphplay files cited:**

- `Graphplay/Bundle.lean` — `Heawood`, `GraphBundle`, `colorCompletion`,
  `fiberPartition`.
- `Graphplay/Equitable.lean` — `EquitablePartition`, `quotient`,
  `branching_eq`.
- `Graphplay/StdLib/CompleteMultipartite.lean` — `CompleteMultipartite`,
  `completeMultipartite_laplacian_spectrum`,
  `completeMultipartite_deterministicSearch`.
- `Graphplay/Search.lean` — `searchHamiltonian`, `searchEvolve`,
  `IsOptimalSearch`.
- `Graphplay/Toolkit/Hardware.lean` — `surfaceSpec`, `HardwareSpec`,
  `surfaceGenus`.
- `Graphplay/Dowsing/HypergraphPST.lean` — clique-expansion Laplacian,
  hypergraph incidence operators (for `k`-CSP generalization).
- `Graphplay/Dowsing/CoherentAlgebra.lean` — coherent / Bose–Mesner-style
  closure of the equitable-partition quotient (relevant to §5.2).
- `Graphplay/Algorithm/WLRefinement.lean` — Weisfeiler–Leman color
  refinement (the algorithmic discovery side of equitable partitions).
