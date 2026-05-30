# Mechanistic Interpretability & Feature-Learning vs. the Equitable-Partition-as-Mechanism Lens

Scout date: 2026-05-30. Scope: mechanistic interpretability (circuits / superposition /
induction heads) and feature-learning / learning-mechanics (grokking, feature-vs-lazy, NTK,
emergence). All assessed against **our lens**:

> A learned attention/weight matrix decomposes as `A = A_eq + R`, where `A_eq`'s cells are
> learned equivalence classes / orbits — a candidate "mechanism" the model implements.
> Hypothesis: equitable (orbit) structure ⇔ identifiable computational structure
> (circuits/heads), and emergence-of-structure during training (grokking, feature learning)
> is the model **finding an equitable partition**.

Each entry: **claim**, **relation to our lens**, and a **blunt verdict** on whether the prior
art already captures what we'd assert.

PDFs in `refs/ml-theory/`. The dir also holds a pre-existing geometric-DL / symmetry corpus
(GDL proto-book `gdl_grids_groups_graphs_2104.13478.pdf`, parameter-space-symmetry survey
`param_space_symmetry_survey_2506.13018.pdf`, G-CNNs, DeepSets, natural graph networks) which
is highly relevant context and is referenced below.

---

## 1. Induction Heads / In-Context Learning — Olsson et al. 2022
`induction_heads_2022.pdf` · arXiv:2209.11895 · Anthropic Transformer Circuits

**Claim.** A specific two-head circuit (a "previous-token head" feeding a later "induction
head") implements the copy/complete operation `[A][B]…[A] → [B]`, and is argued to be the
mechanistic source of much in-context learning. Identified via a discrete phase change in
training loss and a matching jump in an "in-context learning score."

**Relation to our lens.** Strong, concrete, and *adversarial to novelty*. An induction head
is precisely a learned rule that says "tokens equal-to-the-current-token are equivalent for
the purpose of predicting the next token" — i.e. it partitions context positions by a
*match relation* and acts uniformly on each class. That is an equivalence-class mechanism in
all but name. Crucially, it is discovered at a **phase transition during training** — exactly
the "model finds the partition" dynamic our hypothesis predicts.

**Blunt verdict.** This is the single closest prior art for the *mechanism* half of our claim,
without the vocabulary. Mech-interp already describes a head as implementing a relation
(token-match) and acting uniformly across its equivalence class. What they do **not** do:
(a) call it an equitable partition, (b) connect uniform-action-on-cells to the *spectral /
quotient* algebra (their A_eq has no D^{1/2}QD^{-1/2}-style quotient operator), or (c) claim a
general `A = A_eq + R` residual decomposition. Our novelty must live in the algebra and the
quotient, not in "heads implement grouping rules" — they got there first on that.

## 2. Toy Models of Superposition — Elhage et al. 2022
`toy_models_superposition_2022.pdf` · arXiv:2209.10652 · Anthropic

**Claim.** Features are stored as near-orthogonal directions; when features outnumber
dimensions, models pack them in **superposition**, and the geometry self-organizes into
regular polytopes / uniform structures (often tied to discrete symmetries, e.g. antipodal
pairs, tetrahedra) governed by feature sparsity and importance.

**Relation to our lens.** Tangential-but-suggestive. The emergent feature *geometry* is
symmetric (the model picks maximally-symmetric packings), which rhymes with orbit structure.
But superposition is about *representation capacity / direction packing*, not about an
equivalence relation on the rows/cols of an operator. Their symmetry is a property of the
solution's geometry; ours is a property of an operator's block structure.

**Blunt verdict.** Adjacent, not overlapping. Useful to cite as "structure that emerges in
training is often maximally-symmetric," supporting the plausibility of orbit-finding, but it
does **not** pre-empt the equitable-partition framing. Honest: don't overclaim a connection —
superposition geometry ≠ quotient of an operator.

## 3. Grokking: Generalization Beyond Overfitting — Power et al. 2022
`grokking_power_2022.pdf` · arXiv:2201.02177 · OpenAI

**Claim.** On small algorithmic datasets, networks can reach near-perfect generalization
**long after** memorizing the train set — a delayed, sudden phase transition.

**Relation to our lens.** This is the empirical phenomenon our "emergence = finding the
partition" hypothesis must explain. It establishes that there *is* a discrete structural
event during training, distinct from fitting. It does not say what structure.

**Blunt verdict.** Foundational backdrop, not competition. Cite as the phenomenon; the
*mechanism* of grokking is supplied by #4 below.

## 4. Progress Measures for Grokking via Mech-Interp — Nanda et al. 2023  ★ closest prior art on the "finding structure" half
`progress_measures_grokking_nanda_2023.pdf` · arXiv:2301.05217

**Claim.** A 1-layer transformer that groks **modular addition** is fully reverse-engineered:
it implements addition via **discrete Fourier transforms and trig identities** — i.e. it
learns the **representation theory of the cyclic group Z/p**. Grokking is decomposed into
three phases (memorization → circuit formation → cleanup) with continuous "progress measures"
that move *before* the visible generalization jump.

**Relation to our lens.** This is the most dangerous paper for our novelty claim **and** the
most directly supportive. Dangerous: it already shows "the model, during training, discovers
the **group structure** of the task" — and group representations are exactly the source of
orbits / equitable partitions. The learned circuit literally uses the group's irreducible
representations; cells of an equitable partition of a Cayley graph *are* unions of such
orbits. So "the model finds an equitable partition" is, for this task, **demonstrated** —
just phrased in Fourier/rep-theory language rather than partition/quotient language.
Supportive: it confirms the dynamics our hypothesis predicts (gradual circuit formation,
phase transition) and gives a worked example where the learned mechanism = a group-symmetry
object.

**Blunt verdict.** If we want to claim "emergence of structure = model finding an equitable
partition," Nanda et al. already proved the special case **for Cayley graphs of Z/p** under a
different name (Fourier circuits / group reps). Our defensible novelty is the **generality and
the operator algebra**: (i) equitable partition is the right object even when there is *no
group* (general graphs/attention matrices have equitable partitions without symmetry — orbit
partition ⊆ coarsest equitable partition, strict in general); (ii) the symmetric normalized
quotient `Q̃ = D^{1/2} Q D^{-1/2}` and the spectral lift give a *quantitative*,
*compositional* progress measure (block-error `‖R‖` and quotient-spectrum recovery), which is
sharper than task-specific Fourier metrics. **Frame against this paper explicitly or a
reviewer will.** "Equitable partition strictly generalizes the orbit/group picture that
grokking-mech-interp already uses" is the honest, defensible wedge.

## 5. Omnigrok: Grokking Beyond Algorithmic Data — Liu et al. 2022
`omnigrok_2022.pdf` · arXiv:2210.01117

**Claim.** Grokking is governed by the **geometry of the loss landscape** and weight norm; a
"goldilocks zone" of representation norm controls the memorize→generalize transition. Recasts
grokking as movement on the landscape rather than something special to algorithmic data.

**Relation to our lens.** Offers a *competing* (geometric/landscape) explanation of the same
emergence we want to attribute to partition-finding. Adversarially useful: a reviewer can say
"grokking is just weight-norm dynamics, no need for partitions." We should acknowledge that
the *driver* may be landscape geometry while the *learned object* is still an orbit/quotient
structure — these are not mutually exclusive (geometry explains *when*, partition explains
*what*).

**Blunt verdict.** Not prior art for our framing, but the strongest *alternative hypothesis*
to pre-empt. Cite to show we're not naive about non-symmetry explanations.

## 6. Quantization Model of Neural Scaling — Michaud et al. 2023
`quantization_model_neural_scaling_2023.pdf` · arXiv:2303.13506

**Claim.** Knowledge/skills are "quantized" into discrete chunks ("quanta") learned in a
definite order; this jointly explains smooth power-law scaling (averaged over many quanta) and
sudden emergence of individual capabilities (one quantum snapping in).

**Relation to our lens.** Conceptually parallel: a "quantum" is a discrete unit of learned
computational structure that appears at a phase transition — structurally analogous to "a cell
/ a block of the equitable partition becoming resolved." If one identified quanta with
partition refinements, emergence-of-capabilities would map onto refinement of the partition.

**Blunt verdict.** Independent framing of the same emergence-of-discrete-structure intuition,
at a *coarser* (capability) granularity than ours (operator-block). Not competing; a possible
*macro-scale* analog worth one sentence ("our block-level emergence may be the micro-mechanism
underlying quanta"). Do not claim equivalence.

## 7. Attention Heads of LLMs: A Survey — Zheng et al. 2024
`attention_heads_survey_2024.pdf` · arXiv:2409.03752

**Claim.** Taxonomy of attention-head roles (retrieval, induction, copy-suppression,
syntactic, positional, etc.) organized into a four-stage cognitive framework, surveying
methods for discovering and intervening on heads.

**Relation to our lens.** This is the breadth check on the adversarial question "does
mech-interp already describe heads in symmetry/grouping terms?" Answer: **partly**. Many
catalogued head types (positional heads, syntactic-relation heads, induction heads) are
exactly "heads that apply a uniform operation across an equivalence class of positions/tokens"
(positions equal mod offset; tokens in the same syntactic relation; tokens matching a prior
token). The field *describes* these groupings but treats them as a **taxonomy**, not as a
single unifying *algebraic* object (no quotient, no spectral lift, no `A_eq + R`).

**Blunt verdict.** The grouping intuition is pervasive and pre-existing in the head-taxonomy
literature; "heads implement grouping/relation rules" is **not** novel. The unifying claim
"every such head is a near-equitable partition of its attention matrix, and the family of them
is a coherent-algebra / quotient" **is** a new organizing principle — if we can show it buys
something (a measure, a complexity bound, a transfer result) the taxonomy doesn't.

---

## Cross-cutting prior art already in `refs/ml-theory/` (do not ignore)

- **Geometric Deep Learning (Bronstein et al. 2021, `gdl_grids_groups_graphs_2104.13478.pdf`)
  and G-CNNs / DeepSets / natural-graph-networks.** These build symmetry/equivariance in
  *by construction* (architectural prior). Our lens is the dual/inverse: symmetry (equitable
  structure) **emerges in a generic learned matrix** and is *recovered post hoc*. This is a
  clean differentiator — geometric DL imposes the orbit structure; we claim training discovers
  it. Worth stating explicitly: "we study *emergent* equitable structure, not *imposed*
  equivariance."
- **Parameter-space symmetry survey (`param_space_symmetry_survey_2506.13018.pdf`,
  arXiv:2506.13018).** Concerns symmetries of the *loss landscape / weight space* (permutation,
  scaling, conserved quantities under symmetry). Different object from ours (symmetry of the
  parameterization vs. equitable partition of the *learned operator*). Adjacent; cite to
  disambiguate which "symmetry" we mean.
- **Orbit-equivariant GNNs (ICLR 2024, found in search, not downloaded).** Explicitly relaxes
  equivariance using *orbits* and notes "equivariant functions cannot produce different outputs
  for similar nodes." This is the GNN-side cousin of our orbit-vs-equitable distinction and is
  worth a direct citation; it independently motivates orbits as the right granularity.
- **Synchronization-cluster literature (PMC11165003, found in search).** Network-dynamics work
  that *explicitly* ties dynamical clusters to **symmetry orbits and equitable partitions** of
  the graph. This is the strongest external validation that "equitable partition = emergent
  functional grouping" is a real, named, productive idea — *in dynamical systems / network
  science*, not yet in mech-interp. Strong support that the object is right; strong warning
  that it is not ours to claim as new mathematics.

---

## Bottom-line novelty verdict

**Does mechanistic interpretability already capture the grouping/symmetry structure we'd
claim?** Partially, and more than is comfortable:

- The **mechanism** half ("a head/circuit implements a uniform rule over an equivalence class")
  is *already standard* — induction heads (#1), the head taxonomy (#7), and especially the
  fully-reverse-engineered **group-symmetry** grokking circuit (#4) embody it.
- The **emergence** half ("structure appears at a phase transition during training") is *also
  established* — grokking (#3), progress measures (#4), quanta (#6).
- The specific equation of **clusters with equitable partitions/orbits** is *already a named,
  productive idea in network-dynamics / synchronization*, and **orbits** are already used in
  GNN interpretability (orbit-equivariant GNNs).

**So "the model is learning an equitable partition" is NOT a blank-slate new idea.** Its
defensible, genuinely-new contributions are narrower and must be stated as such:

1. **Strict generalization beyond groups.** Grokking-mech-interp explains structure via *group
   representations* (Fourier on Z/p). Equitable partitions exist for graphs/matrices with **no
   symmetry group at all** (orbit partition ⊊ coarsest equitable partition in general). Claiming
   the equitable partition — not the automorphism orbit — is the correct mechanistic object is a
   real, testable sharpening of the existing picture.
2. **An operator-algebraic, quantitative handle.** The symmetric normalized quotient
   `Q̃ = D^{1/2}QD^{-1/2}`, the spectral lift, and the residual `‖R‖` give a *compositional,
   measurable* progress signal and a *complexity statement* (O(n²)→O(nr) structural collapse on
   the quotient) that the existing task-specific progress measures and qualitative taxonomies do
   not. This is where Graphplay's formal machinery earns its keep.
3. **Unification.** Casting induction heads, positional/syntactic heads, and grokking circuits
   as instances of *one* object (near-equitable partition / coherent algebra of the attention
   matrix) is an organizing claim no surveyed paper makes — **valuable only if it predicts or
   buys something** (a head-discovery method, a transfer bound, a training-dynamics measure).

**Testable framing (the honest pitch).** "During training, a head's attention matrix
`A(t) = A_eq(t) + R(t)` has `‖R(t)‖` collapsing at the generalization phase transition, and the
emergent cells of `A_eq` coincide with the head's known functional role (match / position /
syntax)." This is *falsifiable* and *not already done* in this exact operator form — Nanda et
al. checked Fourier structure, not equitable-partition / quotient-spectrum structure. **Run
this on the modular-addition transformer and on a real induction head; if `‖R‖`-collapse tracks
grokking and the cells match the orbit/Fourier modes, the framing pays for itself. If it just
re-derives the Fourier circuit, it is a reformulation, not a discovery.** Be prepared for the
latter outcome on the Z/p task — the generality (non-group graphs) and the complexity bound are
the surer ground.
