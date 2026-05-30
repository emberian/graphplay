# RG / Coarse-Graining / Information-Bottleneck view of deep learning vs. the equitable-partition lens

Scout date: 2026-05-30. Scope: the renormalization-group (RG) / coarse-graining /
information-bottleneck (IB) tradition in deep-learning theory, positioned against
the Graphplay equitable-partition lens.

## Our lens (the thing we are defending / contrasting)

A learned weight or attention matrix `A` is decomposed `A = A_eq + R`, where
`A_eq` is the nearest **equitable partition** (its cells are a coarse-graining /
learned equivalence classes of nodes) and `R` is the non-equitable residual.
The cells carry a **machine-checked spectral → quotient LIFT**: spectral data
(PST, mixing, search, spectrum) of the big object descends to / lifts from the
small quotient (`Graphplay/Equitable.lean`, `Graphplay/PST/QuotientIff.lean`,
the `*Lift` family).

The sharpest single claim is the Lean theorem **`mera_exact_iff_equitable`**
(`Graphplay/Integrations/TensorNetworks.lean`): a MERA (Vidal's multi-scale
entanglement renormalization ansatz — i.e. a tensor-network *renormalization*
tower) is **exact** for a local Hamiltonian iff each coarse-graining map `c_n`
is *literally* the cell map of an **equitable partition** of the level-`n`
effective Hamiltonian, with the level Hamiltonians compatible with the induced
quotient graph. Stated via the equitable branching equation directly (not
`Iff.rfl`); the (⇐) direction is the spectral lift, the (⇒) direction extracts a
partition from the stabilized Heisenberg-picture RG flow. The cell-uniform
commutation of the disentangler is the one honestly-`sorry`-ed bit.

**Hypothesis under test:** "the equitable quotient IS a renormalization /
coarse-graining step, machine-checked." Below: who anticipated this, who extends
it, who challenges it, and the blunt verdict on what is genuinely ours.

---

## Papers (claim + honest relation)

### 1. Mehta & Schwab 2014 — "An exact mapping between the Variational Renormalization Group and Deep Learning" (arXiv:1410.3831)
File: `mehta_schwab_2014_exact_RG_deeplearning.pdf`

**Claim.** Constructs an *exact* mapping between Kadanoff's variational/block-spin
RG and stacked Restricted Boltzmann Machines (RBMs). Each RBM layer = one RG
coarse-graining step; the visible→hidden marginalization implements a
decimation. Demonstrated on 1D/2D Ising. This is the foundational "deep learning
= RG" paper.

**Relation to our lens.** This is **the closest prior art in spirit** and the
single most dangerous one for novelty: it already says, loudly, "a learned layer
IS an RG coarse-graining step." BUT the correspondence is at the level of
*partition functions / probability distributions* (block-spin variational free
energy, exactly summed Ising), not a *structural graph quotient with a spectral
lift*. There is no equitable-partition object, no quotient-graph adjacency
preserved, no eigenvalue/PST descent, and nothing machine-checked. Crucially, the
Mehta–Schwab map is *approximate-becomes-exact only for special couplings* and
was later shown (see #6) not to hold generically. Our `mera_exact_iff_equitable`
gives a **combinatorial necessary-and-sufficient condition** for exactness
(cell-map = equitable) where Mehta–Schwab gives an analogy plus worked examples.

**Verdict on overlap:** they own "DL layer ≈ RG coarse-graining (statistical-
mechanics flavor)." They do **not** own "coarse-graining step = equitable
partition with a proven spectral lift." Different category (measures vs. graph
spectra), different rigor (analogy vs. machine-checked iff).

### 2. Tishby & Zaslavsky 2015 — "Deep Learning and the Information Bottleneck Principle" (arXiv:1503.02406)
File: `tishby_zaslavsky_2015_info_bottleneck_dl.pdf`

**Claim.** Each DNN layer is a point on the information-bottleneck tradeoff curve:
it maximally compresses input `X` (minimize `I(X;T)`) while preserving relevance
to label `Y` (maximize `I(T;Y)`). Successive layers form a *Markov chain of
successively coarser representations* — a coarse-graining viewed through mutual
information.

**Relation to our lens.** IB is the **information-theoretic** sibling of our
combinatorial coarse-graining. The "successively coarser sufficient statistics"
chain is morally our tower of equitable quotients. But IB's coarse-graining is
*soft / probabilistic* (minimal sufficient statistic, lossy, optimized) whereas
an equitable partition is a *hard, exact, lossless-for-the-spectrum* equivalence:
the quotient loses **no** spectral information it is responsible for (that is the
content of the lift). IB has no graph, no adjacency-preservation, no spectral
descent theorem. **Genuinely ours:** the claim that the *right* coarse-graining
is the equitable one *because* it is exactly the one under which the dynamics
(walk/PST/spectrum) factor through the quotient — a structural rather than
rate-distortion justification.

### 3. Shwartz-Ziv & Tishby 2017 — "Opening the Black Box of Deep Neural Networks via Information" (arXiv:1703.00810)
File: `shwartzziv_tishby_2017_opening_blackbox.pdf`

**Claim.** Empirical follow-up: training has a fast "fitting" phase then a long
"compression" phase in the information plane; layers converge near the IB optimal
curve. (Famously contested — see Saxe et al. ICLR 2018, "On the IB theory of deep
learning," which shows the compression phase is activation-function-dependent and
not universal.)

**Relation to our lens.** Adversarial value: this is a cautionary tale about
*soft / empirical* coarse-graining claims being fragile. Our equitable quotient
is **definitionally exact** — there is no empirical phase to be debunked; the
`A = A_eq + R` decomposition is a theorem about a fixed matrix, and the lift is
machine-checked. We should cite Saxe et al. as the reason we deliberately do NOT
rest on information-plane dynamics. **Not prior art for our structural claim**;
useful as the negative control.

### 4. Li & Wang 2018 — "Neural Network Renormalization Group" (arXiv:1802.02840, PRL 121.260601)
File: `li_wang_2018_neural_network_RG.pdf`

**Claim.** A *bijective* (normalizing-flow) deep generative model implements a
variational RG: hierarchical change-of-variables from physical space to a latent
space of reduced mutual information; the inverse flow is generative. Exact,
tractable likelihood; trains the RG transform itself.

**Relation to our lens.** This is the **constructive / learnable** counterpart:
where we *characterize* the exact coarse-graining (equitable cell map) they
*learn* an invertible one. The hierarchical-tower structure parallels our MERA
tower of quotients exactly. Key contrast: their map is **invertible** (no
information discarded, by design of normalizing flows), whereas the equitable
quotient is **non-invertible but spectrally faithful** — it discards within-cell
detail while preserving the quotient spectrum. So NeuralRG and our MERA-equitable
theorem are *dual*: invertible-lossless vs. quotient-lossless-for-spectrum.
**Genuinely ours:** the equitable *iff* characterization of when the
non-invertible coarse-graining is nonetheless exact for the target observable.

### 5. Hashimoto, Sugishita, Tanaka, Tomiya 2018 — "Deep Learning and the AdS/CFT correspondence" (arXiv:1802.08313)
File: `hashimoto_2018_deep_learning_adscft.pdf`

**Claim.** Represents the AdS/CFT (holographic) correspondence as a deep neural
network: network depth = the emergent radial/bulk (holographic, RG) direction;
the bulk metric emerges as learned weights. Depth-as-RG-scale made literal,
gravitationally.

**Relation to our lens.** Supplies the "depth = RG/holographic coarse-graining
scale" framing that legitimizes reading our **tower of equitable quotients as a
discrete RG/holographic flow** (each quotient = one step inward in scale). This is
the broad ideology our MERA theorem lives inside (MERA itself is the canonical
discrete realization of an AdS-like geometry — Swingle). But there is no quotient,
no equitable structure, no combinatorial exactness criterion, nothing checked.
**Context / legitimizer, not competitor.**

### 6. Koch-Janusz & Ringel 2018 — "Mutual information, neural networks and the renormalization group" (arXiv:1704.06279, Nature Physics)
File: `kochjanusz_ringel_2018_ml_realspace_RG.pdf`

**Claim.** Learns a *real-space* RG transformation directly from data by an
information-theoretic objective (maximize mutual information between a coarse
variable and its environment — the "real-space mutual information," RSMI). Gives
an *operational, learnable* coarse-graining that recovers correct critical
exponents, and (with the related Lenggenhager et al. PRX 10.011037, "Optimal RG
Transformation from IB") notably **shows a perfect RSMI coarse-graining does not
increase the interaction range** — a structural locality guarantee on the
coarse-grained Hamiltonian.

**Relation to our lens.** This is the **most direct technical challenger** to the
"equitable quotient is the right coarse-graining" thesis, because it independently
asks "which coarse-graining is *optimal*?" and answers with mutual information +
a *locality-preservation* theorem. Compare directly to our quotient: our
`H_quotient_compat` field demands the coarse Hamiltonian BE the quotient graph
(adjacency exactly preserved on cells) — a *hard* locality/structure guarantee,
versus their *learned, approximate* range-preservation. Their criterion is
"maximize relevant mutual information"; ours is "branching equation holds exactly
(equitable)." These can disagree: equitable partition is the unique exact one for
the *spectrum/walk*, RSMI optimizes for *long-range relevant operators*.
**This is the paper a hostile reviewer will cite to say "optimal learnable
coarse-graining is already solved."** Our rebuttal: theirs is approximate +
information-theoretic + unverified; ours is exact + spectral/combinatorial +
machine-checked, with an *iff* not an optimization.

---

## Honorable mentions (not downloaded; cited for completeness)
- **Saxe et al. 2018**, "On the Information Bottleneck Theory of Deep Learning"
  (OpenReview ry_WPG-A-) — debunks universality of the IB compression phase.
  Our negative control / reason to avoid dynamic-IB claims.
- **Lenggenhager, Gökmen, Ringel, Huber, Koch-Janusz 2020**, "Optimal RG
  Transformation from Information Theory" (PRX 10.011037) — no-range-increase
  theorem; the locality analogue of our quotient-graph adjacency preservation.
- **Stoudenmire / Evenbly**, multi-scale tensor-network architecture for ML
  (arXiv:2001.08286, IOP MLST) — MERA used *as* the learning model, coarse-
  graining input variables; closest to literally treating our object as an ML
  layer, but with no equitable/quotient/spectral-lift content.
- **Mele/Villani-adjacent "Laplacian Renormalization Group"** (arXiv:2406.02337)
  and **external-equitable-partition consensus coarse-graining**
  (O'Clery/Yuan/Stan/Barahona, PRE 88.042805) — the network-science side that
  *does* use equitable partitions for coarse-graining graph dynamics. The PRE
  paper is the single closest non-ML prior art to "equitable partition = exact
  coarse-graining of a dynamical process" and MUST be cited; it predates us on
  EEP-as-coarse-graining of consensus/Laplacian dynamics, though not the
  PST/MERA spectral-lift packaging nor anything machine-checked.

---

## Blunt verdict

**Is "equitable quotient = RG step" already established?**
*Partially, and from two independent directions — neither machine-checked, neither
spectral-lift-complete:*

1. **"DL layer = RG coarse-graining"** is thoroughly established as an *analogy /
   statistical-mechanics mapping* (Mehta–Schwab, Li–Wang, Koch-Janusz–Ringel,
   Hashimoto). None of these use an **equitable partition** or prove a
   **spectral/PST lift**; their coarse-grainings are probabilistic, learned,
   approximate, or invertible.

2. **"Equitable partition = exact coarse-graining of graph dynamics"** is
   established in **network science** (O'Clery et al. PRE 2013, external equitable
   partitions of consensus/Laplacian dynamics; the Barahona-school line). This is
   the genuine prior art for the *equitable side* and is closer than any ML paper
   — but it (a) is about consensus/Laplacian observability, not PST/quantum walks
   or attention, (b) does not connect to RG/MERA or deep learning, and (c) is not
   machine-checked.

**What is genuinely ours:**
- The **synthesis**: identifying the equitable partition (network-science object)
  *with* the RG/MERA coarse-graining step (physics/ML object) under a single
  exactness criterion. Nobody has fused these two literatures.
- **`mera_exact_iff_equitable`**: a combinatorial **iff** for MERA exactness in
  terms of equitable cell-maps. The classical Vidal–Evenbly statement is
  "exact iff RG flow finite"; recasting *finite RG flow* as *each layer is a
  literal equitable partition with quotient-compatible Hamiltonians* appears to be
  new, and it is **machine-checked** (one honest `sorry` on disentangler/cell-
  uniform commutation).
- The **`A = A_eq + R` decomposition with a proven spectral→quotient lift** for
  learned attention/weight matrices: treating the nearest-equitable projection as
  *the* coarse-graining and certifying that dynamics descend. The ML-theory
  corpus offers no analogue of the lift theorem; the network-science corpus has
  the equitable object but not the PST/walk lift nor the ML framing.

**Risk register (what a reviewer will throw at us):**
- Mehta–Schwab to claim "RG=DL is old." Rebuttal: ours is exact/combinatorial/
  verified, theirs is an analogy + special-case Ising.
- O'Clery et al. (PRE 2013) to claim "equitable-partition coarse-graining is old."
  Rebuttal: true for consensus/Laplacian; we extend to PST/quantum walks, to MERA
  exactness, and we machine-check. **Cite it prominently and own the delta.**
- Koch-Janusz–Ringel / Lenggenhager to claim "optimal coarse-graining is solved."
  Rebuttal: their optimum is information-theoretic + approximate + learned; the
  equitable quotient is the *exact* one for the spectrum, with an iff not an argmax.

Bottom line: **the slogan is anticipated piecewise; the exact, machine-checked,
spectral-lift fusion (equitable partition ≡ exact RG/MERA step, with PST descent)
is genuinely ours — provided we cite O'Clery et al. and Mehta–Schwab up front and
sharpen the contrast (exact+verified vs. approximate+analogical).**
