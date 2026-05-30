# Geometric Deep Learning / Symmetry / Equivariance — positioned against the equitable-partition lens

Scope: the GDL / symmetry / equivariance corpus, assessed adversarially against
**our lens**: a learned attention/weight matrix decomposes `A = A_eq + R`, where
`A_eq` is the nearest *equitable-partition* approximation (tokens/features fall
into `r` cells/orbits; `A_eq[i][j]` depends only on the cells of `i,j` — a
discrete symmetry / coarse-graining), `R` is a low-rank/sparse residual, and the
equitable→quotient **spectral + CTQW lift** (spectrum and continuous-time
quantum-walk dynamics on the small quotient lift back to the host) is
machine-checked in Lean.

PDFs downloaded to `refs/ml-theory/`.

---

## Seminal / closest papers

### Bronstein, Bruna, Cohen, Veličković — *Geometric Deep Learning: Grids, Groups, Graphs, Geodesics, and Gauges* (arXiv 2104.13478)
`refs/ml-theory/gdl_grids_groups_graphs_2104.13478.pdf`

- **Claims.** A unifying "Erlangen Programme" for ML: every successful deep
  architecture is explained as enforcing **invariance/equivariance to a
  symmetry group** `G` acting on the domain, plus locality/scale-separation.
  Weight sharing in CNNs = translation equivariance; GNNs = permutation
  equivariance; transformers = permutation-equivariant set/graph processing.
  The blueprint: choose `G`, build `G`-equivariant linear layers + pointwise
  nonlinearity + `G`-invariant pooling.
- **Relation to our lens: ANTICIPATES (the framing), but with a crucial gap.**
  GDL is *the* prior art for "symmetry is the organizing principle of why these
  architectures work." Our `A_eq` (cell structure = orbits under a coloring) is
  exactly a discrete-symmetry / quotient story, and transformers-as-graphs is
  explicitly in GDL. **BUT** GDL is *prescriptive*: it assumes `G` is **known a
  priori and exact**, and bakes equivariance into the architecture. Our lens is
  *descriptive/mechanistic*: the symmetry (equitable partition) is **learned and
  approximate**, *measured* post-hoc from a trained `A`, and explicitly
  **non-exact** — the `R` residual is a first-class object, not noise to be
  designed away. GDL has no spectral-lift theorem and nothing quantum.

### Cohen, Welling — *Group Equivariant Convolutional Networks* (arXiv 1602.07576)
`refs/ml-theory/gcnn_cohen_welling_1602.07576.pdf`

- **Claims.** Generalizes CNN weight sharing from translations to a discrete
  symmetry group `G` (e.g. p4, p4m). `G`-convolution = convolution over the
  group; gives higher weight-tying ⇒ lower sample complexity, provably
  equivariant feature maps.
- **Relation to our lens: ANTICIPATES the weight-tying half.** This is the
  cleanest statement that *parameter sharing = a symmetry constraint on the
  weight matrix*. Our `A_eq` is precisely a weight-tying pattern (entries
  constant on cell-pairs). Difference: G-CNN's tying is **exact, hand-chosen,
  and global**; ours is **learned, approximate (`+R`), and local to a partition
  the data induces**. No spectrum/dynamics result.

### de Haan, Cohen, Welling — *Natural Graph Networks* (arXiv 2007.08349)
`refs/ml-theory/natural_graph_networks_2007.08349.pdf`

- **Claims.** Relaxes global permutation equivariance to **local naturality**:
  message-passing kernels need only be equivariant to **local isomorphisms /
  the local automorphism structure** of each node neighborhood (a
  category-theoretic naturality condition). More expressive than global-equivariant
  GNNs while still principled.
- **Relation to our lens: CLOSEST CONCEPTUAL NEIGHBOR / EXTENDS toward us.**
  "Equivariance to the *local* orbit structure rather than a single global
  group" is morally our equitable-partition picture — the partition *is* the
  local-symmetry/orbit data, and a single global group is not required. This is
  the paper that most anticipates "the relevant symmetry is the graph's own
  orbit/cell structure." Still: exact (not `+R`), spectral lift absent, no
  quantum, not verified.

### Maron, Litany, Chechik, Fetaya — *On Learning Sets of Symmetric Elements* (arXiv 2002.08599)
`refs/ml-theory/deepsets_symmetric_elements_maron_2002.08599.pdf`

- **Claims.** Characterizes the full space of linear layers equivariant to a
  *product* symmetry (set permutation × per-element symmetry). DeepSets-style:
  the equivariant linear maps form a low-dimensional space spanned by a few
  basis operators (identity + "broadcast the mean"), i.e. a partition of the
  index set into diagonal/off-diagonal blocks.
- **Relation to our lens: ANTICIPATES the algebra of `A_eq`.** The
  permutation-equivariant linear layer `a·I + b·(11ᵀ)` is *exactly* the
  2-cell equitable structure (one cell), and the general `S_n`-equivariant
  basis is the canonical example of "matrix entries constant on orbits of index
  pairs." Our `A_eq` lives in the same span. We add: the partition is data-derived
  (not the full `S_n`), and the **eigenvalues/dynamics lift** — which this
  invariant-theory line never addresses.

### Park, Wang, et al. — *Approximate Equivariance in Reinforcement Learning* (arXiv 2411.04225)
`refs/ml-theory/approx_equivariance_rl_2411.04225.pdf`

- **Claims.** Exactly-equivariant nets are *suboptimal* when the domain has
  **symmetry-breaking factors**. Proposes architectures that are only
  *approximately* equivariant; they match exact nets under true symmetry and
  beat them when symmetry is partial.
- **Relation to our lens: STRONGEST ANTICIPATION OF THE `+R` TERM (CHALLENGES novelty of "approximate symmetry").**
  This is the adversarial hit: "exact symmetry + a residual that breaks it"
  is precisely the `A = A_eq + R` intuition, and the broader
  *approximate/relaxed-equivariance* subfield (Approximately Equivariant Neural
  Processes; "Learning (Approximately) Equivariant Networks"; equivariance-loss
  regularizers) has independently arrived at "symmetry is a learned, soft,
  partial constraint." So "learned approximate symmetry + low-rank refinement"
  as a *qualitative* thesis is **not novel**. What they do *not* have: a
  **measured equitable-partition decomposition of a trained `A`**, and no
  spectral/dynamical lift.

### Zhao, Ganev, Walters, et al. — *Symmetry in Neural Network Parameter Spaces* (survey, arXiv 2506.13018)
`refs/ml-theory/param_space_symmetry_survey_2506.13018.pdf`

- **Claims.** Surveys *parameter-space* symmetries (transformations of weights
  leaving the function unchanged, e.g. neuron permutations, scaling), their
  consequences for loss landscapes, optimization, and generalization.
- **Relation to our lens: ORTHOGONAL (different symmetry).** Their symmetry acts
  on **parameters** (gauge of the network); ours acts on the **data/feature
  index set** (orbits of tokens). Useful to cite for "symmetry is the right
  lens on deep nets" but it is *not* about coarse-graining the data graph and
  has no spectral lift. Guards us against conflating the two symmetries.

### Morris, Cuenca Grau, Horrocks — *Orbit-Equivariant Graph Neural Networks* (ICLR 2024)
(OpenReview `GkJOCga62u`; PDF at proceedings.iclr.cc — not on arXiv, link in `lit` only)

- **Claims.** Defines **orbit-equivariance**, a relaxation of permutation
  equivariance where outputs may differ within an automorphism orbit; ties the
  taxonomy to **1-WL / orbit-1-WL** refinement.
- **Relation to our lens: DIRECT NAMING OVERLAP — `orbit` + `WL`.** This is the
  most dangerous prior art *terminologically*: it uses "orbit," "equivariance,"
  and Weisfeiler–Leman refinement — the same vocabulary as our equitable-partition
  (coarsest equitable partition = WL stable coloring = orbit partition). It
  formalizes *relaxing* equivariance to the orbit level. Still architecture-side
  (designing GNN layers), exact within the relaxation, **no spectral/quantum
  lift, not machine-checked.**

---

## What the field already owns (be honest)

1. **Symmetry as the organizing principle of deep nets** — GDL/Erlangen. Fully theirs.
2. **Weight tying ≡ a symmetry constraint on the weight matrix** — G-CNN, DeepSets/Maron. Theirs.
3. **The relevant symmetry can be *local orbit structure*, not a global group** — Natural Graph Networks, Orbit-Equivariant GNNs. Theirs.
4. **Equitable partition ≡ WL stable coloring ≡ orbit partition** is standard graph theory and already imported into GNN expressivity (1-WL bound). Theirs.
5. **Symmetry is learned / approximate / soft, with a residual** — approximate-equivariance line (2411.04225 + Neural Processes + equivariance-loss). Theirs, and this is the sharpest collision with our `+R` story.

So the *qualitative* thesis — "these architectures work because they (softly/learnedly) impose a coarse-graining symmetry plus a refinement" — is **substantially present** in Geometric DL and its approximate-equivariance offshoots. We should not claim that framing as original.

## What is genuinely ours (verdict)

The novelty is **not** "symmetry + low-rank residual" as an idea. It is the **specific operator-theoretic content layered on top**, none of which appears in the GDL corpus:

- **Spectral + dynamical LIFT, as a theorem.** Equitable-partition GDL stops at
  expressivity (what functions are representable) and sample complexity. *We
  prove* that the **spectrum and the continuous-time quantum-walk dynamics on
  the small quotient lift exactly back to the host** (eigenvalue inclusion /
  intertwining `A = A_eq + R` with `A_eq` block-constant on the quotient). The
  GDL line never asks "what does the *quotient's spectrum/dynamics* tell you
  about the host." **This is the load-bearing original contribution.**
- **Quantum.** CTQW / PST / mixing / spatial-search advantage lifted through the
  equitable quotient. Zero overlap with GDL (which is entirely classical).
- **A *measured* decomposition.** GDL designs symmetry in; approximate-equivariance
  learns a soft constraint. We take a **trained `A` and extract its nearest
  equitable partition + residual `R` post-hoc** as a mechanistic diagnostic.
  This "fit the equitable partition to an existing weight matrix and read off the
  quotient" move is, as far as this sweep shows, not framed this way in GDL.
- **Machine-checked in Lean.** The lift theorems are formally verified. No GDL /
  equivariance paper offers a proof assistant–checked spectral/dynamical lift.

**Blunt bottom line.** Treat Geometric Deep Learning (and especially Natural
Graph Networks + Orbit-Equivariant GNNs + the approximate-equivariance line) as
the acknowledged parent of our *framing* — cite them up front and concede the
"learned approximate symmetry + refinement" intuition is theirs. Our defensible,
genuinely novel core is the **verified spectral/quantum-walk lift from the
equitable quotient to the host**, plus the **measured `A = A_eq + R` diagnostic**.
If a referee says "this is just GDL," the honest rebuttal is: GDL gives you the
*symmetry*; we give you a *machine-checked theorem about the quotient's spectrum
and quantum dynamics*, which GDL never attempts.
