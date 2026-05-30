# Related Work & Honest Novelty Positioning: Graphplay vs. ML Theory

*Synthesis pass, 2026-05-30. Distilled from five adversarial literature sweeps:
geometric deep learning / equivariance (`lit/geometric_dl.md`), RG / coarse-graining /
information bottleneck (`lit/rg_coarsegraining.md`), edge-of-stability / Hessian-spectrum /
training dynamics (`lit/edge_of_stability.md`), low-rank / structured attention
(`lit/lowrank_attention.md`), and mechanistic interpretability / feature learning
(`lit/mechanistic_interp.md`). Voice and discipline matched to the QW-side positioning
in `related_work_positioning.md`. Every novelty claim below is stated to survive the
specific prior art that threatens it.*

---

## TL;DR verdict

- **The qualitative thesis is not ours.** "Deep nets work because they (softly, learnedly)
  impose a coarse-graining symmetry, plus a refinement" is substantially present across
  Geometric DL, the approximate-equivariance line, the DL-as-RG tradition, the
  symmetry→landscape-spectrum line, and mechanistic interpretability. We must cite this
  prior art up front and concede the framing.
- **The defensible core is the operator-theoretic content laid on top**, none of which
  appears in the ML corpus: a *machine-checked* spectral/dynamical **lift** from the
  equitable quotient to the host; the use of the **equitable partition** (strictly more
  general than an automorphism orbit / a group) as the right object; an operator-algebraic
  **quantitative handle** (the symmetric normalized quotient `Q̃ = D^{1/2} Q D^{-1/2}`, the
  surviving-spectrum *subset*, and `‖R‖` as a progress/defect signal); the **quantum-
  realizability** layer (CTQW / PST through the quotient); and the *measured*
  `A = A_eq + R` decomposition — which is **a proposed experiment, not yet a result.**
- **Single sharpest "genuinely ours" claim:** *a machine-checked theorem that the
  equitable quotient's spectrum and continuous-time quantum-walk dynamics lift exactly to
  the host, turning a learned weight/attention matrix's nearest-equitable structure into a
  formally certified, quantum-realizable coarse-graining.* No ML-theory paper attempts a
  proof-assistant-checked spectral/dynamical lift; the symmetry/RG/interp literatures stop
  at expressivity, analogy, degeneracy, or qualitative mechanism.
- **Most dangerous prior art (cite prominently):** **O'Clery, Yuan, Stan, Barahona,
  *PRE* 88, 042805 (2013)** — external equitable partitions *are* the exact coarse-graining
  of a graph dynamical process. This is the closest non-ML statement of our central object
  and predates us on "equitable partition = exact coarse-graining of network dynamics."
  Runners-up, each owning one flank: **Şimşek et al. 2021** (symmetry → Hessian
  degeneracy), **Nanda et al. 2023** (training discovers group structure), **Scatterbrain
  (Chen, Dao et al. 2021)** (attention = structured + low-rank), **Mehta & Schwab 2014**
  (DL layer = RG step).

---

## 1. What the field already establishes — CITE, do not claim

The five sweeps converge on one uncomfortable fact: **almost every qualitative ingredient
of our story is already owned somewhere.** We enumerate each established result, name its
owner, and mark it as conceded.

### 1.1 Symmetry is the organizing principle of deep learning
- **Bronstein, Bruna, Cohen, Veličković, *Geometric Deep Learning* (arXiv:2104.13478).**
  The "Erlangen Programme" for ML: every successful architecture enforces invariance/
  equivariance to a symmetry group `G`, plus locality/scale separation. Transformers-as-
  graphs is explicitly in scope. **This is the acknowledged parent of our framing.** Their
  symmetry is *known a priori, exact, and designed in*; ours is *learned, approximate, and
  measured post-hoc*. They have no spectral-lift theorem and nothing quantum — but the
  slogan "symmetry explains these architectures" is theirs.

### 1.2 Weight tying ≡ a symmetry constraint on the weight matrix
- **Cohen & Welling, *Group Equivariant CNNs* (arXiv:1602.07576):** parameter sharing =
  a symmetry constraint; our `A_eq` (entries constant on cell-pairs) is exactly a weight-
  tying pattern. Theirs is exact, global, hand-chosen.
- **Maron, Litany, Chechik, Fetaya, *On Learning Sets of Symmetric Elements*
  (arXiv:2002.08599):** the `S_n`-equivariant linear layer `a·I + b·11ᵀ` is the canonical
  "matrix entries constant on orbits of index pairs" — the 2-cell equitable structure. Our
  `A_eq` lives in the same span. **The algebra of `A_eq` is theirs.**

### 1.3 The relevant symmetry can be *local orbit structure*, not a global group
- **de Haan, Cohen, Welling, *Natural Graph Networks* (arXiv:2007.08349):** relaxes
  global equivariance to *local naturality* — equivariance to local isomorphism structure.
  This is morally our equitable-partition picture: a single global group is not required.
- **Morris, Cuenca Grau, Horrocks, *Orbit-Equivariant GNNs* (ICLR 2024):** defines
  orbit-equivariance and ties it to 1-WL / orbit-1-WL refinement. **The most dangerous
  terminological overlap** — it uses "orbit," "equivariance," and Weisfeiler–Leman, the
  exact vocabulary of our equitable partition (coarsest equitable partition = WL stable
  coloring = orbit partition). Architecture-side, exact within the relaxation, no
  spectral/quantum lift, not machine-checked.

### 1.4 Equitable partition = exact coarse-graining of a graph dynamical process
- **★ O'Clery, Yuan, Stan, Barahona, *PRE* 88, 042805 (2013).** External equitable
  partitions of consensus/Laplacian dynamics: the quotient *exactly* reproduces the coarse
  dynamics. **This is the single closest prior art to our central object and the most
  dangerous citation** — it predates us on "equitable partition = exact coarse-graining of
  network dynamics." We must cite it prominently and own the delta: their target is
  consensus/Laplacian observability; we extend to PST / continuous-time quantum walks,
  to MERA exactness, and we *machine-check*.
- **Barrett et al. (arXiv:1510.04366), *Automorphisms, Equitable Partitions, and Spectral
  Graph Theory*; Godsil–Royle.** The classical statement that an equitable decomposition
  makes the host spectrum the disjoint union of quotient-block spectra. **The subset-
  containment theorem is old; we only re-prove it in Lean.** Do not claim it.

### 1.5 A deep-learning layer ≈ a renormalization-group coarse-graining step
- **★ Mehta & Schwab 2014 (arXiv:1410.3831):** the foundational "DL layer = RG step,"
  stacked RBMs ≈ block-spin RG. The correspondence is at the level of partition functions /
  distributions, not a structural graph quotient with a spectral lift, and is exact only
  for special couplings. **They own "DL ≈ RG (statistical-mechanics flavor)" as an analogy.**
- **Li & Wang 2018 (NeuralRG, PRL 121.260601):** a learnable *invertible* (normalizing-flow)
  RG. Dual to us: invertible-lossless vs. our quotient-lossless-for-the-spectrum.
- **Koch-Janusz & Ringel 2018 (Nature Physics);** **Lenggenhager et al. 2020 (PRX 10.011037).**
  Learn an *optimal* real-space RG by maximizing relevant mutual information, with a
  *no-range-increase* locality theorem. **The most direct technical challenger** to "the
  equitable quotient is the right coarse-graining": they independently ask "which coarse-
  graining is optimal?" Their answer is approximate + information-theoretic + learned + an
  argmax; ours is exact + spectral/combinatorial + verified + an *iff*.
- **Tishby & Zaslavsky 2015; Shwartz-Ziv & Tishby 2017 (Information Bottleneck).** The
  information-theoretic sibling: layers as successively coarser sufficient statistics. Soft/
  lossy/optimized, not hard/exact/lossless-for-the-spectrum. **Cite Saxe et al. 2018**
  (debunking universality of the compression phase) as the reason we deliberately do *not*
  rest on information-plane dynamics — our decomposition is a theorem about a fixed matrix.

### 1.6 Symmetry → Hessian degeneracy and conserved gradient-flow quantities
- **★ Şimşek et al. 2021 (ICML; arXiv:2105.12221):** permutation symmetries of hidden
  units generate symmetry-induced critical points with **highly degenerate Hessians** (many
  zero eigenvalues → flat valleys). A neuron-collision permutation symmetry *is* an
  equitable partition of the unit-interaction structure; the zero Hessian eigenvalues are
  its spectral shadow. **The single cleanest "symmetry → Hessian spectrum" hit — confront
  it.** They give *degeneracy*; we give *which exact eigenvalues survive*.
- **Kunin et al. 2020 (Neural Mechanics, arXiv:2012.04728); Zhao et al. 2022 (arXiv:2210.17216).**
  Symmetry → conserved quantity under gradient flow → constrained dynamics, Noether-style.
  **The conservation-law framing is theirs.** Our discrete-step, formally-proven
  `training_step_linear_under_equitable` is a cousin, not a first.
- **Zhao et al., *Parameter-Space Symmetry* survey (arXiv:2506.13018).** Symmetries of the
  *weights* (gauge of the network). **Orthogonal** to ours, which acts on the *data/feature
  index set* (orbits of tokens). Cite to disambiguate which symmetry we mean.

### 1.7 The full Hessian/NTK spectrum governs training dynamics (edge of stability)
- **Cohen et al. 2021 (arXiv:2103.00065):** GD drives the top Hessian eigenvalue to `2/η`
  and hovers there. **The founding EoS result** — about the *largest* eigenvalue only.
- **Tuci et al. 2026 (arXiv:2604.19740):** generalization at EoS depends on the *complete*
  Hessian spectrum and its partial determinants — closest to our spirit (whole spectrum,
  not a scalar), but dynamical/measure-theoretic, not combinatorial.
- **Ghorbani et al. 2019;** **NTK-spectrum line** (Murray et al. 2022). Real Hessian/NTK
  spectra have structure (bulk + outliers). **Established that the spectrum governs training;
  that race is run.**

### 1.8 Training discovers structure; mechanisms are equivalence-class rules
- **★ Nanda et al. 2023, *Progress Measures for Grokking* (arXiv:2301.05217):** a 1-layer
  transformer that groks modular addition is fully reverse-engineered as learning the
  **representation theory of Z/p** (Fourier circuits). Group reps are exactly the source of
  orbits / equitable partitions. **So "the model finds an equitable partition" is already
  proven for the special case of Cayley graphs of Z/p — under a different name. Frame
  against this explicitly or a reviewer will.**
- **Olsson et al. 2022 (Induction Heads, arXiv:2209.11895):** a head implements "tokens
  matching the current token are equivalent for prediction" — an equivalence-class mechanism
  in all but name, discovered at a *training phase transition*. **The mechanism half is
  theirs**, without the quotient algebra.
- **Power et al. 2022 (Grokking); Liu et al. 2022 (Omnigrok); Michaud et al. 2023
  (Quantization Model); Zheng et al. 2024 (Attention-Heads Survey).** Establish,
  respectively: the emergence phenomenon; a *competing* loss-landscape explanation of it
  (cite to show we are not naive about non-symmetry drivers); discrete "quanta" of learned
  structure; and a head *taxonomy* of grouping rules. **"Heads implement grouping rules" and
  "structure emerges at a phase transition" are both pre-existing.**
- **Synchronization-cluster / network-dynamics line (e.g. PMC11165003).** Already ties
  dynamical clusters to symmetry orbits *and* equitable partitions of the graph. **The
  strongest external validation that the object is right — and the strongest warning that
  the mathematics is not ours to claim as new.**

### 1.9 Attention is low-rank-ish; "structured base + low-rank correction" exists
- **Linformer (Wang et al., arXiv:2006.04768); Performer (Choromanski et al.,
  arXiv:2009.14794):** self-attention is approximately low-rank; a rank-`r` factor applies
  in O(n·r). **Justifies a low-rank summand** — but at the whole-matrix level, *competing*
  with "you need a structured base at all."
- **★ Scatterbrain (Chen, Dao et al., arXiv:2110.15343):** attention ≈ **sparse + low-rank**
  (Robust-PCA style). **The closest "structured component + low-rank correction" prior art —
  the template is theirs.** Their structured summand is *sparse (LSH-bucketed)*; ours is an
  *equitable/quotient base* cheap to apply by symmetry, not by sparsity. Cite as the
  benchmark and the source of the L+R math.
- **LoRA (Hu et al., arXiv:2106.09685); intrinsic-dimension (Aghajanyan et al.,
  arXiv:2012.13255):** weight = frozen base + low-rank update. **Same template, weight space
  not attention-map space.**
- **Dong et al. 2021 (rank collapse, arXiv:2103.03404):** pure attention collapses to
  rank-1; skips/MLPs carry the surviving rank. **The most adversarial paper for a naive
  "R is tiny" claim** — it warns the *signal* may live in the deviation, so our
  decomposition only pays off if `A_eq` is a rich equitable quotient (not rank-1) and `R`
  is the genuine small leftover.

### Honest concession (state this plainly to referees)
The qualitative thesis — *"these architectures work because they impose a (learned,
approximate) coarse-graining symmetry plus a refinement, and training discovers it"* — is
**substantially present** across Geometric DL, the approximate-equivariance offshoots, the
DL-as-RG tradition, the symmetry-to-landscape-spectrum line, and mechanistic
interpretability. **We claim none of it as original framing.**

---

## 2. What is genuinely ours — the sharp statement

The novelty is **not** any of: symmetry-organizes-DL, weight-tying-is-symmetry,
local-orbit-equivariance, equitable-partition-as-coarse-graining, DL-layer-as-RG,
symmetry→Hessian-degeneracy, symmetry→conserved-flow, attention≈structured+low-rank, or
training-discovers-group-structure. Each is conceded in §1. The defensible core is the
**operator-theoretic content layered on top**, distilled to five claims, each stated to
survive the specific prior art that threatens it.

### 2.1 A *verified* spectral / dynamical LIFT (flagship)
*Claim.* The spectrum and the continuous-time quantum-walk dynamics on the small equitable
quotient lift **exactly** to the host — and this is a **machine-checked Lean theorem**, not
an analogy or an expressivity bound.
*Survives:* Geometric DL stops at expressivity and sample complexity and never asks what
the *quotient's spectrum/dynamics* tell you about the host. The DL-as-RG line gives
analogies (Mehta–Schwab) or learned/invertible maps (Li–Wang, Koch-Janusz–Ringel) with no
spectral-descent theorem. The classical subset-containment fact (Barrett, Godsil–Royle,
O'Clery) is old — **our delta is that it is machine-checked and carries CTQW/PST dynamics,
not just consensus/Laplacian observability.** No ML-theory or network-science paper offers
a proof-assistant-checked spectral/dynamical lift. **This is the load-bearing original
contribution.**

### 2.2 Equitable ⊋ group: the right object even with no symmetry
*Claim.* The correct mechanistic object is the **equitable partition**, which is strictly
more general than an automorphism orbit / a group: orbit partition ⊆ coarsest equitable
partition, *strict in general*. Graphs and attention matrices have equitable partitions
**with no symmetry group at all.**
*Survives:* Nanda et al. proved "training finds the structure" for Cayley graphs of `Z/p`
via *group representations*. Şimşek's symmetry is a *permutation group* of neurons.
**Our wedge:** equitable partition names and captures the mechanism even off the group case,
where Fourier/rep-theory has nothing to say. This is a testable sharpening — "the equitable
partition, not the automorphism orbit, is the mechanistic object" — defensible precisely
because the inclusion is strict.

### 2.3 An operator-algebraic *quantitative handle*
*Claim.* The symmetric normalized quotient `Q̃ = D^{1/2} Q D^{-1/2}`, the surviving-spectrum
**subset** statement, and the residual norm `‖R‖` together give a *compositional, measurable*
progress/defect signal and an exact **O(n²)→O(n·r)** structural-collapse statement on the
quotient.
*Survives:* Şimşek gives *degeneracy* (which eigenvalues are zero / flat); we give *which
exact eigenvalues survive* in the symmetric subspace — a constructive upgrade. EoS work
(Cohen, Tuci) owns the full-spectrum *dynamics*; our subset is a *named, computable-a-priori*
sub-block of that spectrum (and transfers to the NTK: block-constant ⇒ subset spectrum,
arguably our cleanest unclaimed static target). Mech-interp's progress measures are
task-specific (Fourier on `Z/p`); `‖R‖` is task-agnostic and operator-level. The O(n)→O(r)
compute collapse tied to the spectral invariant is a consequence the symmetry-dynamics
papers do not pursue.

### 2.4 The quantum-realizability layer
*Claim.* The equitable quotient carries CTQW / PST / mixing / spatial-search structure that
lifts to the host — a quantum-realizable reading of the coarse-graining.
*Survives:* the entire GDL / RG / EoS / interp corpus is **classical**; there is zero
overlap on the quantum side. (For the QW-specific prior art — Ide–Narimatsu, Janmark–
Meyer–Wong, GQWformer/CTQWformer — and the honest delta there, see
`related_work_positioning.md`; that math spine is attributed, the *verified* and *compiled*
stack is ours.)

### 2.5 The *measured* `A = A_eq + R` decomposition — **PENDING EXPERIMENT, not a result**
*Claim (to be tested).* Take a *trained* attention/weight matrix, extract its nearest
equitable partition `A_eq` and residual `R` post-hoc, and read off the quotient as a
mechanistic diagnostic — with the specific empirical prediction that **`rank(R)` is small
relative to `rank(A)`** and that **`‖R(t)‖` collapses at the generalization phase
transition**, with the emergent cells of `A_eq` coinciding with a head's known functional
role (match / position / syntax).
*Honesty (load-bearing):* **this is a proposed measurement, not a demonstrated finding.**
Nobody has measured `rank(A − A_eq)` for an *equitable* `A_eq` (Scatterbrain's structured
summand is sparse, not equitable; Linformer measures whole-matrix rank). The hypothesis is
**falsifiable and may fail:** the rank-collapse result (Dong et al.) warns that if `A_eq` is
too coarse, `R` is where all the signal lives and is *not* small; and on `Z/p` the
decomposition may merely re-derive the Fourier circuit (a reformulation, not a discovery).
**We must not state §2.5 as established.** Until the experiment runs, the surer ground is
§2.1–§2.4 (the verified lift, the strict generality, the operator handle, the quantum layer).

### The single sharpest defensible sentence
> Prior work gives you the *symmetry* (Geometric DL), the *analogy to RG* (Mehta–Schwab),
> the *degeneracy* it induces (Şimşek), the *conserved quantity* it implies (Kunin, Zhao),
> the *low-rank correction* template (Scatterbrain, LoRA), and the *discovery of group
> structure in training* (Nanda); **we give a machine-checked theorem that the equitable
> quotient's spectrum and continuous-time quantum-walk dynamics lift exactly to the host** —
> a formally certified, quantum-realizable coarse-graining of a learned operator, which none
> of them attempts.

---

## 3. Open questions the sweep surfaced

These are the genuinely unanswered seams. Each is an honest "we do not yet know," and each
is the highest-value next step on its respective flank. Stating them as open is part of the
honesty contract — they are also the experiments that would convert §2.5 and parts of §2.3
from "plausible" to "demonstrated."

1. **Equitable-quotient edge of stability.** Cohen/Tuci own the *dynamics* of the full
   spectrum at EoS; we have only a *static* spectral-subset statement. **Does the equitable/
   quotient subspace inherit its own sharpness, and does GD restricted to it sit at its own
   edge of stability `2/η`?** Nobody asks this. The leap from a static spectral subset to a
   *dynamical* one is our most under-defended flank and the single highest-value open
   question of the sweep.

2. **Is `R` low-rank after an *equitable* base?** The empirical heart of §2.5. Compute
   `rank(A − A_eq)` on real heads for an equitable `A_eq` and check it is small relative to
   `rank(A)`. Closest prior art (Scatterbrain) uses a sparse base, not equitable, so this
   measurement is unclaimed. **Falsifiable;** the rank-collapse caveat (Dong et al.) means it
   may fail unless `A_eq` is rich enough to leave a genuinely small `R`.

3. **Does the partition crystallize at grokking?** Run the `A(t) = A_eq(t) + R(t)`
   decomposition through training on the modular-addition transformer *and* on a real
   induction head. **Does `‖R(t)‖` collapse at the generalization phase transition, and do
   the emergent cells of `A_eq` coincide with the head's known functional role / the Fourier
   modes?** If yes, the operator framing pays for itself; if it merely re-derives the Fourier
   circuit on `Z/p`, it is a reformulation, and the generality (§2.2) plus the verified lift
   (§2.1) remain the surer ground. Be prepared for the latter on the group task.

Secondary seams worth one line each: the **NTK analogue** (block-constant feature graph ⇒
quotient-NTK subset spectrum — the cleanest unclaimed static target); reconciling the
**equitable-vs-information-optimal** coarse-graining (our exact `iff` vs. Koch-Janusz–Ringel's
mutual-information argmax — they can disagree, and characterizing when is open); and whether
the **MERA `mera_exact_iff_equitable`** combinatorial exactness criterion extends to
approximate MERA (currently the disentangler cell-uniform commutation is the one honest
`sorry`).

---

## Citation discipline (for the §-writer and for Tino)

- **Concede in the first paragraph of the related-work section**, by name: Geometric DL
  (Bronstein et al.), O'Clery et al. (PRE 2013), Mehta–Schwab, Şimşek et al., Kunin/Zhao,
  Cohen/Tuci, Scatterbrain/LoRA, Nanda et al. Do not let a reviewer surface any of these
  before we do.
- **Never claim** as ours: symmetry-organizes-DL, weight-tying-is-symmetry, equitable-
  partition-as-coarse-graining (the *object* — O'Clery owns it for dynamics; Godsil–Royle/
  Barrett own the subset-containment *theorem*), DL-as-RG, symmetry→degeneracy/conservation,
  attention≈structured+low-rank, or training-finds-group-structure.
- **Do claim**, and only this: the *machine-checked* spectral/dynamical/quantum **lift**
  (§2.1); equitable ⊋ group as the mechanistic object (§2.2); the `Q̃` / subset / `‖R‖`
  operator handle and the verified O(n²)→O(n·r) collapse (§2.3); the quantum-realizability
  layer (§2.4, with QW-side attribution per `related_work_positioning.md`).
- **Mark §2.5 as a proposed experiment everywhere it appears.** It is the claim most likely
  to be over-read as a result; it is the claim most likely to fail. Maximum honesty here is
  what keeps us credible on §2.1–§2.4.

*Written read-only against the repo; no `.lean` edited; no git operations performed.*
