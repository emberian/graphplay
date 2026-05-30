# Edge-of-Stability / Hessian-Spectrum / Training-Dynamics Literature

**Scout date:** 2026-05-30 · **Lens:** Graphplay's spectral spine — eigenvalues/eigenprojectors
of a Hermitian weight matrix, plus the proven `training_step_linear_under_equitable`
(`Graphplay/Integrations/AttentionComplexity.lean:348`), where an equitable partition forces the
*quotient* eigenvalues to be a *subset* of the host spectrum. Working hypothesis:
**symmetry/equitable structure shapes the loss-landscape spectrum (Hessian/NTK) and hence
training dynamics.**

This file maps the prior art onto that hypothesis and renders a blunt verdict on what,
if anything, is ours. PDFs live in `/Users/ember/dev/graphplay/refs/ml-theory/`.

---

## The "symmetry → Hessian spectrum → training dynamics" question, up front

Our hypothesis decomposes into three links. Each link is *already established* somewhere in the
literature, **but no one chains all three through an equitable-partition / quotient-spectrum
lens, and no one has a formally verified gradient-step invariant.** The honest summary:

| Link | Established by | Status for us |
|---|---|---|
| symmetry → Hessian *degeneracy* (zero eigenvalues, flat directions) | Şimşek 2021; Kunin 2020; Zhao 2022 | **Prior art. Not ours.** |
| symmetry → *conserved quantity* under gradient flow | Kunin 2020 (Neural Mechanics); Zhao 2022 | **Prior art. Not ours.** Our `training_step_*` is a *discrete, formally-proven* cousin. |
| full Hessian spectrum → EoS / generalization | Cohen 2021; Tuci 2026 | **Prior art. Not ours.** |
| equitable-partition quotient → exact spectral *subset* containment, *formally verified*, applied to attention/training cost | — | **This is the open seam. Closest thing to ours.** |

---

## Seminal / closest-prior-art papers (downloaded)

### 1. Cohen, Kazdan, Hashemi, Talwalkar, Kolter (2021) — *Gradient Descent on Neural Networks Typically Occurs at the Edge of Stability*
`refs/ml-theory/cohen2021_edge_of_stability.pdf` · arXiv:2103.00065 · ICLR 2021
- **Claim.** Full-batch GD drives the top Hessian eigenvalue (the "sharpness") up to and then
  hovering at `2/η`; loss is locally non-monotone but decreases over long horizons. This is the
  founding EoS paper — purely about the *top* of the Hessian spectrum vs. the step size.
- **Relation to us.** This is the canonical "spectrum governs training dynamics" result, and it
  is *the* anchor for the whole sub-field. It is about the **largest** eigenvalue only; it says
  nothing about *structure* or *symmetry* in the rest of the spectrum. Our equitable lens is
  orthogonal to it: equitable structure constrains *which* eigenvalues exist (subset containment),
  not how the optimizer races the leading one against `2/η`.
- **Verdict.** Foundational background, NOT competition. The bridge we could own is: *does the
  equitable/quotient subspace inherit a sharpness, and does GD restricted to it sit at its own
  edge of stability `2/η`?* Nobody asks this. Genuinely open.

### 2. Tuci, Korkmaz, Şimşekli, Birdal (2026) — *Generalization at the Edge of Stability*
`refs/ml-theory/tuci2026_generalization_at_eos.pdf` · arXiv:2604.19740
- **Claim.** Models stochastic optimization at EoS as a *random dynamical system* converging to
  *fractal attractors*; proves that generalization in the chaotic regime "depends on the
  **complete Hessian spectrum** and the structure of its **partial determinants** — a complexity
  that cannot be captured by the trace or spectral norm considered in prior work." Introduces a
  "Sharpness Dimension."
- **Relation to us.** This is the strongest match to our *spirit*: it explicitly says the **whole
  spectrum** (not a scalar summary) drives the behavior — exactly the move our equitable spine
  makes (the quotient is a *structured subset* of the whole spectrum, not a scalar). But their
  structure is dynamical/measure-theoretic (fractal attractor dimension, partial determinants);
  ours is *algebraic/combinatorial* (which eigenvalues are forced by an equitable partition).
- **Verdict.** Closest in ambition, most useful to cite. NOT overlapping in method. If we want to
  position aggressively, the claim "equitable symmetry pins down a known sub-block of the Hessian
  spectrum, so its contribution to the partial-determinant complexity is *computable a priori*"
  would be a real, novel synthesis of their framework with ours.

### 3. Zhao, Ganev, Walters, Yu, Dehmamy (2022) — *Symmetries, Flat Minima, and the Conserved Quantities of Gradient Flow*
`refs/ml-theory/zhao2022_symmetries_flat_minima_conserved.pdf` · arXiv:2210.17216 · ICLR 2023
- **Claim.** Builds a framework linking **parameter-space symmetries** (incl. nonlinear ones) to
  **conserved quantities under gradient flow**; conserved quantities associated with *linear*
  symmetries provide coordinates along flat low-loss valleys, and explain that standard init only
  explores a small slice of the global-minimum manifold.
- **Relation to us.** This is the most direct prior art for the *"conservation law under gradient
  flow"* half of our story, and the most threatening to a naive novelty claim. Our
  `training_step_linear_under_equitable` is exactly a statement that *the equitable structure is
  preserved by the (discrete) gradient update* — i.e. an invariant/"conserved structure" under the
  step. Zhao et al. own the *continuous-time, Lie-symmetry, conserved-quantity* version.
- **Verdict.** **This is the paper to beat / cite defensively.** Differentiators that are honestly
  ours: (a) ours is a **discrete-step** invariant, proven *exactly* (`Lean`, sorry-free), not a
  continuous-flow Noether argument; (b) the symmetry we use is a **graph/equitable-partition**
  symmetry yielding a **quotient with subset spectrum** — a *combinatorial* object their framework
  doesn't single out; (c) we tie the conserved structure to an **O(n)→O(r) compute collapse**,
  which is an operational consequence they don't pursue. Do NOT claim "first to connect symmetry
  to conserved quantities in training" — that is theirs.

### 4. Kunin, Sagastuy-Brena, Ganguli, Yamins, Tanaka (2020) — *Neural Mechanics: Symmetry and Broken Conservation Laws in Deep Learning Dynamics*
`refs/ml-theory/kunin2020_neural_mechanics.pdf` · arXiv:2012.04728 · ICLR 2021
- **Claim.** Each architectural symmetry (translation/scale/rescale) yields a **conserved
  quantity** under gradient flow (Noether-style), constraining dynamics to a hyperplane/sphere/
  hyperbola; finite LR, weight decay, momentum, and SGD noise *break* these laws in computable
  ways, giving exact ODEs for the dynamics.
- **Relation to us.** The origin of the "symmetry ⇒ conserved quantity ⇒ constrained training
  dynamics" narrative in DL. Same defensive concern as Zhao. They do NOT touch the Hessian
  *spectrum* directly, and their symmetries are weight-space rescalings, not graph-equitable
  partitions / quotient eigenvalue containment.
- **Verdict.** Prior art for the conservation-law framing. Ours is distinguished by being
  (i) discrete-step + formally verified and (ii) tied to an explicit *spectral subset* statement.
  Cite, don't fight.

### 5. Şimşek, Ged, Jacot, Spadaro, Hongler, Gerstner, Brea (2021) — *Geometry of the Loss Landscape in Overparameterized Neural Networks: Symmetries and Invariances*
`refs/ml-theory/simsek2021_geometry_loss_landscape.pdf` · arXiv:2105.12221 · ICML 2021
- **Claim.** **Permutation symmetries** of hidden units generate "symmetry-induced" critical
  points / saddle manifolds; characterizes the width-scaling of their number and the connectivity
  of global minima. Symmetric (collided-neuron) points carry **highly degenerate Hessians** (many
  zero eigenvalues → flat valleys).
- **Relation to us.** This is the cleanest existing instance of **symmetry → Hessian spectral
  degeneracy** — the first link of our hypothesis, done rigorously. Crucially: a permutation
  symmetry that collapses neurons into the *same* function is *exactly an equitable partition of
  the unit-interaction structure*, and the resulting zero Hessian eigenvalues are the spectral
  shadow of that partition. So our equitable framing is, in a real sense, *the graph-theoretic
  name for the mechanism Şimşek already analyzes.*
- **Verdict.** **The single most important paper to confront.** It is the strongest "someone
  already did symmetry → Hessian spectrum" hit. Honest position: they do permutation symmetry of
  hidden units → degenerate critical points; we do *equitable partition → quotient with subset
  spectrum*, generalize to weighted/Hermitian + attention graphs, and provide a *formally verified
  step-invariant + compute bound*. The novelty is the **quotient-spectrum subset** statement
  (theirs gives degeneracy/flatness, ours gives *which exact eigenvalues survive*) and the
  formalization. Do not overclaim originality on "symmetry causes Hessian degeneracy."

### 6. Ghorbani, Krishnan, Xiao (2019) — *An Investigation into Neural Net Optimization via Hessian Eigenvalue Density*
`refs/ml-theory/ghorbani2019_hessian_spectrum.pdf` · arXiv:1901.10159 · ICML 2019
- **Claim.** Stochastic-Lanczos tool to estimate the *full* Hessian eigenvalue density at scale;
  finds a bulk near zero plus a few large outliers, and shows BN/optimization choices reshape the
  outlier spectrum (and that outliers slow training).
- **Relation to us.** The empirical backbone establishing that real-network Hessian spectra have
  **structure** (bulk + outliers). Our equitable/quotient eigenvalues are candidate *named
  generators* of part of that structure — the outliers/degeneracies attributable to symmetry.
- **Verdict.** Background/empirical support, not competition. Useful to motivate *why* a
  structural account of the spectrum matters at all.

---

## Adjacent hits worth knowing (not downloaded — readily available)

- **NTK spectrum line** (Murray et al. 2022, *Characterizing the NTK spectrum via a power series*,
  arXiv:2211.07844; "Understanding the Evolution of the NTK at the Edge of Stability," NeurIPS
  2025): the NTK is the *other* spectral object governing training (linearized-regime dynamics).
  An equitable partition of the data/feature graph would make the NTK **block-constant** and hence
  its spectrum a subset of a quotient NTK — the *exact NTK analogue of our weight-matrix story*.
  **This is arguably our cleanest unclaimed target.** No downloaded PDF; flag for a follow-up pull.
- **Spectral bias / Frequency Principle** (Rahaman et al. 2019, arXiv:1806.08734; Cao et al. 2021):
  low-frequency-first learning, explained via the NTK eigenbasis. Symmetry-respecting (equitable)
  data would reorganize that eigenbasis into symmetry-typed frequencies. Tangential but thematically
  aligned with "spectrum shapes what/when the net learns."
- **SAM** (Foret et al. 2020, arXiv:2010.01412) and *On the Maximum Hessian Eigenvalue and
  Generalization* (Kaur et al.): the "flatness ↔ generalization" engine that motivates caring about
  Hessian eigenvalues operationally. Background, not overlapping.
- **Loss-landscape degeneracy / stagewise development** (Hoogland, Wang, Farrugia-Roberts et al.
  2024, arXiv:2402.02364, "devinterp" / singular-learning-theory line): explicitly frames training
  as governed by *degeneracy* of local loss geometry and its phase structure. Symmetry-induced
  degeneracy is a special case; SLT's "local learning coefficient" is a degeneracy invariant. Worth
  watching — it is the community closest to "symmetry/degeneracy → training-dynamics phases."
- **Graph-theory grounding** (Barrett et al. 2017, arXiv:1510.04366, *Automorphisms, Equitable
  Partitions, and Spectral Graph Theory*): the clean statement that equitable decomposition makes
  the host spectrum the disjoint union of quotient-block spectra. This is the *math* our spine
  imports; useful to cite for the subset-containment claim itself.

---

## Blunt novelty verdict

**What is clearly NOT ours (do not claim):**
- symmetry → conserved quantity under gradient flow → constrained dynamics (Kunin 2020, Zhao 2022).
- permutation symmetry → degenerate Hessian / symmetry-induced saddles & flat valleys (Şimşek 2021).
- training dynamics are governed by the *full* Hessian spectrum, incl. at EoS (Cohen 2021, Tuci 2026).
- equitable partition ⇒ quotient spectrum is a subset of the host spectrum (classical spectral graph
  theory; Barrett 2017, Godsil–Royle). The *theorem* is old; we only re-prove it in Lean.

**What is plausibly ours (the open seam):**
1. **Formal verification of a *discrete* gradient-step invariant.** `training_step_linear_under_equitable`
   is a sorry-free proof that the equitable structure (hence the quotient-spectrum containment) is
   *preserved by an actual SGD step* under weight-tying/equivariance — a discrete, machine-checked
   analogue of the continuous Noether/conservation results. No one in this corpus has a formal proof;
   they have continuous-flow analyses.
2. **The quotient-spectrum *subset* statement as the named mechanism behind symmetry-induced
   Hessian/NTK structure.** Şimşek et al. give *degeneracy* (zero eigenvalues, flatness); the
   equitable lens upgrades that to *which exact eigenvalues survive* in the symmetric subspace. That
   sharper, constructive statement — and its transfer to the **NTK** (block-constant ⇒ subset
   spectrum) — appears unclaimed.
3. **The O(n)→O(r) compute collapse tied to the spectral invariant.** Operationalizing the conserved
   structure as an *exact* cost reduction (forward and backward) is a consequence the symmetry-dynamics
   papers do not pursue.

**Adversarial bottom line.** Do NOT pitch "we discovered symmetry shapes the loss-landscape spectrum"
— that race is run (Şimşek, Kunin, Zhao). The defensible, honest contribution is *constructive +
formally verified*: **"equitable-partition symmetry pins a computable subset of the Hessian/NTK
spectrum, that subset is provably preserved by the discrete gradient step, and that invariant yields
an exact O(n)→O(r) collapse."** The biggest under-defended flank is the leap from a *static* spectral
subset claim to a *dynamical* one — Cohen/Tuci own the dynamics, and we have not shown the quotient
subspace has its *own* edge-of-stability. Closing that gap (equitable-quotient sharpness vs. `2/η`) is
the single highest-value open question this sweep surfaced.

```
( ⌐■_■ )  the spectrum was always the spine — the equitable partition just tells you
          which notes of it the symmetry lets ring.
```
