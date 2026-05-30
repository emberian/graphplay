# Mechanistic-Interpretability Techniques for Testing the Equitable-Partition / Irreducibility Claims

Scope: turning the algebraic claim **A = A_eq + R** (a learned attention head decomposes into an
*equitable base* `A_eq` — the projection onto the equitable-partition / coarsest-equitable-refinement
quotient — plus a *residual* `R` measuring per-head *irreducibility*) into a **causal, falsifiable**
statement about what the head DOES.

The recurring move: the equitable partition induces a subspace decomposition of the head's value/output
space. Cells of the partition span a "cell-uniform" subspace `V_eq` (functions constant on cells, i.e.
the lifted quotient); the residual lives in its orthogonal complement `V_R`. Most techniques below reduce
to: **intervene on `V_eq` vs `V_R` and measure causal effect.** If `A_eq` is the head's mechanism, then
the model's behavior should be (a) **preserved** when we keep `V_eq` and resample/ablate `V_R`, and
(b) **destroyed** when we corrupt `V_eq`. `R` is "irreducible" exactly to the extent that ablating `V_R`
*does* cost behavior that `V_eq` cannot recover.

PDFs downloaded to `/Users/ember/dev/graphplay/refs/ml-theory/`:
- `activation_patching_bestpractices_2404.15255.pdf` — Heimersheim & Nanda, *How to use and interpret activation patching*
- `attribution_patching_2310.10348.pdf` — Syed, Rager, Conmy, *Attribution Patching Outperforms ACDC*
- `acdc_2304.14997.pdf` — Conmy et al., *Towards Automated Circuit Discovery (ACDC)*
- `ioi_path_patching_2211.00593.pdf` — Wang et al., *Interpretability in the Wild (IOI, path patching)*
- `sae_interpretable_features_2309.08600.pdf` — Cunningham et al., *Sparse Autoencoders Find Highly Interpretable Features*
- `linear_representation_hypothesis_2311.03658.pdf` — Park et al., *Linear Representation Hypothesis*
- `tuned_lens_2303.08112.pdf` — Belrose et al., *Tuned Lens*
- `probing_classifiers_promises.pdf` — Belinkov, *Probing Classifiers: Promises, Shortcomings, Advances*
- (already present, relevant) `causal_abstraction_nn_2106.02997.pdf`, `das_causal_alignment_2303.02536.pdf`,
  `toy_models_superposition_2022.pdf`, `induction_heads_2022.pdf`

---

## 1. Activation patching (causal mediation / interchange interventions)
**What it measures.** Run the model on a *clean* input, cache activations, then on a *corrupted* input
substitute (patch) a cached clean activation at a chosen site and measure the recovery of a target metric
(logit diff). Quantifies the *causal* contribution of that site to the behavior — direct causal mediation.
Best-practice caveats (Heimersheim & Nanda): noising vs denoising are not symmetric; choose the corruption
distribution carefully; metric choice (logit diff vs prob) changes conclusions; beware backup/self-repair
heads masking effects.

**How we use it to test our claim.** This is the workhorse. Define two projectors on the head's output
(or value-flow) space: `P_eq` (onto the cell-uniform subspace `V_eq` spanned by the equitable quotient)
and `P_R = I - P_eq`.
- **Denoising test of the quotient as mechanism:** corrupt the input so the head output is wrong, then
  patch in *only* `P_eq z_clean` (the equitable component of the clean activation), leaving `P_R` at the
  corrupted value. If behavior recovers, the equitable quotient carries the head's causal content →
  supports "`A_eq` is the mechanism."
- **Noising test of the residual's irreducibility:** on a clean run, replace `P_R z` with its mean /
  resampled value (keep `P_eq z`). Drop in the metric = the *irreducible* contribution of `R`. If ~0,
  `R` is causally inert and the head is "fully reducible to its quotient." If large, `R` is irreducible.
- The two numbers together estimate the variance/credit split between `A_eq` and `R`.

## 2. Path patching (edge-level causal mediation)
**What it measures.** A refinement (Wang et al., IOI) that patches the contribution flowing along a
*specific path* (sender → receiver, e.g. head→head or head→logits) rather than a node's whole output,
isolating *direct* effects from indirect ones routed through other components.

**How we use it.** Restrict the equitable/residual split to the *downstream-relevant* path. Patch only the
`V_eq`-component of head h's contribution **into** the specific receiver it feeds (next head's query, or
the unembedding) and measure whether the equitable quotient suffices *for that edge*. This tells us not
just "does the head's output factor" but "is the *useful, downstream-consumed* part of the head exactly the
equitable part." Strong evidence that the cells are the functional unit and not an artifact of unused
directions.

## 3. Causal scrubbing (rigorous hypothesis testing via resampling)
**What it measures.** Redwood's method: encode an interpretability hypothesis as a computational graph +
a claim that certain activations are exchangeable (the model is invariant to resampling them among inputs
agreeing on the features the hypothesis says matter). Resample *everything the hypothesis claims is
irrelevant*; if behavior survives, the hypothesis is consistent (it provides a conservative
behavior-preservation check, not a uniqueness proof).

**How we use it — the single most direct test of "the equitable quotient IS the mechanism."** Our
hypothesis: *the head depends on its input only through the equitable-cell assignment.* Concretely, two
inputs are "equivalent" iff they induce the same equitable partition / same `P_eq z`. Causal scrubbing
then **resamples the within-cell (residual `V_R`) variation across all inputs sharing the same cell
structure** and checks behavior is preserved. Pass ⇒ the head's function is a function of the quotient
(scrubbing-consistent mechanism). The recovered-loss fraction is a graded *irreducibility meter*: 1.0 =
perfectly reducible to `A_eq`; the shortfall is exactly the irreducible `R`. This maps our linear-algebra
claim onto Redwood's behavior-preservation criterion almost verbatim.

## 4. Sparse autoencoders / dictionary learning (feature decomposition)
**What it measures.** Train an overcomplete sparse autoencoder on a layer/head's activations to recover
monosemantic *features* (dictionary atoms) out of superposition (Cunningham et al.; Anthropic Towards
Monosemanticity). Gives an unsupervised basis of "what the activation space is made of."

**How we use it — the alignment test.** Train an SAE on the head's value/output activations, then ask
whether the learned dictionary **respects the equitable cells**:
- Compute each SAE feature's activation pattern over the equitable partition. A feature is *cell-aligned*
  if it is (approx.) constant within cells / supported on a union of cells.
- Metric: mutual information / a contingency-table statistic between {SAE-feature firing} and
  {equitable-cell id}; or the fraction of dictionary energy lying in `V_eq` vs `V_R`.
- **Prediction if our claim holds:** the bulk of high-frequency, behavior-relevant features partition
  along equitable cells (live in `V_eq`); residual `V_R` features are rare, low-importance, or
  data-point-specific. If instead many important monosemantic features live in `V_R`, the residual is
  *interpretable structure we mislabeled as noise* — a refutation worth knowing.
This is the test for "do dictionary features align with equitable cells."

## 5. Attribution patching (scalable linear approximation of patching)
**What it measures.** Syed et al. / Nanda: first-order Taylor (gradient × activation-difference)
approximation to activation patching, giving an effect estimate for *every* site in 2 forward + 1 backward
pass instead of one run per site. Outperforms ACDC at recovering circuits at scale; AtP* fixes its known
failure modes (attention-softmax saturation, etc.).

**How we use it — cheap sweep before expensive patching.** Use attribution patching to get a *gradient-
based* per-direction estimate of `∂metric/∂(P_eq z)` vs `∂metric/∂(P_R z)` for many heads/positions at
once. This cheaply ranks heads by how much of their causal effect is concentrated in `V_eq` (a fast,
approximate irreducibility meter), letting us pick the few heads worth full activation/path patching.
Diagnostic + cheap; validate top candidates with §1–§3.

## 6. Automated circuit discovery (ACDC) — and as a baseline for our partition
**What it measures.** Conmy et al.: greedily prune edges of the computation graph (recursive activation
patching against a threshold) to recover a minimal subgraph that explains a behavior — an automated circuit.

**How we use it.** Two ways. (a) **Baseline circuit, then audit:** run ACDC to find the heads relevant to
a task; for each such head, apply our `A_eq/R` decomposition and ask whether ACDC-selected heads are the
ones with large `V_eq` content (mechanism) and small `R` (the partition explains the circuit). (b)
**Resolution comparison:** treat "keep only `V_eq` of every head" as a candidate pruned model and compare
its faithfulness to ACDC's pruned circuit — does our principled, algebraic quotient match what greedy
edge-pruning finds? Agreement is corroboration; the equitable partition would be a *cheaper, closed-form*
route to the same circuit.

## 7. Linear representation hypothesis (geometry of features-as-directions)
**What it measures.** Park et al.: many concepts are encoded as linear directions; gives a causal inner
product / steering framework relating "directions" to interventions.

**How we use it — justifies the whole subspace framing.** Our `P_eq`/`P_R` split *is* a linear-subspace
hypothesis about the head. LRH supplies (a) the legitimacy of treating cell-uniform structure as a set of
directions, and (b) **steering tests**: add/subtract along a `V_eq` cell-direction and check the output
moves between cells as predicted; do the same along a `V_R` direction and check it does *not* change the
cell-level behavior (only within-cell detail). A clean dissociation (cell-directions steer behavior,
residual-directions don't) is strong mechanistic confirmation.

## 8. Probing classifiers (read-out of represented information)
**What it measures.** Train a simple classifier on frozen activations to predict a property; accuracy =
amount of *decodable* information (Belinkov: with selectivity/control-task caveats — high probe accuracy ≠
the model *uses* it).

**How we use it — necessary but not sufficient check.** Probe the head's activations to predict the
*equitable-cell id*. High accuracy ⇒ the head linearly represents the partition (the quotient is at least
*present*). Then probe `V_R` for any task-relevant label: if `V_R` is decodable for something the model
needs, `R` is not pure noise. Crucially, pair every probe with a *control task* (probe selectivity) and
follow up with §1/§3 causal tests, since probing shows *presence*, not *use*. Cheapest possible first
filter.

## 9. (Adjacent, already-present) Causal abstraction / DAS / interchange-intervention accuracy
**What it measures.** Geiger et al. (`causal_abstraction_nn_*`, `das_causal_alignment_*`): formalizes when
a neural net *implements* a higher-level causal model via alignment of interchange interventions; DAS
learns the subspace that best aligns to a hypothesized variable.

**How we use it.** This is the theoretical frame that makes "the equitable quotient is the head's causal
variable" precise: define the high-level causal model whose single variable is the equitable-cell
assignment, and measure **interchange-intervention accuracy (IIA)** between it and the head. DAS can even
*learn* the aligned subspace and we then check whether it coincides with our closed-form `V_eq`. If
DAS-found subspace ≈ `V_eq`, our algebraic partition recovers what gradient search finds — the strongest
possible "this is what the head does" statement.

---

## Ranked: techniques to adopt first (cheapest × most diagnostic)

The decomposition `A = A_eq + R` is *given to us in closed form* (no search), which makes the
intervention-based tests unusually cheap: we already know the subspace to patch.

1. **Causal scrubbing with cell-equivalence resampling (§3).** *The* direct test of the claim:
   resample within-cell (`V_R`) variation, measure recovered loss. Pass ⇒ quotient is the mechanism;
   the loss shortfall *is* the irreducibility meter. No gradient search, no probe training; just
   forward passes with a closed-form resampling rule. Highest diagnostic value per unit effort.

2. **Activation patching of `V_eq` vs `V_R` (§1), denoise-and-noise pair.** Cleanest *quantitative*
   credit split: denoise-patch `P_eq z_clean` (tests "quotient suffices") and noise-patch `P_R`
   (tests "residual is irreducible"). Two numbers per head, directly = the variance split our paper
   claims. Honors the noising/denoising-asymmetry best practices.

*(Then, in order: §5 attribution patching to sweep all heads cheaply and rank irreducibility →
§4 SAE alignment to see if features partition along cells → §2 path patching to confirm the
downstream-consumed part is the equitable part → §9 DAS/IIA for the strongest "implements the
quotient causal model" statement → §8 probing and §7 steering as light corroboration.)*

Harness ordering for `experiments/`: implement the `P_eq`/`P_R` projectors once from the equitable
partition, then (1) a resampling-ablation loop (causal scrubbing) and (2) a clean/corrupt patching loop
(activation patching) reuse the same projectors. Everything else layers on top of those two primitives.
