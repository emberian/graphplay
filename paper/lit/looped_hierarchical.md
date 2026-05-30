# Looped / Recurrent-Depth Transformers & Hierarchical Reasoning Models

*Literature scout + positioning against the Graphplay framework, where iterating
an attention operator IS a discrete-time quantum walk.*

Scope: looped / weight-tied / universal / recurrent-depth transformers, deep
equilibrium models, and hierarchical reasoning models (HRM). The thesis under
test: **a looped transformer applies the same operator `k` times — `A^k` (or
`exp(-ikτ A)`) — which is exactly an operator power / discrete-time quantum
walk, and the Graphplay spectral / equitable-quotient / MERA machinery should
characterize what that loop computes in the limit.**

PDFs downloaded to `/Users/ember/dev/graphplay/refs/ml-theory/`. All verified as
real PDFs > 50 KB.

---

## 1. Architectures surveyed (with refs on disk)

| Architecture | Paper | arXiv | local PDF | One-line |
|---|---|---|---|---|
| **Universal Transformer (UT)** | Dehghani et al. 2018 | 1807.03819 | `UniversalTransformers_1807.03819.pdf` | Original weight-tied "parallel-in-time recurrent" transformer; same block applied `t` times with Adaptive Computation Time (ACT) halting. The progenitor of the whole line. |
| **Deep Equilibrium Models (DEQ)** | Bai, Kolter, Koltun 2019 | 1909.01377 | `DEQ_1909.01377.pdf` | Replace a stack of layers with the *fixed point* `z* = f(z*, x)` of one layer; solve by root-finding, backprop via implicit function theorem (`O(1)` memory). The limit of an infinitely looped block. |
| **Looped Transformers as Programmable Computers** | Giannou, Rajput, ... Papailiopoulos 2023 | 2301.13196 | `Giannou_LoopedProgrammable_2301.13196.pdf` | A *constant-depth* transformer + an external loop emulates a stored-program computer (SUBLEQ-style ISA); iterating the block = stepping the program counter. Universal computation by looping. |
| **Looped TF are Better at Learning Learning Algorithms** | Yang, Lee, Nowak, Papailiopoulos 2023/24 | 2311.12424 | `LoopedLearnLearning_2311.12424.pdf` | Empirically: a looped block trained on in-context regression matches a deep transformer with far fewer params, and the loop reproduces *iterative* solvers (gradient descent / Newton steps). |
| **Looped Transformers for Length Generalization** | Fan et al. 2024 | 2409.15647 | `LoopedLengthGen_2409.15647.pdf` | Adaptive-step looped TF generalizes to longer inputs on `n`-RASP-solvable tasks; #loops scales with problem size. |
| **Recurrent Depth / "Huginn-3.5B"** | Geiping et al. 2025 | 2502.05171 | `RecurrentDepth_Huginn_2502.05171.pdf` | prelude `P` → looped core block `R` (run a *random* number of iterations) → coda `C`. Scales test-time compute by latent iteration, not by emitting tokens. Production-scale (3.5B / 800B tokens). |
| **Hierarchical Reasoning Model (HRM)** | Wang et al. (Sapient) 2025 | 2506.21734 | `HRM_2506.21734.pdf` | Two coupled recurrent modules at two timescales: fast L-module loops `T` steps to a *local equilibrium*; slow H-module updates once per `T`-cycle and resets L's target. `N` H-cycles × `T` L-steps. 27M params, beats CoT LLMs on ARC/Sudoku/maze. |
| **Tiny Recursive Model (TRM)** | Jolicoeur-Martineau 2025 | 2510.04871 | `TinyRecursive_TRM_2510.04871.pdf` | Simplification of HRM: a single tiny net recursing at two frequencies beats HRM on the same puzzles. Confirms the *recursion*, not the bio story, is what matters. |
| **Stability & Generalization in Looped TF** | (2026) | 2604.15259 | `StabilityLooped_2604.15259.pdf` | A **fixed-point framework** for looped architectures along three axes — *reachability* (does iteration converge to a fixed point vs diverge/cycle?), input-dependence, output-stability. The most theory-aligned with us. |

Two structural families:

- **Single-scale loops** (UT, DEQ, Giannou, Yang, Fan, Huginn): one block `f`,
  iterate `z_{k+1} = f(z_k, x)`. DEQ = take `k → ∞` and land on the fixed point.
- **Multi-scale / nested loops** (HRM, TRM): inner loop runs to a (local)
  equilibrium, outer loop advances and *re-seeds* the inner target. Two coupled
  fixed-point iterations at different rates.

---

## 2. The precise relationship to our iterated-walk / spectral / MERA analysis

Our denotational semantics (`Graphplay/Integrations/TransformerDSL.lean`,
`MachineLearning.lean`) already says: **a transformer block denotes to a
WeightedGraph token-graph Hamiltonian** `H = denote(p)` (Hermitian, loopless,
the symmetrized attention `A.symmetrizedAttention`), and the whole
equitable-partition / quantum-walk apparatus acts on `H`. A *loop* iterates the
block, so the question is exactly: *what is the long-`k` behavior of iterating
the operator the block denotes?* That is the home turf of our spectral / Godsil
eigenvalue-support / equitable-quotient theory.

### 2.1 Where it genuinely matches

**(a) Iteration = operator power = discrete-time walk.** If the looped map were
the *linear* operator `H` (or its unitary CTQW propagator `U_τ = exp(-iτ H)`),
then `k` loops = `H^k` / `U_{kτ}` = a discrete-time walk by step `τ`. In the
eigenbasis `H = Σ λ_j P_j`, iteration acts diagonally: `H^k = Σ λ_j^k P_j`,
`U_{kτ} = Σ e^{-ikτ λ_j} P_j`. This is the *exact* object our `Spectral.lean` /
`GodsilRatio.lean` analyze. **The dominant-eigenvalue projector is what survives
the loop** — for a real power `H^k` the top-|λ| eigenspace dominates; for the
unitary walk every `|λ_j|=1` survives but the *phases* `e^{-ikτλ_j}` evolve, and
revival/PST (our `PST/*`) is precisely "the phases re-align after `k` steps."
Our **eigenvalue-support** (`EigenvalueSupport G u`) is literally the set of
`λ_j` with nonzero weight on a vertex — i.e. *the only eigenvalues that can
affect that coordinate under any number of loops.* So:

  > **surviving-eigenvalue subset = what the loop can preserve / transport;
  > eigenvalues outside the joint support are invisible to iteration.**

**(b) The equitable quotient is the loop's invariant / fixed-point structure.**
`EquitablePartition.cellUniformSubspace_invariant` proves the cell-uniform
subspace is `H`-invariant; hence it is invariant under *every* `H^k` and under
`exp(-iτH)`. Cell-uniform vectors are the fixed-point manifold of the
symmetry-averaging; a loop started cell-uniform *stays* cell-uniform and runs
identically to the `r×r` `symmQuotient` (`restrict_eq_symmQuotient`). So **the
equitable quotient is exactly the reduced dynamical system the loop runs on its
symmetric sector** — its fixed points are the quotient's fixed points, and the
quotient's spectrum is the surviving spectrum. This is the rigorous content of
"the equitable quotient is the loop's fixed-point structure."

**(c) Spectral gap governs convergence / depth-generalization.** For a
*contractive* looped map (the DEQ regime, and the "reachability" axis of
2604.15259), convergence to the fixed point is geometric at rate set by the
sub-dominant eigenvalue: error `~ |λ_2/λ_1|^k` (real power) or by the Jacobian
spectral radius `ρ(∂f/∂z) < 1` at equilibrium (DEQ stability is *literally*
characterized by the Jacobian spectrum — DEQ §stability, and 2604.15259's
reachability axis). **The gap predicts how many loops to converge.** This is the
single cleanest bridge: *our quotient's spectral gap is a closed-form predictor
of loop-count-to-convergence on the symmetric sector.*

**(d) Hierarchical recurrence = MERA = nested equitable partitions.** HRM's
two-timescale structure is, formally, a *nested* fixed-point system:
`z_L^i = f_L(z_L^{i-1}, z_H, x)` iterated to a local equilibrium `z_L*(z_H)`,
then `z_H` updates once per `T` and re-seeds. This is precisely a **multi-scale
walk**: fast dynamics equilibrate within a coarse cell, coarse dynamics move
between cells. Our `mera_exact_iff_equitable` / the filtered-colimit picture
(`Dowsing/FilteredColimitPST.lean`) is the statement that **a nested
coarse-graining is exact iff the partitions are equitable at each scale** — i.e.
HRM's "hierarchical convergence" is the dynamical shadow of a *nested equitable
partition*: the L-equilibrium per cycle = a fine equitable quotient parametrized
by the H-state; the H-update = the coarse quotient's step. The **cofiltered /
inverse-limit dual** in `FilteredColimitPST.lean` §3 is the right home for "what
does the multi-scale loop compute as scales/iterations → ∞."

### 2.2 Where it differs — be honest

**(1) Real loops are NONLINEAR; `A^k` is an approximation.** The deciding
caveat. Every architecture here puts **nonlinearities (softmax, GELU/SwiGLU,
LayerNorm/RMSNorm) between iterations**, and most are *input-injected*
(`z_{k+1} = f(z_k, x)`, not `f(z_k)`), so the loop is an affine/nonlinear
dynamical system, not a pure linear power `H^k`. Consequences:
  - `H^k = Σ λ_j^k P_j` holds *exactly* only for a linear, input-free, tied
    block — i.e. our denotation is the **linearization / Koopman tangent** of the
    real loop, exact only locally or for the (real, trained) linear-attention
    looped models (Yang et al.'s linear in-context regression looped TF — where
    the loop demonstrably *is* iterating a linear solver, and our spectral story
    is on the nose).
  - LayerNorm is a *projection to a sphere* — it renormalizes the iterate each
    step. This changes the relevant object from `H^k v` to a **projectively
    normalized power iteration**, whose limit is the *top eigenvector* (power
    method), not the raw power. Interestingly this makes the *dominant-eigenvalue
    = surviving subset* prediction **stronger**, not weaker: normalized iteration
    is exactly power iteration onto the leading eigenspace.

**(2) DEQ = the walk's fixed point, not its trajectory.** DEQ throws away the
transient and reports `z*` with `z* = f(z*, x)`. In our language `z*` is the
**stationary/invariant vector** of the loop. For a CTQW there is no contraction
so no DEQ fixed point in the unitary sense — DEQ corresponds to the
*dissipative / Lindblad* regime (`Graphon/Lindblad.lean`, `NoiseEquitable.lean`),
where the walk relaxes to a steady state. So: **looped-with-residual+norm ≈ our
dissipative quantum-walk steady state; pure tied-linear loop ≈ our unitary
operator power.** Naming the regime matters.

**(3) Trained loops are not symmetric / not Hermitian in general.** Our spectral
theorems assume Hermitian `H` (real spectrum, orthogonal eigenprojectors). A
generic trained attention block is non-normal; iteration can show *transient
amplification* (pseudospectrum) before the asymptotic regime. The
`symmetrizedAttention` denotation deliberately Hermitianizes, so our analysis
predicts the **symmetric part's** asymptotics; the antisymmetric part is exactly
our **chiral** layer (`Chiral.lean`, `ChiralGraphon.lean`) — directed/chiral
walks. This is a feature: chiral graphplay is the right tool for the
non-Hermitian part of a real attention loop.

**(4) "Universal computation" (Giannou) is orthogonal to spectral asymptotics.**
Giannou's loop encodes a *program counter* and does discrete control flow; its
power is Turing-style, not spectral. Our framework says nothing about that
expressivity — it characterizes the *operator-iteration* reading of looping, not
the *stored-program* reading. Honest scope boundary.

### 2.3 Summary verdict

**"Looped transformer = iterated quantum walk" is a PARTIAL but principled
match.** It is *exact* for tied **linear** attention loops (and these provably
exist and are studied — Yang et al., and the linear-looped-TF fixed-point work
o8AaRKbP9K). For the real nonlinear/normalized loops it is the **correct
linearization / Koopman + power-iteration picture**, and the three things our
framework names — surviving-eigenvalue subset, equitable-quotient fixed-point
structure, spectral gap = convergence rate — are exactly the three axes that the
*independent* ML-theory fixed-point literature (DEQ Jacobian spectrum; 2604.15259
reachability/stability) has converged on. We are not retrofitting: the looped-TF
theory community is already doing spectral fixed-point analysis; we supply the
**equitable-quotient closed form** for it when the token graph has symmetry.

---

## 3. What our framework PREDICTS about looped transformers (testable)

1. **(STRONGEST) Equitable-quotient spectral gap predicts loops-to-converge.**
   For a looped/recurrent-depth block whose (symmetrized) token graph has an
   `r`-cell equitable partition, the number of loop iterations to reach a
   tolerance-`ε` fixed point on the symmetric sector is
   `k*(ε) ≈ log ε / log(|λ_2/λ_1|)`, where `λ_1 > λ_2` are the top two
   eigenvalues **of the small `r×r` quotient `Q̃`** — computable in `O(r^3)`
   without ever running the `n`-token loop. *Test:* take Huginn-3.5B or a trained
   looped-TF, build the equitable quotient of its attention on a symmetric input
   family (e.g. translation-invariant / block-structured prompts), compute the
   quotient gap, and check it predicts the measured iteration count at which the
   forward residual (HRM Fig. 3 / Huginn convergence curves) plateaus. A clean
   regression `measured-depth ∝ 1/gap` would confirm.

2. **Surviving-eigenvalue subset = what the loop preserves.** Components of the
   latent state lying outside the joint eigenvalue support of the
   (symmetrized) block are provably annihilated/frozen by iteration. *Test:*
   project Huginn's per-step latent onto the block's eigenbasis; the variance
   that survives many loops should concentrate on the top eigenspaces (power-method
   prediction under RMSNorm); directions outside the support should decay first.

3. **Depth-generalization is gated by gap-stability, not depth seen in
   training.** If the quotient gap `< 1` (contractive symmetric sector), the loop
   has a reachable fixed point and *should* extrapolate to more loops at test
   time (matches Fan et al. 2409.15647 length-gen and 2604.15259 reachability);
   if the gap `≈ 1` or the dominant eigenvalues are complex/equal-modulus, the
   loop *cycles* (revival regime — our PST!) rather than converging, predicting
   depth-generalization failure or periodic behavior. *Test:* tasks where the
   trained block's quotient has near-degenerate top eigenvalues should show
   oscillating (non-converging) test-time-compute curves.

4. **HRM/TRM = nested equitable partition ⇒ two-rate convergence law.** The fast
   loop converges at the *fine* quotient gap, the slow loop at the *coarse*
   quotient gap; HRM's residual-spike pattern (Fig. 3: L spikes reset each
   H-cycle) should match a two-timescale spectral model with rates
   `(gap_fine, gap_coarse)`. *Test:* fit the two gaps from HRM residual traces;
   predict the optimal `(T, N)` (inner/outer counts) as
   `T* ≈ 1/gap_fine`, `N* ≈ 1/gap_coarse`.

### Is HRM / looped a clean testbed for the probe?

**Yes for looped/recurrent-depth single-scale models (Huginn, Yang's looped-TF,
DEQ-transformer) — these are the cleanest probe.** They expose a single tied
block one can extract, symmetrize, build the equitable quotient of, compute the
gap, and directly compare quotient-gap-predicted convergence against the
published per-iteration residual curves. DEQ is even cleaner: it *reports the
fixed point and its Jacobian spectrum directly*, so prediction (2) and the gap
law are checkable with the model's own stability diagnostics.

**HRM/TRM are a richer but messier testbed.** The two-timescale structure is
*exactly* our nested/MERA prediction (a genuine point of contact others lack),
but the tasks (Sudoku, ARC, mazes) have discrete/combinatorial token graphs whose
symmetry (and hence equitable partition) is input-dependent and often trivial,
and the ARC-Prize re-analysis (`arcprize.org/blog/hrm-analysis`) shows much of
HRM's gain is from the outer refinement/augmentation loop rather than the inner
recurrence — so the spectral-gap law applies to the *inner* L-loop but the
headline performance is confounded. Use HRM to test the **nested-partition
two-rate prediction (#4)**, and use a single-scale looped/DEQ transformer with a
deliberately symmetric input family to test the **clean gap law (#1)**.

---

## 4. Pointers / not downloaded but noted

- TorchDEQ / `locuslab/deq` — DEQ Jacobian-spectrum stability diagnostics (ready-made for prediction #2).
- `seal-rg/recurrent-pretraining` + `tomg-group-umd/huginn-0125` — Huginn weights & per-iteration latent traces (for #1, #2).
- `sapientinc/HRM`, `hobson/HRM-eval`, `arcprize.org/blog/hrm-analysis` — HRM code + the confound caveat.
- "Fixed-Point Reasoning: Stable and Adaptive Deep Looped Models" (OpenReview 350036cd) and "Can Looped TF Learn Multi-step Gradient Descent" (o8AaRKbP9K) — the linear-looped-TF = iterative-solver result that makes our linear case exact.
- SELF-Transformer (2507.13569) — attention iterated *to a fixed point* per layer; another clean single-block probe.

---

*Honest bottom line:* iterating attention is iterating an operator, and operator
iteration is our entire subject — so the match is real at the level of *what is
being computed*. The gap is the nonlinearity/normalization between steps, which
turns the exact `H^k` into a normalized power-iteration / Koopman picture. The
three quantities we can compute from the small equitable quotient
(surviving-eigenvalue subset, fixed-point/invariant subspace, spectral gap) map
one-to-one onto the three axes the looped-TF stability literature already cares
about — and we add the closed-form `r×r` reduction they don't have.

( ◕‿◕ ) iterate the operator, read the spectrum, predict the loop.
