# Quantum-Walk Transformers vs. our Walkformer: CTQWformer & GQWformer

Comparison of two prior quantum-walk-in-transformer papers against our walkformer
design, written for honest novelty positioning. Both papers put quantum walks into a
graph transformer for **graph classification**. Neither uses our sequence-as-line
framing, our learnable *mixture* of named walk atoms, our chiral/complex U(1) atom as an
ablatable wedge, or verified Lean operator semantics — but they are clear prior art on
the core idea "quantum-walk-derived structure → transformer attention bias." We are NOT
the first to put a quantum walk into a transformer. ( ◕‿◕ )

Sources:
- CTQWformer: *CTQWformer: A CTQW-based Transformer for Graph Classification*, Zhan Li,
  Wuqing Yu, Yusen Wu, Chuan Wang (Beijing Normal Univ.), arXiv:2605.09486, May 2026.
- GQWformer: *GQWformer: A Quantum-based Transformer for Graph Representation Learning*,
  Lei Yu, Hongyang Chen, Jingsong Lv, Linyao Yang (Zhejiang Lab), arXiv:2412.02285, Dec 2024.

---

## Paper 1 — CTQWformer (continuous-time, learnable Hamiltonian)

**1. Host graph.** The **input graph itself** (graph-classification on TUDataset-style
benchmarks: MUTAG, PTC, PROTEINS, DD, IMDB-B, IMDB-M). The walk runs over the actual
vertex set of each input graph. No sequence/line abstraction; positions are graph nodes.

**2. Walk operator.** **Continuous-time quantum walk (CTQW)**, fully quantum/unitary:
`U(t) = e^{-iHt}`, Schrödinger evolution `i d/dt|ψ⟩ = H|ψ⟩`. Crucially **H is learned, not
fixed**: they build a trainable Hamiltonian `H_θ = D' − A_sym` (Laplacian form) where the
edge weights of `A_sym` come from an MLP on concatenated incident node features
`w_ij = MLP_θ([x_i ‖ x_j])`, then symmetrized. So it is a *feature-adaptive Laplacian*
Hamiltonian. **Multiple times / multi-scale: yes** — they simulate over a set of discrete
time steps `T = {1,…,T}` and stack into a temporal evolution tensor
`P ∈ R^{T×n×n}`, sweeping `T ∈ {2,4,6,8,10}` in the sensitivity study (best ~T=4).
They initialize from all single-node basis states (identity `I_n`) and evolve each.

**3. How it enters the transformer.** **Two injection points** (this is the paper's
structure):
  - **(i) Attention bias (QWGT module):** the *final-time* propagation matrix `P^T ∈ R^{n×n}`
    is column-normalized to a stochastic matrix, log-scaled `B = log(1 + P^T)`, and **added
    inside the softmax**: `Attention = softmax(QK^T/√d + B) V`. This is structurally the
    same "additive pre-softmax bias from a walk operator" idea as ours.
  - **(ii) Recurrent temporal module (QWGR):** the *full* tensor `P` (all T steps),
    diagonal node-wise propagation series `s_i = [P(1)[i,i],…,P(T)[i,i]]`, is fed through a
    **BiGRU** to model temporal evolution, then mean-pooled.
  The two outputs are fused per layer; L layers stacked; global mean pool → classifier.

**4. Complex/phase structure.** The evolution `e^{-iHt}` is genuinely complex/unitary
**inside** the encoder, BUT they **collapse to real probabilities** before the
transformer: `p_i(t) = |⟨i|ψ(t)⟩|²` and `P^T` is a probability (real, non-negative,
stochastic) matrix. So phase/interference shapes the *magnitudes* but **no complex
amplitude or phase reaches attention** — it is `|amplitude|²`. **No chiral / magnetic /
directional structure**: H is symmetric/Hermitian-real (Laplacian of an undirected,
symmetrized graph), so no U(1) gauge phase, no directionality.

**5. Tasks + results.** Graph classification only. Headline accuracies (mean over 10-fold):
MUTAG **92.54**, PTC(MR) **69.16**, PROTEINS 78.53, DD **81.24**, IMDB-B 76.40,
IMDB-M 47.47. Beats graph-kernel baselines on 5/6; competitive with / mixed vs.
Graphormer, GraphGPS, GRIT. Ablation: removing the **recurrent** QWGR hurts most
(MUTAG 92.54→74.97), the attention-bias QWGT matters less.

---

## Paper 2 — GQWformer (discrete-time, coined, attribute-aware)

**1. Host graph.** The **input graph itself** (graph classification on five TUDatasets:
PROTEINS, MUTAG, PTC, IMDB-B, IMDB-M). Walk runs on the actual graph; positions are nodes.

**2. Walk operator.** **Discrete-time *coined* quantum walk (DTQW)**, fully quantum/unitary.
Position ⊗ coin Hilbert space `H = H_p ⊗ H_c`; one step is coin operator then shift:
`U = S(I ⊗ C)`, iterated `|φ^t⟩ = U^t|φ^0⟩`. They run **n non-interacting walkers in
parallel**, one launched from each node (superposition tensor `φ^0 ∈ C^{n×n×d}`,
d = max degree). **Attribute-aware coins**: the coin operator `C_i = I − 2 g(v_i)g(v_i)^T /
(g(v_i)^T g(v_i))` (a Householder reflection) is **learned from node features** via an
attention-style function `g(v_i)` over the neighbor feature matrix — this is their headline
novelty vs. vanilla DTQW, and it makes structurally-identical graphs with different features
produce different encodings. **Multi-scale / multi-step: yes** — they generate a sequence of
encoding matrices `{M^0,…,M^T}` (each `M^i ∈ C^{n×n}`... see point 4) by running T steps;
T (walk length) swept in {3..8}, best T=4. Walk length = receptive-field size.

**3. How it enters the transformer.** **Two injection points**, mirroring CTQWformer:
  - **(i) Attention bias (GQW-Attn):** they interpret the final encoding `M^T` as a
    pairwise distance/structure matrix with entries `p_ij`, and add it **inside the softmax**:
    `a_i = Σ_j exp(q_i^T k_j + p_ij) v_j / Σ_j exp(q_i^T k_j + p_ij)`. Same additive pre-softmax
    bias pattern.
  - **(ii) Recurrent module (GQW-Recu):** the whole sequence `{M^0,…,M^T}` is fed through a
    **bidirectional GRU** with pooling/fusion to capture temporal/sequential dependencies and
    local structure.
  A virtual/super node connected to all nodes serves as readout; L=4 blocks.

**4. Complex/phase structure.** Same as CTQWformer: amplitudes are complex during the DTQW,
but they **collapse to real before the transformer** — each encoding matrix
`M^i = Σ (squared spin states)`, i.e. they **sum the squares of the spin amplitudes** over the
coin space to get a real `M^i ∈ R^{n×n}` (the bias `p_ij` is real). The coin Householder
operators are taken **real** ("elementary unitary matrices … `I − 2ee^T/(e^Te)`"). So again:
interference shapes magnitudes, **no phase/complex amplitude in attention**. **No explicit
chiral/magnetic/directional design**, though the coined-walk shift operator does have a notion
of directed edge traversal internally — they do not expose it as a directional/phase feature.

**5. Tasks + results.** Graph classification only. Headline accuracies: MUTAG **95.2**,
PTC **76.7**, PROTEINS **80.7**, IMDB-B **79.3**, IMDB-M **55.3** — reported as beating all 11
baselines (incl. RWC/RWNN, CIN, GSN, GNN-AK). Ablation: both GQW-Attn and GQW-Recu contribute;
their attribute-aware coin beats vanilla-QW and invariant-QW encodings.

---

## Compare / contrast table vs. our walkformer

| Axis | **Our walkformer** | **CTQWformer** | **GQWformer** |
|---|---|---|---|
| **Host graph** | sequence positions = vertices of a **latent 1-D line/cycle** | **input graph itself** (per-sample) | **input graph itself** (per-sample) |
| **CT vs DT walk** | analytic **CT** atoms (path-heat, shift, circulant, chiral, Chebyshev) as Toeplitz fns of offset | **continuous-time** `e^{-iHt}` | **discrete-time coined** `U=S(I⊗C)` |
| **Which H / operator** | family of **named operators** on the line/cycle (shift, circulant, band-pass, U(1)-phased) | learned **Laplacian** `D'−A_sym`, feature-adaptive | learned **coin** (Householder) + shift; coin is feature-adaptive |
| **Quantum phase vs real-collapse** | **keeps complex phase**: chiral atom `Re(e^{iφd})` is a genuine U(1) phase in the bias | **real-collapse** `\|⟨i\|ψ⟩\|²` (probabilities) | **real-collapse** (sum of squared spin amplitudes) |
| **Chiral / directional** | **yes — explicit chiral U(1)-phased, ablatable wedge** | no (symmetric real H) | no (real coins; direction not exposed) |
| **Injection point** | **attention bias** (Toeplitz, added to QK) | attention **bias** (`+B` pre-softmax) **and** BiGRU recurrent | attention **bias** (`+p_ij` pre-softmax) **and** BiGRU recurrent |
| **Single walk vs learned mixture** | **learnable simplex mixture of multiple named atoms** | effectively single learned CTQW (one H, multi-T tensor) | single attribute-aware DTQW (multi-T sequence) |
| **Multi-scale / multi-time** | yes — multiple atoms + Chebyshev band scales; offset-parametrized | yes — time-step set `T`, full tensor `P` | yes — walk length T sequence `{M^0..M^T}` |
| **Verified semantics** | **yes — operators formalized in Lean (graphplay), machine-checked mixing/PST** | no | no |
| **Target domain** | **sequence / LM** (restrans harness, vs ALiBi/standard/resonance) | graph classification (TUDataset) | graph classification (TUDataset) |
| **Baselines compared** | ALiBi, standard attention, resonance kernels | graph kernels, Graphormer/GraphGPS/GRIT | GIN/CIN/GSN/RWC etc. |

---

## What's genuinely different about ours (honest)

1. **Learnable *mixture* of named walk atoms.** Both prior papers learn **one** walk
   operator (CTQWformer: one feature-adaptive Hamiltonian; GQWformer: one attribute-aware
   coined walk) and read it out over multiple times. We instead take a **simplex-weighted
   mixture of several analytically-distinct atoms** (path-heat, shift, circulant, chiral,
   Chebyshev band-pass), each a closed-form Toeplitz function of relative offset. The
   learnable object is the *combination weights over a basis of named operators*, not the
   internal parameters of a single walk. This is a different inductive prior and it is
   interpretable per-atom.

2. **Chiral / complex U(1) atom as an explicit, ablatable wedge.** This is the sharpest
   technical difference. Both papers have complex amplitudes *internally* but **collapse to
   real probabilities** (`|ψ|²` / summed squared spins) before the transformer, and both use
   **symmetric/real** generators (real Laplacian; real Householder coins). **Neither carries
   phase, directionality, or any magnetic/U(1)/chiral structure into attention.** Our
   `Re(e^{iφd})` chiral atom keeps a genuine relative-phase, direction-sensitive bias and we
   can ablate it on/off. On a directed/causal sequence this is a real, unexplored axis they
   left open.

3. **Verified Lean operator semantics.** Our walk atoms map to operators **formalized and
   machine-checked in Lean (graphplay)**, with proven mixing / PST semantics. Neither prior
   paper has any formal verification — they are empirical deep-learning papers. This is a
   credibility/certificate wedge, not a benchmark wedge.

4. **Sequence-LM framing, not graph classification.** Both prior works are squarely
   graph-classification on TUDataset (small molecular/social graphs). We operate on a **latent
   1-D line/cycle for sequence/LM** in the restrans harness against sequence baselines
   (ALiBi/standard/resonance). The host-graph abstraction is fundamentally different: they
   walk on the *given* graph; we walk on an *imposed* position geometry.

**Where they got there first (be explicit):**
- **CTQW-as-transformer-structural-bias is prior art.** Both papers add a quantum-walk-derived
  matrix **inside the softmax as an attention bias** — exactly our "walk operator → attention
  bias" move. We are **not** the first to put a quantum walk into a transformer, nor the first
  to use `e^{-iHt}`/CTQW as the bias generator (CTQWformer does precisely that, with a
  *learnable* Hamiltonian — arguably more flexible than our fixed analytic atoms on that one
  axis).
- **Learnable, feature-adaptive walk operators** also predate us (CTQWformer's trainable
  Hamiltonian; GQWformer's attribute-aware coin; and earlier Dernbach et al. 2019 "QW with
  feature-dependent coins" they both cite).
- **Multi-scale / multi-time walk readout** predates us (both stack a time/step sequence).
- **Coupling the walk with a recurrent module** is their shared design (BiGRU over the
  time-step sequence) — we do not currently do this.

So our defensible novelty is the **combination**: learnable *mixture-of-named-atoms* + an
explicit *chiral/complex* atom that survives into attention (no real-collapse) + *verified*
operator semantics + *sequence-LM* domain. Each ingredient individually has neighbors in the
literature; the chiral-phase-in-attention + Lean-verification pairing is the cleanest "first."

---

## Atom inspiration — concrete ideas to steal (focus on NON-heat / non-diffusive)

1. **Learnable feature/content-adaptive generator (from CTQWformer's trainable Hamiltonian).**
   Today our atoms are fixed analytic Toeplitz kernels with only mixture weights learned. Add a
   **content-conditioned atom**: let a small MLP on the token pair (or on a global summary)
   modulate the atom's parameters (e.g. the chiral phase φ, the Chebyshev band center/width, or
   shift offset). CTQWformer shows a learned `H_θ` measurably helps; we can borrow the
   *conditioning* without giving up our named-atom interpretability. **Non-diffusive** because it
   targets the phase/band atoms, not heat.

2. **Coined / directed-edge walk atom (from GQWformer's DTQW).** A **discrete-time coined**
   atom on the line/cycle gives a position⊗coin internal state with an explicit *directed*
   shift — a natural home for genuine **directionality** on a causal sequence. Combined with a
   **complex (not real) coin**, this would be a strictly stronger chiral wedge than our current
   `Re(e^{iφd})`: keep the coin Householder/rotation **complex** and **do not** sum-square it,
   so phase reaches attention. This is exactly the "non-real-collapse" gap both papers leave
   open. Strong steal.

3. **Multi-time stacked readout + recurrent fusion (shared by both).** Instead of one Toeplitz
   bias per atom, emit the **whole time/offset-scale series** of an atom and fuse it (a tiny
   GRU or learned scale-mixture) — i.e. expose τ as a *family* `{τ_1..τ_T}` per atom rather than
   one effective scale. CTQWformer's ablation says the **recurrent/temporal** path matters more
   than the static bias, which is a strong hint our single-snapshot bias is leaving signal on
   the table. Implement as a multi-scale band-pass stack (non-heat).

4. **Spectral band-pass / Chebyshev-of-Laplacian framing made explicit (sharpen what we have).**
   Both papers use a *single* spectral object; we already have a Chebyshev band-pass atom — lean
   into it: add **several band-pass atoms at distinct center frequencies** (low/mid/high bands of
   the line/cycle Laplacian) as separate simplex components, so the mixture can learn a
   *frequency profile*. This is genuinely non-diffusive (heat is the low-pass extreme; band-pass
   and high-pass are new behavior).

5. **Stochastic-row-normalized bias trick (cheap, from CTQWformer `B = log(1+P^T)`).** A small
   implementation idea: try **column/row-normalizing** an atom to a stochastic matrix and using
   `log(1+·)` before adding to QK, for numerical stability and a probability-like prior. Minor,
   but free and they found it stable.

---

## Bottom line

Both CTQWformer and GQWformer are direct prior art for "quantum-walk → attention bias in a graph
transformer," and CTQWformer specifically pre-dates us on **CTQW `e^{-iHt}` as the bias generator
with a learnable Hamiltonian**. We must not claim first-contact on quantum-walks-in-transformers.
Our honest, defensible wedge is the **learnable mixture of named atoms**, the **chiral/complex U(1)
atom that survives into attention without real-collapse** (both papers collapse to `|amplitude|²`
and use real, symmetric generators — they leave phase/direction on the table), the **Lean-verified
operator semantics**, and the **sequence-LM** (not graph-classification) domain.

Top 3 atoms to steal: (1) a **complex coined/directed DTQW atom** that does NOT sum-square,
turning our chiral wedge into a true phase-carrying directed walk; (2) **content-conditioned atom
parameters** (learnable φ / band / offset) à la CTQWformer's trainable Hamiltonian, kept
interpretable; (3) **multi-scale time-series readout + light recurrent/scale-mixture fusion**,
since CTQWformer's ablation says the temporal path beats the static snapshot.

⊂( ◜◒◝ )⊃ a little poem for the road:

  *Two walkers came before us on the graph,*
  *squared their amplitudes and lost the phase —*
  *we keep the turning U(1) in its math,*
  *and prove the turning right, in Lean's clear gaze.*
