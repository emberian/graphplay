# Applied: the data/flag subdivision quotient (IBM heavy-hex motivation)

*A worked example of the equitable-quotient lift on a data/flag bipartition,
motivated by IBM superconducting-processor connectivity.*

**Scope.** The formalized host is the **2-cell data/flag subdivision**: a graph in which
flag vertices subdivide data–data edges, with the two roles forming the equitable partition.
The proven quotient spectrum is `±2√(N−1)` (`dataFlagQuotient_eigenvalues`), the spectrum of
subdividing the complete graph K_N. The honest content is the equitable-quotient PST / noise /
chiral lift on this data/flag bipartition. The degree-3 honeycomb connectivity of the physical
heavy-hex chip is the motivation, not what the Lean development formalizes.

## 1. The Graphplay framework in one paragraph

Graphplay treats a quantum-walk Hamiltonian as a Hermitian weighted graph
and asks: what is the **combinatorial assembly language** of the primitives
we run on it — perfect state transfer (PST), uniform mixing, spatial
search, chiral evolution? The framework's load-bearing object is the
**equitable partition** of the graph (Godsil–Royle; Bachman–Tamon
arXiv:1108.0339): a partition of the vertices such that the per-cell row
sums of the adjacency matrix only depend on the source cell. Every
equitable partition `P : V → I` produces a small **quotient matrix**
`Q : I × I → ℂ` on which CTQW primitives are easier to analyse, and lifts
of PST, mixing, and search statements from the quotient to the host are
proved as named theorems in `Graphplay.PST`, `Graphplay.Mixing`,
`Graphplay.Search`. **Spectral disassembly** is the converse process:
given a host operator (a chip's adjacency), recover its equitable
partitions, its bundle structure (when the host is `total` of a
`GraphBundle Q V`), and its chiral phasings (when there is a non-trivial
`ChiralSigning V` that descends to the quotient via
`signedBy_preserves_equitable`). This is the entire content of
`Graphplay.Chiral`.

## 2. The heavy-hex topology

IBM's superconducting processor family — Eagle (127 qubits, 2022), Heron
(133 qubits, 2023), Osprey (433), Condor (1121, 2023) — share a fixed
connectivity skeleton called the **heavy-hexagonal lattice**. It is a
(boundary-truncated) honeycomb lattice in which every edge has been
**subdivided** by a degree-2 "flag" qubit. The result has two kinds of
vertex:

* **Data qubits**, at honeycomb vertices, with degree at most 3 (degree 3
  in the interior, degree 2 on the boundary).
* **Flag qubits**, on subdivided edges, with degree exactly 2.

The heavy-hex graph is bipartite (only data–flag edges), planar, and has
girth 12. The design originates from Chamberland–Zhu–Yoder–Hertzberg–Cross
(arXiv:1907.09528): flag qubits serve as ancillas in subsystem
surface-code stabiliser measurements, and the 3-regular data sublattice
keeps qubit-frequency crowding manageable.

The data/flag role split — flag vertices subdividing data–data edges — is the equitable
partition the development uses. The formalized host carries this bipartition on a
complete-site subdivision (spectrum `±2√(N−1)`); the honeycomb adjacency itself is not
reproduced.

## 3. The data/flag equitable partition and its quotient

The equitable partition we settled on is the **2-cell role partition**:

```
P : HeavyHexVertex → Role           Role := { data, flag }
P (data v)   = data
P (flag u v) = flag
```

The data/flag role split is equitable on any data/flag subdivision graph: every flag vertex
sees its two endpoint data vertices, and (when each data vertex is incident to the same number
of flags) the role partition has constant cross-cell row sums. The proven quotient spectrum is
`±2√(N−1)` (`dataFlagQuotient_eigenvalues`), the spectrum of subdividing the complete graph
K_N; the degree-3 honeycomb is one special template (`λ² = 6`, `±√6`).

On a boundary-truncated chip the bare 2-cell partition is only almost equitable — boundary
data vertices have a smaller flag row sum than interior ones — and the equitable refinement
separates the degree classes. The 2-cell partition is exhibited in the Lean file as
`dataFlagPartition`; the boundary refinement is sketched.

## 4. Payoffs on the data/flag quotient

Three theorems on the data/flag bipartition. Each is proven axiom-clean: the quotient
spectrum, the cell-uniform PST lift, and both noise and chiral payoffs. The remaining `sorry`s
are upstream (boundary-truncation embedding; the `Mixing`/`Search` lifts blocked on upstream
identities), flagged at their sites and not feeding the payoffs.

### Payoff #1 — cell-uniform PST

`dataFlagQuotient_eigenvalues` proves (axiom-clean) the data/flag subdivision quotient has
spectrum `±2√(N−1)` (the spectrum of subdividing K_N; the degree-3 honeycomb template gives
`±√6`). The symmetric quotient `Q̃ = q·X`, `q = 2√(N−1)`, has PST at time `π/(2q)`;
`heavyHex_pst_lift` lifts this to cell-uniform PST between the data-uniform and flag-uniform
states via `EquitablePartition.pst_lift`. Promoting cell-uniform PST to two-qubit PST between
individual data vertices `u, v` requires an automorphism-symmetrisation step
(`ibm_native_pst_two_qubit`, `sorry`).

### Payoff #2 — Noise-symmetric subspaces

A noise model preserves the data/flag partition iff each of its Lindblad operators commutes
with the cell projector. Per-vertex dephasing and amplitude damping (each `|x⟩⟨x|` projector
supported on a single cell) and per-edge crosstalk with role-only rates are symmetric.
`Graphplay.Toolkit.Noise.cellUniform_preserved`: a cell-uniform state under any cell-uniform-
symmetric noise model stays cell-uniform, with evolution given by the noisy 2×2 quotient. This
is `dephasing_preserves_dataFlag` and `amplitudeDamping_preserves_dataFlag`, both proven
axiom-clean under the discrete-cells hypothesis (which is load-bearing for cells of size > 1;
`perEdge_crossTalk_may_break_dataFlag` exhibits a per-edge crosstalk model outside it).

### Payoff #3 — Chiral signing on the 2-cell quotient

On the 2-cell data/flag quotient, chiral signing leaves uniform mixing unchanged.
`dataFlag_chiral_no_speedup`: the signed off-diagonal magnitude `‖τ·q‖` equals `‖q‖`.
`dataFlag_chiral_spectrum_phase_independent`: the signed symmetric quotient
`[[0, e^{iφ}·q], [e^{-iφ}·q, 0]]` has spectrum `±q`, `q = 2√(N−1)`, independent of `φ`, so the
mixing time is phase-invariant. The engine is `roleHermitian_spectrum` (a zero-diagonal
Hermitian 2×2 matrix has spectrum `±r`, depending on its off-diagonal only through the modulus
`r`). The 2-cell quotient is too coarse for the Levine et al. (arXiv:2605.04414) chiral
speedup; a finer refinement carries more phase freedom.
The positive half (`refined_chiral_speedup`, still `sorry`: needs the 3-cell
boundary refinement + upstream `CellUniformMixing`):
on the 3-cell refinement (`data-3`, `data-2`, `flag`), the chiral
phasing has more room — three independent cross-cell phases — and the
chiral mixing optimisation theorem
(`Bundle.chiral_mixing_optimization`) reduces the choice of optimal
chip-level signing to a finite optimisation over 3 × 3 unitary signings
of the quotient. IBM Heron's tunable couplers are exactly the hardware
needed to realise the optimal signing: each cross-cell coupling carries
an independently-controllable phase. This is the meaning of the
`HardwareSpec` we attach to Heron (`allowedPhaseSet = unit circle`),
versus Eagle (`{1}`, no tunable phase).

## 5. Compiling an ML primitive INTO the chip — a falsifiable experiment

The disassembly above runs chip → quotient → CTQW primitive. The companion
file `Graphplay/Applications/CompileML.lean` runs the **inverse** direction —
*compilation*: ML primitive → small quotient → native chip couplings +
schedule. We pick a clean ML primitive that maps to a CTQW observable: a
**2-class structured-attention / associative-recall** task, where recall =
perfect transfer between a *query-uniform* state and a *key-uniform* state.
An attention head whose query/key structure is invariant under a symmetry
induces an equitable partition of its token graph into two role cells, and
the attention pattern descends to the `2×2` matrix the symmetry induces on
those cells (the `O(n²) → O(nr)` collapse of `Integrations.AttentionComplexity`).
When that induced matrix is the off-diagonal `K₂` coupling, the recall map
*is* PST between the two role cells — exactly the data/flag PST proven above.

The compiler `compileToHeavyHex` emits the native IBM-Heron coupling weights
(the proven `ibmHeronSpec` plus the static heavy-hex CTQW schedule run for
`t = π/(2q)`), so it lands on the *same* data/flag cells the disassembly
exposed. The compilation-correctness theorem
`compiled_cellUniform_realizes_target` is **proven, axiom-clean**: the
compiled host's cell-uniform evolution between the data (query) and flag (key)
cells realizes the target recall as PST, obtained by lifting the proven IBM
PST through the equitable partition. We did *not* search for a chip — the
couplings are emitted from the 2-cell recall quotient and the recall property
falls out of `heavyHex_pst_lift`.

The payoff is a **falsifiable on-device protocol**
(`compiled_experiment_prediction`, proven). Hand it to a lab running an
IBM-Heron device — this is the **Heron experiment**:

* **State prep.** Prepare the data-uniform (query) state
  `|C_data⟩ = |V|^{-1/2} ∑_{data v} |v⟩`.
* **Evolution.** Run the native heavy-hex CTQW (every nominal nearest-neighbour
  coupling at unit weight, tunable couplers at zero phase) for time
  `t = π/(2q)`, `q = 2√(N−1)`.
* **Measurement.** Measure the flag-uniform (key) population
  `P_key = |⟨C_flag|U(t)|C_data⟩|²`.
* **Predicted signal.** `P_key(t) = sin²(t·q)` (proven equal to the Born-rule
  population via `predictedKeyPopulation_eq_amplitude_sq`); in particular
  `P_key = 1` at `t = π/(2q)` (ideal recall, `predictedKeyPopulation_at_compiledTime`).
* **Deficit law.** The observed deficit `1 − P_key` is governed by the device
  noise model's `NoiseEquitable.NoiseModel.BreakingScore` of the data/flag
  partition: zero breaking score forces every positive-rate Lindblad to be
  block-diagonal w.r.t. the partition
  (`compiled_breakingScore_zero_blockDiagonal`, proven), so the recall is left
  intact to that order. A measured `P_key` deviating from `sin²(t·q)` by more
  than the breaking-score-predicted deficit **falsifies** either the chip's
  data/flag partition symmetry or the claim that its residual noise respects
  it — and with it the structured-attention `O(n) → O(r)` acceleration claim.
  (The prediction is genuinely two-sided: `compiled_positive_breakingScore_exists`
  proves a positive-breaking-score noise model exists, the regime in which a
  measured deficit is *predicted* rather than a falsification.) The single
  end-to-end referee check is `compile_recall_to_heron`, which compiles the
  plain-recall target onto a Heron-sized `(7, 19)` device and proves all four
  clauses (Heron spec, well-formed schedule, cell-uniform recall, ideal key
  population `1`).

## 6. Open questions about real chip parameters

A few obvious follow-ups that the Lean scaffold leaves open:

1. **Exact embedding match.** The `(n, m) = (7, 18)` rectangle for
   Eagle is an upper-bound rectangle; Eagle's *127* qubits come from an
   irregular truncation of `(7, 19) - one row`. A faithful embedding
   would encode the truncation as an explicit vertex subset.
2. **Tunable-coupler phase resolution.** We modelled
   `heronAllowedPhases` as the full unit circle. Real Heron control
   hardware realises a finite, clock-resolution-bounded subset. Working
   out which equitable-partition speedups survive that truncation is a
   concrete `HardwareSpec` engineering question.
3. **Surface-code interplay.** Heavy-hex was designed for compatibility
   with *subsystem surface codes* (Chamberland et al. 1907.09528). The
   data/flag partition is identical to the role split in those codes.
   Identifying logical operators as cell-uniform observables of the
   data/flag partition — and verifying that logical error rates are
   governed by the quotient noise model — would close the
   stabiliser-code loop.
4. **Chiral honeycomb signings.** The Levine et al. K_4 unitary
   signing (`unitaryHammingChiralK4` in `Graphplay.Chiral`) is the
   prototype chiral speedup for K_4. Its honeycomb analogue —
   explicit cross-cell phases on the 3-cell heavy-hex refinement —
   has, to our knowledge, not been written down. Working it out is the
   natural next worked example.
5. **Beyond IBM.** Google's Sycamore (a "two-tone" 2D square-lattice
   with diagonal cross-couplings) and Quantinuum's H-series
   (all-to-all on small registers) admit cleaner equitable partitions
   than heavy-hex. A side-by-side disassembly across architectures
   would test whether the equitable-partition lens *predicts* which
   chip is better-suited to a given CTQW primitive — the kind of
   architecture-comparison claim Graphplay was built to support.

---

*Files: `Graphplay/Applications/IBMHeavyHex.lean` (disassembly + payoffs)
and `Graphplay/Applications/CompileML.lean` (the compile-into-the-chip
direction).  Companion paper draft: this file. The core of all three
payoffs is now **proven, axiom-clean** — the exact `±2√(N−1)` quotient
spectrum (`dataFlagQuotient_eigenvalues`), the cell-uniform PST lift
(`heavyHex_pst_lift`), the noise-preservation theorems
(`dephasing_/amplitudeDamping_preserves_dataFlag`), and the chiral
no-speedup negative result (`dataFlag_chiral_no_speedup`,
`dataFlag_chiral_spectrum_phase_independent`) — together with the
compilation-correctness and falsifiable-prediction theorems
(`compiled_cellUniform_realizes_target`, `compiled_experiment_prediction`).
Remaining honest `sorry`s are upstream gaps: the boundary-truncation
embedding, the two-qubit automorphism promotion, and the `Mixing`/`Search`
lifts (blocked on still-`sorry`'d upstream identities), each flagged at its
site.*
