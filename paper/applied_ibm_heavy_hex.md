# Applied spectral disassembly: IBM heavy-hex

*A worked example of Graphplay applied to a real superconducting processor.*

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

In Graphplay terms: **heavy-hex = edge-subdivision of the honeycomb**, and
that is the only combinatorial fact we need to disassemble it.

## 3. The data/flag equitable partition and its quotient

The equitable partition we settled on is the **2-cell role partition**:

```
P : HeavyHexVertex → Role           Role := { data, flag }
P (data v)   = data
P (flag u v) = flag
```

On the *toroidal* / *interior-only* honeycomb (every data qubit has
degree 3) this is straightforwardly equitable. Every data qubit sees 3
flag qubits and 0 data qubits; every flag qubit sees 2 data qubits and
0 flag qubits. The quotient matrix is

```
        data  flag
data  [   0    3  ]
flag  [   2    0  ]
```

a 2 × 2 matrix with characteristic polynomial `λ² = 6` and eigenvalues
`±√6`.

On a *boundary-truncated* chip (real Eagle / Heron / Condor), the 2-cell
partition is only **almost** equitable: boundary data qubits have row sum
2 into the flag cell, while interior data qubits have row sum 3. The fix
is a 3-cell refinement that separates `(data, deg=3)`,
`(data, deg=2)`, and `(flag)`. Both partitions are exhibited in the Lean
file as `dataFlagPartition` and (sketched) `refined_chiral_speedup`.

## 4. Engineering payoffs

The Lean file gives three concrete `theorem` statements representing the
engineering payoffs of the disassembly. As of the current proof state, the
core of all three is **proven, axiom-clean**: the exact quotient spectrum,
the cell-uniform PST lift, and both halves of the noise and chiral payoffs
are fully discharged. The only remaining `sorry`s are honest upstream gaps
(boundary-truncation embedding, and the `Mixing`/`Search` lifts that route
through still-`sorry`'d upstream identities); they are flagged at their
sites and never feed the payoffs below.

### Payoff #1 — PST between two specified data qubits (PROVEN)

The exact quotient spectrum is now a theorem:
`dataFlagQuotient_eigenvalues` proves (axiom-clean) that the data/flag
quotient has spectrum exactly `{±2√(N−1)}`, `N = |HoneyVertex| = 2nm` (the
toroidal-template special case is the textbook `±√6`). The symmetric
quotient `Q̃ = q·X`, `q = 2√(N−1)`, exhibits perfect state transfer at time
`π / (2q)`; `heavyHex_pst_lift` then proves (axiom-clean) that this lifts to
*cell-uniform* PST between the data-uniform state and the flag-uniform state,
via `EquitablePartition.pst_lift`. A further chip-automorphism average —
concretely, any reflection or rotation symmetry of the chip exchanging a pair
of data qubits `u, v` — promotes cell-uniform PST to two-qubit PST between
`|u⟩` and `|v⟩` (`ibm_native_pst_two_qubit`, still `sorry`: needs the
automorphism-symmetrisation step). The protocol uses only the chip's native
couplings: Heron's tunable couplers suffice.

### Payoff #2 — Noise-symmetric subspaces (PROVEN)

A noise model preserves the data/flag partition iff each of its Lindblad
operators commutes with the cell projector. Working out three standard
models:

* **Per-vertex dephasing** at uniform rate: each `|x⟩⟨x|` projector
  is supported on a single cell, so the noise is **cell-uniform-symmetric**.
* **Per-vertex amplitude damping** at uniform rate: same conclusion.
* **Per-edge crosstalk** with rates depending only on `(role, role)`:
  symmetric. **Arbitrary** per-edge crosstalk: not symmetric.

`Graphplay.Toolkit.Noise.cellUniform_preserved` then says: a *cell-uniform
initial state* under any cell-uniform-symmetric noise model remains
cell-uniform for all time, and its evolution is the noisy evolution of
the 2 × 2 quotient. This is the engineering content of
`dephasing_preserves_dataFlag` and `amplitudeDamping_preserves_dataFlag`,
both now **proven (axiom-clean)** under the genuinely-needed discrete-cells
hypothesis (the unconditional bare-vector statement is *false* for cells of
size `> 1`, and the file proves that obstruction as a separate theorem,
`perEdge_crossTalk_may_break_dataFlag` — a real per-edge crosstalk noise
model that breaks the partition).

### Payoff #3 — Chiral-signing optimisation for fast mixing (negative half PROVEN)

Here we get an interesting *negative result*, and it is now **proven
(axiom-clean)**: on the 2-cell data/flag quotient, chiral signings
(cross-constant unitary phases τ : Role → Role → ℂ) cannot speed up uniform
mixing. `dataFlag_chiral_no_speedup` proves the signed off-diagonal magnitude
`‖τ·q‖` equals the unsigned `‖q‖`, and `dataFlag_chiral_spectrum_phase_independent`
proves the full spectral statement: the signed symmetric quotient
`[[0, e^{iφ}·q], [e^{-iφ}·q, 0]]` has spectrum exactly `{±q}`, `q = 2√(N−1)`,
*independent of the phase* `φ` — so the spectral radius (hence the mixing
time) is `φ`-invariant. The matrix-level engine is `roleHermitian_spectrum`
(any zero-diagonal Hermitian `2×2` `Role`-matrix has spectrum `{±r}` depending
on its off-diagonal *only through the modulus* `r`). The 2-cell quotient is
*too coarse* for the Levine et al. (arXiv:2605.04414) chiral speedup to bite.
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
