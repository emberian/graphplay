# SCALING_CLAIMS — numerically demonstrated scaling, expanding the Lean frontiers

**Purpose.** Each Lean headline carries a *structural* reduction that is proven
axiom-clean, plus an *open* timing/advantage clause held as an honest `sorry`
(see `paper/RESULTS_LEDGER.md`). This directory turns four of those open clauses
from "honest open sorry" into **"demonstrated numerically across a family, with a
fitted scaling exponent."** Each claim below = a figure + a fitted exponent + a
precise one-line statement of what is now demonstrated (and what remains an open
Lean clause).

All experiments: `source experiments/.venv/bin/activate; python experiments/scaling/expN_*.py`.
Method is dense/eigendecomposition exact dynamics (no Trotter error); fits are
log-log linear with standard errors. Honesty notes on fit quality and finite-size
effects are included per claim.

---

## CLAIM 1 — Quantum search is O(√N) on the complete graph K_n

**Script:** `exp1_kn_search.py` · **Figure:** `figures/exp1_kn_search.png` ·
**Data:** `exp1_results.json`

**Method.** CTQW spatial search `H = -γ·A(K_n) - |w⟩⟨w|`, optimal coupling
`γ = 1/n`. We use the EXACT 2-dimensional invariant subspace `span{|w⟩,|u⟩}` —
the same reduced 2×2 generator `reducedH n` proven in the Lean
`completeGraph_2d_block` — diagonalize it, start from the uniform state `|s⟩`,
scan `t` and find the first time-to-peak `T*(n)` and peak success.

**Result.** Across `n = 16, 32, …, 1024`:

| | fitted |
|---|---|
| time-to-peak | **T\* = 1.5708 · n^(0.5000 ± 0.0000)** (log-log RMS resid 1.6e-15) |
| prefactor | C = 1.5708 = **π/2** (matches theory exactly) |
| peak success | **1.000000** at every n |

> **Demonstrated claim.** *We demonstrate `T* = (π/2)·n^0.5000` — the exact √N
> Grover/CTQW timing — on K_n across n = 16..1024, with the time-to-peak exponent
> equal to 0.5 to machine precision and peak success probability 1.0.* This
> numerically realizes the timing that the Lean spine proves only as the exact
> 2×2 Rabi *amplitude* `√((n-1)/n)` (`quantum_search_exact_amplitude`); the full
> dynamical `IsOptimalCTQWSearch` timing remains the route the ledger tracks.

Honesty: this is an exact reduction (the 2×2 block is exact), so the exponent is
not a noisy fit — it is `0.5` to floating point. The peak is `1.0` because we
start from `|s⟩` (the standard spatial-search initial state), where the K_n Rabi
oscillation reaches full overlap; the Lean `√((n-1)/n)` prefactor is the
`|w⟩→|w⟩` *survival* amplitude (a different initial condition), and both → 1.

---

## CLAIM 2 — Quantum search is O(√N) on the SPARSE hypercube Q_d (the headline)

**Script:** `exp2_hypercube_search.py` · **Figure:** `figures/exp2_hypercube_search.png` ·
**Data:** `exp2_results.json`

**This is the claim-expander.** The open Lean clause
`hypercube_search_optimal_timing` (`SparseSearch.lean:631`) asserts the O(√N)
*timing* on `Q_d` and is a single honest `sorry`; its structural half — the
Hamming-distance equitable reduction to a `(d+1)`-dim collapsed Hamming chain — is
the axiom-clean `hypercube_sparse_search_reduction`.

**Method.** We DEMONSTRATE the timing by simulating exactly that equitable
reduction: `H = -γ·A(Q_d) - |w⟩⟨w|` collapses to the `(d+1)`-dimensional
Krawtchouk tridiagonal chain on the orthonormal shell basis
(`A~[k,k+1] = √((d-k)(k+1))`), with the oracle `-|e₀⟩⟨e₀|`. The coupling `γ` is
critically tuned per `d` (numerically maximizing peak success — the honest
Childs–Goldstone critical-`γ` procedure, no closed form assumed). Initial state =
uniform `|s⟩` (shell amplitude `√(C(d,k)/N)`).

**Result.** Across `d = 4..10`, i.e. `N = 2^d = 16..1024`, on a host of **degree
exactly `d = log₂ N`**:

| | fitted |
|---|---|
| time-to-peak | **T\* = 2.00 · N^(0.479 ± 0.014)** (log-log RMS resid 5.2e-2) |
| peak success | ~**0.75 – 0.83** (a STABLE constant, not decaying) |

> **Demonstrated claim.** *We demonstrate `T* ∝ N^(0.48±0.01)` across N = 16..1024
> on the sparse Boolean hypercube `Q_d` — a host of degree only `log₂ N` — with the
> peak success probability holding at a constant ~0.8 (the Childs–Goldstone
> constant-success signature), i.e. a full √N quantum search advantage on a
> physically buildable, log-degree host. The formal O(√N) `IsOptimalCTQWSearch`
> timing (`hypercube_search_optimal_timing`) remains an open Lean clause; this is
> its numerical demonstration.*

Honesty / finite-size: the fitted exponent `0.479` sits just below the asymptotic
`0.5`; with only `d = 4..10` (7 points) and the leading-order finite-`d`
corrections to critical `γ`, this is the expected mild downward bias. The key
*qualitative* fact — that peak success stays **constant** rather than decaying as
`N` grows 64× — is the unambiguous signature that the √N regime holds (contrast
the d≤3 lattice in Claim 3, where peak success decays).

---

## CLAIM 3 — The d>4 lattice dimension threshold (Childs–Goldstone)

**Script:** `exp3_lattice_threshold.py` · **Figure:** `figures/exp3_lattice_threshold.png` ·
**Data:** `exp3_results.json`

<!-- FILLED IN BY exp3 RUN -->

**Method.** Full (non-reduced) CTQW search on the periodic torus `Z_L^d`,
`H = -γ·A - |w⟩⟨w|`, `γ` tuned per `(d,L)`, dense `eigh` on the `N = L^d`
Hilbert space. We track how the **peak success probability** and `T*` scale with
`N` across `d = 2,3,4,5,6`. The threshold prediction (Childs–Goldstone): peak
success → const for `d ≥ 5`, marginal at `d = 4`, and **decays** for `d ≤ 3`.

This is the open Lean clause `lattice_search_dimension_threshold`
(`IsOptimalCTQWSearch (latticeGraph d L) w ↔ 4 < d`), whose proof needs the
Childs–Goldstone spectral integral (IR convergence, dimension-4-critical).

> **Demonstrated claim (RESULTS PENDING exp3 run — see below).**

---

## CLAIM 4 — Attention apply is O(n·r) (linear), dense is O(n²)

**Script:** `exp4_attention_linear.py` · **Figure:** `figures/exp4_attention_linear.png` ·
**Data:** `exp4_results.json`

**Method.** Real wall-clock timing of the block-equitable attention apply
(precompute `r` cell-sums in `O(n·d)`, then per-token `r`-term contraction in
`O(n·r·d)`) versus the dense `O(n²·d)` apply, at fixed cells `r = 8`, features
`d = 16`, for `n = 128 … 16384`. Both compute the SAME output when
`A[i][j] = B[cell i][cell j]` — the exact identity proven in the Lean
`blockAttentionApply_eq_fullAttentionApply`.

**Result.**

| | fitted (asymptotic, n ≥ 512) |
|---|---|
| dense apply | **t ∝ n^(2.44)** (≥ quadratic; super-quadratic in wall-clock from cache/bandwidth) |
| block apply | **t ∝ n^(0.98)** — linear in n |
| correctness | max\|dense − block\| = **2.6e-12** (machine precision, all n) |
| speedup | **67.9×** at n = 16384, and **growing with n** |

> **Demonstrated claim.** *We demonstrate empirically that the block-equitable
> attention apply runs in time `∝ n^0.98` (linear) while the dense apply runs in
> `∝ n^2.4` (at least quadratic), producing identical output to 1e-12, with the
> speedup growing to 68× at n = 16384 — backing the proven Lean O(n·r) reduction
> (`attention_apply_linear_in_n`, `blockAttentionApply_eq_fullAttentionApply`) with
> real timings.* Here the Lean side is already axiom-clean; this experiment
> confirms the *constant factors and asymptotics are real*, not just the
> operation-count model.

Honesty: the dense exponent `2.44 > 2` reflects memory-bandwidth/cache effects on
the materialized `n×n` matrix (super-quadratic wall-clock), which only strengthens
the "dense is at least quadratic" conclusion. The block exponent `0.98` is the
clean linear scaling. At small `n` (< 512) numpy per-call overhead dominates and
the block apply is *slower* in absolute terms; the crossover is near `n ≈ 1024`.

---

## Summary table

| # | Claim | Family | Fitted exponent | Status of formal Lean clause |
|---|-------|--------|-----------------|------------------------------|
| 1 | K_n search √N | n=16..1024 | T\* ∝ n^**0.5000±0.0000** | timing route open; amplitude proven |
| 2 | **Q_d (sparse) search √N** | N=16..1024 | T\* ∝ N^**0.479±0.014** | `hypercube_search_optimal_timing` OPEN |
| 3 | lattice d>4 threshold | d=2..6 | (see Claim 3) | `lattice_search_dimension_threshold` OPEN |
| 4 | attention O(n·r) | n=128..16384 | block n^**0.98**, dense n^**2.44** | proven; timings confirm |

**Strongest newly-demonstrable claim:** Claim 2 — *a full √N quantum search
advantage on the sparse, buildable hypercube `Q_d` (degree log₂N), demonstrated
across N = 16..1024 with a constant ~0.8 peak success* — because it numerically
expands the headline open clause `hypercube_search_optimal_timing` from
"structural reduction proven" to "√N timing demonstrated."
