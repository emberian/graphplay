# rust-probe

High-throughput **equitable-partition + residual** decomposition core for the
attention-zoo probe — the Rust workhorse behind `paper/explanatory_program.md` §2
and the block-equitable math verified in
`Graphplay/Integrations/AttentionComplexity.lean`
(`A_eq[i][j] = B[cell i][cell j]`).

Given a large real `n×n` matrix `A` (an attention head, per layer), it computes:

1. the **exact equitable partition** via 1-WL color refinement on the symmetrized,
   quantized matrix (`src/wl.rs`);
2. the **quotient** `B[c][c'] = mean block` and the **symmetric normalized quotient**
   `Q̃ = D^{1/2} Q D^{-1/2}` (`src/quotient.rs`);
3. the **residual** `R = A − A_eq` and its top-`k` singular values via randomized SVD
   (`src/rsvd.rs`);
4. per-sweep-point JSON stats (`src/decompose.rs`): `r`, `‖A‖`, `‖A_eq‖`, `‖R‖`,
   `rel_defect = ‖R‖/‖A‖`, residual singular values + ε-rank, and the surviving
   spectrum (top-`k` eigenvalues of `Q̃`).

The semantics match the Lean spine exactly: a genuinely block-equitable `A` has
**zero residual** and the quotient recovers `B` exactly.

## Crate layout

```
src/lib.rs        public API re-exports
src/wl.rs         1-WL color refinement → exact equitable partition (parallel)
src/quotient.rs   block-average quotient B, equitable lift A_eq, residual, Q̃
src/rsvd.rs       randomized SVD (Halko–Martinsson–Tropp); dense + randomized
                  symmetric eigensolvers for the quotient spectrum
src/decompose.rs  the probe: full decomposition over a quantization sweep → JSON
src/npy.rs        .npy / .csv / raw-binary I/O (f4/f8, C-contiguous)
src/main.rs       CLI (probe + deterministic block/random matrix generators)
tests/probe.rs    integration tests
```

Dependencies: `ndarray` (+ rayon feature), `rayon` (data-parallel matmuls /
refinement), `serde` + `serde_json` (output), `byteorder` (binary I/O). No BLAS /
LAPACK / external RNG — fully self-contained and reproducible.

## Algorithms

**1-WL refinement (`equitable_partition`).** Symmetrize and quantize the edge
weights `S = quantize((A+Aᵀ)/2, quant)`. Seed colors by the diagonal, then iterate:
each vertex's new color is the canonicalization of `(old color, sorted multiset of
(edge weight, neighbour old color))`. Signatures are built in parallel and sorted to
dense ids deterministically. At the fixed point the color classes are the cells of
the **coarsest equitable partition** of the quantized graph. Per round is
`O(n² log n)`; it short-circuits when no cell splits **or** when `r = n` (the
all-singleton partition is automatically equitable — this bound is what keeps
noisy/generic matrices, which tend toward `r = n`, fast).

`quant` is the knob that drives the cell-count sweep: coarse `quant` ⇒ few cells
(structure dominates), fine `quant` ⇒ many cells, recovering the trivial `r = n`
partition at the fine end.

**Randomized SVD (`randomized_svdvals`).** For the residual `R` (n×n): draw a
Gaussian sketch `Ω` (n×ℓ, `ℓ = k + oversample`), capture the dominant range with
`n_iter` subspace iterations `Y ← orth(R(RᵀY))`, project `B = QᵀR`, and read the
top-`k` singular values off the tiny `ℓ×ℓ` `BBᵀ` (Jacobi). `O(n²·ℓ)` — no `n³`.

**Quotient spectrum (`eigvals_desc_k`).** Top-`k` eigenvalues (sign-aware) of the
symmetric `Q̃`. Dense cyclic-Jacobi when the quotient is small (`r ≤ 512`); a
randomized Rayleigh–Ritz projection (`randomized_sym_eigvals_topk`, `O(n²·ℓ)`) when
the quotient is itself large (`r ≈ n`) — so the surviving-spectrum step never
degenerates into an `O(r³)` dense eigendecomposition at scale.

## CLI

```sh
cargo build --release

# probe a matrix over a quantization sweep, write JSON
./target/release/rust-probe A.npy --r-sweep 1,4,16,64,256 --k 16 --out out.json
#   flags: --k K  --oversample O  --n-iter I  --eps E  --out FILE  (default stdout)
#   inputs: .npy (<f4/<f8, C-contiguous), .csv, .bin (<u64 rows><u64 cols><f64...>)

# deterministic generators (for benchmarking / smoke tests)
./target/release/rust-probe gen-block  block.npy  --n 2048 --blocks 8 [--noise 0.02] [--seed 7]
./target/release/rust-probe gen-random rand.npy   --n 2048 [--seed 3]
```

Each `--r-sweep` value is a quantization resolution; the realized cell-count `r` is
reported per point. The probe prints a one-line-per-point summary to stderr and the
full `Decomposition` (`n`, `config_k`, `sweep[]`) as JSON to `--out`/stdout.

## Build & test status

```
cargo build --release   # clean
cargo test  --release   # 6 passed; 0 failed
cargo clippy --release  # clean (no warnings)
```

Tests (`tests/probe.rs`): a known 2-block / 3-block matrix refines to the exact
coarse partition with zero residual and `B` = the block table; a generic random
matrix refines to the trivial `r = n` singleton partition; randomized SVD recovers
the known singular values of a rank-2 matrix to `< 1e-2`; Jacobi eigenvalues match a
known symmetric matrix; `.npy` round-trips.

## Benchmarks (n = 2048, 12-core Apple Silicon, `--release`)

Wall-clock via `/usr/bin/time -p` (includes the ~20 ms `.npy` load); "probe"
excludes I/O.

| matrix | sweep | realized `r` | rel_defect | probe time | wall |
|---|---|---|---|---|---|
| block 2048 (8 blocks, exact) | 1 pt | 8 | 0.0 (≈1e-13) | 176 ms | 0.40 s |
| block 2048 (8 blocks, exact) | 5 pts | 8 | 0.0 | 859 ms | 0.88 s |
| random 2048 | 1 pt | 2048 | 0.0 | 126 ms | 0.15 s |
| noisy 3-block 2048 (+0.01) | 1 pt @quant=5 | 5 | 0.0216 | 189 ms | 0.21 s |
| block 4096 (8 blocks, exact) | 1 pt | 8 | 0.0 | 712 ms | 0.81 s |

Scaling is the expected `O(n²)` per sweep point (2048→4096 ≈ 4×). A single probe
point on a 2048×2048 head is ~0.15–0.19 s end to end, so a full transformer's worth
of heads (layers × heads, each at several `r`) is seconds, not the minutes a
numpy/Python loop over dense `n×n` equitable refinement + dense SVD would take. The
randomized SVD and the `r = n` short-circuits are what make the **noisy / trivial**
cases (where naive 1-WL fragments to `r = n` and a dense quotient eigendecomposition
would be `O(n³)`) cheap rather than pathological.

### Honest note on noisy matrices

Exact 1-WL on a noisy matrix collapses to the block structure **only when the
quantization bucket is coarser than the noise but finer than the block-value gaps**.
In the noisy-3-block example above, `quant=5` recovers `r ≈ 5` cells with a small
residual (`rel_defect = 0.0216` — the residual *is* the noise); coarser/finer quant
either under- or over-fragments. When the block-value spacing is below the noise
floor (e.g. 8 blocks ⇒ 64 distinct values ~0.016 apart vs 0.02 noise) the blocks are
genuinely unidentifiable and 1-WL correctly returns `r = n`. The sweep is designed
to surface exactly this trade-off.

## How the Python probe calls it for scale

The Rust core is the scale path for the Python instrument: dump each attention head
to `.npy` and shell out (or read the JSON), instead of doing dense equitable
refinement + SVD in numpy on tiny models.

```python
import numpy as np, json, subprocess

def rust_probe(A: np.ndarray, r_sweep, k=16, bin="./target/release/rust-probe"):
    np.save("/tmp/head.npy", np.ascontiguousarray(A, dtype=np.float64))
    sweep = ",".join(str(q) for q in r_sweep)
    subprocess.run([bin, "/tmp/head.npy", "--r-sweep", sweep,
                    "--k", str(k), "--out", "/tmp/head.json"], check=True)
    return json.load(open("/tmp/head.json"))   # {n, config_k, sweep:[{r, rel_defect, ...}]}

# e.g. per (layer, head): A* from a trained full-attention reference
d = rust_probe(A_star, r_sweep=[1, 4, 16, 64, 256])
for sp in d["sweep"]:
    print(sp["r"], sp["rel_defect"], sp["residual_rank_eps"], sp["surviving_spectrum"][:4])
```

`.npy` is the zero-copy interchange (numpy `np.save` ↔ `src/npy.rs`); for tighter
loops the raw `.bin` (`<u64 rows><u64 cols><f64 row-major>`) avoids the npy header.
Everything is deterministic given the inputs (fixed-seed internal RNGs), so probe
outputs are reproducible across runs.
