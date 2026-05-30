//! 1-WL color refinement to the *exact* equitable partition of a real matrix.
//!
//! Semantics (matching `Graphplay/Integrations/AttentionComplexity.lean`): the
//! coarsest partition `cell : 0..n -> 0..r` such that the matrix is *block-equitable*
//! up to the chosen quantization, i.e. `A[i][j] ≈ B[cell i][cell j]`. We obtain it by
//! standard color refinement on the *symmetrized, quantized* matrix `S = quantize((A+Aᵀ)/2)`:
//!
//! Each round, a vertex `i`'s new color is the hash of its *old* color together with the
//! multiset of `(quantized edge weight, neighbour old color)` pairs over all `j`. The
//! partition is iterated to a fixed point (no further split). At the fixed point the
//! color classes are exactly the cells of the coarsest equitable partition of the
//! quantized graph — which is the genuine 1-WL stable coloring.
//!
//! Complexity: each round sorts `n` signature vectors of length `O(n)`, so
//! `O(n² log n)` per round and at most `n` rounds, but in practice the partition
//! stabilizes in a handful of rounds.

use ndarray::Array2;
use rayon::prelude::*;
use std::collections::HashMap;

/// Result of refinement: a `cell` map and the number of cells `r`.
#[derive(Clone, Debug)]
pub struct Partition {
    /// `cell[i]` is the cell index (`0..r`) of vertex `i`.
    pub cell: Vec<usize>,
    /// number of cells.
    pub r: usize,
}

impl Partition {
    /// Build the membership lists `cells[c] = { i : cell i = c }`.
    pub fn cells(&self) -> Vec<Vec<usize>> {
        let mut out = vec![Vec::new(); self.r];
        for (i, &c) in self.cell.iter().enumerate() {
            out[c].push(i);
        }
        out
    }
}

/// Quantize a real value to an integer bucket at resolution `1/quant`.
/// Larger `quant` ⇒ finer buckets ⇒ more (smaller) cells.
#[inline]
fn qbucket(x: f64, quant: f64) -> i64 {
    (x * quant).round() as i64
}

/// Compute the exact (stable) 1-WL equitable partition of the matrix `a`.
///
/// `quant` controls the edge-weight quantization (e.g. `1e6` ≈ exact for clean
/// block matrices; smaller values tolerate floating noise so learned attention
/// still collapses). The matrix is symmetrized to `(A+Aᵀ)/2` for the signatures
/// (the equitable structure is about the undirected weighted graph), but the
/// quotient lift downstream uses the original `A`.
pub fn equitable_partition(a: &Array2<f64>, quant: f64) -> Partition {
    let n = a.nrows();
    assert_eq!(n, a.ncols(), "matrix must be square");
    if n == 0 {
        return Partition { cell: vec![], r: 0 };
    }

    // Symmetrized + quantized edge weights, materialized once: sym[i][j].
    // (For large n this is the dominant n² memory term; acceptable for n≈few-k.)
    let sym: Vec<Vec<i64>> = (0..n)
        .into_par_iter()
        .map(|i| {
            let mut row = Vec::with_capacity(n);
            for j in 0..n {
                let v = 0.5 * (a[[i, j]] + a[[j, i]]);
                row.push(qbucket(v, quant));
            }
            row
        })
        .collect();

    // Initial coloring: split vertices by their own diagonal value (a natural
    // 1-WL seed that distinguishes self-weights), all else equal.
    let mut color: Vec<usize> = vec![0; n];
    {
        let mut seed: HashMap<i64, usize> = HashMap::new();
        for i in 0..n {
            let d = sym[i][i];
            let next = seed.len();
            let c = *seed.entry(d).or_insert(next);
            color[i] = c;
        }
    }
    let mut num_colors = color.iter().copied().max().map(|m| m + 1).unwrap_or(1);

    // Refine to a fixed point.
    loop {
        // For each vertex, build a signature: (own color, sorted [(weight, nbr color)]).
        // We compute signatures in parallel, then canonicalize to dense new colors.
        let sigs: Vec<Vec<(i64, usize)>> = (0..n)
            .into_par_iter()
            .map(|i| {
                let mut s: Vec<(i64, usize)> = (0..n).map(|j| (sym[i][j], color[j])).collect();
                s.sort_unstable();
                s
            })
            .collect();

        // Key = (own color, signature, vertex). Map to dense new color ids, in a
        // stable order so the labeling is deterministic.
        type Keyed<'a> = (usize, &'a Vec<(i64, usize)>, usize);
        let mut keyed: Vec<Keyed> = (0..n).map(|i| (color[i], &sigs[i], i)).collect();
        keyed.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(b.1)));

        let mut new_color = vec![0usize; n];
        let mut next_id = 0usize;
        for (idx, win) in keyed.iter().enumerate() {
            if idx == 0 {
                new_color[win.2] = 0;
                continue;
            }
            let prev = &keyed[idx - 1];
            let same = prev.0 == win.0 && prev.1 == win.1;
            if !same {
                next_id += 1;
            }
            new_color[win.2] = next_id;
        }
        let new_num = next_id + 1;

        if new_num == num_colors || new_num == n {
            // No new splits ⇒ stable (equitable) coloring reached. Also short-circuit
            // when every vertex is already its own cell (`r == n`): the all-singleton
            // partition is automatically equitable, so no further round can refine it.
            // This bounds the pathological "fragment one cell per round" case that
            // arises on noisy/generic matrices (which tend toward `r = n`).
            color = new_color;
            num_colors = new_num;
            break;
        }
        color = new_color;
        num_colors = new_num;
    }

    Partition {
        cell: color,
        r: num_colors,
    }
}

/// Verify (for tests / diagnostics) that a partition is genuinely equitable for
/// the *quantized symmetrized* matrix: for every ordered cell pair `(c, c')`, every
/// vertex `i ∈ c` has the same quantized row-sum into `c'`. Returns the max
/// absolute defect over the *raw* (unquantized) matrix, i.e.
/// `max_{c,c'} (max - min) of (Σ_{j∈c'} A[i][j]) over i∈c`.
pub fn equitable_defect(a: &Array2<f64>, p: &Partition) -> f64 {
    let cells = p.cells();
    let mut worst = 0.0f64;
    for c in &cells {
        for cp in &cells {
            let mut lo = f64::INFINITY;
            let mut hi = f64::NEG_INFINITY;
            for &i in c {
                let mut s = 0.0;
                for &j in cp {
                    s += a[[i, j]];
                }
                lo = lo.min(s);
                hi = hi.max(s);
            }
            worst = worst.max(hi - lo);
        }
    }
    worst
}
