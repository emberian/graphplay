//! Quotient construction and the equitable lift.
//!
//! Given a partition `cell : 0..n -> 0..r`, the **block (quotient) matrix** is the
//! cell-pair *average* of `A`:
//!
//! `B[c][c'] = mean_{i∈c, j∈c'} A[i][j]`.
//!
//! This is the least-squares-best cell-constant approximation; for a genuinely
//! block-equitable `A` (where `A[i][j] = B[cell i][cell j]`, as in
//! `AttentionComplexity.lean`) it recovers `B` exactly. The **lift** `A_eq` re-expands
//! it to `n×n` via `A_eq[i][j] = B[cell i][cell j]`, and the **residual** is
//! `R = A − A_eq`.
//!
//! We also form the **symmetric normalized quotient** `Q̃ = D^{1/2} Q D^{-1/2}` where
//! `Q[c][c'] = B[c][c'] · |c'|` is the *divisor* (row-collapsed) quotient acting on
//! cell-indicator coordinates, and `D = diag(|c|)` is the cell-size diagonal. `Q̃` is
//! the symmetric conjugate whose spectrum is the subset of `A`'s spectrum that
//! survives into the quotient (matching `EquitablePartition.symmQuotient`,
//! `Q̃ = D^{1/2} Q D^{-1/2}` in the Lean spine).

use crate::wl::Partition;
use ndarray::parallel::prelude::*;
use ndarray::Array2;

/// The full quotient bundle for a partition.
pub struct Quotient {
    /// `B[c][c'] = mean over the (c,c') block of `A` — the cell-constant lift coeff.
    pub b: Array2<f64>,
    /// cell sizes `|c|`.
    pub sizes: Vec<usize>,
    /// `r` = number of cells.
    pub r: usize,
}

/// Build the block-average quotient `B[c][c']` and cell sizes.
pub fn quotient(a: &Array2<f64>, p: &Partition) -> Quotient {
    let r = p.r;
    let cells = p.cells();
    let sizes: Vec<usize> = cells.iter().map(|c| c.len()).collect();

    // sum over each block, in parallel over the r² blocks (flattened).
    let sums: Vec<f64> = (0..r * r)
        .into_par_iter()
        .map(|idx| {
            let c = idx / r;
            let cp = idx % r;
            let mut s = 0.0;
            for &i in &cells[c] {
                for &j in &cells[cp] {
                    s += a[[i, j]];
                }
            }
            s
        })
        .collect();

    let mut b = Array2::<f64>::zeros((r, r));
    for c in 0..r {
        for cp in 0..r {
            let denom = (sizes[c] * sizes[cp]) as f64;
            b[[c, cp]] = if denom > 0.0 {
                sums[c * r + cp] / denom
            } else {
                0.0
            };
        }
    }
    Quotient { b, sizes, r }
}

/// The equitable lift `A_eq[i][j] = B[cell i][cell j]`.
pub fn lift(q: &Quotient, p: &Partition) -> Array2<f64> {
    let n = p.cell.len();
    let mut out = Array2::<f64>::zeros((n, n));
    out.axis_iter_mut(ndarray::Axis(0))
        .into_par_iter()
        .enumerate()
        .for_each(|(i, mut row)| {
            let ci = p.cell[i];
            for j in 0..n {
                row[j] = q.b[[ci, p.cell[j]]];
            }
        });
    out
}

/// The residual `R = A − A_eq`.
pub fn residual(a: &Array2<f64>, a_eq: &Array2<f64>) -> Array2<f64> {
    a - a_eq
}

/// The **symmetric normalized quotient** `Q̃ = D^{1/2} Q D^{-1/2}` with
/// `Q[c][c'] = B[c][c'] · |c'|` (the divisor matrix) and `D = diag(|c|)`.
///
/// Concretely `Q̃[c][c'] = B[c][c'] · sqrt(|c'|·|c|)`, which is symmetric whenever the
/// average matrix `B` is (it is, for symmetric `A`), and whose eigenvalues are the
/// cell-uniform eigenvalues of `A`.
pub fn symm_quotient(q: &Quotient) -> Array2<f64> {
    let r = q.r;
    let mut qt = Array2::<f64>::zeros((r, r));
    for c in 0..r {
        for cp in 0..r {
            let w = ((q.sizes[c] as f64) * (q.sizes[cp] as f64)).sqrt();
            qt[[c, cp]] = q.b[[c, cp]] * w;
        }
    }
    qt
}

/// Frobenius norm of a matrix.
pub fn frob(a: &Array2<f64>) -> f64 {
    a.iter().map(|x| x * x).sum::<f64>().sqrt()
}
