//! The probe: equitable decomposition + residual spectrum + surviving spectrum,
//! over a sweep of quantization resolutions (which control the cell-count `r`).
//!
//! This is the Rust analogue of `graphplay_probe.decompose(A, r_sweep)`. Because the
//! exact equitable partition is determined by the matrix (not a target `r`), we sweep
//! the *quantization resolution* `quant`; coarse quant ⇒ few cells, fine quant ⇒ many
//! cells, recovering the trivial partition `r = n` at the fine end. Each sweep point
//! reports the realized `r` and the full decomposition stats.

use crate::quotient::{frob, lift, quotient, residual, symm_quotient};
use crate::rsvd::{eigvals_desc_k, randomized_svdvals};
use crate::wl::{equitable_defect, equitable_partition};
use ndarray::Array2;
use serde::Serialize;

/// Per-sweep-point decomposition statistics.
#[derive(Serialize, Debug, Clone)]
pub struct SweepPoint {
    /// quantization resolution used for WL refinement.
    pub quant: f64,
    /// realized number of cells.
    pub r: usize,
    /// cell sizes (sorted descending, truncated to 32 for compactness).
    pub cell_sizes_head: Vec<usize>,
    /// `‖A‖_F`.
    pub norm_a: f64,
    /// `‖A_eq‖_F` (captured / explained mass).
    pub norm_a_eq: f64,
    /// `‖R‖_F` where `R = A − A_eq` (the residual / defect).
    pub norm_residual: f64,
    /// relative defect `‖R‖_F / ‖A‖_F` (the equitable "match" coordinate).
    pub rel_defect: f64,
    /// equitable defect on the *raw* matrix: max block-rowsum spread over a cell.
    pub equitable_defect: f64,
    /// top-`k` singular values of the residual `R` (randomized SVD).
    pub residual_svals: Vec<f64>,
    /// ε-rank of `R`: # singular values above `eps · σ₁(R)` (here within the top-k).
    pub residual_rank_eps: usize,
    /// eigenvalues of the symmetric normalized quotient `Q̃ = D^{1/2} Q D^{-1/2}`
    /// (the surviving spectrum), descending, truncated to top-`k`.
    pub surviving_spectrum: Vec<f64>,
}

/// Knobs for the decomposition.
#[derive(Clone, Debug)]
pub struct ProbeConfig {
    /// number of top residual singular values to compute.
    pub k: usize,
    /// rsvd oversampling.
    pub oversample: usize,
    /// rsvd power iterations.
    pub n_iter: usize,
    /// ε for the residual ε-rank.
    pub eps: f64,
}

impl Default for ProbeConfig {
    fn default() -> Self {
        ProbeConfig {
            k: 16,
            oversample: 10,
            n_iter: 2,
            eps: 1e-3,
        }
    }
}

/// Run one sweep point at a given quantization resolution.
pub fn decompose_at(a: &Array2<f64>, quant: f64, cfg: &ProbeConfig) -> SweepPoint {
    let p = equitable_partition(a, quant);
    let q = quotient(a, &p);
    let a_eq = lift(&q, &p);
    let r = residual(a, &a_eq);

    let norm_a = frob(a);
    let norm_a_eq = frob(&a_eq);
    let norm_residual = frob(&r);

    let residual_svals = randomized_svdvals(&r, cfg.k, cfg.oversample, cfg.n_iter);
    let rank_eps = if let Some(&s0) = residual_svals.first() {
        if s0 > 0.0 {
            residual_svals.iter().filter(|&&s| s > cfg.eps * s0).count()
        } else {
            0
        }
    } else {
        0
    };

    let ed = equitable_defect(a, &p);

    // Surviving spectrum = top-k eigenvalues of the symmetric normalized quotient.
    // Uses dense Jacobi for a small quotient and a randomized Rayleigh–Ritz estimate
    // when the quotient is large (`r ≈ n`), so this stays fast at scale.
    let qt = symm_quotient(&q);
    let surviving: Vec<f64> = eigvals_desc_k(&qt, cfg.k, cfg.oversample, cfg.n_iter);

    let mut sizes = q.sizes.clone();
    sizes.sort_unstable_by(|a, b| b.cmp(a));
    sizes.truncate(32);

    SweepPoint {
        quant,
        r: p.r,
        cell_sizes_head: sizes,
        norm_a,
        norm_a_eq,
        norm_residual,
        rel_defect: if norm_a > 0.0 {
            norm_residual / norm_a
        } else {
            0.0
        },
        equitable_defect: ed,
        residual_svals,
        residual_rank_eps: rank_eps,
        surviving_spectrum: surviving,
    }
}

/// The full decomposition over a sweep of quantization resolutions.
#[derive(Serialize, Debug, Clone)]
pub struct Decomposition {
    pub n: usize,
    pub config_k: usize,
    pub sweep: Vec<SweepPoint>,
}

/// Run the probe over a `quant`-sweep.
pub fn decompose(a: &Array2<f64>, quant_sweep: &[f64], cfg: &ProbeConfig) -> Decomposition {
    let sweep = quant_sweep
        .iter()
        .map(|&q| decompose_at(a, q, cfg))
        .collect();
    Decomposition {
        n: a.nrows(),
        config_k: cfg.k,
        sweep,
    }
}
