//! Randomized SVD (Halko–Martinsson–Tropp) for the top-`k` singular values of a
//! large dense matrix, plus a small dense symmetric-eigensolver (Jacobi) used both
//! for the core SVD step and for the quotient spectrum.
//!
//! Pipeline for the residual `R` (n×n):
//!   1. draw a Gaussian test matrix `Ω` (n × ℓ), `ℓ = k + oversample`;
//!   2. form `Y = (R Rᵀ)^q R Ω` (subspace iteration, `q` power iterations) to
//!      capture the dominant range; orthonormalize `Y → Q` (modified Gram–Schmidt);
//!   3. form the small `B = Qᵀ R` (ℓ × n); compute the SVD of `B` via the
//!      eigendecomposition of the tiny `ℓ × ℓ` `B Bᵀ`; singular values of `R` ≈
//!      sqrt of those eigenvalues. `O(n² ℓ)` work, no `n³` factorization.

use ndarray::parallel::prelude::*;
use ndarray::{Array1, Array2, Axis};

/// Deterministic xorshift128+ style RNG so results are reproducible without an
/// external rng crate. Seeded per call.
struct Rng(u64, u64);
impl Rng {
    fn new(seed: u64) -> Self {
        // splitmix64 to spread the seed into two state words
        let mut z = seed.wrapping_add(0x9E3779B97F4A7C15);
        let mut next = || {
            z = z.wrapping_add(0x9E3779B97F4A7C15);
            let mut x = z;
            x = (x ^ (x >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94D049BB133111EB);
            x ^ (x >> 31)
        };
        Rng(next() | 1, next() | 1)
    }
    #[inline]
    fn next_u64(&mut self) -> u64 {
        let mut s1 = self.0;
        let s0 = self.1;
        self.0 = s0;
        s1 ^= s1 << 23;
        self.1 = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
        self.1.wrapping_add(s0)
    }
    /// standard normal via Box–Muller
    #[inline]
    fn next_normal(&mut self) -> f64 {
        let u1 = ((self.next_u64() >> 11) as f64 + 1.0) / (1u64 << 53) as f64;
        let u2 = ((self.next_u64() >> 11) as f64) / (1u64 << 53) as f64;
        (-2.0 * u1.ln()).sqrt() * (std::f64::consts::TAU * u2).cos()
    }
}

/// Top-`k` singular values of `a` (n×n or n×m) via randomized SVD.
/// `oversample` (default ~10) and `n_iter` (power iterations, default ~2) trade
/// accuracy for cost. Returns singular values in descending order (length ≤ k).
pub fn randomized_svdvals(a: &Array2<f64>, k: usize, oversample: usize, n_iter: usize) -> Vec<f64> {
    let (n, m) = a.dim();
    let l = (k + oversample).min(m).min(n);
    if l == 0 {
        return vec![];
    }
    // small enough? just do the exact symmetric path on AᵀA / AAᵀ.
    let mut rng = Rng::new(0x5EED_1234_ABCD_EF01);

    // Ω : m × l
    let mut omega = Array2::<f64>::zeros((m, l));
    for v in omega.iter_mut() {
        *v = rng.next_normal();
    }

    // Y = A Ω : n × l
    let mut y = par_matmul(a, &omega);
    orthonormalize(&mut y);

    // power/subspace iteration: Y ← orth(A (Aᵀ Y))
    for _ in 0..n_iter {
        let at_y = par_matmul_t(a, &y); // Aᵀ Y : m × l
        let mut yy = par_matmul(a, &at_y); // A (Aᵀ Y) : n × l
        orthonormalize(&mut yy);
        y = yy;
    }

    // B = Qᵀ A : l × m   (Q = y)
    let b = par_matmul_t(&y, a); // (n×l)ᵀ · (n×m) = l×m
    // singular values of B == singular values of A in the captured subspace.
    // get them from eigvals of B Bᵀ (l × l).
    let bbt = par_matmul_t2(&b, &b); // B Bᵀ : l × l
    let mut eig = jacobi_eigvals(&bbt);
    eig.sort_by(|a, b| b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal));
    eig.into_iter()
        .take(k)
        .map(|e| if e > 0.0 { e.sqrt() } else { 0.0 })
        .collect()
}

/// `C = A · B` with A : n×p, B : p×l  → n×l. Row-parallel.
fn par_matmul(a: &Array2<f64>, b: &Array2<f64>) -> Array2<f64> {
    let (n, p) = a.dim();
    let (p2, l) = b.dim();
    assert_eq!(p, p2);
    let mut c = Array2::<f64>::zeros((n, l));
    c.axis_iter_mut(Axis(0))
        .into_par_iter()
        .enumerate()
        .for_each(|(i, mut crow)| {
            for kk in 0..p {
                let aik = a[[i, kk]];
                if aik != 0.0 {
                    for j in 0..l {
                        crow[j] += aik * b[[kk, j]];
                    }
                }
            }
        });
    c
}

/// `C = Aᵀ · B` with A : n×p, B : n×l → p×l. (used as Aᵀ Y and Qᵀ A)
fn par_matmul_t(a: &Array2<f64>, b: &Array2<f64>) -> Array2<f64> {
    let (n, p) = a.dim();
    let (n2, l) = b.dim();
    assert_eq!(n, n2);
    let mut c = Array2::<f64>::zeros((p, l));
    c.axis_iter_mut(Axis(0))
        .into_par_iter()
        .enumerate()
        .for_each(|(i, mut crow)| {
            for kk in 0..n {
                let aki = a[[kk, i]];
                if aki != 0.0 {
                    for j in 0..l {
                        crow[j] += aki * b[[kk, j]];
                    }
                }
            }
        });
    c
}

/// `C = A · Bᵀ` with A : l×m, B : l×m → l×l. (used for B Bᵀ)
fn par_matmul_t2(a: &Array2<f64>, b: &Array2<f64>) -> Array2<f64> {
    let (la, m) = a.dim();
    let (lb, m2) = b.dim();
    assert_eq!(m, m2);
    let mut c = Array2::<f64>::zeros((la, lb));
    c.axis_iter_mut(Axis(0))
        .into_par_iter()
        .enumerate()
        .for_each(|(i, mut crow)| {
            for j in 0..lb {
                let mut s = 0.0;
                for kk in 0..m {
                    s += a[[i, kk]] * b[[j, kk]];
                }
                crow[j] = s;
            }
        });
    c
}

/// Modified Gram–Schmidt orthonormalization of the columns of `q` (n × l), in place.
fn orthonormalize(q: &mut Array2<f64>) {
    let (n, l) = q.dim();
    for j in 0..l {
        // subtract projections onto earlier columns
        for i in 0..j {
            let mut dot = 0.0;
            for r in 0..n {
                dot += q[[r, j]] * q[[r, i]];
            }
            for r in 0..n {
                q[[r, j]] -= dot * q[[r, i]];
            }
        }
        // normalize
        let mut nrm = 0.0;
        for r in 0..n {
            nrm += q[[r, j]] * q[[r, j]];
        }
        let nrm = nrm.sqrt();
        if nrm > 1e-12 {
            for r in 0..n {
                q[[r, j]] /= nrm;
            }
        }
    }
}

/// Eigenvalues of a small *symmetric* matrix via the cyclic Jacobi method.
/// Returns eigenvalues (unsorted). `O(l³)` per sweep, a few sweeps — fine for the
/// small `ℓ×ℓ` and the quotient `r×r`.
pub fn jacobi_eigvals(a: &Array2<f64>) -> Vec<f64> {
    let n = a.nrows();
    if n == 0 {
        return vec![];
    }
    let mut m = a.clone();
    // symmetrize defensively
    for i in 0..n {
        for j in (i + 1)..n {
            let v = 0.5 * (m[[i, j]] + m[[j, i]]);
            m[[i, j]] = v;
            m[[j, i]] = v;
        }
    }
    let max_sweeps = 100;
    for _ in 0..max_sweeps {
        // off-diagonal norm
        let mut off = 0.0;
        for i in 0..n {
            for j in (i + 1)..n {
                off += m[[i, j]] * m[[i, j]];
            }
        }
        if off.sqrt() < 1e-12 {
            break;
        }
        for p in 0..n {
            for q in (p + 1)..n {
                let apq = m[[p, q]];
                if apq.abs() < 1e-300 {
                    continue;
                }
                let app = m[[p, p]];
                let aqq = m[[q, q]];
                let theta = 0.5 * (aqq - app) / apq;
                let t = theta.signum() / (theta.abs() + (theta * theta + 1.0).sqrt());
                let c = 1.0 / (t * t + 1.0).sqrt();
                let s = t * c;
                // apply rotation to rows/cols p,q
                for i in 0..n {
                    let mip = m[[i, p]];
                    let miq = m[[i, q]];
                    m[[i, p]] = c * mip - s * miq;
                    m[[i, q]] = s * mip + c * miq;
                }
                for i in 0..n {
                    let mpi = m[[p, i]];
                    let mqi = m[[q, i]];
                    m[[p, i]] = c * mpi - s * mqi;
                    m[[q, i]] = s * mpi + c * mqi;
                }
            }
        }
    }
    (0..n).map(|i| m[[i, i]]).collect()
}

/// Eigenvalues of a (symmetric) matrix, sorted descending. Convenience wrapper
/// for the quotient spectrum. **Dense** — `O(n³)` Jacobi; only use for small `n`.
pub fn eigvals_desc(a: &Array2<f64>) -> Array1<f64> {
    let mut v = jacobi_eigvals(a);
    v.sort_by(|a, b| b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal));
    Array1::from(v)
}

/// Top-`k` eigenvalues (by magnitude, returned descending **with sign**) of a
/// *symmetric* matrix, sorted descending. Routes to dense Jacobi when the matrix is
/// small enough (`n ≤ dense_cutoff`), and otherwise to a randomized Rayleigh–Ritz
/// projection (`O(n²·ℓ)`), so it stays fast even when the quotient is itself large
/// (`r ≈ n`). This is the surviving-spectrum estimator used by the probe.
pub fn eigvals_desc_k(a: &Array2<f64>, k: usize, oversample: usize, n_iter: usize) -> Vec<f64> {
    let n = a.nrows();
    const DENSE_CUTOFF: usize = 512;
    if n <= DENSE_CUTOFF {
        let mut v = jacobi_eigvals(a);
        v.sort_by(|x, y| y.partial_cmp(x).unwrap_or(std::cmp::Ordering::Equal));
        v.truncate(k);
        return v;
    }
    randomized_sym_eigvals_topk(a, k, oversample, n_iter)
}

/// Randomized top-`k` eigenvalues (with sign) of a *symmetric* `n×n` matrix via
/// subspace iteration + Rayleigh–Ritz: capture the dominant-magnitude invariant
/// subspace `Q` (`n × ℓ`, `ℓ = k + oversample`) by `ℓ` steps of `Q ← orth(M Q)`,
/// then diagonalize the tiny `ℓ × ℓ` projected matrix `Qᵀ M Q` (dense Jacobi). The
/// Ritz values are the top-`k` eigenvalues by magnitude, sorted descending.
/// `O(n²·ℓ·n_iter)` work — no `n³` factorization.
pub fn randomized_sym_eigvals_topk(
    a: &Array2<f64>,
    k: usize,
    oversample: usize,
    n_iter: usize,
) -> Vec<f64> {
    let n = a.nrows();
    let l = (k + oversample).min(n);
    if l == 0 {
        return vec![];
    }
    let mut rng = Rng::new(0xA17E_BEEF_0F0F_1234);
    // Ω : n × l
    let mut q = Array2::<f64>::zeros((n, l));
    for v in q.iter_mut() {
        *v = rng.next_normal();
    }
    orthonormalize(&mut q);
    // subspace iteration on the symmetric M: Q ← orth(M Q)
    for _ in 0..(n_iter + 1) {
        let mq = par_matmul(a, &q); // n × l
        q = mq;
        orthonormalize(&mut q);
    }
    // project: T = Qᵀ M Q  (l × l), via MQ then Qᵀ(MQ)
    let mq = par_matmul(a, &q); // n × l
    let t = par_matmul_t(&q, &mq); // (n×l)ᵀ (n×l) = l × l
    let mut ritz = jacobi_eigvals(&t);
    ritz.sort_by(|x, y| {
        y.abs()
            .partial_cmp(&x.abs())
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    ritz.truncate(k);
    // present descending by value (sign-aware) for a stable spectrum view
    ritz.sort_by(|x, y| y.partial_cmp(x).unwrap_or(std::cmp::Ordering::Equal));
    ritz
}
