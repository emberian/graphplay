//! Integration tests:
//!  - a known block matrix refines to the correct (coarse) partition with zero residual;
//!  - a generic random matrix refines to the trivial all-singleton partition;
//!  - randomized SVD recovers known singular values of a low-rank residual;
//!  - npy round-trip.

use ndarray::Array2;
use rust_probe::npy::{load_npy, save_npy};
use rust_probe::quotient::{frob, lift, quotient, residual, symm_quotient};
use rust_probe::rsvd::{eigvals_desc, randomized_svdvals};
use rust_probe::wl::{equitable_defect, equitable_partition};

/// Build an n×n block-equitable matrix from a b×b block-value table, contiguous cells.
fn block_matrix(n: usize, blocks: usize, bvals: &[f64]) -> Array2<f64> {
    let cell = |i: usize| (i * blocks) / n;
    let mut a = Array2::<f64>::zeros((n, n));
    for i in 0..n {
        for j in 0..n {
            a[[i, j]] = bvals[cell(i) * blocks + cell(j)];
        }
    }
    a
}

#[test]
fn block_matrix_recovers_correct_partition() {
    // 2 distinct blocks ⇒ exactly 2 cells, each of size n/2.
    let n = 64;
    let bvals = [1.0, 0.3, 0.3, 2.0]; // symmetric 2×2 block values
    let a = block_matrix(n, 2, &bvals);

    let p = equitable_partition(&a, 1e6);
    assert_eq!(p.r, 2, "expected exactly 2 cells for a 2-block matrix");
    let sizes = p.cells().iter().map(|c| c.len()).collect::<Vec<_>>();
    let mut sizes = sizes;
    sizes.sort();
    assert_eq!(sizes, vec![32, 32], "cells must be the two equal halves");

    // residual must be ~0: A is genuinely block-equitable.
    let q = quotient(&a, &p);
    let a_eq = lift(&q, &p);
    let r = residual(&a, &a_eq);
    assert!(frob(&r) < 1e-9, "block matrix must have zero residual, got {}", frob(&r));
    assert!(equitable_defect(&a, &p) < 1e-9);
}

#[test]
fn three_block_matrix() {
    let n = 90; // divisible by 3
    // 3×3 symmetric block table, all distinct rows ⇒ 3 cells.
    let bvals = [
        1.0, 0.5, 0.2, //
        0.5, 2.0, 0.7, //
        0.2, 0.7, 3.0,
    ];
    let a = block_matrix(n, 3, &bvals);
    let p = equitable_partition(&a, 1e6);
    assert_eq!(p.r, 3);
    let q = quotient(&a, &p);
    // quotient B should equal the block table
    for c in 0..3 {
        for cp in 0..3 {
            assert!((q.b[[c, cp]] - bvals[c * 3 + cp]).abs() < 1e-9);
        }
    }
    // symmetric quotient is symmetric
    let qt = symm_quotient(&q);
    for c in 0..3 {
        for cp in 0..3 {
            assert!((qt[[c, cp]] - qt[[cp, c]]).abs() < 1e-9);
        }
    }
}

#[test]
fn random_matrix_is_trivial_partition() {
    // a generic random matrix has all-distinct row signatures ⇒ r = n singletons.
    let n = 48;
    let mut a = Array2::<f64>::zeros((n, n));
    // simple deterministic "random-ish" fill with all-distinct structure
    let mut s: u64 = 0x1234_5678;
    for v in a.iter_mut() {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        *v = (s >> 11) as f64 / (1u64 << 53) as f64;
    }
    // use a fine quantization so floating values aren't accidentally merged
    let p = equitable_partition(&a, 1e9);
    assert_eq!(p.r, n, "generic random matrix should give n singleton cells");
    // with the trivial partition the lift = A (each cell is a singleton) ⇒ residual ~0
    let q = quotient(&a, &p);
    let a_eq = lift(&q, &p);
    assert!(frob(&residual(&a, &a_eq)) < 1e-9);
}

#[test]
fn rsvd_recovers_lowrank_singular_values() {
    // construct a rank-2 matrix u1 v1ᵀ * s1 + u2 v2ᵀ * s2 with known singular values.
    let n = 200;
    let s1 = 10.0;
    let s2 = 3.0;
    // orthonormal-ish u/v via two simple deterministic vectors then Gram-Schmidt.
    let mut u1 = vec![0.0; n];
    let mut u2 = vec![0.0; n];
    let mut v1 = vec![0.0; n];
    let mut v2 = vec![0.0; n];
    for i in 0..n {
        let x = i as f64;
        u1[i] = (x * 0.01).sin();
        u2[i] = (x * 0.013 + 1.0).cos();
        v1[i] = (x * 0.017).cos();
        v2[i] = (x * 0.019 + 0.5).sin();
    }
    let normalize = |v: &mut Vec<f64>| {
        let nrm = v.iter().map(|x| x * x).sum::<f64>().sqrt();
        for x in v.iter_mut() {
            *x /= nrm;
        }
    };
    let orth = |v: &mut Vec<f64>, w: &[f64]| {
        let d: f64 = v.iter().zip(w).map(|(a, b)| a * b).sum();
        for (a, b) in v.iter_mut().zip(w) {
            *a -= d * b;
        }
    };
    normalize(&mut u1);
    orth(&mut u2, &u1);
    normalize(&mut u2);
    normalize(&mut v1);
    orth(&mut v2, &v1);
    normalize(&mut v2);

    let mut a = Array2::<f64>::zeros((n, n));
    for i in 0..n {
        for j in 0..n {
            a[[i, j]] = s1 * u1[i] * v1[j] + s2 * u2[i] * v2[j];
        }
    }
    let sv = randomized_svdvals(&a, 4, 8, 3);
    assert!(sv.len() >= 2);
    assert!((sv[0] - s1).abs() < 1e-2, "σ1 ≈ {s1}, got {}", sv[0]);
    assert!((sv[1] - s2).abs() < 1e-2, "σ2 ≈ {s2}, got {}", sv[1]);
    // remaining singular values ≈ 0
    if sv.len() > 2 {
        assert!(sv[2] < 1e-2, "σ3 ≈ 0, got {}", sv[2]);
    }
}

#[test]
fn jacobi_eigvals_match_known() {
    // diag(3,1,1) rotated: known eigenvalues {3,1,1}; test symmetric eig.
    let a = ndarray::array![[2.0, 1.0, 0.0], [1.0, 2.0, 0.0], [0.0, 0.0, 1.0]];
    // eigenvalues of [[2,1],[1,2]] are 3 and 1, plus the isolated 1.
    let ev = eigvals_desc(&a);
    assert!((ev[0] - 3.0).abs() < 1e-9);
    assert!((ev[1] - 1.0).abs() < 1e-9);
    assert!((ev[2] - 1.0).abs() < 1e-9);
}

#[test]
fn npy_roundtrip() {
    let a = ndarray::array![[1.0, 2.5, -3.0], [4.0, 0.0, 6.25]];
    let tmp = std::env::temp_dir().join("rust_probe_roundtrip_test.npy");
    save_npy(&tmp, &a).unwrap();
    let b = load_npy(&tmp).unwrap();
    assert_eq!(a.dim(), b.dim());
    for (x, y) in a.iter().zip(b.iter()) {
        assert!((x - y).abs() < 1e-12);
    }
    let _ = std::fs::remove_file(&tmp);
}
