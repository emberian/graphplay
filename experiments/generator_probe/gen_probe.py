"""Generator-structure probes for the score generator S = Q Kᵀ.

The thesis under test (NEW, open): a dense, full-rank attention matrix
``A = rownorm(exp(S/√d))`` may *look* irreducible, but the structure can live in
the GENERATOR ``S = Q Kᵀ`` (rank ≤ d by construction) — and specifically a
structure *beyond* low-rank: an equitable partition, a coherent / circulant /
Toeplitz algebra, a sparse "Hamiltonian" log, or a butterfly product.

We import the equitable machinery read-only from ``graphplay_probe.probe`` and
add the generator-specific probes here. Everything operates on real matrices.

Distinctions we keep brutally honest about:
  * "generator low-rank"   — KNOWN (it's why linear attention works). Baseline.
  * "generator equitable"  — NEW. Does S have a nontrivial 1-WL equitable
                             partition (r ≪ n) that A does not?
  * "generator coherent"   — NEW. Small entry-alphabet / association-scheme /
                             circulant-Toeplitz algebra even at full rank.
  * "log(A) sparse"        — NEW. Is the matrix-log a sparse Hamiltonian?
  * "butterfly product"    — NEW. Sub-quadratic product factorization of A / S.
"""

from __future__ import annotations

import sys
import os
import numpy as np
from scipy.linalg import logm

# read-only import of the existing instrument
_HERE = os.path.dirname(os.path.abspath(__file__))
_EXP = os.path.dirname(_HERE)
if _EXP not in sys.path:
    sys.path.insert(0, _EXP)
from graphplay_probe.probe import (  # noqa: E402
    equitable_partition_wl,
    quotient_lift,
    rank_eps,
    _symmetrize,
)


# --------------------------------------------------------------------------- #
# 1. generator rank (baseline, KNOWN)
# --------------------------------------------------------------------------- #
def generator_rank(S: np.ndarray, eps: float = 1e-2) -> dict:
    """rank(S) and the singular-value tail. For S = Q Kᵀ this should be ≤ d.

    Reported as the BASELINE 'generator low-rank' story (known)."""
    s = np.linalg.svd(S, compute_uv=False)
    s = s / (s[0] + 1e-30)
    return {
        "rank_eps": int(rank_eps(S, eps=eps)),
        "n": int(S.shape[0]),
        "svals_norm": s.tolist(),
        # effective rank (entropy of normalized singular spectrum)
        "eff_rank": float(np.exp(_spectral_entropy(s))),
        "stable_rank": float((s ** 2).sum() / (s[0] ** 2 + 1e-30)),
    }


def _spectral_entropy(s: np.ndarray) -> float:
    p = s / (s.sum() + 1e-30)
    p = p[p > 0]
    return float(-(p * np.log(p)).sum())


# --------------------------------------------------------------------------- #
# 2. equitable structure of the generator (THE NEW QUESTION)
# --------------------------------------------------------------------------- #
def equitable_defect(M: np.ndarray, n_bins: int = 16) -> dict:
    """Run 1-WL equitable partition on (symmetrized, quantized) ``M`` and report
    the number of cells r and the equitable defect ‖M − M_eq‖/‖M‖.

    A *small* r (≪ n) with a *small* defect ⇒ M has nontrivial equitable
    structure. r == n (all singletons) ⇒ no equitable structure (the generic
    fate of continuous-weight matrices under exact WL)."""
    n = M.shape[0]
    norm = float(np.linalg.norm(M)) + 1e-30
    part = equitable_partition_wl(M, n_bins=n_bins)
    r = int(part.max()) + 1
    M_eq, _ = quotient_lift(M, part)
    R = M - M_eq
    return {
        "n": n,
        "r_cells": r,
        "r_over_n": r / n,
        "defect_eq": float(np.linalg.norm(R) / norm),
        "rank_R": int(rank_eps(R)),
        "partition": part,
    }


def equitable_compare(S: np.ndarray, A: np.ndarray, n_bins: int = 16) -> dict:
    """The headline comparison: equitable structure of the GENERATOR S and its
    symmetrization vs. the equitable structure of A. Does S quotient where A
    does not?"""
    return {
        "S": equitable_defect(S, n_bins=n_bins),
        "S_sym": equitable_defect(_symmetrize(S), n_bins=n_bins),
        "A": equitable_defect(A, n_bins=n_bins),
        "A_sym": equitable_defect(_symmetrize(A), n_bins=n_bins),
    }


# --------------------------------------------------------------------------- #
# 3. coherent-algebra / color count / circulant-Toeplitz structure
# --------------------------------------------------------------------------- #
def entry_color_count(M: np.ndarray, n_bins: int = 64, rel_tol: float = 1e-3) -> dict:
    """How many distinct 'colors' (quantized entry values) does M have? A small
    alphabet at full rank is the association-scheme / coherent-algebra signature.
    We report both a fixed-bin count and an agglomerative 'natural' cluster count
    (gaps in the sorted unique values)."""
    n = M.shape[0]
    vals = M.ravel()
    lo, hi = float(vals.min()), float(vals.max())
    span = hi - lo + 1e-30
    # fixed quantization
    q = np.clip(((vals - lo) / span * n_bins).astype(int), 0, n_bins - 1)
    n_colors_binned = int(len(np.unique(q)))
    # natural clusters: sort, split where gap > rel_tol*span
    sv = np.sort(np.unique(np.round(vals / (rel_tol * span)) * (rel_tol * span)))
    n_colors_natural = int(len(sv))
    return {
        "n": n,
        "n_entries": int(M.size),
        "n_colors_binned": n_colors_binned,
        "n_colors_natural": n_colors_natural,
        "colors_per_n": n_colors_natural / n,
        # an association scheme on n points has O(n) classes at most; a circulant
        # has ≤ n distinct entries; a generic matrix has ~n² distinct entries.
        "alphabet_ratio": n_colors_natural / (M.size),
    }


def toeplitz_circulant_defect(M: np.ndarray) -> dict:
    """How close is M to Toeplitz (constant on diagonals) and to circulant
    (Toeplitz + wraparound)? A full-rank circulant/Toeplitz matrix has a TINY
    algebra (it is diagonalized by the DFT / generated by one shift).

    Returns relative-Frobenius defect to the nearest Toeplitz and circulant."""
    n = M.shape[0]
    norm = float(np.linalg.norm(M)) + 1e-30

    # nearest Toeplitz: average each diagonal
    T = np.zeros_like(M)
    for k in range(-(n - 1), n):
        idx = np.where(np.subtract.outer(np.arange(n), np.arange(n)) == -k)
        # diagonal offset k: entries M[i, i+k]
        diag_vals = [M[i, j] for i, j in zip(*idx)]
        m = np.mean(diag_vals)
        for i, j in zip(*idx):
            T[i, j] = m
    toeplitz_defect = float(np.linalg.norm(M - T) / norm)

    # nearest circulant: average over cyclic diagonals (i-j mod n)
    C = np.zeros_like(M)
    offs = (np.subtract.outer(np.arange(n), np.arange(n))) % n
    for k in range(n):
        mask = offs == k
        m = M[mask].mean()
        C[mask] = m
    circulant_defect = float(np.linalg.norm(M - C) / norm)

    return {
        "toeplitz_defect": toeplitz_defect,
        "circulant_defect": circulant_defect,
    }


def coherent_algebra_probe(M: np.ndarray) -> dict:
    """A cheap proxy for 'small coherent (adjacency) algebra'. The coherent
    closure of M is the smallest matrix *-algebra containing M, I, J closed under
    Schur (entrywise) product. We do not compute it exactly (expensive); instead
    we report two cheap upper-bound proxies for its dimension:

      * n_colors_natural (entry alphabet) — the coherent algebra of a matrix with
        c distinct entries has dimension ≥ c and is generated by ≤ c Schur-idem-
        potents; a SMALL alphabet bounds the algebra small.
      * the dimension of the *commutant-by-entry* — number of distinct rows under
        sorted-row-multiset (a 1-WL-ish color count on rows).
    """
    colors = entry_color_count(M)
    # row-multiset colors (sorted each row, dedup)
    rows_sorted = np.sort(M, axis=1)
    # quantize to dedup robustly
    lo, hi = rows_sorted.min(), rows_sorted.max()
    span = hi - lo + 1e-30
    rq = np.round((rows_sorted - lo) / span * 256).astype(int)
    uniq_rows = len({tuple(r) for r in rq})
    return {
        **colors,
        "distinct_row_profiles": int(uniq_rows),
        "row_profiles_per_n": uniq_rows / M.shape[0],
    }


# --------------------------------------------------------------------------- #
# 4. matrix-log of A — is the generator/Hamiltonian sparse?
# --------------------------------------------------------------------------- #
def _band_mass_fraction(M: np.ndarray, w: int) -> float:
    """Fraction of Frobenius mass within band half-width w."""
    n = M.shape[0]
    idx = np.abs(np.subtract.outer(np.arange(n), np.arange(n)))
    band = M * (idx <= w)
    return float(np.linalg.norm(band) ** 2 / (np.linalg.norm(M) ** 2 + 1e-30))


def sparsity_profile(M: np.ndarray, name: str = "") -> dict:
    """Is M sparse / banded / spiky? Reports:
      * gini of |entries| (concentration)
      * top-k% mass fraction
      * banded mass fraction at several half-widths
      * fraction of entries below 1% of max (numerically-zero)
    """
    a = np.abs(M.ravel())
    norm2 = float((a ** 2).sum()) + 1e-30
    a_sorted = np.sort(a)[::-1]
    cum = np.cumsum(a_sorted ** 2) / norm2
    n_e = a.size
    topk = {f"top{int(p*100)}pct_mass": float(cum[max(0, int(p * n_e) - 1)])
            for p in (0.01, 0.05, 0.1)}
    # gini
    s = np.sort(a)
    idx = np.arange(1, n_e + 1)
    gini = float((2 * (idx * s).sum()) / (n_e * s.sum() + 1e-30) - (n_e + 1) / n_e)
    near_zero = float((a < 0.01 * (a.max() + 1e-30)).mean())
    n = M.shape[0]
    bands = {f"band_w{w}_mass": _band_mass_fraction(M, w)
             for w in (1, 2, max(1, n // 8), max(1, n // 4))}
    return {"name": name, "gini": gini, "near_zero_frac": near_zero,
            **topk, **bands}


def matrix_log_A(A: np.ndarray, eps: float = 1e-6) -> dict:
    """Real matrix log of the row-stochastic A (the implied 'generator' if A were
    a one-step transition / propagator). We regularize A toward a doubly-mild
    operator and take the principal real log; we then ask whether log(A) is
    sparse / banded / low-degree-polynomial in a shift.

    Honest caveat: A is row-stochastic but generally NOT diagonalizable-with-
    positive-spectrum, so logm can be complex; we take the real part and report
    the imaginary mass as a fidelity flag."""
    from scipy.linalg import expm
    n = A.shape[0]
    # Blend A toward (1/n)J and the identity: a convex mix that is strictly
    # positive, row-stochastic, and pushes the spectrum into the right-half
    # plane so the principal real log is well-defined and exp(log)≈A_reg.
    J = np.full((n, n), 1.0 / n)
    A_reg = (1 - 2 * eps) * A + eps * np.eye(n) + eps * J
    A_reg = A_reg / A_reg.sum(axis=1, keepdims=True)
    try:
        G = logm(A_reg)
    except Exception as e:  # noqa: BLE001
        return {"ok": False, "error": str(e)}
    imag_mass = float(np.linalg.norm(G.imag) / (np.linalg.norm(G) + 1e-30))
    Gr = G.real
    # fidelity: does exp(real log) reproduce A_reg? if not, the log is unreliable
    # (A not diagonalizable with positive spectrum) and we must NOT trust sparsity.
    recon_err = float(np.linalg.norm(expm(Gr) - A_reg) / (np.linalg.norm(A_reg) + 1e-30))
    reliable = bool(recon_err < 0.05 and imag_mass < 0.05)
    prof = sparsity_profile(Gr, name="logA")
    return {"ok": True, "reliable": reliable, "imag_mass": imag_mass,
            "recon_err": recon_err, "rank_eps": int(rank_eps(Gr)), **prof}


# --------------------------------------------------------------------------- #
# 5. butterfly / monarch product factorization
# --------------------------------------------------------------------------- #
def _bit_reverse_perm(n_bits: int) -> np.ndarray:
    n = 1 << n_bits
    out = np.zeros(n, dtype=int)
    for i in range(n):
        b = 0
        x = i
        for _ in range(n_bits):
            b = (b << 1) | (x & 1)
            x >>= 1
        out[i] = b
    return out


def butterfly_fit(M: np.ndarray, depth: int | None = None, n_iter: int = 200,
                  lr: float = 0.05, seed: int = 0) -> dict:
    """Fit M ≈ B_L ... B_1 P, a product of ``depth`` butterfly (block-2x2)
    factors with a bit-reversal-style permutation, via gradient descent (torch).
    Each butterfly factor is a block-diagonal of 2x2 blocks at a given stride —
    O(n) params per factor, O(n log n) total, sub-quadratic.

    Returns relative-Frobenius error of the best product at the chosen depth,
    plus the error-vs-depth curve. A genuine butterfly matrix fits at error ~0
    with depth = log2(n); a generic dense full-rank matrix does NOT.
    """
    import torch

    n = M.shape[0]
    n_bits = int(np.ceil(np.log2(n)))
    n_pad = 1 << n_bits
    if depth is None:
        depth = n_bits

    Mp = np.zeros((n_pad, n_pad))
    Mp[:n, :n] = M
    target = torch.tensor(Mp, dtype=torch.float64)
    norm = target.norm().item() + 1e-30

    torch.manual_seed(seed)

    def build_butterfly(thetas_list):
        """Product of butterfly factors. Each factor mixes pairs at stride s=2^k."""
        prod = torch.eye(n_pad, dtype=torch.float64)
        for k, thetas in enumerate(thetas_list):
            stride = 1 << k
            F = torch.zeros(n_pad, n_pad, dtype=torch.float64)
            # 2x2 blocks: pair index i with i+stride within each block of 2*stride
            bidx = 0
            for base in range(0, n_pad, 2 * stride):
                for off in range(stride):
                    i = base + off
                    j = base + off + stride
                    a, b, c, d = thetas[bidx]
                    F[i, i] = a
                    F[i, j] = b
                    F[j, i] = c
                    F[j, j] = d
                    bidx += 1
            prod = F @ prod
        return prod

    n_blocks = n_pad // 2
    errs_by_depth = []
    best = None
    for dep in range(1, depth + 1):
        thetas_list = [torch.nn.Parameter(
            0.01 * torch.randn(n_blocks, 4, dtype=torch.float64)
            + torch.tensor([1.0, 0.0, 0.0, 1.0], dtype=torch.float64))
            for _ in range(dep)]
        opt = torch.optim.Adam(thetas_list, lr=lr)
        for _ in range(n_iter):
            opt.zero_grad()
            B = build_butterfly(thetas_list)
            loss = ((B - target) ** 2).sum()
            loss.backward()
            opt.step()
        with torch.no_grad():
            B = build_butterfly(thetas_list)
            err = (B - target).norm().item() / norm
        errs_by_depth.append(float(err))
        best = float(err)
    return {
        "n": n, "n_pad": n_pad, "depth": depth,
        "params_per_depth": int(n_blocks * 4),
        "dense_params": int(n * n),
        "err_by_depth": errs_by_depth,
        "best_err": best,
    }
