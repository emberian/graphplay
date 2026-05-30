"""The equitable-decomposition probe.

Given an n×n attention matrix ``A`` we want to place it in *one coordinate
system* — the equitable-partition spectrum — and simultaneously measure how
close it lies to each of the structured submanifolds that the attention zoo
bets on (low-rank, banded, fixed-sparse).

Definitions used here
---------------------
* **Equitable partition.** A partition ``P`` of the vertices into cells is
  *equitable* for ``A`` when the row-sum of ``A`` from any vertex into a fixed
  cell depends only on the cell of the source vertex. We find it for the
  *symmetrized, quantized* ``A`` via 1-WL colour refinement (exact equitable
  partition), and we also produce *soft* partitions at a target cell-count ``r``
  via spectral clustering.
* **Quotient lift.** Given a partition with cells ``C_1..C_r`` the lift
  ``A_eq`` is the matrix that is *constant on cell-pairs*, equal on block
  ``(a,b)`` to the mean of ``A`` over ``C_a × C_b``. This is the orthogonal
  (Frobenius) projection of ``A`` onto the space of cell-constant matrices, so
  ``R = A − A_eq`` is the minimal-norm equitability defect for that partition.
* **Symmetric quotient ``Q̃``.** The r×r quotient operator
  ``Q̃ = D^{1/2} Q D^{-1/2}`` where ``Q`` is the (cell-mean) quotient and ``D``
  is diag(cell sizes). Its eigenvalues are the subset of ``A``'s spectrum that
  "survives" the lift.
"""

from __future__ import annotations

from typing import Optional

import numpy as np


# --------------------------------------------------------------------------- #
# helpers
# --------------------------------------------------------------------------- #
def _symmetrize(A: np.ndarray) -> np.ndarray:
    return 0.5 * (A + A.T)


def rank_eps(M: np.ndarray, eps: float = 1e-2, relative: bool = True) -> int:
    """Numerical rank: number of singular values above ``eps`` (relative to the
    top singular value when ``relative``)."""
    if M.size == 0:
        return 0
    s = np.linalg.svd(M, compute_uv=False)
    if s.size == 0 or s[0] == 0:
        return 0
    thresh = eps * s[0] if relative else eps
    return int(np.sum(s > thresh))


# --------------------------------------------------------------------------- #
# partitions
# --------------------------------------------------------------------------- #
def equitable_partition_wl(
    A: np.ndarray,
    n_bins: int = 16,
    max_iter: int = 100,
    symmetrize: bool = True,
) -> np.ndarray:
    """Exact equitable partition of (symmetrized, quantized) ``A`` via 1-WL
    colour refinement.

    We quantize edge weights into ``n_bins`` buckets so that "equal row-sum
    into a cell" is a discrete predicate (a continuous weighted graph has only
    the trivial equitable partition almost surely). The returned array maps each
    vertex to its stable colour; colours are relabelled 0..r-1.
    """
    M = _symmetrize(A) if symmetrize else A
    n = M.shape[0]
    if n == 0:
        return np.zeros(0, dtype=int)

    # quantize weights so refinement sees discrete multiset signatures
    lo, hi = float(M.min()), float(M.max())
    if hi > lo:
        Q = np.clip(((M - lo) / (hi - lo) * n_bins).astype(int), 0, n_bins - 1)
    else:
        Q = np.zeros_like(M, dtype=int)

    colors = np.zeros(n, dtype=int)  # start: everyone one colour
    for _ in range(max_iter):
        # signature of a vertex = its own colour + sorted (neighbour-colour,
        # quantized-weight) multiset
        sigs = []
        for i in range(n):
            neigh = tuple(sorted((int(colors[j]), int(Q[i, j])) for j in range(n)))
            sigs.append((int(colors[i]), neigh))
        # relabel signatures to dense colour ids
        uniq = {s: k for k, s in enumerate(sorted(set(sigs)))}
        new_colors = np.array([uniq[s] for s in sigs], dtype=int)
        if new_colors.max() == colors.max() and np.array_equal(
            _canonical(new_colors), _canonical(colors)
        ):
            colors = new_colors
            break
        colors = new_colors
    return _canonical(colors)


def _canonical(labels: np.ndarray) -> np.ndarray:
    """Relabel a partition so cells are 0..r-1 in order of first appearance."""
    seen: dict[int, int] = {}
    out = np.empty_like(labels)
    for i, v in enumerate(labels):
        v = int(v)
        if v not in seen:
            seen[v] = len(seen)
        out[i] = seen[v]
    return out


def spectral_partition(A: np.ndarray, r: int, symmetrize: bool = True) -> np.ndarray:
    """Soft equitable partition into exactly ``r`` cells via spectral
    clustering on the symmetrized ``A`` (treated as an affinity)."""
    from sklearn.cluster import KMeans

    n = A.shape[0]
    r = max(1, min(r, n))
    if r == 1:
        return np.zeros(n, dtype=int)
    if r >= n:
        return np.arange(n, dtype=int)

    M = _symmetrize(A) if symmetrize else A
    # affinity must be nonnegative; shift then build normalized Laplacian embed
    W = M - M.min()
    np.fill_diagonal(W, 0.0)
    d = W.sum(axis=1)
    d[d == 0] = 1.0
    Dinv = 1.0 / np.sqrt(d)
    L = np.eye(n) - (Dinv[:, None] * W * Dinv[None, :])
    # smallest-r eigenvectors of normalized Laplacian
    vals, vecs = np.linalg.eigh(L)
    embed = vecs[:, :r]
    # row-normalize (Ng-Jordan-Weiss)
    norms = np.linalg.norm(embed, axis=1, keepdims=True)
    norms[norms == 0] = 1.0
    embed = embed / norms
    labels = KMeans(n_clusters=r, n_init=10, random_state=0).fit_predict(embed)
    return _canonical(labels)


# --------------------------------------------------------------------------- #
# quotient lift + symmetric quotient
# --------------------------------------------------------------------------- #
def quotient_lift(A: np.ndarray, partition: np.ndarray):
    """Project ``A`` onto cell-constant matrices.

    Returns ``(A_eq, Q)`` where ``A_eq`` is the n×n lift (block means broadcast
    back to vertices) and ``Q`` is the r×r quotient of cell-pair means.
    """
    n = A.shape[0]
    r = int(partition.max()) + 1 if n > 0 else 0
    # one-hot cell membership
    S = np.zeros((n, r))
    S[np.arange(n), partition] = 1.0
    sizes = S.sum(axis=0)  # cell sizes
    sizes_safe = np.where(sizes == 0, 1.0, sizes)
    # block sums then means
    block_sum = S.T @ A @ S  # r×r
    Q = block_sum / np.outer(sizes_safe, sizes_safe)
    A_eq = S @ Q @ S.T
    return A_eq, Q


def symmetric_quotient(A: np.ndarray, partition: np.ndarray) -> np.ndarray:
    """The symmetric quotient ``Q̃ = D^{1/2} Q D^{-1/2}`` (D = diag cell sizes).

    Eigenvalues of ``Q̃`` are the surviving subset of ``A``'s spectrum under the
    lift. The similarity transform keeps them real-comparable to ``A``'s while
    making the operator symmetric when ``A`` and the partition are.
    """
    _, Q = quotient_lift(A, partition)
    n = A.shape[0]
    r = Q.shape[0]
    sizes = np.array([np.sum(partition == a) for a in range(r)], dtype=float)
    sizes_safe = np.where(sizes == 0, 1.0, sizes)
    Dsqrt = np.sqrt(sizes_safe)
    Qtil = (Dsqrt[:, None] * Q) / Dsqrt[None, :]
    return Qtil


# --------------------------------------------------------------------------- #
# submanifold residuals (place every variant's bet in one coordinate)
# --------------------------------------------------------------------------- #
def lowrank_residual(A: np.ndarray, k: int):
    """Nearest rank-k matrix (truncated SVD) and the residual ``A − A_k``."""
    k = max(0, min(k, min(A.shape)))
    U, s, Vt = np.linalg.svd(A, full_matrices=False)
    if k == 0:
        A_k = np.zeros_like(A)
    else:
        A_k = (U[:, :k] * s[:k]) @ Vt[:k]
    return A_k, A - A_k


def banded_residual(A: np.ndarray, w: int):
    """Nearest banded matrix of half-width ``w`` (keep |i−j|<=w, zero else) and
    the off-band residual. This is the projection onto the banded submanifold."""
    n = A.shape[0]
    idx = np.abs(np.subtract.outer(np.arange(n), np.arange(n)))
    mask = idx <= w
    A_band = A * mask
    return A_band, A - A_band


def fixed_sparse_residual(A: np.ndarray, mask: Optional[np.ndarray] = None, density: float = 0.1):
    """Nearest matrix supported on a *fixed* sparse pattern.

    If ``mask`` is given it is used directly; otherwise we take the ``density``
    fraction of largest-magnitude entries as the (data-chosen but fixed) pattern.
    Returns ``(A_sparse, off_pattern_residual, mask)``.
    """
    if mask is None:
        n = A.size
        k = max(1, int(round(density * n)))
        thresh = np.partition(np.abs(A).ravel(), n - k)[n - k]
        mask = np.abs(A) >= thresh
    A_sparse = A * mask
    return A_sparse, A - A_sparse, mask


def _dof_lowrank(n: int, k: int) -> int:
    return k * (2 * n - k)


def _dof_banded(n: int, w: int) -> int:
    # count of entries with |i-j| <= w in an n x n matrix
    total = 0
    for off in range(-w, w + 1):
        total += n - abs(off)
    return total


def _fixed_strided_mask(n: int, m: int) -> np.ndarray:
    """A *data-independent* fixed sparse pattern of ~m entries: the main diagonal
    plus the lowest sub-diagonals (causal local) until the budget is spent. This
    is a genuinely *fixed* pattern (chosen before seeing A), unlike the
    magnitude-thresholded mask which can cherry-pick A's support."""
    mask = np.zeros((n, n), dtype=bool)
    placed = 0
    off = 0
    while placed < m and off < n:
        for i in range(off, n):
            if placed >= m:
                break
            mask[i, i - off] = True
            placed += 1
        off += 1
    return mask


def matched_submanifold_residuals(A: np.ndarray, budget: int) -> dict:
    """Project ``A`` onto each structured submanifold at a *matched* degree-of-
    freedom budget ``budget`` (number of free real parameters retained), so the
    bets compete fairly. Returns relative-Frobenius residual per manifold.

    Budget is interpreted as a *floor*: each manifold is given at least its
    canonical small instance (low-rank k>=2, banded w>=1, equitable r>=2) so a
    too-stingy budget can't artificially kill one manifold. The fixed-sparse bet
    is reported two ways: ``fixed-sparse`` uses a *data-independent* strided
    pattern (the honest "fixed pattern" of Longformer/BigBird), while
    ``oracle-sparse`` keeps the top-magnitude entries (an upper bound only).

    * low-rank-k:  largest k with k(2n-k) <= budget, min k=2.
    * banded-w:    largest w whose band has <= budget entries, min w=1.
    * fixed-sparse-m: data-independent strided pattern of ~budget entries.
    * equitable-r: largest r with r*r <= budget, min r=2 (spectral partition).
    """
    n = A.shape[0]
    A_norm = float(np.linalg.norm(A))
    if A_norm == 0:
        return {m: 0.0 for m in ("low-rank", "banded", "fixed-sparse",
                                 "oracle-sparse", "equitable")}

    # largest k with dof <= budget, but at least 2 (canonical low-rank)
    k = 1
    while k < n and _dof_lowrank(n, k + 1) <= budget:
        k += 1
    k = min(max(k, 2), n)
    _, Rk = lowrank_residual(A, k)

    # largest w with band-dof <= budget, but at least 1 (canonical band)
    w = 0
    while w < n - 1 and _dof_banded(n, w + 1) <= budget:
        w += 1
    w = max(w, 1)
    _, Rw = banded_residual(A, w)

    # fixed-sparse: data-independent strided pattern of ~budget entries
    m = max(1, min(budget, A.size))
    fmask = _fixed_strided_mask(n, m)
    _, Rs_fixed, _ = fixed_sparse_residual(A, mask=fmask)
    # oracle-sparse: keep budget largest entries (upper bound, can cherry-pick)
    _, Rs_oracle, _ = fixed_sparse_residual(A, density=m / A.size)

    # equitable-r: largest r with r^2 <= budget, at least 2
    r = 1
    while (r + 1) ** 2 <= budget and r + 1 <= n:
        r += 1
    r = min(max(r, 2), n)
    part = spectral_partition(A, r)
    A_eq, _ = quotient_lift(A, part)
    Req = A - A_eq

    return {
        "low-rank": float(np.linalg.norm(Rk) / A_norm),
        "banded": float(np.linalg.norm(Rw) / A_norm),
        "fixed-sparse": float(np.linalg.norm(Rs_fixed) / A_norm),
        "oracle-sparse": float(np.linalg.norm(Rs_oracle) / A_norm),
        "equitable": float(np.linalg.norm(Req) / A_norm),
        "_budget": budget, "_k": k, "_w": w, "_m": m, "_r": r,
    }


# --------------------------------------------------------------------------- #
# the headline entry point
# --------------------------------------------------------------------------- #
def decompose(
    A: np.ndarray,
    r_sweep: list[int],
    *,
    k_sweep: Optional[list[int]] = None,
    w_sweep: Optional[list[int]] = None,
    wl_bins: int = 16,
) -> dict:
    """Equitable decomposition of attention matrix ``A`` over a cell-count sweep.

    Parameters
    ----------
    A : (n, n) array — a single attention matrix (one head, one layer).
    r_sweep : list of target cell counts. For each ``r`` we build a spectral
        soft-equitable partition; the special sentinel ``r == -1`` (or any ``r``
        ``>= n``) uses the *exact* 1-WL equitable partition instead.
    k_sweep, w_sweep : cell counts for the low-rank / banded submanifold sweeps.
        Default to a geometric-ish spread.

    Returns
    -------
    dict with the stable API keys (all sub-dicts keyed by the sweep value):
        partition[r], A_eq[r], R[r], R_svals[r], surviving_spectrum[r],
        lowrank_resid[k], banded_resid[w]
    Plus diagnostics: ``A_spectrum``, ``A_norm``, ``defect_eq[r]``,
    ``rank_R[r]``, ``surviving_fraction[r]``, ``n_cells[r]``,
    ``lowrank_resid_norm[k]``, ``banded_resid_norm[w]``,
    ``sparse_resid``/``sparse_resid_norm`` (off-pattern mass at density 0.1),
    and the WL exact partition under key ``"wl"`` inside the per-r dicts.
    """
    A = np.asarray(A, dtype=float)
    n = A.shape[0]
    assert A.ndim == 2 and A.shape[0] == A.shape[1], "A must be square"

    A_norm = float(np.linalg.norm(A))
    A_spectrum = np.linalg.eigvals(A)
    A_spectrum = A_spectrum[np.argsort(-np.abs(A_spectrum))]

    if k_sweep is None:
        ks = sorted({1, 2, 4, 8, max(1, n // 4), max(1, n // 2)})
        k_sweep = [k for k in ks if k <= n]
    if w_sweep is None:
        ws = sorted({0, 1, 2, 4, 8, max(1, n // 4)})
        w_sweep = [w for w in ws if w < n]

    out: dict = {
        "n": n,
        "A_norm": A_norm,
        "A_spectrum": A_spectrum,
        "partition": {},
        "A_eq": {},
        "R": {},
        "R_svals": {},
        "surviving_spectrum": {},
        "defect_eq": {},
        "rank_R": {},
        "surviving_fraction": {},
        "n_cells": {},
        "lowrank_resid": {},
        "lowrank_resid_norm": {},
        "banded_resid": {},
        "banded_resid_norm": {},
    }

    # exact WL equitable partition (reported under key "wl")
    wl_part = equitable_partition_wl(A, n_bins=wl_bins)
    r_targets = list(r_sweep)

    for r in r_targets:
        if r == -1 or r >= n:
            part = wl_part
            key = "wl" if r == -1 else r
        else:
            part = spectral_partition(A, r)
            key = r
        A_eq, _ = quotient_lift(A, part)
        R = A - A_eq
        svals = np.linalg.svd(R, compute_uv=False)
        Qtil = symmetric_quotient(A, part)
        surv = np.linalg.eigvals(Qtil)
        surv = surv[np.argsort(-np.abs(surv))]

        out["partition"][key] = part
        out["A_eq"][key] = A_eq
        out["R"][key] = R
        out["R_svals"][key] = svals
        out["surviving_spectrum"][key] = surv
        out["defect_eq"][key] = float(np.linalg.norm(R) / A_norm) if A_norm > 0 else 0.0
        out["rank_R"][key] = rank_eps(R)
        # fraction of A's spectral mass captured by the surviving subset
        denom = float(np.sum(np.abs(A_spectrum)))
        out["surviving_fraction"][key] = (
            float(np.sum(np.abs(surv)) / denom) if denom > 0 else 0.0
        )
        out["n_cells"][key] = int(part.max()) + 1 if n > 0 else 0

    # always include the exact WL partition's decomposition under "wl"
    if "wl" not in out["partition"]:
        A_eq, _ = quotient_lift(A, wl_part)
        R = A - A_eq
        out["partition"]["wl"] = wl_part
        out["A_eq"]["wl"] = A_eq
        out["R"]["wl"] = R
        out["R_svals"]["wl"] = np.linalg.svd(R, compute_uv=False)
        Qtil = symmetric_quotient(A, wl_part)
        surv = np.linalg.eigvals(Qtil)
        out["surviving_spectrum"]["wl"] = surv[np.argsort(-np.abs(surv))]
        out["defect_eq"]["wl"] = float(np.linalg.norm(R) / A_norm) if A_norm > 0 else 0.0
        out["rank_R"]["wl"] = rank_eps(R)
        out["n_cells"]["wl"] = int(wl_part.max()) + 1 if n > 0 else 0

    # submanifold residuals
    for k in k_sweep:
        _, Rk = lowrank_residual(A, k)
        out["lowrank_resid"][k] = Rk
        out["lowrank_resid_norm"][k] = (
            float(np.linalg.norm(Rk) / A_norm) if A_norm > 0 else 0.0
        )
    for w in w_sweep:
        _, Rw = banded_residual(A, w)
        out["banded_resid"][w] = Rw
        out["banded_resid_norm"][w] = (
            float(np.linalg.norm(Rw) / A_norm) if A_norm > 0 else 0.0
        )

    A_sparse, R_sparse, mask = fixed_sparse_residual(A, density=0.1)
    out["sparse_resid"] = R_sparse
    out["sparse_mask"] = mask
    out["sparse_resid_norm"] = (
        float(np.linalg.norm(R_sparse) / A_norm) if A_norm > 0 else 0.0
    )

    return out
