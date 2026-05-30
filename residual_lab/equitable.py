"""
Equitable decomposition of an attention matrix via 1-WL color refinement.

Given a (possibly row-stochastic) attention matrix A (n x n), we find an
equitable partition P of the n tokens, and form A_eq = the quotient *lift*:
the best matrix that is constant on each (cell_i, cell_j) block in the sense
of equitable averaging.  R = A - A_eq is the residual.

The base A_eq is cheap to apply: O(n * r) where r = number of cells, because it
is determined by an r x r quotient matrix B (block averages) lifted back to n x n.

1-WL color refinement on a *weighted* matrix:
  - Start: all nodes one color (or seeded by row/col degree).
  - Iterate: a node's new color = (old color, multiset of {(neighbor color, quantized
    weight)}).  We quantize edge weights into bins so WL on a weighted graph is
    well-defined and produces a genuinely equitable (in the quantized sense) partition.
  - Converge when the number of colors stops growing.

Because exact equitability on continuous weights gives the trivial all-singletons
partition, we expose a `tol`/`n_bins` knob: coarser quantization -> coarser partition
-> larger residual R.  This knob *is* the experiment ("how coarse is the base").
"""
import numpy as np


def _quantize(W, n_bins):
    """Quantize a weight matrix into integer bins by rank (quantile binning)."""
    flat = W.reshape(-1)
    # quantile edges so bins are populated
    qs = np.quantile(flat, np.linspace(0, 1, n_bins + 1))
    qs = np.unique(qs)
    if len(qs) < 2:
        return np.zeros_like(W, dtype=np.int64)
    binned = np.digitize(W, qs[1:-1], right=False)
    return binned.astype(np.int64)


def wl_refine(A, n_bins=8, max_iter=50, seed_degree=True, symmetrize=True):
    """1-WL color refinement on weighted matrix A. Returns integer color vector (n,)."""
    n = A.shape[0]
    M = 0.5 * (A + A.T) if symmetrize else A
    Wb = _quantize(M, n_bins)  # n x n int bins

    if seed_degree:
        # seed colors by quantized row-degree so initial colors carry weight info
        deg = M.sum(axis=1)
        colors = _quantize(deg.reshape(-1, 1), min(n_bins, n)).reshape(-1)
        colors = colors.astype(np.int64)
    else:
        colors = np.zeros(n, dtype=np.int64)

    for _ in range(max_iter):
        # signature per node: (own color, sorted tuple of (neighbor color, weight bin))
        sigs = []
        for i in range(n):
            nbr = tuple(sorted((int(colors[j]), int(Wb[i, j])) for j in range(n)))
            sigs.append((int(colors[i]), nbr))
        # relabel signatures -> compact ints
        uniq = {}
        new_colors = np.empty(n, dtype=np.int64)
        for i, s in enumerate(sigs):
            if s not in uniq:
                uniq[s] = len(uniq)
            new_colors[i] = uniq[s]
        if len(set(new_colors.tolist())) == len(set(colors.tolist())):
            colors = new_colors
            break
        colors = new_colors
    return colors


def equitable_quotient_lift(A, colors):
    """
    Given a partition `colors` (n,), build A_eq by replacing each block (c,d) with
    its mean over A[i in cell c, j in cell d].  This is the L2-optimal block-constant
    approximation of A subject to the partition -> the equitable base.

    Returns A_eq (n x n), and the quotient matrix B (r x r) of block means.
    """
    n = A.shape[0]
    labels = np.unique(colors)
    r = len(labels)
    idx = {c: np.where(colors == c)[0] for c in labels}
    B = np.zeros((r, r))
    A_eq = np.zeros_like(A, dtype=float)
    for a, c in enumerate(labels):
        ic = idx[c]
        for b, d in enumerate(labels):
            jd = idx[d]
            block = A[np.ix_(ic, jd)]
            m = block.mean()
            B[a, b] = m
            A_eq[np.ix_(ic, jd)] = m
    return A_eq, B, labels


def equitable_decompose(A, n_bins=8, **kw):
    """Full pipeline: A -> (colors, A_eq, R, B)."""
    colors = wl_refine(A, n_bins=n_bins, **kw)
    A_eq, B, labels = equitable_quotient_lift(A, colors)
    R = A - A_eq
    return dict(colors=colors, A_eq=A_eq, R=R, B=B, labels=labels,
                r=len(labels), n=A.shape[0])


# ---------------------------------------------------------------------------
# Coarsening to a TARGET number of cells r.
#
# Exact 1-WL on continuous weights gives the trivial all-singletons partition,
# so R=0 trivially and the experiment is vacuous.  The honest experiment the
# program (paper/explanatory_program.md §2) actually asks for is a *sweep of
# cell-counts r*: at each budget r, find the best equitable-ish partition and
# measure the residual.  We obtain a partition with exactly r cells by:
#   1. building a per-token feature (its WL-style row/col profile of A), then
#   2. agglomerative clustering of tokens into r groups, then
#   3. the L2-optimal block-constant lift on that partition.
# This is the operational "nearest equitable partition at cell-count r".
# (Spectral co-clustering and degree-profile clustering give the same story;
# agglomerative on the row+col profile is the most faithful to WL's "a node is
# defined by the multiset of its weighted neighborhood".)
# ---------------------------------------------------------------------------

def _wl_features(A, symmetrize=True):
    """Per-token feature = concatenation of its row and column of the symmetrized
    matrix, sorted (permutation-invariant WL-style signature) plus raw row/col.
    We use raw row+col so the partition respects positional structure too."""
    M = 0.5 * (A + A.T) if symmetrize else A
    # raw row and column (captures who-i-attend-to and who-attends-to-me)
    feat = np.concatenate([M, M.T], axis=1)
    return feat


def partition_at_r(A, r, method="agglomerative"):
    """Return a color vector with (at most) r cells, approximating the nearest
    equitable partition at budget r."""
    from sklearn.cluster import AgglomerativeClustering, KMeans
    n = A.shape[0]
    r = int(min(max(r, 1), n))
    if r == 1:
        return np.zeros(n, dtype=np.int64)
    if r >= n:
        return np.arange(n, dtype=np.int64)
    F = _wl_features(A)
    if method == "agglomerative":
        cl = AgglomerativeClustering(n_clusters=r, linkage="ward")
    else:
        cl = KMeans(n_clusters=r, n_init=4, random_state=0)
    colors = cl.fit_predict(F).astype(np.int64)
    return colors


def decompose_at_r(A, r, method="agglomerative"):
    colors = partition_at_r(A, r, method=method)
    A_eq, B, labels = equitable_quotient_lift(A, colors)
    R = A - A_eq
    return dict(colors=colors, A_eq=A_eq, R=R, B=B, labels=labels,
                r=len(labels), n=A.shape[0])
