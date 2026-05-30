"""
Recovery / modeling techniques for the residual R = A - A_eq.

Each function returns a dict of (cost_param -> reconstruction_error) plus any
diagnostics.  Error is relative Frobenius ||R - R_hat||_F / ||R||_F.

Techniques:
  1. svd_truncation      : exact low-rank SVD; singular-value decay & error vs rank.
  2. robust_pca          : L+S (sparse+low-rank) via inexact ALM (Scatterbrain template).
  3. soft_threshold      : pure sparse recovery (entrywise soft-threshold) vs kept-mass.
  4. krylov_compress     : does R's *action* live in a small Krylov subspace?
  5. random_feature      : kernel/random-feature (Performer-style) approx of R's action.
  6. partition_tower     : recurse equitable refinement on R (finer partition residual).
  7. polynomial_model    : low-order polynomial of A_eq / position approximating R.
  8. steered_noise       : covariance-matched random sketch eta, E[eta eta^T] ~ R R^T.
"""
import numpy as np


def relerr(R, Rhat):
    d = np.linalg.norm(R)
    return np.linalg.norm(R - Rhat) / (d if d > 0 else 1.0)


# ---------- 1. exact low-rank SVD ----------
def svd_truncation(R, ranks=None):
    U, s, Vt = np.linalg.svd(R, full_matrices=False)
    n = len(s)
    if ranks is None:
        ranks = sorted(set([1, 2, 3, 4, 6, 8, 12, 16, 24, 32, n // 2, n - 1, n]))
        ranks = [k for k in ranks if 1 <= k <= n]
    errs = {}
    for k in ranks:
        Rhat = (U[:, :k] * s[:k]) @ Vt[:k]
        errs[k] = relerr(R, Rhat)
    # effective rank metrics
    energy = s ** 2
    cum = np.cumsum(energy) / energy.sum()
    rank90 = int(np.searchsorted(cum, 0.90) + 1)
    rank99 = int(np.searchsorted(cum, 0.99) + 1)
    p = energy / energy.sum()
    eff_rank = float(np.exp(-(p * np.log(p + 1e-300)).sum()))  # entropy / stable rank
    stable_rank = float(energy.sum() / (energy.max() + 1e-300))
    return dict(svals=s, errs=errs, rank90=rank90, rank99=rank99,
                eff_rank=eff_rank, stable_rank=stable_rank)


# ---------- 2. Robust PCA (L+S) via inexact ALM ----------
def robust_pca(R, lam=None, mu=None, max_iter=200, tol=1e-6):
    """Decompose R = L (low-rank) + S (sparse).  Classic IALM."""
    n1, n2 = R.shape
    norm_fro = np.linalg.norm(R)
    if lam is None:
        lam = 1.0 / np.sqrt(max(n1, n2))
    norm_two = np.linalg.norm(R, 2)
    norm_inf = np.abs(R).max() / lam
    dual_norm = max(norm_two, norm_inf)
    Y = R / (dual_norm if dual_norm > 0 else 1.0)
    if mu is None:
        mu = 1.25 / (norm_two if norm_two > 0 else 1.0)
    mu_bar = mu * 1e7
    rho = 1.5
    L = np.zeros_like(R)
    S = np.zeros_like(R)
    for it in range(max_iter):
        # update L via singular value thresholding
        U, sig, Vt = np.linalg.svd(R - S + Y / mu, full_matrices=False)
        sig_t = np.maximum(sig - 1.0 / mu, 0)
        rankL = int((sig_t > 0).sum())
        L = (U[:, :rankL] * sig_t[:rankL]) @ Vt[:rankL]
        # update S via soft threshold
        T = R - L + Y / mu
        S = np.sign(T) * np.maximum(np.abs(T) - lam / mu, 0)
        Z = R - L - S
        Y = Y + mu * Z
        mu = min(mu * rho, mu_bar)
        if np.linalg.norm(Z) / (norm_fro if norm_fro > 0 else 1) < tol:
            break
    sparsity = float((np.abs(S) > 1e-9).mean())
    rankL = int(np.linalg.matrix_rank(L, tol=1e-6))
    err = relerr(R, L + S)
    return dict(L=L, S=S, rankL=rankL, sparsity=sparsity, err=err,
                Lnorm=np.linalg.norm(L), Snorm=np.linalg.norm(S))


# ---------- 3. pure sparse (soft-threshold) ----------
def soft_threshold(R, fracs=None):
    """Keep the top-fraction of entries by magnitude; error vs kept fraction."""
    if fracs is None:
        fracs = [0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.5]
    mag = np.abs(R).reshape(-1)
    order = np.sort(mag)[::-1]
    errs = {}
    total = R.size
    for f in fracs:
        k = max(1, int(f * total))
        thr = order[k - 1]
        Rhat = R * (np.abs(R) >= thr)
        errs[f] = relerr(R, Rhat)
    return dict(errs=errs)


# ---------- 4. Krylov compressibility of R's action ----------
def krylov_compress(R, n_probe=8, dims=None, seed=0):
    """For random probe vectors b, how well does the Krylov subspace
    K_m(R, b) = span{b, Rb, ..., R^{m-1} b} capture R b (i.e. R^{deg} b)?
    We measure: project the *true* action of R on random vectors onto the
    block-Krylov subspace of growing dimension m and report relative error of
    reconstructing R applied to a fresh random matrix."""
    n = R.shape[0]
    rng = np.random.default_rng(seed)
    if dims is None:
        dims = [1, 2, 4, 8, 16, min(32, n - 1)]
        dims = sorted(set(d for d in dims if 1 <= d < n))
    # build block Krylov basis from probe block B0
    B0 = rng.normal(size=(n, n_probe))
    Q, _ = np.linalg.qr(B0)
    basis = [Q]
    cur = Q
    for _ in range(max(dims)):
        cur = R @ cur
        # orthogonalize against existing
        for Qb in basis:
            cur = cur - Qb @ (Qb.T @ cur)
        q, _ = np.linalg.qr(cur)
        basis.append(q)
    # test action on fresh random vectors
    Xtest = rng.normal(size=(n, 16))
    Y = R @ Xtest
    errs = {}
    for m in dims:
        # subspace spanned by first m blocks
        Qm = np.concatenate(basis[:m], axis=1)
        Qm, _ = np.linalg.qr(Qm)
        Yhat = Qm @ (Qm.T @ Y)  # project true action into Krylov subspace
        errs[m * n_probe] = relerr(Y, Yhat)
    return dict(errs=errs, note="x-axis = krylov subspace dim (blocks*probe)")


# ---------- 5. random-feature / kernel approx of R's action ----------
def random_feature(R, feats=None, seed=0):
    """Approximate R (as a linear map) by a random low-rank sketch:
    R ~ (R Omega)(Omega^T R^T R Omega)^+ (R Omega)^T ... we use the simpler
    randomized range finder: Rhat = Q Q^T R, Q = orth(R Omega), and report
    error vs number of features (sketch width).  This is the kernel/random-
    projection analogue (Performer uses phi(Q)phi(K)^T; here phi is random)."""
    n = R.shape[0]
    rng = np.random.default_rng(seed)
    if feats is None:
        feats = [1, 2, 4, 8, 16, 32, min(64, n)]
        feats = sorted(set(f for f in feats if 1 <= f <= n))
    errs = {}
    for w in feats:
        Omega = rng.normal(size=(n, w))
        Y = R @ Omega
        Q, _ = np.linalg.qr(Y)
        Rhat = Q @ (Q.T @ R)   # randomized SVD range approximation
        errs[w] = relerr(R, Rhat)
    return dict(errs=errs)


# ---------- 6. partition tower: recurse equitable refinement on R ----------
def partition_tower(A, depth=3, r_schedule=(2, 4, 8, 16)):
    """Recursively peel off equitable bases.  Level 0: A_eq(r0); residual R0.
    Level 1: treat R0 as a matrix, find ITS nearest equitable partition, peel
    A_eq1; residual R1.  etc.  Does the residual itself have equitable structure
    that recursion captures?  Report ||R_k||/||A|| per level."""
    from equitable import decompose_at_r
    cur = A.copy()
    base_norm = np.linalg.norm(A)
    levels = []
    accum_base = np.zeros_like(A)
    for k in range(depth):
        r = r_schedule[min(k, len(r_schedule) - 1)]
        d = decompose_at_r(cur, r)
        accum_base = accum_base + d['A_eq']
        cur = d['R']
        levels.append(dict(level=k, r=d['r'],
                           res_norm=np.linalg.norm(cur) / base_norm,
                           rankR=int(np.linalg.matrix_rank(cur, tol=1e-9))))
    return dict(levels=levels, final_residual=cur,
                total_base=accum_base,
                final_relerr=np.linalg.norm(cur) / base_norm)


# ---------- 7. low-order polynomial model of R from A_eq ----------
def polynomial_model(A_eq, R, degree=3):
    """Fit R entrywise as a polynomial in features derived from A_eq and position:
    can a slow, expressive *closed-form* model of the base reproduce R?
    Features: A_eq, (A_eq^2), row/col index normalized, |i-j|.  We solve least
    squares for coefficients (this is a global model, cost irrelevant)."""
    n = A_eq.shape[0]
    ii, jj = np.meshgrid(np.arange(n), np.arange(n), indexing="ij")
    i = ii.reshape(-1) / n
    j = jj.reshape(-1) / n
    dist = np.abs(ii - jj).reshape(-1) / n
    ae = A_eq.reshape(-1)
    Apow = (A_eq @ A_eq).reshape(-1)
    feats = [np.ones_like(ae), ae, ae ** 2, ae ** 3, Apow, i, j, dist, i * j, dist ** 2]
    feats = feats[: 1 + degree * 3]
    X = np.stack(feats, axis=1)
    y = R.reshape(-1)
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    yhat = X @ coef
    Rhat = yhat.reshape(n, n)
    return dict(err=relerr(R, Rhat), coef=coef, Rhat=Rhat, n_feats=X.shape[1])


# ---------- 8. steered noise: covariance-matched random sketch ----------
def steered_noise(R, ranks=None, n_trials=20, seed=0):
    """Generate random eta with E[eta eta^T] ~ R R^T using the rank-k eigenbasis
    of the row-covariance of R, and measure how well a SINGLE steered draw (and
    the best-of-n) reconstructs R vs rank k.  This tests the 'steered correction'
    idea: can a cheap covariance-matched noise STAND IN for R?

    Crucially we distinguish:
      - covariance match (can noise reproduce R's second-order statistics?) -> always yes-ish
      - actual reconstruction (does a draw equal R?) -> the real test; if R is
        signal not noise, a covariance-matched draw will NOT reconstruct it.
    """
    n = R.shape[0]
    rng = np.random.default_rng(seed)
    # row covariance C = R R^T (n x n); eigendecompose
    C = R @ R.T
    w, V = np.linalg.eigh(C)
    w = np.clip(w[::-1], 0, None)
    V = V[:, ::-1]
    if ranks is None:
        ranks = [1, 2, 4, 8, 16, min(32, n)]
        ranks = sorted(set(k for k in ranks if 1 <= k <= n))
    out = {}
    Rn = np.linalg.norm(R)
    for k in ranks:
        # sqrt of rank-k covariance
        sq = V[:, :k] * np.sqrt(w[:k])
        best = np.inf
        mean = 0.0
        for _ in range(n_trials):
            G = rng.normal(size=(k, n))
            eta = sq @ G  # E[eta eta^T] = V_k diag(w_k) V_k^T = rank-k approx of RR^T
            # align column scale to R (best the noise can do)
            e = relerr(R, eta)
            best = min(best, e)
            mean += e
        mean /= n_trials
        # also: covariance-match quality (2nd order) at this rank
        cov_match = np.linalg.norm(C - (V[:, :k] * w[:k]) @ V[:, :k].T) / np.linalg.norm(C)
        out[k] = dict(best_recon=best, mean_recon=mean, cov_residual=cov_match)
    return dict(per_rank=out, Rnorm=Rn)
