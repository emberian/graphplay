"""Sparse-code a head's attention matrix A against the walk dictionary D.

Two coders:
  * OMP (orthogonal matching pursuit): greedily pick atoms, refit by least
    squares each step. Gives the canonical "reconstruction error vs # atoms"
    sparsity curve and the ordered list of chosen named atoms.
  * NNLS-LASSO: non-negative least squares (attention is nonnegative; a convex
    combination of row-stochastic atoms is itself row-stochastic-ish), as a
    sanity cross-check on which atoms carry weight.

Targets are flattened attention matrices a = A.ravel() (length n*n). We measure
relative Frobenius reconstruction error ||a - D^T c|| / ||a||.
"""
from __future__ import annotations

import numpy as np
from scipy.optimize import nnls


def _relerr(a, recon):
    na = np.linalg.norm(a)
    return float(np.linalg.norm(a - recon) / na) if na > 0 else 0.0


def omp(a: np.ndarray, D: np.ndarray, max_atoms: int):
    """Orthogonal matching pursuit of target a against dictionary rows of D.

    D : (n_atoms, dim). a : (dim,). Returns dict with:
      order   -- list of atom indices chosen, in order
      errors  -- relerr after using 1,2,...,len(order) atoms (errors[0] = err
                 with 0 atoms = 1.0 baseline is prepended)
      coef    -- final coefficient vector over all atoms (zeros off support)
    """
    Dn = D  # (m, dim)
    m = Dn.shape[0]
    residual = a.copy()
    chosen: list[int] = []
    errors = [_relerr(a, np.zeros_like(a))]  # 0 atoms -> err 1.0
    coef = np.zeros(m)
    # precompute column norms for correlation scoring
    norms = np.linalg.norm(Dn, axis=1)
    norms[norms == 0] = 1.0
    for _ in range(min(max_atoms, m)):
        corr = np.abs(Dn @ residual) / norms
        corr[chosen] = -np.inf
        j = int(np.argmax(corr))
        if not np.isfinite(corr[j]):
            break
        chosen.append(j)
        # least squares refit on chosen support: solve min ||a - Phi^T c||
        Phi = Dn[chosen].T  # (dim, k)
        c, *_ = np.linalg.lstsq(Phi, a, rcond=None)
        recon = Phi @ c
        residual = a - recon
        errors.append(_relerr(a, recon))
        coef[:] = 0.0
        coef[chosen] = c
    return {"order": chosen, "errors": errors, "coef": coef}


def nnls_code(a: np.ndarray, D: np.ndarray):
    """Non-negative least squares fit of a against all atoms. Returns coef and
    relerr. Sparsity emerges from NNLS naturally zeroing many atoms."""
    Phi = D.T  # (dim, m)
    c, _ = nnls(Phi, a, maxiter=10 * D.shape[0])
    recon = Phi @ c
    return {"coef": c, "relerr": _relerr(a, recon),
            "nnz": int(np.sum(c > 1e-6))}


def atoms_to_reach(errors: list[float], thresh: float) -> int:
    """Smallest number of atoms whose OMP reconstruction error <= thresh.
    errors[k] is the error after using k atoms. Returns a large sentinel if
    never reached within the computed budget."""
    for k, e in enumerate(errors):
        if e <= thresh:
            return k
    return len(errors)  # not reached within budget
