"""A structured-walk dictionary D of n x n operators.

Every atom is an interpretable, NAMED operator that matches the shape of a
(causal) attention matrix: real, row-normalized to be row-stochastic on the
causal-allowed support (lower-triangular, including the diagonal). We build:

  * identity            -- attend to self
  * uniform             -- attend uniformly over the causal prefix (the "average
                           over everything seen so far" operator)
  * shift-k (prev-k)    -- attend to the token k positions back (k=1..K). This is
                           the induction / previous-token primitive. shift-1 is
                           the classic "previous token head".
  * cell-uniform(part)  -- block-uniform averaging over a coarse partition of
                           positions (a few partitions: halves, thirds, quarters,
                           even/odd parity).
  * path-diffusion(tau) -- rownorm(exp(tau * (-L_path))) for the path graph
                           Laplacian, several tau. The thermal walk on a line.
  * cycle-diffusion(tau)-- rownorm(exp(tau * (-L_cycle))) on the cycle graph.

All atoms are causal-masked (lower-triangular kept) and then row-normalized so
that, like A, every row sums to 1 over its causal support. We store them as a
flat (n_atoms, n*n) design matrix plus a list of names.
"""
from __future__ import annotations

import numpy as np
from scipy.linalg import expm


def _causal_mask(n: int) -> np.ndarray:
    return np.tril(np.ones((n, n)))


def _rownorm_causal(M: np.ndarray) -> np.ndarray:
    """Causal-mask (keep lower triangle) then row-normalize to sum 1 per row."""
    n = M.shape[0]
    M = np.asarray(M, dtype=float).copy()
    M = M * _causal_mask(n)
    M = np.maximum(M, 0.0)
    rs = M.sum(axis=1, keepdims=True)
    rs[rs == 0] = 1.0
    return M / rs


def identity_atom(n: int) -> np.ndarray:
    return _rownorm_causal(np.eye(n))


def uniform_atom(n: int) -> np.ndarray:
    """Uniform over the causal prefix: row i -> 1/(i+1) on cols 0..i."""
    return _rownorm_causal(np.ones((n, n)))


def shift_atom(n: int, k: int) -> np.ndarray:
    """Attend to the token k positions back. Row i -> position i-k (if >=0).

    The induction primitive. For rows with i<k there is no valid target, so we
    fall back to self (diagonal) so the row is still stochastic. shift-0 == id.
    """
    M = np.zeros((n, n))
    for i in range(n):
        j = i - k
        if j >= 0:
            M[i, j] = 1.0
        else:
            M[i, i] = 1.0  # fallback: self
    return _rownorm_causal(M)


def sink_atom(n: int, col: int = 0) -> np.ndarray:
    """Attention-sink operator: every row attends entirely to a fixed column
    (default col 0 = the BOS token). Real LLM heads dump a large constant share
    of attention onto BOS; this is a CONSTANT operator, not a walk. We include it
    NAMED so the walk story is tested on the residual AFTER the sink is removed.
    """
    M = np.zeros((n, n))
    M[:, col] = 1.0
    # diagonal so row 0 (which can only see col 0 anyway) stays valid
    return _rownorm_causal(M)


def cell_uniform_atom(n: int, part: np.ndarray) -> np.ndarray:
    """Block-uniform averaging: row i attends uniformly to all causal-allowed
    positions in the same partition cell as i."""
    M = np.zeros((n, n))
    for i in range(n):
        same = (part == part[i])
        same[i + 1:] = False  # causal
        M[i, same] = 1.0
    return _rownorm_causal(M)


def _path_laplacian(n: int) -> np.ndarray:
    A = np.zeros((n, n))
    for i in range(n - 1):
        A[i, i + 1] = 1.0
        A[i + 1, i] = 1.0
    D = np.diag(A.sum(axis=1))
    return D - A


def _cycle_laplacian(n: int) -> np.ndarray:
    A = np.zeros((n, n))
    for i in range(n):
        A[i, (i + 1) % n] = 1.0
        A[(i + 1) % n, i] = 1.0
    D = np.diag(A.sum(axis=1))
    return D - A


def diffusion_atom(L: np.ndarray, tau: float) -> np.ndarray:
    """rownorm(exp(tau*(-L))) restricted to the causal triangle."""
    H = expm(-tau * L)
    return _rownorm_causal(H)


# partitions of positions 0..n-1 ---------------------------------------------
def _partitions(n: int) -> dict[str, np.ndarray]:
    idx = np.arange(n)
    return {
        "halves": (idx >= n // 2).astype(int),
        "thirds": np.minimum(idx * 3 // n, 2),
        "quarters": np.minimum(idx * 4 // n, 3),
        "parity": idx % 2,
        "blocks8": np.minimum(idx * 8 // n, 7),
    }


def build_dictionary(n: int,
                     shift_ks=(1, 2, 3, 4, 5, 8),
                     path_taus=(0.5, 1.0, 2.0, 4.0, 8.0),
                     cycle_taus=(1.0, 4.0)) -> tuple[np.ndarray, list[str]]:
    """Return (D, names) where D has shape (n_atoms, n*n): each row a flattened
    NAMED structured-walk operator."""
    atoms: list[np.ndarray] = []
    names: list[str] = []

    def add(name, M):
        atoms.append(M.ravel())
        names.append(name)

    add("identity", identity_atom(n))
    add("uniform", uniform_atom(n))
    add("bos-sink", sink_atom(n, 0))
    for k in shift_ks:
        add(f"shift-{k}", shift_atom(n, k))
    for pname, part in _partitions(n).items():
        add(f"cell-{pname}", cell_uniform_atom(n, part))
    Lp = _path_laplacian(n)
    for tau in path_taus:
        add(f"path-diff-tau{tau}", diffusion_atom(Lp, tau))
    Lc = _cycle_laplacian(n)
    for tau in cycle_taus:
        add(f"cycle-diff-tau{tau}", diffusion_atom(Lc, tau))

    D = np.stack(atoms, axis=0)  # (n_atoms, n*n)
    return D, names


# semantic class of each atom (for the cross-reference table) -----------------
def atom_class(name: str) -> str:
    if name.startswith("shift-") or name == "induction-shift":
        return "shift"
    if name.startswith("cell-"):
        return "cell-uniform"
    if name.startswith("path-diff") or name.startswith("cycle-diff"):
        return "diffusion"
    if name in ("identity", "uniform", "bos-sink"):
        return name
    return "other"
