"""graphplay_probe — the equitable-decomposition instrument.

The headline entry point is :func:`decompose`, which takes an attention matrix
``A`` and a sweep of cell-counts ``r`` and returns, per ``r``, the nearest
equitable partition, the quotient lift ``A_eq(r)``, the residual ``R(r)``, its
singular-value spectrum, and the surviving-eigenvalue subset. It also returns
submanifold residuals (nearest low-rank-k, nearest banded-w, nearest
fixed-sparse) so every attention-variant's structural "bet" lands in one
coordinate.

API contract (stable — other agents code against this):

    decompose(A: np.ndarray, r_sweep: list[int]) -> dict
        with keys:
            partition[r], A_eq[r], R[r], R_svals[r], surviving_spectrum[r],
            lowrank_resid[k], banded_resid[w]
"""

from .probe import (
    decompose,
    equitable_partition_wl,
    spectral_partition,
    quotient_lift,
    symmetric_quotient,
    lowrank_residual,
    banded_residual,
    fixed_sparse_residual,
    matched_submanifold_residuals,
    rank_eps,
)

__all__ = [
    "decompose",
    "equitable_partition_wl",
    "spectral_partition",
    "quotient_lift",
    "symmetric_quotient",
    "lowrank_residual",
    "banded_residual",
    "fixed_sparse_residual",
    "matched_submanifold_residuals",
    "rank_eps",
]
