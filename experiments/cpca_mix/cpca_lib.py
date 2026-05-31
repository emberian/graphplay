"""
cpca_lib.py — operator-level mixing machinery for the CPCA-MIX experiment.

We measure the continuous-time quantum walk (CTQW) uniform-mixing time of a
Hermitian propagation host H under three phasings:

  H_0    : unsigned real-symmetric host
  H_chi  : H_0 with a CROSS-CONSTANT U(1) edge signing sigma(i,j)=e^{i theta(cell i, cell j)}
  H_free : H_0 with FREE per-pair random phases (control)

The CTQW propagator is  U(t) = exp(-i t H).
The instantaneous mixing matrix is  M(t)_{uv} = |U(t)_{uv}|^2  (a doubly-stochastic
matrix, by unitarity of U).  Uniform mixing at time t means M(t)_{uv} = 1/n for all
u,v.  We track the uniform-mixing distance

  D(t) = max_{u,v} | M(t)_{uv} - 1/n |

and define the uniform-mixing time tau_mix(eps) = first t in [0, T] with D(t) <= eps.

This mirrors Graphplay/Mixing.lean: WeightedGraph.mixing t u v = |evolve t u v|^2,
IsUniformMixing := every entry = 1/n.  The chiral K_4 reference (Chiral.lean,
unitaryHammingChiralK4_uniformMixing) gives D = 0 exactly at tau = pi/(3 sqrt 3).
"""

import numpy as np
from scipy.linalg import expm


# ----------------------------------------------------------------------------
# Hosts
# ----------------------------------------------------------------------------

def host_complete(n):
    """Unsigned real-symmetric complete graph K_n adjacency (host H_0)."""
    H = np.ones((n, n), dtype=complex) - np.eye(n, dtype=complex)
    return H


def host_band(n, bandwidth):
    """Circulant banded relative-position host (RoPE/Toeplitz stand-in).

    H_0[i,j] = 1 if 0 < min(|i-j|, n-|i-j|) <= bandwidth else 0  (real symmetric,
    loopless).  This is a circulant graph; its position-cell partition (cells by
    i mod q) is equitable, which is what makes cross-constant signing descend.
    """
    H = np.zeros((n, n), dtype=complex)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            d = abs(i - j)
            d = min(d, n - d)
            if d <= bandwidth:
                H[i, j] = 1.0
    return H


# ----------------------------------------------------------------------------
# Signings
# ----------------------------------------------------------------------------

def levine_k4_signing():
    """The exact Levine K_4 chiral signing (Chiral.lean chiralK4Matrix).

    A(K_4^sigma) entries are +/- i; spectrum is +/- sqrt(3) (each mult 2),
    giving B^2 = 3 I and uniform mixing at tau = pi/(3 sqrt 3).
    """
    I = 1j
    return np.array([
        [0,  -I, -I, -I],
        [I,   0, -I,  I],
        [I,   I,  0, -I],
        [I,  -I,  I,  0],
    ], dtype=complex)


def cross_constant_signing(cells, tau):
    """Build a cross-constant Hermitian phase signing sigma(i,j)=tau[c_i, c_j].

    cells: array of length n, cell index of each vertex.
    tau:   (q,q) complex array of unit-modulus phases with tau[b,a]=conj(tau[a,b]),
           tau[a,a]=1.  Returns the (n,n) signing matrix sigma with |sigma|=1.
    """
    cells = np.asarray(cells)
    sigma = tau[np.ix_(cells, cells)]
    return sigma


def hermitize_phase(theta):
    """Given a real (q,q) array theta, return a Hermitian U(1) signing
    tau = exp(i*theta) made antisymmetric in the exponent (theta_ba=-theta_ab,
    diag 0), i.e. tau[b,a]=conj(tau[a,b]), tau[a,a]=1."""
    A = np.triu(theta, 1)
    A = A - A.T               # antisymmetric real
    return np.exp(1j * A)


def free_phase_signing(n, rng):
    """Free per-pair Hermitian U(1) signing: random phase on each edge,
    independent across pairs (NOT cross-constant)."""
    theta = rng.uniform(-np.pi, np.pi, size=(n, n))
    A = np.triu(theta, 1)
    A = A - A.T
    return np.exp(1j * A)


def apply_signing(H0, sigma):
    """H0 with phases: H[i,j] = sigma[i,j] * H0[i,j].  Hermitian preserved when
    sigma is Hermitian (sigma[j,i]=conj(sigma[i,j])) and H0 real symmetric."""
    return sigma * H0


# ----------------------------------------------------------------------------
# Mixing measurement
# ----------------------------------------------------------------------------

def evolve(H, t):
    """CTQW propagator U(t) = exp(-i t H)."""
    return expm(-1j * t * H)


def mixing_matrix(H, t):
    """M(t)_{uv} = |U(t)_{uv}|^2."""
    U = evolve(H, t)
    return np.abs(U) ** 2


def uniform_distance(H, t):
    """D(t) = max_{u,v} |M(t)_{uv} - 1/n| (L_inf uniform-mixing distance)."""
    n = H.shape[0]
    M = mixing_matrix(H, t)
    return np.max(np.abs(M - 1.0 / n))


def uniform_distance_curve(H, ts):
    return np.array([uniform_distance(H, t) for t in ts])


def tau_mix(H, eps, T_max, n_grid=4000, refine=True):
    """First time t in [0, T_max] with D(t) <= eps.

    Coarse grid scan then (optional) bisection refinement at the first crossing.
    Returns (tau, D_min_overall): tau is None if D never drops to eps on [0,T_max];
    D_min_overall is the best (smallest) uniform distance achieved on the grid.
    """
    ts = np.linspace(1e-9, T_max, n_grid)
    D = uniform_distance_curve(H, ts)
    D_min = float(np.min(D))
    below = np.where(D <= eps)[0]
    if len(below) == 0:
        return None, D_min
    k = below[0]
    if not refine or k == 0:
        return float(ts[k]), D_min
    lo, hi = ts[k - 1], ts[k]
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if uniform_distance(H, mid) <= eps:
            hi = mid
        else:
            lo = mid
    return float(hi), D_min


def min_uniform_distance(H, T_max, n_grid=4000):
    """Smallest uniform distance achieved on [0, T_max], and the argmin time."""
    ts = np.linspace(1e-9, T_max, n_grid)
    D = uniform_distance_curve(H, ts)
    k = int(np.argmin(D))
    return float(D[k]), float(ts[k])


# ----------------------------------------------------------------------------
# Equitable-quotient check (the structural claim: cross-constant => descends)
# ----------------------------------------------------------------------------

def is_equitable(H, cells, atol=1e-9):
    """Check whether the partition `cells` is equitable for Hermitian host H:
    for any two vertices x,x' in the same cell and any target cell j, the
    signed row-sum  sum_{y in cell j} H[x,y]  equals  sum_{y in cell j} H[x',y].

    Returns (ok, max_violation)."""
    cells = np.asarray(cells)
    q = cells.max() + 1
    max_v = 0.0
    for ci in range(q):
        members = np.where(cells == ci)[0]
        if len(members) < 1:
            continue
        # cell-j row sums for each member
        rowsums = np.zeros((len(members), q), dtype=complex)
        for mi, x in enumerate(members):
            for cj in range(q):
                ys = np.where(cells == cj)[0]
                rowsums[mi, cj] = H[x, ys].sum()
        # all rows must be equal
        ref = rowsums[0]
        v = np.max(np.abs(rowsums - ref))
        max_v = max(max_v, v)
    return (max_v <= atol), float(max_v)
