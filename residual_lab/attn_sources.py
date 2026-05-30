"""
Sources of attention matrices: synthetic structured ones (with known character)
and real ones extracted from SmolLM2-135M on CPU.

All returned matrices are row-stochastic (rows sum to 1), n x n.
"""
import numpy as np


def _row_normalize(A):
    A = np.clip(A, 0, None)
    s = A.sum(axis=1, keepdims=True)
    s[s == 0] = 1.0
    return A / s


def softmax_rows(S):
    S = S - S.max(axis=1, keepdims=True)
    E = np.exp(S)
    return E / E.sum(axis=1, keepdims=True)


# ---------- synthetic families ----------

def make_block_equitable(n=64, n_blocks=4, noise=0.0, rng=None):
    """Truly equitable: scores depend only on (block_i, block_j). A_eq should ~recover it."""
    rng = rng or np.random.default_rng(0)
    sizes = np.full(n_blocks, n // n_blocks)
    sizes[: n - sizes.sum()] += 1
    blk = np.repeat(np.arange(n_blocks), sizes)[:n]
    core = rng.normal(size=(n_blocks, n_blocks)) * 2.0
    S = core[np.ix_(blk, blk)]
    if noise:
        S = S + rng.normal(scale=noise, size=(n, n))
    return softmax_rows(S), dict(name="block_equitable", blk=blk)


def make_banded(n=64, w=4, rng=None):
    """Local/sliding-window: banded scores (translation-equitable / circulant-ish)."""
    rng = rng or np.random.default_rng(1)
    idx = np.arange(n)
    d = np.abs(idx[:, None] - idx[None, :])
    S = -d.astype(float) ** 2 / (2 * w * w) * 5.0
    S = S + 0.1 * rng.normal(size=(n, n))
    return softmax_rows(S), dict(name="banded", w=w)


def make_induction(n=64, rng=None):
    """Induction head: each query attends sharply to one specific 'previous occurrence'
    key -> a near-permutation matrix.  High-rank, sparse.  Known hard case for low-rank."""
    rng = rng or np.random.default_rng(2)
    perm = rng.permutation(n)
    S = np.full((n, n), -8.0)
    S[np.arange(n), perm] = 8.0
    S = S + 0.5 * rng.normal(size=(n, n))
    return softmax_rows(S), dict(name="induction", perm=perm)


def make_lowrank(n=64, k=3, rng=None):
    """Global low-rank scores -> low-rank-ish attention (the Linformer regime)."""
    rng = rng or np.random.default_rng(3)
    Q = rng.normal(size=(n, k))
    K = rng.normal(size=(n, k))
    S = Q @ K.T * 1.5
    return softmax_rows(S), dict(name="lowrank", k=k)


def make_rank1_collapse(n=64, eps=0.3, rng=None):
    """Rank-collapse regime: a near-rank-1 core (identical rows) plus a structured
    deviation eps*D.  Tests whether R carries the signal when the core is rank-1."""
    rng = rng or np.random.default_rng(4)
    base_row = rng.dirichlet(np.ones(n))          # one shared row -> rank-1 core
    core = np.tile(base_row, (n, 1))
    # the *signal* lives in a structured deviation (an induction-like sharp pattern)
    perm = rng.permutation(n)
    D = np.zeros((n, n))
    D[np.arange(n), perm] = 1.0
    A = (1 - eps) * core + eps * D
    return _row_normalize(A), dict(name="rank1_collapse", eps=eps, perm=perm)


def make_hierarchical(n=64, rng=None):
    """Hierarchical / multi-scale: coarse blocks + finer sub-blocks + local band.
    Designed so a coarse equitable base leaves a *finer-equitable* residual ->
    tests the partition-tower (recursive refinement) idea."""
    rng = rng or np.random.default_rng(5)
    coarse = np.repeat(np.arange(4), n // 4)[:n]
    fine = np.repeat(np.arange(8), n // 8)[:n]
    Cc = rng.normal(size=(4, 4)) * 2.0
    Cf = rng.normal(size=(8, 8)) * 1.0
    idx = np.arange(n)
    band = -np.abs(idx[:, None] - idx[None, :]) / 8.0
    S = Cc[np.ix_(coarse, coarse)] + Cf[np.ix_(fine, fine)] + band
    return softmax_rows(S), dict(name="hierarchical", coarse=coarse, fine=fine)


SYNTH = {
    "block_equitable": make_block_equitable,
    "banded": make_banded,
    "induction": make_induction,
    "lowrank": make_lowrank,
    "rank1_collapse": make_rank1_collapse,
    "hierarchical": make_hierarchical,
}


# ---------- real model ----------

def get_smollm_attentions(prompt=None, max_tokens=48, model_id="HuggingFaceTB/SmolLM2-135M"):
    """Extract per-(layer,head) attention matrices from SmolLM2-135M on CPU.
    Returns list of dicts: {layer, head, A (n x n row-stochastic numpy), tokens}."""
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    if prompt is None:
        prompt = ("The cat sat on the mat. The dog sat on the log. "
                  "When numbers like 3 7 3 7 3 7 repeat, the pattern continues 3 7. "
                  "Paris is the capital of France and Rome is the capital of Italy.")
    tok = AutoTokenizer.from_pretrained(model_id)
    model = AutoModelForCausalLM.from_pretrained(
        model_id, attn_implementation="eager", torch_dtype=torch.float32)
    model.eval()
    enc = tok(prompt, return_tensors="pt")
    ids = enc["input_ids"][:, :max_tokens]
    with torch.no_grad():
        out = model(ids, output_attentions=True)
    atts = out.attentions  # tuple(L) each (1, H, n, n)
    tokens = tok.convert_ids_to_tokens(ids[0].tolist())
    results = []
    L = len(atts)
    for layer in range(L):
        a = atts[layer][0].numpy()  # (H, n, n)
        H = a.shape[0]
        for head in range(H):
            results.append(dict(layer=layer, head=head,
                                A=a[head].astype(np.float64), tokens=tokens))
    return results, dict(n_layers=L, n_heads=atts[0].shape[1], tokens=tokens)
