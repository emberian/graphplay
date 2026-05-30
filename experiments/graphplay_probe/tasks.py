"""Synthetic, tiny task suite with *known, distinct* structural character.

Each task returns integer token sequences and integer targets (one target per
position; positions that should not be scored are marked with target == -100,
the standard ignore index). The structural character each task *needs*:

* ``induction``  — copy the token that followed a previous occurrence of the
  current token. Needs *sharp / sparse* attention (a single off-diagonal edge).
* ``averaging``  — predict the (binned) running mean of the sequence so far.
  A *low-rank* (uniform-ish) attention suffices.
* ``recall``     — associative recall: stream of key,value pairs then a query
  key; output the matching value. Needs sharp content-based pointer (sparse).
* ``local``      — predict a function of the immediately preceding ``w`` tokens
  (here: token[i-1]). Needs *banded / local* attention.
"""

from __future__ import annotations

import numpy as np

IGNORE = -100


def _rng(seed):
    return np.random.default_rng(seed)


def make_induction(n_samples=512, seq_len=24, vocab=16, seed=0):
    """Induction / copy. Sequence of tokens; at each position the target is the
    token that followed the *previous* occurrence of the current token (else
    IGNORE). The model must attend sharply to that one earlier position."""
    rng = _rng(seed)
    X = rng.integers(1, vocab, size=(n_samples, seq_len))
    Y = np.full((n_samples, seq_len), IGNORE)
    for s in range(n_samples):
        last_after: dict[int, int] = {}
        for i in range(seq_len):
            t = X[s, i]
            if t in last_after:
                Y[s, i] = last_after[t]
            # record the token that follows position i (its successor)
            if i + 1 < seq_len:
                last_after_token = X[s, i + 1]
            # update: previous occurrence of token at i maps to its successor
        # second pass to fill "token that followed previous occurrence"
        prev_succ: dict[int, int] = {}
        Y[s, :] = IGNORE
        for i in range(seq_len):
            t = int(X[s, i])
            if t in prev_succ:
                Y[s, i] = prev_succ[t]
            if i + 1 < seq_len:
                prev_succ[t] = int(X[s, i + 1])
    return X.astype(np.int64), Y.astype(np.int64), vocab


def make_averaging(n_samples=512, seq_len=24, vocab=16, n_bins=None, seed=1):
    """Averaging / bag-of-words. Target at position i = binned running mean of
    tokens[0..i]. Low-rank (near-uniform) attention suffices."""
    rng = _rng(seed)
    if n_bins is None:
        n_bins = vocab
    X = rng.integers(1, vocab, size=(n_samples, seq_len))
    means = np.cumsum(X, axis=1) / (np.arange(1, seq_len + 1)[None, :])
    Y = np.clip((means / vocab * n_bins).astype(int), 0, n_bins - 1)
    return X.astype(np.int64), Y.astype(np.int64), max(vocab, n_bins)


def make_recall(n_samples=512, n_pairs=5, vocab=16, seed=2):
    """Associative recall. Layout: k1 v1 k2 v2 ... kP vP  q  where q equals one
    of the earlier keys; the target is read out *at the query position itself*
    (the matching value). Putting the readout at the query token means a single
    content-based head suffices: the q position attends sharply to the matching
    key occurrence and routes the *adjacent* value forward — an attention-only
    (sparse, sharp) circuit. Keys are even ids, values odd ids (separable)."""
    rng = _rng(seed)
    keys = np.arange(2, vocab, 2)          # even tokens are keys
    vals = np.arange(1, vocab, 2)          # odd tokens are values
    seq_len = 2 * n_pairs + 1              # pairs + the query key
    X = np.zeros((n_samples, seq_len), dtype=np.int64)
    Y = np.full((n_samples, seq_len), IGNORE, dtype=np.int64)
    for s in range(n_samples):
        ks = rng.permutation(keys)[:n_pairs]
        vs = rng.choice(vals, size=n_pairs)
        for p in range(n_pairs):
            X[s, 2 * p] = ks[p]
            X[s, 2 * p + 1] = vs[p]
        qi = rng.integers(0, n_pairs)
        X[s, 2 * n_pairs] = ks[qi]         # the query key (readout position)
        Y[s, 2 * n_pairs] = vs[qi]         # target read out here
    return X, Y, vocab


def make_local(n_samples=512, seq_len=24, vocab=16, seed=3):
    """Local / translation. Target at position i = token[i-1] (copy the
    immediately preceding token). A genuine *local* routing task: banded
    (width-1) attention copying the previous token's value suffices, and an
    attention-only model can realize it (it routes/copies a token identity; it
    does not need to transform it — which an attention-only model cannot do)."""
    rng = _rng(seed)
    X = rng.integers(1, vocab, size=(n_samples, seq_len))
    Y = np.full((n_samples, seq_len), IGNORE, dtype=np.int64)
    Y[:, 1:] = X[:, :-1]
    return X.astype(np.int64), Y.astype(np.int64), vocab


TASKS = {
    "induction": (make_induction, "sparse"),
    "averaging": (make_averaging, "low-rank"),
    "recall": (make_recall, "sparse"),
    "local": (make_local, "banded"),
}


def build_task(name, n_train=4096, n_test=512, seed=0):
    """Return (Xtr, Ytr, Xte, Yte, vocab, needed_structure)."""
    fn, structure = TASKS[name]
    Xtr, Ytr, vocab = fn(n_samples=n_train, seed=seed)
    Xte, Yte, _ = fn(n_samples=n_test, seed=seed + 9999)
    return Xtr, Ytr, Xte, Yte, vocab, structure
