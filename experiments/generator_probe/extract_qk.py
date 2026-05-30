"""Extract Q, K (hence S = Q Kᵀ / √d) and A from the tiny attention-only model.

Imports model/tasks read-only from graphplay_probe. We re-run the model forward
but tap the per-head q,k tensors *before* the softmax, so the score generator
S = q kᵀ / √d_head is directly available (this is what graphplay_probe.model
computes internally as ``scores``; we recompute it and also recover q,k).
"""

from __future__ import annotations

import math
import os
import sys

import numpy as np
import torch

_HERE = os.path.dirname(os.path.abspath(__file__))
_EXP = os.path.dirname(_HERE)
if _EXP not in sys.path:
    sys.path.insert(0, _EXP)

from graphplay_probe.model import TinyTransformer, train_model  # noqa: E402
from graphplay_probe import tasks as T  # noqa: E402


@torch.no_grad()
def extract_S_and_A(model: TinyTransformer, X, n_examples=64, device="cpu",
                    apply_causal_mask=True):
    """Return per (layer, head): S (pre-softmax score generator = qkᵀ/√d) and
    A (post-softmax). Averaged over a batch of inputs.

    We register forward hooks on each block to grab q,k. S is the *masked* score
    (causal -inf above diagonal) when apply_causal_mask, matching how A is formed;
    we ALSO return the unmasked raw generator S_raw = qkᵀ/√d (rank ≤ d_head, no
    mask) because the masking is what destroys the generator's low-rank-ness, and
    the structural question is cleanest on S_raw.
    """
    model.eval()
    Xt = torch.tensor(np.asarray(X)[:n_examples], device=device)
    B, Tlen = Xt.shape

    captured = []  # list per layer of dict(q,k)

    def make_hook():
        store = {}
        def hook(module, inp, out):
            x = inp[0]
            h = module.ln(x)
            qkv = module.qkv(h).reshape(x.shape[0], x.shape[1], 3,
                                        module.n_heads, module.d_head)
            q, k, v = qkv.unbind(dim=2)
            store["q"] = q.transpose(1, 2)  # B,H,T,dh
            store["k"] = k.transpose(1, 2)
        return store, hook

    handles = []
    stores = []
    for blk in model.blocks:
        store, hook = make_hook()
        handles.append(blk.register_forward_hook(hook))
        stores.append(store)

    model(Xt, return_attn=False)
    for h in handles:
        h.remove()

    out = []
    causal = torch.triu(torch.ones(Tlen, Tlen), diagonal=1).bool()
    for store in stores:
        q, k = store["q"], store["k"]  # B,H,T,dh
        dh = q.shape[-1]
        S_raw = (q @ k.transpose(-1, -2)) / math.sqrt(dh)  # B,H,T,T
        S_masked = S_raw.clone()
        if apply_causal_mask:
            S_masked = S_masked.masked_fill(causal, float("-inf"))
        A = torch.softmax(S_masked, dim=-1)
        # average over batch
        layer = {
            "S_raw": S_raw.mean(0).cpu().numpy(),       # H,T,T
            "S_masked": S_masked.mean(0).cpu().numpy(),  # H,T,T (has -inf)
            "A": A.mean(0).cpu().numpy(),                # H,T,T
            "d_head": int(dh),
        }
        out.append(layer)
    return out


def train_task(name, d_model=32, n_heads=2, n_layers=2, epochs=30, seed=0,
               n_train=4096, n_test=512, verbose=False):
    Xtr, Ytr, Xte, Yte, vocab, structure = T.build_task(
        name, n_train=n_train, n_test=n_test, seed=seed)
    model, acc = train_model(
        Xtr, Ytr, Xte, Yte, vocab,
        d_model=d_model, n_heads=n_heads, n_layers=n_layers,
        epochs=epochs, seed=seed, verbose=verbose)
    return model, Xte, acc, structure, vocab
