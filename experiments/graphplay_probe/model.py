"""A tiny, from-scratch, attention-only transformer (~10k-100k params).

Deliberately minimal: token + positional embedding, ``n_layers`` causal
multi-head self-attention blocks with a residual stream, and an unembedding to
logits. No MLP (attention-only) so that the *attention matrices are the whole
story* — which is exactly what the probe inspects. Trains in minutes on CPU.

The forward pass optionally returns the per-layer per-head attention maps so the
probe can decompose the held-out ``A*``.
"""

from __future__ import annotations

import math

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F


class AttnOnlyBlock(nn.Module):
    def __init__(self, d_model, n_heads, causal=True):
        super().__init__()
        assert d_model % n_heads == 0
        self.n_heads = n_heads
        self.d_head = d_model // n_heads
        self.causal = causal
        self.qkv = nn.Linear(d_model, 3 * d_model, bias=False)
        self.proj = nn.Linear(d_model, d_model, bias=False)
        self.ln = nn.LayerNorm(d_model)

    def forward(self, x, return_attn=False):
        B, T, D = x.shape
        h = self.ln(x)
        qkv = self.qkv(h).reshape(B, T, 3, self.n_heads, self.d_head)
        q, k, v = qkv.unbind(dim=2)            # each B,T,H,dh
        q = q.transpose(1, 2)                  # B,H,T,dh
        k = k.transpose(1, 2)
        v = v.transpose(1, 2)
        scores = (q @ k.transpose(-1, -2)) / math.sqrt(self.d_head)
        if self.causal:
            mask = torch.triu(torch.ones(T, T, device=x.device), diagonal=1).bool()
            scores = scores.masked_fill(mask, float("-inf"))
        attn = F.softmax(scores, dim=-1)        # B,H,T,T
        out = attn @ v                          # B,H,T,dh
        out = out.transpose(1, 2).reshape(B, T, D)
        x = x + self.proj(out)
        if return_attn:
            return x, attn
        return x, None


class TinyTransformer(nn.Module):
    def __init__(self, vocab, d_model=32, n_heads=2, n_layers=2, max_len=64, causal=True):
        super().__init__()
        self.tok = nn.Embedding(vocab, d_model)
        self.pos = nn.Embedding(max_len, d_model)
        self.blocks = nn.ModuleList(
            [AttnOnlyBlock(d_model, n_heads, causal=causal) for _ in range(n_layers)]
        )
        self.ln_f = nn.LayerNorm(d_model)
        self.unembed = nn.Linear(d_model, vocab, bias=False)
        self.max_len = max_len

    def forward(self, idx, return_attn=False):
        B, T = idx.shape
        pos = torch.arange(T, device=idx.device)
        x = self.tok(idx) + self.pos(pos)[None]
        attns = []
        for blk in self.blocks:
            x, a = blk(x, return_attn=return_attn)
            if return_attn:
                attns.append(a)
        x = self.ln_f(x)
        logits = self.unembed(x)
        if return_attn:
            return logits, attns
        return logits, None

    def num_params(self):
        return sum(p.numel() for p in self.parameters())


def train_model(
    Xtr, Ytr, Xte, Yte, vocab,
    d_model=32, n_heads=2, n_layers=2, epochs=30, batch=128, lr=3e-3,
    device="cpu", seed=0, ignore_index=-100, verbose=False,
):
    torch.manual_seed(seed)
    np.random.seed(seed)
    T = Xtr.shape[1]
    model = TinyTransformer(vocab, d_model, n_heads, n_layers, max_len=T).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=0.0)
    Xtr_t = torch.tensor(Xtr, device=device)
    Ytr_t = torch.tensor(Ytr, device=device)
    Xte_t = torch.tensor(Xte, device=device)
    Yte_t = torch.tensor(Yte, device=device)
    n = Xtr.shape[0]
    for ep in range(epochs):
        model.train()
        perm = torch.randperm(n)
        for i in range(0, n, batch):
            bi = perm[i:i + batch]
            logits, _ = model(Xtr_t[bi])
            loss = F.cross_entropy(
                logits.reshape(-1, vocab), Ytr_t[bi].reshape(-1),
                ignore_index=ignore_index,
            )
            opt.zero_grad()
            loss.backward()
            opt.step()
        if verbose and (ep % 5 == 0 or ep == epochs - 1):
            acc = eval_acc(model, Xte_t, Yte_t, vocab, ignore_index)
            print(f"  ep {ep:3d}  loss {loss.item():.4f}  test_acc {acc:.3f}")
    acc = eval_acc(model, Xte_t, Yte_t, vocab, ignore_index)
    return model, acc


@torch.no_grad()
def eval_acc(model, Xte_t, Yte_t, vocab, ignore_index=-100):
    model.eval()
    logits, _ = model(Xte_t)
    pred = logits.argmax(-1)
    mask = Yte_t != ignore_index
    if mask.sum() == 0:
        return float("nan")
    return float((pred[mask] == Yte_t[mask]).float().mean())


@torch.no_grad()
def extract_attention(model, X, n_examples=64, device="cpu"):
    """Return mean attention maps per (layer, head): list[layer] of arrays of
    shape (n_heads, T, T), averaged over ``n_examples`` held-out inputs."""
    model.eval()
    Xt = torch.tensor(X[:n_examples], device=device)
    _, attns = model(Xt, return_attn=True)
    # attns: list[layer] of (B,H,T,T); average over batch
    return [a.mean(dim=0).cpu().numpy() for a in attns]
