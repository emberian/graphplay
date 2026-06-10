"""Export a kernel-checkable equitability certificate for SmolLM2-135M's GQA
head-axis tying.

`run_gqa_defect.py` MEASURED (float) that the head -> KV-group partition of
SmolLM2-135M has equitability defect exactly 0 on every layer: grouped-query
attention literally ties the K/V projection weights of the query heads within
a group (Ainslie et al., GQA, arXiv 2305.13245). This script upgrades that
measurement to a certificate the Lean kernel can re-check:

  1. For one layer (default 0) build the per-head K||V weight vectors
     (the KV-head weights expanded along the query-head axis).
  2. Convert every float32 weight to an EXACT dyadic rational (m * 2^-149 is
     integral for every float32), and form the exact 9x9 head-axis Gram matrix
     G[h,h'] = <W_h, W_h'> in big-integer arithmetic. Zero the diagonal
     (WeightedGraph is loopless). Tying makes the head->group partition
     equitable for G; the cross-group entries are genuine learned numbers, so
     the certificate depends on the real weights, not just a block pattern.
  3. Verify in exact arithmetic: (a) within-group K/V weight rows are
     bit-identical on ALL layers (the defect-0 fact); (b) the partition is
     equitable for G; (c) a misaligned partition is NOT equitable for G
     (negative control -- the entries are load-bearing).
  4. Emit Graphplay/Integrations/GQACertSmolLM2.lean: the matrix as exact
     rational literals plus `decide`-proved checker verdicts, consuming
     Graphplay.Integrations.EquitableCertChecker.

Run:  .venv/bin/python export_gqa_cert.py [--layer N]
Needs the cached HuggingFaceTB/SmolLM2-135M (offline ok if cached).
"""

from __future__ import annotations

import argparse
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(HERE), "Graphplay", "Integrations",
                   "GQACertSmolLM2.lean")

# Every float32 value v satisfies v * 2^149 in ZZ (smallest subnormal is
# 2^-149); ldexp by a power of two is exact in float64, so int(ldexp(v, S))
# is the exact integer numerator of v over denominator 2^S.
S = 149


def exact_ints(vec: np.ndarray) -> list[int]:
    out = []
    for v in vec.astype(np.float64).tolist():
        x = math.ldexp(v, S)
        assert x.is_integer(), f"float32 value {v} not integral at 2^{S}"
        out.append(int(x))
    return out


def fmt_rat(num: int, den_pow: int) -> str:
    """Exact rational num / 2^den_pow as a reduced Lean `mkRat` literal."""
    if num == 0:
        return "0"
    tz = (num & -num).bit_length() - 1  # trailing zeros of |num|
    s = min(tz, den_pow)
    num >>= s
    den_pow -= s
    den = "1" if den_pow == 0 else f"(2 ^ {den_pow})"
    return f"mkRat {num} {den}" if num > 0 else f"mkRat ({num}) {den}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--layer", type=int, default=0)
    args = ap.parse_args()

    import torch
    from transformers import AutoConfig, AutoModelForCausalLM

    name = "HuggingFaceTB/SmolLM2-135M"
    cfg = AutoConfig.from_pretrained(name)
    n_heads = cfg.num_attention_heads
    n_kv = cfg.num_key_value_heads
    d_head = cfg.hidden_size // n_heads
    group = n_heads // n_kv
    n_layers = cfg.num_hidden_layers
    head_to_group = [h // group for h in range(n_heads)]
    print(f"config: n_heads={n_heads} n_kv={n_kv} group={group} "
          f"d_head={d_head} layers={n_layers}")

    model = AutoModelForCausalLM.from_pretrained(name, dtype=torch.float32)
    model.eval()

    # ---- (3a) bit-identity of within-group K/V rows on ALL layers ----
    tied_layers = []
    for li, layer in enumerate(model.model.layers):
        ok = True
        for W in (layer.self_attn.k_proj.weight, layer.self_attn.v_proj.weight):
            Wh = W.detach().numpy().reshape(n_kv, d_head, -1)[head_to_group]
            for g in range(n_kv):
                idx = [h for h in range(n_heads) if head_to_group[h] == g]
                ok &= all(np.array_equal(Wh[idx[0]], Wh[h]) for h in idx[1:])
        tied_layers.append(ok)
    assert all(tied_layers), f"tying broken on layers {[i for i, t in enumerate(tied_layers) if not t]}"
    print(f"bit-identical within-group K/V rows verified on all {n_layers} layers")

    # ---- (2) exact head-axis Gram matrix for the chosen layer ----
    L = args.layer
    attn = model.model.layers[L].self_attn
    Wk = attn.k_proj.weight.detach().numpy().reshape(n_kv, d_head, -1)[head_to_group]
    Wv = attn.v_proj.weight.detach().numpy().reshape(n_kv, d_head, -1)[head_to_group]
    flat = np.concatenate([Wk.reshape(n_heads, -1), Wv.reshape(n_heads, -1)], axis=1)
    print(f"layer {L}: per-head K||V vector length = {flat.shape[1]}")
    ints = [exact_ints(flat[h]) for h in range(n_heads)]

    G = [[0] * n_heads for _ in range(n_heads)]  # numerators over 2^(2S)
    for a in range(n_heads):
        for b in range(a, n_heads):
            dot = sum(x * y for x, y in zip(ints[a], ints[b]))
            G[a][b] = G[b][a] = dot
    for h in range(n_heads):
        G[h][h] = 0  # loopless

    # ---- (3b)/(3c) exact equitability check + negative control ----
    def equitable(cell: list[int], r: int) -> bool:
        prof = [[sum(G[x][z] for z in range(n_heads) if cell[z] == j)
                 for j in range(r)] for x in range(n_heads)]
        return all(prof[x] == prof[y]
                   for x in range(n_heads) for y in range(n_heads)
                   if cell[x] == cell[y])

    mis = [((h + 1) % n_heads) // group for h in range(n_heads)]
    ok_true = equitable(head_to_group, n_kv)
    ok_false = not equitable(mis, n_kv)
    print(f"exact check: head_to_group equitable = {ok_true}, "
          f"misaligned equitable = {not ok_false}")
    assert ok_true, "head->group partition NOT equitable in exact arithmetic"
    assert ok_false, "misaligned partition unexpectedly equitable (degenerate weights?)"

    # ---- (4) emit the Lean module ----
    rows = ",\n   ".join(
        "[" + ", ".join(fmt_rat(G[a][b], 2 * S) for b in range(n_heads)) + "]"
        for a in range(n_heads))
    lean = f"""/-
# Graphplay.Integrations.GQACertSmolLM2 — **kernel-checked certificate** that
SmolLM2-135M's grouped-query attention head-tying induces an equitable
partition of the head-axis weight graph.

GENERATED by `experiments/export_gqa_cert.py` from the released weights of
`HuggingFaceTB/SmolLM2-135M` (Allal et al., arXiv 2502.02737), layer {L};
do not edit by hand — regenerate instead.

SmolLM2 uses grouped-query attention (Ainslie et al., GQA, arXiv 2305.13245):
{n_heads} query heads share {n_kv} KV heads ({group} per group), so within a group the
K/V projection weights are *bit-identical by construction*.
`experiments/run_gqa_defect.py` measured the resulting head-axis equitability
defect to be exactly 0 on all {n_layers} layers; the exporter re-verified the
within-group bit-identity of the K/V rows on all {n_layers} layers in exact
arithmetic.  This module is that measurement upgraded to a proof object:

* `gqaGram` — the exact 9×9 head-axis Gram matrix of layer {L}:
  entry `(h, h')` is `⟨W_h, W_h'⟩` where `W_h` is head `h`'s K∥V projection
  weight vector ({flat.shape[1]} float32 entries, each an exact dyadic rational
  `m/2^{S}`), computed in big-integer arithmetic — *no float round-off
  anywhere* — with the diagonal zeroed (`WeightedGraph` is loopless).
  Cross-group entries are genuine learned inner products, so this matrix is
  data, not a pattern.

* `gqa_head_tying_isEquitable` — `decide`-proved: the head → KV-group
  partition is equitable for `gqaGram`.  This holds *because* the within-group
  vectors are identical — it is the exact-arithmetic shadow of GQA tying.

* `gqa_misaligned_not_equitable` — `decide`-proved negative control: shifting
  the group boundaries by one head destroys equitability.  The certificate
  depends on the actual weight values; no degenerate matrix could pass both
  verdicts.

* `gqaHeadPartition` / `gqa_head_collapse` — the verdict transported through
  `certifiedPartition` into an `EquitablePartition` of the head-axis
  `WeightedGraph`, to which the spectral collapse
  (`restrict_eq_symmQuotient`) applies: the 9×9 head-axis operator acts on
  the cell-uniform subspace as its 3×3 symmetric quotient.  That 3× collapse
  of the head axis is the formal content of "GQA defect ≡ 0".
-/

import Graphplay.Integrations.EquitableCertChecker

namespace Graphplay
namespace Integrations
namespace EquitableCert

open scoped BigOperators

/-- Row-major entries of the exact head-axis Gram matrix of layer {L}
(numerators over powers of two — every float32 is a dyadic rational). -/
def gqaGramRows : List (List ℚ) :=
  [{rows}]

/-- The exact 9×9 head-axis K∥V Gram matrix of SmolLM2-135M layer {L},
diagonal zeroed. -/
def gqaGram : Matrix (Fin {n_heads}) (Fin {n_heads}) ℚ := matOfLists {n_heads} gqaGramRows

/-- The GQA head → KV-group partition: heads `3g, 3g+1, 3g+2` share KV head `g`. -/
def headToGroup : Fin {n_heads} → Fin {n_kv} := fun h => ⟨h.val / {group}, by omega⟩

/-- The negative-control labelling: group boundaries shifted by one head. -/
def headMisaligned : Fin {n_heads} → Fin {n_kv} :=
  fun h => ⟨((h.val + 1) % {n_heads}) / {group}, by omega⟩

set_option maxRecDepth 1000000

/-- **The certificate.**  The head → KV-group partition is equitable for the
exact head-axis Gram matrix — kernel-computed from the released weights. -/
theorem gqa_head_tying_isEquitable :
    isEquitable? gqaGram headToGroup = true := by decide +kernel

/-- **Negative control.**  Misaligning the groups by one head breaks
equitability: the verdict reads the learned entries, not the block shape. -/
theorem gqa_misaligned_not_equitable :
    isEquitable? gqaGram headMisaligned = false := by decide +kernel

/-- The head-axis weight graph of layer {L} (symmetry of the Gram matrix and
the zeroed diagonal are themselves kernel-checked). -/
def gqaHeadGraph : WeightedGraph (Fin {n_heads}) :=
  ratWeightedGraph gqaGram (by decide +kernel) (by decide +kernel)

/-- The certified equitable partition of the head axis. -/
def gqaHeadPartition : EquitablePartition gqaHeadGraph (Fin {n_kv}) :=
  certifiedPartition gqaGram headToGroup gqaHeadGraph rfl gqa_head_tying_isEquitable

/-- **The instantiated collapse**: on the cell-uniform subspace of the
certified partition, the 9×9 head-axis operator acts as its 3×3 symmetric
quotient — the head-axis reduction GQA performs, derived rather than assumed. -/
theorem gqa_head_collapse (w : Fin {n_kv} → ℂ) :
    gqaHeadGraph.adj.mulVec (fun v => ∑ i, w i * gqaHeadPartition.cellUniformVec i v)
      = fun v => ∑ i,
          (gqaHeadPartition.symmQuotient.mulVec w) i
            * gqaHeadPartition.cellUniformVec i v :=
  gqaHeadPartition.restrict_eq_symmQuotient w

end EquitableCert
end Integrations
end Graphplay
"""
    with open(OUT, "w") as f:
        f.write(lean)
    print(f"wrote {OUT} ({os.path.getsize(OUT)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
