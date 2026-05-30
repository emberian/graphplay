"""Circuit Atlas: classify every attention head of a REAL production LLM by its
dominant structured-walk atom, using the walk-basis sparse-coding diagnostic that
was validated on the labeled attn-only-2l toy model.

Pipeline:
  1. Load a real LLM (SmolLM3-3B, fall back to OLMo-2 / SmolLM2). Run a few diverse
     prompts INCLUDING a repeated-random-token sequence (activates induction heads)
     and natural text. Extract per-(layer, head) attention matrices, averaged over
     inputs of the same structural type. Handle GQA (KV-head sharing).
  2. For each head: the bos-sink atom is in the dictionary so OMP encodes the BOS
     attention sink FIRST (mandatory or everything looks irreducible). Then
     sparse-code the residual against the named walk dictionary. The induction atom
     uses the KNOWN repeat period of the repeated-token prompt (content-dependent
     offset, handled explicitly).
  3. Assign each head a CIRCUIT-TYPE label = its dominant named atom(s):
       {sink, prev-token/shift, induction, positional/diffusion, content/irreducible}
     with the reconstruction error / residual.
  4. Emit results.json for the figure + findings stage.

Honest about: which model loaded, CPU compute limits, GQA, and the
content/irreducible fraction.
"""
from __future__ import annotations

import gc
import json
import os
import sys
import time
import warnings

import numpy as np
import torch

warnings.filterwarnings("ignore")

_HERE = os.path.dirname(os.path.abspath(__file__))
_EXP = os.path.dirname(_HERE)
_WALK = os.path.join(_EXP, "walk_basis")
for p in (_HERE, _EXP, _WALK):
    if p not in sys.path:
        sys.path.insert(0, p)

# read-only reuse of the validated walk-basis dictionary + sparse coder
from dictionary import build_dictionary, atom_class, _rownorm_causal  # noqa: E402
from sparsecode import omp, nnls_code, atoms_to_reach  # noqa: E402

torch.manual_seed(0)
RNG = np.random.default_rng(0)

SEQ_LEN = 96          # natural-text seq length (n); repeated prompt uses 2*HALF+BOS
HALF = 40             # repeated-prompt period: [prefix(HALF), prefix(HALF)] + BOS
ERR_THRESH = 0.10
MAX_ATOMS = 12        # OMP budget (kept modest; CPU + many heads)

MODEL_CANDIDATES = [
    "HuggingFaceTB/SmolLM3-3B",
    "allenai/OLMo-2-0425-1B",
    "HuggingFaceTB/SmolLM2-1.7B",
    "HuggingFaceTB/SmolLM2-360M",
]


# --------------------------------------------------------------------------- #
# induction atom (content-dependent shift at the KNOWN repeat period)
# --------------------------------------------------------------------------- #
def induction_atom(n: int, period: int, bos: int = 1) -> np.ndarray:
    """On a length-`period`-repeated sequence, an induction head attends from q to
    k = q - period + 1 (token AFTER the previous occurrence of the current token).
    `bos` = index of first real token (1 if BOS prepended). This is the explicit
    content-dependent shift; without it the induction structure is invisible."""
    M = np.zeros((n, n))
    for q in range(n):
        k = q - period + 1
        if bos <= k <= q:
            M[q, k] = 1.0
        else:
            M[q, q] = 1.0
    return _rownorm_causal(M)


# --------------------------------------------------------------------------- #
# model loading with fallback
# --------------------------------------------------------------------------- #
def load_model():
    from transformers import AutoModelForCausalLM, AutoTokenizer
    last_err = None
    for name in MODEL_CANDIDATES:
        try:
            print(f"[load] trying {name} ...", flush=True)
            tok = AutoTokenizer.from_pretrained(name)
            t0 = time.time()
            model = AutoModelForCausalLM.from_pretrained(
                name,
                torch_dtype=torch.float32,   # CPU: fp32 most reliable for attn
                device_map="cpu",
                attn_implementation="eager",  # required for output_attentions
            )
            model.eval()
            print(f"[load] OK {name} in {time.time()-t0:.0f}s", flush=True)
            return model, tok, name
        except Exception as e:  # noqa: BLE001
            print(f"[load] FAILED {name}: {type(e).__name__}: {e}", flush=True)
            last_err = e
            gc.collect()
    raise RuntimeError(f"all model candidates failed; last={last_err}")


# --------------------------------------------------------------------------- #
# prompts
# --------------------------------------------------------------------------- #
NATURAL_PROMPTS = [
    "The history of science is a long sequence of ideas that build on one "
    "another, each new theory refining or overturning the assumptions of the "
    "previous generation of thinkers and experimenters across many countries.",
    "When the river finally reached the sea, the travelers stopped to rest on "
    "the warm sand and watched the sun fall slowly behind the distant hills, "
    "talking quietly about everything they had seen along the winding journey.",
    "In computer programming, a function takes some input values, performs a "
    "computation on them, and then returns an output value that other parts of "
    "the program can use to make decisions and continue the running process.",
]


def build_repeated_tokens(tok, n_seq, half):
    """[prefix, prefix] repeated random tokens -> activates induction heads.
    Returns (input_ids tensor (n_seq, L), period=half, bos_offset)."""
    vocab = tok.vocab_size
    lo, hi = 200, max(1000, vocab - 50)
    seqs = []
    bos_id = tok.bos_token_id
    for _ in range(n_seq):
        pre = RNG.integers(low=lo, high=hi, size=half)
        full = np.concatenate([pre, pre])
        if bos_id is not None:
            full = np.concatenate([[bos_id], full])
        seqs.append(full)
    ids = torch.tensor(np.stack(seqs), dtype=torch.long)
    bos_off = 1 if bos_id is not None else 0
    return ids, half, bos_off


def encode_natural(tok, prompts, seq_len):
    """Tokenize natural prompts, pad/truncate to a common length. BOS handled by
    tokenizer. Returns (ids, attn_mask, bos_offset)."""
    enc = tok(prompts, return_tensors="pt", padding="max_length",
              truncation=True, max_length=seq_len)
    # bos offset: 1 if tokenizer prepends bos
    first = enc["input_ids"][0, 0].item()
    bos_off = 1 if (tok.bos_token_id is not None and first == tok.bos_token_id) else 0
    return enc["input_ids"], enc["attention_mask"], bos_off


# --------------------------------------------------------------------------- #
# attention extraction
# --------------------------------------------------------------------------- #
@torch.no_grad()
def get_attentions(model, input_ids, attention_mask=None):
    """Return tuple of (n_layers) tensors each (batch, n_heads, q, k)."""
    out = model(input_ids=input_ids, attention_mask=attention_mask,
                output_attentions=True, use_cache=False)
    return out.attentions  # tuple len n_layers, each (B, H, T, T)


def per_head_mean(att_tuple):
    """Stack attentions -> array (n_layers, n_heads, T, T) averaged over batch."""
    arrs = []
    for a in att_tuple:
        arrs.append(a.float().mean(0).cpu().numpy())  # (H, T, T)
    return np.stack(arrs, axis=0)  # (L, H, T, T)


# --------------------------------------------------------------------------- #
# per-head scores (induction / prev-token / sink / diag)
# --------------------------------------------------------------------------- #
def head_scores(A, period, bos_off):
    """Structural diagnostics on a single head matrix A (T,T), repeated-token run.
      induction_score : mean attn from q in 2nd copy to k = q-period+1
      prev_token_score: mean attn to q-1
      diag_score      : mean self-attention
      sink_score      : mean attn to column bos_off (the BOS column)
    """
    T = A.shape[0]
    start2 = bos_off + period
    ind = [A[q, q - period + 1] for q in range(start2, T)
           if 0 <= q - period + 1 < T]
    induction_score = float(np.mean(ind)) if ind else 0.0
    prev = [A[q, q - 1] for q in range(1, T)]
    prev_token_score = float(np.mean(prev)) if prev else 0.0
    diag_score = float(np.mean([A[q, q] for q in range(T)]))
    sink_score = float(np.mean(A[:, bos_off])) if bos_off < T else float(np.mean(A[:, 0]))
    return dict(induction_score=induction_score, prev_token_score=prev_token_score,
                diag_score=diag_score, sink_score=sink_score)


# --------------------------------------------------------------------------- #
# sparse coding a head -> circuit type
# --------------------------------------------------------------------------- #
def circuit_type(order_named, errors, scores):
    """Assign the dominant circuit-type label from the OMP atom order, the error
    floor, and the structural scores. The bos-sink atom is mandatory-first in the
    dictionary so we read the FIRST NON-SINK atom as the dominant walk.
      sink      : head is ~pure BOS sink (sink_score high, first/only atom = sink,
                  residual after removing sink is small noise)
      induction : induction-shift is the dominant non-sink atom (or high ind score)
      prev-token: shift-1 dominant non-sink atom
      shift     : shift-k (k>1) dominant
      positional: diffusion / cell-uniform / identity / uniform dominant
      content   : never reaches a usable error with the structured atoms
    """
    floor = float(min(errors))
    # the named atoms in order; sink usually first
    non_sink = [a for a in order_named if a != "bos-sink"]
    first_non_sink = non_sink[0] if non_sink else None

    # very high sink mass AND the residual is small (or no other atom helps much)
    sink_dominated = scores["sink_score"] >= 0.5
    # err after the sink atom alone:
    # find index of sink in order, error after it
    err_after_sink = None
    if "bos-sink" in order_named:
        k = order_named.index("bos-sink") + 1
        if k < len(errors):
            err_after_sink = errors[k]

    if sink_dominated and (err_after_sink is not None and err_after_sink <= 0.25):
        return "sink"

    # INDUCTION exception (validated pitfall): an induction head selects the
    # `induction-shift` atom as its dominant non-sink walk but carries a LARGE
    # diffuse residual (batch-mean blur + genuine spread), so its floor stays
    # high. The ATOM IDENTITY is diagnostic even when the reconstruction is not
    # (WALK_BASIS_FINDINGS headline). So if the head has a real induction signal
    # AND induction-shift is its dominant walk, label it induction regardless of
    # the floor. Threshold 0.15 ~= the toy-model induction-head cutoff.
    if first_non_sink == "induction-shift" and scores["induction_score"] >= 0.15:
        return "induction"

    # if no structured atom ever brings error to a usable level -> content
    USABLE = 0.30
    if floor > USABLE:
        return "content"

    if first_non_sink is None:
        return "sink" if sink_dominated else "content"

    if first_non_sink == "induction-shift":
        return "induction"
    if first_non_sink == "shift-1":
        return "prev-token"
    if first_non_sink.startswith("shift-"):
        return "shift"
    cls = atom_class(first_non_sink)
    if cls in ("diffusion", "cell-uniform", "identity", "uniform"):
        return "positional"
    if first_non_sink == "bos-sink":
        return "sink"
    return "content"


def code_head(A, D, names, scores):
    a = np.asarray(A, dtype=float).ravel()
    res = omp(a, D, MAX_ATOMS)
    order_named = [names[j] for j in res["order"]]
    order_classes = [atom_class(n) for n in res["order_named"]] if False else \
        [atom_class(names[j]) for j in res["order"]]
    errors = res["errors"]
    ctype = circuit_type(order_named, errors, scores)
    floor = float(min(errors))
    # residual / irreducibility = error floor with the full OMP budget
    return dict(
        circuit_type=ctype,
        order_named=order_named,
        order_classes=order_classes,
        errors=[float(e) for e in errors],
        err_floor=floor,
        k_to_10pct=atoms_to_reach(errors, 0.10),
        k_to_25pct=atoms_to_reach(errors, 0.25),
        first_non_sink=next((a for a in order_named if a != "bos-sink"), None),
        used_bos_sink="bos-sink" in order_named,
        used_induction="induction-shift" in order_named,
        coef_top=sorted(
            [(names[j], float(res["coef"][j])) for j in res["order"]],
            key=lambda t: -abs(t[1]))[:5],
        **scores,
    )


# --------------------------------------------------------------------------- #
# main
# --------------------------------------------------------------------------- #
def main():
    model, tok, model_name = load_model()
    cfg = model.config
    n_layers = cfg.num_hidden_layers
    n_heads = cfg.num_attention_heads
    n_kv = getattr(cfg, "num_key_value_heads", n_heads)
    print(f"[model] {model_name}: layers={n_layers} heads={n_heads} kv={n_kv}",
          flush=True)

    # tokenizer padding
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token or tok.bos_token

    # ----- repeated-token (induction) run -----
    print("[run] repeated-token batch (induction probe) ...", flush=True)
    rep_ids, period, bos_off_rep = build_repeated_tokens(tok, n_seq=6, half=HALF)
    rep_att = get_attentions(model, rep_ids)
    A_rep = per_head_mean(rep_att)  # (L, H, T, T)
    T_rep = A_rep.shape[-1]
    del rep_att
    gc.collect()
    print(f"[run] repeated T={T_rep} period={period} bos_off={bos_off_rep}",
          flush=True)

    # ----- natural-text run -----
    print("[run] natural-text batch ...", flush=True)
    nat_ids, nat_mask, bos_off_nat = encode_natural(tok, NATURAL_PROMPTS, SEQ_LEN)
    nat_att = get_attentions(model, nat_ids, nat_mask)
    A_nat = per_head_mean(nat_att)  # (L, H, Tn, Tn)
    T_nat = A_nat.shape[-1]
    del nat_att
    gc.collect()
    print(f"[run] natural T={T_nat} bos_off={bos_off_nat}", flush=True)

    # ----- dictionaries at the two seq lengths -----
    # repeated run carries the induction structure -> add induction-shift atom
    D_rep, names_rep = build_dictionary(T_rep)
    D_rep = np.concatenate(
        [D_rep, induction_atom(T_rep, period, bos_off_rep).ravel()[None, :]], axis=0)
    names_rep = list(names_rep) + ["induction-shift"]

    D_nat, names_nat = build_dictionary(T_nat)
    # no known period in natural text -> no induction atom there
    print(f"[dict] rep: {len(names_rep)} atoms (incl induction-shift); "
          f"nat: {len(names_nat)} atoms", flush=True)

    # ----- code every head -----
    # GQA: every q-head is materialized separately in output_attentions (HF expands
    # KV across the group), so each (L,H) is a real q-head pattern. We still record
    # the kv-group so the findings can note KV-sharing-induced pattern similarity.
    heads = {}
    group = n_heads // n_kv if n_kv else 1
    print("[code] coding heads (induction-run = primary; natural cross-check) ...",
          flush=True)
    for L in range(n_layers):
        for H in range(n_heads):
            scores = head_scores(A_rep[L, H], period, bos_off_rep)
            coded_rep = code_head(A_rep[L, H], D_rep, names_rep, scores)
            # natural-text cross-check (no induction atom): floor + first atom
            scores_nat = head_scores(A_nat[L, H], period=0, bos_off=bos_off_nat) \
                if False else None
            # natural scores: reuse sink/prev/diag (induction NA on natural text)
            nat_sc = dict(
                sink_score=float(np.mean(A_nat[L, H][:, bos_off_nat]
                                          if bos_off_nat < T_nat else A_nat[L, H][:, 0])),
                prev_token_score=float(np.mean([A_nat[L, H][q, q - 1]
                                                for q in range(1, T_nat)])),
                diag_score=float(np.mean([A_nat[L, H][q, q] for q in range(T_nat)])),
                induction_score=0.0,
            )
            coded_nat = code_head(A_nat[L, H], D_nat, names_nat, nat_sc)
            heads[f"L{L}H{H}"] = dict(
                layer=L, head=H, kv_group=H // group,
                rep=coded_rep, nat=coded_nat,
            )
        if (L + 1) % 6 == 0 or L == n_layers - 1:
            print(f"[code]   ...{L+1}/{n_layers} layers", flush=True)

    # ----- aggregate -----
    out = dict(
        model=model_name,
        n_layers=n_layers, n_heads=n_heads, n_kv=n_kv, kv_group=group,
        T_rep=int(T_rep), T_nat=int(T_nat), period=int(period),
        err_thresh=ERR_THRESH, max_atoms=MAX_ATOMS,
        dictionary_rep=names_rep, dictionary_nat=names_nat,
        heads=heads,
    )
    path = os.path.join(_HERE, "results.json")
    with open(path, "w") as f:
        json.dump(out, f, default=_jsonify)
    print(f"[done] wrote {path}", flush=True)

    # quick console summary
    from collections import Counter
    ctypes = Counter(h["rep"]["circuit_type"] for h in heads.values())
    print("\n==== circuit-type distribution (induction-run labels) ====")
    total = len(heads)
    for t, c in ctypes.most_common():
        print(f"  {t:12s} {c:4d}  ({100*c/total:.0f}%)")
    # induction heads by layer
    ind = [(h["layer"], h["head"], h["rep"]["induction_score"],
            h["rep"]["err_floor"])
           for h in heads.values() if h["rep"]["circuit_type"] == "induction"]
    print(f"\n  induction heads: {len(ind)} -> "
          f"{sorted(set(l for l,_,_,_ in ind))}")
    return out


def _jsonify(o):
    if isinstance(o, np.floating):
        return float(o)
    if isinstance(o, np.integer):
        return int(o)
    if isinstance(o, np.ndarray):
        return o.tolist()
    return str(o)


if __name__ == "__main__":
    main()
