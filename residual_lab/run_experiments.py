"""
Main driver: build attention matrices, equitable-decompose, run every recovery
technique, save figures + a results.json that RESIDUAL_FINDINGS.md is built from.
"""
import json
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from attn_sources import SYNTH, get_smollm_attentions
from equitable import decompose_at_r
import recover as rec

HERE = os.path.dirname(os.path.abspath(__file__))
FIG = os.path.join(HERE, "figures")
os.makedirs(FIG, exist_ok=True)

N = 64
R_SWEEP = [2, 4, 8, 12, 16, 24, 32]
# the "operating" r at which we characterize R in depth (a meaningfully coarse base)
R_OP = 8


def jsonable(o):
    if isinstance(o, dict):
        return {str(k): jsonable(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [jsonable(v) for v in o]
    if isinstance(o, np.ndarray):
        return o.tolist()
    if isinstance(o, (np.floating, np.integer)):
        return o.item()
    return o


# ---------------------------------------------------------------------------
def collect_matrices():
    mats = {}
    for name, fn in SYNTH.items():
        A, meta = fn(n=N)
        mats[f"synth/{name}"] = dict(A=A, meta=meta, kind="synthetic")
    # real model: sample a spread of layers, head 0 and a mid head
    try:
        res, info = get_smollm_attentions(max_tokens=N)
        L = info["n_layers"]
        H = info["n_heads"]
        picks = [(0, 0), (L // 4, 0), (L // 2, H // 2),
                 (3 * L // 4, 0), (L - 1, H // 2), (L - 1, 0)]
        bypos = {(d["layer"], d["head"]): d for d in res}
        for (l, h) in picks:
            d = bypos[(l, h)]
            mats[f"smollm/L{l}H{h}"] = dict(A=d["A"], meta=dict(layer=l, head=h),
                                            kind="real")
        # keep ALL for the layer-localization sweep
        mats["_smollm_all"] = res
        mats["_smollm_info"] = info
    except Exception as e:
        print("SmolLM extraction failed:", e)
    return mats


# ---------------------------------------------------------------------------
def characterize_one(name, A):
    """Run the full battery on one matrix at the operating r, plus the r-sweep."""
    out = dict(name=name, n=A.shape[0],
               normA=float(np.linalg.norm(A)),
               rankA=int(np.linalg.matrix_rank(A, tol=1e-9)))
    # r sweep: residual norm + rank
    sweep = []
    for r in R_SWEEP:
        d = decompose_at_r(A, r)
        R = d["R"]
        sweep.append(dict(r=d["r"],
                          rel=float(np.linalg.norm(R) / (np.linalg.norm(A) + 1e-12)),
                          rankR=int(np.linalg.matrix_rank(R, tol=1e-9))))
    out["r_sweep"] = sweep

    # at operating r, deep dive
    d = decompose_at_r(A, R_OP)
    R, A_eq = d["R"], d["A_eq"]
    out["r_op"] = d["r"]
    out["rel_op"] = float(np.linalg.norm(R) / (np.linalg.norm(A) + 1e-12))
    out["rankR_op"] = int(np.linalg.matrix_rank(R, tol=1e-9))

    svd = rec.svd_truncation(R)
    out["svd"] = dict(errs=jsonable(svd["errs"]), rank90=svd["rank90"],
                      rank99=svd["rank99"], eff_rank=svd["eff_rank"],
                      stable_rank=svd["stable_rank"],
                      svals=jsonable(svd["svals"][:32]))
    rpca = rec.robust_pca(R)
    out["rpca"] = dict(rankL=rpca["rankL"], sparsity=rpca["sparsity"],
                       err=rpca["err"], Lnorm=float(rpca["Lnorm"]),
                       Snorm=float(rpca["Snorm"]))
    out["sparse"] = jsonable(rec.soft_threshold(R)["errs"])
    out["krylov"] = jsonable(rec.krylov_compress(R)["errs"])
    out["rfeat"] = jsonable(rec.random_feature(R)["errs"])
    tower = rec.partition_tower(A, depth=4, r_schedule=(4, 8, 16, 24))
    out["tower"] = jsonable(tower["levels"])
    out["poly"] = dict(err=rec.polynomial_model(A_eq, R)["err"])
    sn = rec.steered_noise(R)
    out["steered"] = {str(k): dict(best=v["best_recon"], mean=v["mean_recon"],
                                   cov_res=v["cov_residual"])
                      for k, v in sn["per_rank"].items()}
    # where does R live: row/col mass concentration (Gini)
    rowmass = np.abs(R).sum(1)
    out["R_row_gini"] = float(gini(rowmass))
    out["R_concentration_top10pct"] = float(
        np.sort(np.abs(R).reshape(-1))[::-1][: max(1, R.size // 10)].sum()
        / (np.abs(R).sum() + 1e-12))
    return out, R, A_eq, A


def gini(x):
    x = np.sort(np.abs(x))
    n = len(x)
    if x.sum() == 0:
        return 0.0
    cum = np.cumsum(x)
    return float((n + 1 - 2 * (cum / cum[-1]).sum()) / n)


# ---------------------------------------------------------------------------
def fig_rsweep(results):
    plt.figure(figsize=(9, 6))
    for name, r in results.items():
        if name.startswith("_"):
            continue
        rs = [s["r"] for s in r["r_sweep"]]
        rel = [s["rel"] for s in r["r_sweep"]]
        plt.plot(rs, rel, marker="o", label=name)
    plt.xlabel("cells r (equitable base granularity)")
    plt.ylabel("||R||_F / ||A||_F")
    plt.title("Residual norm vs equitable-base granularity")
    plt.legend(fontsize=7, ncol=2)
    plt.grid(alpha=0.3)
    plt.tight_layout()
    plt.savefig(os.path.join(FIG, "01_residual_vs_r.png"), dpi=110)
    plt.close()


def fig_svd_decay(results):
    plt.figure(figsize=(9, 6))
    for name, r in results.items():
        if name.startswith("_"):
            continue
        s = np.array(r["svd"]["svals"])
        s = s / (s[0] + 1e-12)
        plt.semilogy(np.arange(1, len(s) + 1), s, marker=".", label=name)
    plt.xlabel("singular-value index of R (at r=%d)" % R_OP)
    plt.ylabel("sigma_i / sigma_1  (log)")
    plt.title("Singular-value decay of the residual R")
    plt.legend(fontsize=7, ncol=2)
    plt.grid(alpha=0.3)
    plt.tight_layout()
    plt.savefig(os.path.join(FIG, "02_svd_decay.png"), dpi=110)
    plt.close()


def fig_technique_compare(results):
    """For each matrix, plot reconstruction error vs cost for each technique."""
    names = [n for n in results if not n.startswith("_")]
    ncol = 3
    nrow = (len(names) + ncol - 1) // ncol
    fig, axes = plt.subplots(nrow, ncol, figsize=(5 * ncol, 3.5 * nrow))
    axes = np.array(axes).reshape(-1)
    for ax, name in zip(axes, names):
        r = results[name]
        # svd
        ks = sorted(int(k) for k in r["svd"]["errs"])
        ax.plot(ks, [r["svd"]["errs"][str(k)] for k in ks], "o-", label="SVD low-rank")
        # sparse
        fs = sorted(float(k) for k in r["sparse"])
        ax.plot([f * r["n"] * r["n"] for f in fs],
                [r["sparse"][str(f)] for f in fs], "s--", label="sparse (kept entries)")
        # krylov
        kk = sorted(int(k) for k in r["krylov"])
        ax.plot(kk, [r["krylov"][str(k)] for k in kk], "^-", label="Krylov dim")
        # random feature
        ff = sorted(int(k) for k in r["rfeat"])
        ax.plot(ff, [r["rfeat"][str(k)] for k in ff], "v-", label="random-feature width")
        ax.set_title(name, fontsize=8)
        ax.set_xlabel("cost (rank / dim / kept entries)")
        ax.set_ylabel("rel recon err")
        ax.set_ylim(-0.02, 1.05)
        ax.grid(alpha=0.3)
        ax.legend(fontsize=6)
    for ax in axes[len(names):]:
        ax.axis("off")
    fig.suptitle("Recovery of R: reconstruction error vs cost (at r=%d base)" % R_OP)
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, "03_technique_compare.png"), dpi=100)
    plt.close()


def fig_steered(results):
    """Steered-noise: best-of-n reconstruction AND covariance match vs rank."""
    names = [n for n in results if not n.startswith("_")]
    plt.figure(figsize=(10, 6))
    for name in names:
        st = results[name]["steered"]
        ks = sorted(int(k) for k in st)
        best = [st[str(k)]["best"] for k in ks]
        plt.plot(ks, best, marker="o", label=name)
    plt.axhline(1.0, color="k", ls=":", lw=1, label="||R|| (noise=0 baseline)")
    plt.xlabel("covariance rank k of steered noise")
    plt.ylabel("best-of-20 reconstruction rel-err of a single draw")
    plt.title("Steered noise: can a covariance-matched draw RECONSTRUCT R?")
    plt.legend(fontsize=7, ncol=2)
    plt.grid(alpha=0.3)
    plt.tight_layout()
    plt.savefig(os.path.join(FIG, "04_steered_noise.png"), dpi=110)
    plt.close()


def fig_heatmaps(samples):
    """A, A_eq, R side by side for a few representative matrices."""
    n = len(samples)
    fig, axes = plt.subplots(n, 3, figsize=(10, 3.2 * n))
    if n == 1:
        axes = axes.reshape(1, -1)
    for row, (name, (A, A_eq, R)) in enumerate(samples.items()):
        for col, (M, t) in enumerate([(A, "A"), (A_eq, "A_eq (r=%d)" % R_OP),
                                      (R, "R = A - A_eq")]):
            ax = axes[row, col]
            vmax = np.abs(M).max()
            im = ax.imshow(M, cmap="RdBu_r" if col == 2 else "viridis",
                           vmin=-vmax if col == 2 else 0, vmax=vmax)
            ax.set_title(f"{name}\n{t}", fontsize=8)
            ax.axis("off")
            fig.colorbar(im, ax=ax, fraction=0.046)
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, "05_heatmaps.png"), dpi=100)
    plt.close()


def fig_layer_localization(res_all, info):
    """Where does R live across LAYERS of the real model: rel residual + R rank
    + rank-collapse correlation (is R fat exactly when the core is rank-1?)."""
    L = info["n_layers"]
    H = info["n_heads"]
    rel = np.zeros((L, H))
    rankR = np.zeros((L, H))
    corerank = np.zeros((L, H))  # stable rank of A itself (rank-collapse proxy)
    svd_decay = np.zeros((L, H))  # rank99 of R
    bypos = {(d["layer"], d["head"]): d for d in res_all}
    for l in range(L):
        for h in range(H):
            A = bypos[(l, h)]["A"]
            d = decompose_at_r(A, R_OP)
            R = d["R"]
            rel[l, h] = np.linalg.norm(R) / (np.linalg.norm(A) + 1e-12)
            rankR[l, h] = np.linalg.matrix_rank(R, tol=1e-9)
            s = np.linalg.svd(A, compute_uv=False)
            corerank[l, h] = (s.sum() ** 2) / (np.sum(s ** 2) + 1e-12)  # participation
            sv = rec.svd_truncation(R)
            svd_decay[l, h] = sv["rank99"]
    fig, axes = plt.subplots(2, 2, figsize=(12, 9))
    for ax, (M, t) in zip(axes.reshape(-1), [
            (rel, "||R||/||A||  (residual mass)"),
            (rankR, "rank(R)"),
            (svd_decay, "rank99(R)  (rank to 99% energy)"),
            (corerank, "participation ratio of A (low => rank-collapsed core)")]):
        im = ax.imshow(M, aspect="auto", cmap="magma")
        ax.set_xlabel("head")
        ax.set_ylabel("layer")
        ax.set_title(t, fontsize=10)
        fig.colorbar(im, ax=ax)
    fig.suptitle("SmolLM2-135M: where R lives across layers/heads")
    fig.tight_layout()
    fig.savefig(os.path.join(FIG, "06_layer_localization.png"), dpi=100)
    plt.close()
    # rank-collapse hypothesis test: corr(rel residual, core rank-collapse)
    flat_rel = rel.reshape(-1)
    flat_core = corerank.reshape(-1)
    corr = float(np.corrcoef(flat_rel, flat_core)[0, 1])
    return dict(rel=jsonable(rel), rankR=jsonable(rankR),
                corerank=jsonable(corerank),
                corr_rel_vs_corerank=corr,
                mean_rel=float(rel.mean()), mean_rankR=float(rankR.mean()),
                mean_rank99R=float(svd_decay.mean()))


# ---------------------------------------------------------------------------
def main():
    print("collecting matrices...")
    mats = collect_matrices()
    results = {}
    samples = {}
    sample_names = ["synth/block_equitable", "synth/induction",
                    "synth/rank1_collapse", "synth/hierarchical"]
    for name, d in mats.items():
        if name.startswith("_"):
            continue
        print("characterizing", name)
        out, R, A_eq, A = characterize_one(name, d["A"])
        out["kind"] = d["kind"]
        results[name] = out
        if name in sample_names or (d["kind"] == "real" and len(samples) < 6):
            samples[name] = (A, A_eq, R)

    # layer localization on the real model (rank-collapse test)
    layerstats = None
    if "_smollm_all" in mats:
        print("layer localization sweep (real model)...")
        layerstats = fig_layer_localization(mats["_smollm_all"], mats["_smollm_info"])

    print("figures...")
    fig_rsweep(results)
    fig_svd_decay(results)
    fig_technique_compare(results)
    fig_steered(results)
    fig_heatmaps(samples)

    payload = dict(results=results, layerstats=layerstats,
                   config=dict(N=N, R_OP=R_OP, R_SWEEP=R_SWEEP))
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(jsonable(payload), f, indent=2)
    print("done -> results.json")


if __name__ == "__main__":
    main()
