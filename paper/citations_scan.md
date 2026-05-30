# Citations Scan — prior art & novelty confirmations for Graphplay

Literature scout pass (Kagi Search API, 2026-05-30). Goal: ground/challenge our
quantum-walk / equitable-partition claims and confirm where we are genuinely
filling a gap. Honest-novelty flags are called out per cluster.

Cross-references to our files use the in-repo paths under `Graphplay/`. Format:
`- **Title** — url — one-line what-it-shows`.

---

## Cluster 1 — CTQW spatial search beyond K_n

- **Spatial search by quantum walk (Childs & Goldstone, 2003/2004)** — https://arxiv.org/abs/quant-ph/0306054 (PRA 70, 022314) — the foundational CTQW spatial-search paper; O(√N) search on the complete graph and hypercube, exactly the host we lift in `Applications/SparseSearch.lean`.
- **Global Symmetry is Unnecessary for Fast Quantum Search (Janmark, Meyer, Wong, 2014)** — https://link.aps.org/doi/10.1103/PhysRevLett.112.210502 (arXiv:1403.2228) — CTQW search on strongly-regular graphs is optimal; the state evolves in a *3-dimensional* invariant subspace from a *local* symmetry, i.e. an equitable partition rather than a global automorphism. This is essentially our "equitable-quotient collapses the search" thesis, stated for SRGs.
- **Spatial Search by Quantum Walk is Optimal for Almost all Graphs (Chakraborty, Novo, Ambainis, Omar, 2016)** — https://link.aps.org/doi/10.1103/PhysRevLett.116.100501 — O(√N) optimality for almost all graphs; the genericity backdrop for our K_n / hypercube special cases.
- **On the optimality of spatial search by CTQW (Chakraborty, Novo, Roland, 2020)** — https://arxiv.org/abs/2004.12686 (PRA 102, 032214) — the CNO spectral-ratio necessary-and-sufficient condition we formalize verbatim in `Search/CNO.lean` (the `sorry`-ed Theorem 1–2).
- **Efficient circuit implementations of CTQW for spatial search (2024)** — https://pmc.ncbi.nlm.nih.gov/articles/PMC12109817/ — explicit circuits compiling CTQW search evolution operators for graph families; relevant to our "compile ML primitives onto real chips" ambition (`Toolkit/Hardware.lean`).

**Relevance to Graphplay.** This cluster is almost entirely **PRIOR ART that we
must cite**, and our files already do (Childs–Goldstone and CNO are named in
`Applications/SparseSearch.lean` and `Search/CNO.lean`). The Janmark–Meyer–Wong
SRG result is the most important overlap to be honest about: our headline framing
— "a *local* equitable partition, not a global automorphism, is what makes search
collapse to a low-dim quotient" — is *exactly their 2014 message* (3-dim subspace
from local symmetry). Our contribution is therefore a **machine-checked
formalization and a uniform equitable-quotient packaging** of an idea that is
established physics, NOT a new search result. The `hammingPartition_equitable`
core of `SparseSearch.lean` is a formalization of Childs–Goldstone hypercube
structure; the CNO ratio criterion in `CNO.lean` is an explicitly-attributed
`sorry`. Claim posture: formalization/extension, not novelty.

---

## Cluster 2 — Quantum walks ↔ ML / transformers

- **GQWformer: A Quantum-based Transformer for Graph Representation Learning (Zhejiang Lab, 2024)** — https://arxiv.org/abs/2412.02285 — embeds *continuous quantum walks on attributed graphs* as inductive bias to generate attention scores in a graph transformer. Direct prior art for "attention as a quantum walk."
- **CTQWformer: A CTQW-based Transformer for Graph Classification (2026)** — https://arxiv.org/html/2605.09486v1 — uses CTQW final-time propagation probabilities as structural encodings inside a transformer. Closest existing instantiation of the exact phrase "CTQW + transformer."
- **Quantum Adaptive Self-Attention (QASA, 2025)** — https://arxiv.org/html/2504.05336v3 — replaces the attention value-projection with a parameterized quantum circuit; representative of the hybrid quantum-attention literature aimed at reducing attention's compute overhead.
- **QSAN: A Near-term Achievable Quantum Self-Attention Network** — https://inspirehep.net/literature/2115384 — quantum self-attention for image classification on NISQ devices.
- **Quantum ML: read the fine print (Aaronson)** — https://www.scottaaronson.com/papers/qml.pdf — the standard caveat paper on HHL-style QML "exponential speedups" (state-prep, readout, condition-number caveats). The honesty anchor we should cite next to any speedup claim in `Integrations/MachineLearning.lean`.

**Relevance to Graphplay.** This is the cluster with the **sharpest
novelty-overlap risk** for `Integrations/MachineLearning.lean` and
`Integrations/AttentionComplexity.lean`. GQWformer (2024) and CTQWformer (2026)
already marry quantum walks to transformer attention — so the bare claim "we
bridge attention and quantum walks" is **NOT novel**; it is established and must
be cited (neither is currently referenced — `MachineLearning.lean` only cites HHL
at line 63). HOWEVER, our actual contribution is *orthogonal* to theirs and the
gap is real: GQWformer/CTQWformer use the walk as a *heuristic feature/inductive
bias* (no proven speedup, no exactness guarantee). Graphplay instead proves an
**exact** structural identity — `blockAttentionApply_eq_fullAttentionApply`
(sorry-free), `EquitablePartition.restrict_eq_symmQuotient`, and the O(n²)→O(n·r)
operation-count theorems — i.e. a *machine-checked exact-reduction certificate*
under an equitable/equivariant attention pattern, plus the quotient-search lift
giving O(√r) independent of host size. **CONFIRMS a gap we fill** (verified exact
compression + complexity), while we must **honestly cite** GQWformer/CTQWformer as
prior art for the walk-attention connection itself, and cite Aaronson/QML and HHL
to scope the linear-algebra speedup claims.

---

## Cluster 3 — Equitable-partition / quotient walks

- **Perfect state transfer on quotient graphs (Bachman, Fredette, Fuller, Landry, Opperman, Tamon, Tollefson, 2012)** — https://arxiv.org/abs/1108.0339 (QIC 12, 293) — *G* has PST iff its quotient *G/π* under any equitable partition has PST; constructs PST graphs lacking the swapping automorphism. This is the exact "quotient-iff" spine theorem of `PST/QuotientIff.lean`.
- **PST, equitable partition and CTQW-based search (2022/2024)** — https://arxiv.org/abs/2209.07688 (Quantum Stud. Math. Found.) — uses equitable partition + PST to compute search success probability and runtime; the direct prior art unifying our PST-quotient and search-quotient bridges.
- **State Transfer on Graphs (Godsil, 2011 survey)** — https://arxiv.org/abs/1102.4898 (Discrete Math. 312) — the canonical PST survey; the reference frame for `PST/Cospectrality.lean`, `PST/GodsilRatio.lean`.
- **Perfect state transfer in Laplacian quantum walk (Alvir, Dever, Lovitz, Myer, Tamon, Xu, Zhan, 2014)** — https://arxiv.org/abs/1409.5840 — Laplacian-walk PST closure properties (products, complements); backs `Loopy/Laplacian.lean` and `Product/PST.lean`.
- **Continuous-time quantum walks on graphs: Group State Transfer (Godsil/Lato et al.)** — https://par.nsf.gov/servlets/purl/10580610 — generalizes PST to transfer between *subspaces/group orbits*, the natural language for our cell-uniform-subspace lifts.

**Relevance to Graphplay.** Entirely **PRIOR ART we must cite**, and the most
load-bearing for the project spine. The quotient-iff theorem (Bachman–Tamon et
al. 1108.0339) is precisely what `PST/QuotientIff.lean` formalizes — our claim
there is a *Lean formalization* of an existing theorem, **not** a new
mathematical result, and the file should make that attribution explicit. The
2209.07688 paper (equitable partition + PST + CTQW search) is arguably the single
closest prior work to the whole Graphplay thesis and should be cited prominently
in `Integrations/QuantumAdvantage.lean` and `Applications/SparseSearch.lean`.
Godsil's survey and the Laplacian-PST closure paper ground `PST/*` and
`Product/PST.lean`. Posture: we are the **verified formalization** of the Tamon–
Godsil equitable-quotient PST corpus; novelty is in the mechanization + uniform
spine, not the theorems.

---

## Cluster 4 — Hardware realization

- **Perfect state transfer on a spin chain without state initialization (Di Franco, Paternostro, Kim, 2008)** — https://link.aps.org/doi/10.1103/PhysRevLett.101.230502 — engineered XX spin chain achieving PST with only end-chain control; the canonical hardware-PST proposal.
- **Parity-dependent state transfer / PST on six superconducting transmons with tunable couplers (Nature Commun., 2025)** — https://www.nature.com/articles/s41467-025-57818-2 — *experimental* PST and multi-qubit entanglement on a real superconducting chain; the strongest evidence that our PST chains are physically realizable today.
- **How to construct spin chains with perfect state transfer (Vinet & Zhedanov, 2012)** — https://arxiv.org/abs/1110.6474 — systematic construction of nearest-neighbor XX chains with PST (Krawtchouk/binomial couplings) — the same binomial-path structure as our collapsed Hamming chain in `SparseSearch.lean`.
- **The IBM Quantum heavy-hex lattice (IBM, 2021)** — https://www.ibm.com/quantum/blog/heavy-hex-lattice — primary source for the heavy-hex connectivity skeleton disassembled in `Applications/IBMHeavyHex.lean`.
- **Observing and braiding topological Majorana modes on a superconducting processor (Nature Commun., 2023)** — https://www.nature.com/articles/s41467-023-37725-0 — simulated MZMs + braiding on real hardware; the realistic backdrop for the speculative `Applications/MajoranaOne.lean` (note: this is a *simulator* of MZMs, not native topological qubits — relevant honesty caveat).

**Relevance to Graphplay.** Mixed **PRIOR ART + confirmation**. The spin-chain PST
papers (Di Franco 2008, Vinet–Zhedanov 2012) are prior art for the *physical
realizability* premise of `SparseSearch.lean` and the PST tower; the binomial/
Krawtchouk coupling structure they engineer is the same object as our collapsed
Hamming chain, so we should cite Vinet–Zhedanov specifically there. The 2025
six-transmon PST experiment **confirms** the buildability claim that motivates the
"sparse, physically-realizable host" framing — strong support, cite it. IBM
heavy-hex blog grounds `IBMHeavyHex.lean` (already cited internally). For
`MajoranaOne.lean`, the 2023 braiding-on-superconductors result is the honest
state of the art (MZMs simulated, not natively realized) and reinforces that file's
own "speculative / stretch-demo" framing — there is **no** prior art doing an
equitable-partition spectral disassembly of Majorana-1, so that specific modeling
exercise is novel (though unverified physically).

---

## Cluster 5 — ML-as-walk primitives

- **Experimental quantum stochastic walks simulating associative memory of Hopfield networks (2019)** — https://link.aps.org/doi/10.1103/PhysRevApplied.11.024020 (arXiv:1901.02462) — open-system (Lindblad/stochastic) quantum walks implementing Hopfield associative memory; prior art linking quantum walks to ML memory primitives, and it connects to our `Graphon/Lindblad.lean` / `NoiseEquitable.lean` open-system layer.
- **A quantum Hopfield associative memory on actual quantum hardware (Sci. Rep., 2021)** — https://www.nature.com/articles/s41598-021-02866-z.pdf — HHL-based quantum Hopfield memory run on a real device; the ML-primitive-as-quantum-linear-algebra angle of `Integrations/MachineLearning.lean`.
- **BBBV optimality of Grover search (Bennett, Bernstein, Brassard, Vazirani)** — https://www.scottaaronson.com/qclec/23.pdf — the Ω(√N) quantum query lower bound; the matching lower bound for our `quantum_search_quadratic_advantage` separation in `Integrations/QuantumAdvantage.lean`.
- **Thermodynamic limit of spin systems on random graphs via graphons (PRResearch 6, 013011, 2024)** — https://link.aps.org/doi/10.1103/PhysRevResearch.6.013011 — uses graphons as the continuum limit of dense quantum spin systems; the closest physics prior art to our `Graphon/Limit.lean` CTQW-graphon-limit construction.
- **Graphon Quantum Filtering Systems (2025)** — https://arxiv.org/pdf/2506.12249 — mean-field/graphon limit of interacting quantum systems with blockwise (equitable!) interactions; directly parallels `Graphon/Equitable.lean` + `Integrations/MeanFieldGames.lean`.

**Relevance to Graphplay.** Mixed, with two honesty flags. (1) The Hopfield/
associative-memory walk papers are **prior art for "quantum walk as an ML
primitive"** — if Graphplay ever claims the walk-as-memory idea as novel, that
would be wrong; our angle (equitable reduction of the memory operator) is the
differentiator. (2) BBBV is **prior art we must cite** as the lower bound making
our K_n separation honest — `QuantumAdvantage.lean` proves a clean *classical*
counting lower bound but the *quantum* Ω(√N) optimality it implicitly relies on is
BBBV; cite it explicitly. (3) The graphon-quantum papers (PRResearch 2024;
arXiv:2506.12249) are the **most important novelty check for Tower-4**: people are
already using graphons as limits of *quantum* spin systems, including the
blockwise/equitable case. So "graphon limit of quantum walks" is **not a brand-new
object** — our contribution is the *equitable-partition-preserving CTQW limit with
a machine-checked op-intertwining/PST lift* (`Graphon/Limit.lean`,
`Graphon/PST.lean`), which appears genuinely un-done elsewhere, but the framing
must cite the 2024/2025 graphon-quantum work as the surrounding prior art rather
than claim the limit construction itself as new.

---

## Summary — honest-novelty ledger

**Must-cite prior art that overlaps our framing (our claim = formalization, not new math):**
1. Bachman–Tamon et al. 2012 (quotient-iff PST, arXiv:1108.0339) ↔ `PST/QuotientIff.lean` — the spine theorem is a known result we mechanize.
2. Janmark–Meyer–Wong 2014 (local symmetry ⇒ low-dim search subspace) ↔ `Applications/SparseSearch.lean` — our "equitable-not-automorphism" search collapse is their established idea.
3. GQWformer 2024 / CTQWformer 2026 (quantum walk ↔ transformer attention) ↔ `Integrations/MachineLearning.lean` — the bare walk-attention bridge is already done; currently UNCITED in our files. Our differentiator is the *exact verified reduction*, not the bridge.
4. CNO 2020 (arXiv:2004.12686) ↔ `Search/CNO.lean` — already attributed; the headline theorem is their result (our `sorry`).
5. "PST + equitable partition + CTQW search" 2022/2024 (arXiv:2209.07688) — closest single prior work to the whole thesis; should be cited prominently and is the strongest "someone already did the synthesis" flag.

**Gaps we genuinely fill (novelty confirmations):**
- Machine-checked **exact** equitable-attention compression with proven op-counts (`AttentionComplexity.lean`, `blockAttentionApply_eq_fullAttentionApply`) — the QML-walk-transformer literature gives heuristics, not certificates.
- Verified equitable-partition-preserving **CTQW graphon limit + PST/op-intertwining lift** (`Graphon/Limit.lean`, `Graphon/PST.lean`) — graphon-quantum limits exist (2024/2025) but not this verified equitable-walk version.
- Equitable-partition **spectral disassembly of real chips** (IBM heavy-hex, Majorana-1) — no prior art does this specific modeling.

**Recommended citation additions to source files:** add GQWformer/CTQWformer + Aaronson-QML to `MachineLearning.lean`; add arXiv:2209.07688 to `QuantumAdvantage.lean` and `SparseSearch.lean`; add Janmark–Meyer–Wong to `SparseSearch.lean`/`CNO.lean`; add BBBV to `QuantumAdvantage.lean`; add Vinet–Zhedanov + the 2025 six-transmon PST experiment to `SparseSearch.lean`; add the graphon-quantum (PRResearch 2024 / 2506.12249) refs to `Graphon/Limit.lean`.
