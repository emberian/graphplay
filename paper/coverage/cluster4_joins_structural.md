# Cluster 4 coverage audit — joins/corona/product, structural, deterministic-search, graphons

Auditor scope: capture in Graphplay of the 13 papers below. Lean modules consulted:
`Graphplay/Bundle.lean`, `Graphplay/Search.lean`, `Graphplay/StdLib/CompleteMultipartite.lean`,
`Graphplay/StdLib/Cayley.lean`, `Graphplay/Dowsing/{BundlePSTLift,FractionalRevivalNC,Conjecture93,FilteredColimitPST}.lean`,
`Graphplay/Graphon/{Limit,Spectrum,Lindblad}.lean`, `Graphplay/Integrations/MeanFieldGames.lean`,
`Graphplay/Examples/HeawoodOnTorus.lean`. Legend: ✅ captured · ⚠️ partial · ❌ not captured.

---

### arXiv:0909.0431 — PST in weighted join graphs (Angeles-Canul et al.)
**Key theorems/constructions:**
1. Weighted join theorem (Thm 1): PST in `G̃₁(μ₁,η₁) +ρ G̃₂(μ₂,η₂)` reduces to PST in the unweighted `G₁` plus a closed-form double-cone correction term in `δ=κ₁−κ₂`, `Δ=√(δ²+4n₁n₂)`.
2. Weighted double-cone corollary (Cor 2): for any `k`-regular `G`, weights `μ,η` exist so `K̃₂ᵇ(μ,η)+G` has PST between the two `K₂` vertices.
3. Half-join no-go (Thm 3 / Cor 4): the double half-cone `K₂` ⋈ `(G+G)` (and weighted `K_{n,n}`) has **no** PST for any real weights — weights don't help in complete bipartite.
4. Weighted Cartesian-product closure (Thm 5): PST closes under `⊕` even with per-factor times `tⱼ=ηⱼt⋆`.
5. Hamming-graph universal PST (Thm 6) and arbitrary-subcube PST on the weighted `n`-cube (Thm 8).

**Captured in Graphplay?** ⚠️ partial. The *bundle/equitable* skeleton is present: `Bundle.fiberPartition` + `BundlePSTLift.{master,cartesian,lex}` give the regular-fiber/biregular-coupling PST-lift that subsumes the join (`J`-coupling) and Cartesian (`I`-coupling) cases as quotient theorems. `StdLib/Hamming.lean` exists. But the **weighted-self-loop double-cone closed form** (Thm 1 amplitude, the `δ/Δ` number-theoretic PST condition) is *not* stated, and the **half-join no-go** (Thm 3) is entirely absent.

**Gaps to close:**
- `Graphplay/StdLib/Join.lean`: `def weightedDoubleCone (G : WeightedGraph V) (k μ η : ℝ) : WeightedGraph (Unit⊕Unit ⊕ V)` and `theorem weightedDoubleCone_PST_iff` — PST ↔ `Δ:=√(δ²+8n)∈ℤ ∧ δ/4η,Δ/4η∈ℤ` with parity matching `b` (Cor 2).
- `theorem halfJoin_no_PST (G regular) : ¬ IsPST (doubleHalfCone …) …` (Thm 3); corollary `completeBipartite_weighted_no_PST` (Cor 4).
- `theorem weightedCartesian_pst_closure` with per-factor transfer times (Thm 5) — generalizes the equal-time `BundlePSTLift.cartesian`.

---

### arXiv:0907.2148 — PST, integral circulants and join of graphs (Angeles-Canul et al.)
**Key theorems/constructions:**
1. Circulant join `G +_C G` (adj `[[A,C],[Cᵀ,A]]`); Thm 1: PST lifts iff `[cos(t⋆√B)]^{1−s}[sin(t⋆√B)B^{-1/2}Cᵀ]=±I`, `B=CᵀC`; circulant iff `C` palindrome. Interpolates bunkbed (`C=I`) and join (`C=J`).
2. New integral circulants `ICG_{2n}(2D∪Q)` with PST (Thm 4; Cor 5).
3. Heterogeneous Cartesian-product PST closure (Thm 7); `m`-fold self-join reduction (Thm 9, Cor 10/11).
4. Join of two arbitrary regular graphs (Thm 12): same `δ,Δ` reduction as 0909.0431 Thm 1, unweighted.
5. Non-periodic double-cone PST family `K̄₂+(C_{2(2ℓ−1)}□C_{2ℓ+1})` (Cor 14) — answers Godsil.

**Captured in Graphplay?** ⚠️ partial. `StdLib/Cayley.lean` captures the **integral-circulant / unitary-Cayley PST characterization** (Bašić–Petković–Stevanović, `cayley_abelian_PST_iff_rationalEigenvalues`, `cycle_PST_iff`, order-≤32 enumeration) — this is the abelian backbone. The Cartesian/self-join closure is the `BundlePSTLift` material. **Not captured:** the circulant-join operator `+_C`, the `cos/sin(t√B)` lift condition (Thm 1), the `ICG_{2n}(2D∪Q)` construction (Thm 4), and the non-periodic double-cone family (Cor 14).

**Gaps to close:**
- `Graphplay/StdLib/CirculantJoin.lean`: `def circulantJoin (A C : Matrix (ZMod n) (ZMod n) ℂ) : …`; `theorem circulantJoin_PST` (Thm 1 lift condition); `theorem circulantJoin_isCirculant_of_palindrome`.
- `def ICG (n : ℕ) (D : Finset ℕ) : WeightedGraph (ZMod n)` + `theorem ICG_2n_PST` (Thm 4) in `StdLib/Cayley.lean`.
- `theorem nonperiodic_doubleCone_PST` — `K̄₂+(C_a□C_b)` PST yet non-periodic (Cor 14); needs a `Periodic` predicate + a `λ-ratio∉ℚ` witness.

---

### arXiv:1605.05260 — Quantum State Transfer in Coronas (Ackelsberg–Brehm–Chan–Mundinger–Tamon)
**Key theorems/constructions:**
1. Corona spectrum + eigenprojectors (Prop 3.2/3.3): for `H` `k`-regular, `G∘H` eigenvalues `½(λ+k±√((λ−k)²+4m))`; transition-element formula.
2. Periodicity obstruction (Lem 4.2, Thm 4.3, Cor 4.4): periodic vertex needs `λ−k, √((λ−k)²+4m) ∈ ℤ√Δ`; eigenvalues "can't be too close" ⇒ no PST for `Q_d∘H`, `nK₂∘H`, halved cubes (Cor 4.5); no PST for `G∘K_m`, `G∘K̄_m` (m prime) (Thm 4.7/4.10).
3. Barbell PGST `K₂∘K_m` for all `m` (Thm 5.1); `(K_n+I)∘K̄₂` PGST (Thm 5.3); `(K_n□K₂)∘K̄₂` PGST (Thm 5.4).
4. Thorny-graph PGST `G∘K₁` from PST-at-`π/g` (Thm 5.5) ⇒ thorny cube `Q_d∘K₁` PGST.
5. Multigraph digon `C₂∘K̄_m` PST when `m+1` even square (Prop 4.11, Thm 4.12) — real PST between subsets.

**Captured in Graphplay?** ❌ not captured. There is **no corona construction anywhere in the Lean tree** (only paper-notes prose in `paper/tamon_corpus_expansion.md`). PGST itself has no dedicated predicate (only `IsPST`/`IsFR`). Kronecker-approximation machinery is absent.

**Gaps to close:**
- `Graphplay/StdLib/Corona.lean`: `def corona (G : WeightedGraph V) (H : WeightedGraph W) : WeightedGraph (V × (Unit⊕W))` (adj per (10)); `theorem corona_spectrum_of_regular` (Thm 3.1/Prop 3.2).
- `def IsPGST` predicate (limit-of-fidelity-1) in `Graphplay/PST.lean`; `theorem barbell_PGST` (Thm 5.1), `theorem thorny_PGST_of_PST` (Thm 5.5).
- `theorem corona_no_PST_close_eigenvalues` (Thm 4.3) and `theorem corona_complete_no_PST` (Thm 4.7/4.10).
- Supporting `Graphplay/ForMathlib/Kronecker.lean`: Kronecker approximation theorem + `Richards`/`Newman–Flanders` Q-linear-independence of `√(squarefree)` (used by 1605, 1508).

---

### arXiv:1508.05458 — Laplacian State Transfer in Coronas (Ackelsberg–Brehm–Chan–Mundinger–Tamon)
**Key theorems/constructions:**
1. Inhomogeneous corona `G∘(H₁,…,H_n)` Laplacian spectrum + eigenprojectors (Prop 3.2): `λ±=½(m+λ+1±√((m+λ−1)²+4m))`.
2. **No Laplacian PST** in any corona with `|G|≥2` (Thm 4.1) — no integer eigenvalues in support.
3. Laplacian PGST sufficient condition (Thm 5.2): `G` has PST, `2^{r+1}∣m+1` ⇒ `G∘H⃗` PGST. ⇒ `Q_d∘H⃗` PGST when `m≡3 (4)`.
4. `K₂∘H⃗` Laplacian PGST for all `m` (Thm 5.3) — double-star, no number-theoretic condition (contrast adjacency).
5. Cocktail-party `nK₂∘K₁` Laplacian PGST (Thm 5.5) though `nK₂` (odd `n`) has no PST.

**Captured in Graphplay?** ❌ not captured. Same as 1605: no corona, no Laplacian-PST/PGST predicate. `StdLib/CompleteMultipartite.lean` has a `laplacian` def reusable as a building block, but nothing about corona Laplacians or Laplacian PST.

**Gaps to close:**
- Reuse `Corona.lean`; add `def IsLaplacianPST` / `IsLaplacianPGST` (walk by `exp(-itL)`).
- `theorem corona_no_laplacian_PST (|G|≥2)` (Thm 4.1).
- `theorem corona_laplacian_PGST_of_PST` with the `2^{r+1}∣m+1` hypothesis (Thm 5.2); `theorem doubleStar_laplacian_PGST` (Thm 5.3); `theorem cocktail_corona_PGST` (Thm 5.5).

---

### arXiv:1911.01953 — A note on quantum Markov models (Tamon–Xie)
**Key theorems/constructions:**
1. Quantum Moore vs. Mealy machine models (conditional channel + quantum instrument); equivalence (Thm 3.6) via Kraus decoupling.
2. QOMDP as MDP over density-matrix Borel space; reward reduction to current-state (Prop 4.4).
3. Quantum Reachability undecidable (Thm 5.2), with τ=1 undecidable (Barry et al., Thm 5.3); Quantum Non-Occurrence undecidable (Cor 5.5/Thm 5.6).
4. `D(S)` is a Borel set (Prop 6.4) ⇒ optimal stationary policy exists (Thm 6.5, via Blackwell).
5. **Headline:** Quantum Approximate-Optimal-Policy (discounted reward) is **decidable** (Thm 6.8) via Banach-fixed-point value iteration; value function is piecewise-linear-convex (Thm 6.6).

**Captured in Graphplay?** ❌ not captured. No QOMDP, quantum transducer, decidability, or MDP/policy material anywhere in the tree. (Flagged in task prompt as likely uncaptured — confirmed.)

**Gaps to close:**
- `Graphplay/QuantumMarkov.lean`: `structure QOMDP` (states `S`, channels `Λ`, reward operators, discount `γ`); `structure QuantumMooreMachine` / `QuantumMealyMachine`; `theorem moore_mealy_equiv` (Thm 3.6).
- `theorem densityMatrices_isBorel` (Prop 6.4) — leans on Mathlib `Mat d ℂ` metric/closed lemmas.
- `theorem optimalPolicy_exists` (Thm 6.5), `theorem valueFunction_PWLC` (Thm 6.6), `theorem approxOptimalPolicy_decidable` (Thm 6.8) — Bellman operator `T`, `γ`-contraction via `ContractingWith`/`Banach fixed point` already in Mathlib.

---

### arXiv:2508.06611 — Matrix inversion by quantum walk (Kay–Tamon)
**Key theorems/constructions:**
1. Embed (possibly non-square) `A` into a sparse Hermitian `H` (4-block); weak coupling `γ1`; degenerate perturbation theory makes the near-0 subspace evolve by `H^{-1}` ⇒ produces `|x⟩∝A^{-1}|b⟩`.
2. Basic protocol: evolve `t=2π/γ`, post-select; `‖|x⟩−|ψ⟩‖∼γκ²`, runtime `O(κ²)` matching HHL.
3. Block-extension to `(R+1)×(R+1)` `h₊` suppresses high-energy sector to `O(γ^{2R})`; LCU/odd-power cancellation ⇒ accuracy `O(γ^R κ^{R+1})`, `R∼log(1/ε)`.
4. Conjecture 1: coupling strengths `{Jₙ}` give one-shot evolution `(⟨2R+2|⊗1)e^{-iHt}(|1⟩⊗|b⟩)∝γ|x⟩+O(γ^{2R}κ^{2R})`; Table I numerical solutions `R≤6`.
5. Krawtchouk-chain / PST-as-constructive-tool reuse (Kay review) — same weighted-chain inverse-eigenvalue machinery.

**Captured in Graphplay?** ❌ not captured. No HHL / matrix-inversion / weak-coupling-perturbation content. The PST-chain inverse-eigenvalue tooling that 2508 reuses is also not present (see 2507 below). (Flagged in prompt — confirmed.)

**Gaps to close:**
- `Graphplay/Algorithm/MatrixInversionQW.lean`: `def embedHamiltonian (A : Matrix m n ℂ) (γ : ℝ) : Matrix … ℂ`; `theorem matrixInversion_leadingOrder` (αₙ∝γ/λₙ); `theorem matrixInversion_accuracy (R) : ‖|ψ⟩−|x⟩‖ ≤ C·γ^R κ^{R+1}`.
- Shared with 2507: `def krawtchoukChain`, inverse-eigenvalue (Lanczos) reconstruction from a symmetric odd-gap spectrum.

---

### arXiv:2507.18872 — Optimising PST for timing insensitivity (Kay–Kim–Tamon)
**Key theorems/constructions:**
1. Figure of merit `F̃ₑ≈∫p(δt)(1−½δt²⟨1|H₀²|1⟩)` ⇒ minimise first coupling `J₁²=⟨1|H₀²|1⟩` (field-free tridiagonal, symmetric PST chain).
2. Improved Mandelstam–Tamm bound (Thm 1): for length `N≥4`, `J₁²≥(πα/2t₀)²`, `α=2` (even) or `√3` (odd); length-4/5 Krawtchouk chains are optimal.
3. T-Rex construction: keep `R` central evenly-spaced eigenvalues, push the other `N−R` to `O(γ)` ⇒ arrival profile `sin^{2(R−1)}` (vs. Krawtchouk `sin^{2(N−1)}`); asymptotically optimal `R=4/5`.
4. Robustness to manufacturing perturbations; encoded transfer via singular vectors of `Π_B e^{-iH₀t}Π_A`.
5. Time-insensitive fractional revival: modify central two couplings `J→√2 J cos/sin θ` (Thm/method of Genest–Vinet–Zhedanov).

**Captured in Graphplay?** ⚠️ partial (only the FR *kinematics*). `Dowsing/FractionalRevivalNC.lean` captures fractional-revival on weighted graphs + association schemes (Chan–Coutinho–Tamon–Vinet–Zhan 1907.04729): `IsFR`, `isPST_of_isFR`, `bose_mesner_fr_iff`, cell-uniform FR + lifting. **Not captured:** Krawtchouk chains, the `J₁²=⟨1|H₀²|1⟩` figure-of-merit, Mandelstam–Tamm timing bound, the T-Rex spectral-engineering construction, or encoded/timing-insensitive transfer.

**Gaps to close:**
- `Graphplay/StdLib/Chain.lean`: `def krawtchoukChain (N : ℕ) (J : ℝ)` with `Jₙ=J√(n(N−n))`; `theorem krawtchouk_PST`.
- `Graphplay/Algorithm/TimingInsensitivePST.lean`: `def firstCouplingFOM (H₀) := ⟨1|H₀²|1⟩`; `theorem mandelstam_tamm_PST_bound` (Thm 1); `def tRexChain (N R : ℕ) (γ : ℝ)` via inverse-eigenvalue solve + `theorem tRex_arrival_profile` (`sin^{2(R−1)}`).
- Connect to `FractionalRevivalNC`: `theorem tRex_fractionalRevival` (central-couplings modification).

---

### arXiv:2506.21108 — Deterministic search on Laplacian-integral graphs (Li–Luo–Feng–Li)
**Key theorems/constructions:**
1. **Main (Thm 1):** for *any* Laplacian-integral graph (any predetermined marked-fraction `ε`), a CIQW algorithm finds a marked vertex with certainty in evolution time and query complexity `O(1/√ε)`.
2. Mechanism: QPE on `e^{iLt}` separates the 0-eigenvalue `|π⟩` exactly ⇒ perfect phase shift `e^{iβ|π⟩⟨π|}` ⇒ Long's zero-failure Grover (Lem 1, `G(α,β)=e^{iβ|π⟩⟨π|}e^{iαΠ_M}`).
3. Improves Wang et al. [7] (alternating walks): removes vertex-transitivity, the `2^{d_L}` depth factor, and the single-marked-vertex restriction.
4. Worked Laplacian-integral families: antiregular `A_N`, Johnson, Hamming/hypercube, Kneser, Grassmann, Rook, complete-multipartite, cocktail-party, star (Appendix A).
5. Gate complexity dominated by `e^{iLt}` simulation; `O(poly log N/√ε)` when CTQW is efficient (Thm 3).

**Captured in Graphplay?** ⚠️ partial **and mis-attributed.** `StdLib/CompleteMultipartite.lean` cites 2506.21108 but **describes it incorrectly** — it claims the paper is about CTQW-Grover on *complete multipartite graphs* with a single marked vertex at `τ=π/(2√(d−λ₂))`. The real paper is the *general* Laplacian-integral CIQW result above (complete-multipartite is just one Appendix-A example). The Lean file does correctly capture (statement-only, `sorry`) Laplacian-integrality of `K_{n₁,…,n_k}` and a deterministic-search theorem for that family; `Search.lean` has the Childs–Goldstone search Hamiltonian + marked-refined equitable-partition quotient (orthogonal CTQW search line).

**Gaps to close:**
- **Fix the citation** in `CompleteMultipartite.lean` (the `τ`, "complete multipartite", single-marked claims are wrong for 2506.21108).
- `Graphplay/Algorithm/DeterministicSearch.lean`: `def IsLaplacianIntegral (G)`; `def CIQW …`; `theorem deterministic_search_laplacian_integral (G) (hLI) (M) (ε) : ∃ algorithm, success_prob = 1 ∧ time = O(1/√ε)` (Thm 1).
- `def longGroverIteration` + `theorem long_zero_failure` (Lem 1); `theorem perfect_phase_shift_via_QPE` (the `e^{iβ|π⟩⟨π|}` construction).
- `theorem antiregular_laplacian_spectrum` (`{0..n}∖{⌊(N+1)/2⌋}`) as a non-vertex-transitive Laplacian-integral example.

---

### arXiv:math0109191 — Heawood-type result for algebraic connectivity on surfaces (Freitas)
**Key theorems/constructions:**
1. **Main (Thm 3.1):** for genus-`γ`, nonpositive-`χ` graphs, `a(G) ≤ a(K^γ) = H(S) = ⌊(7+√(49−24χ))/2⌋`, equality iff `G=K^γ` (except Klein bottle). Cor 3.3: `A(S)=κ(S)` for positive genus.
2. Test-function/Cheeger bound (Lem 4.2): `a(G) ≤ d(H)n/(m(n−m))`; planar `d_max≤5 ⇒ a(G)≤4` (Thm 4.3).
3. Regular-graph girth bound (Thm 5.1) and planar regular `a(G)≤4/(g−2)` (Cor 5.2); planar cubic ≠ K₄ ⇒ `a≤2` (Thm 5.3).
4. `a(G)≤n−⌈n/κ(G)⌉` (Thm 6.1); Ramanujan genus lower bound (Thm 7.1).
5. Asymptotic `2≤A^∞(S)≤6`; `A^∞_{Gr}(S)≤4` for regular graphs (Thm 8.2).

**Captured in Graphplay?** ⚠️ partial. `Bundle.Heawood (g) = ⌊(7+√(1+48g))/2⌋` packages the **orientable** Heawood number (note: `1+48g = 49−24χ` for orientable `χ=2−2g`, so the formulas agree). `Examples/HeawoodOnTorus.lean` realises `K₇↪T²` tightness. **Not captured:** the *algebraic-connectivity* statement `a(G)≤H(S)` (the paper's actual theorem — Graphplay only has the chromatic-number side), Fiedler's `a(G)≤v(G)`, the Cheeger test-function lemma, or the Ramanujan genus bound.

**Gaps to close:**
- `Graphplay/Spectral/AlgebraicConnectivity.lean`: `def algebraicConnectivity (G) := λ₂(L)`; `theorem fiedler_bound : a(G) ≤ vertexConnectivity G`.
- `theorem freitas_heawood_algconn : genus G = γ → χ ≤ 0 → a(G) ≤ Bundle.Heawood γ` (Thm 3.1) — bridges the existing `Heawood` def to the spectral side.
- `theorem subset_degree_bound` (Lem 4.2) and `theorem planar_algconn_le_4` (Thm 4.3); `theorem ramanujan_genus_lower_bound` (Thm 7.1).

---

### arXiv:1003.5588 — Limits of kernel operators / spectral regularity lemma (B. Szegedy)
**Key theorems/constructions:**
1. Cut-norm convergence ⇔ joint convergence of eigenvalues + eigenspaces (Prop 1.1/1.2, Lem 1.10/1.11): `[M_i]_λ → [M]_λ` in `L²` for `λ∉spec`.
2. Spectral regularity lemma (Thm 2): `M=S+E+R`, `S=[M]_λ`, `‖E‖₂≤ε`, `‖R‖_□≤F(λ,ε)`.
3. Symmetry-preserving regularity lemma (Thm 3): structured part `S` approx-invariant under `Aut(G)`; eigenvector-clustering step function (Lem 1.12).
4. Quasirandom group action (Cor 1.2/1.3): `G`-invariant operator with min-`G`-invariant-dim `d` has `‖M−p‖_□≤1/√d`; weakly-random actions (Thm 4) ⇒ cut-norm-compact invariant sets.
5. Sphere vs. circle (Prop 1.4/1.5): isometry-invariant graphons closed on `Sⁿ` (`n≥2`), **not** on the circle.

**Captured in Graphplay?** ⚠️ partial. `Graphon/Limit.lean` cites 1003.5588 and states cut-norm + graphon convergence and operator-norm convergence of quotients; `Graphon/Spectrum.lean` has the pure-point/continuous-spectrum split, `[M]_λ`-style cell-uniform projections, and (cell) strong cospectrality — i.e. the *spectral* side restricted to the finite cell-uniform sector. **Not captured:** the spectral regularity lemma itself (Thm 2/3), eigenvector-clustering step functions, quasirandom/weakly-random group actions, or the sphere-vs-circle closure dichotomy.

**Gaps to close:**
- `Graphplay/Graphon/Regularity.lean`: `def cutNormTruncation (M) (λ) := [M]_λ`; `theorem spectral_regularity_lemma` (Thm 2) and `theorem symmetry_preserving_regularity` (Thm 3).
- `theorem cutNorm_conv_iff_eigenspace_conv` (Prop 1.1) — strengthens the existing `Graphon/Limit` convergence statement.
- `Graphplay/Graphon/GroupAction.lean`: `def WeaklyRandom (G action)`; `theorem quasirandom_action_cutnorm_bound` (Cor 1.3); `theorem sphere_invariant_graphons_compact` (Prop 1.4) vs. `theorem circle_invariant_not_compact` (Prop 1.5).

---

### arXiv:2110.13686 — Dynamical systems on graph limits and their symmetries (Bick–Sclosa)
**Key theorems/constructions:**
1. Graph dynamical system `u̇ⱼ=f(uⱼ, n⁻¹Σ A_{jk} g(uⱼ,uₖ))`; automorphisms ⇒ symmetries (finite case, §2).
2. Graphon dynamical systems on `L¹(J)`; graphon automorphisms induce symmetries (Cor 3.13); generalized **noninvertible** symmetries (doubling map) absent in finite dim.
3. Symmetry-induced dynamically invariant subspaces — fixed-point sets of symmetries OR images of Koopman operator (§3.4); cluster/synchrony patterns (Thm 4.4).
4. Manifold-indexed graphons (distance-dependent coupling, Thm 5.2): spherical graphon, torus twisted states; graphop automorphisms (Prop 8.4).
5. "Ghosts of symmetry": asymmetric finite graphs with symmetric limit (Erdős–Rényi → constant graphon) inherit limit symmetries (§6).

**Captured in Graphplay?** ❌ not captured (closest neighbours are tangential). `Graphon/Lindblad.lean` does *open-system CTQW* on graphons and has cell-uniform-invariance under equitable partitions — a symmetry-invariant-subspace flavour — but it is *linear quantum* dynamics, not the nonlinear `f,g` graph dynamical systems, and there is no graphon-automorphism group, Koopman operator, noninvertible symmetry, or graphop here.

**Gaps to close:**
- `Graphplay/Graphon/DynamicalSystem.lean`: `def graphonFlow (W) (f g) : (L¹ J) → ℝ → (L¹ J)`; `def GraphonAutomorphism (W)`; `theorem automorphism_induces_symmetry` (Cor 3.13).
- `theorem symmetry_invariant_subspace` (fixed-point + Koopman, §3.4) — generalizes the existing equitable cell-uniform invariance to nonlinear flows.
- `def NoninvertibleSymmetry` (measure-preserving non-injective); `theorem manifold_graphon_symmetry` (Thm 5.2, spherical/torus).

---

### arXiv:2004.00677 — Graphon LQR invariant subspaces (Gao–Caines)
**Key theorems/constructions:**
1. Graphon LQR problem on `(L²[0,1])ⁿ`: state/control/cost couplings via (possibly distinct) graphons; operators `DA` (eq. 2).
2. Common-invariant-subspace assumption (A5): couplings share a finite-dim invariant subspace `S` (weaker than shared eigenfunctions of [2]).
3. Decomposition: host LQR → finite `nd×nd` network-coupled Riccati on `S` + decoupled infinite-dim LQR on `S^⊥`.
4. Centralized + nodal-collaborative optimal control; complexity one `nd×nd` + one `n×n` Riccati vs. direct `nN×nN`.
5. Low-rank approximate control for general (non-low-rank) couplings; harmonic-oscillator network application (§VII).

**Captured in Graphplay?** ⚠️ partial (best-captured of the three graphon papers). `Integrations/MeanFieldGames.lean` directly cites 2004.00677: `structure GraphonLQR`, operators `Aop/Bop`, `MildSolution` + `mildSolution_exists_unique` (Prop 1), cost functional, and the key thesis that **(A5)'s invariant subspace = the cell-uniform subspace of an equitable partition**, with the quotient LQR theorem as the headline. **Not captured:** the explicit two-Riccati `nd×nd`/`n×n` decomposition with complexity claim, the nodal-collaborative solution, and the low-rank approximate-control error bound.

**Gaps to close:**
- `theorem graphonLQR_subspace_decomposition` — host LQR = network-coupled finite Riccati on `S` ⊕ decoupled infinite LQR on `S^⊥` (the paper's central decomposition, currently only the *reduction* is stated, not the `S/S^⊥` split + Riccati pair).
- `def nodalCollaborativeControl` + `theorem nodalControl_optimal`.
- `theorem lowRank_approxControl_bound` (§VI) — approximate control error under low-rank coupling approximation.

---

## Top gaps (cluster 4)

1. **Corona products — entirely absent (1605.05260 + 1508.05458).** No `corona`, no PGST/Laplacian-PGST predicate, no Kronecker-approximation machinery. This is the single biggest structural-operator hole; coronas are flagged in the task as the second core product alongside join. Build `StdLib/Corona.lean` + `ForMathlib/Kronecker.lean` first — both papers reuse them.

2. **Quantum-Markov decidability (1911.01953) — entirely absent.** QOMDP, Moore/Mealy equivalence, and the headline approximate-optimal-policy decidability (Thm 6.8) have no scaffold. High novelty (Tamon's "rare tractable quantum problem"), and Mathlib's Banach-fixed-point/`ContractingWith` makes the value-iteration core tractable.

3. **Matrix inversion by quantum walk (2508.06611) — entirely absent.** No HHL/weak-coupling-perturbation/embedding. Shares the Krawtchouk-chain inverse-eigenvalue tooling with 2507, so pairs naturally with gap #4.

4. **Timing-insensitive PST / T-Rex + Krawtchouk chains (2507.18872) — only FR kinematics captured.** Missing the figure-of-merit `⟨1|H₀²|1⟩`, the Mandelstam–Tamm PST bound (Thm 1), and the T-Rex construction. `StdLib/Chain.lean` (Krawtchouk + inverse-eigenvalue) is a shared dependency of 2508 and 2507.

5. **Citation fix + general Laplacian-integral search (2506.21108).** `CompleteMultipartite.lean` mis-describes 2506.21108 as a complete-multipartite/single-marked CTQW result; the real theorem is general Laplacian-integral CIQW search for any marked fraction. Correct the attribution and add `Algorithm/DeterministicSearch.lean` (CIQW + Long-Grover + QPE phase shift).
