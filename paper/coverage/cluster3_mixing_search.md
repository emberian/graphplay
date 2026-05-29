# Cluster 3 — Mixing / Chiral / Spatial-Search Coverage Audit

Audit of Graphplay capture for twelve mixing/chiral/spatial-search papers.
Conventions: paths are repo-relative. `WeightedGraph` is **loopless**
(`Graphplay/Weighted.lean:42-48` enforces `adj v v = 0`), which is a recurring
structural obstruction for self-loop / Laplacian-weighted / lackadaisical
constructions flagged below.

Relevant existing infrastructure:
- `Graphplay/Mixing.lean`: `IsUniformMixing`, `IsAverageUniformMixing`,
  `WeightedGraph.mixing`, `WeightedGraph.averageMixing` (both `sorry`/abstract),
  `ChiralMixingSigning`, `IsCellUniformMixing`, `chiralMixingQuotient`,
  `chiralAverageMixingQuotient`.
- `Graphplay/Chiral.lean`: `ChiralSigning`, `signedBy`, `signedBy_preserves_equitable`,
  `Bundle`, `chiral_mixing_optimization`, `unitaryHammingChiralK4(Signing)`.
- `Graphplay/Search.lean`: `searchHamiltonian`, `IsOptimalSearch`,
  marked-refined partition, `search_quotient_reduction`, `optimal_search_lift`.
- `Graphplay/CarusoSpeedup.lean`: noisy/Lindblad CTQW search, `darkSpectralGap`,
  `search_speedup_via_partial_symmetry_breaking`.
- `Graphplay/StdLib/{Hypercube,Hamming,Cycle,CompleteMultipartite,Cayley,Path}.lean`.

---

### arXiv:2605.04414 — Uniform Mixing in Chiral Quantum Walks (Levine–Mesapam–Mustico–Tamon–Tucker–Zhan)
**Key theorems/constructions:**
1. Thm 2 (conical reduction): if Hermitian `A` has `0` as simple eigenvalue with eigenvector `1ₙ`, the cone `X̂` has probabilistic uniform mixing in expected `n^{3/2}` time (stopping-rule / Las Vegas via partial measurement at the conical vertex).
2. Cor 1: for any `n≥5`, a unitary signing `σ` makes `Kₙ^σ` uniform-mixing (circulant `Circ(0,-i,i,…)` for odd; skew block-circulant of roots of unity for even).
3. Claim 2 / Thm 3: explicit `K₄^σ ≅ K₁+K⃗₃` mixes at `π/3√3`; hence signed `H(n,4)=(K₄^σ)^□n` mixes at `π/3√3` — faster than any unoriented Hamming graph (improves Godsil–Zhan).
4. Thm 5 + Cor 5/6: any `ℤ/nℤ`-circulant with distinct eigenvalues has **average** uniform mixing (`M̄ = ΣEr∘Ē_r = (1/n)J`); oriented odd cycles and transitive tournaments qualify — a chiral No-Go violation of Godsil's Thm 4 (`K₂` is the only undirected average-uniform-mixing graph).
5. Cor 8: no oriented non-abelian Cayley graph has average uniform mixing (repeated eigenvalue from a >1-dim irrep).
6. Lemmas 1–3: local-uniform-mixing closure under `□`; equitable-quotient intertwiner `e^{-iBt}=Sᵀe^{-iAt}S`.

**Captured in Graphplay?** ⚠️ partial. `Graphplay/Chiral.lean` captures the K₄ signing (`unitaryHammingChiralK4Signing`, the exact Fig. 2 matrix), `signedBy_preserves_equitable`, `Bundle`, and the optimization statement `chiral_mixing_optimization` (Lemma 2/3 intertwiner, `sorry`). `Graphplay/Mixing.lean` `chiralMixingQuotient`/`chiralAverageMixingQuotient` capture the cell-uniform lift. `Graphplay/StdLib/Hamming.lean:hamming_no_chiral_uniformMixing` records the q≥5 chiral closure.
**Gaps to close:**
- `Graphplay/Chiral.lean`: `theorem conical_reduction_uniformMixing (G : WeightedGraph V) (h0 : 0 ∈ simple-spectrum with eigvec 1) : IsProbabilisticUniformMixing (cone G) (expectedTime := n^{3/2})` — needs a new `IsProbabilisticUniformMixing`/`LocalUniformMixing` predicate (currently only global `IsUniformMixing` exists) plus a `stoppingRule`/partial-measurement abstraction.
- `Graphplay/StdLib/Cayley.lean` or new `Chiral.lean` lemma: `theorem circulant_distinct_eigenvalues_averageUniformMixing : (∀ distinct eigenvalues) → IsAverageUniformMixing G` (Thm 5); corollaries `orientedOddCycle_averageUniformMixing`, `transitiveTournament_averageUniformMixing`. **Requires oriented/`±i`-signed graphs** — fits `ChiralSigning` with range `{±i}` (`IsOriented σ := ∀ x y, σ x y ∈ {i,-i}`), currently absent.
- `theorem nonabelian_cayley_no_averageUniformMixing` (Cor 8) — needs irrep-dimension/repeated-eigenvalue lemma (Babai Thm 6).
- `theorem signedHamming_uniformMixing (n) : IsUniformMixing ((unitaryHammingChiralK4)^□n) (π/3√3)` (Thm 3) — needs Cartesian-product `□` on `WeightedGraph` + local-mixing closure (Lemma 1).

---

### arXiv:quant-ph/0209106 — Mixing in CTQW on Graphs (Ahmadi–Belk–Tamon–Wendler)
**Key theorems/constructions:**
1. Thm 1: `Kₙ` has (instantaneous) uniform mixing **iff** `n ∈ {2,3,4}`; reduces to `sin²(tn/2(n-1)) = n/4`, integral only for `n≤4`.
2. Thm 2: among **balanced complete multipartite** graphs only `K_{2,2}=C₄` (besides the `Kₙ` cases) has uniform mixing; via `A=(1/(a-1))K_a ⊗ (1/b)J_b` circulant structure.
3. §3 `K₂` worked example: `Pₜ=[cos²t, sin²t]`, uniform at `t=kπ+π/4`.
4. Conj 1: no `Cₙ` (n>4) has instantaneous uniform mixing.
5. Conj 2 / Claim 3: Cayley graph `X(Sₙ,Tₙ)` not uniform mixing except `S₃` (`=K₃,₃` excluded); `S₄` verified.

**Captured in Graphplay?** ⚠️ partial. The Hamming/`Kₙ` boundary is captured indirectly: `Graphplay/StdLib/Hamming.lean:hamming_uniformMixing_iff_q_le_4` (the `K_q=H(1,q)` clique case is `q≤4`) and `hamming_no_uniformMixing_of_q_ge_5`. `K₄`/`C₄`/`K₃` mixing implied by `Hypercube` (`Q₂=C₄`) and Hamming `q∈{2,3,4}`. The headline **"no Kₙ uniform mixing except K₂,K₃,K₄"** and the **balanced multipartite K₂,₂-only** classification are **not stated as theorems**.
**Gaps to close:**
- New `Graphplay/StdLib/Complete.lean` (or extend `CompleteMultipartite.lean`): `theorem complete_uniformMixing_iff (n) : (∃ t, IsUniformMixing (completeWG (Fin n)) t) ↔ n ∈ ({2,3,4} : Finset ℕ)`. Needs a clean `completeWG`/`Kₙ` `WeightedGraph` (currently only `CompleteMultipartite [n]` analogue and `completeWG` referenced in `CarusoSpeedup`).
- `Graphplay/StdLib/CompleteMultipartite.lean`: `theorem balancedMultipartite_uniformMixing_iff (a b) : (∃ t, IsUniformMixing (CompleteMultipartite (List.replicate a b)) t) ↔ a*b ≤ 4` (the `1≤ab≤4` condition; `K₄,K₂,₂,K̄₄` solutions).
- `theorem K2_uniformMixing_times : IsUniformMixing K₂ t ↔ ∃ k, t = k*π + π/4` (sharpens the `Q₁`/`K₂` smoke test).

---

### arXiv:quant-ph/0509163 — Mixing & Decoherence in CTQW on Cycles (Fedichkin–Solenov–Tamon)
**Key theorems/constructions:**
1. Gurvitz decoherence model: `dρ_{j,k}/dt = i(…) − Γ(1−δ_{j,k})ρ_{j,k}`; substitution `S_{j,k}=i^{k-j}ρ_{j,k}` linearizes to real coefficients.
2. Small-decoherence (`ΓN≪1`) mixing bound `T_mix < (2/Γ)ln(N/ε)(1+1/(N-2))` — `T_mix ∝ 1/Γ` (decoherence *helps*, linearly).
3. Large-decoherence (`Γ≫1`) bounds `(2ΓN²/π²)ln(2/Nε) < T_mix < (ΓN²/2)ln((2+ε)/ε)` — `T_mix ∝ Γ`, `∝ N²` (classical limit).
4. Existence of a unique optimal `Γ*` minimizing mixing time (numerical) — continuous-time Kendon–Tregenna analogue.

**Captured in Graphplay?** ❌ not captured for cycles specifically; ⚠️ the *qualitative* "optimal nontrivial noise" mechanism is captured abstractly in `Graphplay/CarusoSpeedup.lean` (`search_speedup_via_partial_symmetry_breaking`, `darkSpectralGap`, breaking-score window) — but that file targets *spatial search* success probability on `Kₙ`/hypercube/star, not *total-variation mixing time on cycles*, and has no `Cₙ`+Gurvitz instance. `Graphplay/StdLib/Cycle.lean` has `Cycle`/eigenvalues but no decoherent walk.
**Gaps to close:**
- `Graphplay/Mixing.lean` (or new `MixingTime.lean`): `def totalVariationDist`, `def epsilonMixingTime (ρ-evolution) (ε) : ℝ` (TV-distance-from-uniform mixing time) — currently no TV-distance or `ε`-mixing-time notion exists.
- New instance in `CarusoSpeedup`/`Cycle`: `theorem cycle_decoherent_mixingTime_smallΓ (N) (Γ) (hΓ : Γ*N ≤ ...) : epsilonMixingTime (gurvitzEvolve (Cycle N) Γ) ε ≤ (2/Γ)*Real.log (N/ε)*(1+1/(N-2))` and the large-Γ two-sided bound. Requires a `Lindblad`/Gurvitz dephasing generator for cycles (Lindblad infra exists in `Graphplay/Graphon/Lindblad.lean` and `Toolkit/Noise.lean`; needs a `Cₙ`-specific all-vertex-monitoring jump set).

---

### arXiv:quant-ph/0509059 — Mixing of QW on Circulant Bunkbeds (Lo–Rajaram–Schepens–Sullivan–Tamon–Ward)
**Key theorems/constructions:**
1. Thm 1: circulant `G` with bounded eigenvalue multiplicity `μ(G)=O(1)` is **average** uniform mixing (`|p̄_j − 1/n| ≤ μ(G)/(2n)`); generalizes cycles.
2. Thm 2/Cor 3: constant-degree circulants `⟨1,n/k₁,…⟩` (incl. wheel `Vₙ=⟨1,n/2⟩`) are average uniform mixing.
3. Lemma 4 / Thm 5: spectra of join `G+H`; explicit limiting distribution `p_x(G+H)`. Cor 7/8: cone `K₁+C` of any circulant is **not** average uniform mixing (explains `Kₙ`).
4. Thm 9 / Cor 10: constant `m`-fold homogeneous join `G^{(+m)}` preserves average uniform mixing; explains `K_{n}^{(m)}` (complete multipartite) non-mixing.
5. Thm 12 / Cor 13–14: Cartesian bunkbed `Pₘ⊕G` (constant `m`) preserves average uniform mixing; `Pₘ` itself is average uniform; contrast with hypercube `Qₙ=P₂⊕Q_{n-1}`.

**Captured in Graphplay?** ❌ not captured. No circulant `WeightedGraph` family with a multiplicity-bounded average-mixing theorem; no `join`/`+` graph operator; the average-mixing matrix exists (`WeightedGraph.averageMixing`, abstract) but no spectral-multiplicity bound. `Graphplay/StdLib/CompleteMultipartite.lean` has the family but only Laplacian-integrality, not the cone/join non-mixing explanation. `Path` exists but no average-mixing result.
**Gaps to close:**
- New `Graphplay/StdLib/Circulant.lean`: `def Circulant (firstRow : Fin n → ℂ) : WeightedGraph (Fin n)` with `μ`/`spectralType`; `theorem circulant_boundedMult_averageUniformMixing (hμ : μ(G) ≤ c) : IsAverageAlmostUniformMixing G` (needs an `IsAverageAlmostUniformMixing` predicate = `∀ j, p̄_j = O(1/n)`, distinct from exact `IsAverageUniformMixing`).
- New graph ops in `Graphplay/Basic.lean` or `Weighted.lean`: `def WeightedGraph.join`, `def WeightedGraph.cartesianProduct (□)`; `theorem cone_circulant_not_averageUniformMixing`, `theorem homogeneousJoin_averageMixing_transfer`, `theorem cartesianBunkbed_averageMixing_transfer`.

---

### arXiv:quant-ph/0608044 — Universal Mixing of QW on Graphs (Carlson–Ford–Harris–Rosen–Tamon–Wrobel)
**Key theorems/constructions:**
1. Lemma 1 / Thm 2: weighted `P₃` and weighted claw `K_{1,n}` are **instantaneous universal mixing** (reach *any* distribution as edge weights vary); weighted `Kₙ` too (path-collapsing).
2. Thm 3/4: all weighted complete multipartite (`K_{m,n}`, all `k`-partite) are instantaneous universal mixing — contrast unweighted (only `K₂,₂`).
3. Cor 5: **unweighted** claw `K_{1,n}` is instantaneous **uniform** mixing (at `t=cos⁻¹(1/√(n+1))/√n`) — new uniform-mixing family beyond hypercubes.
4. Fact 6 / Prop 7: uniform mixing closed under Cartesian product `⊕` (shared mixing time); products of `Qₙ,K₄` mix. Fact 8: `C₅` not uniform mixing.
5. Lemma 9 / Cor 10/11: `p̄_start ≥ 1/τ(G)` (τ = #distinct eigenvalues) ⇒ no weighted graph is **average** universal mixing; average-almost-uniform mixing ⇒ `τ(G)=O(n)`.

**Captured in Graphplay?** ❌ not captured. No `universal mixing` notion at all; no weighted-claw / `P₃` family; no Cartesian-product closure; no `τ(G)` (distinct-eigenvalue-count) parameter or the `p̄_start ≥ 1/τ` lemma. The "claw is uniform mixing" result (the *only* non-hypercube unweighted family at the time) is absent.
**Gaps to close:**
- New `Graphplay/Mixing.lean` predicates: `def IsUniversalMixing (G) : Prop := ∀ (Q : distribution V) (x : V), ∃ (weights) (t), instMixing(weighted G)(x,t) = Q`; `def IsAverageUniversalMixing`.
- New `Graphplay/StdLib/Star.lean`: `def Star (n) : WeightedGraph (Fin (n+1))` (= `K_{1,n}`); `theorem star_unweighted_uniformMixing (n) : IsUniformMixing (Star n) (Real.arccos (1/Real.sqrt (n+1))/Real.sqrt n)`; `theorem weightedStar_universalMixing`.
- `theorem cartesianProduct_uniformMixing_closure` (Fact 6) — depends on `□` operator (shared gap with 0509059).
- `Graphplay/Spectral.lean`: `def spectralType (G) : ℕ` (# distinct eigenvalues) + `theorem averageProb_start_ge_inv_spectralType : p̄_start ≥ 1/spectralType G`, and corollary `no_weighted_averageUniversalMixing`.

---

### arXiv:quant-ph/0308073 — Graphs Resistant to QW Uniform Mixing (Adamczak–Andrew–Hernberg–Tamon)
**Key theorems/constructions:**
1. Lemma 1 (AAKV): average prob `P̄(ℓ)=Σ_{λ_j=λ_k}⟨z_j|0⟩⟨0|z_k⟩⟨ℓ|z_j⟩⟨z_k|ℓ⟩`; distinct eigenvalues ⇒ candidate average uniform mixing.
2. Thm 4 / Cor 5: for **abelian** `G`, no `G`-circulant except `K₂` is average uniform mixing (spectral gap zero via `λ_a = λ_{-a}` or Hadamard pigeonhole, Lemma 3).
3. Thm 6: `Cₙ` is average `(1/n)`-uniform mixing; Thm 7: `Kₙ` is *not* average `(1/n^{O(1)})`-uniform mixing.
4. Thm 8: bunkbed `G=A⋊ℤ₂` (adj `I₂⊗Aₙ + X₂⊗Iₙ`) has memoryless property `P̄⁰≡P̄¹` across the two copies.
5. Thm 9: no complete path `Pₙ` (except `K₂`) is average *classical* mixing; `P̄(0) < 1/2(n-1)` for `n>5`.

**Captured in Graphplay?** ❌ not captured. The AAKV average-probability formula, the abelian-circulant No-Go, the `Cₙ` `(1/n)`-mixing bound, the bunkbed memoryless property, and the path average-classical-mixing failure are all absent. (Note: 2605.04414 Thm 5 is the *chiral violation* of exactly this No-Go; capturing both gives a clean contrast pair.)
**Gaps to close:**
- `Graphplay/Mixing.lean`: `theorem averageMixing_eq_degenerate_sum` (Lemma 1 closed form for `averageMixing`); this is the spectral content underlying `WeightedGraph.averageMixing` (currently a bare `sorry`).
- `def IsAverageEpsilonUniformMixing (G) (ε)`; `theorem cycle_average_inv_n_uniformMixing (n) : IsAverageEpsilonUniformMixing (Cycle n) (1/n)` (Thm 6) and `theorem complete_not_average_polyinv_uniformMixing` (Thm 7).
- `theorem abelian_circulant_no_averageUniformMixing` (Thm 4) — pairs with 2605.04414's chiral violation; needs `spectralGap = 0` lemma.
- New `Graphplay/StdLib/Bunkbed.lean`: `def Bunkbed (A) := I₂⊗A + X₂⊗I`; `theorem bunkbed_memoryless : P̄⁰ = P̄¹`.

---

### arXiv:0808.2382 — Mixing of QW on Generalized Hypercubes (Best–Kliegl–Mead-Gluchacki–Tamon)
**Key theorems/constructions:**
1. Thm 1: hypercube + additive matching `Qₙ^η` (add edges `a↦a⊕η`) is instantaneous uniform mixing **iff** `|η|` even (slower time, `t* = (n+1)π/4`); includes Moore–Russell `η=0`.
2. Thm 4: `H(n,q)` not uniform mixing unless `q≤4` — via `H(n,q)=Kq^□n` + Cartesian-product Corollary 3 (`G⊕H` uniform mixing iff both factors are). Tight characterization.
3. Cor 3 / Fact 2: `|ψ_{G⊕H}⟩=|ψ_G⟩⊗|ψ_H⟩`; product uniform-mixing iff componentwise.
4. Thm 6: bunkbed `Bₙ(A_f)=I⊗Qₙ+X⊗A_f` (`A_f` a `ℤ₂ⁿ`-circulant) **not** uniform mixing if `|supp(f̂)| < 2^{n-1}`. Cor 7: join `Qₙ+Qₙ` not uniform mixing. Thm 8: `Bₙ(Qₙ)` not uniform mixing (tightness counterexample).

**Captured in Graphplay?** ⚠️ partial. The headline `H(n,q)` characterization (`q≤4`) is captured: `Graphplay/StdLib/Hamming.lean:hamming_uniformMixing_iff_q_le_4`, `hamming_no_uniformMixing_of_q_ge_5`. Moore–Russell hypercube uniform mixing: `Graphplay/StdLib/Hypercube.lean:hypercube_uniformMixing`. The **additive-matching** `Qₙ^η`, the **Cartesian-product factorization** (Cor 3 — needed by the Hamming proof itself), and the **bunkbed Fourier-support** criterion are absent.
**Gaps to close:**
- `Graphplay/StdLib/Hypercube.lean`: `def HypercubeMatched (n) (η : Fin n → Bool) : WeightedGraph`; `theorem hypercubeMatched_uniformMixing_iff_even (η) : (∃ t, IsUniformMixing (HypercubeMatched n η) t) ↔ Even (hammingWeight η)`.
- `Graphplay/Mixing.lean` or `Weighted.lean`: `theorem cartesianProduct_uniformMixing_iff (G H) (g₀ h₀) : IsUniformMixing (G □ H) t ↔ (localUniform G g₀ t ∧ localUniform H h₀ t)` (Cor 3). This is shared infrastructure with 0608044 Fact 6 and 2605.04414 Lemma 1, and is the natural way to *derive* `hamming_no_uniformMixing_of_q_ge_5` from the `Kq` case rather than `sorry`.
- New `Graphplay/StdLib/Bunkbed.lean`: `theorem bunkbed_fourierSupport_not_uniformMixing (hsupp : (f̂.support).card < 2^(n-1)) : ¬ IsUniformMixing (Bₙ A_f) t`.

---

### arXiv:0708.2096 — Non-uniform Mixing of QW on Cycles (Adamczak–Andrew–Bergen–Ethier–Hernberg–Lin–Tamon)
**Key theorems/constructions:**
1. Thm 7: `Cₙ` is **not** instantaneous uniform mixing when (a) `n=2^u`, `u≥3`; or (b) `n=2^u q`, `u≥1`, `q≡3 (mod 4)` — via eigenvalue symmetry `λ_k=λ_{n-k}`, parity of amplitudes (Cor 5: even-index real, odd-index imaginary), and a Gelfond–Schneider transcendence argument.
2. Lemma 2/6: divisor reduction `Σ_{j≡a (m)}⟨j|ψ_n⟩=⟨a|ψ_m⟩` and `⟨j|ψ_{2n}⟩+⟨n-j|ψ_{2n}⟩=⟨j|ψ_n⟩`.
3. Thm 10 (≈0308073 Thm 4): no abelian `G`-circulant except `C₂` is average uniform mixing (spectral gap zero).
4. Thm 12: `Cₙ` is average `(1/n)`-uniform mixing; Thm 13: `Kₙ` is not.

**Captured in Graphplay?** ❌ not captured. The even-cycle non-uniform-mixing theorem, the divisor-reduction lemmas, and the cycle average `(1/n)`-mixing are absent. `Graphplay/StdLib/Cycle.lean` has only the combinatorial `Cycle` + `λ_k=2cos(2πk/n)` eigenvalue formula. Substantial overlap with 0308073 (Thm 10/12 ≈ 0308073 Thm 4/6).
**Gaps to close:**
- `Graphplay/StdLib/Cycle.lean`: `def CycleWG (n) : WeightedGraph (Fin n)` (a `WeightedGraph`, not just `SimpleGraph`); `theorem cycle_not_uniformMixing_pow2 (u) (hu : 3 ≤ u) : ∀ t, ¬ IsUniformMixing (CycleWG (2^u)) t`; `theorem cycle_not_uniformMixing_2uq (u q) (hu) (hq : q % 4 = 3) : …`.
- `theorem cycle_average_inv_n_uniformMixing` (shared with 0308073 Thm 6).
- Helper `theorem cycle_divisor_reduction` (Lemma 2) — useful lemma in the eigenvalue-symmetry proof.

---

### arXiv:2204.04355 — Of Shadows and Gaps in Spatial Search (Chan–Godsil–Tamon–Xie)
**Key theorems/constructions:**
1. Def 2.1: `γ`-**Groverian** family: `U(t)=exp(-it(γH+ww†))` maps `ρ(0)=E₁` to `ww†` with constant fidelity in `τ=O(1/ε₁)`, `ε₁=‖E₁w‖` (the *shadow*). Spectral params `S_k=Σ_{r≥2}‖E_r w‖²/(θ₁-θ_r)^k`.
2. Thm 3.1: time lower bound `τ=Ω(1/ε₁)` for constant fidelity, arbitrary graphs (extends Farhi–Gutmann `Ω(√n)` for unit fidelity, vertex-transitive).
3. Thm 6.1 (main): for `γ=S₁` and `ε₁ ≪ √(S₁∆₂)` with `θ₂∈Supp_H(w)`, `H` is `S₁`-Groverian **iff** `S₂/S₁² = Θ(1)`. Improves Chakraborty–Novo–Roland.
4. Lemma 4.3 strict interlacing (Weyl); Prop 4.5 sharp gap estimates via Cauchy determinant.
5. Thm 5.1–5.3: necessary gap conditions; used to prove **cycles are not Groverian**.
6. §7 examples: Hamming `H(n,q)`, Johnson `J(n,k)`, Grassmann `Gq(n,k)`, strongly-regular, expanders, distance-regular-classical all Groverian (constant `∆₂`); `Cₙ` not.

**Captured in Graphplay?** ⚠️ partial / weakly. `Graphplay/Search.lean:IsOptimalSearch` is a *different, cruder* predicate (fixed `1/√2` fidelity, fixed γ/τ, amplitude not density-matrix fidelity) — does not encode the shadow `ε₁`, `S_k` params, or the `S₂/S₁²` characterization. The "`Ω(1/ε₁)` lower bound", "Groverian iff `S₂/S₁²=Θ(1)`", strict interlacing, and the distance-regular examples are **not captured**. `Graphplay/StdLib/Hamming.lean` has the spectrum but no Groverian statement.
**Gaps to close:**
- New `Graphplay/Search.lean` (or `Groverian.lean`): `def shadow (H) (w) : ℝ := ‖E₁ w‖`; `def Sparam (H) (w) (k) : ℝ := Σ_{r≥2} ‖E_r w‖²/(θ₁-θ_r)^k`; `def IsGroverian (H : Matrix) (γ) : Prop` (density-matrix fidelity `Tr(ww†ρ(τ))=Ω(1)` in `τ=O(1/shadow)`).
- `theorem groverian_lower_bound : IsGroverian → τ = Ω(1/shadow)` (Thm 3.1, density-matrix proof — uses `‖ρ_w(t)-ρ₀(t)‖²` derivative bound).
- `theorem groverian_iff_S2_S1sq (hθ₂ : θ₂ ∈ Supp) (hε : shadow ≪ √(S₁∆₂)) : IsGroverian H S₁ ↔ Sparam H w 2 / (Sparam H w 1)^2 = Θ(1)` (Thm 6.1).
- Examples leveraging existing spectra: `theorem hamming_groverian`, `theorem strongly_regular_groverian`, `theorem cycle_not_groverian`. Needs strict-interlacing/Weyl lemma (`Mathlib` has `Matrix.IsHermitian` eigenvalue interlacing partially).

---

### arXiv:1508.01327 — Spatial Search Optimal for Almost All Graphs (Chakraborty–Novo–Ambainis–Omar)
**Key theorems/constructions:**
1. Lemma 1 (sufficient condition): if `H₁` has `λ₁=1`, `|λ_i|≤c<1` for `i>1`, eigenvector `|s⟩`, then `(1+r)H₁+|w⟩⟨w|` drives `|s⟩` to fidelity `≥(1-c)/(1+c)-o(1)` in time `Θ(1/ε)`, `ε=|⟨w|s⟩|`. Hence search optimal when `λ₂/λ₁ ≤ c < 1`.
2. Main: Erdős–Rényi `G(n,p)` is a.s. optimal-search for `p ≥ log^{3/2}(n)/n`; hence almost all graphs (`p=1/2`). Uses `λ₁≈np`, `λ₂=2√(np)+o(·)`, `|v₁⟩→|s⟩` a.s. (Füredi–Komlós, Vu).
3. Random regular graphs degree `d≥3` optimal (`λ₂=O(d^{3/4})`).
4. State-transfer + Bell-pair protocols on random networks via the 3×3 degenerate-subspace Hamiltonian; fidelity→1.

**Captured in Graphplay?** ❌ not captured. The constant-spectral-ratio sufficient condition (`λ₂/λ₁≤c<1 ⇒ optimal`) is the conceptual core the audit calls "CNO spectral ratio" — but it is **not present** in `Graphplay/Search.lean` or `Spectral.lean`. `Graphplay/CarusoSpeedup.lean` uses a *dark-spectral-gap* for the noisy case but not this closed-system ratio. No random-graph / Erdős–Rényi model, no `G(n,p)`, no Füredi–Komlós/Vu bounds, no random-regular result, no state-transfer-on-random-network protocol.
**Gaps to close:**
- `Graphplay/Search.lean` or `Spectral.lean`: `def spectralRatio (H) : ℝ := λ₂(H)/λ₁(H)`; `theorem search_optimal_of_spectralRatio_lt_one (hgap : spectralRatio (γ•A) ≤ c) (hc : c < 1) (hs : ‖E₁ w‖ = 1/√n) : IsOptimalSearch G {w} (1/λ₁) (O(√n))` (Lemma 1). This is the highest-leverage missing item — it subsumes much of 2204.04355's example table (constant `∆₂` ⇒ constant ratio).
- New `Graphplay/StdLib/RandomGraph.lean` (probabilistic): `def ErdosRenyi (n) (p)`; `theorem erdosRenyi_search_optimal_ae (hp : p ≥ log^{3/2} n / n)`. Heavy probabilistic infrastructure — likely a long-horizon `sorry`-scaffold.
- `theorem randomRegular_search_optimal (d) (hd : 3 ≤ d)`.
- `Graphplay/PST.lean` link: `theorem randomNetwork_stateTransfer_highFidelity` (3-state degenerate subspace) — connects search ⇒ PST, matching the existing PST tower.

---

### arXiv:1406.0339 — Quantum Spatial Search on Planar Networks (Sadowski)
**Key theorems/constructions:**
1. Non-regular **discrete-time** coined walk on Apollonian networks: direct-sum coin space `X=⊕_i C^{d_i}`, per-vertex Grover coin `G_{d_i}`, flip-flop shift `S`.
2. Lemma 1 (Ambainis abstract search) / Fact 1–2: with `U₁=O_m`, `U₂=SC`, search for any marked node is `O(√N)` on any Apollonian network (asymptotic).
3. Key obstruction: asymptotic `O(√N)` holds for all nodes, but the **optimal measurement step differs by generation**, so a *single fixed measurement time* fails for arbitrary marked node. The fix: restrict to last-generation nodes (all same optimal time `T₀≈α√N`), with post-selection projection.
4. `Edges=O(N)`, `d_max=O(N^{0.63})`, avg degree →6; planar/scale-free/small-world.

**Captured in Graphplay?** ❌ not captured. This is a **discrete-time coined** walk on a **non-regular** graph (direct-sum coin space) — Graphplay's `IsOptimalSearch` (`Graphplay/Search.lean`) and `CarusoSpeedup` are all **continuous-time** with no coin/coined-walk apparatus. `Graphplay/DiscreteTime.lean` exists but (per filename) is the discrete-time CTQW-analogue, not the Ambainis coined model. No Apollonian network, no abstract-search-algorithm (`U₂U₁`) framework, no measurement-time/fixed-step subtlety.
**Gaps to close:**
- New `Graphplay/DiscreteTime.lean` extension or `CoinedWalk.lean`: `def CoinedWalk (G : SimpleGraph) : coin space ⊕_v C^{deg v}`, flip-flop shift `S`, per-vertex Grover diffusion. (Structural: non-regular ⇒ direct-sum coin, novel for this codebase.)
- `def AbstractSearch (U₁ U₂) (ψstart ψgood)` + `theorem abstract_search_runtime : ∃ t = O(1/α), |⟨ψgood|(U₂U₁)ᵗ ψstart⟩| = Ω(1)` (Ambainis Lemma 1/3).
- `Graphplay/StdLib/Apollonian.lean`: `def Apollonian (K : ℕ)` (iterative triangle subdivision); `theorem apollonian_search_optimal_lastGen : fixed-measurement-step O(√N)` and the negative `apollonian_no_uniform_measurementStep` (the paper's actual point).
- **Lowest priority** — orthogonal to the codebase's continuous-time/equitable-quotient/PST core.

---

### arXiv:1706.06939 — Faster Search by Lackadaisical Quantum Walk (Wong)
**Key theorems/constructions:**
1. Construction: discrete-time coined walk on 2D grid (torus) with a **self-loop of weight `l`** at each vertex; coin space `C⁵` (`↑↓←→` + self-loop `⟲`), weighted Grover coin `|s_c⟩∝(↑+↓+←+→+√l⟲)`.
2. Main numerical result: with `l=4/N`, success probability → constant near 1 in `O(√(N log N))` steps — an `O(√log N)` improvement over loopless Ambainis et al. Grover oracle stores amplitude in the marked vertex's self-loop.
3. SKW oracle does **not** improve (self-loop amplitude alternates sign).
4. Algorithm is **not** an instance of the abstract search algorithm (the `Q⊗I₅` oracle flips two orthogonal coin states), so it resists the standard analytic framework.

**Captured in Graphplay?** ❌ not captured. **Structural blocker:** Graphplay's `WeightedGraph` is loopless by definition (`Graphplay/Weighted.lean:48 loopless : ∀ v, adj v v = 0`). The lackadaisical walk *requires* per-vertex self-loop weights `l`, which cannot be expressed in the current `WeightedGraph` type. Also discrete-time coined (no coined-walk infra, shared blocker with 1406.0339). No 2D-grid/torus standard-library entry.
**Gaps to close:**
- **Structural prerequisite:** a `LoopyWeightedGraph` (or `selfWeights : V → ℝ` field added to a new structure) — the existing loopless `WeightedGraph` cannot host this. Cf. the 2605.04414 remark that *Laplacian* `L(X)=D-A` with self-loops also needs this. Recommend a `Graphplay/WeightedLoopy.lean` with `structure LoopyWeightedGraph extends adjacency + selfWeights`.
- `Graphplay/StdLib/Grid2D.lean`: `def Torus2D (k)` (periodic √N×√N grid).
- `def LackadaisicalCoinedWalk (G) (l) : coined walk with C^{deg+1} coin`; `theorem lackadaisical_grid_search_runtime : l = 4/N → success ≈ 1 in O(√(N log N))` (numerical in the paper — likely a *statement-level* `sorry` only).
- Builds on the coined-walk/abstract-search infra of 1406.0339.

---

## Top gaps (cluster 3) — ranked

1. **CNO constant-spectral-ratio sufficient condition (1508.01327 Lemma 1 + 2204.04355 Thm 6.1).** Single highest-leverage item. Add `spectralRatio`/`shadow`/`Sparam` to `Graphplay/Search.lean`+`Spectral.lean` and the theorem `λ₂/λ₁ ≤ c < 1 ⇒ optimal search`. This *immediately* gives the entire 2204.04355 example table (Hamming/Johnson/Grassmann/SRG/expander Groverian via constant gap) and is the spectral counterpart to the existing equitable-quotient/PST machinery. The current `IsOptimalSearch` is too crude (fixed fidelity, no shadow) and should be refactored to the density-matrix `IsGroverian` form.

2. **Cartesian-product `□` operator + uniform-mixing closure (0608044 Fact 6, 0808.2382 Cor 3, 2605.04414 Lemma 1).** A `WeightedGraph.cartesianProduct` with `|ψ_{G□H}⟩=|ψ_G⟩⊗|ψ_H⟩` and uniform-mixing-iff-componentwise unblocks: deriving `hamming_no_uniformMixing_of_q_ge_5` from the `Kq` base case (replacing a `sorry`), the signed `H(n,4)` mixing time (2605.04414 Thm 3), and hypercube/claw/`K₄` product families. Currently no graph product exists on `WeightedGraph`.

3. **Average-mixing spectral formula + `Kₙ`/balanced-multipartite/abelian-circulant No-Go (0209106 Thm 1–2, 0308073 Thm 4/6, 0708.2096 Thm 10/12, 0509059 Thm 1).** `WeightedGraph.averageMixing` is currently a bare `sorry`; give it the AAKV degenerate-eigenvalue closed form, then the `Kₙ`-iff-`{2,3,4}`, balanced-multipartite-iff-`K₂,₂`, no-abelian-circulant (= the No-Go that 2605.04414's chiral Thm 5 *violates* — capture both for the contrast), and circulant-bounded-multiplicity average-mixing theorems. Needs `IsAverageEpsilonUniformMixing` + `spectralType`/`μ` parameters.

4. **Oriented (`±i`) signings + chiral average-uniform-mixing violation (2605.04414 Thm 5, Cor 5/6/8).** Extend `ChiralSigning` with `IsOriented` (range `{±i}`) and prove circulant-distinct-eigenvalues ⇒ average uniform mixing, instantiated on oriented odd cycles and transitive tournaments — the paper's flagship No-Go violation, directly paired with gap #3. Infrastructure (`ChiralSigning`, `signedBy`) already exists; this is incremental.

5. **Self-loop / loopy weighted graphs (1706.06939; also 2605.04414 Laplacian remark; coined-walk infra for 1406.0339).** Structural: the loopless `WeightedGraph` invariant blocks lackadaisical walks and Laplacian-with-self-loop constructions entirely. Requires a new `LoopyWeightedGraph` (`selfWeights : V → ℝ`) plus a discrete-time coined-walk model. Largest scope, most orthogonal to the codebase's continuous-time core — lowest priority but a hard prerequisite for two papers.
