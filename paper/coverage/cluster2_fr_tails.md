# Cluster 2 coverage audit — fractional revival / speed / tails

Scope: nine FR/speed/tails papers vs. Graphplay capture. Notation: ✅ captured,
⚠️ partial, ❌ not captured. File:def references are absolute-anchored to
`/Users/ember/dev/graphplay/Graphplay/...`.

Note on corpus: **`references/1801.09654.txt` is absent** ("Quantum Fractional
Revival on Graphs", Chan–Coutinho–Tamon–Vinet–Zhan, DAM 269:86–98, 2019). It is
cited as ref [6] in 2004.01129 and ref [7] in 1907.04729; audited below from
those descriptions.

---

### arXiv:1907.04729 — Fractional Revival and Association Schemes
**Key theorems/constructions:**
1. **Thm 3.1** (Bose-Mesner FR iff): `A ∈` Bose-Mesner algebra ⇒ FR `a→b` iff a
   unique class `A_q` is an order-2 permutation matrix and spectral congruences
   `(θ_r−θ_0)τ ≡ 0` or `≡ 2 arccos α (mod 2π)` hold; then `U(τ)=e^{iζ}(αI+βA_q)`.
2. **Cor 3.2 / Thm 3.5** (g,h characterization): integers `g=gcd(θ_0−θ_s)`,
   `hg=gcd(θ_r−θ_s)_{σ_r=σ_s}`; `h=1` no FR, `h>2` proper FR (min time `2π/hg`),
   `h` even ⇒ PST, `h` doubly even ⇒ balanced FR.
3. **Prop 3.6** DRG: `U(τ)=αA_0+βA_d`, `A_d` the antipodal `(d/2)K₂` perm.
4. **Thm 4.4/4.5, Prop 4.6** Hamming `H(n,2)`: balanced-FR characterization via
   binary-carry/Kummer conditions on `C(n−1,r−1)`; min FR time `π/2^k`.
5. **Prop 4.14, 4.15** Infinite families: `X_r` with balanced FR at `π/2^k`;
   consecutive unions `X_1∪…∪X_r` with balanced FR at `π/4`.
6. **Prop 5.2, Cor 5.4/5.5** Weighted: `ωA_2+A_1` balanced FR iff `4ω/Ω` odd
   integer; `A_2±2A_1` in `H(2m,2)`, `A_2±A_1` in `H(2m+1,2)` at `π/4`.

**Captured in Graphplay?** ⚠️ partial. `Dowsing/FractionalRevivalNC.lean`:
`IsFR`, `IsFRSystem`, `IsCellUniformFR`, and `bose_mesner_fr_iff` (Thm 3.1, one
direction + `True` placeholder for the spectral congruences) are stated.
Scheme infra `QuantumGraph.lean:206 AssociationScheme`, `:216 BoseMesner` exist.
Hamming family stated as `hammingGraph_balanced_fr` / `hammingGraph_fr_iff` (both
`sorry`, and the stated `4∣n` time `π/(2n)` does not match the paper's
`π/2^k` / Kummer conditions). All proofs `sorry`. The `g,h` invariants, Thm 3.5,
Kummer/`α₂` machinery, DRG Prop 3.6, and the infinite families are **not** stated.

**Gaps to close:**
- `FractionalRevivalNC.lean`: `def schemeG (S) (G) : ℤ` and `schemeH`, then
  `theorem fr_iff_h (S) (G) (hG) : (∃ τ α β, IsFR …) ↔ 2 < schemeH S G` plus
  `pst_iff_h_even`, `balancedFR_iff_h_doublyEven` (Thm 3.5).
- `StdLib/Hamming.lean`: `def alpha2 : ℕ → ℕ`, Kummer carry lemma
  `kummer_carries`, then `theorem hamming_balancedFR_iff (n r) : balancedFR (X r) ↔
  Odd n ∧ alpha2 (n-1) = alpha2 (r-1) ∧ …` (Lemma 4.8 / Prop 4.9).
- `theorem drg_fr_eq (X : DRG) : IsFR … → U τ = α•A 0 + β•A d` (Prop 3.6).

---

### arXiv:2004.01129 — Fundamentals of fractional revival in graphs
**Key theorems/constructions:**
1. **Def 3.1, Prop 3.2** `K`-fractional revival for arbitrary `K⊆V`: `U(τ)`
   block-diagonal with a `|K|×|K|` block ⟺ density matrix `D_K/|K|` periodic.
2. **Thm 5.1 / Def 5.2** commuting partition `P` of eigenindices with
   `(Σ_{r∈C}E_r)D_K = D_K(Σ E_r)`; unique minimal `P_min^K`.
3. **Thm 5.5** (ratio condition): `K`-FR occurs iff eigenvalues satisfy the
   **ratio condition** wrt `P_min^K` (`(θ_r−θ_s)/(θ_h−θ_k)∈ℚ`); eigenvalue
   support `Φ_K={(θ_r,θ_s):E_rD_KE_s≠0}` (Thm 6.6 equivalence).
4. **Thm 3.3 / Cor 6.7** integer weights ⇒ ∃ squarefree `Δ` with `θ_r−θ_s∈ℤ√Δ`;
   first FR by time `2π`.
5. **Def 7.1, Thm 7.2** decomposability wrt `K`: `⟨A⟩` contains a non-identity
   `K`-block-diagonal matrix ⟺ `P_min^K` has ≥2 nonzero `F̃_j` (necessary for FR).
6. **Constructions §4**: Cartesian/direct/double-cover/join products, antipodal
   `r`-fold covers of `K_n`; FR is **non-monogamous** (resolves open Q of [6]).

**Captured in Graphplay?** ⚠️ partial. Only the `|K|=2` vertex case is captured
(`IsFR`). Strong-cospectrality + eigenvalue-support + Godsil/ratio infra exists
for **pairs**: `PST/Cospectrality.lean:120 IsStronglyCospectral`, `:197
eigenSupport`, `:205 GodsilRatioCondition`; `PST/GodsilRatio.lean:106
EigenvalueSupport`, `:154 IsGodsilRatio`, `:189 ratios_rational`. The
arbitrary-`K` framework — `K`-FR, `D_K` periodicity, commuting/minimal partition
`P_min^K`, set eigenvalue support `Φ_K`, decomposability, strong fractional
cospectrality, monogamy — is **❌ not captured**.

**Gaps to close:**
- New `Dowsing/SubsetFractionalRevival.lean`:
  `def DensityK (G) (K : Finset V) : Matrix V V ℂ`;
  `def IsKFR (G) (K) (τ) : Prop` (block-diagonal `U(τ)`);
  `theorem isKFR_iff_periodic : IsKFR G K τ ↔ Periodic (DensityK/|K|) τ` (Prop 3.2).
- `def CommutingPartition`, `def minCommutingPartition (G) (K)`,
  `def setEigenSupport (G) (K) : Set (ℝ×ℝ)`, then
  `theorem kfr_iff_ratioCondition` (Thm 5.5) and
  `theorem ratio_conditions_equiv` (Thm 6.6).
- `def IsDecomposable (G) (K)`, `theorem decomposable_iff_partition` (Thm 7.2),
  and `theorem fr_not_monogamous : ∃ G, pairwise-{a,b,c}-FR` (the §1 headline).

---

### arXiv:1801.09654 — Quantum Fractional Revival on Graphs (Chan et al., DAM 2019)
**Key theorems/constructions:** (audited via citation; text not in corpus)
1. FR between **cospectral pairs**; spectral/eigenvalue conditions for `{a,b}`-FR.
2. Open Q: necessary conditions for FR between **non-cospectral** pairs
   (resolved later by 2004.01129).
3. Open Q: monogamy of FR (resolved negatively by 2004.01129).
4. `Cor 5.6` (eigenvalues integral ⇒ τ rational multiple of π) used by 1907.04729.

**Captured in Graphplay?** ⚠️ partial (indirect). The pair-FR predicate `IsFR`
and pair cospectrality exist (`PST/Cospectrality.lean`), so the `{a,b}` core is
present in shape; the specific spectral conditions/`Cor 5.6` are not stated.

**Gaps to close:** add the source paper to `references/`; state
`theorem fr_cospectral_necessary (G u v) : IsFR G u v τ α β → α≠0 → IsCospectral G u v`
and `theorem integral_spectrum_fr_time_rational` (Cor 5.6) in
`FractionalRevivalNC.lean`.

---

### arXiv:1710.02705 — A graph with fractional revival (Bernard et al.)
**Key theorems/constructions:**
1. NNN-Krawtchouk XX chain `H=αJ²+βJ` (J = Krawtchouk Jacobi matrix); balanced
   FR conditions: `α/β=p/q` coprime, `p` odd, `q,N` opposite parity, `τ_FR=πq/2β`.
2. Column-space projection: `A_1` on the one-link hypercube projects to `2J`
   (NN-Krawtchouk chain) — recovers Christandl PST.
3. **Main**: weighted graph `G_1∪G_2` (hypercube + face-diagonals, weights
   `β/2`, `α/2`) projects to NNN chain ⇒ exhibits balanced antipodal FR.
4. Unweighted case `α=β=2`: `G_1∪G_2` has balanced FR at `π/4` for `N` even.
5. Appendix: direct verification `e^{−iτH_G}=e^{−iφ'}(A_0±iA_{N−1})/√2`.

**Captured in Graphplay?** ⚠️ partial. The cell-uniform FR lifting machinery
(`FractionalRevivalNC.lean:229 EquitablePartition.fr_lift`) is exactly the
abstract avatar of the column-space projection here, and `StdLib/Hamming.lean`
has Krawtchouk eigenvalue scaffolding. But the specific construction `G_1∪G_2`
(hypercube + weighted face-diagonals = `span{A_1,A_2}` of `H(n,2)`), and its
balanced-antipodal-FR theorem, are **not** stated.

**Gaps to close:**
- `StdLib/Hypercube.lean` or `FractionalRevivalNC.lean`:
  `noncomputable def hypercubeFaceDiagonal (n) (α β : ℝ) : WeightedGraph (Fin n → Fin 2)`
  (= `(β/2)•A₁ + (α/2)•A₂`);
  `theorem hypercubeFaceDiagonal_balancedFR (n α β) (hpq …) :
   IsFR (hypercubeFaceDiagonal n α β) u (antipode u) (π*q/(2β)) (cos…) (i·sin…)`.
- A `column_space_projection` lemma realizing the `A₁↦2J` projection as an
  `EquitablePartition` (Hamming-weight distance partition) feeding `fr_lift`.

---

### arXiv:2209.08160 — Breaking the speed limit for PST (Xie–Kay–Tamon)
**Key theorems/constructions:**
1. PST speed limit `J_max τ ≥ (π/4)√(N²−¼(1−(−1)ᴺ))` (Yung; recalled Eq.1).
2. θ-revival `e^{−iHτ₀}|1⟩=cosθ|1⟩+sinθe^{iφ}|N⟩`; symmetric-chain decomposition
   into symmetric/antisymmetric subspaces with relative phase `2θ`.
3. **Monorail protocol**: encode qubit as `α|2⟩+β|1⟩`, evolve FR chain, herald
   arrival by measurement; **anti-Zeno** repeat-until-success, expected time
   `J_maxτ₀/sin²θ`, Chernoff-bounded repetitions.
4. **Fastest-possible-FR** bound `J_maxτ₀ ≥ Nθ/2` (even N), saturated by Genest
   et al. chains ⇒ expected transfer time **below** the PST speed limit.
5. Odd-`N`: asymmetric reduction, `sinθ=sin(2η)sinθ′`; **no** speed advantage.

**Captured in Graphplay?** ❌ not captured — **flag prominently**. The only
"anti-Zeno" in Graphplay is the **open-system / Lindblad** noise-assisted search
speedup (`CarusoSpeedup.lean:294 anti_zeno_mechanism`, `:311
zeno_antiZeno_boundary`), which is a *different mechanism* (decoherence
broadcasting cell labels), not the unitary heralded-measurement repeat-until-
success protocol here. There is **no** speed-limit theorem, no θ-revival
quantity, no monorail/dual-rail encoding, no fastest-FR bound.

**Gaps to close:**
- New `Dowsing/AntiZenoSpeed.lean` (or extend `StdLib/Path.lean`):
  `def thetaRevival (H) (a b) (τ θ φ) : Prop`;
  `theorem pst_speed_limit (J : Fin n → ℝ) (τ) (hPST) :
   (⨆ n, |J n|) * τ ≥ π/4 * Real.sqrt (n^2 - …)` (Yung, Eq.1);
  `theorem fr_speed_limit_symmetric : Jmax*τ₀ ≥ n*θ/2` (Eq. saturated);
  `def MonorailProtocol`, `def expectedTransferTime`,
  `theorem monorail_beats_speed_limit (heven) : E[Jmax T] < Jmax τ_min`.

---

### arXiv:1609.01854 — A Note on the Speed of PST (Kay–Xie–Tamon)
**Key theorems/constructions:**
1. PST iff `H` symmetric (`B_n=B_{N+1−n}`, `J_n=J_{N−n}`) and ordered eigenvalues
   `e^{−iλ_nt₀}=(−1)^{n+1}e^{iφ}`; eigenvectors `S|λ_n⟩=(−1)^{n+1}|λ_n⟩`.
2. **Even N**: `2J_max ≥ 2J_{N/2}=Σ(λ_{2n−1}−λ_{2n}) ≥ (N/2)(π/t₀)` ⇒
   `J_max t₀ ≥ πN/4` (Yung).
3. **Odd N** (the note's contribution): via `Tr(SH²)` and a clean quadratic-form
   bound, `J_max t₀ ≥ (π/4)√(N²−1)`.

**Captured in Graphplay?** ❌ not captured. `StdLib/Path.lean:158` only *mentions*
"Yung 2006" in a docstring; no speed-limit theorem exists. The
mirror-symmetry/eigenphase PST characterization (item 1) is partially mirrored by
`PST/GodsilRatio.lean isPST_exists_iff_strongCospectral_and_godsilRatio` but not
in the tridiagonal-chain `J_max·t₀` quantitative form.

**Gaps to close:** the `pst_speed_limit` theorem listed under 2209.08160 covers
both parities; additionally state the characterization
`theorem tridiagonal_pst_iff (B J) : IsPST … ↔ (symmetric ∧ eigenphase_condition)`
and the odd-`N` bound `Jmax*t₀ ≥ (π/4)√(N²−1)` (a `Tr(S H²)` quadratic-form
lemma) in `StdLib/Path.lean`.

---

### arXiv:2211.14704 — Quantum state transfer in graphs with tails (Bernard–Tamon–Vinet–Xie)
**Key theorems/constructions:**
1. **Decoupling (Thm 7, Golinskii)**: one-sum of finite `G_n` with `P_∞` at `v`
   ⇒ `U⁻¹A(H)U = ℑ_v ⊕ J̃₀`, dim `ℑ_v = n − rank W_{G_n}(v)` (dark subspace);
   if `G_n` has an equitable distance partition, leading block of `J̃₀ = A(G_n/π)`.
2. **Sedentariness (Prop 3, Thm 4)**: clique `K_n` (and `K̄_m+K_n` with tails)
   stays sedentary under infinite tails ("conical illusion").
3. **Cone transport (Thm 5)**: one-sum of cone `K_1+G_n` with `P_∞` ⇒ asymptotic
   efficient PST inherited from `G_n` (fidelity `1−O(1/2ⁿ)` for cube cone).
4. **Series/sl2 (Thm 9, 12, 13, 14)**: `P_m(G_0,…)` series graphs; `(Q_n/π)^□2`
   and `Q_n` with tails carry multiple PST via Clebsch-Gordan / walk modules of
   the Terwilliger algebra (Krawtchouk-chain decomposition).
5. **Dual-rail (Thm 15)**: rooted product `P_3⟨G,P_∞,G⟩` (or `G□K₂`) gives PST
   between `(e(u₀)−e(u₁))/√2` and `(e(v₀)−e(v₁))/√2` — protecting any PST graph.

**Captured in Graphplay?** ⚠️ partial — only the **abstract** filtered-colimit
shadow. `Dowsing/FilteredColimitPST.lean` states `ConsistentPartitionSequence.
pst_inherited` (master), `K_n_plus_tree` family, and names this paper. But the
**concrete graph operations are ❌ not captured**: one-sum, cone `K_1+G`,
rooted product, `G□K₂` doubling, the decoupling theorem `A(H)=ℑ_v⊕J̃₀`, dark
subspace `ℑ_v = n−rank W_G(v)`, eventually-free Jacobi matrices, sedentariness,
walk modules / Terwilliger / sl2 Clebsch-Gordan, dual-rail antisymmetric PST.
The walk matrix / controllability `W_G(v)` is also absent.

**Gaps to close:**
- New `StdLib/GraphsWithTails.lean`:
  `def oneSum (G H : WeightedGraph _) (u : …)`, `def cone (G)`,
  `def rootedProduct (G) (Y : V → RootedGraph)`, `def evenuallyFreeJacobi`.
- `def walkMatrix (G) (v)`, `def IsControllable`, `def darkSubspace (G) (v)`,
  then `theorem decoupling (Golinskii Thm 7)`:
  `U⁻¹ A(oneSum G P∞ v) U = darkBlock ⊕ jacobiTail ∧ dim dark = card V − rank (walkMatrix G v)`.
- `def IsSedentary (G) (v)`, `theorem clique_sedentary_with_tail` (Prop 3);
  `theorem cone_pst_with_tail` (Thm 5, the headline) — pairs naturally with
  the existing `FilteredColimitPST.K_n_plus_path` scaffold.
- `theorem dualRail_pst (G □ K₂)` (Thm 15) — note `G□K₂` already exists via
  `BundlePSTLift.cartesianProduct_pst`; the antisymmetric-subspace PST is the
  missing piece.

---

### arXiv:2301.07251 — No Infinite Tail Beats Optimal Spatial Search (Xie–Tamon)
**Key theorems/constructions:**
1. **Thm 1**: infinite lollipop `L_n=K_n(P_∞)` with oracle weight `γ=n+O(1)`
   has optimal spatial search `|⟨e₁,e^{−itH}z₁⟩|=Ω(1)` at `t=π/(2√n)`.
2. Jost-function / eventually-free Jacobi analysis: `H=−I_{n−2}⊕Ĥ`; the search
   lives in the **infinite-dimensional** invariant subspace; two bound states
   `λ_± = n ± √n + O(1)` carry the initial/target states.
3. **§IV**: oracle at the gateway/attachment vertex — same `π/(2√n)` time ⇒
   algorithm is **oblivious** to tail presence/location.
4. **Thm 3 (optimality)**: Farhi-Gutmann-style lower bound `γt₀=Ω(1/ε₁)` on
   `K_1+G_n` cones with tail (`ε₁=|⟨e_w,z₁⟩|`), matching the upper bound.

**Captured in Graphplay?** ⚠️ partial. `Search.lean:124 search_infinite_tail`
states the infinite-tail-search claim but trivially (returns the finite witness;
self-described as needing an `InverseLimit`/`UnionGraph` extension).
`FilteredColimitPST.lean` provides the `K_n_plus_path` consistent partition
sequence + `search_inherited` master corollary and `xie_tamon_search_via_master`
(both `True`/`sorry`). `Categorical.lean:530` states the "no infinite tail beats
optimality" corollary abstractly. The **Jost-function spectral analysis, bound
states `λ_± = n±√n`, the `π/(2√n)` time, and the obliviousness theorem are not
captured**.

**Gaps to close:**
- `Dowsing/FilteredColimitPST.lean` / new `JostBoundState.lean`:
  `def JostFunction (J : eventually-free Jacobi) : ℂ → ℂ`,
  `theorem jost_point_spectrum` (Golinskii p8);
  `def infiniteLollipop (n)`, `theorem lollipop_optimal_search (n) (γ=n+O(1)) :
   |⟨e₁, e^{−itH} z₁⟩| = Ω(1)` at `t=π/(2√n)` (Thm 1) — discharge
   `search_infinite_tail` non-trivially.
- `theorem search_oblivious_to_tail` (§IV) and `theorem search_lower_bound_cone`
  (Thm 3, Farhi-Gutmann `M(t)` argument).

---

### arXiv:2512.08141 — The Strength of Weak Coupling (Kay–Tamon)
**Key theorems/constructions:**
1. **Feshbach-Schur map** `F(λ)=λ₀+δW_{P0}+δ²W₀₁(λ−H_{P1})⁻¹W₁₀`; effective
   Hamiltonian `h` on degenerate subspace `P0` (Thm 3.1, Lemma 3.2).
2. **Effective-walk reduction (Claims 3.1–3.5)**: with `ε=δκ=o(1)`,
   `⟨ϕ_b,e^{−itH}ϕ_a⟩=(1−O(ε²))⟨ϕ_b,e^{−ith}ϕ_a⟩+O_d(ε)` ⇒ HFST on `H` reduces
   to ST on `h`.
3. **T.rex HFST (Thm 4.1)**: base graph `G₀∪K̄₂`, weak pendant edges `δW`,
   `(2γ)`-cospectral `α,β` ⇒ fidelity `(1−o(1))/√(1+γ²)` at
   `τ=O(1/(δ²|⟨α|A⁻¹|β⟩|))`; **γ-cospectrality** (Def 2) weaker than strong
   cospectrality; transfer time independent of diameter.
4. **Anderson-localization robustness (Thm 4.2)**: 4 protected vertices + control
   `B` for cospectrality ⇒ HFST on Jacobi chains under arbitrary random diagonal
   noise.
5. **Resonant tunneling (§5.1)**: singular base graph, Schrieffer-Wolff effective
   `h` on `{|a⟩,|ρ⟩,|b⟩}` ⇒ hitting time `(π/2)/(ε∆|⟨α|ρ⟩|)`.
6. **Quantum hitting times / edge-oracle search (§5, Table 1)**: T.rex speedups
   for path/clique/barbell/cube etc.; oracle as a pendant edge.

**Captured in Graphplay?** ❌ not captured — **flag prominently**. No
Feshbach-Schur map, no resolvent/condition-number infrastructure, no
γ-cospectrality (weaker than the existing `IsStronglyCospectral`), no T.rex
pendant-edge construction, no effective Hamiltonian, no Schrieffer-Wolff /
resonant tunneling, no high-fidelity-state-transfer (`HFST`) predicate, no
Anderson-localization model, no quantum-hitting-time table. The existing
`IsPGST`/pretty-good (`PST.lean:67`) is the closest predicate but is a distinct
notion (ε arbitrarily small vs. fixed). Entirely fresh territory.

**Gaps to close:**
- New `Dowsing/WeakCoupling.lean` (or `FeshbachSchur.lean`):
  `def resolvent (A) (ζ) := (ζ•1 − A)⁻¹`, `def conditionNumber (A) : ℝ`,
  `def feshbachMap (H) (P0 P1) (λ) : Matrix …`,
  `theorem feshbach_eigen_iff` (Thm 3.1).
- `def IsHighFidelityST (G) (a b) : Prop` (Def 1), `def IsGammaCospectral (G) (α β γ)`
  (Def 2, weaker than `IsStronglyCospectral`), with
  `theorem stronglyCospectral_imp_gammaCospectral`.
- `def TRex (G₀) (α β : V) (δ) : WeightedGraph (V ⊕ Fin 2)` (pendant edges),
  `theorem trex_hfst (hcosp) (hδκ) : IsHighFidelityST (TRex …) a b` (Thm 4.1).
- `def resonantTunneling`, `theorem resonant_hitting_time` (§5.1);
  `theorem trex_anderson_robust` (Thm 4.2); a `quantumHittingTime` def + the
  Table-1 family bounds.

---

## Top gaps (cluster 2) — ranked highest-value missing

1. **Weak-coupling / Feshbach-Schur (2512.08141) — entirely uncaptured.** The
   newest paper, a self-contained perturbation-theory framework (resolvent,
   condition number, γ-cospectrality, T.rex pendant edges, HFST, resonant
   tunneling, Anderson robustness, edge-oracle search). New
   `Dowsing/WeakCoupling.lean` with `resolvent`, `feshbachMap`, `IsHighFidelityST`,
   `IsGammaCospectral`, `TRex`, `trex_hfst` (Thm 4.1). Touches PST, Search,
   localization — broadest payoff.

2. **PST speed limit + anti-Zeno protocol (1609.01854, 2209.08160) — uncaptured.**
   The quantitative `J_max·τ ≥ (π/4)√(N²−…)` bound (both parities), θ-revival,
   monorail/dual-rail heralded protocol, fastest-FR `J_maxτ₀ ≥ Nθ/2`. Note the
   only existing "anti-Zeno" (`CarusoSpeedup.lean`) is a *different*, open-system
   mechanism — do not conflate. New `Dowsing/AntiZenoSpeed.lean` + speed-limit
   theorem in `StdLib/Path.lean` (currently only a docstring mention of Yung).

3. **`K`-fractional revival framework (2004.01129) — uncaptured beyond pairs.**
   Subset FR `IsKFR`, density-matrix periodicity, commuting/minimal partition
   `P_min^K`, set eigenvalue support `Φ_K`, ratio condition (Thm 5.5),
   decomposability (Thm 7.2), **non-monogamy** of FR. New
   `Dowsing/SubsetFractionalRevival.lean`; reuses the existing pair-level
   strong-cospectrality/Godsil-ratio infra as the `|K|=2` base case.

4. **Graphs-with-tails concrete operations (2211.14704) — only abstract shadow.**
   Missing `oneSum`, `cone`, `rootedProduct`, eventually-free Jacobi, the
   Golinskii decoupling theorem `A(H)=ℑ_v⊕J̃₀`, walk matrix / controllability,
   dark subspace, sedentariness, dual-rail PST. New `StdLib/GraphsWithTails.lean`
   feeding the existing `FilteredColimitPST` scaffold; `cone_pst_with_tail`
   (Thm 5) is the natural headline.

5. **1907.04729 scheme `(g,h)` invariants + Hamming Kummer characterization.**
   `bose_mesner_fr_iff` exists but with a `True` placeholder for the spectral
   congruences and a mis-stated Hamming time; add `schemeG`/`schemeH`,
   `fr_iff_h`/`balancedFR_iff_h_doublyEven` (Thm 3.5) and the `α₂`/Kummer
   balanced-FR characterization (Lemma 4.8, Prop 4.9) in
   `FractionalRevivalNC.lean` + `StdLib/Hamming.lean`.
