# Cluster 1 — PST core: coverage audit

Audit of seven "PST core" papers against the Graphplay Lean development. All
file paths are relative to `/Users/ember/dev/graphplay`. "Captured" means a Lean
`def`/`theorem` *states* the notion; many bodies are `sorry` (statement layer),
which is noted where relevant.

Key existing Graphplay notions (for reference):
- `WeightedGraph` (`Graphplay/Weighted.lean`): Hermitian, loopless `Matrix V V ℂ`; `evolve t = exp(-i t A)`; `isRegular`; `SimpleGraph.toWeighted`.
- `IsPST`, `IsPGST`, `IsCellUniformPST`, `IsCellUniformPGST`, `EquitablePartition.pst_lift`/`pgst_lift` (`Graphplay/PST.lean`).
- `EquitablePartition`, `quotient`, `symmQuotient` (+ Hermitian), `cellInflate`, `refine`, `discrete`/`indiscrete` (`Graphplay/Equitable.lean`).
- `spectrum_subset`, `geomMult_le`, `adj_mulVec_cellInflateVec`, `pst_on_quotient_iff` (`Graphplay/Spectral.lean`).
- `IsStronglyCospectral`(+real variant), `IsCospectral`, `eigenSupport`, `GodsilRatioCondition`, `IsPhantomSymmetric` (`Graphplay/PST/Cospectrality.lean`).
- `EigenvalueSupport`, `IsGodsilRatio`, `isPST_exists_iff_strongCospectral_and_godsilRatio`, path/hypercube/Cayley corollaries, `IsChiralGodsilRatio` (`Graphplay/PST/GodsilRatio.lean`).
- `cellUniformPST_iff_quotientPST` (full Bachman–Tamon iff), `NoCellUniformLeakage`, phantom-symmetry existence, chiral signed iff (`Graphplay/PST/QuotientIff.lean`).
- `GraphBundle`, `total`, `fiberPartition`, `cartesianProduct`/`lexProduct`/`strongProduct`, `colorCompletion`; `pst_iff_quotient` master + GGPT product corollaries + Feder naturality (`Graphplay/Bundle.lean`, `Graphplay/Dowsing/BundlePSTLift.lean`).
- `ChiralSigning`, `signedBy`, `signedBy_preserves_equitable`, `CrossConstant`, `unitaryHammingChiralK4` (`Graphplay/Chiral.lean`); `ChiralBundle`, `pst_iff_quotient_signed_pst`, phase-equitable refinement (`Graphplay/Dowsing/ChiralBundlePST.lean`).
- `Path`/`WeightedPath`/`CLWPath` (`StdLib/Path.lean`), `Hypercube` (`StdLib/Hypercube.lean`), `CayleyGraph` (`StdLib/Cayley.lean`), `Cycle` (`StdLib/Cycle.lean`), `Hamming`/Krawtchouk (`StdLib/Hamming.lean`).

---

### arXiv:1108.0339 — Bachman et al., Perfect state transfer on quotient graphs
**Key theorems/constructions:**
1. Thm 2: `G` has PST a↔b iff quotient `G/π` has PST π(a)↔π(b) (singleton cells), via `A(G)Q = Q·A(G/π)`, `QQᵀ` commutes with `A`; symmetric quotient `A(G/π)_{jk}=√(d_{jk}d_{kj})`.
2. Lemma 1 (Godsil): `QᵀQ=I`, `QQᵀ=diag(|V_k|⁻¹J)`, `QQᵀ` commutes with `A`, `A(G/π)=QᵀAQ`.
3. Thm 4: explicit family `K₁+Aₙ∘Bₙ+K₁` with PST but no automorphism swapping a↔b (answers Godsil's question; "phantom" symmetry).
4. Thm 8: Feder's boson graph `G^⊙k ≅ Gᵏ/π` (orbits of `Sₖ`); PST on `G` ⇒ PST on `G^⊙k`.
5. Thm 9/10: composition — `(G^m₁/π₁)^m₂/π₂ ≅ G^(m₁m₂)/π₃`; `⊗ₖ(Gₖ/πₖ) ≅ (⊗ₖGₖ)/π` with partition matrix `⊗ₖQₖ`.
6. Facts 3,5: weighted `P₄(a,b)`, `P₅(a,b)` PST conditions used in the lifting.

**Captured in Graphplay?**
1. ✅ `Graphplay/PST/QuotientIff.lean:cellUniformPST_iff_quotientPST` (both directions; `sorry`-bodies); also `Graphplay/Spectral.lean:pst_on_quotient_iff` and `EquitablePartition.pst_lift` (`Graphplay/PST.lean`). Uses `symmQuotient` (correctly the `√(d d)` normalization, `symmQuotient_isHermitian` proved).
2. ✅ Lemma 1 facts are the backbone: `symmQuotient_isHermitian` (proved), `cellUniformSubspace_invariant` (proved), `restrict_eq_symmQuotient` (`sorry`), `spectrum_subset`/`adj_mulVec_cellInflateVec`. `QᵀQ=I`/`QQᵀ=diag` not isolated as named lemmas but implicit in the cell-uniform isometry.
3. ✅ `IsPhantomSymmetric` (`Cospectrality.lean`) + `exists_phantomSymmetric_isPST` + `QuotientIff.lean:phantom_symmetry_PST_exists` (all `sorry`; no explicit `K₁+Aₙ∘Bₙ+K₁` witness built).
4. ⚠️ partial `Graphplay/Bundle.lean`/`BundlePSTLift.lean` — the *Cartesian-product* PST closure is captured (`cartesianProduct_pst`), but Feder's boson graph `G^⊙k = Gᵏ/Sₖ` is **not** built. `Graphplay/ManyBody.lean` exists; symmetric-power/`Sₖ`-orbit quotient not formalized as the `G^⊙k` construction.
5. ⚠️ partial `BundlePSTLift.lean:cartesianProduct_quotient_naturality` + `cartesianProduct_iter_quotient` state the Feder naturality square (Thm 9/10) but `iter` form is a `True` stub and the iterated `⊗ₖQₖ` partition is not concretely constructed.
6. ⚠️ partial `StdLib/Path.lean` has `WeightedPath`/`CLWPath` (Krawtchouk) with PST, but the specific `P₄(a,b)`/`P₅(a,b)` self-loop eigen-analysis (Facts 3,5) is not present.

**Gaps to close:**
- `Graphplay/ManyBody.lean` (or new `Graphplay/StdLib/BosonQuotient.lean`): `def federGraph (G) (k) : WeightedGraph (BosonConfigs G k)` and `theorem federGraph_iso_symPower : federGraph G k ≃ symmQuotient (Sₖ-orbit partition of cartProduct^k G)`; plus `theorem federGraph_pst_of_pst : IsPST G a b τ → IsPST (federGraph G k) … τ`.
- `BundlePSTLift.lean`: replace `cartesianProduct_iter_quotient`'s `True` with a real iterated-product statement; build the `⊗ₖ Qₖ` partition explicitly (extend `productPartition`).
- `StdLib/Path.lean`: add `weightedP4`/`weightedP5` with the Fact 3/5 PST `cos`/`sin` conditions, to make the §4 lifting examples concrete.

---

### arXiv:1009.1340 — Ge–Greenberg–Perez–Tamon, PST, graph products, equitable partitions
**Key theorems/constructions:**
1. Prop 2 (weak product): `G×H` has PST if `G` has PST with `t_G Spec(G)⊆ℤπ` and `H` circulant with odd eigenvalues (`A(G×H)=A_G⊗A_H`).
2. Prop 4 / Lemma 5 (lexicographic): `G[H]` (`A_G⊗J+I⊗A_H`) has PST for regular `H` with PST if `t_H|V_H|Spec(G)⊆2ℤπ`; generalized lex product `GC[H]=A_G⊗A_C+I⊗A_H`.
3. Thm 7 / Cor 8 (irregular double cone): `K̄₂+G` has PST with edge weights ∝ Perron eigenvector; `λ̃₀/∆∈Q_{0,1}∪Q_{1,0}`.
4. Thm 9 / Cor 10 (glued double cone): `K₁+G∘G+K₁` PST via circulant connection `C` commuting with `A_G`.
5. Thm 11 (negative): cylindrical cone `K₁+G₁+K̄_m+G₂+K₁` has no PST.
6. Lemma 12 (path-collapsing): `|⟨b|e^{-itA}|a⟩| = |⟨π(b)|e^{-itB_{G/π}}|π(a)⟩|` for equitable distance partition, `B_{jk}=√(d_{jk}d_{kj})`.

**Captured in Graphplay?**
1. ✅ `BundlePSTLift.lean:BundlePSTCorollaries.tensorProduct_pst` (states it; `tensorProduct` itself a `sorry` def). The spectral hypothesis `t_G Spec⊆ℤπ` is folded into `IsPST` rather than `IsGodsilRatio`-checked.
2. ✅ `BundlePSTLift.lean:lexProduct_pst` (states it, `sorry`); `lexProduct` def proved Hermitian in `Bundle.lean`. Generalized `GC[H]` connection-matrix product **not** captured (only `C=J` lex and `C=I` Cartesian).
3. ❌ Irregular/Perron-weighted double cone `K̄₂+G` not captured. No `doubleCone` construction, no Perron-eigenvector weighting.
4. ❌ Glued double cone `K₁+G∘G+K₁` not captured.
5. ❌ Cylindrical-cone negative result not captured (no negative-PST theorems for cones at all).
6. ✅ Lemma 12 = the equitable-distance-partition lifting = `Spectral.lean:pst_on_quotient_iff` / `PST.lean:pst_lift` (singleton-cell special case). Uses `symmQuotient` (matching `B_{jk}=√(d d)`).

**Gaps to close:**
- `BundlePSTLift.lean`: real `tensorProduct`/`conormalProduct`/`disjunctiveProduct` defs (currently `sorry`), and a generalized-lex `genLexProduct G C H` (`A_G⊗A_C+I⊗A_H`) bundle so Prop 4 isn't a special case of `J`.
- New `Graphplay/StdLib/Cone.lean`: `def doubleCone (G) (b∈{0,1}) : WeightedGraph …`, `theorem doubleCone_perron_pst` (Thm 7), `theorem gluedDoubleCone_pst` (Thm 9), and the **negative** `theorem cylindricalCone_no_pst` (Thm 11) — Graphplay currently has *no* negative-PST results, a structural gap.
- Tie the weak/lex product spectral hypotheses to `IsGodsilRatio` (`PST/GodsilRatio.lean`) rather than assuming `IsPST G` as a black box.

---

### arXiv:1310.3885 — Cameron et al., Universal State Transfer on Graphs
**Key theorems/constructions:**
1. Thm 7/8: universal (P)PGST ⇒ diagonalizing unitary is **flat** (type-II) and all eigenvalues **distinct/simple**.
2. Thm 11/15: `SwAut(G)` abelian, `|SwAut(G)| | n`; for universal PST it is **cyclic**.
3. Thm 2/3 + Cor 4: PST a→φ(a) along a switching automorphism `P̃_φ` ⇒ `e^{-itA}=γP̃_φ`; PST then holds b→φ(b) for all b.
4. Thm 16: `SwAut(G)` cyclic of order `n` iff `G` switching-isomorphic to a circulant.
5. Thm 19 / Cor 20: oriented prime cycle `C_p` (`iΘ_n - iΘ_nᵀ`, ±i weights) has universal PGST; `K₂□C_p` likewise for `p≥5` (Kronecker's theorem).
6. §3.2: oriented Hermitian `K₄` has universal PGST; `C₃` (`Circ(0,-i,i)`) has universal *perfect* ST.

**Captured in Graphplay?**
1. ❌ No `IsUniversalPST`/`IsUniversalPGST` predicate; no `IsFlat`/type-II matrix notion; "distinct eigenvalues" not stated as a PST consequence.
2. ❌ No `SwitchingAutomorphismGroup`; no monomial-matrix / switching-equivalence infrastructure (`Chiral.lean` has `ChiralSigning` but not the monomial `P_φ D` group action).
3. ⚠️ partial `Cospectrality.lean:IsStronglyCospectral.of_aut` captures "automorphism ⇒ strong cospectrality" (`sorry`), but the sharper `e^{-itA}=γP̃_φ` and "PST propagates to all vertices" are absent.
4. ❌ Switching-iso-to-circulant characterization absent (no circulant ↔ cyclic-`SwAut` link).
5. ⚠️ partial `StdLib/Cycle.lean` has unsigned `Cycle n` with `λ_k=2cos(2πk/n)`; the **oriented** `iΘ-iΘᵀ` cycle and its universal PGST are not present. `StdLib/Cayley.lean`/`Bundle.cartesianProduct` give `K₂□·` but no universal-ST claim.
6. ⚠️ partial `Chiral.lean:unitaryHammingChiralK4` is the oriented `K₄` (uniform-mixing framing), but universal-PGST is not asserted; oriented `C₃` not built.

**Gaps to close:**
- New `Graphplay/PST/Universal.lean`: `def IsUniversalPST G := ∀ u v, ∃ τ, IsPST G u v τ` (and PGST variant); `def IsFlat (M : Matrix) := ∀ i j, ‖M i j‖ = (card)⁻¹ᐟ²`; `theorem universalPST_eigenbasis_flat` and `…_eigenvalues_distinct`.
- New `Graphplay/SwitchingAutomorphism.lean`: monomial matrices `Pφ·D`, `def SwAut G`, `theorem universalPST_swAut_cyclic`, `theorem swAut_cyclic_order_n_iff_circulant`.
- `StdLib/Cycle.lean`: `def OrientedCycle n : WeightedGraph (Fin n)` with `iΘ-iΘᵀ`, `theorem orientedCycle_prime_universal_pgst` (Kronecker), and oriented `C₃` universal PST.

---

### arXiv:1701.04145 — Connelly et al., Universality in perfect state transfer
**Key theorems/constructions:**
1. Lemma 2: universal PST ⇔ PST from a single vertex `u` to *all* vertices.
2. Lemma 3 / Thm 2: canonical-form type-II diagonalizer `X` (first row & col all-ones); spectral characterization `(λ_k-λ₀)t_ℓ = α_{ℓ,k}`.
3. Thm 4: spacing characterization — `t_{k,k+1}=t_{0,1}` for all `k` iff switching-iso to a circulant.
4. Thm 7 / Ex 1: first **non-circulant** universal-PST family (composite order `n=ab`, eigenvalues `ϑ_b(k)`); `G₆` with spectrum `{0,1,6,7}`.
5. Thm 8: circulant universal PST of prime / prime² / 2-power order ⇒ **dense** (cyclotomic-field argument).
6. Prop 1: non-dense universal-PST circulants exist for `n=pq` (cyclotomic units).

**Captured in Graphplay?**
1. ❌ Not captured (depends on `IsUniversalPST`, absent — see 1310.3885).
2. ❌ No type-II canonical form, no `(λ_k-λ₀)t=α_{ℓ,k}` spectral characterization.
3. ❌ PST-time spacing `T_{u,v}`/`t_{u,v}` machinery absent (no "min PST time" / discrete-subgroup-of-ℝ structure on PST times).
4. ❌ Non-circulant universal-PST family not built; no `G₆`.
5. ❌ Dense-circulant + cyclotomic results absent (no cyclotomic-field / `ℤ[ζ_n]` infrastructure tied to PST).
6. ❌ Not captured.

**Gaps to close:**
- Depends entirely on the Universal/SwitchingAutomorphism modules above. After those: `Graphplay/PST/Universal.lean` add `theorem universalPST_iff_from_one_vertex` (Lemma 2) and `theorem universalPST_canonical_typeII` (Lemma 3 / Thm 2).
- New `def pstTimeSet G u v : Set ℝ` + `theorem pstTimeSet_discrete_subgroup`, then `theorem circulant_iff_uniform_pst_spacing` (Thm 4).
- New `Graphplay/StdLib/UniversalCirculant.lean`: the `ϑ_d` non-circulant family + `G₆` witness; `theorem prime_power_universal_circulant_dense` (cyclotomic, hard — likely long-horizon).

---

### arXiv:1211.0505 — Brown–Godsil–Mallory–Raz–Tamon, PST on signed graphs
**Key theorems/constructions:**
1. Lemma 1 / Cor 2: balanced or anti-balanced signing (`A(Gσ)=±D⁻¹A(G)D`, `D` diagonal ±1) preserves PST; closed under Cartesian product.
2. Thm 3 / Cor 5: signed join `G₁⁻+G₂⁺` PST formula; `K₂⁻+G⁺` (3-regular `G`) has PST at `π/∆`, `∆=√(4+2n)` — *unsigned* join has none, and PST time shrinks as `n` grows.
3. Thm 6 / Cor 7: decomposition `Σ=G⁺∪H⁻` — if `G` has PST, `H` periodic at `a`, `[A(G),A(H)]=0`, then `Σ` has PST; signed complete `G⁺∪Ḡ⁻` PST.
4. Thm 9: double cover of `Σ=G⁺∪G⁻` (`A=A(G⁺)⊗I+A(G⁻)⊗X`) has PST if `G⁺` has PST and `⟨b|cos(tA(G⁻))|b⟩=±1`.
5. §6: signed equitable partitions / signed quotient `A(Σ/π)_{jk}=±√|d⁺_{jk}d⁺_{kj}|`; Thm 11 = signed quotient PST iff (generalizes Bachman et al.).
6. Thm 13: exterior power `⋀ᵏG` (fermionic; anti-symmetrizer `Alt`) has PST given `k` disjoint PST pairs.

**Captured in Graphplay?**
1. ⚠️ partial `Chiral.lean:ChiralSigning`/`signedBy` generalizes ±1 signings to unit-modulus phases, but the **balanced/anti-balanced** notion (`D⁻¹AD`, switching class) and "signing preserves PST" (Lemma 1) are **not** stated. `signedBy_trivial` is `sorry`.
2. ❌ Signed join `G⁻+G⁺` not captured (no `join`/`signedJoin` construction; `colorCompletion` is complete-multipartite, not join).
3. ❌ Decomposition `G⁺∪H⁻` / commuting-subgraph PST not captured; signed complete graph PST absent.
4. ❌ Double cover (`⊗X` lift) not captured — Graphplay has no double-cover construction.
5. ✅ (closest) `Chiral.lean:signedBy_preserves_equitable` (proved!) + `QuotientIff.lean:cellUniformPST_iff_quotientPST_signed` give the signed quotient iff for *cross-constant* phase signings — strictly more general than ±1 signed quotients but the *signed quotient matrix* `±√|d⁺ d⁺|` is a placeholder (`NNReal.toReal 1`), so Thm 11's exact signed-quotient is not realized.
6. ❌ Exterior power `⋀ᵏG`, anti-symmetrizer, fermionic quotient not captured (contrast: boson `G^⊙k` also missing — see 1108.0339).

**Gaps to close:**
- `Chiral.lean`: `def ChiralSigning.IsBalanced`/`IsAntiBalanced` (∃ diagonal ±1 `D`); `theorem signedBy_balanced_preserves_pst` (Lemma 1); finish `signedBy_trivial`.
- New `Graphplay/StdLib/Join.lean`: `def join`/`signedJoin`; `theorem signedJoin_K2neg_pst` (Cor 5, the `π/√(4+2n)` headline).
- New `Graphplay/StdLib/DoubleCover.lean`: `def doubleCover (Σ) : WeightedGraph (V×Bool)` with `A(G⁺)⊗I+A(G⁻)⊗X`; `theorem doubleCover_pst` (Thm 9).
- `QuotientIff.lean`: replace the `NNReal.toReal 1` placeholder with the real signed quotient `±√|d⁺_{jk}d⁺_{kj}|` so `cellUniformPST_iff_quotientPST_signed` is Thm 11.
- New `Graphplay/Dowsing/ExteriorPowerPST.lean`: `def exteriorPower G k` (signed, via `Alt`), `theorem exteriorPower_pst_of_disjoint_pairs` (Thm 13).

---

### arXiv:2301.01473 — Acuaviva et al., State transfer in complex/chiral quantum walks
**Key theorems/constructions:**
1. Thm 2.1: PST a→b in a Hermitian graph iff `a,b` strongly cospectral (with quarrels `q_r`) **and** the rational/quarrel ratio condition on `Φ_a`.
2. Thm 2.2/2.4: periodicity iff ratio condition on `Φ_a`; PGST a↔b iff strong cospectrality + Kronecker quarrel condition (Thm 2.3 Kronecker).
3. Thm 3.5: oriented `K₂` and `K₃` are the **only** oriented graphs with universal PST (settles Cameron conjecture) — eigenvalue-gap counting, `n≤11`.
4. §3.2 (Lemma 3.7): infinite family of oriented graphs with **multiple** PST on 4-vertex subsets (`I⊗H_C₄ + H_X⊗J₄`, odd-integer spectrum).
5. Thm 4.4 / §4.2: **one-way** PST (a→b without periodicity) for transcendental-entry Hermitian graphs; Thm 4.1 phase-factor algebraicity (Gelfond–Schneider).
6. §5 (Thm 5.4): multiple PGST on rooted products `X∘K̂₁,ₘ` and `X∘Pₘ^γ` (loops); generalizes Fan–Godsil, Kempton–Lippner–Yau.

**Captured in Graphplay?**
1. ⚠️ partial `GodsilRatio.lean:isPST_exists_iff_strongCospectral_and_godsilRatio` + `Cospectrality.lean:IsStronglyCospectral.isPST_iff_godsilRatio` capture the *existence-at-some-time* iff (strong cospectrality + Godsil ratio), all `sorry`. The **quarrel** `q_r(a,b)` phase data and the exact `(θ_r-θ_s)/(θ_h-θ_ℓ)` quarrel-ratio (Thm 2.1.ii) are not modeled — Graphplay's `IsStronglyCospectral` carries a phase `ε` per eigenvalue but not the quarrel-difference ratio condition.
2. ⚠️ partial periodicity not defined (`IsPST G u u τ` exists implicitly but no `IsPeriodic`); PGST iff is not stated; **Kronecker's theorem** is cited in comments but not available as a lemma.
3. ❌ Oriented-graph universal-PST classification (`n≤11`, `K₂`/`K₃` only) absent (depends on universal-ST + oriented-graph infra).
4. ❌ Multiple PST predicate (`MultiplePST` on `S⊂V`) and the `I⊗H_C₄+H_X⊗J₄` family absent.
5. ❌ One-way PST / non-periodic PST not captured; phase-factor-algebraicity (Gelfond–Schneider) absent. Graphplay's `IsPST` is modulus-only (`‖evolve‖=1`), so one-way is in principle expressible but no theorem distinguishes it from periodicity.
6. ❌ Rooted product `X∘Y`, loops, double-star / `Pₘ^γ` families absent (Graphplay has no rooted-product or self-loop-vertex construction; `WeightedGraph` is loopless by definition — a real obstruction for loop families).

**Gaps to close:**
- `Cospectrality.lean`: add `def quarrel G a b r : ℝ` and strengthen `IsStronglyCospectral`/the existence iff to the quarrel-ratio form (Thm 2.1); add `theorem Kronecker_approx` (number theory) as the engine for PGST.
- New `Graphplay/PST/Periodic.lean`: `def IsPeriodic G u := ∃ τ>0, IsPST G u u τ`; `theorem periodic_iff_ratio_condition` (Thm 2.2); `def IsMultiplePST G S`.
- `Weighted.lean`: a `LoopyWeightedGraph` variant (allow nonzero diagonal) to host `Pₘ^γ` loop families; then `Graphplay/Dowsing/RootedProductPST.lean`: `def rootedProduct X Y root`, `theorem rootedProduct_multiple_pgst` (Cor 5.3 / Thm 5.4).
- New `theorem exists_oneWay_pst_nonperiodic` (Thm 4.4) — needs transcendental-eigenvalue example; long-horizon.

---

### arXiv:1409.5840 — Alvir et al., PST in Laplacian quantum walk
**Key theorems/constructions:**
1. Facts 2/3: on regular graphs A / `L=D-A` / `Q=D+A` / normalized `𝓛` walks are equivalent (phase/dilation/reversal); on bipartite graphs `L≡Q`.
2. Thm 2 / Cor 3-5: standard-Laplacian PST closed under complementation when `|V|t∈2πℤ`; `K₂+H` Laplacian PST **iff** `|V(H)|≡2 (mod 4)` (double-cone characterization).
3. §4.2: signless-Laplacian double cone `K₂+H` PST when `|V(H)|` even & densely regular (`deg=½|V(H)|-1`).
4. Weak-product closure for normalized Laplacian: `G×H` has PST if `μ(λ-1)τ∈2πℤ` for all eigenvalue pairs; `P₃×{even K, odd Q}` PST.
5. Negative: no `Pₙ` (`n≥4`) antipodal PST under normalized Laplacian; no PST on odd unicyclic / `Pₙ≥5` under signless Laplacian (controllable subsets, line graphs).
6. Fact 7 / almost-equitable partitions: Laplacian quotient `L(G/π)` (Cardoso et al.), used for the double-cone lifting; line-graph / signless-Laplacian spectral correspondence.

**Captured in Graphplay?**
1. ❌ No Laplacian at all. `WeightedGraph` is Hermitian + **loopless**, with `evolve=exp(-itA)`; `L=D-A` (nonzero diagonal) is not representable, and the A/L/𝓛 equivalence (regular/bipartite) is unstated. (`Graphplay/ConservationLaw.lean` etc. mention "Laplacian" but not as a graph-walk Hamiltonian.)
2. ❌ Complementation-closure and the `K₂+H` `≡2 (mod 4)` characterization absent (no `complement`, no `doubleCone`, no Laplacian).
3. ❌ Signless Laplacian `Q=D+A` and its double-cone PST absent.
4. ❌ Normalized Laplacian `𝓛` and its weak-product closure absent.
5. ❌ Laplacian negative results absent (Graphplay has no negative-PST theorems).
6. ⚠️ partial `EquitablePartition` (adjacency) exists, but **almost-equitable** partitions and the **Laplacian** quotient `L(G/π)` (Cardoso) are not present; line-graph / controllable-subset machinery absent.

**Gaps to close:**
- New `Graphplay/Laplacian.lean`: `structure LaplacianGraph` (or reuse a loopy `Matrix V V ℝ`) with `L=D-A`, `Q=D+A`, normalized `𝓛`; `def laplacianEvolve`; `theorem regular_laplacian_equiv_adj` (Fact 2), `theorem bipartite_signless_equiv_standard` (Fact 3).
- `theorem laplacian_pst_closed_under_complement` (Thm 2) + `theorem doubleCone_laplacian_pst_iff_card_2_mod_4` (Cor 5) — requires `complement` and `doubleCone` constructions (shared with 1009.1340 gap).
- `Equitable.lean`: add `def AlmostEquitablePartition` and a Laplacian quotient `laplacianQuotient` (Cardoso et al. Fact 7), plus the singleton-cell Laplacian lifting lemma.
- Normalized-Laplacian weak-product closure + the path negative results (`theorem path_no_antipodal_pst_normalized_laplacian`).

---

## Top gaps (cluster 1)

Ranked by value (breadth across papers × foundational leverage):

1. **Universal / multiple state transfer + switching-automorphism infrastructure**
   (`IsUniversalPST`, `IsFlat`/type-II, `SwAut`, monomial-matrix switching equivalence,
   PST-time sets/spacing). This is the *entire* substance of 1310.3885 and 1701.04145
   and a large part of 2301.01473, none of which is captured. New
   `Graphplay/PST/Universal.lean` + `Graphplay/SwitchingAutomorphism.lean`. Highest
   leverage: unblocks three papers at once.

2. **Laplacian quantum-walk layer** (standard `D-A`, signless `D+A`, normalized `𝓛`;
   A/L equivalence on regular/bipartite; almost-equitable partitions & Laplacian
   quotient). Paper 1409.5840 is *completely* uncaptured because `WeightedGraph` is
   loopless-adjacency-only. New `Graphplay/Laplacian.lean` + `AlmostEquitablePartition`.

3. **Cone / join / complement / double-cover construction family + negative-PST
   theorems**. `doubleCone` (Perron-weighted), `join`/`signedJoin`, `complement`,
   `doubleCover` recur across 1009.1340 (Thm 7/9/11), 1211.0505 (Cor 5, Thm 9), and
   1409.5840 (Cor 5). Graphplay currently has **no** negative-PST results and none of
   these constructions. New `Graphplay/StdLib/{Cone,Join,DoubleCover}.lean`.

4. **Many-particle quotient constructions: Feder boson `G^⊙k` and fermionic exterior
   power `⋀ᵏG`**. The `Sₖ`-orbit / anti-symmetrizer quotients are the concrete payoff
   of the quotient theory in 1108.0339 (Thm 8) and 1211.0505 (Thm 13); only the abstract
   `pst_lift` exists, not these named families. New `Graphplay/Dowsing/{BosonQuotient,
   ExteriorPowerPST}.lean`; leverages existing `ManyBody.lean`.

5. **Quarrel-phase strong cospectrality + Kronecker engine, and the realized signed
   quotient matrix**. The PST/PGST *existence* iffs (Cospectrality/GodsilRatio) and the
   signed quotient iff (QuotientIff) are stated but (a) omit the quarrel-ratio condition
   (2301.01473 Thm 2.1), (b) lack a Kronecker-approximation lemma, and (c) use a
   `NNReal.toReal 1` placeholder for the signed quotient (1211.0505 Thm 11). Closing
   these turns three statement-level iffs into faithful, provable formalizations.

---

### Coverage summary
- **1108.0339**: ~70% (core quotient iff, phantom symmetry, symmQuotient all present as statements; Feder boson graph + concrete witnesses missing).
- **1009.1340**: ~40% (Cartesian/weak/lex product closures stated; all cone constructions + negative result missing).
- **1310.3885**: ~10% (oriented K₄ exists in mixing framing; universal-ST/flatness/SwAut entirely missing).
- **1701.04145**: ~0% (depends on universal-ST infra).
- **1211.0505**: ~25% (signed equitable preservation proved + signed quotient iff stated; balanced-signing PST, join/double-cover/exterior-power missing).
- **2301.01473**: ~30% (existence iff stated; quarrel data, periodicity, multiple/one-way PST, rooted products missing).
- **1409.5840**: ~5% (adjacency equitable theory reusable; no Laplacian layer at all).
