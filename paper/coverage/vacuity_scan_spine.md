# Vacuity / stub scan — load-bearing spine (READ-ONLY audit)

Date: 2026-05-30. Auditor pass over the 18 declared spine files. No `.lean` files
were edited. Worst-first (D, A on top).

## Summary

- **Total findings: 13** (across the spine).
- Per-category: **D = 1**, **A = 3**, **B = 4**, **C = 2**, **F = 0**, **E = 0**.
- **Spine-lift theorems verified GENUINE (non-hollow): 9** (see list at bottom).
- **All real vacuity is concentrated in `Graphplay/Relational.lean`**, which is a
  self-described "scaffold" (its header literally says "Proofs are mostly `sorry`").
  The **CTQW spine proper — Equitable / Weighted / Spectral / PST / Mixing /
  Search / Product / Product.PST / Loopy{,/Laplacian,/Search} / PST.DiagonalShift /
  PST.QuotientIff / PST.GodsilRatio / ForMathlib — is NOT hollow.** The headline
  lift theorems are genuine, with satisfiable nonempty-cell hypotheses and real
  (non-degenerate) `symmQuotient`-based conclusions.

The remaining spine `sorry`s (Mixing, Search, DiscreteTime, the GodsilRatio
Diophantine half, QuotientIff eigenbasis-transport, HilbertSchmidt Fubini/compact)
are **honest deferrals attached to genuinely-stated, non-vacuous theorems** — they
are flagged below for completeness but are NOT vacuity in the adversarial sense.

## Findings table

| file:line | category | name | one-line why | suggested fix |
|---|---|---|---|---|
| Graphplay/Relational.lean:580 | **D** | `chromatic_hierarchy` (χ_f ≤ θ ≤ χ_q ≤ χ) | All four invariants are `:= 0` (lines 538/546/554/561), so the headline Lovász-sandwich inequality collapses to `0 ≤ 0 ≤ 0 ≤ 0`; proof is `simp [..., le_refl]`. Green only because the defs are stubs. | Give `chromaticNumber`/`fractionalChromaticNumber`/`lovaszTheta`/`quantumChromaticNumber` real bodies, then re-prove. |
| Graphplay/Relational.lean:409 | **A** | `incidence` | Body `:= 0`; intended root-of-unity incidence matrix. | Instantiate the Tower-2 root-of-unity formula. |
| Graphplay/Relational.lean:416 | **A** | `degreeMatrix` | Body `:= 0`; intended diagonal degree matrix. Downstream `HypergraphPST` "depends on this `0` value." | Real diagonal degree. |
| Graphplay/Relational.lean:734 | **A** | `RelStructure.toSimpleGraph` | Body `:= (⊥ : SimpleGraph V)` — always the empty graph regardless of input `_A`. | Reconstruct adjacency from `_A.rel`. |
| Graphplay/Relational.lean:461 | **B** | `equitable_partition_lifts` | Concludes `: True := trivial`; the stated "induces a Tower-2 equitable partition" content is entirely in the doc comment, the proposition is `True`. | State as the actual `∃ EquitablePartition …` and prove/sorry. |
| Graphplay/Relational.lean:739 | **B** | `ofSimpleGraph_toSimpleGraph` | Concludes `: True := trivial`; claims a roundtrip identity but asserts nothing. | State `toSimpleGraph (ofSimpleGraph G) … = G`. |
| Graphplay/Relational.lean:759 | **B** | `example` (RelPullback recovers PullbackGraph) | `: True := trivial`; the asserted structure equality is only in the comment. | State the data equality. |
| Graphplay/Relational.lean:595 | **B** | `quantumCSP` | Def body `:= True`; "statement shape only". A `Prop`-valued def that is constantly `True`, so any theorem quantifying over it is vacuous. | Real operator-system-hom existence predicate. |
| Graphplay/Relational.lean:728 | **C** | `toSimpleGraph` hyp `_symm : ∀ x y, True` | Vacuous hypothesis (always satisfiable, says nothing); paired with `_irrefl` below. | Use genuine symmetry/irreflexivity of `_A.rel`. |
| Graphplay/Relational.lean:729 | **C** | `toSimpleGraph` hyp `_irrefl : ∀ x, True` | Same — vacuous, unused. | Genuine irreflexivity hypothesis. |
| Graphplay/PST/QuotientIff.lean:551 | (B-adjacent) | `phantom_symmetry_PST_exists` | A pure existential closed by `sorry`: asserts (unproven) existence of a witness `(V,G,P,i,j,τ)` with host PST and no swapping automorphism. The statement is genuine/non-vacuous, but the existence is currently unsubstantiated (witness "parked in examples/"). | Construct the Bachman–Tamon 6-vertex witness, or downgrade to a hypothesis. |
| Graphplay/PST/QuotientIff.lean:618 | (B-adjacent) | `phantom_symmetry_chiral_PST_exists` | Same pattern: `sorry`'d existential asserting unproven existence of a chiral phantom-PST witness. | Construct (trivial signing of the above) or downgrade. |
| Graphplay/Relational.lean:136 | (note) | `RelStructure.complete.rel := True` | Intentional: the *complete* relational structure genuinely relates every tuple, so `:= True` is correct here (not a stub). Listed only to disclaim. | None — correct as written. |

### Honest-deferral `sorry`s in the spine (NOT vacuity — disclosed for completeness)

These theorems are *genuinely stated* (non-trivial conclusions, satisfiable
hypotheses) and merely deferred; none is "green-because-of-a-stub":

- `Mixing.lean:209` `cellBlockAmp_eq_quotient` — host↔quotient cell-block identity; the
  two dependent chiral-mixing lift theorems (`chiralMixingQuotient`,
  `chiralAverageMixingQuotient`) are honest derivations *modulo* this `sorry`, and
  importantly carry **genuine** `ReducesToQuotient`/`hmix` hypotheses (the prior
  `True →` formulations were corrected — see the doc comments).
- `Search.lean:344` `optimal_search_lift`; `Search.lean:374` `search_infinite_tail`
  (reduces to it) — genuine `IsRefinedQuotientOptimalSearch` hypothesis (prior vacuous
  `True →` / `A → A` formulations were corrected, per doc comments).
- `Loopy/Search.lean:287` `searchSuccess_optimal_time` — genuine spectral-gap hyp `hgap`.
- `DiscreteTime.lean` :131,235,310,370,393 — `SzegedyWalk_unitary`, `szegedy_spectrum`,
  etc.; concrete defs (SzegedyWalk, groverCoin, randomWalkOp), deep theorems deferred.
- `PST/QuotientIff.lean:483` `stronglyCospectral_cellUniform_iff_quotient` — eigenbasis
  transport; genuine spelled-out spectral-projector iff. (Its corollary at :496 is
  honestly discharged via this iff.)
- `PST/GodsilRatio.lean:774,863,931` — Godsil Diophantine half / path / cube; honestly
  stated true theorems (file documents *correcting* a prior false `True ↔ (n+1)∣6`).
- `ForMathlib/HilbertSchmidt.lean:~470,550` — self-adjointness Fubini swap & compactness;
  genuine bounded-kernel hyps. The L² Schur core (`kernelIntegralFun_memLp`,
  `kernelIntegralFun_eLpNorm_le_mul`) is **fully proven, no `sorry`**.

## Spine-lift theorems VERIFIED GENUINE (non-hollow)

Each was read in full; hypotheses are satisfiable by non-trivial partitions
(`∀ i, 0 < cellCard i` is met by any all-nonempty-cell partition, e.g. `discrete`
or any honest coarsening), and the conclusion references the genuinely-Hermitian
`symmQuotient = D^{1/2} Q D^{-1/2}` (not a degenerate `quotient`):

1. **`EquitablePartition.restrict_eq_symmQuotient`** (Equitable.lean:425) — the
   combinatorial heart; `A·(cell-uniform) = symmQuotient`-action. Fully proven.
2. **`EquitablePartition.spectrum_subset`** (Spectral.lean:134) — quotient spectrum ⊆
   host spectrum, via real `cellInflateVec` eigenvector lift. Fully proven (the
   "HONEST SORRY" comment is stale; the proof body is complete).
3. **`EquitablePartition.geomMult_le`** (Spectral.lean:217) — multiplicity lift via
   injective `cellInflateLin`. Fully proven.
4. **`EquitablePartition.pst_on_quotient_iff`** (Spectral.lean:303) — Bachman–Tamon
   spectral form. Fully proven.
5. **`EquitablePartition.pst_lift`** (PST.lean:248) and **`pgst_lift`** (PST.lean:298)
   — headline PST/PGST lift; require `hne : ∀ k, cellCard k ≠ 0`, conclusion is real
   `symmQuotient` evolution modulus. Fully proven.
6. **`EquitablePartition.cellUniformPST_iff_quotientPST`** (PST/QuotientIff.lean:407)
   — the keystone Bachman–Tamon **iff**, BOTH directions, no `sorry`. Genuine.
   (`noLeakage_of_equitable` at :321 also fully proven.)
7. **`search_quotient_reduction`** (Search.lean:243) — host search Hamiltonian acts as
   refined-quotient `−γ·Q̃′ − markedDiag` on the cell-uniform subspace; `refineByMarked`
   (Search.lean:67) equitability honestly proved under genuine `hM` (marked = union of
   cells). Fully proven. (This is the real content the deferred `optimal_search_lift`
   would consume.)
8. **`WeightedGraph.cartesianProduct_pst`** (Product/PST.lean:241) — product PST via
   `evolve_cartesianProduct` (Kronecker-sum exp factorization). Fully proven, no `sorry`;
   the whole `exp_kronecker_one` / `exp_one_kronecker` chain is genuine.
9. **`isLoopyPST_laplacian_iff_adjacency_of_regular`** (Loopy/Laplacian.lean:130) and
   **`searchSuccess_shift_eq`** (Loopy/Search.lean:146) — diagonal-shift global-phase
   invariance; both fully proven, resting on the genuine `DiagonalShift` engine
   (`exp_add_smul_one`, `norm_exp_shifted_entry_eq` — all proven, no `sorry`).

Additionally clean (no vacuity): `Weighted.lean` (all evolve unitarity/semigroup
lemmas proven; `isRegular_eigenvalue_real` genuine), `Equitable.lean`
(`symmQuotient_isHermitian` genuine handshake proof; `indiscrete` honestly takes the
regularity witness rather than degenerating), `ForMathlib/Basic.lean` (the
Hermitian↔self-adjoint bridges are real). `IsGodsilRatio`/`IsStronglyCospectral`/
`EigenvalueSupport` are genuine non-stub predicates.
