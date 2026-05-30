# Vacuity / stub scan — Tower-3 + Categorical slice

READ-ONLY audit. Slice: `OperatorSystem.lean`, `QuantumGraph.lean`, `Chiral.lean`,
`Categorical.lean`, `Categorical/Topos.lean`, `Bundle.lean`.

Worst-first (D / A on top). Categories: A placeholder-def, B trivial-conclusion,
C vacuous-hypothesis, D stub-driven-green-vacuity, E false-as-stated,
F degenerate-quantification.

| file:line | cat | name | one-line why | suggested fix |
|---|---|---|---|---|
| Categorical/Topos.lean:530-548 | **D** | `refinement_grothendieck_topology` + `sheaf_is_consistent_cell_data` | def is the *discrete* (maximal) topology `GrothendieckTopology.discrete`; the green theorem `… = ⊤` is true ONLY because of that stub — it proves nothing about the intended "refinement cover" condition (every sieve covers, so consistency-under-refinement is vacuous). | define the genuine refinement topology (cells covered by images of refining sieves); restate/sorry the `= ⊤` theorem honestly. |
| Categorical/Topos.lean:711-745 | **D** + A | `TwoCellWGraphP` / `tower7_bridge` | doc says "natural isomorphisms of partitions — pairs of bijections commuting with adjacency strictly", but the *fields* only require `vertexIso x = f x ∨ = g x` (no bijectivity, no naturality, no adjacency-preservation). So `tower7_bridge`/`tower7_quotient_coherence` are green via the trivial witness `vertexIso := f.base.toFun, Or.inl rfl` — a degenerate 2-cell, not an iso. | add `Function.Bijective` + naturality/adjacency fields; the existence theorems then carry real content. |
| Categorical/Topos.lean:755-760 | **D** | `tower7_quotient_coherence` | same root: green only because `TwoCellWGraphP` is a stub structure (identity 2-cell always exists). | follows from the `TwoCellWGraphP` fix above. |
| OperatorSystem.lean:711-712 | **A** | `OpSysToStarAlg` | functor body is `Functor.const … (carrier := ℂ)` — the *constant* functor at the unit ℂ-algebra, NOT the "*-envelope functor" the docstring/§6 names. (Honestly disclosed in the docstring, but still a placeholder body where real content intended.) | implement the multiplicative-domain action on UCP morphisms, or rename to `OpSysConstStarAlg`. |
| OperatorSystem.lean:812-814 | **A** | `Tower6QuantumToStarAlg` | body is `fun _ => SheafGraph.constSheaf X ℂ` — ignores its input entirely; the "forgetful map induced by `OpSysToStarAlg` on stalks" collapses to constant-ℂ because `OpSysToStarAlg` is itself the const stub. | depends on `OpSysToStarAlg`; real forgetful functor on sheaves needed. |
| QuantumGraph.lean:521 | **A** | `QuantumChromatic` | `:= 0` placeholder (docstring admits it). | define via projective-measurement colouring game. |
| QuantumGraph.lean:525 | **A** | `Chromatic` | `:= 0` placeholder. | define via the adjacency operator-system / classical χ. |
| Categorical.lean:758 | **A** | `GraphonEmbedding.stepGraphon` | `:= { dummy := () }` into the placeholder `Graphon` struct (`dummy : Unit`); the whole graphon target is a stub. | wire to the real `Graphplay.Graphon` type once available. |
| Categorical.lean:763-765 | **B** | `stepGraphon_functorial` | conclusion is literally `: True` (`by trivial`); states nothing. | replace `True` with the functoriality equation. |
| Categorical.lean:769-771 | **B** | `stepGraphon_preservesFilteredColimits_cutnorm` | conclusion `: True` (`by trivial`); names a BCLSV theorem but asserts nothing. | state the cut-norm colimit-preservation. |
| Categorical/Topos.lean:262-284 | **B** (mild) | `FinerThan.join` / `le_join` | "join" def is just `P` itself (the top element); `le_join : Z ≤ join` is the trivial `⟨Z.refines⟩` — it is the top element, not a least-upper-bound, so "join" is misnamed though the proved bound is honest. | rename to `top`/`improperRefinement`, or build the genuine join (with equitability hyp like `meet`). |
| Categorical/Topos.lean:301-308 | B (mild) | `subobject_iso_finerThan` | "subobject classifier iso" is downgraded to "∃ top, ∀ X, X ≤ top" — a true but weak top-element fact, not the claimed order-iso of subobjects. | state/sorry the genuine subobject ≃ FinerThan bijection. |
| Categorical/Topos.lean:348-355 | B (mild) | `internal_exists_is_refinement_witness` | `∃ Z, φ.pred Z` from `φ.pred X` is the trivial `⟨X, hX⟩`; honest but near-tautological "internal ∃". | acceptable as scaffold; tighten to genuine cell-quantifier semantics. |
| Categorical/Topos.lean:669-672 | B (mild) | `assembly_soundness` | repackages two `LawvereEq` constructors (`lift_quotient`, `quotient_lift`) as a conjunction — true by the inductive def, but "soundness" should be a semantic interpretation claim. | state soundness against an actual `WGraphP` model. |
| OperatorSystem.lean:963-977 | F | `quantumColoring_via_UCP` / `_complete` | `quantumColoring_via_UCP S := Nonempty (UCPMap S (K_n_quantum k))`; the `_complete` witness is `UCPMap.id` — a self-map, no zero-pattern/colouring constraint is encoded, so "n-colouring of K_n^q" is trivially witnessed by identity. The intended Stahlke zero-pattern condition (§10 docstring) is absent from the def. | add the adjacency/zero-pattern constraint to `quantumColoring_via_UCP`. |

## Honest (NOT vacuous) — explicitly verified

- **QuantumGraph.lean:530-537 `quantumChromatic_le_chromatic`** — green-tempting `0 ≤ 0`
  was deliberately left as an honest `sorry` with a comment explaining the stub
  would make it vacuous. Correctly NOT category-D. Good.
- **OperatorSystem.lean** complete-positivity infrastructure (`amplification`,
  `IsKPositive`, `padBlock*`, `IsKPositive.of_succ/of_le`, `IsCompletelyPositive.comp`,
  `IsKPositive.one_le_isPositive`) — real, fully-proved content over non-stub defs.
  `choiMatrix` / `isCompletelyPositive_iff_choi_posSemidef` and
  `stinespring_dilation` are honest `sorry`s (deep theorems), not stubs.
- **OperatorSystem.lean:758-775 `QuantumEquitablePartition.toOperatorSystemPartition`** —
  ∃ discharged by the *identity* retract `T = S`. Domain non-empty, statement is a
  genuine existential, witness is real (id UCP map). Borderline-trivial but honestly
  so; the docstring is candid. Not flagged D.
- **OperatorSystem.lean:194-198** `toQuantumGraph/toOperatorSystem` round-trips by
  `rfl` — genuine (same carrier fields), not vacuous.
- **Categorical/Topos.lean `FinerThan.preorder`, `regular_epi_comp`, `discrete_adjoint_forget`,
  `discrete_adjoint_quotient`(sorry), `EPCat.category`, `assembly_lawvere_theory_exists`,
  `assembly_completeness`(sorry)** — preorder/adjunction/equivalence/regular-epi-comp are
  real proofs over real data; the two `sorry`s are honest (adjunction hom-bijection;
  faithful-model existence — note 692 explicitly *replaced* an earlier tautology, good).
- **Categorical.lean** category structures (`WGraph`, `WGraphP`), `Quotient` functor,
  `sigmaDesc`/universal-property lemmas, `chainColimit*`/`cochainLimit*` (Mathlib-backed),
  `Quotient.cellMap_adj_preserving` + `Quotient.mapCocone_isColimit` (honest isolated
  `sorry`s, candidly conditional). Real scaffold, not stub-green.
- **Chiral.lean** — CLEAN. `ChiralSigning`, `signedBy`, `signedBy_preserves_equitable`,
  `unitaryHammingChiralK4Signing`/`unitaryHammingChiralK4` are real fully-proved
  constructions; `chiral_mixing_optimization` is an honest theorem-level `sorry`
  over genuine (non-stub) `CellUniformMixing`/`symmQuotient` defs. No vacuity.
- **Bundle.lean** — CLEAN. `GraphBundle`, `total`, products (`cartesianProduct`,
  `lexProduct`, `strongProduct`), `colorCompletion`, `Heawood`, `fiberPartition`
  are all real, fully-proved, over non-trivial data. `ofTemplateJoin` uses zero
  fibers + all-ones couplings *by design* (it models the template join), and
  `ofTemplateJoin_total_eq_templateJoin` proves the intended equation — not vacuous.

## Notes

- `QuantumGraph.lean` and the OperatorSystem CP-machinery are the strongest parts of
  the slice; the genuine vacuity is concentrated in the **categorical scaffold**
  (Topos §1/§5/§7 and Categorical §8 graphon block), where placeholder defs
  (`discrete` topology, `Graphon.dummy`, `TwoCellWGraphP`, const functors) drive
  green theorems that assert less than their names claim.
