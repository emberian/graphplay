# Godsil / Coutinho literature haul — relevance notes

Fetched 2026-05-28 by the literature-acquisition agent. All 17 targets landed as
valid PDFs (+ `pdftotext`). No 404s. Sizes/word-counts verified non-trivial.
Anchored against the live Lean tree (`Graphplay/PST/{Cospectrality,GodsilRatio,
QuotientIff}.lean`, `Graphplay/Dowsing/BundlePSTLift.lean`, `Graphplay/Graphon.lean`,
`Graphplay/Chiral.lean`, `Graphplay/ManyBody.lean`, `Graphplay/Mixing.lean`,
`Graphplay/Tower6.lean`) and the gap map in `paper/coverage/SUMMARY.md`.

---

## Tier 1 — equitable-partition / quotient / cospectrality spine

### arXiv:2510.05306 — Quantum walks on finite and bounded infinite graphs (Godsil–Kirkland–Mohapatra–Monterde–Pal, 2025) [references/2510.05306.{pdf,txt}]
**Key results:** Thm 1 — a locally-finite weighted graph is *bounded* (sup of absolute
degree finite) iff `A(G)` is a bounded operator on ℓ²(Z⁺), so `exp(itA)` converges
(recovers Mohar). Thm 2 generalizes the equitable-partition fact (Godsil–Royle Lemma
4.2, `A P = P A_{G/π}`) to *bounded infinite* graphs with **twin / edge-perturbed twin
subgraphs**, then lifts vertex-PST in the quotient to **pair/plus PST** in the parent
(finite or bounded-infinite); plus sedentariness, signed-edge, blow-up, Cayley, and
graphs-with-tails constructions; "almost all planar graphs / trees admit pair PST".
**Maps to graphplay:** This is the *proof technique we need* to close the honest `sorry`s
in `Graphplay/Graphon.lean` (bounded Hermitian-kernel operator `Graphon.op`, `essBound`)
and to give the Tower-4 bounded-infinite equitable story a real engine instead of a
placeholder. Its `A P = P A_{G/π}` for bounded operators is the exact analogue of our
`adj_mulVec_cellUniformVec_eq` / `restrict_eq_symmQuotient` but in ℓ²; supplies the
convergence lemma (`exp(itA)` well-defined when bounded) that `BundlePSTLift` currently
elides. The twin-subgraph machinery is a *new construction to capture* feeding the
pair/plus-state layer (overlaps Chen–Godsil below).

### arXiv:2411.09157 — Quotient graphs and stochastic matrices (Cançado–Coutinho, 2024) [references/2411.09157.{pdf,txt}]
**Key results:** Develops the **symmetrized quotient** `B = P̃ᵀ A P̃` (P̃ = column-normalized
characteristic matrix) — *our exact `symmQuotient` `Q̃`*. Thm 2: two graphs share a
symmetrized quotient via equitable partitions iff there is `M` with both `MMᵀ` and `MᵀM`
doubly stochastic (and `A_G M = M A_H`); Thm 3 extends to **pseudo-equitable** partitions
on vertex-weighted graphs (Perron–Frobenius + doubly-stochastic-by-diagonal-scaling). New
characterization of "same combinatorial quotient". Surveys fractional-isomorphism ⇔
common-equitable-partition (Thm 1).
**Maps to graphplay:** Primary citation + proof source for the *entire* `symmQuotient`
construction in `BundlePSTLift.lean` (`symmQuotient`, `symmQuotient_isHermitian`,
`restrict_eq_symmQuotient`). The pseudo-equitable extension (vertex weights, diagonal
scaling to doubly-stochastic) is precisely the rigor needed to discharge the
"quotient-as-WeightedGraph" `sorry` blocked by our loopless `Q̃`-has-diagonal problem
(SUMMARY blocker #1) — `Q̃` having nonzero diagonal is exactly the vertex-weighted /
pseudo-equitable regime they formalize. Supplies a proof technique we can formalize.

### arXiv:1709.07975 — Strongly Cospectral Vertices (Godsil–Smith, 2017) [references/1709.07975.{pdf,txt}]
**Key results:** Founding paper of strong cospectrality: `E_r e_a = ± E_r e_b` for every
eigenprojector. Characterizations via parallel vertices, the "uncomplicated algebra",
walk-regular graphs, the rational-function test, symmetries/automorphisms, and equitable
partitions; constructions of strongly-cospectral pairs.
**Maps to graphplay:** Direct primary source for `Graphplay/PST/Cospectrality.lean` —
`IsStronglyCospectral`, `IsRealStronglyCospectral`, `IsCospectral`, `eigenProjEntry`, and
the §12 "Automorphisms, Equitable Partitions" section underwrites
`Hom.preserves_stronglyCospectral`. The §11 symmetries result and the rational-function
test (§8) are the technique for several stated-but-unproven lemmas there. Mostly
rigor/citation + a few proof techniques to formalize.

### arXiv:1709.03591 — A New Perspective on the Average Mixing Matrix (Coutinho–Godsil–Guo–Zhan, 2017) [references/1709.03591.{pdf,txt}]
**Key results:** The average mixing matrix M̂ = lim (1/T)∫ U(t)∘U(−t) dt is the matrix of
the orthogonal projection onto the **commutant algebra** of `A`, restricted to diagonal
matrices. rank(M̂) bounds and links to automorphisms.
**Maps to graphplay:** Conceptual backbone for `Graphplay/Mixing.lean` (gap-map #11,
average-mixing spectral formula) and connects directly to
`Graphplay/Dowsing/{CoherentAlgebra,NonCommutativeCoherent}.lean` — the commutant/coherent
algebra is the *same object* those files model. Supplies the clean operator-algebra
statement to formalize M̂ rather than the integral definition. Proof technique + citation.

---

## Tier 2 — PST conditions / Laplacian / oriented / negatives / products

### arXiv:1201.4822 — Number-Theoretic Nature of Communication in Quantum Spin Systems (Godsil–Kirkland–Severini–Smith, PRL 2012) [references/1201.4822.{pdf,txt}]
**Key results:** Complete characterization of **pretty good state transfer** on uniform
XY chains Pₙ: PGST between end vertices iff n = p−1, 2p−1 (p prime) or n = 2ᵐ−1. The
eigenvalue **ratio condition** in number-theoretic form (Kronecker/linear-independence of
eigenvalue differences over ℚ).
**Maps to graphplay:** This is the source for the unproven `IsGodsilRatio.ratios_rational`
in `Graphplay/PST/GodsilRatio.lean` (its comment literally cites "Godsil 2012, Theorem
3.1"). Supplies the number-theoretic technique (Kronecker's theorem) to turn the stated
ratio condition into a proof, and is the canonical PGST citation for any Pₙ example.
Proof technique to formalize.

### arXiv:2002.04666 — Perfect State Transfer on Oriented Graphs (Godsil–Lato, 2020) [references/2002.04666.{pdf,txt}]
**Key results:** PST theory for oriented graphs (skew-symmetric `A`, `iA` Hermitian,
`U=exp(tA)` real orthogonal). Characterizes **multiple state transfer** (a vertex set with
PST between every pair) — impossible for ordinary vertices but possible here — with a new
example.
**Maps to graphplay:** Direct source for `Graphplay/Chiral.lean` (`ChiralSigning`,
`signedBy`, oriented/skew adjacency) and SUMMARY gap #4 (multiple/universal state
transfer). The multiple-state-transfer characterization is the theorem to state in
`PST/Universal.lean`; the skew-symmetric Hamiltonian model justifies the `signedBy`
construction (and the `signedBy_trivial` `sorry`). New construction + proof technique.

### arXiv:1906.01591 — Pair State Transfer (Chen–Godsil, 2020) [references/1906.01591.{pdf,txt}]
**Key results:** Laplacian quantum walk `U=exp(itL)` with **pair states** `e_a−e_b`; two
infinite families with perfect pair-state transfer; a "transitivity" phenomenon absent in
vertex transfer; full characterization on paths and cycles; **plus states** `e_a+e_b`
under signless Laplacian, equivalent to pair transfer on bipartite graphs.
**Maps to graphplay:** Wants the Laplacian layer — SUMMARY blocker #2 (`LoopyWeightedGraph`
/ `L = D−A`). Pair/plus states `e_a∓e_b` are the same "pure-state" objects 2510.05306 and
2502.08103 lift through quotients; this is the original construction. Once the Laplacian
walk exists this gives concrete families (paths/cycles characterization) to capture.
New construction; blocked on #2.

### arXiv:2502.08103 — Perfect state transfer between real pure states (Godsil–Kirkland–Monterde, 2025) [references/2502.08103.{pdf,txt}]
**Key results:** PST between **real pure states** (unit vectors / 1-dim subspaces), adjacency
*and* Laplacian. Three theorems: (i) every periodic real pure state has PST with some `y`;
(ii) every connected graph admits PST between *some* real pure states; (iii) for any
`x,y,τ` there is a real symmetric `M` realizing PST. Spread-of-graphs bound on minimum PST
time (join graphs optimal). Full pair/plus characterization on Pₙ and complete bipartite.
**Maps to graphplay:** Generalizes vertex-PST (`e_a`) to arbitrary real pure states — the
right abstraction to unify `Graphplay/PST.lean` vertex transfer with the pair/plus work,
and slots above `Cospectrality.lean`'s `IsRealStronglyCospectral`. Result (iii)
(any-`M`-realizes) is a clean existence theorem; spread bound connects to join
constructions (gap #9 / `Bundle.lean` joins). Proof technique + new framing.

### arXiv:2305.10199 — No perfect state transfer in trees with > 3 vertices (Coutinho–Juliano–Spier, 2023) [references/2305.10199.{pdf,txt}]
**Key results:** The only trees with adjacency-model PST are P₂ and P₃ (resolves Godsil
2012 / Coutinho–Liu 2015 conjecture). Continued-fraction / matching-polynomial technique.
**Maps to graphplay:** Sharp **negative result** to cite alongside the `StdLib/Path.lean`
PST facts and any tree examples; bounds what the spine can hope to prove. Pairs with
2206.02995. Rigor/citation (a no-go that prevents wasted formalization effort on tree PST).

### arXiv:2206.02995 — Strong cospectrality in trees (Coutinho–Juliano–Spier, 2022) [references/2206.02995.{pdf,txt}]
**Key results:** No tree has 3 pairwise strongly-cospectral vertices (answers Godsil–Smith
2017). Continued-fraction argument on characteristic-polynomial ratios.
**Maps to graphplay:** Companion no-go for `PST/Cospectrality.lean`'s `IsStronglyCospectral`
— a structural ceiling on strong cospectrality in trees; good citation, and the
continued-fraction technique is reusable for the rational-function test (1709.07975 §8).
Rigor/citation + technique.

### arXiv:1501.04396 — Perfect state transfer in products and covers of graphs (Coutinho–Godsil, 2018) [references/1501.04396.{pdf,txt}]
**Key results:** PST when `A` is a sum of tensor products of 01-matrices; tensor-product
graphs; covers. Many new PST families.
**Maps to graphplay:** Directly serves SUMMARY blocker #3 (first-class `□`/tensor/strong
products + spectral-sum lemma, target `Product.lean`) — the tensor-product PST and
spectral-sum arguments are what `Bundle.lean`'s product corners want promoted to a real
operator. Also feeds covers (relevant to fractional-iso / 2411.09157). New construction +
proof technique; blocked on #3.

---

## Tier 3 — mixing / surveys / weighted-path / periodicity

### arXiv:1103.2578 — Average Mixing of Continuous Quantum Walks (Godsil, 2011) [references/1103.2578.{pdf,txt}]
**Key results:** Defines M̂; proves it is PSD with **rational entries**; closed forms — Pₙ:
`(2J+I+T)/(2n+2)`; pseudocyclic schemes / odd cycles: `((n−m+1)/n²)J + ((m−1)/n)I`.
**Maps to graphplay:** Concrete computable targets for `Graphplay/Mixing.lean` (gap #11);
the rationality theorem and the Pₙ / cycle closed forms are exactly the example-table
results to formalize, and pair with 1709.03591's commutant formulation. New
construction/results to capture.

### arXiv:1301.5889 — Uniform Mixing and Association Schemes (Godsil–Mullin–Roy, 2014) [references/1301.5889.{pdf,txt}]
**Key results:** Instantaneous **uniform mixing** on distance-regular graphs via complex
Hadamard matrices in association schemes. Only SRGs with IUM: Paley(9) + certain RSHCD
graphs; bipartite uniform mixing ⇒ 4∣n (and regular ⇒ n is a sum of two squares); no IUM
on C₂ₘ (m≥3) or Cₚ (p≥5 prime), but ε-uniform mixing on all Cₚ.
**Maps to graphplay:** Feeds `Graphplay/Mixing.lean` uniform-mixing side (gap #11) and the
association-scheme / Bose–Mesner thread (relevant to `Dowsing/FractionalRevivalNC.lean`
Bose–Mesner FR, gap #16). Strong no-go list + Hadamard technique. New results to capture +
rigor.

### arXiv:2404.02236 — Selected Open Problems in Continuous-Time Quantum Walks (Coutinho–Guo, survey, 2024) [references/2404.02236.{pdf,txt}]
**Key results:** Survey of open problems in three areas: PST, instantaneous uniform mixing,
average mixing matrices. Curated problem list with context.
**Maps to graphplay:** Roadmap / framing document — use to prioritize which spine
extensions are research-frontier vs. settled, and to phrase the paper's "open problems we
formalize" narrative. Rigor/citation (orientation, not a proof source).

### arXiv:2509.09948 — Orthogonal polynomials, quantum walks and the Prouhet–Tarry–Escott problem (Cançado–Coutinho–Spier, 2025) [references/2509.09948.{pdf,txt}]
**Key results:** Weighted-path (tridiagonal, possibly weighted loops) PST: tuning weights so
the first vertex transfers to any position is equivalent to a case of the **Prouhet–Tarry–
Escott** problem (hence hard). New three-term-recurrence orthogonal-polynomial results,
incl. full characterization of when two polynomials lie in one OP sequence.
**Maps to graphplay:** Weighted paths with **weighted loops** = the loopy/tridiagonal regime
of SUMMARY blocker #2 (`LoopyWeightedGraph`) and the Chebyshev/Jacobi-matrix angle behind
`StdLib/Path.lean`. The OP three-term-recurrence machinery is the right algebraic tool for
weighted-path spectra; the PTE equivalence is a hardness/no-go to cite. Proof technique +
hardness citation; relevant to #2.

### arXiv:0806.2074 — Periodic Graphs (Godsil, 2008) [references/0806.2074.{pdf,txt}]
**Key results:** `X` periodic at `u` iff ratios of distinct nonzero eigenvalues are rational;
converse holds; regular graph periodic iff eigenvalues distinct. For a wide class (incl.
vertex-transitive), if PST occurs then `H(τ)` is a scalar × fixed-point-free involution.
New PST family via Hadamard matrices.
**Maps to graphplay:** Periodicity is the PST prerequisite underlying `PST/GodsilRatio.lean`
— the rational-ratio ⇔ periodic theorem is the companion to `IsGodsilRatio` and supplies
the converse direction. The "PST ⇒ involution" structural result constrains
`PST.lean`/`Tower6.lean` transfer maps. Proof technique + citation; pairs with 1201.4822.

### arXiv:2110.07762 — Fractional revival on non-cospectral vertices (Godsil–Zhang, 2022) [references/2110.07762.{pdf,txt}]
**Key results:** First infinite family of *unweighted* graphs with **fractional revival
between non-cospectral vertices** (FR does not require cospectrality, unlike PST); first
examples with **overlapping** FR pairs. Subset-transfer framing.
**Maps to graphplay:** Direct constructions for `Graphplay/Dowsing/FractionalRevivalNC.lean`
(the file name *is* "non-cospectral") and gap #6 (`K`-fractional-revival framework,
non-monogamy). The overlapping-pairs examples address the non-monogamy/`P_min^K` items.
New constructions to capture.

---

## Top 5 to integrate (ranked by leverage for current proof effort)

1. **2411.09157 (Cançado–Coutinho, symmetrized quotient + pseudo-equitable).** Highest
   leverage: it is the *primary source and proof recipe* for the already-central
   `symmQuotient` `Q̃` in `BundlePSTLift.lean`, and its pseudo-equitable / vertex-weighted
   theory is exactly the regime that resolves the loopless-`Q̃`-has-diagonal `sorry`
   (SUMMARY blocker #1). Citing + formalizing it strengthens the spine's foundation
   directly.
2. **2510.05306 (Godsil et al., bounded infinite graphs).** Supplies the boundedness ⇒
   bounded-operator ⇒ `exp(itA)`-converges machinery and the bounded-operator equitable
   identity `AP = P A_{G/π}` — the missing engine for `Graphon.lean` and the Tower-4
   bounded-infinite story (see note below).
3. **1709.07975 (Godsil–Smith, strongly cospectral vertices).** The founding text for
   `PST/Cospectrality.lean`; its equitable-partition (§12) and rational-function (§8)
   sections underwrite the stated-but-unproven functoriality and characterization lemmas.
4. **1201.4822 (Godsil–Kirkland–Severini–Smith, ratio condition / PGST).** The exact source
   cited by `GodsilRatio.lean`'s unproven `ratios_rational`; Kronecker-theorem technique to
   convert that statement into a proof, plus the canonical PGST characterization.
5. **0806.2074 (Godsil, periodic graphs).** The periodicity ⇔ rational-ratio result is the
   converse half that `GodsilRatio.lean` lacks and the prerequisite layer beneath all PST
   existence; small, foundational, and pairs with #4. (Close runner-up: 1501.04396 for
   product/tensor PST, which serves blocker #3 but is gated on building `Product.lean`.)

## Does 2510.05306 / 2411.09157 change the Tower-4 (graphon / bounded-infinite) story?

Yes, and they push in the *same* direction. Today `Graphplay/Graphon.lean` defines a
bounded Hermitian kernel and `Graphon.op` with an `essBound` field but leaves the
operator-theoretic equitable lift informal. **2510.05306 says the right hypothesis is
graph-side boundedness (sup absolute degree), which is *equivalent* to `A` being a bounded
ℓ² operator (Mohar) — i.e. our `essBound` is the correct and provably-sufficient
condition** — and gives the bounded-operator version of `AP = P A_{G/π}` plus convergence
of `exp(itA)`. So the Tower-4 graphon equitable partition should be reframed as a *bounded
self-adjoint operator with an invariant cell-uniform subspace*, mirroring the finite
`cellUniformSubspace_invariant` proof, rather than a measure-theoretic special case.
**2411.09157 complements this on the finite side**: it shows the symmetrized quotient `Q̃`
is the canonical invariant and that the vertex-weighted (pseudo-equitable) generalization
— exactly what a graphon-cell quotient produces (cells carry mass `μ(C_i)`, hence weights)
— is the natural setting. Combined recommendation: treat the bounded-infinite graphon
quotient as `P̃ᵀ op P̃` on the cell-uniform subspace of a bounded self-adjoint operator,
porting the finite `symmQuotient`/`restrict_eq_symmQuotient` proofs to the operator setting
with boundedness (not finiteness) as the only essential hypothesis. This unifies Tower-4
with the finite spine instead of treating it as a separate analytic track.
