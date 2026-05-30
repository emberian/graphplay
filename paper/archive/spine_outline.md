# Spine Outline: Graphplay Paper v2

Working title: *Equitable Quotients Across Five Towers: A Lean-Verified Spine
for Quantum-Walk Search and Transfer, with a Graphon Quasi-Infinite Limit*.

## Reading guide

- **(N)** = novel contribution (not in the existing literature in this form).
- **(F)** = formalization of a known result; the contribution is the Lean
  mechanization and the unified treatment.
- **(T)** = toolkit / engineering vision; conjectural or applied framing.

The five-tower spine is:

```
Tower 0 — Set                   (book-keeping)
Tower 1 — SimpleGraph           (existing Graphplay/Basic.lean)
Tower 2 — WeightedGraph         (Hermitian V x V over C, zero diagonal; chiral included)
Tower 3 — Operator algebra      (coherent algebra; Bose-Mesner; quantum graph)
Tower 4 — Graphon               (measurable kernel; integral operator)
Tower 5 — Categorical           (filtered colimits; Quotient as a functor)
```

The universal object that lives at every tower is the **equitable partition**;
the universal operation is **quotient = a small finite Hermitian matrix**.

The three load-bearing theorems, repeated at every tower:

1. `spec(quotient) ⊂ spec(adj)`, with eigenvector lift.
2. PST / mixing / search lifts from quotient to cell-uniform states.
3. (Tower 5) The Quotient functor preserves filtered colimits, so finite
   quotients extend to the colimit; this is the **quasi-infinite limit
   theorem**.

---

## Section 0. Front matter

- Title, abstract, keywords, MSC.
- Abstract reframed around: equitable-partition spine (F); graphon equitable
  PST/search (N); chiral-on-quotient (N); categorical filtered-colimit
  preservation (N); a search/transfer compiler that emits Lean-checkable
  certificates (T).

## Section 1. Introduction (motivating the five-tower picture)

- 1.1 The Tamon program in one paragraph: PST on quotient graphs
  [Bachman-Fredette-Fuller-Landry-Opperman-Tamon-Tollefson, 1108.0339] makes
  equitable partition the right structural lens; products [Ge-Greenberg-Perez-Tamon,
  1009.1340] are PST constructions; the modern picture
  [Chan-Godsil-Tamon-Xie, 2204.04355; Xie-Tamon, 2301.07251] sharpens the
  spectral criterion and pushes into infinite-dimensional probes.
- 1.2 The compiler frame: given (primitive, hardware) emit (host, partition,
  schedule, certificate). The previous version of this paper observed that
  four-color completion gives one such pipeline. The general pipeline is the
  spine.
- 1.3 What's new: (a) graphon-level equitable partitions with a measurable
  PST/search lift (extending [Bick-Sclosa, 2110.13686] from real dynamics
  to unitary CTQW); (b) chiral signing as optimization on the quotient
  [Levine-Mesapam-Mustico-Tamon-Tucker-Zhan, 2605.04414]; (c) categorical
  framing where the Quotient functor preserves filtered colimits — making the
  "quasi-infinite" of the title precise. (d) Everything mechanized in Lean 4.
- 1.4 Reader map: how the five sections after the spine specialize.

Marker: 1.3a (N), 1.3b (N — chiral-on-quotient direction is new even though
the chiral mixing speedup is from the Levine et al. 2026 paper), 1.3c (N),
1.4 (T), rest (F).

## Section 2. The spine — equitable partitions and the universal lift theorem (Tower 2)

- 2.1 Definitions on `WeightedGraph V := { A : V -> V -> C // Hermitian, zero diag }`
  and `EquitablePartition pi`: cells, cell-to-cell weighted row-sum constancy.
  Lean: `Graphplay/Weighted.lean`, `Graphplay/Equitable.lean`.
- 2.2 The quotient matrix `A/pi : pi -> pi -> C` and the characteristic matrix
  `P : V -> pi`. Statement of `P (A/pi) = A P`. (F, classical Godsil.)
- 2.3 **Theorem 2.1 (spectral lift).** `spec(A/pi) ⊂ spec(A)`; eigenvectors of
  `A/pi` lift to cell-constant eigenvectors of `A` via `P`. Lean: `Spectral.lean`.
  (F)
- 2.4 **Theorem 2.2 (PST lift).** If pi is equitable and the source/target are
  unions of cells, then `e^{-itA}` restricts to the cell-constant subspace,
  and PST on the quotient implies PST on the original. Cite
  [Bachman et al., 1108.0339] and [Ide-Narimatsu, 2209.07688] for the PST and
  search-side antecedents. Lean: `PST.lean`. (F)
- 2.5 **Theorem 2.3 (search lift).** The marked-aware refinement `pi_w` of an
  equitable partition is equitable for `A - gamma e_w e_w^*` and reduces
  spatial search to a bounded-dimensional Hamiltonian. Cite
  [Chan-Godsil-Tamon-Xie, 2204.04355] for the spectral-gap criterion and
  [Ide-Narimatsu, 2209.07688] for the equitable-partition-for-search idiom.
  Lean: `Search.lean`. (F)
- 2.6 Worked example sketch: complete multipartite quotient of the four-color
  completion (carried over from v1); state how K_3 ⨯ K_3 (rook) appears at
  Tower 2 as a regular weighted graph and what the spectral ratio is.

## Section 3. Constructive engine — bundles and their corners

- 3.1 Definition: `GraphBundle Q H B` consists of a base weighted graph `Q`
  on `I`, a family of fiber graphs `H_i` on `V_i`, and a coupling family
  `B_{ij} : V_i -> V_j -> C` defined for each Q-edge `(i,j)`. Lean:
  `Graphplay/Bundle.lean`.
- 3.2 The total graph `Tot(Q, H, B)`. Special cases recovered as corners:
  - `H_i` empty, `B` complete-ones: `TemplateJoin(Q, V)` of v1.
  - `Q` = K_2 with all-ones B: classical Cartesian product
    [Ge-Greenberg-Perez-Tamon, 1009.1340].
  - `Q` an edge, `B = J` everywhere: lexicographic and strong products fall
    out by varying `H_i`.
  - `Q = K_C`, `H_i = 0`: color completion of v1.
- 3.3 **Theorem 3.1 (equitable iff regularity).** `pi = { V_i }_i` is equitable
  for `Tot(Q, H, B)` iff each fiber `H_i` is regular and each coupling `B_{ij}`
  is biregular in the doubly-stochastic sense (row sums constant in i, column
  sums constant in j). (F generalization; this is the bundle-level version of
  classical equitable-partition criteria.)
- 3.4 Corollary: for equal-fiber bundles, `spec(Tot) = m·spec(Q) ⊔ (fiber-internal modes)`,
  recovering the v1 spectral-ratio inheritance and the CNO criterion. Cite
  [Chakraborty-Novo-Ambainis-Omar, 1508.01327] and the cleaner
  [Chan-Godsil-Tamon-Xie, 2204.04355] characterization.
- 3.5 Engineering reading: bundles are the data the compiler emits. The
  certificate is regularity + biregularity, both Lean-checkable.

Marker: 3.1 (N as a unifying definition), 3.2 (F), 3.3 (N synthesis), 3.4 (F),
3.5 (T).

## Section 4. Tower 3 — operator-algebra / quantum-graph upgrade

- 4.1 From `A` to its commutant and to the coherent algebra of pi. Equitable
  partition iff `P P^*` is in the commutant of `A`. Lean:
  `Graphplay/QuantumGraph.lean`.
- 4.2 Bose-Mesner algebra of association schemes as the maximally symmetric
  case; cite [Chan-Coutinho-Tamon-Vinet-Zhan, 1907.04729] for fractional
  revival on schemes, an example of a Tower-3 phenomenon that descends from
  a Tower-2 spine.
- 4.3 Quantum graphs (operator-system definition): a quantum graph on a
  finite-dim C*-algebra `M` is a self-adjoint `M`-bimodule of `B(H)`. State the
  spine in this language: an equitable partition becomes a *coarsening* of the
  diagonal subalgebra; the quotient is a smaller quantum graph.
- 4.4 **Theorem 4.1 (operator-algebra lift).** Theorems 2.1-2.3 generalize: if
  a quantum graph admits a coarsening with bimodule-respecting projection
  `Pi`, then `spec(coarsening) ⊂ spec(original)` and CTQW evolution restricts
  to the range of `Pi`. (F-style, but the unified Tower 2/3 statement is N.)
- 4.5 Fractional revival as a Tower 3 corollary in commutative cases; cite
  [Chan-Coutinho-Tamon-Vinet-Zhan, 1907.04729]. Hamming-scheme reduction
  matches the spatial-search-on-distance-regular result of
  [Chan-Godsil-Tamon-Xie, 2204.04355].

Marker: 4.3-4.4 (N synthesis), rest (F).

## Section 5. Tower 4 — graphons and the quasi-infinite limit theorem (HEADLINE)

This is the section that earns the "quasi-infinite" in the title.

- 5.1 Reminder of graphons as measurable kernels `W : [0,1]^2 -> R`, with the
  associated Hilbert-Schmidt integral operator `T_W` on `L^2[0,1]`. Cite
  [Szegedy, 1003.5588] for spectral graph-limit theory.
- 5.2 Hermitian graphons valued in C; chiral graphons (skew-Hermitian
  imaginary part). Lean: `Graphplay/Graphon/Basic.lean`,
  `Graphplay/Graphon/Hermitian.lean`.
- 5.3 **Definition 5.1 (graphon equitable partition).** A measurable partition
  `[0,1] = ⊔ A_k` is equitable for `W` iff for all `j,k`, the map
  `x ↦ ∫_{A_k} W(x,y) dy` is constant a.e. on `A_j`. Lean:
  `Graphplay/Graphon/Equitable.lean`. (N at this level of generality; closest
  ancestor is [Bick-Sclosa, 2110.13686] which gives the invariant-subspace
  view for real dynamics on graphons.)
- 5.4 **Theorem 5.2 (graphon spectral lift).** If pi is equitable for `W`, the
  finite Hermitian matrix `W/pi` (entry `(j,k) =` the a.e.-constant value times
  `|A_k|`) satisfies `spec(W/pi) ⊂ spec(T_W)`, with measurable cell-constant
  eigenfunction lifts. Lean: `Graphon/Spectral.lean`. (N)
- 5.5 **Theorem 5.3 (graphon CTQW + PST lift).** For Hermitian `W` and an
  equitable partition pi with measurable cell-constant initial state, the
  one-parameter unitary group `e^{-itT_W}` restricts to the cell-constant
  subspace and acts there as `e^{-it W/pi}`. PST between cells lifts. Lean:
  `Graphon/PST.lean`. (N — direct extension of [Bachman et al., 1108.0339]
  from finite to graphon.)
- 5.6 **Theorem 5.4 (graphon search lift).** For a marked subset `S` of
  positive measure, the rank-one perturbed Hamiltonian `T_W - gamma·P_S`
  has the refined partition `pi_S` equitable, reducing search to a finite
  Hermitian problem on the quotient. Cite the spectral criterion of
  [Chan-Godsil-Tamon-Xie, 2204.04355] which is now stable under the limit. (N)
- 5.7 **Theorem 5.5 (quasi-infinite limit theorem).** Let `(G_n, pi_n)` be a
  sequence of finite weighted graphs with equitable partitions of bounded
  size r, converging in cut metric to a graphon `W` with equitable partition
  pi of size r, and with the quotient matrices `G_n / pi_n` converging to
  `W / pi` in Frobenius. Then any spatial-search / PST optimum of the
  quotients passes to the limit; the limit is realized on the graphon, and
  the limiting quotient is a *bona fide* finite Hermitian search/PST problem.
  Cite [Xie-Tamon, 2301.07251] (infinite-tail optimality) as the special case
  where the limit is a complete graph plus a path. Cite
  [Bernard-Tamon-Vinet-Xie, 2211.14704] for the transfer-side companion.
  Lean: `Graphon/Limit.lean`. (N — this is the headline.)
- 5.8 Worked example sketch: an `n -> infinity` cycle blowup with bounded
  template `Q` whose quotient stays fixed; the limit is the Cayley graphon on
  the unit interval; the search criterion converges to a closed-form
  expression on Q.

Marker: all of 5.3-5.7 (N); 5.8 (T).

## Section 6. Tower 5 — categorical framing

- 6.1 Category `WGr` of weighted graphs with weight-preserving cell maps.
  Category `EqWGr` of pairs `(G, pi)` with morphisms refining partitions.
  Functor `Q : EqWGr -> Mat_fin(C)` sending `(G, pi)` to its quotient.
- 6.2 **Theorem 6.1 (filtered colimit preservation).** `Q` preserves filtered
  colimits. Concretely: a filtered system of finite equitable quotients whose
  morphisms refine partitions has a colimit equitable partition (possibly
  on a graphon), and the colimit of the quotient matrices is the quotient
  of the colimit. Lean: `Graphplay/Categorical.lean`. (N)
- 6.3 Corollary: the quasi-infinite limit theorem of Section 5 is the
  Tower-4 instance of Theorem 6.1. The Tower-1 inverse-limit observations
  of the v1 paper are the Tower-1 instance.
- 6.4 Adjoint shadow: a left adjoint to `Q` does not exist in general
  (recovering the failed-reflector observation of v1), but a relative
  left adjoint along a chosen template `Q` does exist and is exactly the
  bundle construction of Section 3.

Marker: 6.2 (N), 6.3 (F restatement), 6.4 (N synthesis).

## Section 7. Chiral and CSP specializations

- 7.1 Chiral: a unitary signing `sigma : E -> U(1)` of a bundle. Phase-equitable
  partition: signed row-sums constant per cell. Lean: `Graphplay/Chiral.lean`.
- 7.2 **Theorem 7.1 (chiral signing as optimization on the quotient).** For a
  fixed bundle `Tot(Q, H, B)` with equitable cell partition pi, mixing-time
  optimization over signings `sigma` factors through the quotient: the
  optimum is the optimum of `e^{-it (sigma·Q)}` for a signed quotient `sigma·Q`,
  plus phase contributions from fiber-internal modes that are explicitly
  controllable. Cite [Levine-Mesapam-Mustico-Tamon-Tucker-Zhan, 2605.04414]
  for the speedup result that motivates this. (N — the existing chiral
  mixing paper does the speedup; the spine reduction is new.)
- 7.3 Corollary: chiral uniform mixing on `Tot` reduces to chiral uniform
  mixing on the quotient `Q`, modulo a fiber-resonance condition. This makes
  the search for chiral speedups a small finite optimization.
- 7.4 CSP / relational: a k-ary template `T : I^k -> {0,1}` and a label map
  `f : V -> I` induce a `k`-uniform hypergraph; the incidence matrix gives
  a Tower-2 weighted graph on `V ⊔ E`. Equitable partition on this incidence
  graph recovers the standard fractional/clonoid invariants. Lean:
  `Graphplay/Relational.lean`. The k=2 case is exactly the v1 pullback
  graph; new content is k > 2.

Marker: 7.1-7.3 (N), 7.4 (N for the k>2 case, F for k=2).

## Section 8. Toolkit-for-engineering vision

- 8.1 Compiler signature: `(primitive: PST | Mixing | Search, hardware: Constraints)`
  `-> (host: GraphBundle, partition: EquitablePartition, schedule: Hamiltonian(t), certificate: LeanProof)`.
- 8.2 Existing prototype (`tools/search_compiler.py`) emits the host, partition,
  and a numerical schedule. The new piece is a Lean-checkable certificate:
  the artifact `Graphplay/Toolkit/Certificate.lean` types a `Certificate p h`
  whose existence is exactly the relevant spectral/equitable hypothesis.
- 8.3 Worked end-to-end: from a CSP-shaped scheduling problem on a fabric
  with hardware-zone constraints to (i) a multi-template pullback, (ii) the
  equitable partition for marked-vertex search, (iii) the certified spectral
  ratio. Carry over the rook, hypercube, surface-K_7, and powerlaw-C_8
  examples from v1; reinterpret each as an instance of Theorem 3.1.
- 8.4 Limits and honest gaps: noisy CTQW, time-dependent schedules, and
  open-system extensions. The bundle/quotient picture survives unitary
  perturbations whose generator is itself equitable; everything else is open.

Marker: all (T).

## Section 9. Connections, open directions, what's next

- 9.1 Graphops (Backhausz-Szegedy) versus graphons: the quotient survives in
  the more general graphop setting whenever the operator commutes with the
  characteristic projection. Lean port is open.
- 9.2 The Heawood-on-surface direction of v1 lives at Tower 2 with a chosen
  template `Q = K_{H(g)}`; a topological version of Tower 6 (homotopy types
  of partitions) might unify surface-coloring spectral budgets with categorical
  filtered-colimit preservation. (T)
- 9.3 Fractional revival on graphons; PST on Cayley graphons of locally
  compact groups; chiral signings as connections on a principal U(1)-bundle
  over the base template.
- 9.4 Tino-corpus question: which families in the Tamon corpus admit a
  graphon quasi-infinite limit *and* are chiral-extendable? Conjecture:
  exactly those for which the Bose-Mesner algebra at Tower 3 is generated
  by the partition's characteristic projections.

Marker: 9.1, 9.3, 9.4 (T conjectures); 9.2 (T).

## Section 10. References

Bibtex-style list. Required entries (read .txt summaries to anchor):

- 1108.0339 Bachman-Fredette-Fuller-Landry-Opperman-Tamon-Tollefson 2011
- 1009.1340 Ge-Greenberg-Perez-Tamon 2010
- 2204.04355 Chan-Godsil-Tamon-Xie 2022
- 2301.07251 Xie-Tamon 2023
- 2211.14704 Bernard-Tamon-Vinet-Xie 2022
- 2209.07688 Ide-Narimatsu 2022
- 1907.04729 Chan-Coutinho-Tamon-Vinet-Zhan 2019
- 2312.06906 Kirkland-Monterde 2023
- 2605.04414 Levine-Mesapam-Mustico-Tamon-Tucker-Zhan 2026
- 2110.13686 Bick-Sclosa 2021 (graphon dynamical systems)
- 1003.5588 Szegedy 2010 (graphon spectral regularity)
- 2004.00677 Gao-Caines 2020 (graphon LQR invariant subspaces)
- 1508.01327 Chakraborty-Novo-Ambainis-Omar
- 2501.08148 King-Linnebacher-Orth-Rizzi-Morigi
- 2506.21108 Li-Luo-Feng-Li
- 1406.0339 Sadowski
- 1706.06939 Wong
- math/0109191 Freitas

---

## Cross-reference summary (which sections are N / F / T)

| Section | Title | Status |
|---|---|---|
| 1 | Introduction | mostly (F) framing + (N) claims previewed |
| 2 | Equitable spine (Tower 2) | (F) — Lean mechanization of classical |
| 3 | GraphBundle engine | 3.1 (N), 3.3 (N), 3.4 (F), 3.5 (T) |
| 4 | Operator-algebra (Tower 3) | 4.3-4.4 (N synthesis), rest (F) |
| 5 | **Graphons + quasi-infinite limit** | **(N) — headline** |
| 6 | Categorical (Tower 5) | 6.2, 6.4 (N), 6.3 (F) |
| 7 | Chiral + CSP | 7.1-7.3 (N), 7.4 partly (N) |
| 8 | Toolkit | (T) |
| 9 | Open directions | (T) conjectures |

The three "headline" novel theorems are 5.5 (quasi-infinite limit), 6.2
(filtered-colimit preservation of the Quotient functor), and 7.1
(chiral-signing-as-optimization-on-the-quotient).
