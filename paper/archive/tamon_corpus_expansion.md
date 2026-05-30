# Tamon-Corpus Expansion (May 2026)

This note expands the Tamon corpus in `references/` with 20 newly-fetched
papers, all confirmed downloaded and `pdftotext`-extracted (no 404s). For
each paper we give a one-sentence summary of the principal theorem(s) and
a brief integration note explaining which tower / dowsing-rod file / current
sorry it bears on. Honesty notes: many entries are literature context rather
than direct framework changes; the truly load-bearing items are gathered
under "Priority additions" at the end.

## Tower 2 — chiral / signed graphs

### arXiv:2301.01473 — State Transfer in Complex Quantum Walks (2023)
*Acuaviva, Chan, Eldridge, Godsil, How-Chun-Lun, Tamon, Wright, Zhang.*
Proves that the oriented edge K2 and the oriented 3-cycle are the *only*
oriented graphs (Hermitian adjacency with ±i entries) admitting universal
PST, constructs the first infinite family of *Hermitian* graphs with
one-way PST and PST without periodicity, and gives infinite families of
non-monogamous PGST in rooted graph products.
**What this adds to graphplay:** This is the missing Tower 2 predecessor to
Levine et al. 2605.04414. The "PST without periodicity" result is exactly
the dichotomy our `ChiralPeriodicity` lemmas attempt to formalise — we
should cite this as the literature precedent for the sorried "chiral PST
implies periodicity only under algebraic-entry hypothesis" claim.

### arXiv:1211.0505 — Perfect State Transfer on Signed Graphs (2012)
*Brown, Godsil, Mallory, Raz, Tamon.* The signed join of a negative K2 with
any (n,3)-regular graph has PST (improving as n grows); signed complete
graphs achieve PST whenever their positive part is regular-with-PST and
their negative part is periodic; double covers transfer PST from the signed
to the unsigned world.
**What this adds to graphplay:** The original signed-graph PST paper and
the direct ancestor of our chiral story. The double-cover construction is
the combinatorial twin of our `Graphplay/Chiral/DoubleCover.lean` lift.
Their exterior-power family (many-fermion PST) is the unsigned-to-signed
bridge currently encoded informally in Tower 2's spine outline.

### arXiv:1310.3885 — Universal State Transfer on Graphs (2013)
*Cameron, Fehrenbach, Granger, Hennigh, Shrestha, Tamon.* Graphs with
universal state transfer have distinct eigenvalues and a flat eigenbasis;
the switching automorphism group is abelian (cyclic if PST); explicit
prime-length cycle families with universal PGST exist, and (real-symmetric)
universal PGST is achievable even though Kay forbids real universal PST.
**What this adds to graphplay:** Provides the flat-eigenbasis lemma we
informally invoke when stating "chiral universal PST forces a Schur-flat
spectrum" in the Tower 2 outline. Conjectures stated here are resolved by
Acuaviva–Tamon 2301.01473 — citing both together establishes a clean
"conjecture/resolution" arc.

### arXiv:1701.04145 — Universality in Perfect State Transfer (2017)
*Connelly, Grammel, Kraut, Serazo, Tamon.* New characterisations of
universal-PST graphs extending Cameron et al.; non-circulant universal-PST
families (all prior examples were circulant); for circulants of prime,
prime-square, or 2-power order, universal PST forces the underlying graph
to be complete.
**What this adds to graphplay:** Disposes of the "circulants only" myth.
Mostly literature context — does not displace any sorry — but worth a
footnote in the chiral chapter.

## Tower 4-style — infinite / tail / weak-coupling constructions

### arXiv:2512.08141 — The Strength of Weak Coupling (2025)
*Kay, Tamon.* Rigorously proves (via Feshbach–Schur) the folklore that
attaching weakly-coupled pendant edges ("T.rex" arms) to a large base graph
yields high-fidelity quantum state transfer with transfer time *independent
of diameter*; uses the same trick to circumvent Anderson localisation and
to give a hitting-time-based quantum search.
**What this adds to graphplay:** This is *the* Tower-5 paper. It is the
mathematical core that 2211.14704 ("Graphs with tails") and 2301.07251
("Infinite tail spatial search") gesture at. Our `Graphplay/Tails/` weak-
coupling pendant lemmas can now be stated as direct corollaries of the
Feshbach–Schur block-resolvent identity (Lemma 2.1 in the paper). This is a
genuine sorry-killer for `Tails.WeakPendantFidelity`.

### arXiv:2508.06611 — Matrix Inversion by Quantum Walk (2025)
*Kay, Tamon.* Replaces HHL's phase estimation + amplitude amplification +
Hamiltonian simulation pipeline with a single CTQW that uses a weakly-
coupled subsystem H₀ to expose H⁻¹ via degenerate perturbation theory.
**What this adds to graphplay:** A clean algorithmic *application* of the
T.rex Tower-5 machinery, not a new theorem for the framework. Worth citing
in the pitch as the "downstream payoff" of pendant-edge perturbation
analysis. Currently no Lean file is affected.

## Fractional revival

### arXiv:2004.01129 — Fundamentals of Fractional Revival in Graphs (2020)
*Chan, Coutinho, Drazen, Eisenberg, Godsil, Lippner, Kempton, Tamon, Zhan.*
General spectral framework for FR: generalises cospectral and strongly-
cospectral vertices to *arbitrary subsets*, resolves two open questions of
Chan et al. 2019, and supplies the natural algebraic-graph-theoretic
language for multi-site revivals.
**What this adds to graphplay:** This is *the* canonical FR reference and
should be cited wherever 1907.04729 (FR + association schemes) is cited.
The "strongly cospectral subset" definition is exactly the predicate our
`FR.MultiSiteCospectral` structure encodes (currently with an axiomatised
"existence" sorry). Concrete sorry-killer.

### arXiv:1710.02705 — A Graph with Fractional Revival (2017)
*Bernard, Chan, Loranger, Tamon, Vinet.* Explicit construction of a graph
admitting balanced antipodal FR via a face-diagonal extension of the
hypercube with next-to-nearest neighbour Krawtchouk-coupled spin chains.
**What this adds to graphplay:** A *concrete witness* graph — useful as a
test case for the FR predicates in `Graphplay/FR/` and as an example for
the pitch's "non-trivial FR exists" assertion. Tower 3 (Hamming scheme)
example.

## Speed, engineering, and coronas

### arXiv:2507.18872 — Optimising PST for Timing Insensitivity (2025)
*Kay, Kim, Tamon.* Designs a γ-parametrised family of N-qubit PST chains
that are asymptotically optimal in the trade-off between transfer time and
arrival-peak width, achieving sin⁶(t) (even N) or sin⁸(t) (odd N) arrival
profiles vs. the original sin^{2(N−1)}(t) chains; extends to FR.
**What this adds to graphplay:** Direct engineering payoff for the "PST is
useful in practice" framing. Most impactful as a *citation* in the pitch
section about engineering relevance. The chain construction itself is
parametric and reproducible in Lean, but doing so is out of scope for v3.

### arXiv:1609.01854 — A Note on the Speed of Perfect State Transfer (2016)
*Kay, Xie, Tamon.* Provides a simplified proof of Yung's speed bound
J_max·t₀ ≥ π√(N²−1)/4 for odd N spin chains (the even case was elegant; the
odd case had been less so), in a form that ports to FR and to alternate
phase conditions.
**What this adds to graphplay:** Closes a minor pedagogical gap. Useful
for our `Graphplay/Speed/YungBound` file (currently states even case
cleanly, has a sorry on the odd case) — this paper's argument can be
transcribed directly.

### arXiv:1409.5840 — PST in Laplacian Quantum Walk (2014)
*Alvir, Dever, Lovitz, Myer, Xu, Tamon, Zhan.* Closure properties for
Laplacian PST: complement-PST under nτ ∈ 2πℤ, weak-product transfer under
spectrum-compatibility, double-cone characterisation modulo 4; negative
result that no path P_n (n ≥ 4) has antipodal normalised-Laplacian PST.
**What this adds to graphplay:** Establishes the Laplacian variant as a
parallel track. Our framework currently fixes the adjacency model; if/when
we add a Laplacian flag, this is the literature anchor. Not currently a
sorry-killer.

### arXiv:1605.05260 — Quantum State Transfer in Coronas (2016)
*Ackelsberg, Brehm, Chan, Mundinger, Tamon.* Sufficient spectral conditions
for adjacency-matrix PST/PGST on corona products G ◦ H, with several new
infinite families of PST-bearing graphs.
**What this adds to graphplay:** Corona product is one of the two
operators (alongside join) where we have only stubs in `Graphplay/Products/`.
Fills literature context for any future corona work.

### arXiv:1508.05458 — Laplacian State Transfer in Coronas (2015)
*Ackelsberg, Brehm, Chan, Mundinger, Tamon.* Companion paper showing the
opposite for the Laplacian model: no Laplacian PST on G ◦ H if |G| ≥ 2, but
mild conditions give Laplacian PGST (the first known family of such
graphs).
**What this adds to graphplay:** Pure literature context for now — note
the adjacency / Laplacian dichotomy.

### arXiv:0909.0431 — PST in Weighted Join Graphs (2009)
*Angeles-Canul, Norton, Opperman, Paribello, Russell, Tamon.* Weighted
two-vertex graph joined with any regular graph has PST; the half-join does
not; Hamming graphs have PST between *every* pair, and the hypercube
admits PST between subcube-uniform superpositions.
**What this adds to graphplay:** Backs up our Tower 3 (Hamming) treatment.
Literature context.

### arXiv:0907.2148 — PST, Integral Circulants, and Joins (2009)
*Angeles-Canul, Norton, Opperman, Paribello, Russell, Tamon.* New integral-
circulant families ICG_n({2, n/2^b}∪Q) with PST (n a multiple of 16); a
double-cone family that is non-periodic yet exhibits PST, answering a
question of Godsil.
**What this adds to graphplay:** Literature context for integral
circulants. Notable: the "non-periodic yet PST" example here is later
extended by 2301.01473 to the Hermitian setting.

### arXiv:quant-ph/0509059 — Mixing of QW on Circulant Bunkbeds (2005)
*Lo, Rajaram, Schepens, Sullivan, Tamon, Ward.* New mixing-dynamics
observations for CTQW on circulants and bunkbed extensions defined via
join G+H and Cartesian product G⊕H; identifies regimes where joins inherit
uniform-mixing behaviour from their summands and where Cartesian products
fail.
**What this adds to graphplay:** Concrete join/Cartesian-product mixing
lemmas underpinning Tower 3 product constructions. Literature context for
`Graphplay/Products/` (no current sorry directly closed).

## Chiral / signed-graph algebra

### arXiv:1301.0973 — Which Exterior Powers Are Balanced? (2013)
*Mallory, Raz, Tamon, Zaslavsky.* Characterises which exterior powers
∧^k Σ of a signed graph Σ are balanced (i.e. diagonally similar to an
unsigned adjacency): for k = 1, balanced iff Σ is balanced; for 2 ≤ k ≤
n−2, balanced iff Σ is *antibalanced or balanced*; gives the full sign-
group / cycle-sign analysis.
**What this adds to graphplay:** Direct chiral predecessor and the
exterior-power balance theorem behind Tower 2's many-fermion signed-
unsigned bridge (currently encoded informally in the spine outline). The
"k = 2 dichotomy" is what underlies our `ChiralBundlePST.lean` lift from
single-particle to two-fermion PST — this paper is the literature anchor
for that move and a candidate sorry-killer for the balance-condition
hypothesis there.

## Universal / instantaneous mixing

### arXiv:quant-ph/0608044 — Universal Mixing of QW on Graphs (2006)
*Carlson, Ford, Harris, Rosen, Tamon, Wrobel.* Defines universal mixing
(every probability distribution on V(G) is visited by the CTQW) and
proves: the complete graph K_n is universal mixing; star graphs K_{1,n}
are universal mixing iff n ≥ 2; gives weighted constructions and
obstructions.
**What this adds to graphplay:** The "universal mixing" companion to
1310.3885's universal *state transfer*. Literature context for any future
"chiral universal mixing" extension; not a current sorry-killer.

### arXiv:quant-ph/0308073 — Graphs Resistant to QW Uniform Mixing (2003)
*Adamczak, Andrew, Hernberg, Tamon.* Complete graphs K_n are neither
instantaneous nor average uniform mixing (except K_2, K_3, K_4); a wider
infinite circulant family is resistant to uniform mixing; complements the
Moore–Russell n-cube positive result.
**What this adds to graphplay:** Foundational negative result paired with
0209106 — together they bracket the regime in which Tower 2's chiral
machinery is genuinely *needed* to recover uniform mixing on graphs where
the unsigned walk fails. Background bibliography for chiral mixing.

## Decoherence / open systems

### arXiv:quant-ph/0509163 — Mixing and Decoherence in CTQW on Cycles (2005)
*Fedichkin, Solenov, Tamon.* Analytical proof that *moderate* decoherence
*improves* mixing time on finite cycles: linear improvement for small
decoherence rates, linear deterioration to classical for large rates,
unique optimal middle rate (confirmed numerically).
**What this adds to graphplay:** Direct precedent for the `D8` Noise-
Equitable refinement and Tower-L17 (Caruso-style noise-assisted transport).
The "unique optimum" result is the empirical analogue of what the L17
energy-landscape sweep produces. Should be cited as the foundational paper
for "decoherence is not the enemy of transport."

### arXiv:1911.01953 — A Note on Quantum Markov Models (2019)
*Tamon, Xie.* While goal-state reachability is undecidable in the quantum
POMDP setting (Barry-Barry-Aaronson 2014), the problem of approximating the
optimal average-discounted-reward policy *remains decidable* in the
quantum case — one of the few tractable quantum-Markov problems.
**What this adds to graphplay:** Decidability boundary marker for our
`PrimitiveDSL` and any planned "graph-walk planner". Mostly literature
context, but useful as a sanity check that average-reward objectives are
the right complexity class to target.

## Foundational mixing

### arXiv:quant-ph/0209106 — Mixing in Continuous Quantum Walks on Graphs (2002)
*Ahmadi, Belk, Tamon, Wendler.* Among balanced complete multipartite
graphs, the only instantaneous-uniform-mixing graphs are K₂, K₃, K₄ and
C₄ = K_{2,2}; circulant Fourier analysis is the workhorse.
**What this adds to graphplay:** The foundational "no uniform mixing
except K₂, K₃, K₄" theorem cited by Levine 2605.04414 as the obstruction
that chiral graphs partially circumvent. Genuine canon — should appear in
any Tower 2 / chiral mixing background bibliography.

### arXiv:0808.2382 — Mixing of Quantum Walks on Generalised Hypercubes (2008)
*Best, Kliegl, Mead-Gluchacki, Tamon.* Hypercube uniform-mixing survives
adding a perfect matching x ↦ x⊕η iff |η| is even (with slower mixing);
Hamming H(n,q) is uniform-mixing iff q ≤ 4; bunkbed graphs B_n(A_f) are
not uniform-mixing if supp(f̂) < 2^{n−1}.
**What this adds to graphplay:** Robustness/fragility results for uniform
mixing under structured perturbation. Literature context for Tower 3.

### arXiv:0708.2096 — Non-Uniform Mixing of QW on Cycles (2007)
*Adamczak, Andrew, Bergen, Ethier, Hernberg, Lin, Tamon.* Quantum walks on
even cycles C_n are not instantaneous uniform mixing for n = 2^u (u ≥ 3) or
n = 2^u·q (q ≡ 3 mod 4); average distribution on any abelian circulant is
never uniform, though O(1/n)-close on C_n.
**What this adds to graphplay:** Companion to 0209106. Literature context.

---

## Priority additions to the framework

Three papers stand out as theorems we should explicitly cite (and in two
cases formalise) in pitch v3:

1. **arXiv:2512.08141 (Kay–Tamon, "The Strength of Weak Coupling", 2025).**
   This is the rigorous Feshbach–Schur backbone of Tower 5's entire weak-
   pendant story. Citing it converts our "T.rex tails give high-fidelity
   transfer" line in the spine outline from a *gesture* into a *theorem
   reference*, and the Feshbach–Schur block-resolvent lemma is directly
   transcribable as the elimination of `Tails.WeakPendantFidelity`'s sorry.

2. **arXiv:2301.01473 (Acuaviva–Chan–Godsil–…–Tamon, "State Transfer in
   Complex Quantum Walks", 2023).** Tower 2's missing chiral predecessor.
   It resolves the Cameron-et-al. universal-PST conjecture in the negative
   for oriented graphs, gives the first Hermitian one-way PST family, and
   exhibits PST *without* periodicity — precisely the dichotomy our
   `ChiralPeriodicity` lemmas attempt to formalise. Must be cited
   alongside Levine 2605.04414.

3. **arXiv:2004.01129 (Chan–Coutinho–…–Tamon–Zhan, "Fundamentals of
   Fractional Revival", 2020).** The canonical FR reference, generalising
   cospectrality to arbitrary subsets. Our `FR.MultiSiteCospectral`
   structure currently axiomatises existence; this paper's Theorems 4.3
   and 5.1 give the concrete spectral characterisations that close that
   sorry.

Honest demotions: 2507.18872 (Kay–Kim–Tamon, timing insensitivity) is a
*pitch-relevance* citation (engineering payoff) rather than a
framework-altering theorem; 2508.06611 (HHL via QW) is a downstream
*application* of priority #1, worth a one-line mention in the pitch's
"applications" section but not a sorry-killer.
