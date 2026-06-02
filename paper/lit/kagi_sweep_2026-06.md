# KAGI Literature Sweep — Graphplay (2026-06)

**Purpose.** Adversarial prior-art sweep for the equitable-partition / CTQW corpus and
the Tower-8 result (equitable partition ≡ bisimulation ≡ Paige–Tarjan coarsest partition
≡ 1-WL) plus the succinct/coinductive-certificate thread. Goal: precision-as-credibility
for Tino Tamon. Verdicts: **CITE** (supports/contextualizes), **MODEL** (formalize/fold in),
**PRE-EMPTS** (already does something we might claim — flagged loudly), **TANGENTIAL**.

Method note: 13 KAGI queries (one pass, no retries) + 6 abstract fetches to confirm claims.
Krovi–Brun (2007) deliberately excluded (already in a prior memo).

---

## Topic 1 — PST / search lifts via the equitable-partition quotient

**Bachman, Fredette, Fuller, Landry, Opperman, Tamon, Tollefson — "Perfect state transfer on
quotient graphs"** (arXiv:1108.0339, 2011; QIC 12(3&4):293–313, 2012).
Claim (confirmed by fetch, verbatim): *"a graph G has perfect state transfer if and only if
its quotient G/π, under any equitable partition π, has perfect state transfer."* A two-way
(iff) lifting theorem; uses it to build new PST graphs.
**Verdict: PRE-EMPTS (the core PST lift).** This is THE classical result our PST-quotient
lift re-derives. Tamon is a co-author — so the senior reviewer *owns* this. We must NOT
present "PST descends to / lifts from the equitable quotient" as new mathematics. Our
genuine delta is the *Lean formalization* and the verified iff, not the theorem.

**Ide & Narimatsu — "Perfect state transfer, Equitable partition and Continuous-time quantum
walk based search"** (arXiv:2209.07688, 2022; Quantum Stud. Math. Found. 2024,
DOI 10.1007/s40509-024-00321-y).
Claim (confirmed): introduces equitable partition + PST to *analytically compute success
probability and finding time* of a CTQW spatial-search algorithm. Combines exactly our
three ingredients (equitable partition + PST + CTQW search) on worked graph families.
**Verdict: PRE-EMPTS (the search-lift use-case), partial.** Does the search-success
computation via the quotient that our "search lift" advertises. It does NOT state a clean
general lifting theorem or any bisimulation/WL equivalence (abstract confirms). So our
*general categorical lift* is still distinguishable, but the headline "you can compute
CTQW search via the equitable quotient" is taken. Cite it as the closest prior art and
position our contribution as the *general verified theorem* behind their special cases.

**Krovi–Brun (2007)** — excluded per instructions (symmetry-subspace = quotient walk; small
quotient necessary for speedup). Still the upstream anchor.

---

## Topic 2 — Equitable partition = bisimulation = coarsest partition (our Tower-8 headline)

**Martens, Groote, van den Haak, Hijma, Wijs — "A linear parallel algorithm to compute
bisimulation and relational coarsest partitions"** (arXiv:2105.11788, 2021; FACS/Springer).
Claim (confirmed): treats "strong bisimilarity = relational coarsest partition" as
**established methodology**, not a result to prove. Paige–Tarjan coarsest stable partition
= bisimulation is folklore in concurrency since the 1980s.
**Verdict: PRE-EMPTS (the bisimulation ↔ coarsest-partition leg of Tower-8).** The
identification "bisimulation = Paige–Tarjan coarsest stable partition" is classical and
universally assumed. We must NOT claim *that leg* as discovery.

**Cançado & Coutinho — "Equitable Partitions and Random Walks"** (CNMAC 2025 proceedings,
SBMAC 5125, 2026; companion arXiv:2411.09157, 2024).
Claim (confirmed): equitable partitions arise in *two* poly-time GI relaxations —
Weisfeiler–Leman and fractional isomorphism — both of which test "shared common equitable
partition." Introduces *pseudo-equitable partitions* for random walks.
**Verdict: CITE / partial PRE-EMPTS.** Coutinho is a Tamon-adjacent senior name in
quantum-walk algebraic graph theory; this explicitly ties equitable partition ↔ WL ↔
fractional isomorphism in the random-walk setting. The "coarsest equitable partition = 1-WL
stable colouring" leg of Tower-8 is *standard* here too. Read the 2411.09157 companion
before claiming any WL-equitable equivalence as novel.

**Rattan & Seppelt — "Weisfeiler–Leman and Graph Spectra"** (arXiv:2103.02972, 2021;
SODA 2023).
Claim (confirmed): cospectrality (adjacency/Laplacian) is *strictly finer* than 2-WL;
individualise-one-vertex + 1-WL subsumes cospectrality w.r.t. all such matrices; builds a
matrix hierarchy where k-WL-after-t-rounds = a spectral condition.
**Verdict: CITE (sharpens our spectral↔WL framing).** Important nuance for credibility:
WL-indistinguishability and cospectrality are NOT the same relation. If our corpus ever
implies "equitable/WL refinement captures the spectrum," this paper is the counter-precision
— color refinement is coarser than the spectrum in general. Cite to show we know the gap.

**Hordan, Dym, Seppelt — "Weisfeiler–Leman Is Incomplete on Simple Spectrum Graphs, so
Canonicalize Them"** (arXiv:2605.23446, May 2026).
Claim (confirmed): for every k there are non-isomorphic simple-spectrum multigraphs that
k-WL cannot distinguish, even though simple-spectrum GI is poly-time via eigenvalues;
proposes PRiSM canonicalization mixing spectral decomposition + refinement.
**Verdict: CITE (very recent, reinforces the WL≠spectrum boundary).** Same caution as above,
sharpened and current. Good to cite so a reviewer sees we track the 2026 frontier.

---

## Topic 3 — Coinductive / coalgebraic certificates of behavioral equivalence

**Pous & Sangiorgi et al. — "Enhancements of the bisimulation proof method" / "Bisimulations
up-to: beyond first-order transition systems"** (Sangiorgi; Madiot–Pous–Sangiorgi, CONCUR 2014;
book *Advanced Topics in Bisimulation and Coinduction*, CUP, ch.6).
Claim: up-to techniques are *the* established way to give small witnesses for bisimilarity —
a relation closed under the functor up-to a sound enhancement is a certificate.
**Verdict: PRE-EMPTS (the "succinct coinductive certificate" idea, in general form).** Our
succinct/coinductive-certificate thread is, in the abstract, *bisimulation up-to* re-skinned.
We must NOT claim "small coinductive certificate of behavioral equivalence" as a new proof
concept. Our possible delta: a *concrete certificate for the equitable-quotient / quantum-walk
equivalence*, mechanized in Lean — not the up-to method itself.

**Chini et al. — "A Lightweight Formalization of the Metatheory of Bisimulation-Up-To"**
(CPP 2015) and **"An abstract account of up-to techniques for inductive behavioural relations"**
(arXiv:2412.07351, 2024).
**Verdict: CITE / MODEL.** Prior *formalizations* of up-to metatheory — directly relevant
template if we mechanize certificates in Lean. Fold in as the formal-methods precedent.

**Ceragioli, Di Lavore, Lomurno, Tedeschi — "A Coalgebraic Model of Quantum Bisimulation"**
(arXiv:2509.20933, Sept 2025; ACT 2024 proceedings version).
Claim (confirmed): coalgebras over effect-algebra-weighted distributions; graded monads
enforcing no-cloning; "kernel bisimilarity" as the right behavioral equivalence for open
quantum systems. **No equitable partitions, quotients, or quantum walks.** Process-calculus /
concurrency setting.
**Verdict: TANGENTIAL (but cite as the quantum-coalgebra state of the art).** Closest thing to
"quantum bisimulation done coalgebraically," but it targets concurrent quantum processes, not
graph CTQW spectra. It does NOT pre-empt our specific equitable-partition-as-bisimulation-of-a-
quantum-walk story — different objects. Cite to show the quantum-coalgebra landscape and to
explicitly distinguish: their bisimulation is on labelled quantum transition systems; ours is
the symmetric quotient of a CTQW Hamiltonian.

---

## Topic 4 — Lumpability, Szegedy/Markov spectral structure (supporting)

**"Average Mixing in Quantum Walks of Reversible Markov Chains"** (arXiv:2211.02037).
Average uniform mixing in CTQW implies it in the Szegedy walk; spectral conditions.
**Verdict: CITE (mixing-lift context).**

**"On aggregation–quantization permutability for discrete-time [quantum walks]"**
(arXiv:2603.14269, 2026). Asks when classical aggregation (lumping) commutes with
Szegedy quantization of a random walk.
**Verdict: MODEL / CITE — flag for follow-up.** This is *precisely* the commuting square our
quotient story lives in (lump-then-quantize vs. quantize-then-lump). Very recent and very
on-topic; fetch the full paper. If it proves a general permutability theorem, parts of our
"quotient commutes with the walk construction" claim may be PRE-EMPTED — treat as the single
highest-priority follow-up read.

**Wikipedia *Lumpability* / Tian–Kemeny lumpability & commutativity** — classical Markov
lumpability (partition with constant cross-block transition rates = our equitable condition
on a stochastic matrix). **Verdict: CITE (names our equitable condition in the classical
Markov literature; do not claim the lumpable↔equitable identity as new).**

---

## Topic 5 — CTQW spatial search (recent, for folding into the corpus)

**Apers, Chakraborty, Novo, Roland — "Optimality of spatial search via continuous-time
quantum walks"** (Phys. Rev. A 102, 032214, 2020) and **Chakraborty et al. — "Multimarked
Spatial Search by CTQW"** (arXiv:2203.14384; ACM TQC 2025, DOI 10.1145/3706064).
**Verdict: MODEL.** Current best general conditions for optimal CTQW search and the multimarked
extension. Fold in as the modern target our quotient-based search lift should reproduce /
specialize to. Lets us frame "our verified lift recovers the [these] optimality criteria on
symmetric instances."

---

## Topic 6 — Quantum model checking / bisimulation acceleration (adjacent verification)

**"Model-checking quantum systems"** (Ying et al., PMC8291611) and **"Quantum Bisimulation-Based
Acceleration Method for Quantum [model checking]"** (Springer 2025, ICFEM-vol).
**Verdict: TANGENTIAL.** Establishes that quantum bisimulation is used to *minimize* quantum
transition systems for verification — same minimization-by-bisimulation idea, different domain.
Cite once to show the bisimulation-minimization paradigm is mature; not a graph-walk pre-emption.

---

## Positioning impact

**What we must NOT claim as novel (mathematics):**
1. **The PST lift.** "PST holds on G iff on the equitable quotient G/π" is Bachman–…–**Tamon**
   2011/2012 (arXiv:1108.0339). The reviewer is an author. Frame our work as the *first
   machine-checked* proof of this iff, never as a new theorem.
2. **bisimulation = Paige–Tarjan coarsest stable partition.** Classical concurrency folklore
   (assumed in arXiv:2105.11788 and everywhere). The Tower-8 *leg* connecting these is not a
   discovery.
3. **coarsest equitable partition = 1-WL stable colouring.** Standard in the WL/GI literature
   (Cançado–Coutinho; Rattan–Seppelt). Tower-8's WL leg is also standard.
4. **Succinct coinductive certificate of behavioral equivalence** = bisimulation *up-to*
   (Sangiorgi/Pous). The proof-method idea is not ours.
5. Be careful: **WL/equitable refinement ≠ spectrum** (Rattan–Seppelt; Hordan–Dym–Seppelt).
   Do not imply equitable partition captures cospectrality — it is strictly coarser.

**The genuinely-open corner that remains ours:**
- **The full Tower-8 *as one mechanized chain* in Lean.** Each leg is classically known, but
  no one has assembled equitable partition ≡ bisimulation ≡ Paige–Tarjan ≡ 1-WL into a single
  axiom-clean formal artifact, *and then* wired it to the CTQW operator-level lifts
  (PST/mixing/search) with the Szegedy-unitarity + Jordan `exp(±i·arccos λ)` spectral machinery.
  The novelty is *unification + mechanization + the quantum-walk bridge*, not any single edge.
- **The verified general lifting theorem** behind Ide–Narimatsu's special-case search
  computations and Bachman–Tamon's PST iff — stated once, for PST + mixing + search uniformly
  via the symmetric quotient, with `#print axioms`-clean status.
- **One sharp risk to retire first:** arXiv:2603.14269 (aggregation–quantization permutability,
  2026) may already prove the lump/quantize commuting square in the Szegedy setting. Read it
  before asserting that our "quotient commutes with walk construction" is new.

**Net:** precision-as-credibility demands we lead with "we *mechanized and unified* a body of
results due to Tamon and others," not "we discovered." The defensible novelty is the verified
unification + the quantum-walk operator bridge + the certificate artifact — not the individual
equivalences, the PST lift, or the up-to proof method.

---

### 2603.14269 pre-emption assessment (2026-06-01)

**Paper.** Adam Doliwa, Artur Siemaszko, Adam Zalewski — *"On aggregation–quantization
permutability problem for discrete-time Markov chains"* (arXiv:2603.14269, submitted 15 Mar 2026).
Read: full PDF text extracted locally (`/tmp/gp_2603.txt`, 2226 lines); abstract + Prop 3.1,
Cor 3.2, intro, conclusions, and bibliography inspected directly.

**Actual main theorem (Proposition 3.1, verbatim sense).** *Given a lumpable Markov chain w.r.t. a
partition Ṽ of its state space V, satisfying (i) the weak-reversibility condition (3.13)
`P_ij > 0 ⇔ P_ji > 0`, and (ii) two nonlinear "consistency" conditions (3.14)–(3.15) on the
transition probabilities, then for the connected graph there exists a **unique** aggregation of
Szegedy's quantization of the original chain (with non-negative "linking coefficients" s_iv) that
is **isomorphic to the Szegedy quantization of the lumped chain.*** I.e. lump-then-quantize =
quantize-then-lump as a commuting square, *conditional* on (3.13)–(3.15). The mechanism: they
build aggregated basis vectors `|u,v⟩ = Σ_{i∈u,j∈v} s_iv √P_ij |i⟩⊗|j⟩` and derive (3.14)–(3.15)
as the self-consistency of a linear system for the s_iv (they liken it to integrable-systems
consistency). **Corollary 3.2:** random walks on graphs with an **equitable partition**
automatically satisfy (3.14) and are lumpable — so the commuting square holds *unconditionally for
the equitable-partition case*. They note distance-regular graphs (sphere partitions) as the
canonical instances and work examples on the five Platonic solids, the N-cube ↔ Ehrenfest urn, and
Cayley graphs of free groups. A parallel thread compares to CMV (Cantero–Moral–Velázquez)
uniformization of the unitary.

- **"Aggregation" =** classical Markov **lumpability / equitable partition** (strong lumpability,
  Kemeny–Snell sense), lifted to the quantum level via linking coefficients. Exactly our
  cell-uniform / equitable-quotient notion.
- **"Quantization" = Szegedy** specifically (coined walks mentioned only as background, not the
  theorem). This is the *same* quantization our `SzegedyWalk_unitary` / `dtqw_equitable_lift` use.
- **Generality:** the *general* theorem is conditional (needs 3.13–3.15, of which 3.13 is exactly a
  reversibility/weak-reversibility hypothesis); the *clean unconditional* statement is for
  equitable partitions / distance-regular graphs (a regularity-restricted class).

**Pre-emption verdict: PRE-EMPTS-PARTIALLY (leaves the LIFTS + the Lean mechanization + the
succinct angle).**

This paper **does prove the DTQW/Szegedy aggregation↔quantization commuting square**, including the
equitable-partition case (Cor 3.2). That is, mathematically, the same square our
`dtqw_equitable_lift` lives in: the Szegedy walk restricted to the aggregated (cell-uniform)
subspace = the Szegedy quantization of the quotient chain. **We must NOT present "the Szegedy walk
commutes with the equitable quotient" as new mathematics.** It is now in the literature, by name,
as of March 2026 (and the unconditional equitable-partition corollary is theirs).

What genuinely **stays graphplay's**:
1. **The Lean mechanization / axiom-clean formal artifact.** They give a pen-and-paper Prop 3.1
   with a construction-style proof. No formalization. Our `SzegedyWalk_unitary` proof, the Jordan
   `exp(±i·arccos λ)` spectral correspondence, and the verified `dtqw_equitable_lift` are the
   machine-checked version — a real, defensible delta (same status as our CTQW story vs Bachman–Tamon).
2. **The operator-level LIFTS (PST / mixing / search).** Doliwa et al. prove **only the commuting
   square** — they explicitly say PST "deserves deeper studies" and cite the PST-on-quotient
   literature ([4] Bachman–Tamon, [30] Ge–…–Tamon, [57] Salimi, [41]) only in a *remark*, in the
   CTQW setting, **not** for their DTQW square. There is **no** discrete-time PST-lift theorem, no
   mixing-lift, no search-lift in this paper. Our `cellUniformPST_iff_quotientPST` and the
   uniform-lift framing (PST + mixing + search via the symmetric quotient) is not pre-empted on the
   *discrete-time* side — they built the square but did not run any property through it.
3. **The CTQW square + the unified CTQW/DTQW treatment.** Their paper is DTQW-only (the CTQW
   quotient is referenced as Salimi/CTQW prior art, not re-proven). Our `restrict_eq_symmQuotient`
   / `cellUniformPST_iff_quotientPST` CTQW layer and the *unification* of CTQW and DTQW under one
   equitable-quotient mechanism remains ours.
4. **The Tower-8 equivalence chain** (equitable ≡ bisimulation ≡ Paige–Tarjan ≡ 1-WL) — entirely
   untouched here.

What is now **clearly NOT ours** (retire these as novelty claims):
- "Lump-then-quantize = quantize-then-lump for Szegedy walks" — **theirs** (Prop 3.1).
- "Equitable partition makes the Szegedy quantization commute with aggregation" — **theirs** (Cor 3.2).
- The N-cube ↔ Ehrenfest / Platonic-solid worked reductions — **theirs**.

**Krovi–Brun / Bachman–Tamon citation status.** Yes to both, which tightens the squeeze:
- **[46] Krovi–Brun 2007** ("Quantum walks on quotient graphs") **is cited** — in the intro
  (line 66) as the closest prior work on DTQW on quotient graphs from symmetric graphs with chosen
  initial state. They claim *novelty over Krovi–Brun* by being the first to *formulate and
  systematically study the aggregation–quantization permutability problem* per se ("We do not know
  any previous work where the aggregation–quantization problem … was formulated and systematically
  investigated"). So they self-position as the canonical reference for exactly our square.
- **[4] Bachman–Fredette–…–Tamon (PST on quotient graphs, 2012)** and **[30] Ge–Greenberg–Perez–
  Tamon (PST, graph products and equitable partitions, 2011)** **are cited** — but only in the PST
  remark after Cor 3.2, attached to the *continuous-time* quotient-PST literature. They do **not**
  prove or claim a discrete-time PST lift.

**Succinct / symbolic-input / certificate angle (relevance to our (A′) frontier).** **No
mention.** Zero treatment of succinct/symbolic graph representations, implicit/exponential-state
chains, descriptive complexity, or any certificate framing. Their examples are explicit small
graphs (Platonic solids) or structured families (hypercube, free-group Cayley graphs) handled by
hand. **This does not open or close the (A′) door — it leaves it wide open.** If anything it
*strengthens* the (A′) wedge: they have now established the DTQW commuting square as a named,
citable object, so a succinct-input / certificate-complexity treatment of *when the aggregated
description is exponentially smaller and verifiable* is a clean, unclaimed follow-on that
explicitly builds on (rather than races) 2603.14269.

**Positioning impact.**
- Reposition the DTQW layer: cite 2603.14269 as the prior-art **theorem** for the Szegedy
  aggregation–quantization square (alongside Krovi–Brun for the quotient-walk idea). Our DTQW
  contribution is now explicitly **"the first machine-checked proof of the Szegedy
  aggregation–quantization permutability (Doliwa–Siemaszko–Zalewski 2026 / equitable case), plus
  the operator-level PST/mixing/search lifts they leave open, unified with the CTQW quotient."**
  Do NOT claim the square itself.
- This mirrors the Bachman–Tamon situation on the CTQW/PST side: the *theorem* is in the
  literature; our delta is mechanization + unification + the lifts.
- It tightens but does not close the corner. Net frontier that stays ours after this read: the
  unified CTQW+DTQW Lean artifact, the verified PST/mixing/search lifts (uniform, axiom-clean), the
  Tower-8 chain, and — untouched and arguably *enabled* — the (A′) succinct-systems / certificate
  frontier.
