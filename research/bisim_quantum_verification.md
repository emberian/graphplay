# Quantum speedups for verification/reachability on bisimulation-reduced transition systems

**Status: research scoping memo (adversarial). Default posture: skeptical.**
**Audience: Ember + Tino Tamon. Precision over enthusiasm.**
Date: 2026-06-01

---

## 0. TL;DR verdict (read this first)

For the conjecture *"there are quantum speedups for verification/reachability tasks on
bisimulation-reduced transition systems"*:

- **(A) Quantum walk on a bisimulation quotient for a reachability/hitting/detection task —
  NOT NOVEL in the generic explicitly-given-graph regime.** This is exactly the
  Szegedy/MNRS hitting-time speedup applied to a quotient. The quotient is classical
  preprocessing; for an explicitly given transition system, Paige–Tarjan partition refinement
  costs `O(m log n)`, which dominates or matches any `√` win on the (smaller) quotient walk.
  Worse: **Krovi–Brun (2007) already proved the quotient/quantum-walk correspondence** and
  **conjectured that a small quotient is *necessary* for quantum speedup** — i.e. the quotient
  is not a *source* of new speedup, it is the *structural explanation* of speedups that already
  exist. So in the generic regime the conjecture is not just unoriginal, it is arguably
  *backwards*.

- **(A′) Novel ONLY in regime X = succinct / symbolic transition systems.** If the system is
  given *succinctly* (a circuit / symbolic encoding with `N = 2^n` states) and the *quotient is
  exponentially smaller* (`r = poly(n)` cells) but **bisimulation is hard to materialize
  classically** (PSPACE-complete to decide on succinct systems), then a quantum walk that
  addresses the quotient *as an oracle it never materializes* could beat any classical method
  that must build the partition. This is the only regime where there is room for a genuine,
  non-trivial claim — and it is **unclaimed in the literature as far as this survey found**.
  But it is fragile: you must exhibit a task where the quotient oracle is *quantum-accessible
  without* solving the (hard) bisimulation, which is the entire difficulty.

- **(B) Quantum speedup for COMPUTING the coarsest bisimulation — likely a modest `√`-type
  Grover win at best, no asymptotic breakthrough, and no formalized asset supports it.** Classical
  Paige–Tarjan is `O(m log n)`; the matching lower bound `Ω((m+n) log n)` (Groote et al. 2021)
  is for the *partition-refinement paradigm*. Grover could shave inner-loop search factors but
  the dependency-chain structure of refinement resists quadratic speedup. Not where the
  formalized corpus has leverage.

**Single sharpest falsifiable next step (see §5):** pick a *named succinct graph family* whose
bisimulation/equitable quotient is `poly(n)` while the graph is `2^n`, where the quotient walk's
Szegedy spectrum is computable and the classical reachability task is `Ω(2^n)` even given the
symbolic encoding — and check whether the quotient is quantum-oracle-addressable *without*
first computing the partition. The hypercube-fold and `K_n`-fold already in the corpus are the
two cleanest test fixtures: predict whether the speedup survives when you are *forbidden* to
precompute the partition. If it does not survive on those, the succinct regime is also dead.

---

## 1. Grounding: what graphplay actually proved (not on faith)

Read the assets. The load-bearing, axiom-clean pieces are:

**Bisimulation ≡ equitable partition (Tower 8).**
`Graphplay/Tower8.lean` + `Graphplay/Tower8/DistributedQuotient.lean`:
- Cell-equality `cells x = cells y` is a *genuine* bisimulation of the walk coalgebra
  (`dist_equitable_isBisim`), proven as the kernel of the coalgebra morphism `cells`
  (`dist_cells_isCoalgMorphism`) — and the successor is now non-trivial
  (`distVertexCoalg_next`, the "take turn `j`, land in cell `j`" Moore machine).
- The coarsest equitable partition = coarsest bisimulation = Paige–Tarjan = 1-WL color
  refinement; `dist_bisim_refines_wlStable` places the genuine-dynamics bisimulation inside the
  Paige–Tarjan = 1-WL picture.
- **Honest caveat carried in-file:** the deep Paige–Tarjan *converse*
  (`coarsest_equitable_isCoarsest_bisim`) is the single remaining `sorry` in `Tower8.lean`.
  This matters for (B): we do **not** have a fully formalized coarsest-bisimulation = PT step.

**Szegedy quantum walk (DiscreteTime + JordanLemma).**
`Graphplay/DiscreteTime.lean`:
- `SzegedyWalk_unitary` — PROVEN (`U Uᴴ = 1`).
- `szDiscriminant_spec` — PROVEN, **sorry-free**, but it is the *corrected* (surjective-half)
  direction: `spectrum randomWalkOp ⊆ spectrum D₀` where `D₀ = reflStepDiscriminant R S`. The
  previously-claimed reverse inclusion was dropped as not generally true. The eigenvalue
  correspondence is `exp(±i·arccos λ)` via Jordan's lemma (`Graphplay/ForMathlib/JordanLemma.lean`,
  `U = SR` two-reflection product). **This is the spectral engine of the `√`-speedup**: the
  eigenphase gap is `arccos`-folded, hence quadratically larger than the classical spectral gap.

**The equitable quotient lift (PST / quotient walk).**
- `restrict_eq_symmQuotient`, `cellUniformPST_iff_quotientPST`: CTQW restricted to the
  cell-uniform subspace = walk on the `r×r` symmetric quotient `Q̃`, spectrum-preserving
  (`spec Q̃ ⊆ spec A`). Cell-uniform PST on the host ⟺ PST on the quotient.
- `dist_quotientPST_bridge` reuses this verbatim; `dist_next_eq_pst_target` ties the discrete
  Moore successor to the PST endpoint.

**Spatial search (Childs–Goldstone), the existing "speedups."**
- On *specific* graphs: `K_n` at `O(√n)`, hypercube. **The `√` win is from amplitude
  amplification / a spectral gap, NOT from the partition.** The equitable partition is what lets
  you *reduce the analysis to a small quotient*; it is not the *origin* of the advantage.

**So the conjecture, stated honestly in our terms:** "Does running the Szegedy/CTQW walk on the
`r×r` quotient `Q̃` (which we proved is spectrum-preserving and PST-equivalent) give a quantum
*algorithmic* advantage for a reachability/verification task, beyond what Szegedy already gives,
attributable to the *bisimulation reduction itself*?"

---

## 2. Prior-art map (citations + links)

### 2.1 Szegedy / MNRS quantum-walk speedup (the baseline the claim must beat)
- **Szegedy 2004**, "Quantum Speed-up of Markov Chain Based Algorithms" (FOCS 2004).
  For any reversible Markov chain `P`, builds a quantum walk `W(P)` whose eigenphase gap is
  **quadratically larger** than the spectral gap of `P` ⇒ quadratic speedup in **detection** /
  hitting time `O(√HT)`. Crucial caveat baked in since 2004: this **detects** a marked element
  (deviation from start), it does not **find** one. https://www.researchgate.net/publication/4109377_Quantum_speed-up_of_Markov_Chain_based_algorithms
- **Magniez–Nayak–Roland–Santha (MNRS)**, "Search via Quantum Walk." The standard
  setup/update/check framework giving `√`-type speedups for search; the framework our quotient
  walk would have to plug into. https://www.math.uwaterloo.ca/~anayak/papers/NRS.pdf
- **Magniez–Nayak–Roland–Santha 2009**, "On the hitting times of quantum versus random walks."
  https://www.math.uwaterloo.ca/~anayak/papers/MagniezNRS09.pdf
- **Apers–Gilyén–Jeffery(–Kokainis) 2019/STOC 2020**, "Quadratic speedup for finding marked
  vertices by quantum walks" (arXiv:1903.07493). **Closes the 15-year detection-vs-finding gap**:
  `O(√HT)` to actually *find* a marked vertex for *any* graph and *any* marked set. This is the
  current best generic quantum-walk-search baseline; any quotient-based claim competes against
  this. https://arxiv.org/abs/1903.07493

### 2.2 Quantum walks on quotient graphs / equitable partitions (THE closest prior art)
- **Krovi–Brun 2007**, "Quantum walks on quotient graphs" (arXiv:quant-ph/0701173, Phys. Rev. A
  75, 062332). A quantum walk confined to the automorphism-symmetry subspace **is** a quantum
  walk on a smaller quotient graph; they analyze how hitting times descend to the quotient.
  **The killer line:** *"All known examples of quantum walks with fast hitting times correspond
  to systems with quotient graphs much smaller than the original graph; we conjecture that the
  existence of a small quotient graph with finite hitting times is necessary for a walk to
  exhibit a quantum speed-up."* This is the *exact* structure of the conjecture under review —
  and Krovi–Brun frame the small quotient as a *necessary condition / structural explanation* of
  speedup, not as a new source of it. https://arxiv.org/abs/quant-ph/0701173
- **Ide 2018**, "Partition of graphs and quantum walk based search algorithms"
  (arXiv:1812.06376). Uses equitable partition to find the "effective subspace" and reduced
  operator for QW search — explicitly a **problem-reduction/analysis** method, **no asymptotic
  speedup claim**. https://arxiv.org/abs/1812.06376
- **Bachman–Tamon et al. 2011**, "Perfect state transfer on quotient graphs"
  (arXiv:1108.0339) — *already cited in `DistributedQuotient.lean`*. PST descends through
  equitable-partition quotients (a graph has PST iff its quotient does). This is the PST analogue
  of exactly what `cellUniformPST_iff_quotientPST` formalizes. The quotient is a *spectral
  bookkeeping* device, not an algorithmic speedup. https://arxiv.org/abs/1108.0339
- **"Perfect state transfer, equitable partition and CTQW based search" (Quantum Stud. 2024)** —
  same toolkit; equitable partitioning reduces the search-operator size.
  https://link.springer.com/article/10.1007/s40509-024-00321-y

### 2.3 Quantum algorithms for reachability / s-t connectivity (the "verification" side)
- **Belovs–Reichardt 2012**, "Span programs and quantum algorithms for st-connectivity and claw
  detection" (arXiv:1203.2603). `O(n·d^{1/2})` queries to the adjacency matrix to decide s-t
  connectivity under a path-length-`d` promise; witness size = effective resistance (positive) /
  capacitance (negative). This is the principled quantum reachability primitive — **and it is
  defined on the raw graph via an adjacency oracle, with no bisimulation step.**
  https://arxiv.org/abs/1203.2603
- **Jarret–Jeffery–Kimmel–Piedrafita 2018**, "Quantum Algorithms for Connectivity and Related
  Problems" (arXiv:1804.10591). Extends to connectivity, forest/bipartiteness, sharper
  resistance/capacitance characterizations. https://arxiv.org/abs/1804.10591
- These set the bar: the quantum reachability literature operates on the **explicit graph via an
  oracle**; nobody in it inserts a bisimulation quotient.

### 2.4 Complexity of bisimulation / partition refinement (the classical cost that can kill the win)
- **Paige–Tarjan 1987**, SIAM J. Comput. 16(6): coarsest partition / relational coarsest
  partition in `O(m log n)`. (Cited in-corpus.)
- **Groote et al., CONCUR 2021 / LMCS 2022**, "Lowerbounds for Bisimulation by Partition
  Refinement": `Ω((m+n) log n)` sequential lower bound *for partition-refinement algorithms*,
  `Ω(n)` parallel. So classical PT is essentially optimal within its paradigm.
  https://arxiv.org/abs/2203.07158
- **No quantum algorithm for computing bisimulation / partition refinement was found** in this
  survey — the intersection (Grover/quantum-walk × bisimulation computation) appears genuinely
  unexplored. (Searches returned only classical PT-family results.)

### 2.5 "Quantum model checking" — a NAMING TRAP, not prior art for our claim
- The entire "quantum model checking" literature (Ying et al.; QCTL/QLTL; super-operator-valued
  Markov chains; QMC tool; QReach CAV 2023 arXiv:2512.04497; quantum CTMC reachability
  arXiv:2310.11882) is about **model-checking quantum *systems*** (verifying quantum programs /
  quantum Markov chains), **NOT** about quantum *speedups for classical* model checking.
  - https://www.mdpi.com/2076-3417/12/4/2016 (intro to quantum model checking)
  - https://academic.oup.com/nsr/article/6/1/28/5128515 (Ying, model-checking quantum systems)
  - https://arxiv.org/pdf/2512.04497 (QReach)
  **Do not cite these as support for the conjecture.** They are orthogonal. This is the single
  most likely place to accidentally overclaim novelty; flagged explicitly for Tino.

### 2.6 The "oracle source code" deflation (sharpens regime X)
- **"Opening the Black Box Inside Grover's Algorithm" (Phys. Rev. X 2024, arXiv:2303.11317):**
  once you are given the *structure/source* of the oracle, the a-priori quantum speedup can
  evaporate. https://arxiv.org/abs/2303.11317 . Directly relevant: if the quotient is given
  *explicitly* (you computed the partition), the quotient walk is a small explicit graph and
  there is no oracular advantage hiding in it. The advantage can only live where the quotient is
  accessed as a genuine oracle you *cannot* cheaply materialize — i.e. regime X.

---

## 3. Two sharpened, falsifiable conjectures

### Conjecture (A): Quantum speedup for a verification/reachability/hitting task ON the bisimulation-reduced system

- **Task:** Given a transition system `T` with `N` states and coarsest bisimulation quotient
  `T/∼` with `r ≪ N` cells, and a target predicate `φ` definable on cells, decide
  reachability / detect a marked cell / estimate hitting time to a marked cell.
- **Classical baseline:** build the quotient (Paige–Tarjan `O(m log n)`, `m,n` in terms of `N`),
  then classical random walk / BFS on `T/∼`: `O(HT(T/∼))` or `O(r + #edges)`.
- **Claimed quantum cost:** Szegedy/MNRS/AGJ walk on `T/∼`: `O(√HT(T/∼))` (+ `O(m log n)`
  classical preprocessing to get the quotient).
- **Input model:** **explicit** transition system (adjacency/edge oracle on `N` states).
- **Falsifier:** the `O(m log n)` preprocessing is `≥` the quotient-walk cost whenever
  `√HT(T/∼) ≤ m log n`, which is essentially always for `r ≪ N` (the quotient is tiny, its walk
  is cheap, the reduction dominates). ⇒ **no asymptotic win in this model.**

### Conjecture (A′): same task, SUCCINCT/SYMBOLIC input (the only live version)

- **Task:** same, but `T` is given **succinctly** — a Boolean circuit / symbolic encoding of the
  transition relation over `n` bits, `N = 2^n` states — and the quotient has `r = poly(n)` cells.
- **Classical baseline:** deciding/bisimulation-minimizing a succinctly-given system is
  **PSPACE-complete** in general; even the best symbolic PT can blow up to `2^n`. So classical
  cost is `2^{Ω(n)}` (or PSPACE) to materialize the quotient.
- **Claimed quantum cost:** if the quotient walk `Q̃` (size `poly(n)`) is **quantum-oracle-
  addressable directly from the symbolic encoding without first computing the partition**, run
  Szegedy on `Q̃`: `poly(n)·O(√HT(Q̃))`.
- **Input model:** **succinct/symbolic**, with the crucial extra assumption that the quotient is
  oracle-addressable without partition refinement.
- **Falsifier (the crux of whether this is real):** does addressing `Q̃` as an oracle *require*
  solving the (PSPACE-hard) bisimulation? If yes — if you cannot produce the cell of a state, or
  the cell-to-cell transition amplitudes, without effectively running partition refinement — the
  oracle is *not* cheaply implementable and the win is illusory. **This is exactly the open
  question.** A positive answer needs a *specific symbolic family* where cell membership is
  computable in `poly(n)` (e.g. cells = a known invariant: Hamming weight, an orbit under a
  succinctly-described symmetry, a syntactic congruence class) even though *coarsest* bisimulation
  is hard.

### Conjecture (B): Quantum speedup for COMPUTING the coarsest bisimulation

- **Task:** given `T` (explicit, `N` states, `M` edges), output the coarsest bisimulation
  partition.
- **Classical baseline:** Paige–Tarjan `O(M log N)`; lower bound `Ω((M+N) log N)` for the
  refinement paradigm (Groote et al.).
- **Claimed quantum cost:** Grover-amplified refinement: shave the inner splitter-search /
  predecessor-scan by `√`, but the **sequential refinement dependency chain** (each split depends
  on the previous partition) blocks a global quadratic speedup. Best plausible: constant-factor
  or low-order-term improvement, or a `√`-in-some-subroutine claim.
- **Input model:** explicit.
- **Falsifier:** the `Ω((M+N) log N)` paradigm bound + the inherent sequentiality. No known
  quantum primitive parallelizes refinement's dependency chain. ⇒ **no asymptotic breakthrough
  expected; not where the formalized corpus helps.**

---

## 4. Adversarial novelty verdict

**Conjecture (A): NOT NOVEL (and arguably backwards).**
A quantum walk on a bisimulation quotient for a reachability/hitting/detection task is the
Szegedy speedup with a classical preprocessing step. Three independent reasons it does not yield
a new advantage in the explicit-input regime:
1. **The quotient is classical preprocessing.** Paige–Tarjan `O(m log n)` dominates the cost of
   walking the tiny quotient; the `√` win lives entirely in the Szegedy/AGJ walk, which is *not
   ours and not new*.
2. **Krovi–Brun (2007) already established the correspondence** (confined symmetry-subspace walk
   = walk on the quotient) and **conjectured the small quotient is *necessary*, not sufficient,
   for speedup.** Our formalized `restrict_eq_symmQuotient` / `cellUniformPST_iff_quotientPST` is a
   rigorous, axiom-clean *instance* of the Krovi–Brun picture (and the PST half is literally
   Bachman–Tamon 2011, already cited in-file). Restating it as "the quotient *gives* a speedup"
   inverts the established direction.
3. **The spatial-search wins we have (`K_n`, hypercube) come from amplitude amplification /
   spectral gap, not from the partition** — the corpus itself is careful about this, and so must
   the claim be.

**Conjecture (A′): NOVEL ONLY IN REGIME X = succinct/symbolic input where bisimulation is
classically intractable but the quotient is quantum-oracle-addressable.**
This is the one defensible frontier and it appears unclaimed. But it is conditional on a hard
sub-question (the (A′) falsifier): you must exhibit a succinct family where the *coarsest*
quotient is `poly(n)`-addressable as an oracle **without** solving the hard partition problem.
If cell membership is itself bisimulation-hard, the oracle is not implementable and the regime
collapses. The honest statement: *novel-only-in-regime-X, and even there contingent on an
unresolved oracle-implementability question.* This is precisely the kind of claim that must be
stated with the precondition attached (per the "precision as credibility" rule) — never as a
bare "quantum speedup for bisimulation-reduced verification."

**Conjecture (B): NOT NOVEL / not promising.**
No asymptotic quantum breakthrough is expected against the `Ω((M+N) log N)` refinement bound
plus sequential dependency; and the corpus has *no* asset here (the PT converse is the open
`sorry`). Deprioritize.

**One-line verdict:** *There is no generic, novel quantum speedup from bisimulation reduction
itself; the only live novelty is in the succinct/symbolic regime, and it is contingent on the
quotient being quantum-oracle-addressable without solving the (intractable) bisimulation —
an open and possibly false assumption.*

---

## 5. Connection to formalized assets + the smallest decisive next step

**Which proven pieces are the building blocks (for A′, the only live conjecture):**
- `SzegedyWalk_unitary` + `szDiscriminant_spec` + the `exp(±i·arccos λ)` Jordan correspondence
  (`Graphplay/ForMathlib/JordanLemma.lean`) — the spectral engine giving the eigenphase
  quadratic fold. **This is the `√` and it is genuinely ours and axiom-clean.**
- `restrict_eq_symmQuotient` + `cellUniformPST_iff_quotientPST` + `spec Q̃ ⊆ spec A` — the
  spectrum-preserving quotient lift: the rigorous statement that *the walk on the quotient is the
  walk restricted to the cell-uniform subspace.* This is the formal license to run the Szegedy
  analysis on `Q̃` instead of `A`.
- `dist_*` coalgebra layer (`DistributedQuotient.lean`) — the genuine Moore/DFA realization;
  `dist_cell_confinement` is the closest thing we have to a *reachability/safety* statement on
  the quotient dynamics. This is where a verification task would attach.

**The smallest new theorem that would settle the sharpest surviving conjecture (A′):**

> **Theorem (target).** For the symbolic graph family `F_n` [hypercube-fold / `K_n`-fold, the
> two fixtures already in the corpus], let `Q̃_n` be its equitable quotient (`r = poly(n)`,
> proven spectrum-preserving via `cellUniformPST_iff_quotientPST`). Then the cell-membership map
> `cells : {0,1}^n → [r]` and the quotient transition amplitudes are computable in `poly(n)`
> **directly from the symbolic encoding**, i.e. *without* partition refinement — exhibiting an
> explicit quantum-oracle implementation of the Szegedy walk on `Q̃_n`, whose eigenphase gap
> (`arccos`-folded, by the proven Jordan correspondence) yields `O(√HT(Q̃_n))` detection of a
> marked cell while any classical method on the succinct `2^n`-state encoding costs `2^{Ω(n)}`.

If `cells` is computable in `poly(n)` for these fixtures (for the hypercube it *is* — the cell is
the Hamming weight, a one-line symbolic function), this theorem is provable and the speedup is
**real in regime X**. If `cells` for the *coarsest* quotient of an interesting verification
family is itself bisimulation-hard, the theorem fails and (A′) is dead.

**The single sharpest falsifiable experiment (do this first, before any Lean):**
Take the **hypercube-fold** (cells = Hamming weight, manifestly `poly(n)`-computable) and the
**`K_n`-fold** already in the corpus. For each, answer concretely, with an a-priori prediction:

1. Is `cells(x)` computable in `poly(n)` from the symbolic encoding *without* materializing the
   partition? (Hypercube: **yes**, Hamming weight. `K_n`: trivially yes.)
2. Is the marked-cell **detection/reachability** task on the `2^n`-state symbolic system
   classically `2^{Ω(n)}`, or does the same symbolic structure that makes `cells` cheap *also*
   give a classical `poly(n)` shortcut (collapsing the claimed quantum win)?

**Prediction (the deflating one to test):** for the hypercube the symbolic structure that makes
`cells = HammingWeight` cheap *also* makes the classical reachability/hitting task `poly(n)`
classically (you reason on the weight directly) — so the quantum win **does not survive** even in
the succinct regime for the "easy" fixtures. The conjecture (A′) is real **only** if there exists
a family where `cells` is cheap **but** the classical cell-level reachability is still hard —
a genuine separation between *"can name the cell"* and *"can reason about reachability among
cells classically."* Finding (or ruling out) one such family is the whole ballgame, and it is a
pencil-and-paper / small-simulation question answerable *before* committing any formalization
effort.

---

## 6. Bottom line for Tino

- The bisimulation ≡ equitable-partition bridge and the spectrum-preserving quotient lift are
  rigorous and axiom-clean, and they are a *correct, formalized instance of the Krovi–Brun (2007)
  / Bachman–Tamon (2011) quotient-walk picture* — that is their honest standing: precise
  formalization of known structure, not a new speedup.
- The quantum *advantage* is Szegedy's (eigenphase `arccos`-fold, which we *do* have formalized
  via the Jordan lemma); the bisimulation quotient is the structural *explanation* of when such
  advantages exist, per Krovi–Brun's necessity conjecture — **not a new source** of advantage.
- The only place a *novel* claim can live is succinct/symbolic systems where bisimulation is
  classically intractable yet the quotient is quantum-oracle-addressable — and that hinges on an
  unresolved separation between cheap cell-naming and hard cell-reachability. State it only with
  that precondition attached.

---

### Sources
- Szegedy, Quantum Speed-up of Markov Chain Based Algorithms (FOCS 2004): https://www.researchgate.net/publication/4109377_Quantum_speed-up_of_Markov_Chain_based_algorithms
- Magniez–Nayak–Roland–Santha, Search via Quantum Walk: https://www.math.uwaterloo.ca/~anayak/papers/NRS.pdf
- Magniez–Nayak–Roland–Santha 2009, Hitting times quantum vs random walks: https://www.math.uwaterloo.ca/~anayak/papers/MagniezNRS09.pdf
- Apers–Gilyén–Jeffery, Quadratic speedup for finding marked vertices (arXiv:1903.07493): https://arxiv.org/abs/1903.07493
- Krovi–Brun, Quantum walks on quotient graphs (arXiv:quant-ph/0701173): https://arxiv.org/abs/quant-ph/0701173
- Ide, Partition of graphs and quantum walk based search (arXiv:1812.06376): https://arxiv.org/abs/1812.06376
- Bachman–Tamon et al., Perfect state transfer on quotient graphs (arXiv:1108.0339): https://arxiv.org/abs/1108.0339
- Perfect state transfer, equitable partition and CTQW search (Quantum Stud. 2024): https://link.springer.com/article/10.1007/s40509-024-00321-y
- Belovs–Reichardt, Span programs / st-connectivity (arXiv:1203.2603): https://arxiv.org/abs/1203.2603
- Jarret–Jeffery–Kimmel–Piedrafita, Connectivity and Related Problems (arXiv:1804.10591): https://arxiv.org/abs/1804.10591
- Paige–Tarjan, SIAM J. Comput. 16 (1987) (three partitions refinement).
- Groote et al., Lowerbounds for Bisimulation by Partition Refinement (arXiv:2203.07158): https://arxiv.org/abs/2203.07158
- Ying, Model-checking quantum systems (Natl. Sci. Rev. 2019): https://academic.oup.com/nsr/article/6/1/28/5128515
- An Introduction to Quantum Model Checking (Appl. Sci. 2022): https://www.mdpi.com/2076-3417/12/4/2016
- QReach (arXiv:2512.04497): https://arxiv.org/pdf/2512.04497
- Opening the Black Box Inside Grover's Algorithm (PRX 2024, arXiv:2303.11317): https://arxiv.org/abs/2303.11317
