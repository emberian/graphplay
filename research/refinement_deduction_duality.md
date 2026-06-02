# Refinement ⊣ Deduction: the abstract-interpretation duality between graphplay's partition refinement and the Lattice Deduction Transformer

**Status: research elaboration (adversarially honest, literature-grounded). Default posture: skeptical. Consolidate-and-expand-verifiably, NOT novelty-chasing.**
**Audience: Ember (+ possibly Tino Tamon / the Axiom/Haller PL∩SAT scene). Precision over enthusiasm.**
**Companion to:** `research/ldt_assessment.md` (the per-bridge LDT verdict) and `research/bisim_quantum_verification.md` (the quantum-side adversarial map). This doc does **not** repeat those; it pins the *order-theoretic duality* precisely, grades the *expansion directions*, and sketches the *Tower-9 Lean build*.
**Date:** 2026-06-01.

---

## 0. TL;DR (read this first)

graphplay's WL/colour-refinement (= coarsest equitable partition = coarsest bisimulation, Tower-8) and the Lattice Deduction Transformer's lattice deduction (LDT, arXiv:2605.08605) are **the two order-dual halves of one Knaster–Tarski fixpoint story, and abstract interpretation (Cousot–Cousot 1977) is the single framework that contains both**:

| | **graphplay: refinement** | **LDT: deduction** |
|---|---|---|
| Lattice | partition lattice `Part(V)` (refinement order) | grid powerset `A = pos → ℘(V)` (pointwise ⊆) |
| Operator | `wlStep` — monotone, **extensive/refining** (splits cells) | `dedₚ = α∘(·∩‖p‖)∘γ` — monotone, **reductive** (removes candidates) |
| Fixpoint | **lfp** from the trivial (1-block) partition, ascending the refinement order | **gfp** from ⊤, descending the precision order |
| Builds | the **coarsest sound abstraction** (the quotient automaton) | a value **within** a fixed abstraction (the solution set) |
| Distinguishes / eliminates | *distinguishes states* | *eliminates values* |
| Termination | `wlRefine_stable`: ≤ |V| rounds (lattice height) | well-foundedness: strict alive-count descent (lattice height) |

The duality is **classical and real** (Knaster–Tarski lfp ⟂ gfp; the Cousot Galois frame; the Paige–Tarjan-as-abstract-interpretation literature). **The quantum content lives only on the refinement leg** — there is no honest deduction-dual on quantum amplitudes (§3.3). The **single most valuable near-term Lean build** is the already-identified first brick, sharpened: `Graphplay/Integrations/LatticeDeduction.lean`, a machine-checked **run-soundness** theorem for learned lattice-deduction, reusing Tower-8's `stepInv_preserved`. **Tower-9** (a genuine `GaloisConnection`-based abstraction layer) is **PLAUSIBLE and worth one focused module** but should be scoped to *the partition↔abstract-domain Galois insertion that the literature already validates* (Ranzato–Tapparo), not to an invented `cellInflate ⊣ cells` adjunction (which is **not** a Galois connection — §2.1).

Sharpest 2–3 REAL directions, what stays SPECULATIVE, and the one build: see §5.

---

## 1. The duality, pinned precisely (with citations)

### 1.1 Knaster–Tarski: lfp and gfp are order-dual

For a complete lattice `(L, ⊑)` and a monotone `f : L → L`, the fixpoints form a complete lattice; the **least fixpoint** `lfp f = ⊓{x | f(x) ⊑ x}` (least *pre*-fixpoint) and the **greatest fixpoint** `gfp f = ⊔{x | x ⊑ f(x)}` (greatest *post*-fixpoint) [Tarski 1955]. The two are exchanged by passing to the **order-dual lattice** `L^op`: `lfp_L f = gfp_{L^op} f`. The proof principles are dual: **gfp ↦ coinduction** ("to show `x ⊑ gfp f`, exhibit `x` as a post-fixpoint `x ⊑ f(x)`"); **lfp ↦ induction / inductive invariant** ("to show `lfp f ⊑ x`, exhibit `x` as a pre-fixpoint `f(x) ⊑ x`"). Baldan–Eggert–König–Padoan, *Fixpoint Theory – Upside Down* (FOSSACS '21 / LMCS 2023, arXiv:2101.08184) is the clean modern reference that **bisimilarity is a gfp** and develops the dual (below-lfp / above-gfp) rules; it lists *bisimilarity and behavioural distances* as its motivating gfp examples.

> **The duality in one line.** WL/bisimulation-minimization computes a **gfp** *of a refinement operator on `Part(V)`* — but read as the *coarsest* bisimulation it is the **largest** partition that is stable, i.e. the gfp of "split where a cell is not equitable" — equivalently the **lfp of the colour-refinement map in the finer-than order** (each round can only refine). LDT computes a **gfp** *of a reductive deduction operator on the grid powerset*. Both are Knaster–Tarski fixpoints; they sit on **different lattices** and the operators move in **opposite directions** (refining/splitting vs reducing/eliminating). This is why "refine partition" and "propagate constraints" are *dual instances of the same theorem*, not the same computation.

A precision note that matters for honesty (and that Tower-8 already records in-file): "coarsest bisimulation = gfp" and "colour refinement = lfp-of-the-refining-map" are **two views of the same object** — the refinement chain *ascends* the finer-than order to its limit, which *is* the *coarsest* stable (= largest gfp-in-the-coarser-than order) partition. graphplay proves the *operational* (Kleene-iterate-to-stabilization) version: `wlStep_isRefinement` (monotone/extensive in the refinement order), `wlColorCount_mono` (height strictly increases until fixed), `wlRefine_stable` (stabilizes ≤ |V| rounds), `wlRefine_coarsestEquitable` (the fixpoint is the coarsest equitable partition). It does **not** currently package this as a Mathlib `OrderHom.lfp`/`gfp` on a `CompleteLattice (Part V)` instance — see §4 for whether that is worth adding.

### 1.2 Cousot–Cousot: abstract interpretation is the frame that contains both

Cousot–Cousot, *Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints* (POPL '77) and *Systematic design of program analysis frameworks* (POPL '79): a **Galois connection** `α ⊣ γ` between a concrete complete lattice `C` and an abstract one `A` (`α(c) ⊑ a ⟺ c ⊑ γ(a)`), with a **sound abstract transformer** `f^♯ ⊒ α∘f∘γ`, and the **fixpoint transfer** `α(lfp f) ⊑ lfp f^♯` (dually for gfp). Soundness = the abstract fixpoint over-approximates the concrete one.

- **LDT is a textbook instance** (its App. A states `α(S')(i) = {s(i):s∈S'}`, `γ(a) = {s : ∀i. s(i)∈a(i)}`, best transformer `dedₚ = α∘(·∩‖p‖)∘γ`, gfp-Kleene descent from ⊤, and invokes Cousot fixpoint-transfer `α(gfp f) ⊑ gfp f^♯`). The over-approximation is **lossy by design** (`α∘γ ≠ id`; their Fig. 5 — it forgets inter-cell correlations). Verified per `ldt_assessment.md §1`.
- **Partition refinement is *also* an instance**, and this is **proved in the literature**: Ranzato–Tapparo, *Generalizing the Paige–Tarjan algorithm by abstract interpretation* (Inf. Comput. 206 (2008), arXiv:cs/0612120) shows bisimulation/partition refinement **is** an abstract interpretation, via a **Galois insertion between the lattice of partitions and the lattice of abstract domains** ("partitions are a higher-order abstraction of abstract domains"). Their generalized-PT computes the *minimal refinement of an abstract model* that strongly preserves a temporal language — i.e. *coarsest sound abstraction* — which is exactly the lfp/coarsest-bisimulation graphplay formalizes (Tower-8). **This is the scholarly anchor for any "Tower-9 Galois layer."**

So the honest unifying statement — defensible, cited, non-inflated — is:

> **Both WL-refinement (graphplay) and lattice-deduction (LDT) are Kleene-fixpoint computations on complete lattices carrying Galois connections, in the sense of Cousot–Cousot abstract interpretation; graphplay's is the *coarsest-sound-abstraction-building* (refinement / partition-domain Galois insertion, Ranzato–Tapparo) leg and LDT's is the *value-narrowing-within-a-fixed-abstraction* (over-approximation, Cousot) leg.** Refinement *distinguishes states* (builds the quotient); deduction *eliminates values* (descends to the solution).

### 1.3 CEGAR is the refine ⊣ deduce loop

Clarke–Grumberg–Jha–Lu–Veith, *Counterexample-guided abstraction refinement* (CAV 2000; JACM 50(5):752–794, 2003): start with a coarse abstraction; model-check it (the *deduction/analysis within the abstraction*); if a returned counterexample is **spurious**, **refine** the abstraction (split the offending abstract states) and repeat. The two motions are exactly **(deduce = analyze inside the current abstraction)** and **(refine = rebuild a finer abstraction)** — the *alternation* of the two fixpoints. This is the precise sense in which "the alternation refine↔deduce is CEGAR": refinement is the abstraction-*builder* (a partition lfp), deduction/checking is the *engine* inside it (often a gfp on the abstract state space). A *verified* CEGAR loop with bisimulation-minimization as the builder and lattice-deduction as the engine is the natural "Tower-9 dynamics" target — graded below (PLAUSIBLE, partly aspirational).

Note the deeper genealogy that makes the LDT↔graphplay pairing *not a coincidence*: **D'Silva–Haller–Kroening, *Abstract Conflict Driven Learning* (POPL 2013)** — Haller is the LDT senior author — recast CDCL conflict analysis as abstract interpretation whose engine **"combines over-approximation of greatest fixed points with under-approximation of least fixed points."** That is the *two-fixpoint* (gfp-narrow + lfp-learn) structure in its original PL form; LDT is its neural descendant on the deduction leg, and graphplay supplies a verified instance of the refinement/lfp leg. The communities are the same neighbourhood.

### 1.4 The CSP instance: k-WL ↔ k-consistency ↔ Sherali–Adams makes "refine = propagate" literally one hierarchy

This is the rung that turns the duality from analogy into a *named, theorem-backed correspondence* on one side (the constraint side):

- **Atserias–Maneva**, *Graph isomorphism, Sherali–Adams relaxations and expressibility in counting logics* (SIAM J. Comput. 42(1), 2013): the **level-`k` Sherali–Adams** LP relaxation of the isomorphism polytope **interleaves in power** with **`k`-WL** colour refinement and with **`C^k`** (first-order counting logic, `k` variables) indistinguishability.
- **Grohe–Otto** (*Pebble games and linear equations*, CSL 2012 / J. Symb. Logic 2015) sharpen this to a *precise* match (a modified counting pebble game = a Sherali–Adams variant) and prove the interleaving is **strict**.
- **Berkholz–Nordström** give near-optimal **lower bounds** on WL refinement steps / quantifier depth (`k`-WL can need `n^{Ω(k/log k)}` iterations).
- **Atserias–Bulatov–Dawar**, *On the power of k-consistency* (ICALP 2007), and the bounded-width / Datalog CSP line (Feder–Vardi; Barto–Kozik; Kozik): the **`k`-consistency** algorithm (the canonical *constraint-propagation* procedure — iteratively delete partial assignments on ≤ `k` variables that don't extend) solves exactly the **bounded-width** CSPs, and `k`-consistency power = `C^k` = `k`-WL.

So on the CSP instance, **"refine the partition" (k-WL) and "propagate the constraints to local consistency" (k-consistency) are levels of the *same* hierarchy** (both `≡ C^k ≡` level-`k` Sherali–Adams). This is the strongest, most literally-true form of the duality:
- LDT's `dedₚ` *is* arc-/local-consistency propagation (its naked/hidden singles = the standard rules; `ldt_assessment.md §2(iii)`), i.e. a `k`-consistency-style narrowing;
- graphplay's WL *is* the colour-refinement / `C^k` side;
- they meet in the **Atserias hierarchy**.

The honest caveat (already in `ldt_assessment.md §2(iii)`): this is a correspondence of *hierarchies / expressive power*, **not** a transfer of carriers. `k`-WL refines a *partition of vertex-tuples*; `k`-consistency narrows *candidate partial-assignments*; LDT's `dedₚ` narrows *per-cell candidate sets on a fixed instance*. Same hierarchy, different objects, opposite fixpoint direction. graphplay even has the scaffolding for the higher levels: `kWlStep` / `kWlRefine_stable` (`Graphplay/Algorithm/WLRefinement.lean`). It does **not** formalize the Sherali–Adams or `k`-consistency equivalence — that would be a *large* descriptive-complexity project, out of near-term scope (§4, aspirational).

---

## 2. Expansion directions, graded REAL / PLAUSIBLE / SPECULATIVE

Grading key. **REAL/SOLID** = the mathematics is classical and the Lean is a short, self-contained build over existing assets (high-confidence, do-it). **PLAUSIBLE** = the target is true and reachable but is *new* Lean work of nontrivial size, or depends on one unproved-in-repo lemma. **SPECULATIVE** = the connection is an analogy whose load-bearing step is unestablished or likely false; state the precondition, do not build on faith.

### 2.A "Tower-9" Galois/abstraction layer unifying the quotient, Tower-8 bisimulation, LDT's α⊣γ, and dregg2's Disclosure lattice — **PLAUSIBLE (scoped), with one SPECULATIVE sub-claim to drop**

**The honest state of the repo.** Grep confirms graphplay has **zero** `GaloisConnection`/`GaloisInsertion` instances (every "adjoint" in the corpus is operator self-adjointness/Hermiticity). The `Refines` order exists (`Equitable.lean:463` structure; `WLRefinement.lean:189` predicate) and `wlStep` is monotone in it, but the **partition lattice is not packaged as a Mathlib `CompleteLattice`**, and the abstraction adjunction `α ⊣ γ` for *any* of these lattices is **not present**. So "wire our verified Galois machinery to Tower-8" would *overstate*: the Galois machinery does not yet exist. Tower-9 = **build that machinery**, and it is genuinely graphplay's native idiom (monotone fixpoints, coalgebraic run-invariants) — so it is a *good* fit, but it is construction, not wiring.

**Is `cellInflate ⊣ cells` a Galois connection? — NO. Drop it.** I checked: `cellInflate : Matrix I I ℂ → Matrix V V ℂ` (`Equitable.lean:240`) is a **block-diagonal linear lift of matrices** with a `/|cell|` normalization; `cells : V → I` is the **partition-assignment function**. These are not adjoint maps of a common order — they do not even have comparable domains/codomains (one is `Matrix I I ℂ → Matrix V V ℂ`, the other `V → I`), and `cellInflate`'s content is a *linear-algebra subspace isometry* (`restrict_eq_symmQuotient`, an **exactness** statement: the `r×r` quotient computes the *same* spectrum/evolution on the cell-uniform subspace), **not** an over-approximation adjunction. Calling them a Galois connection is a category error. (This was already the warning in `ldt_assessment.md §2(i)`/`bisim_quantum_verification.md`: the quotient is *exact reduction*, the dual species of LDT's *lossy approximation*.)

**The Galois connection that IS real and is the right Tower-9 spine:** the **partition ↔ abstract-domain Galois insertion of Ranzato–Tapparo (2008)** — `Part(V)` (or its image as a closure-operator lattice on `℘(V)`) abstracts the powerset domain, and partition refinement is the lfp building the coarsest strongly-preserving abstraction. *That* is a real, published `GaloisInsertion`, it is exactly the structure under Tower-8, and it is the principled thing to formalize. Concretely the reachable Tower-9 statements:

- **(T9-a) REAL/SOLID once started:** `instance : CompleteLattice (partition lattice)` + `wlStep` as an `OrderHom`, and `wlRefine_coarsestEquitable` re-expressed as a genuine **`OrderHom.lfp`/`gfp`** identity. This is mostly repackaging proved facts; the only friction is choosing the carrier (Mathlib `Setoid V` with its lattice, or `{c : V → ℕ}/≈`) and porting `wlRefine_stable` to "Kleene iteration reaches the fixpoint." *Reachable.*
- **(T9-b) PLAUSIBLE:** an **abstract `AbstractInterpretation` interface** (a `structure` bundling `C`, `A`, `GaloisConnection α γ`, a sound `f♯`, and the transfer lemma) with **two instances**: (i) the LDT grid-powerset domain (§2 of `ldt_assessment.md`'s build), (ii) the partition-domain insertion. Proving the interface + both instances is real new work but each piece is short and classical. *Reachable with effort; the unification theorem is "both are `AbstractInterpretation`," which is honest and modest.*
- **(T9-c) SPECULATIVE — do NOT claim:** "dregg2's `Disclosure`/knowledge lattice is an instance of the same interface." dregg2 lives in the **separate `breadstuffs` repo** and is **not a Lake dependency** (Tower-8's header says so explicitly); graphplay only *mirrors* its coalgebra abstractly via `TransitionCoalg`. The authority-/knowledge-lattice reading is **explicitly omitted as "too loose"** in Tower-8's own inventory. Pulling `Disclosure` into a Galois unification would require importing or re-deriving an external artifact and asserting an information-lattice adjunction graphplay has never built. **Leave it as a remark ("the same interface would also receive an information-disclosure lattice"), not a theorem.**

**Verdict: PLAUSIBLE, scoped to (T9-a)+(T9-b) over the Ranzato–Tapparo partition-domain insertion + the LDT domain.** Reuse `Tower8.stepInv_preserved` for the run-invariant. Drop `cellInflate ⊣ cells` (category error) and the dregg2 `Disclosure` instance (out-of-repo, too loose).

### 2.B Verified abstraction-refinement (CEGAR): bisimulation-minimization (lfp builder) + lattice-deduction (gfp engine) as a two-fixpoint loop — **PLAUSIBLE skeleton, aspirational full loop**

The *concept* is exactly right and exactly the LDT-authors' lineage (Abstract Conflict Driven Learning's gfp-narrow + lfp-learn; CEGAR's refine↔check). What is **reachable in Lean near-term**:

- **REAL/SOLID:** the **soundness invariants of each leg in isolation**: (deduce leg) `stepInv_preserved`-based run-soundness of narrowing (this is exactly the §5 build); (refine leg) `wlRefine_coarsestEquitable` + `equitable_isBisim` as "the built abstraction is a sound quotient (a genuine bisimulation, strongly preserving observations)."
- **PLAUSIBLE:** a **single CEGAR round** stated abstractly: given a sound abstraction `Q` (a bisimulation quotient) and a sound deduction engine on it, *if* the engine reports a property and the abstraction is exact for that property (cell-uniform, via `obs_property_lift` / `cellUniformPST_iff_quotientPST`), the property holds on the host. This is a **lift-along-a-coalgebra-morphism** theorem — graphplay already has the shape (`obs_property_lift`). Packaging *one round* (abstract → check → lift) is reachable.
- **ASPIRATIONAL:** the **full iterated loop with spuriousness detection and guaranteed termination/progress** (the actual CEGAR fixpoint, with a measure that each refinement strictly increases lattice height until the property is decided). This needs a refinement *operator* on abstractions with a well-founded progress measure and a spurious-counterexample analysis — a real verified-model-checking sub-project, not a one-module build. State it as the *direction*, build only the single-round lift now.

**Verdict: PLAUSIBLE for the single-round lift + per-leg soundness (reachable); the closed iterated CEGAR loop is aspirational.** The honest deliverable is "verified one CEGAR round (sound-abstraction → sound-deduce → property-lift)," not "verified CEGAR."

### 2.C A deduction-dual on the quantum side (gfp-narrowing on amplitudes dual to cell-splitting) — **SPECULATIVE → effectively NO. State the asymmetry.**

This is the direction to be most skeptical about, and the skeptical answer is the honest one. The quantum content of graphplay is **entirely on the refinement leg**:
- `restrict_eq_symmQuotient` / `cellUniformPST_iff_quotientPST` / `spec Q̃ ⊆ spec A`: the CTQW restricted to the cell-uniform subspace **is** the walk on the `r×r` symmetric quotient — an **exact, spectrum-preserving** reduction *along the equitable partition* (the refinement object). This is the Krovi–Brun (2007) / Bachman–Tamon (2011) quotient-walk picture, formalized (`bisim_quantum_verification.md §1, §6`).
- The Szegedy `√`-speedup (`SzegedyWalk_unitary`, `szDiscriminant_spec`, the `exp(±i·arccos λ)` Jordan fold) is a **spectral / linear-operator** phenomenon.

A "deduction dual on amplitudes" would need a **monotone reductive operator on a lattice of quantum states/amplitudes**, descending a gfp to *eliminate amplitude*. There is no such lattice here, and there is a structural reason there cannot be a *clean* one: amplitudes live in a **complex inner-product space** (no canonical complete-lattice order; `ℂ` is not ordered, superposition is not meet/join), whereas deduction needs a **distributive/Boolean candidate lattice** (∩, ∪, ⊆). The honest reading:

> **The refinement↔deduction duality is a *classical* duality.** Its **refinement leg has a genuine quantum lift** (the equitable-quotient CTQW/Szegedy reduction, exact and spectrum-preserving). Its **deduction leg is intrinsically classical-CSP** (a Boolean candidate lattice with arc-consistency narrowing). So the picture is **asymmetric**: `refinement = quantum-walk-quotient` vs `deduction = classical-CSP`, and that asymmetry is itself the correct thing to state — not a symmetric "quantum deduction."

Where a *thin* honest analogue might live (each conditional, none a Lean target now):
- **Quantum CSP / non-commutative constraint relaxations.** There *is* a real literature on quantum/operator relaxations of CSPs and the quantum value of nonlocal games (NPA/Lasserre-style SDP hierarchies as the operator analogue of Sherali–Adams). graphplay has `Graphplay/QuantumCSP.lean` and operator-system files. A "quantum-relaxation dual of the Atserias hierarchy" is a *real research area*, but it is **not** "narrowing amplitudes in a quantum walk dual to cell-splitting" — it is SDP/operator-algebraic, a different object, and graphplay has no fixpoint-narrowing result there. **SPECULATIVE; do not conflate with the LDT duality.**
- **Lindblad/open-system contraction** (`Graphplay/Graphon/Lindblad.lean`): a CPTP semigroup contracts toward a fixed point — but that is *spectral mixing* (a gfp of a *linear* CP map, in the operator-order sense), which is precisely the analogy `ldt_assessment.md §2(ii)` already graded **SUPERFICIAL** for LDT (no `λ₂` in LDT's discrete gfp). Reusing it here would re-import the same falsified bridge. **Do not.**

**Verdict: SPECULATIVE, effectively NO clean quantum deduction-dual. The correct, publishable statement is the *asymmetry*: the duality is classical; only the refinement leg lifts to the quantum walk (exactly, via the equitable quotient).** This is a *sharper* and *more credible* claim than a forced symmetric one.

### 2.D A Galois connection between the solution-lattice and the symmetry-lattice (candidate-sets ↔ partitions/automorphisms), connecting to equitable ⊋ orbit — **PLAUSIBLE-but-a-stretch; one clean true nugget inside it**

The appealing picture: the LDT **solution/candidate lattice** `A` and graphplay's **symmetry/partition lattice** ought to be linked by an adjunction (symmetries of an instance constrain its solutions; solution structure reveals symmetry). Assessment:

- **The clean true nugget (REAL, with honesty-status split — direction stated carefully):** the WL/symmetry gap is a genuine lattice inequality, *partly proved, partly stated* in-repo. The code facts (`Graphplay/Algorithm/WLOrbit.lean`): the orbit partition is **always equitable** (`orbitPartition_isEquitable`, a constructed `def` — real), and the **WL-stable / coarsest-equitable partition *refines* the orbit partition** is **PROVED** (`wlStable_refines_orbit`, line 273, real proof via reindex-and-refine: every automorphism preserves every WL colour, so each orbit is a union of WL-cells) — i.e. in the finer-than order **`WL-stable ⊑ orbit`** (WL-stable is *finer than or equal to* orbits). The **strictness** — that this can be *proper* (`HasPhantomSymmetry`: vertices with equal WL colour that *no* automorphism relates, witnessed by the **Cai–Fürer–Immerman** gadget) — is **STATED BUT `sorry`-stubbed** in-repo (the file is an avowed statement-level sketch, ~10 sorries; the CFI existence witness is among them). It is classical and true (CFI, FOCS '89) but **not machine-checked here**. So the honest "symmetry-lattice ↔ refinement-lattice" content is: **`WL-stable ⊑ orbit` is PROVED in-repo; the strict-in-general gap is true-but-unformalized (CFI `sorry`).** Combinatorial indistinguishability is *finer than* (refines) true symmetry. (Note the subtlety behind the brief's "equitable ⊋ orbit" phrasing: among *all* equitable partitions the orbit one is a *coarsening target*, but the canonical *coarsest-equitable = WL-stable* object refinement actually computes sits **below** orbits in the refinement order, strictly when phantom symmetry exists.)
- **The stretch (SPECULATIVE):** packaging *candidate-sets ↔ automorphisms* as a **Galois connection** (à la a Galois correspondence between sub-structures and symmetry sub-groups, the classical Galois-theory shape) is **not** something graphplay has, and the LDT side has *no symmetry/automorphism structure at all* (its lattice is per-cell candidate sets on a *fixed* instance; there is no group action). So "Galois connection between solution-lattice and symmetry-lattice" **across the LDT↔graphplay bridge** is a stretch: the two lattices live in different problems (LDT's fixed-instance candidate sets vs graphplay's graph automorphisms), and there is no adjunction relating them. *Within graphplay alone*, an orbit↔equitable Galois-style relationship is closer to reachable (it is a refinement inequality, and the orbit-lattice / partition-lattice connection could be packaged), but it is **not** the LDT duality and should not be sold as such.

**Verdict: the `WL-stable ⊑ orbit` (strict, via CFI) inequality is REAL and proved-in-repo; "candidate-sets ↔ automorphisms as a Galois connection bridging LDT and graphplay" is SPECULATIVE (no group action on the LDT side, different problems).** Keep the proved refinement inequality; do not claim the cross-bridge Galois correspondence.

---

## 3. What Tower-9 would add *beyond* the §5 first brick — reachable vs aspirational

The §5 brick (`LatticeDeduction.lean`) delivers: the LDT abstract domain `A`, the **`GaloisConnection α γ`**, `dedₚ` as a **sound reductive closure**, and the **run-soundness invariant** via `stepInv_preserved`. Tower-9, layered on top, would add:

**Reachable in Lean (do these if Tower-9 is pursued):**
1. **(T9-a)** `CompleteLattice` on the partition carrier + `wlStep : OrderHom` + `wlRefine_coarsestEquitable` as an **`OrderHom.lfp` identity**. *Repackaging; small.*
2. **(T9-b)** an **`AbstractInterpretation` `structure`** (Galois connection + sound transformer + fixpoint-transfer lemma `α (gfp f) ⊑ gfp f♯`), with the **LDT grid-powerset** and the **partition/Ranzato–Tapparo** domains as two instances. The *unification theorem* = "both are `AbstractInterpretation`." *New but classical; the transfer lemma is a few lines over Mathlib's `OrderHom.gfp`.*
3. **single-round CEGAR lift**: abstract (bisimulation quotient) → sound deduce → `obs_property_lift` to the host. *Reuses Tower-8 directly.*

**Aspirational (state as direction, not near-term build):**
4. The **full iterated CEGAR loop** with spurious-counterexample analysis and a well-founded progress measure (true verified abstraction-refinement). *Sub-project.*
5. The **k-WL ↔ k-consistency ↔ Sherali–Adams equivalence** formalized (using `kWlStep`). *Large descriptive-complexity project; Mathlib lacks the LP/Sherali–Adams and `C^k` infrastructure.*
6. Any **quantum deduction-dual** (§2.C) — not reachable, likely not true; build the *asymmetry statement* (a one-paragraph note) instead.

**The precise added value of Tower-9 over the brick:** the brick proves **LDT's own missing soundness theorem**; Tower-9 (a)+(b) proves that **LDT's deduction and graphplay's refinement are two instances of one verified abstract-interpretation interface** — i.e. it makes the *duality itself* a machine-checked statement (`both : AbstractInterpretation`), not just prose. That is the genuine increment, and it is reachable. Everything past (b)+(3) is aspirational.

---

## 4. Honest scope notes (so nothing here inflates)

- **graphplay has no Galois connection today.** Every claim above that needs one is flagged as *new construction*. The literature license for the partition-domain one is Ranzato–Tapparo (2008); the LDT one is the paper's own App. A. Neither is "wiring existing assets."
- **The quotient is exact, not approximate.** `restrict_eq_symmQuotient` is a subspace **isometry** (no information loss on the symmetric sector), the *dual species* of LDT's lossy `α∘γ`. Do not present the equitable quotient as an over-approximation; it is a no-loss symmetry reduction. (Stated repeatedly because it is the easiest thing to get wrong.)
- **The spectral-gap / loops-to-convergence bridge stays retracted for LDT** (`ldt_assessment.md §2(ii)`): LDT's gfp is well-founded discrete descent with **no iterated linear operator and no `λ₂`**. The convergence quantity is **lattice height / longest deduction chain** (a Cousot/combinatorial height), not a spectral mixing rate. Any Tower-9 "iteration count" statement must be the *height* statement, never `log ε / log|λ₂/λ₁|`.
- **dregg2's `Disclosure`/authority lattice is out-of-repo and deliberately omitted** from graphplay's formal content (Tower-8 header + inventory). Reference it as motivation only.
- **The k-WL = k-consistency = Sherali–Adams correspondence is a correspondence of *expressive-power hierarchies*, not of carriers/proofs.** True and citable as *positioning*; formalizing the equivalence is a large separate project.
- **ember is not an author/contributor of LDT** (exhaustive grep: zero `ember`/`arlynx`/`lunar.town`/`cmr://` in repo, paper, git; sole committer is Haller). Social proximity only — an outreach lever, not prior involvement (`ldt_assessment.md §4`).

---

## 5. Bottom line — the sharpest REAL directions, what stays SPECULATIVE, the one build

**The 2–3 sharpest REAL directions (high-confidence, do them):**

1. **The machine-checked run-soundness of learned lattice-deduction** (the brick, below) — proves *LDT's own unproved empirical-soundness claim* ("returns a correct answer or abstains") using the *one* graphplay asset that genuinely fits, **Tower-8's `stepInv_preserved`**. REAL, finite, falsifiable, and the precise currency (a *proof*) this PL∩SAT community trades in. **This is the single most valuable near-term Lean build.**
2. **Tower-9 (a)+(b): the verified abstract-interpretation interface with two instances** (LDT grid-powerset + the Ranzato–Tapparo partition domain), making the **refinement⊣deduction duality a machine-checked statement** ("both are `AbstractInterpretation`"). REAL/SOLID for (a) (repackaging proved WL facts as `OrderHom.lfp`), PLAUSIBLE for (b) (short classical new work). This is the honest, non-inflated formal form of "expand outwards."
3. **The lattice inequalities as the *positioning* spine**: `WL-stable ⊑ orbit` (PROVED in-repo as `wlStable_refines_orbit`; the strict-gap/CFI witness is true-but-`sorry`-stubbed) and the **lfp(WL) ⟂ gfp(deduction)** Knaster–Tarski duality (Baldan et al.; Cousot; CEGAR; Atserias hierarchy) — all *cited, classical, and either proved-in-repo or one-module-away*. This is the paragraph that frames the whole program credibly.

**What stays SPECULATIVE (state with preconditions, do not build on faith):**
- A **quantum deduction-dual** (gfp-narrowing on amplitudes): effectively **NO** — the duality is classical; only the *refinement* leg lifts to the quantum walk (exactly, via the equitable quotient). The honest deliverable is the **asymmetry statement**, not a symmetric quantum deduction. (Quantum/operator CSP relaxations are a *different*, SDP-based object — do not conflate.)
- A **cross-bridge Galois connection between LDT's solution-lattice and graphplay's symmetry-lattice**: a stretch — no group action exists on the LDT side; different problems. (The *intra*-graphplay `WL-stable ⊑ orbit` inequality, strict via CFI, is the real, proved residue.)
- The **dregg2 `Disclosure` lattice as a Tower-9 instance**: out-of-repo, deliberately omitted — a remark, not a theorem.
- The **full iterated CEGAR loop** and the **formalized k-WL=k-consistency=Sherali–Adams equivalence**: true but aspirational sub-projects, not near-term builds.

**The single most valuable near-term Lean build (unchanged from `ldt_assessment.md §3`, restated as the concrete brick):**

> **`Graphplay/Integrations/LatticeDeduction.lean` — `theorem soundDeduction_run_preserves_solutions`.**
> 1. `A := pos → Finset V` with pointwise `⊑`; `instCompleteLattice`.
> 2. `γ a := {s | ∀ i, s i ∈ a i}`; `α S i := S.image (· i)`; **prove `GaloisConnection α γ`** (the paper's two round-trip laws — both short).
> 3. `soundNarrow (f : A → A) := ∀ a, f a ⊑ a ∧ (‖p‖ ∩ γ a) ⊆ γ (f a)` (reductive **and** never drops a true solution).
> 4. Instantiate `Tower8.TransitionCoalg` with carrier `A`, `step` = abstract narrow-or-branch; apply **`stepInv_preserved`** with `Good a := (‖p‖ ∩ γ ⊤) ⊆ γ a` ⟹ every reachable Solve-state keeps every true solution alive ⟹ a singleton-per-cell terminal **is** a solution.
> 5. A short note recording the **lfp(WL) ⟂ gfp(deduction)** Knaster–Tarski/Cousot duality and (now) the **`AbstractInterpretation`-interface** framing, with the spectral-gap bridge explicitly retracted for LDT.

If `α ⊣ γ` and the run-invariant type-check, the duality is real and graphplay hands the LDT authors the soundness artifact they lack — a clean outreach hook to Haller/Santolucito. If `α ⊣ γ` or the invariant resists, *that resistance is itself the honest finding* that the connection is thinner than the prose. Either way: a proof, not a press release. ( ◕‿◕ )

---

### Sources

- Tarski, *A lattice-theoretical fixpoint theorem and its applications*, Pacific J. Math. 5 (1955): https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem
- Baldan, Eggert, König, Padoan, *Fixpoint Theory – Upside Down* (FOSSACS '21; LMCS 2023), arXiv:2101.08184: https://arxiv.org/abs/2101.08184
- Cousot & Cousot, *Abstract interpretation: a unified lattice model...* (POPL '77): https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf
- Cousot & Cousot, *Systematic design of program analysis frameworks* (POPL '79). (Patrick Cousot publications: https://pcousot.github.io/publications.html)
- Clarke, Grumberg, Jha, Lu, Veith, *Counterexample-guided abstraction refinement* (CAV 2000; JACM 50(5):752–794, 2003): https://www.semanticscholar.org/paper/d859b6698969b788bd25bc2abd96e6e57e341bea
- D'Silva, Haller, Kroening, *Abstract Conflict Driven Learning* (POPL 2013): http://www.kroening.com/papers/popl2013.pdf
- Ranzato & Tapparo, *Generalizing the Paige–Tarjan algorithm by abstract interpretation* (Inf. Comput. 206 (2008)), arXiv:cs/0612120: https://arxiv.org/pdf/cs/0612120
- Paige & Tarjan, *Three partition refinement algorithms*, SIAM J. Comput. 16(6):973–989, 1987.
- Atserias & Maneva, *Graph isomorphism, Sherali–Adams relaxations and expressibility in counting logics* (SIAM J. Comput. 42(1), 2013): https://www.researchgate.net/publication/220139057
- Grohe & Otto, *Pebble games and linear equations* (CSL 2012; J. Symb. Logic 2015), arXiv:1204.1990: https://arxiv.org/abs/1204.1990
- Atserias, Bulatov, Dawar, *On the power of k-consistency* (ICALP 2007): https://link.springer.com/chapter/10.1007/978-3-540-73420-8_26
- Berkholz & Nordström, lower bounds for Weisfeiler–Leman refinement / quantifier depth (LICS 2016). (Grohe, *The iteration number of the WL algorithm*, arXiv:2301.13317: https://arxiv.org/pdf/2301.13317)
- Krovi & Brun, *Quantum walks on quotient graphs* (Phys. Rev. A 75, 062332, 2007), arXiv:quant-ph/0701173: https://arxiv.org/abs/quant-ph/0701173
- Bachman, Tamon et al., *Perfect state transfer on quotient graphs* (2011), arXiv:1108.0339: https://arxiv.org/abs/1108.0339
- LDT: *Lattice Deduction Transformers*, Davis, Haller, Alfarano, Santolucito, arXiv:2605.08605 (assessed in `research/ldt_assessment.md`).
