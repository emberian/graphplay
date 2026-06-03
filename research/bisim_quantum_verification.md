# Quantum walks on bisimulation-reduced transition systems: where a speedup can live

**For** Tino Tamon. **From** the graphplay formalization effort. **Date** 2026-06-02.

---

For the question *"are there quantum speedups for verification/reachability on bisimulation-reduced
transition systems?"*, the honest map has three regimes.

- **Explicit transition systems: the quotient is a structural explanation, not a new source of
  speedup.** A quantum walk confined to the symmetry subspace is a walk on the smaller quotient
  (Krovi–Brun 2007), and a √-type hitting-time win is Szegedy's, attached to the spectral gap.
  Building the quotient classically costs Paige–Tarjan `O(m log n)`, which matches or dominates the
  walk on the tiny quotient. Krovi–Brun's standing conjecture runs the other way: a small quotient is a
  *necessary condition* for a fast quantum hitting time. Our `restrict_eq_symmQuotient` /
  `cellUniformPST_iff_quotientPST` is an axiom-clean formal instance of this picture (the PST half is
  Bachman–Tamon 2011, cited in `DistributedQuotient.lean`).

- **Succinct / symbolic systems: the one regime with room.** If the system is given succinctly — a
  circuit over `n` bits, `N = 2^n` states — and the quotient has `r = poly(n)` cells while
  bisimulation on succinct systems is PSPACE-complete to decide, then a quantum walk addressing the
  quotient *as an oracle it never materializes* can beat any classical method that must build the
  partition. This regime appears unclaimed. It holds under one precondition: the quotient is
  quantum-oracle-addressable without solving the bisimulation — cell membership and cell-to-cell
  amplitudes computable in `poly(n)` directly from the symbolic encoding.

- **Computing the coarsest bisimulation: a modest Grover win at best.** Classical Paige–Tarjan is
  `O(m log n)` with a matching `Ω((m+n) log n)` paradigm lower bound (Groote et al. 2021); the
  sequential refinement dependency chain resists quadratic speedup. Not where the formalized corpus has
  leverage.

The sharpest test: take the hypercube-fold (cells = Hamming weight, `poly(n)`-computable) and the
`K_n`-fold already in the corpus, and ask whether the cell-level reachability task stays classically
hard once cell membership is cheap. The succinct regime is real only if cheap cell-naming can coexist
with hard cell-reachability.

## 1. What graphplay proves

**Bisimulation ≡ equitable partition (Tower 8).** Cell-equality `cells x = cells y` is a genuine
bisimulation of the walk coalgebra (`dist_equitable_isBisim`), the kernel of the coalgebra morphism
`cells` (`dist_cells_isCoalgMorphism`), with non-trivial successor (`distVertexCoalg_next`, the
take-turn-`j`-land-in-cell-`j` Moore machine). The coarsest equitable partition = coarsest
bisimulation = Paige–Tarjan = 1-WL refinement (`dist_bisim_refines_wlStable`). The Paige–Tarjan
*converse* (coarsest equitable ⇒ coarsest bisimulation) is the remaining open step in `Tower8.lean`;
this scopes the "computing-bisimulation" regime, not the quotient-lift used below.

**Szegedy quantum walk.** `SzegedyWalk_unitary` (`U Uᴴ = 1`), and `szDiscriminant_spec`, axiom-clean:
`spectrum randomWalkOp ⊆ spectrum D₀` for `D₀ = reflStepDiscriminant R S`, with eigenvalue
correspondence `exp(±i·arccos λ)` via Jordan's lemma (`JordanLemma.lean`, `U = SR` two-reflection
product). The eigenphase gap is `arccos`-folded, hence quadratically larger than the classical spectral
gap — the spectral engine of the √-speedup.

**The equitable quotient lift.** `restrict_eq_symmQuotient`, `cellUniformPST_iff_quotientPST`: the CTQW
restricted to the cell-uniform subspace is the walk on the `r×r` symmetric quotient `Q̃`,
spectrum-preserving (`spec Q̃ ⊆ spec A`); cell-uniform PST on the host ⟺ PST on the quotient.
`dist_quotientPST_bridge` reuses this; `dist_next_eq_pst_target` ties the Moore successor to the PST
endpoint. This is the formal license to run the Szegedy analysis on `Q̃` instead of `A`.

The spatial-search wins in the corpus (`K_n` at `O(√n)`, hypercube) come from amplitude amplification /
the spectral gap; the equitable partition reduces the analysis to a small quotient.

## 2. The sharpened conjecture and its falsifier

**Succinct regime.** Given `T` succinct over `n` bits (`N = 2^n`) with quotient `r = poly(n)`, decide
reachability / detect a marked cell. Deciding bisimulation on a succinct system is PSPACE-complete; even
the best symbolic Paige–Tarjan can blow up to `2^n`. If the quotient walk `Q̃` (size `poly(n)`) is
quantum-oracle-addressable directly from the symbolic encoding, Szegedy on `Q̃` runs in
`poly(n)·O(√HT(Q̃))`.

The crux: does addressing `Q̃` as an oracle require solving the PSPACE-hard bisimulation? A positive
result needs a specific symbolic family where cell membership is `poly(n)`-computable (cells = a known
invariant: Hamming weight, an orbit under a succinctly-described symmetry, a syntactic congruence class)
while *coarsest* bisimulation is hard. Once the oracle source is given explicitly, an a-priori quantum
speedup can evaporate (Phys. Rev. X 2024, arXiv:2303.11317) — the advantage lives only where the
quotient cannot be cheaply materialized.

## 3. The smallest decisive next step

Before any Lean, answer for the two corpus fixtures with an a-priori prediction:

1. Is `cells(x)` `poly(n)`-computable from the symbolic encoding without materializing the partition?
   (Hypercube: yes, Hamming weight. `K_n`: yes.)
2. Is the marked-cell detection task on the `2^n`-state symbolic system classically `2^{Ω(n)}`, or does
   the same structure that makes `cells` cheap give a classical `poly(n)` shortcut?

For the hypercube, the structure that makes `cells = HammingWeight` cheap also makes the classical
reachability task `poly(n)` — so the quantum win does not survive for the easy fixtures. The regime is
real only if some family has cheap cell-naming with classically-hard cell-reachability. Finding or
ruling out one such family is the whole question, answerable on paper before committing formalization.

If it survives, the target theorem is: for a symbolic family `F_n` with `cells` `poly(n)`-computable and
quotient `Q̃_n` spectrum-preserving (via `cellUniformPST_iff_quotientPST`), the Szegedy walk on `Q̃_n`
has an explicit quantum-oracle implementation whose `arccos`-folded eigenphase gap yields `O(√HT(Q̃_n))`
detection while any classical method on the `2^n`-state encoding costs `2^{Ω(n)}`.

## 4. Bottom line

The bisimulation ≡ equitable-partition bridge and the spectrum-preserving quotient lift are
axiom-clean, and they are a precise formal instance of the Krovi–Brun (2007) / Bachman–Tamon (2011)
quotient-walk picture — formalization of known structure. The quantum advantage is Szegedy's
(`arccos`-fold, formalized via the Jordan lemma); the quotient is the structural explanation of when
such advantages exist. A novel claim can live only in succinct/symbolic systems where bisimulation is
classically intractable yet the quotient is quantum-oracle-addressable — stated with that precondition
attached. ("Quantum model checking" in the literature means model-checking quantum systems, a different
problem; not prior art here.)

---

### Sources
- Szegedy, *Quantum Speed-up of Markov Chain Based Algorithms* (FOCS 2004).
- Magniez–Nayak–Roland–Santha, *Search via Quantum Walk*: https://www.math.uwaterloo.ca/~anayak/papers/NRS.pdf
- Apers–Gilyén–Jeffery, *Quadratic speedup for finding marked vertices*, arXiv:1903.07493.
- Krovi & Brun, *Quantum walks on quotient graphs*, arXiv:quant-ph/0701173.
- Ide, *Partition of graphs and quantum walk based search*, arXiv:1812.06376.
- Bachman, Tamon et al., *Perfect state transfer on quotient graphs*, arXiv:1108.0339.
- Belovs–Reichardt, *Span programs / st-connectivity*, arXiv:1203.2603.
- Jarret–Jeffery–Kimmel–Piedrafita, *Connectivity and Related Problems*, arXiv:1804.10591.
- Paige & Tarjan, *Three partition refinement algorithms*, SIAM J. Comput. 16 (1987).
- Groote et al., *Lowerbounds for Bisimulation by Partition Refinement*, arXiv:2203.07158.
- *Opening the Black Box Inside Grover's Algorithm*, PRX 2024, arXiv:2303.11317.
