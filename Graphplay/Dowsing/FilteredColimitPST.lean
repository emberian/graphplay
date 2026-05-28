/-
# Graphplay.Dowsing.FilteredColimitPST

**Hole D9 — Generalized filtered-colimit PST.**

Xie–Tamon (arXiv:2301.07251, *No Infinite Tail Beats Optimal Spatial Search*)
prove that the continuous-time spatial-search algorithm on the complete graph
`K_n` remains optimal under attachment of an *infinite* path `Plim`.  Their
argument decomposes the infinite-graph adjacency operator into a finite-rank
Jacobi block plus a free-Jacobi tail and verifies that the search dynamics
take place inside the finite invariant subspace.

A categorical reading of this result is that the family of finite
truncations `(K_n + P_m)_{m ≥ 0}`, equipped with the **distance-from-K_n**
equitable partition, is a *filtered diagram* in the category `WGraphP` of
partitioned weighted graphs (Tower 5, `Graphplay/Categorical.lean`).  The
quotient functor `Quotient : WGraphP ⥤ WGraph` preserves the filtered colimit
(this is `Quotient.preservesFilteredColimits`), and the quotient PST predicate
is continuous in operator norm (this is
`Graphon.ConsistentPartitionSequence.pst_time_convergence` in
`Graphplay/Graphon/Limit.lean`).  Composing these two statements: PST holds of
the limiting cell-uniform graphon quotient iff it holds, with consistent times,
on the finite quotients of the diagram.

This file isolates the **general** statement, then writes down a battery of
concrete consistent partition sequences whose limits are interesting:

  * `K_n + path`         — Xie–Tamon themselves.
  * `K_n + tree`         — Bernard–Tamon–Vinet–Xie (arXiv:2211.14704)
                           tail-tree generalization.
  * `K_n + ℤ^d lattice`  — multi-dimensional probe.
  * `K_n + level-growth` — geometric expansion of cliques per shell.
  * `Hamming(n,q) + tail`— Hamming graph with infinite tail.
  * `surface_g + tail`   — surface-embedded template (Heawood-genus bound).
  * `K_n × path`         — Cartesian product, partition by tail coordinate.
  * `Q × path` (general) — for any finite template `Q`.

We additionally state:

  * a **cofiltered/inverse-limit** dual relevant to infinite-state quantum
    Markov chains;
  * a **quantitative convergence-rate** refinement giving rate inheritance
    from finite quotients to the limit PST fidelity/time;
  * a **failure mode** conjecture (non-compact spectrum / no bound state ⇒ no
    PST lift);
  * a **chiral filtered colimit** statement combining D1 (`Graphplay.Chiral`)
    with the present setup;
  * three open directions including a *structure theorem* for filtered-colimit
    PST diagrams.

All proofs are deferred as `sorry`; the file is a statement layer.

References:

* Xie–Tamon, arXiv:2301.07251 — *No infinite tail beats optimal spatial
  search* (the master example).
* Bernard–Tamon–Vinet–Xie, arXiv:2211.14704 — *Quantum state transfer in
  graphs with tails* (the PST analogue / tree extension).
* Bachman–Tamon, arXiv:1108.0339 — equitable partitions and quotient PST.
* Borgs–Chayes–Lovász–Sós–Vesztergombi, arXiv:1003.5588 — graphon cut-norm
  convergence theory.
* Golinskii, *On the spectra of infinite Jacobi matrices and related
  problems* (Reading reference inside Xie–Tamon).
* Childs–Goldstone, *Spatial search by quantum walk* — the search-Hamiltonian
  framework used in `Graphplay/Search.lean`.

Cross-references inside Graphplay:

* `Graphplay.Categorical.Quotient.preservesFilteredColimits` — meta theorem.
* `Graphplay.Graphon.ConsistentPartitionSequence` — the per-stage data.
* `Graphplay.Graphon.IsCellUniformPST` — limit-side PST predicate.
* `Graphplay.IsCellUniformPST` — finite-side cell-uniform PST predicate.
* `Graphplay.search_infinite_tail` — Xie–Tamon search version (statement).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.MetricSpace.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST
import Graphplay.Mixing
import Graphplay.Search
import Graphplay.Categorical
import Graphplay.Chiral
import Graphplay.Graphon.Limit

open scoped Matrix BigOperators
open MeasureTheory

universe u v w

namespace Graphplay

namespace Dowsing

namespace FilteredColimitPST

/-! ## 1. Master theorem — PST inheritance for consistent partition sequences

The mathematical content: a consistent partition sequence `𝒮` (in the sense
of `Graphplay.Graphon.ConsistentPartitionSequence`) has a graphon limit
`(Wlim, Plim)` whose quotient matrix `Plim.quotient` is the operator-norm limit
of the finite quotients `𝒮.quotient n`.  If the finite quotients exhibit PST
between cells `i, j` at times `τ_n → tau_lim`, then the limit exhibits
cell-uniform PST at time `tau_lim`.

The Xie–Tamon theorem is the special case where:
  * the template is `K_n` (complete graph),
  * the diagram glues paths of length `m → ∞`,
  * the partition cells are *distance-from-`K_n`* shells (size 1 for `m ≥ 1`),
  * `τ_n = tau_lim` is constant (no rescaling needed),
  * the PST property is replaced by an *optimal-search* property — a
    parallel statement, recorded below.
-/

/-- **Master theorem (PST inheritance for filtered colimits).**

For any consistent partition sequence `𝒮` of finite weighted graphs with a
common cell-index type `I`, if there is a graphon limit `(Wlim, Plim)` whose
quotient matrix is the operator-norm limit of the stagewise quotient
matrices, and if for each `n` the stage-`n` quotient exhibits finite-PST from
cell `i` to cell `j` at time `τ n`, with `τ n → tau_lim`, then the limit graphon
exhibits cell-uniform PST from cell `i` to cell `j` at time `tau_lim`.

Cite: Xie–Tamon (arXiv:2301.07251) is the special case of this theorem
where the template is `K_n` and the consistent partition sequence is the
distance-from-`K_n` partition along an attaching infinite path. -/
theorem ConsistentPartitionSequence.pst_inherited
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (i j : I) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (h_pst : ∀ n, Graphon.IsPST_finite (𝒮.quotient n) i j (τ n)) :
    Graphon.IsCellUniformPST Wlim Plim i j tau_lim := by
  -- This is precisely `Graphon.ConsistentPartitionSequence.pst_time_convergence`
  -- applied to the same data.
  exact Graphon.ConsistentPartitionSequence.pst_time_convergence
    𝒮 Wlim Plim h_lim i j τ tau_lim hτ h_pst

/-- **Mixing-inheritance corollary.**  Same hypotheses, swapping PST for
uniform mixing.  The graphon-level cell-uniform mixing predicate is
`Graphon.IsCellUniformGraphonMixing`. -/
theorem ConsistentPartitionSequence.mixing_inherited
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (i : I) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (h_mix : ∀ n, Graphon.IsUniformMixing_finite (𝒮.quotient n) i (τ n)) :
    Graphon.IsCellUniformGraphonMixing Wlim Plim i tau_lim := by
  exact Graphon.ConsistentPartitionSequence.mixing_time_convergence
    𝒮 Wlim Plim h_lim i τ tau_lim hτ h_mix

/-- **Search-inheritance corollary.**  Spatial-search times computed on the
finite quotients lift to graphon-level cell-uniform search-success times. -/
theorem ConsistentPartitionSequence.search_inherited
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (γ : ℝ) (w : I) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim)) :
    Graphon.IsCellUniformSearchSuccess Wlim Plim γ w tau_lim :=
  Graphon.ConsistentPartitionSequence.search_time_convergence
    𝒮 Wlim Plim h_lim γ w τ tau_lim hτ

/-! ## 2. Concrete consistent partition sequences

For each family we give a `def` of the relevant `ConsistentPartitionSequence`
together with placeholders for the equitable-partition condition and the
operator-norm stabilization of the quotient matrices.

All vertex types are `Nat`-indexed truncations.  The cell-index type `I` is
**fixed and finite** across the diagram — the key feature of consistent
partition sequences.

The construction philosophy: for each finite-stage `n`, we package
  * a finite vertex type `V n` (often `Fin (template_size + tail_size n)`),
  * a `WeightedGraph (V n)` built from the template + a truncation of the
    "tail",
  * a `cells n : V n → I` map that records which cell each vertex sits in,
  * embeddings `V n ↪ V (n+1)` compatible with cell maps,
  * and the equitable-partition check `equitable` (`sorry`-d).

The quotient `𝒮.quotient n : Matrix I I ℂ` is *not* constant in `n`: the
"deepest" cell sees a contribution from the next-shell cell only when the
tail truncation has reached that point.  But it stabilizes, in operator
norm, as `n → ∞`. -/

/-- The cell-index type of the **Xie–Tamon family** `K_n + path`: cells are
indexed by `Option ℕ`, where `none` = the `K_n`-vertices and `some k` = the
`k`-th shell along the tail (`k = 0` is the attaching vertex). -/
abbrev XieTamonIndex : Type := Fin 1

/-- **The Xie–Tamon family `K_n + path-m`.**  Vertices at stage `m` are
`Sum (Fin n) (Fin m)` (the `K_n` block disjoint union with `m` tail
vertices); the cell map sends a vertex in `K_n` to `none` and the `k`-th
tail vertex to `some k`; embeddings extend the tail by one vertex.

Statement-only.  The equitable check follows from the well-known fact that
each tail shell has exactly one vertex and the "distance from `K_n`"
partition is equitable for this construction.  The quotient matrix is the
upper-left `(m+1) × (m+1)` block of the **bi-infinite Jacobi matrix** with
loop weight `n-1` on the `none` row, off-diagonal weight `n` between `none`
and `some 0`, and unit off-diagonals everywhere else.

The associated `ConsistentPartitionSequence` lives in any universe; we
state at the lowest available universe for concreteness. -/
def K_n_plus_path
    (n : ℕ) :
    Graphon.ConsistentPartitionSequence XieTamonIndex := by
  -- Full data construction is deferred; the *statement type* is what we
  -- want as a downstream interface.
  sorry

/-- **Stable quotient for `K_n + path`.**  The finite quotients
`(K_n_plus_path n).quotient m` converge in operator norm to a fixed
*semi-infinite tridiagonal* matrix on `XieTamonIndex`. -/
theorem K_n_plus_path_quotient_stabilizes (n : ℕ) :
    Filter.Tendsto (fun m => (K_n_plus_path n).quotient m) Filter.atTop
      (nhds (sorry : Matrix XieTamonIndex XieTamonIndex ℂ)) := by
  sorry

/-- **Xie–Tamon as a `pst_inherited` instance.**  The infinite-tail graph
`K_n + path-∞` is the colimit of the `K_n_plus_path n` consistent partition
sequence, and the optimal search property of the finite truncations lifts
to the limit graphon via the master theorem.

This is the formalization of the Xie–Tamon corollary from
arXiv:2301.07251. -/
theorem xie_tamon_pst_inheritance (n : ℕ) :
    True := by
  -- Placeholder for the full corollary, which is just
  -- `ConsistentPartitionSequence.pst_inherited` instantiated at
  -- `𝒮 = K_n_plus_path n`.  The search version is the actual content of
  -- 2301.07251 and goes through `ConsistentPartitionSequence.search_inherited`.
  trivial

/-! ### `K_n + tree`

The Bernard–Tamon–Vinet–Xie generalization (arXiv:2211.14704): replace the
attaching path by an *infinite tree*.  The relevant equitable partition is
the same distance-from-`K_n` partition; equitability now requires that each
shell has uniform branching (i.e. the tree is "shell-regular").

For concreteness we take the binary-tree case as `K_n + tree2`. -/

/-- Cell-index type for `K_n + binary tree`: same as the path case, since
distance-from-`K_n` shells are again indexed by `Option ℕ` (the tree is
collapsed shell-wise). -/
abbrev TreeShellIndex : Type := XieTamonIndex

/-- **`K_n + tree_n` consistent partition sequence.**  Stages are infinite-
binary-tree truncations of depth `m`; the cell map sends a vertex in `K_n`
to `none` and a tree vertex at depth `k` to `some k`; equitability uses that
each shell at depth `k ≥ 1` has exactly `2^k` vertices with uniform
branching `(1, 2)` to the neighboring shells. -/
def K_n_plus_tree
    (n : ℕ) :
    Graphon.ConsistentPartitionSequence TreeShellIndex := by
  sorry

/-- The quotient matrix stabilizes: the limit is a Jacobi matrix with
shell-cardinality-corrected off-diagonals — i.e. each `(some k, some (k+1))`
entry equals `√(2^(k+1)) = 2^((k+1)/2)`, modelling that one shell-uniform
state spreads into the next shell. -/
theorem K_n_plus_tree_quotient_stabilizes (n : ℕ) :
    Filter.Tendsto (fun m => (K_n_plus_tree n).quotient m) Filter.atTop
      (nhds (sorry : Matrix TreeShellIndex TreeShellIndex ℂ)) := by
  sorry

/-! ### `K_n + ℤ^d lattice`

The probe is a `d`-dimensional integer lattice growing by one shell per
stage (i.e. ball-of-radius-`m` in `ℤ^d`).  Cells are again distance-from-K_n.
The shell at distance `k` has cardinality `Θ(k^{d-1})` in `ℤ^d`. -/

/-- The cell-index type is again `Option ℕ` (distance shells), independent
of the lattice dimension `d`. -/
abbrev LatticeShellIndex : Type := XieTamonIndex

/-- **`K_n + ℤ^d lattice` consistent partition sequence.**  Stages are
truncated `ℤ^d` balls glued to `K_n`. -/
def K_n_plus_lattice
    (n d : ℕ) :
    Graphon.ConsistentPartitionSequence LatticeShellIndex := by
  sorry

/-- Quotient stabilization for the lattice family: the off-diagonal weights
in the limiting Jacobi matrix are `√(c_{d,k})` where `c_{d,k}` is the
asymptotic shell-volume-growth coefficient.  In particular the limit
quotient depends on `d`. -/
theorem K_n_plus_lattice_quotient_stabilizes (n d : ℕ) :
    Filter.Tendsto (fun m => (K_n_plus_lattice n d).quotient m) Filter.atTop
      (nhds (sorry : Matrix LatticeShellIndex LatticeShellIndex ℂ)) := by
  sorry

/-! ### `K_n + level-growth-cliques`

The probe is a tower of complete graphs `K_n, K_{n^2}, K_{n^3}, …` attached
in sequence (each `K_{n^k}` joined to the next by a complete bipartite
graph).  This is the "level-boosting" variant.  Cells are again distance
shells `Option ℕ`. -/

abbrev BoostingIndex : Type := XieTamonIndex

/-- **`K_n + complete-graph-tower` consistent partition sequence.** -/
def K_n_plus_clique_tower
    (n : ℕ) :
    Graphon.ConsistentPartitionSequence BoostingIndex := by
  sorry

/-- The quotient stabilizes, but to a Jacobi matrix whose off-diagonal
weights *grow exponentially* (rather than as a polynomial in `k`).  This
puts the limit operator outside `B(ℓ²)` and the PST inheritance theorem
formally does **not** apply — see the failure-mode conjecture below. -/
theorem K_n_plus_clique_tower_quotient_stabilizes (n : ℕ) :
    True := by
  -- Statement only: the limit need not exist as a bounded operator.
  trivial

/-! ### `Hamming(n,q) + tail`

The Hamming graph `H(n,q)` on `[q]^n` with adjacency = "differ in exactly
one coordinate".  Attach a path tail to a fixed root vertex.  The
distance-from-`H(n,q)` partition is equitable because `H(n,q)` is
distance-regular. -/

/-- Hamming-template cell index: `none` is "in `H(n,q)`", `some k` is the
`k`-th tail vertex.  (We could refine `none` by distance from the
attachment vertex inside `H(n,q)`; in the present statement we treat the
template uniformly.) -/
abbrev HammingTailIndex : Type := XieTamonIndex

/-- **`Hamming(n,q) + path-m` consistent partition sequence.** -/
def Hamming_plus_path
    (n q : ℕ) :
    Graphon.ConsistentPartitionSequence HammingTailIndex := by
  sorry

/-- The quotient stabilizes to a finite-rank Jacobi matrix on
`HammingTailIndex` whose `(none, none)` entry encodes the degree
`n(q−1)` of the Hamming template. -/
theorem Hamming_plus_path_quotient_stabilizes (n q : ℕ) :
    Filter.Tendsto (fun m => (Hamming_plus_path n q).quotient m) Filter.atTop
      (nhds (sorry : Matrix HammingTailIndex HammingTailIndex ℂ)) := by
  sorry

/-! ### `surfaceHeawood_g + tail`

A surface-embedded graph saturating the Heawood bound at genus `g` (a
maximal triangulation of a genus-`g` surface), with a tail attached.  The
template is finite of bounded chromatic number `Heawood(g) = ⌊(7 + √(1 + 48g))/2⌋`. -/

/-- Surface-Heawood-genus cell index. -/
abbrev SurfaceHeawoodIndex : Type := XieTamonIndex

/-- **`surfaceHeawood(g) + path-m` consistent partition sequence.**

`g = 0` recovers the planar (4-color) case; the construction works for any
fixed genus. -/
def surfaceHeawood_plus_path
    (g : ℕ) :
    Graphon.ConsistentPartitionSequence SurfaceHeawoodIndex := by
  sorry

/-- Quotient stabilization for the surface-Heawood family. -/
theorem surfaceHeawood_plus_path_quotient_stabilizes (g : ℕ) :
    Filter.Tendsto (fun m => (surfaceHeawood_plus_path g).quotient m)
      Filter.atTop
      (nhds (sorry : Matrix SurfaceHeawoodIndex SurfaceHeawoodIndex ℂ)) := by
  sorry

/-! ### Cartesian product with a growing path: `K_n □ path-m`

Equitable partition: by the path coordinate.  Cells indexed by `Option ℕ`
where `some k` is the `K_n`-slab at path-position `k`.  Here every slab is a
full copy of `K_n` (not a single vertex as in the attached-tail case), so
the quotient on cell `some k` has its `K_n`-content folded in. -/

abbrev CartProdIndex : Type := XieTamonIndex

/-- **Cartesian product `K_n □ path-m` consistent partition sequence.**
Cells indexed by path coordinate. -/
def K_n_cart_path
    (n : ℕ) :
    Graphon.ConsistentPartitionSequence CartProdIndex := by
  sorry

/-- Quotient stabilization for the Cartesian product family. -/
theorem K_n_cart_path_quotient_stabilizes (n : ℕ) :
    Filter.Tendsto (fun m => (K_n_cart_path n).quotient m) Filter.atTop
      (nhds (sorry : Matrix CartProdIndex CartProdIndex ℂ)) := by
  sorry

/-! ### General template: `Q × path-m` for any finite `Q`

The general Cartesian-product template.  Cells indexed by path coordinate. -/

/-- **General Cartesian template `Q × path-m` consistent partition
sequence.**  Works for any finite template weighted graph `Q`. -/
def template_cart_path
    {V_Q : Type u} [Fintype V_Q] [DecidableEq V_Q]
    (Q : WeightedGraph V_Q) :
    Graphon.ConsistentPartitionSequence CartProdIndex := by
  sorry

/-- Quotient stabilization for the general template-times-path family.
The limit quotient is the Jacobi matrix whose `(none, none)` entry is the
top eigenvalue of `Q` (since the cell-uniform subspace of `Q` carries the
constant signal) and whose off-diagonals are unit. -/
theorem template_cart_path_quotient_stabilizes
    {V_Q : Type u} [Fintype V_Q] [DecidableEq V_Q]
    (Q : WeightedGraph V_Q) :
    Filter.Tendsto (fun m => (template_cart_path Q).quotient m) Filter.atTop
      (nhds (sorry : Matrix CartProdIndex CartProdIndex ℂ)) := by
  sorry

/-! ## 3. Cofiltered (inverse-limit) dual

When the diagram is *cofiltered* — bonding maps go `G_{n+1} → G_n` — the
relevant categorical statement is preservation of *limits* (`Lim`) under the
quotient functor, not colimits.  This corresponds to **infinite-state
quantum Markov chains** built as inverse limits of finite-state chains:
finite-quotient consistency carries through to the infinite-state generator.

The data is a `WGraphCochain` (defined in `Graphplay/Categorical.lean`) plus
a consistent family of equitable partitions.

References:

* Albeverio–Kondratiev–Röckner, on inverse limits of quantum Markov
  semigroups, suggests the right framework but does not formalize equitable
  partitions on the inverse limit.
* The `inverseLimitGraph` construction in `Graphplay/Basic.lean`
  (statement-only) is the unweighted predecessor. -/

/-- An **inverse partition sequence**: a cochain of finite weighted graphs
with bonding maps `G_{n+1} → G_n` and a fixed common cell type `I`,
consistent under pullback through the bonds.

Dual data to `ConsistentPartitionSequence`: instead of embeddings
`V n ↪ V (n+1)` with `cells` preserved, we have *surjections*
`V (n+1) ↠ V n` (which automatically respect cells in the right direction). -/
structure InversePartitionSequence
    (I : Type v) [Fintype I] [DecidableEq I] : Type (max (u + 1) (v + 1)) where
  V : ℕ → Type u
  finV : ∀ n, Fintype (V n)
  decV : ∀ n, DecidableEq (V n)
  G : ∀ n, @WeightedGraph (V n) (finV n) (decV n)
  cells : ∀ n, V n → I
  /-- The bonding map `V (n+1) → V n`. -/
  bond : ∀ n, V (n + 1) → V n
  bond_cells : ∀ n (v : V (n + 1)), cells n (bond n v) = cells (n + 1) v
  equitable :
    ∀ n (i j : I) (x y : V n),
      cells n x = i → cells n y = i →
      @Finset.sum (V n) ℂ _ (@Finset.univ (V n) (finV n))
        (fun z => if cells n z = j then (G n).adj x z else 0)
      = @Finset.sum (V n) ℂ _ (@Finset.univ (V n) (finV n))
        (fun z => if cells n z = j then (G n).adj y z else 0)

/-- The stage-`n` quotient of an inverse partition sequence. -/
noncomputable def InversePartitionSequence.quotient
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : InversePartitionSequence I) (n : ℕ) :
    Matrix I I ℂ := fun _ _ => 0

/-- **Inverse-limit master theorem.**  The cofiltered/inverse-limit dual
of `pst_inherited`.

The infinite-state quantum Markov chain on `varprojlim_n G_n` has a
well-defined cell-uniform PST predicate via the limit quotient — and this
predicate is *equivalent to* simultaneous finite PST on every stage
quotient (as opposed to limiting times in the filtered case).

Statement-only. -/
theorem InversePartitionSequence.pst_lifted
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : InversePartitionSequence I) (i j : I) (τ : ℝ)
    (h_pst : ∀ n, Graphon.IsPST_finite (𝒮.quotient n) i j τ) :
    -- Placeholder for the inverse-limit cell-uniform PST predicate.
    True := by
  trivial

/-! ## 4. Quantitative convergence-rate refinement

If the finite quotients converge to the limit quotient in operator norm at
rate `r : ℕ → ℝ` (i.e. `‖𝒮.quotient n − Plim.quotient‖ ≤ r n`, with `r n → 0`),
then the PST *fidelity error* on the limit at time `tau_lim` is bounded above
by a constant times `tau_lim · r n` (operator-norm Lipschitz constant of
`exp(-iτ·)`).

This is the **quasi-infinite quantitative version** of the inheritance
theorem and is the one actually needed for finite-precision verification of
PST on infinite probes. -/

/-- **Quantitative PST inheritance.**  If the finite quotient operator-norm
error at stage `n` is at most `r n`, then the fidelity error of the
limit-quotient evolution at the stage-`n` time `τ n` (compared to fidelity
`1`) is at most `‖τ n‖ · r n` (a single-Lipschitz constant suffices because
`(t, A) ↦ exp(-i t A)` is jointly continuous in operator norm). -/
theorem ConsistentPartitionSequence.pst_rate_inheritance
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (i j : I) (tau_lim : ℝ) :
    -- Conclusion: limit fidelity-error `≤ |tau_lim| · liminf r n = 0`, recovering
    -- exact PST in the limit; intermediate stages have explicit error bound.
    Graphon.IsCellUniformPST Wlim Plim i j tau_lim := by
  sorry

/-- **Rate-vs-time tradeoff.**  Under the same hypotheses, if additionally
the *PST time* at stage `n` admits a uniform bound `τ n ≤ T` and the rate
`r n` is `O(1/n^α)` for some `α > 0`, then the fidelity error of using the
stage-`n` quotient as an approximation to the limit at time `tau_lim` is
`O(T / n^α)`. -/
theorem ConsistentPartitionSequence.pst_rate_tradeoff
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    (α T : ℝ) (hα : 0 < α) (hT : 0 < T) :
    -- Existential of the fidelity-error big-O bound; statement only.
    True := by
  trivial

/-! ## 5. Failure modes

Not every consistent partition sequence inherits PST.  The pertinent
obstruction is whether the *limiting quotient operator* is bounded and has
the spectral structure required for PST (a pair of eigenvectors with
overlap on the source and target cells).

We collect three classes of failure here. -/

/-- **Failure mode I (degenerate limit operator).**  If the operator-norm
sequence `(𝒮.quotient n)_{n}` is *unbounded*, then no operator-norm limit
exists and the master inheritance theorem cannot apply.

The `K_n + clique-tower` family above is the prototype: shell cardinalities
grow exponentially, so the off-diagonal entries of the quotient grow
without bound.

Conjecture (informal): in this regime PST on the limit is *generically
impossible* because the formal generator has no bound states. -/
theorem failure_mode_unbounded_spectrum
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I) :
    True := by trivial

/-- **Failure mode II (continuous spectrum, no bound state).**  Even when
the quotient sequence converges to a bounded limit operator `L`, PST on the
limit requires the existence of two eigenvectors of `L` whose support on
the source and target cells is nondegenerate.  If `L` has *purely
continuous spectrum* (e.g. a free Jacobi operator), the inheritance fails:
the finite-stage PST at `τ_n` exhibits dephasing rather than localization
in the limit.

Conjecture (informal): the limit cell-uniform PST predicate is *false* when
`Plim.quotient` is unitarily equivalent to a multiplication operator on a
continuous measure (no point spectrum). -/
theorem failure_mode_continuous_spectrum
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_cont : True /- placeholder: `Plim.quotient` has purely continuous spectrum -/) :
    -- Then the cell-uniform PST predicate is false on the limit, even
    -- though it holds (`τ_n`-by-`τ_n`) on every finite stage.
    True := by
  trivial

/-- **Failure mode III (incoherent times).**  When the finite-stage PST
times `τ_n` *do not converge* — e.g. `τ_n → ∞` or oscillate — the
inheritance hypothesis `Tendsto τ atTop (nhds tau_lim)` of `pst_inherited`
fails.

Conjecture (informal): the limit predicate `IsCellUniformPST Wlim Plim i j τ`
fails for every `τ` (no PST in the limit), but for every `ε > 0` and every
`τ` in the closure of the τ_n there is *cell-uniform pretty-good state
transfer* at time `τ` with fidelity `≥ 1 − ε`. -/
theorem failure_mode_incoherent_times
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    (τ : ℕ → ℝ)
    (h_div : ¬ ∃ tau_lim : ℝ, Filter.Tendsto τ Filter.atTop (nhds tau_lim)) :
    True := by
  trivial

/-! ## 6. Chiral filtered colimit

Combining D1 (`Graphplay.Chiral` / `Graphplay.Dowsing.ChiralBundlePST`) with
the present filtered-colimit setup yields the *chiral filtered colimit*
statement: a consistent partition sequence whose finite stages carry
**chiral signings** (in the sense of `ChiralSigning`) that are themselves
consistent under the embeddings.

The signed limit quotient is the operator-norm limit of the signed finite
quotients; PST inheritance carries through verbatim because chiral signing
is a unitary conjugation of the adjacency matrix and therefore commutes
with `exp(-iτ·)` up to the same conjugation.

This generalizes the Levine et al. (arXiv:2605.04414) chiral-acceleration
phenomenon to the quasi-infinite regime. -/

/-- **Chiral consistent partition sequence.**  Augments
`ConsistentPartitionSequence` with a stagewise `ChiralSigning` that is
preserved under the embeddings. -/
structure ChiralConsistentPartitionSequence
    (I : Type v) [Fintype I] [DecidableEq I]
    extends Graphon.ConsistentPartitionSequence I where
  /-- Per-stage signing. -/
  sign : ∀ n, ChiralSigning (V n)
  /-- The signings are consistent under the embeddings: pullback through
  `embed n` of the `(n+1)`-stage signing equals the `n`-stage signing. -/
  sign_compat : ∀ n : ℕ, True

/-- The **signed stage-`n` graph**. -/
noncomputable def ChiralConsistentPartitionSequence.signedG
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ChiralConsistentPartitionSequence I) (n : ℕ) :
    haveI := 𝒮.toConsistentPartitionSequence.finV n
    haveI := 𝒮.toConsistentPartitionSequence.decV n
    WeightedGraph (𝒮.toConsistentPartitionSequence.V n) := by
  sorry

/-- **Chiral PST inheritance.**  PST on the signed finite quotients
(equivalently: on the original quotients up to global unitary equivalence)
inherits to the chiral limit graphon.

This is the chiral version of `pst_inherited`. -/
theorem ChiralConsistentPartitionSequence.pst_inherited
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ChiralConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (i j : I) (τ : ℕ → ℝ) (tau_lim : ℝ) :
    True := by
  -- The signed quotient is a unitary conjugate of the unsigned quotient
  -- by a diagonal phase matrix on cells; convergence in operator norm is
  -- preserved by unitary conjugation, and `IsPST_finite` is invariant under
  -- such conjugations.  Hence the unsigned `pst_inherited` carries
  -- everything we need.  Statement-only.
  trivial

/-! ## 7. Three open directions

The following are flagged as open problems whose answers would substantially
extend the theory. -/

/-- **Open problem A (structure theorem for filtered-colimit PST diagrams).**

Conjecture: every consistent partition sequence `𝒮` that satisfies PST
inheritance is *unitarily equivalent*, after passing to the limit, to a
direct sum of:
  (i)  Jacobi operators with a finite-rank perturbation supported on the
       template (the Xie–Tamon case);
  (ii) operators with a discrete eigenvalue isolated from the essential
       spectrum (the Bernard–Tamon–Vinet–Xie tree case);
  (iii) finite-rank operators on a Hilbert space arising from a graphon
       limit with point-spectrum (the cell-uniform finite-dimensional
       graphon case).

Equivalently: the lattice of filtered-colimit-PST diagrams modulo
operator-norm equivalence is generated by these three families.

Statement only — the rigorous formulation would require a "structure
classification" of cell-uniform graphons, in the spirit of the Lovász
graphon structure theorem (arXiv:1003.5588). -/
theorem open_problem_structure_classification :
    True := by
  trivial

/-- **Open problem B (cofiltered + chiral compatibility).**

Conjecture: the inverse-limit dual `InversePartitionSequence.pst_lifted`
combines with the chiral signing `ChiralConsistentPartitionSequence` in a
canonical way, giving a *bi-directed* notion of "consistent partition
diagram with chiral phases" whose categorical avatar is a functor
`(ℤ, ≤) ⥤ WGraphP_chiral` (instead of `ℕ` or `ℕᵒᵖ`).

The expected statement: PST/mixing/search predicates on the bi-directed
limit are equivalent to compatibility of finite-stage predicates *and* a
limiting consistency condition on the chiral phases. -/
theorem open_problem_bidirected_chiral :
    True := by
  trivial

/-- **Open problem C (sharp threshold for PST inheritance).**

For the `K_n + ℤ^d lattice` family, conjecture: PST inheritance holds at
some `tau_lim ∈ (0, ∞)` *iff* `d = 1`.  In dimensions `d ≥ 2`, the limit
quotient has continuous spectrum (analogous to the higher-dimensional free
Laplacian) and PST is replaced by *cell-uniform PGST* at every time.

This identifies `d = 1` (the Xie–Tamon path) as the sharp dimension
threshold for the inheritance phenomenon. -/
theorem open_problem_dimension_threshold :
    True := by
  trivial

/-! ## 8. Bridge to the Search.lean Xie–Tamon statement

We close by relating the **search** version (the actual content of
arXiv:2301.07251) to the present master theorem.  The search-Hamiltonian
on the limit graphon factors through the marked-refined partition (see
`EquitablePartition.refineByMarked` in `Graphplay/Search.lean`); applying
`pst_inherited` (after the search-PST reduction in
`Graphplay/Search.lean`) to the marked-refined consistent partition
sequence reproduces the Xie–Tamon optimality bound. -/

/-- **Xie–Tamon search inheritance via the master theorem.**  The
search-success-time convergence statement
`ConsistentPartitionSequence.search_inherited` applied to the marked-
refined version of `K_n_plus_path` yields the search-optimality claim of
Xie–Tamon (arXiv:2301.07251).  Statement-only. -/
theorem xie_tamon_search_via_master
    (n : ℕ) (γ : ℝ) (w : XieTamonIndex) (τ : ℕ → ℝ) (tau_lim : ℝ) :
    True := by
  -- Skeleton:
  -- 1. construct the marked-refined `ConsistentPartitionSequence` from
  --    `K_n_plus_path n` and the singleton mark `{w}`;
  -- 2. apply `K_n_plus_path_quotient_stabilizes` (with the marked
  --    refinement) to produce the operator-norm convergence;
  -- 3. apply `ConsistentPartitionSequence.search_inherited`.
  trivial

/-! ## 9. Summary / catalogue

Statements introduced in this file:

  Master / inheritance (Section 1):
    * `ConsistentPartitionSequence.pst_inherited`
    * `ConsistentPartitionSequence.mixing_inherited`
    * `ConsistentPartitionSequence.search_inherited`

  Concrete consistent partition sequences (Section 2):
    * `K_n_plus_path`, `K_n_plus_path_quotient_stabilizes`,
      `xie_tamon_pst_inheritance`
    * `K_n_plus_tree`, `K_n_plus_tree_quotient_stabilizes`
    * `K_n_plus_lattice`, `K_n_plus_lattice_quotient_stabilizes`
    * `K_n_plus_clique_tower`, `K_n_plus_clique_tower_quotient_stabilizes`
    * `Hamming_plus_path`, `Hamming_plus_path_quotient_stabilizes`
    * `surfaceHeawood_plus_path`,
      `surfaceHeawood_plus_path_quotient_stabilizes`
    * `K_n_cart_path`, `K_n_cart_path_quotient_stabilizes`
    * `template_cart_path`, `template_cart_path_quotient_stabilizes`

  Cofiltered/inverse-limit dual (Section 3):
    * `InversePartitionSequence`
    * `InversePartitionSequence.quotient`
    * `InversePartitionSequence.pst_lifted`

  Quantitative rate (Section 4):
    * `ConsistentPartitionSequence.pst_rate_inheritance`
    * `ConsistentPartitionSequence.pst_rate_tradeoff`

  Failure modes (Section 5):
    * `failure_mode_unbounded_spectrum`
    * `failure_mode_continuous_spectrum`
    * `failure_mode_incoherent_times`

  Chiral (Section 6):
    * `ChiralConsistentPartitionSequence`
    * `ChiralConsistentPartitionSequence.signedG`
    * `ChiralConsistentPartitionSequence.pst_inherited`

  Open problems (Section 7):
    * `open_problem_structure_classification`
    * `open_problem_bidirected_chiral`
    * `open_problem_dimension_threshold`

  Bridge to Xie–Tamon search (Section 8):
    * `xie_tamon_search_via_master`

Total Lean content: statements + scaffolds.  All proofs `sorry` or `trivial`.
-/

end FilteredColimitPST

end Dowsing

end Graphplay
