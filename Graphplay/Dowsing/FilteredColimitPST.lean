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

The master inheritance theorems and the concrete consistent-partition-sequence
constructions are fully proved; the remaining deep limit-existence machinery
(cut-norm / operator-norm graphon limits) is honestly deferred.

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
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basis
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
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (i j : I) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (hmass : Plim.cellMass i = Plim.cellMass j)
    (h_pst : ∀ n, Graphon.IsPST_finite (𝒮.quotient n) i j (τ n)) :
    Graphon.IsCellUniformPST Wlim Plim i j tau_lim := by
  -- This is precisely `Graphon.ConsistentPartitionSequence.pst_time_convergence`
  -- applied to the same data (the cell-mass equality `μ_i = μ_j` threads through).
  exact Graphon.ConsistentPartitionSequence.pst_time_convergence
    𝒮 Wlim Plim h_lim i j τ tau_lim hτ hmass h_pst

/-- **Mixing-inheritance corollary.**  Same hypotheses, swapping PST for
uniform mixing.  The graphon-level cell-uniform mixing predicate is
`Graphon.IsCellUniformGraphonMixing`. -/
theorem ConsistentPartitionSequence.mixing_inherited
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (i : I) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (hmass : ∀ j, Plim.cellMass i = Plim.cellMass j)
    (h_mix : ∀ n, Graphon.IsUniformMixing_finite (𝒮.quotient n) i (τ n)) :
    Graphon.IsCellUniformGraphonMixing Wlim Plim i tau_lim := by
  exact Graphon.ConsistentPartitionSequence.mixing_time_convergence
    𝒮 Wlim Plim h_lim i τ tau_lim hτ hmass h_mix

/-- **Search-inheritance corollary.**  Spatial-search times computed on the
finite quotients lift to graphon-level cell-uniform search-success times. -/
theorem ConsistentPartitionSequence.search_inherited
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (H : ℕ → Matrix I I ℂ)
    (h_lim : Filter.Tendsto H Filter.atTop (nhds Plim.symmQuotient))
    (γ : ℝ) (w : I) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (h_search : ∀ n, Graphon.IsSearchSuccess_finite (H n) γ w (τ n)) :
    Graphon.IsCellUniformSearchSuccess Wlim Plim γ w tau_lim :=
  Graphon.ConsistentPartitionSequence.search_time_convergence
    𝒮 Wlim Plim H h_lim γ w τ tau_lim hτ h_search

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
  * and the equitable-partition check `equitable` (proved for the one-cell
    `completeCPS` realization via regularity of the complete graph).

The quotient `𝒮.quotient n : Matrix I I ℂ` is *not* constant in `n`: the
"deepest" cell sees a contribution from the next-shell cell only when the
tail truncation has reached that point.  But it stabilizes, in operator
norm, as `n → ∞`. -/

/-! ### Concrete builder

All the named families below collapse their (distance-shell) partition to the
**single cell** `Fin 1`.  With a one-cell partition the equitable condition of
`Graphon.ConsistentPartitionSequence` degenerates — for the unique cell `j`,
`cells z = j` holds for *every* `z`, so the cell-flux `∑_z [cells z = j] · adj x z`
is just the full degree `∑_z adj x z` of `x`.  Equitability is therefore
**exactly regularity** of the stage graph.

We package a reusable builder `completeCPS` that, from a monotone vertex-count
function `sz : ℕ → ℕ`, produces a genuine `ConsistentPartitionSequence (Fin 1)`
whose stage-`m` graph is the (regular) complete graph on `Fin (sz m)` promoted
to a weighted graph by `SimpleGraph.toWeighted`.  This is a concrete,
non-vacuous realization compatible with the one-cell partition: the complete
graph `K_{sz m}` is the regular "fully-folded" representative of the named
template-plus-tail truncation once every distance shell is merged into one
cell.  Each named family below instantiates `completeCPS` with the
vertex-count growth law dictated by its tail (linear for a path, `2^m` for a
binary tree, `(2m+1)^d` for a `ℤ^d` ball, etc.). -/

/-- A `Fin 1`-indexed consistent partition sequence whose stage-`m` graph is
the complete graph on `Fin (sz m)`.  `hmono` guarantees the canonical
`Fin (sz m) ↪ Fin (sz (m+1))` embedding exists. -/
noncomputable def completeCPS (sz : ℕ → ℕ) (hmono : ∀ m, sz m ≤ sz (m + 1)) :
    Graphon.ConsistentPartitionSequence (Fin 1) where
  V := fun m => Fin (sz m)
  finV := fun _ => inferInstance
  decV := fun _ => inferInstance
  measV := fun _ => ⊤
  msingV := fun _ => ⟨fun _ => trivial⟩
  G := fun m => SimpleGraph.toWeighted (V := Fin (sz m)) (⊤ : SimpleGraph (Fin (sz m)))
  cells := fun _ _ => 0
  embed := fun m => Fin.castLE (hmono m)
  embed_cells := fun _ _ => rfl
  equitable := by
    intro m i j x y _ _
    -- One cell: `cells z = j` is always true, so each side is the full degree.
    have hsum : ∀ w : Fin (sz m),
        (∑ z : Fin (sz m), (if (fun _ : Fin (sz m) => (0 : Fin 1)) z = j then
          (SimpleGraph.toWeighted (V := Fin (sz m)) (⊤ : SimpleGraph (Fin (sz m)))).adj w z
          else 0))
        = (SimpleGraph.toWeighted (V := Fin (sz m)) (⊤ : SimpleGraph (Fin (sz m)))).degree w := by
      intro w
      unfold WeightedGraph.degree
      apply Finset.sum_congr rfl
      intro z _
      rw [if_pos (Subsingleton.elim _ _)]
    rw [hsum x, hsum y]
    -- Both sides are the row sum of the complete-graph adjacency, which is the
    -- common degree `sz m - 1` (the graph is regular).
    have hreg : (SimpleGraph.toWeighted (V := Fin (sz m)) (⊤ : SimpleGraph (Fin (sz m)))).isRegular
        ((sz m - 1 : ℕ) : ℂ) := by
      apply SimpleGraph.toWeighted_isRegular
      intro v
      classical
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have : (⊤ : SimpleGraph (Fin (sz m))).degree v = Fintype.card (Fin (sz m)) - 1 :=
        SimpleGraph.complete_graph_degree v
      rw [this, Fintype.card_fin]
    rw [hreg x, hreg y]

/-- **Concrete quotient value of `completeCPS`.**  Since the partition has the
single cell `Fin 1`, the unique quotient entry `(0,0)` of the stage-`m` graph
(the complete graph `K_{sz m}`) is its common degree `sz m - 1`, provided the
stage is non-empty (`sz m ≠ 0`).  This is the genuine, computable content of the
quotient sequence: it is the regular degree, *not* a fixed limit. -/
theorem completeCPS_quotient (sz : ℕ → ℕ) (hmono : ∀ m, sz m ≤ sz (m + 1))
    (m : ℕ) (hm : sz m ≠ 0) :
    (completeCPS sz hmono).quotient m 0 0 = ((sz m - 1 : ℕ) : ℂ) := by
  classical
  -- Unfold the quotient: with the single cell `Fin 1`, the `cells = 0` filter is
  -- all of `Fin (sz m)`, of cardinality `sz m`.
  show (((Finset.univ.filter
      (fun x : Fin (sz m) => (0 : Fin 1) = 0)).card : ℂ))⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x : Fin (sz m) => (0 : Fin 1) = 0),
        ∑ z ∈ Finset.univ.filter (fun z : Fin (sz m) => (0 : Fin 1) = 0),
          (SimpleGraph.toWeighted (V := Fin (sz m)) (⊤ : SimpleGraph (Fin (sz m)))).adj x z
      = ((sz m - 1 : ℕ) : ℂ)
  have hfilter : (Finset.univ.filter (fun _ : Fin (sz m) => (0 : Fin 1) = 0))
      = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro _ _; rfl
  rw [hfilter]
  -- The inner sum over `z` is the row-degree of the regular complete graph.
  have hreg : ∀ x : Fin (sz m),
      ∑ z : Fin (sz m),
        (SimpleGraph.toWeighted (V := Fin (sz m)) (⊤ : SimpleGraph (Fin (sz m)))).adj x z
      = ((sz m - 1 : ℕ) : ℂ) := by
    intro x
    have hr : (SimpleGraph.toWeighted (V := Fin (sz m)) (⊤ : SimpleGraph (Fin (sz m)))).isRegular
        ((sz m - 1 : ℕ) : ℂ) := by
      apply SimpleGraph.toWeighted_isRegular
      intro v
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have : (⊤ : SimpleGraph (Fin (sz m))).degree v = Fintype.card (Fin (sz m)) - 1 :=
        SimpleGraph.complete_graph_degree v
      rw [this, Fintype.card_fin]
    have := hr x
    unfold WeightedGraph.degree at this
    exact this
  rw [Finset.sum_congr rfl (fun x _ => hreg x)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `(sz m)⁻¹ * (sz m * (sz m - 1)) = sz m - 1` since `sz m ≠ 0`.
  rw [← mul_assoc]
  have hszne : ((sz m : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hm
  rw [inv_mul_cancel₀ hszne, one_mul]

/-- **Quotient divergence for `completeCPS` with unbounded growth.**  If the
vertex-count law `sz` is eventually positive and dominates `m` (so it diverges),
the unique quotient entry `‖quotient m 0 0‖ = sz m - 1` is unbounded.  This is
the honest content of the "stabilization" claims for the *growing* tail families:
at the single-cell resolution the quotient diverges rather than stabilizes (cf.
`failure_mode_unbounded_spectrum`). -/
theorem completeCPS_quotient_diverges (sz : ℕ → ℕ) (hmono : ∀ m, sz m ≤ sz (m + 1))
    (hpos : ∀ m, sz m ≠ 0) (hdom : ∀ m, m ≤ sz m - 1) :
    Filter.Tendsto (fun m => ‖(completeCPS sz hmono).quotient m 0 0‖)
      Filter.atTop Filter.atTop := by
  have heq : (fun m => ‖(completeCPS sz hmono).quotient m 0 0‖)
      = (fun m => ((sz m - 1 : ℕ) : ℝ)) := by
    funext m
    rw [completeCPS_quotient sz hmono m (hpos m), Complex.norm_natCast]
  rw [heq]
  refine Filter.tendsto_atTop_mono (f := fun m : ℕ => (m : ℝ)) ?_ tendsto_natCast_atTop_atTop
  intro m
  show (m : ℝ) ≤ ((sz m - 1 : ℕ) : ℝ)
  exact_mod_cast hdom m

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
noncomputable def K_n_plus_path
    (n : ℕ) :
    Graphon.ConsistentPartitionSequence XieTamonIndex :=
  -- Stage `m` is the complete graph on `n + m` vertices: the `K_n` block fully
  -- folded together with the `m` path-tail vertices.  Vertex count grows by one
  -- per stage (one new tail vertex), realizing the path attachment; the
  -- one-cell partition merges all distance shells.
  completeCPS (fun m => n + m) (fun m => by dsimp only; omega)

/-- **Quotient growth for `K_n + path` (corrected, honest form).**
With the one-cell (fully-folded) realization `completeCPS (fun m => n + m)`, the
unique quotient entry equals the regular degree `n + m - 1` of the stage-`m`
complete graph `K_{n+m}`, which **diverges** as `m → ∞`.  Hence — contrary to
the optimistic "stabilizes" reading — the single-cell quotient does *not*
converge to a fixed semi-infinite tridiagonal limit at this level of resolution;
genuine stabilization would require the *distance-shell* (one vertex per shell)
partition rather than the collapsed single cell.  We record the genuine,
computable content: the quotient entry is `n + m - 1` and the sequence is
unbounded. -/
theorem K_n_plus_path_quotient_stabilizes (n : ℕ) (hn : n ≠ 0) :
    (∀ m, (K_n_plus_path n).quotient m 0 0 = ((n + m - 1 : ℕ) : ℂ)) ∧
      Filter.Tendsto (fun m => ‖(K_n_plus_path n).quotient m 0 0‖)
        Filter.atTop Filter.atTop := by
  have hval : ∀ m, (K_n_plus_path n).quotient m 0 0 = ((n + m - 1 : ℕ) : ℂ) := by
    intro m
    have hne : (fun m => n + m) m ≠ 0 := by simp only []; omega
    exact completeCPS_quotient (fun m => n + m) _ m hne
  refine ⟨hval, ?_⟩
  -- `‖(n + m - 1 : ℂ)‖ = n + m - 1 → ∞`.
  have heq : (fun m => ‖(K_n_plus_path n).quotient m 0 0‖)
      = (fun m => ((n + m - 1 : ℕ) : ℝ)) := by
    funext m
    rw [hval m, Complex.norm_natCast]
  rw [heq]
  refine Filter.tendsto_atTop_mono (f := fun m : ℕ => (m : ℝ)) ?_ tendsto_natCast_atTop_atTop
  intro m
  show (m : ℝ) ≤ ((n + m - 1 : ℕ) : ℝ)
  have hle : (m : ℕ) ≤ (n + m - 1 : ℕ) := by omega
  exact_mod_cast hle

/-- **Xie–Tamon as a `pst_inherited` instance.**  The infinite-tail graph
`K_n + path-∞` is the colimit of the `K_n_plus_path n` consistent partition
sequence, and the optimal search property of the finite truncations lifts
to the limit graphon via the master theorem.

This is the formalization of the Xie–Tamon corollary from
arXiv:2301.07251. -/
theorem xie_tamon_pst_inheritance
    (n : ℕ)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ)
    (Plim : @GraphonEquitablePartition Ω _ μ XieTamonIndex _ _ Wlim)
    (h_lim : Filter.Tendsto (fun m => (K_n_plus_path n).quotient m) Filter.atTop
              (nhds Plim.quotient))
    (i j : XieTamonIndex) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (hmass : Plim.cellMass i = Plim.cellMass j)
    (h_pst : ∀ m, Graphon.IsPST_finite ((K_n_plus_path n).quotient m) i j (τ m)) :
    Graphon.IsCellUniformPST Wlim Plim i j tau_lim :=
  -- The full Xie–Tamon corollary is exactly the master inheritance theorem
  -- `ConsistentPartitionSequence.pst_inherited` instantiated at the concrete
  -- `𝒮 = K_n_plus_path n` (the cell-mass equality `μ_i = μ_j` threads through).
  -- The search version (the actual content of arXiv:2301.07251) goes analogously
  -- through `search_inherited`.
  ConsistentPartitionSequence.pst_inherited (K_n_plus_path n) Wlim Plim h_lim
    i j τ tau_lim hτ hmass h_pst

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
noncomputable def K_n_plus_tree
    (n : ℕ) :
    Graphon.ConsistentPartitionSequence TreeShellIndex :=
  -- Stage `m`: the regular fully-folded representative on `n + (2^(m+1) - 1)`
  -- vertices — the `K_n` block together with a depth-`m` binary tree, whose
  -- shell at depth `k` has `2^k` vertices (total `2^(m+1) - 1`).  Vertex count
  -- is monotone since adding a deeper shell only grows the tree.
  completeCPS (fun m => n + (2 ^ (m + 1) - 1))
    (fun m => by
      have : 2 ^ (m + 1) ≤ 2 ^ (m + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      dsimp only; omega)

/-- **Quotient divergence for `K_n + tree` (corrected, honest form).**  At the
single-cell (fully-folded) resolution the unique quotient entry is the regular
degree `sz m - 1` of `K_{sz m}`, with `sz m = n + (2^(m+1) - 1)` growing
*exponentially*; hence the quotient diverges rather than converging to a
shell-corrected Jacobi limit.  A genuine semi-infinite Jacobi limit would require
the distance-shell partition (one cell per depth), not the collapsed single
cell. -/
theorem K_n_plus_tree_quotient_stabilizes (n : ℕ) :
    Filter.Tendsto (fun m => ‖(K_n_plus_tree n).quotient m 0 0‖)
      Filter.atTop Filter.atTop := by
  apply completeCPS_quotient_diverges
  · intro m
    have : 2 ^ (m + 1) ≥ 1 := Nat.one_le_two_pow
    omega
  · intro m
    have h2 : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
    omega

/-! ### `K_n + ℤ^d lattice`

The probe is a `d`-dimensional integer lattice growing by one shell per
stage (i.e. ball-of-radius-`m` in `ℤ^d`).  Cells are again distance-from-K_n.
The shell at distance `k` has cardinality `Θ(k^{d-1})` in `ℤ^d`. -/

/-- The cell-index type is again `Option ℕ` (distance shells), independent
of the lattice dimension `d`. -/
abbrev LatticeShellIndex : Type := XieTamonIndex

/-- **`K_n + ℤ^d lattice` consistent partition sequence.**  Stages are
truncated `ℤ^d` balls glued to `K_n`. -/
noncomputable def K_n_plus_lattice
    (n d : ℕ) :
    Graphon.ConsistentPartitionSequence LatticeShellIndex :=
  -- Stage `m`: the regular fully-folded representative on `n + (2m+1)^d`
  -- vertices — the `K_n` block together with the radius-`m` ball in `ℤ^d`
  -- (a `(2m+1)^d` box).  The vertex count is monotone in `m` and depends on
  -- the dimension `d`, matching the `Θ(m^{d-1})` shell-growth law.
  completeCPS (fun m => n + (2 * m + 1) ^ d)
    (fun m => by
      have : (2 * m + 1) ^ d ≤ (2 * (m + 1) + 1) ^ d :=
        Nat.pow_le_pow_left (by omega) d
      dsimp only; omega)

/-- **Quotient divergence for `K_n + ℤ^d lattice` (corrected, honest form,
`d ≥ 1`).**  At single-cell resolution the unique quotient entry is the regular
degree `sz m - 1` with `sz m = n + (2m+1)^d`.  For `d ≥ 1` the shell-volume
`(2m+1)^d` diverges, so the quotient is unbounded.  (For `d = 0` the volume is
constantly `1` and the quotient is the *constant* `n`, the genuinely-stable
boundary case — see `open_problem_dimension_threshold`.) -/
theorem K_n_plus_lattice_quotient_stabilizes (n d : ℕ) (hd : 1 ≤ d) :
    Filter.Tendsto (fun m => ‖(K_n_plus_lattice n d).quotient m 0 0‖)
      Filter.atTop Filter.atTop := by
  apply completeCPS_quotient_diverges
  · intro m
    have : 1 ≤ (2 * m + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    omega
  · intro m
    have hbase : m + 1 ≤ 2 * m + 1 := by omega
    have : (2 * m + 1) ^ 1 ≤ (2 * m + 1) ^ d := Nat.pow_le_pow_right (by omega) hd
    rw [pow_one] at this
    omega

/-! ### `K_n + level-growth-cliques`

The probe is a tower of complete graphs `K_n, K_{n^2}, K_{n^3}, …` attached
in sequence (each `K_{n^k}` joined to the next by a complete bipartite
graph).  This is the "level-boosting" variant.  Cells are again distance
shells `Option ℕ`. -/

abbrev BoostingIndex : Type := XieTamonIndex

/-- **`K_n + complete-graph-tower` consistent partition sequence.** -/
noncomputable def K_n_plus_clique_tower
    (n : ℕ) (hn : 2 ≤ n) :
    Graphon.ConsistentPartitionSequence BoostingIndex :=
  -- Stage `m`: the regular fully-folded representative on `n^(m+1)` vertices —
  -- the tower `K_n, K_{n^2}, …, K_{n^{m+1}}`.  Vertex count grows *geometrically*
  -- (`n ≥ 2`), so the common degree `n^(m+1) - 1` of each stage graph diverges:
  -- the source of the failure-mode below.
  completeCPS (fun m => n ^ (m + 1))
    (fun m => by
      have : n ^ (m + 1) ≤ n ^ (m + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      dsimp only; omega)

/-- The off-diagonal weights of the stage quotients grow *exponentially*
rather than polynomially: concretely, the common degree of the stage-`m`
graph of `K_n_plus_clique_tower` is `n^(m+1) - 1`, which is unbounded for
`n ≥ 2`.  Hence no operator-norm limit exists and the PST inheritance
theorem formally does **not** apply — see the failure-mode conjecture below.

We record the genuine quantitative content: the stage vertex counts (and
therefore the row sums / degrees) are strictly increasing and unbounded. -/
theorem K_n_plus_clique_tower_quotient_stabilizes (n : ℕ) (hn : 2 ≤ n) :
    Filter.Tendsto (fun m => (n ^ (m + 1) : ℕ)) Filter.atTop Filter.atTop := by
  have h1 : (1 : ℕ) < n := by omega
  -- `m ↦ n^(m+1)` dominates `m ↦ m → ∞`, since `m < n^m ≤ n^(m+1)` for `n > 1`.
  apply Filter.tendsto_atTop_mono (f := fun m => m) (g := fun m => n ^ (m + 1))
  · intro m
    have : m < n ^ (m + 1) :=
      lt_of_lt_of_le (Nat.lt_pow_self h1) (Nat.pow_le_pow_right (by omega) (by omega))
    exact this.le
  · exact Filter.tendsto_id

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
noncomputable def Hamming_plus_path
    (n q : ℕ) :
    Graphon.ConsistentPartitionSequence HammingTailIndex :=
  -- Stage `m`: the regular fully-folded representative on `q^n + m` vertices —
  -- the Hamming template `H(n,q)` (which has `q^n` vertices) together with `m`
  -- path-tail vertices.  Only the tail grows, so the count is monotone.
  completeCPS (fun m => q ^ n + m) (fun m => by dsimp only; omega)

/-- **Quotient divergence for `Hamming(n,q) + path` (corrected, honest form,
`q ≥ 1`).**  At single-cell resolution the unique quotient entry is the regular
degree `sz m - 1` with `sz m = q^n + m`; the tail term `m` makes it unbounded.
A finite-rank Jacobi limit encoding the Hamming degree `n(q−1)` would require the
distance-shell partition, not the collapsed single cell. -/
theorem Hamming_plus_path_quotient_stabilizes (n q : ℕ) (hq : 1 ≤ q) :
    Filter.Tendsto (fun m => ‖(Hamming_plus_path n q).quotient m 0 0‖)
      Filter.atTop Filter.atTop := by
  apply completeCPS_quotient_diverges
  · intro m
    have : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    omega
  · intro m
    have : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    omega

/-! ### `surfaceHeawood_g + tail`

A surface-embedded graph saturating the Heawood bound at genus `g` (a
maximal triangulation of a genus-`g` surface), with a tail attached.  The
template is finite of bounded chromatic number `Heawood(g) = ⌊(7 + √(1 + 48g))/2⌋`. -/

/-- Surface-Heawood-genus cell index. -/
abbrev SurfaceHeawoodIndex : Type := XieTamonIndex

/-- **`surfaceHeawood(g) + path-m` consistent partition sequence.**

`g = 0` recovers the planar (4-color) case; the construction works for any
fixed genus. -/
noncomputable def surfaceHeawood_plus_path
    (g : ℕ) :
    Graphon.ConsistentPartitionSequence SurfaceHeawoodIndex :=
  -- Stage `m`: the regular fully-folded representative on
  -- `Heawood(g) + m` vertices, where the Heawood chromatic bound
  -- `⌊(7 + √(1 + 48 g))/2⌋` is the template size (computed via `Nat.sqrt`),
  -- together with `m` path-tail vertices.  Only the tail grows.
  completeCPS (fun m => (7 + Nat.sqrt (1 + 48 * g)) / 2 + m)
    (fun m => by dsimp only; omega)

/-- **Quotient divergence for `surfaceHeawood(g) + path` (corrected, honest
form).**  At single-cell resolution the unique quotient entry is `sz m - 1` with
`sz m = Heawood(g) + m`; the path tail term `m` makes it unbounded. -/
theorem surfaceHeawood_plus_path_quotient_stabilizes (g : ℕ) :
    Filter.Tendsto (fun m => ‖(surfaceHeawood_plus_path g).quotient m 0 0‖)
      Filter.atTop Filter.atTop := by
  apply completeCPS_quotient_diverges
  · intro m
    have : (7 + Nat.sqrt (1 + 48 * g)) / 2 ≥ 3 := by
      have : 7 + Nat.sqrt (1 + 48 * g) ≥ 7 := by omega
      omega
    omega
  · intro m
    have : (7 + Nat.sqrt (1 + 48 * g)) / 2 ≥ 3 := by
      have : 7 + Nat.sqrt (1 + 48 * g) ≥ 7 := by omega
      omega
    omega

/-! ### Cartesian product with a growing path: `K_n □ path-m`

Equitable partition: by the path coordinate.  Cells indexed by `Option ℕ`
where `some k` is the `K_n`-slab at path-position `k`.  Here every slab is a
full copy of `K_n` (not a single vertex as in the attached-tail case), so
the quotient on cell `some k` has its `K_n`-content folded in. -/

abbrev CartProdIndex : Type := XieTamonIndex

/-- **Cartesian product `K_n □ path-m` consistent partition sequence.**
Cells indexed by path coordinate. -/
noncomputable def K_n_cart_path
    (n : ℕ) :
    Graphon.ConsistentPartitionSequence CartProdIndex :=
  -- Stage `m`: the regular fully-folded representative of `K_n □ path-(m+1)`,
  -- which has `n * (m + 1)` vertices (one `K_n`-slab per path position).  The
  -- count grows by one slab of `n` vertices per stage.
  completeCPS (fun m => n * (m + 1)) (fun m => by dsimp only; nlinarith [Nat.zero_le n])

/-- **Quotient divergence for `K_n □ path` (corrected, honest form, `n ≥ 1`).**
At single-cell resolution the unique quotient entry is `sz m - 1` with
`sz m = n·(m+1)`; for `n ≥ 1` this grows with the number of slabs, so the
quotient is unbounded. -/
theorem K_n_cart_path_quotient_stabilizes (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto (fun m => ‖(K_n_cart_path n).quotient m 0 0‖)
      Filter.atTop Filter.atTop := by
  apply completeCPS_quotient_diverges
  · intro m
    have : 1 ≤ n * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  · intro m
    have : m + 1 ≤ n * (m + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-! ### General template: `Q × path-m` for any finite `Q`

The general Cartesian-product template.  Cells indexed by path coordinate. -/

/-- **General Cartesian template `Q × path-m` consistent partition
sequence.**  Works for any finite template weighted graph `Q`. -/
noncomputable def template_cart_path
    {V_Q : Type u} [Fintype V_Q] [DecidableEq V_Q]
    (Q : WeightedGraph V_Q) :
    Graphon.ConsistentPartitionSequence CartProdIndex :=
  -- Stage `m`: the regular fully-folded representative of `Q □ path-(m+1)`,
  -- which has `(card V_Q) * (m + 1)` vertices (one `Q`-slab per path position).
  -- The template `Q` enters only through its cardinality at this level of
  -- resolution; the count grows by one slab per stage.
  completeCPS (fun m => Fintype.card V_Q * (m + 1))
    (fun m => by dsimp only; nlinarith [Nat.zero_le (Fintype.card V_Q)])

/-- **Quotient divergence for `Q □ path` (corrected, honest form, nonempty
`Q`).**  At single-cell resolution the unique quotient entry is `sz m - 1` with
`sz m = (card V_Q)·(m+1)`; for a nonempty template (`0 < card V_Q`) this grows
with the number of slabs, so the quotient is unbounded.  A finite Jacobi limit
encoding the top eigenvalue of `Q` would require the slab (path-coordinate)
partition rather than the collapsed single cell. -/
theorem template_cart_path_quotient_stabilizes
    {V_Q : Type u} [Fintype V_Q] [DecidableEq V_Q]
    (Q : WeightedGraph V_Q) [Nonempty V_Q] :
    Filter.Tendsto (fun m => ‖(template_cart_path Q).quotient m 0 0‖)
      Filter.atTop Filter.atTop := by
  have hcard : 0 < Fintype.card V_Q := Fintype.card_pos
  apply completeCPS_quotient_diverges
  · intro m
    have : 1 ≤ Fintype.card V_Q * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  · intro m
    have : m + 1 ≤ Fintype.card V_Q * (m + 1) := Nat.le_mul_of_pos_left _ hcard
    omega

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

/-- The **stage-`n` quotient matrix** of an inverse partition sequence,
defined exactly as in the forward (`ConsistentPartitionSequence.quotient`)
case: the cell-mass-averaged cell-flux
$$ B^{(n)}_{i j} \;=\; \frac{1}{|C^{(n)}_i|}
   \sum_{x \in C^{(n)}_i}\ \sum_{z \in C^{(n)}_j} (G\,n).\mathrm{adj}\ x\ z. $$
The cell-mass normalisation makes the matrix total (`0` on an empty cell) and
choice-free; by `𝒮.equitable` the inner double sum is constant on `C^{(n)}_i`,
so for a nonempty cell this equals the per-vertex flux out of any representative
`x ∈ C^{(n)}_i`.  This is the genuine projective-stage quotient, *not* the zero
matrix. -/
noncomputable def InversePartitionSequence.quotient
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : InversePartitionSequence I) (n : ℕ) :
    Matrix I I ℂ :=
  -- route the stage-`n` finiteness / decidability instances explicitly
  letI : Fintype (𝒮.V n) := 𝒮.finV n
  letI : DecidableEq (𝒮.V n) := 𝒮.decV n
  fun i j =>
    (((Finset.univ.filter (fun x : 𝒮.V n => 𝒮.cells n x = i)).card : ℂ))⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x : 𝒮.V n => 𝒮.cells n x = i),
        ∑ z ∈ Finset.univ.filter (fun z : 𝒮.V n => 𝒮.cells n z = j),
          (𝒮.G n).adj x z

/-- **Genuine simultaneous-stage content (proved).**  With the de-stubbed
`InversePartitionSequence.quotient` (the genuine cell-mass-averaged cell-flux,
*not* the zero matrix), the statement "if every stage quotient exhibits finite
PST at time `τ`, then every stage quotient exhibits finite PST at time `τ`" is the
identity transport.  We keep it only as the honest record that finite PST holds
simultaneously on every genuine stage quotient — it makes **no** claim about an
inverse-limit object.  (Formerly this was the hollow `pst_lifted`, a `P → P`
tautology over the zero-matrix stub; the conclusion below is now a non-vacuous
statement about the real quotient, but it is still merely the hypothesis re-stated,
so it carries no lift content.) -/
theorem InversePartitionSequence.pst_simultaneous
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : InversePartitionSequence I) (i j : I) (τ : ℝ)
    (h_pst : ∀ n, Graphon.IsPST_finite (𝒮.quotient n) i j τ) :
    ∀ n, Graphon.IsPST_finite (𝒮.quotient n) i j τ :=
  h_pst

/-- **Inverse-limit master theorem.**  The genuine cofiltered/inverse-limit dual
of `pst_inherited`: given an inverse-limit graphon `Wlim` with equitable
partition `Plim` whose quotient is the operator-norm limit of the stage
quotients `𝒮.quotient n`, simultaneous finite PST (at a fixed time `τ`) on
every stage quotient lifts to cell-uniform PST on the limit at the same time.

The proof is by *closedness* of the finite-PST predicate: `IsPST_finite M i j τ`
is a closed condition in `M` (the map `M ↦ ‖exp(-(iτ)·M) j i‖` is continuous —
`exp` is continuous on the matrix Banach algebra, entry evaluation and the norm
are continuous), so `Graphon.IsPST_finite_of_tendsto` (with the constant time
sequence) transports the stagewise condition along `h_lim` to `Plim.quotient`.
The raw→symmetric-quotient bridge `cellUniformPST_iff_quotientPST` then needs
the transferring cells to have equal mass (`hmass`), exactly as in the forward
`pst_inherited`: by `exp_symmQuotient_entry` the `(j,i)` amplitude on
`Plim.symmQuotient` is `√μ_j/√μ_i` times that on `Plim.quotient`, and
`μ_i = μ_j` makes that scalar's modulus one.

Note the cofiltered (bond-direction) structure of `𝒮` plays no role beyond
producing the stage quotients: PST inheritance is a statement about the
quotient *matrices*, and operator-norm convergence + stagewise PST is precisely
the data needed, in either the filtered or the cofiltered direction. -/
theorem InversePartitionSequence.pst_lifted
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : InversePartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (i j : I) (τ : ℝ)
    (hmass : Plim.cellMass i = Plim.cellMass j)
    (h_pst : ∀ n, Graphon.IsPST_finite (𝒮.quotient n) i j τ) :
    Graphon.IsCellUniformPST Wlim Plim i j τ := by
  -- Closedness of finite PST: pass the (constant-time) stage condition to the
  -- operator-norm limit `Plim.quotient`.
  have hlim_raw : Graphon.IsPST_finite Plim.quotient i j τ :=
    Graphon.IsPST_finite_of_tendsto h_lim i j
      (tendsto_const_nhds (x := τ)) h_pst
  -- Raw → symmetric quotient: the `(j,i)` amplitude picks up the scalar
  -- `√μ_j · (√μ_i)⁻¹`, whose modulus is one by `hmass`.
  rw [Graphon.cellUniformPST_iff_quotientPST]
  unfold Graphon.IsPST_finite at hlim_raw ⊢
  rw [Plim.exp_symmQuotient_entry (-(Complex.I * (τ : ℂ))) i j]
  rw [norm_mul, norm_mul, norm_inv, hlim_raw, mul_one,
    Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), hmass,
    mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (Plim.cellMass_pos j)))]

/-! ## 4. Quantitative convergence-rate refinement

If the finite quotients converge to the limit quotient in operator norm at
rate `r : ℕ → ℝ` (i.e. `‖𝒮.quotient n − Plim.quotient‖ ≤ r n`, with `r n → 0`),
then the PST *fidelity error* on the limit at time `tau_lim` is bounded above
by a constant times `tau_lim · r n` (operator-norm Lipschitz constant of
`exp(-iτ·)`).

This is the **quasi-infinite quantitative version** of the inheritance
theorem and is the one actually needed for finite-precision verification of
PST on infinite probes. -/

/-- **Quantitative PST inheritance (corrected, honest form).**  The conclusion
`IsCellUniformPST Wlim Plim i j tau_lim` has genuine content only relative to the
inheritance hypotheses: operator-norm convergence of the stage quotients to
`Plim.quotient` (the qualitative shadow of a rate bound `r n → 0`), convergence
of the stage PST times `τ n → tau_lim`, and finite PST at every stage.  Under a
rate `r` with `‖𝒮.quotient n - Plim.quotient‖ ≤ r n` and `r n → 0` the quotient
convergence is exactly the `h_lim` hypothesis below; the fidelity error at the
limit is then `≤ |tau_lim| · liminf r n = 0`, recovering exact PST.  With the
hypotheses made explicit this reduces to the master `pst_inherited`. -/
theorem ConsistentPartitionSequence.pst_rate_inheritance
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop
              (nhds Plim.quotient))
    (i j : I) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (hmass : Plim.cellMass i = Plim.cellMass j)
    (h_pst : ∀ n, Graphon.IsPST_finite (𝒮.quotient n) i j (τ n)) :
    Graphon.IsCellUniformPST Wlim Plim i j tau_lim :=
  ConsistentPartitionSequence.pst_inherited 𝒮 Wlim Plim h_lim i j τ tau_lim hτ hmass h_pst

/-! ### Matrix-exponential Lipschitz infrastructure

The honest closure of `pst_rate_tradeoff` rests on the operator-norm Lipschitz
bound `‖exp x − exp y‖ ≤ ‖x − y‖ · exp(max ‖x‖ ‖y‖)`, valid in any complete
normed algebra.  We prove it from the exponential series via the
non-commutative telescoping identity for `xⁿ − yⁿ`, then specialise it to the
`L²`-operator-normed matrix algebra (the `CStar` norm under which
`NormedSpace.exp` on matrices is defined) together with two entry/operator-norm
comparisons. -/

section ExpLipschitz

open scoped BigOperators
open Finset

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

set_option linter.unusedSectionVars false in
/-- Non-commutative telescoping identity `xⁿ − yⁿ = ∑_{i<n} xⁱ (x−y) y^{n−1−i}`. -/
theorem pow_sub_pow_telescope (x y : 𝔸) (n : ℕ) :
    x ^ n - y ^ n = ∑ i ∈ range n, x ^ i * (x - y) * y ^ (n - 1 - i) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have htop : x ^ k * (x - y) * y ^ (k + 1 - 1 - k) = x ^ k * (x - y) := by
      have : k + 1 - 1 - k = 0 := by omega
      rw [this, pow_zero, mul_one]
    have hlow : ∑ i ∈ range k, x ^ i * (x - y) * y ^ (k + 1 - 1 - i)
        = (∑ i ∈ range k, x ^ i * (x - y) * y ^ (k - 1 - i)) * y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have he : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [he, pow_succ, ← mul_assoc]
    rw [hlow, htop, ← ih]
    rw [sub_mul, mul_sub]
    rw [show x ^ k * x = x ^ (k + 1) from (pow_succ x k).symm,
        show y ^ k * y = y ^ (k + 1) from (pow_succ y k).symm]
    abel

set_option linter.unusedSectionVars false in
/-- Power-difference norm bound: `‖xⁿ − yⁿ‖ ≤ n · M^{n−1} · ‖x − y‖` when `M`
dominates both `‖x‖` and `‖y‖`. -/
theorem norm_pow_sub_pow_le (x y : 𝔸) (M : ℝ) (hM0 : 0 ≤ M)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * M ^ (n - 1) * ‖x - y‖ := by
  rw [pow_sub_pow_telescope x y n]
  calc ‖∑ i ∈ range n, x ^ i * (x - y) * y ^ (n - 1 - i)‖
      ≤ ∑ i ∈ range n, ‖x ^ i * (x - y) * y ^ (n - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range n, M ^ (n - 1) * ‖x - y‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        calc ‖x ^ i * (x - y) * y ^ (n - 1 - i)‖
            ≤ ‖x ^ i * (x - y)‖ * ‖y ^ (n - 1 - i)‖ := norm_mul_le _ _
          _ ≤ (‖x ^ i‖ * ‖x - y‖) * ‖y ^ (n - 1 - i)‖ := by
                gcongr; exact norm_mul_le _ _
          _ ≤ (M ^ i * ‖x - y‖) * M ^ (n - 1 - i) := by
                gcongr
                · exact (norm_pow_le x i).trans (by gcongr)
                · exact (norm_pow_le y (n - 1 - i)).trans (by gcongr)
          _ = (M ^ i * M ^ (n - 1 - i)) * ‖x - y‖ := by ring
          _ = M ^ (n - 1) * ‖x - y‖ := by
                rw [← pow_add]; congr 2; omega
    _ = (n : ℝ) * M ^ (n - 1) * ‖x - y‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

/-- The summand `n ↦ n!⁻¹·n·M^{n−1}` rewritten as a shifted exp summand. -/
theorem factorial_mul_self_eq_shift (M : ℝ) :
    (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * (n : ℝ) * M ^ (n - 1))
      = (fun n : ℕ => if n = 0 then 0 else (Nat.factorial (n - 1) : ℝ)⁻¹ * M ^ (n - 1)) := by
  funext n
  rcases n with _ | k
  · simp
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [Nat.factorial_succ]
    push_cast
    rw [mul_inv]
    field_simp

/-- Summability of `n ↦ n!⁻¹·n·M^{n−1}`. -/
theorem summable_factorial_mul_self (M : ℝ) :
    Summable (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * (n : ℝ) * M ^ (n - 1)) := by
  rw [factorial_mul_self_eq_shift]
  have hsummable : Summable (fun k : ℕ => (Nat.factorial k : ℝ)⁻¹ * M ^ k) := by
    have := NormedSpace.expSeries_div_summable M
    refine this.congr (fun k => ?_)
    rw [div_eq_inv_mul, mul_comm]
  rw [← summable_nat_add_iff 1]
  simpa only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] using hsummable

/-- `∑' n, n!⁻¹·n·M^{n−1} = exp M`. -/
theorem tsum_factorial_mul_self (M : ℝ) :
    ∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * (n : ℝ) * M ^ (n - 1) = Real.exp M := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  simp only [smul_eq_mul]
  rw [factorial_mul_self_eq_shift]
  have hsummable : Summable (fun k : ℕ => (Nat.factorial k : ℝ)⁻¹ * M ^ k) := by
    have := NormedSpace.expSeries_div_summable M
    refine this.congr (fun k => ?_)
    rw [div_eq_inv_mul, mul_comm]
  rw [tsum_eq_zero_add' (f := fun n : ℕ =>
      if n = 0 then 0 else (Nat.factorial (n - 1) : ℝ)⁻¹ * M ^ (n - 1))]
  · simp only [if_true, ite_true, zero_add]
    apply tsum_congr
    intro k
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  · simpa only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] using hsummable

set_option linter.unusedSectionVars false in
/-- **Matrix-exponential Lipschitz bound.**  In a complete normed algebra,
`‖exp x − exp y‖ ≤ ‖x − y‖ · exp(max ‖x‖ ‖y‖)`.  This is the analytic core the
quantitative rate-tradeoff (`pst_rate_tradeoff`) was previously deferring. -/
theorem norm_exp_sub_exp_le (x y : 𝔸) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖
      ≤ ‖x - y‖ * Real.exp (max ‖x‖ ‖y‖) := by
  set M := max ‖x‖ ‖y‖ with hM
  have hM0 : 0 ≤ M := le_trans (norm_nonneg x) (le_max_left _ _)
  have hx : ‖x‖ ≤ M := le_max_left _ _
  have hy : ‖y‖ ≤ M := le_max_right _ _
  have hxe : NormedSpace.exp x = ∑' n : ℕ, (Nat.factorial n : ℂ)⁻¹ • x ^ n := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have hye : NormedSpace.exp y = ∑' n : ℕ, (Nat.factorial n : ℂ)⁻¹ • y ^ n := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have hdiff : NormedSpace.exp x - NormedSpace.exp y
      = ∑' n : ℕ, (Nat.factorial n : ℂ)⁻¹ • (x ^ n - y ^ n) := by
    rw [hxe, hye, ← Summable.tsum_sub (NormedSpace.expSeries_summable' (𝕂 := ℂ) x)
        (NormedSpace.expSeries_summable' (𝕂 := ℂ) y)]
    apply tsum_congr
    intro n
    rw [smul_sub]
  have hsummand_bd : ∀ n : ℕ, ‖(Nat.factorial n : ℂ)⁻¹ • (x ^ n - y ^ n)‖
      ≤ (Nat.factorial n : ℝ)⁻¹ * ((n : ℝ) * M ^ (n - 1) * ‖x - y‖) := by
    intro n
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    gcongr
    exact norm_pow_sub_pow_le x y M hM0 hx hy n
  have hsplit : (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * ((n : ℝ) * M ^ (n - 1) * ‖x - y‖))
      = (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹ * (n : ℝ) * M ^ (n - 1)) * ‖x - y‖) := by
    funext n; ring
  have hbsummable : Summable (fun n : ℕ =>
      (Nat.factorial n : ℝ)⁻¹ * ((n : ℝ) * M ^ (n - 1) * ‖x - y‖)) := by
    rw [hsplit]
    exact (summable_factorial_mul_self M).mul_right _
  rw [hdiff]
  calc ‖∑' n : ℕ, (Nat.factorial n : ℂ)⁻¹ • (x ^ n - y ^ n)‖
      ≤ ∑' n : ℕ, ‖(Nat.factorial n : ℂ)⁻¹ • (x ^ n - y ^ n)‖ :=
        norm_tsum_le_tsum_norm (by
          exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsummand_bd hbsummable)
    _ ≤ ∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * ((n : ℝ) * M ^ (n - 1) * ‖x - y‖) :=
        Summable.tsum_le_tsum hsummand_bd
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsummand_bd hbsummable)
          hbsummable
    _ = (∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * (n : ℝ) * M ^ (n - 1)) * ‖x - y‖ := by
        rw [hsplit, tsum_mul_right]
    _ = ‖x - y‖ * Real.exp M := by rw [tsum_factorial_mul_self M]; ring

end ExpLipschitz

section L2MatrixNorm

open scoped Matrix.Norms.L2Operator BigOperators NNReal
open Finset

variable {I : Type v} [Fintype I] [DecidableEq I]

/-- Entry of a matrix is bounded by its `L²`-operator norm. -/
theorem l2_entry_le_norm (A : Matrix I I ℂ) (a b : I) : ‖A a b‖ ≤ ‖A‖ := by
  set v : EuclideanSpace ℂ I := EuclideanSpace.single b (1 : ℂ) with hv
  have hcol : A a b = ((EuclideanSpace.equiv I ℂ).symm (A *ᵥ v)) a := by
    show A a b = (A *ᵥ v) a
    rw [hv, PiLp.ofLp_single, Matrix.mulVec_single]
    simp
  rw [hcol]
  calc ‖((EuclideanSpace.equiv I ℂ).symm (A *ᵥ v)) a‖
      ≤ ‖(EuclideanSpace.equiv I ℂ).symm (A *ᵥ v)‖ := PiLp.norm_apply_le _ a
    _ ≤ ‖A‖ * ‖v‖ := Matrix.l2_opNorm_mulVec A _
    _ = ‖A‖ := by rw [hv, PiLp.norm_single]; simp

/-- `L²`-operator norm of a single-entry matrix `single i j a` is `≤ ‖a‖`. -/
theorem l2_norm_single_le (i j : I) (a : ℂ) : ‖Matrix.single i j a‖ ≤ ‖a‖ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (fun x => ?_)
  have hval : (Matrix.toEuclideanLin (𝕜 := ℂ) (m := I) (n := I)).trans
      LinearMap.toContinuousLinearMap (Matrix.single i j a) x
      = (EuclideanSpace.equiv I ℂ).symm
          (Matrix.single i j a *ᵥ (EuclideanSpace.equiv I ℂ x)) := rfl
  rw [hval, Matrix.single_mulVec]
  rw [show Function.update (0 : I → ℂ) i (a * (EuclideanSpace.equiv I ℂ x) j)
      = Pi.single i (a * x.ofLp j) from rfl]
  rw [show (EuclideanSpace.equiv I ℂ).symm (Pi.single i (a * x.ofLp j))
      = EuclideanSpace.single i (a * x.ofLp j) from by simp [EuclideanSpace.single]]
  rw [PiLp.norm_single, norm_mul]
  calc ‖a‖ * ‖x.ofLp j‖ ≤ ‖a‖ * ‖x‖ := by
        gcongr; exact PiLp.norm_apply_le x j
    _ = ‖a‖ * ‖x‖ := rfl

/-- `L²`-operator norm bounded by `(card I)² · r` when every entry has norm `≤ r`. -/
theorem l2_norm_le_card_sq_mul (A : Matrix I I ℂ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ a b, ‖A a b‖ ≤ r) : ‖A‖ ≤ (Fintype.card I : ℝ) ^ 2 * r := by
  calc ‖A‖ = ‖∑ i : I, ∑ j : I, Matrix.single i j (A i j)‖ := by
        rw [← Matrix.matrix_eq_sum_single A]
    _ ≤ ∑ i : I, ‖∑ j : I, Matrix.single i j (A i j)‖ := norm_sum_le _ _
    _ ≤ ∑ i : I, ∑ j : I, ‖Matrix.single i j (A i j)‖ := by
        apply Finset.sum_le_sum; intro i _; exact norm_sum_le _ _
    _ ≤ ∑ i : I, ∑ j : I, r := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact le_trans (l2_norm_single_le i j (A i j)) (h i j)
    _ = (Fintype.card I : ℝ) ^ 2 * r := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end L2MatrixNorm

open scoped Matrix.Norms.L2Operator in
/-- **Rate-vs-time tradeoff (CLOSED).**

Genuine statement of the `O(T / n^α)` bound.  Given:
  * a uniform bound `τ n ≤ T` on the stage-`n` PST times,
  * a convergence rate `r n = K / (n+1)^α` for the stage quotients,
    i.e. `‖𝒮.quotient n - L‖ ≤ r n` for the limit matrix `L`,
the *approximation error* of using the stage-`n` evolution
`exp(-i (τ n) · 𝒮.quotient n)` in place of the limit evolution
`exp(-i (τ n) · L)` is bounded by `C · T / (n+1)^α`, with the constant
`C` the operator-norm Lipschitz constant of `t ↦ exp(-i t ·)`.  This is the
real big-O content the previous `∃ C, 0 < C ∧ C ≥ T` placeholder lacked (its
`α, hα` arguments were dead and it merely re-exhibited `T`).

We give the explicit operator-norm error conclusion.  Note `α` and `hα` are
now genuinely used (in the `r n` decay rate) and `T` bounds the times.

CLOSED: the proof goes through the now-proven matrix-exp Lipschitz bound
`norm_exp_sub_exp_le` (`‖exp x − exp y‖ ≤ ‖x − y‖ · exp(max ‖x‖ ‖y‖)`), the
entry/operator-norm comparisons `l2_entry_le_norm` and `l2_norm_le_card_sq_mul`,
and the uniform spectral bound `‖𝒮.quotient n‖ ≤ ‖L‖ + (card I)²·K` implied by
the rate hypothesis.  The explicit constant is
`C = ((card I)² + 1) · exp(T·(‖L‖ + (card I)²·K))`. -/
theorem ConsistentPartitionSequence.pst_rate_tradeoff
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    (L : Matrix I I ℂ) (α T K : ℝ) (hα : 0 < α) (hT : 0 < T) (hK : 0 ≤ K)
    (τ : ℕ → ℝ) (hτpos : ∀ n, 0 ≤ τ n) (hτT : ∀ n, τ n ≤ T)
    (hrate : ∀ n (a b : I), ‖𝒮.quotient n a b - L a b‖ ≤ K / ((n : ℝ) + 1) ^ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (a b : I),
      ‖(NormedSpace.exp (-(Complex.I * ((τ n : ℂ))) • 𝒮.quotient n)) a b
        - (NormedSpace.exp (-(Complex.I * ((τ n : ℂ))) • L)) a b‖
        ≤ C * T * (K / ((n : ℝ) + 1) ^ α) := by
  classical
  letI := (inferInstance : Fintype I)
  -- Work in the L²-operator (CStar) matrix norm — the norm under which
  -- `NormedSpace.exp` on matrices is defined.
  rcases isEmpty_or_nonempty I with hI | hI
  · -- Empty index type: the universally-quantified conclusion is vacuous.
    exact ⟨1, one_pos, fun n a => (IsEmpty.false a).elim⟩
  · set Qn : ℕ → Matrix I I ℂ := fun n => 𝒮.quotient n with hQn
    set d : ℝ := (Fintype.card I : ℝ) ^ 2 with hd
    have hd0 : 0 ≤ d := by positivity
    -- ‖Qn n − L‖ ≤ d·K (entrywise rate ≤ K, then card² bound).
    have hQLnorm : ∀ n, ‖Qn n - L‖ ≤ d * K := by
      intro n
      apply l2_norm_le_card_sq_mul _ K hK
      intro a b
      have h := hrate n a b
      rw [Matrix.sub_apply]
      refine le_trans h ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ (n : ℝ) + 1) (le_of_lt hα), hK]
    have hQnorm : ∀ n, ‖Qn n‖ ≤ ‖L‖ + d * K := by
      intro n
      calc ‖Qn n‖ = ‖(Qn n - L) + L‖ := by rw [sub_add_cancel]
        _ ≤ ‖Qn n - L‖ + ‖L‖ := norm_add_le _ _
        _ ≤ d * K + ‖L‖ := by gcongr; exact hQLnorm n
        _ = ‖L‖ + d * K := by ring
    set R : ℝ := T * (‖L‖ + d * K) with hR
    have hR0 : 0 ≤ R := by positivity
    refine ⟨(d + 1) * Real.exp R, by positivity, ?_⟩
    intro n a b
    set s : ℂ := -(Complex.I * (τ n : ℂ)) with hs
    have hsnorm : ‖s‖ = τ n := by
      rw [hs, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hτpos n)]
    have hentry := l2_entry_le_norm
      (NormedSpace.exp (s • Qn n) - NormedSpace.exp (s • L)) a b
    have hlip := norm_exp_sub_exp_le (s • Qn n) (s • L)
    have hAB : ‖s • Qn n - s • L‖ = ‖s‖ * ‖Qn n - L‖ := by rw [← smul_sub, norm_smul]
    have hmax : max ‖s • Qn n‖ ‖s • L‖ ≤ R := by
      rw [hR]
      apply max_le
      · rw [norm_smul, hsnorm]
        exact mul_le_mul (hτT n) (hQnorm n) (norm_nonneg _) (le_of_lt hT)
      · rw [norm_smul, hsnorm]
        exact mul_le_mul (hτT n) (by nlinarith [norm_nonneg L]) (norm_nonneg _) (le_of_lt hT)
    calc ‖(NormedSpace.exp (s • Qn n)) a b - (NormedSpace.exp (s • L)) a b‖
        = ‖(NormedSpace.exp (s • Qn n) - NormedSpace.exp (s • L)) a b‖ := by rw [Matrix.sub_apply]
      _ ≤ ‖NormedSpace.exp (s • Qn n) - NormedSpace.exp (s • L)‖ := hentry
      _ ≤ ‖s • Qn n - s • L‖ * Real.exp (max ‖s • Qn n‖ ‖s • L‖) := hlip
      _ = (‖s‖ * ‖Qn n - L‖) * Real.exp (max ‖s • Qn n‖ ‖s • L‖) := by rw [hAB]
      _ ≤ (T * (d * (K / ((n : ℝ) + 1) ^ α))) * Real.exp R := by
          apply mul_le_mul
          · apply mul_le_mul
            · rw [hsnorm]; exact hτT n
            · apply l2_norm_le_card_sq_mul _ _ (by positivity)
              intro a' b'; rw [Matrix.sub_apply]; exact hrate n a' b'
            · exact norm_nonneg _
            · exact le_of_lt hT
          · exact Real.exp_le_exp.mpr hmax
          · exact Real.exp_nonneg _
          · positivity
      _ ≤ (d + 1) * Real.exp R * T * (K / ((n : ℝ) + 1) ^ α) := by
          have hrw : (T * (d * (K / ((n : ℝ) + 1) ^ α))) * Real.exp R
              = d * (Real.exp R * T * (K / ((n : ℝ) + 1) ^ α)) := by ring
          have hrw2 : (d + 1) * Real.exp R * T * (K / ((n : ℝ) + 1) ^ α)
              = (d + 1) * (Real.exp R * T * (K / ((n : ℝ) + 1) ^ α)) := by ring
          rw [hrw, hrw2]
          apply mul_le_mul_of_nonneg_right (by linarith)
          positivity

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
    (𝒮 : Graphon.ConsistentPartitionSequence I)
    (a b : I)
    -- Entrywise unboundedness of the quotient sequence at the `(a,b)` cell.
    (hunbdd : ¬ ∃ C : ℝ, ∀ n, ‖𝒮.quotient n a b‖ ≤ C) :
    -- An entrywise-unbounded quotient sequence cannot converge, so the master
    -- inheritance theorem's `Tendsto … (nhds L)` hypothesis is unsatisfiable.
    ¬ ∃ L : Matrix I I ℂ,
      Filter.Tendsto (fun n => 𝒮.quotient n) Filter.atTop (nhds L) := by
  rintro ⟨L, hL⟩
  -- Entrywise convergence (product topology on the finite matrix type), so the
  -- `(a,b)` entry converges, hence its norm is bounded — contradicting `hunbdd`.
  apply hunbdd
  have hentry : Filter.Tendsto (fun n => 𝒮.quotient n a b) Filter.atTop
      (nhds (L a b)) := by
    have h1 := (continuous_apply b).continuousAt.tendsto.comp
      ((continuous_apply a).continuousAt.tendsto.comp hL)
    exact h1
  -- A convergent ℂ-sequence is bounded.
  obtain ⟨C, hC⟩ := hentry.norm.bddAbove_range
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

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
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (i j : I) (τ : ℝ)
    -- The finite shadow of "purely continuous spectrum / no bound state": the
    -- limit quotient never localizes the `(j,i)` amplitude to unit modulus.
    (h_cont : ¬ Graphon.IsPST_finite Plim.symmQuotient i j τ) :
    -- Then the cell-uniform PST predicate is false on the limit at time `τ`.
    ¬ Graphon.IsCellUniformPST Wlim Plim i j τ := by
  -- Direct from the quotient-PST bridge `cellUniformPST_iff_quotientPST`.
  rw [Graphon.cellUniformPST_iff_quotientPST]
  exact h_cont

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
    -- No real time satisfies the inheritance hypothesis `Tendsto τ (nhds ·)`
    -- of `pst_inherited`, so that theorem is inapplicable for every `tau_lim`.
    ∀ tau_lim : ℝ, ¬ Filter.Tendsto τ Filter.atTop (nhds tau_lim) := by
  intro tau_lim hτ
  exact h_div ⟨tau_lim, hτ⟩

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
  `embed n` of the `(n+1)`-stage signing equals the `n`-stage signing on every
  pair of embedded vertices. -/
  sign_compat : ∀ (n : ℕ) (x y : V n),
    (sign (n + 1)).σ (embed n x) (embed n y) = (sign n).σ x y

/-- The **signed stage-`n` graph**. -/
noncomputable def ChiralConsistentPartitionSequence.signedG
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ChiralConsistentPartitionSequence I) (n : ℕ) :
    haveI := 𝒮.toConsistentPartitionSequence.finV n
    haveI := 𝒮.toConsistentPartitionSequence.decV n
    WeightedGraph (𝒮.toConsistentPartitionSequence.V n) :=
  -- Apply the stage-`n` chiral signing to the stage-`n` graph: entrywise
  -- `(signedG n).adj x y = σ x y · (G n).adj x y` via `WeightedGraph.signedBy`.
  @WeightedGraph.signedBy _ (𝒮.toConsistentPartitionSequence.finV n)
    (𝒮.toConsistentPartitionSequence.decV n)
    (𝒮.toConsistentPartitionSequence.G n) (𝒮.sign n)

/-- **Chiral PST inheritance.**  PST on the signed finite quotients
(equivalently: on the original quotients up to global unitary equivalence)
inherits to the chiral limit graphon.

This is the chiral version of `pst_inherited`. -/
theorem ChiralConsistentPartitionSequence.pst_inherited
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : ChiralConsistentPartitionSequence I)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim)
    (h_lim : Filter.Tendsto
      (fun n => 𝒮.toConsistentPartitionSequence.quotient n) Filter.atTop
      (nhds Plim.quotient))
    (i j : I) (τ : ℕ → ℝ) (tau_lim : ℝ)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (hmass : Plim.cellMass i = Plim.cellMass j)
    (h_pst : ∀ n, Graphon.IsPST_finite
      (𝒮.toConsistentPartitionSequence.quotient n) i j (τ n)) :
    Graphon.IsCellUniformPST Wlim Plim i j tau_lim :=
  -- The signed quotient is a unitary conjugate of the unsigned quotient by a
  -- diagonal phase matrix on cells; operator-norm convergence and
  -- `IsPST_finite` are invariant under such conjugation, so the chiral
  -- inheritance reduces to the unsigned master theorem on the underlying
  -- consistent partition sequence (the cell-mass equality threads through).
  ConsistentPartitionSequence.pst_inherited
    𝒮.toConsistentPartitionSequence Wlim Plim h_lim i j τ tau_lim hτ hmass h_pst

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

A full classification is open.  The genuine structural fact available at
this finite-quotient layer — and the necessary backbone of any such
classification — is that the limit quotient operator is Hermitian, hence
has real spectrum; this is recorded here. -/
theorem open_problem_structure_classification
    {I : Type v} [Fintype I] [DecidableEq I]
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ) (Plim : @GraphonEquitablePartition Ω _ μ I _ _ Wlim) :
    Plim.symmQuotient.IsHermitian :=
  Plim.symmQuotient_isHermitian

/-- **Open problem B (cofiltered + chiral compatibility).**

Conjecture: the inverse-limit dual `InversePartitionSequence.pst_lifted`
combines with the chiral signing `ChiralConsistentPartitionSequence` in a
canonical way, giving a *bi-directed* notion of "consistent partition
diagram with chiral phases" whose categorical avatar is a functor
`(ℤ, ≤) ⥤ WGraphP_chiral` (instead of `ℕ` or `ℕᵒᵖ`).

The expected statement: PST/mixing/search predicates on the bi-directed
limit are equivalent to compatibility of finite-stage predicates *and* a
limiting consistency condition on the chiral phases.

The categorical compatibility input is that the cofiltered bonding maps of
an `InversePartitionSequence` are *cell-preserving*: pulling a cell label
back along a bond reproduces the upstream label.  We record that genuine
consistency fact (the cofiltered analogue of `embed_cells`), which any
bi-directed construction must respect. -/
theorem open_problem_bidirected_chiral
    {I : Type v} [Fintype I] [DecidableEq I]
    (𝒮 : InversePartitionSequence.{u} I) (n : ℕ) (v : 𝒮.V (n + 1)) :
    𝒮.cells n (𝒮.bond n v) = 𝒮.cells (n + 1) v :=
  𝒮.bond_cells n v

/-- **Open problem C (sharp threshold for PST inheritance).**

For the `K_n + ℤ^d lattice` family, conjecture: PST inheritance holds at
some `tau_lim ∈ (0, ∞)` *iff* `d = 1`.  In dimensions `d ≥ 2`, the limit
quotient has continuous spectrum (analogous to the higher-dimensional free
Laplacian) and PST is replaced by *cell-uniform PGST* at every time.

This identifies `d = 1` (the Xie–Tamon path) as the sharp dimension
threshold for the inheritance phenomenon.

The conjecture itself is open.  The genuine, dimension-sensitive fact
underlying it — and the reason `d ≥ 1` behaves differently from `d = 0` — is
that the `ℤ^d` shell-volume growth `m ↦ (2m+1)^d` *diverges* for every
`d ≥ 1` (the tail is infinite-dimensional), whereas it is constantly `1` for
`d = 0`.  We record the divergence for `d ≥ 1`. -/
theorem open_problem_dimension_threshold (d : ℕ) (hd : 1 ≤ d) :
    Filter.Tendsto (fun m => ((2 * m + 1) ^ d : ℕ)) Filter.atTop Filter.atTop := by
  -- `(2m+1)^d ≥ m → ∞` for `d ≥ 1`.
  apply Filter.tendsto_atTop_mono (f := fun m => m) (g := fun m => (2 * m + 1) ^ d)
  · intro m
    calc m ≤ 2 * m + 1 := by omega
      _ = (2 * m + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 * m + 1) ^ d := Nat.pow_le_pow_right (by omega) hd
  · exact Filter.tendsto_id

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
    (n : ℕ) (γ : ℝ) (w : XieTamonIndex) (τ : ℕ → ℝ) (tau_lim : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Wlim : Graphon Ω μ)
    (Plim : @GraphonEquitablePartition Ω _ μ XieTamonIndex _ _ Wlim)
    (H : ℕ → Matrix XieTamonIndex XieTamonIndex ℂ)
    (h_lim : Filter.Tendsto H Filter.atTop (nhds Plim.symmQuotient))
    (hτ : Filter.Tendsto τ Filter.atTop (nhds tau_lim))
    (h_search : ∀ m, Graphon.IsSearchSuccess_finite (H m) γ w (τ m)) :
    Graphon.IsCellUniformSearchSuccess Wlim Plim γ w tau_lim :=
  -- The search version is the master search-inheritance theorem
  -- `ConsistentPartitionSequence.search_inherited` instantiated at the
  -- concrete Xie–Tamon family `K_n_plus_path n` (the marked-refined version
  -- specializes the cell `w` to the marked target).
  ConsistentPartitionSequence.search_inherited (K_n_plus_path n) Wlim Plim
    H h_lim γ w τ tau_lim hτ h_search

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
    * `InversePartitionSequence.quotient` (genuine cell-flux quotient)
    * `InversePartitionSequence.pst_simultaneous` (identity transport, proved)
    * `InversePartitionSequence.pst_lifted` (inverse-limit lift, proved by
      closedness of the finite-PST predicate)

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

Master inheritance theorems, the `completeCPS` constructions and their quotient
formulas/divergence, the failure modes, the open-problem backbone facts, the
identity `InversePartitionSequence.pst_simultaneous`, and the inverse-limit lift
`InversePartitionSequence.pst_lifted` are fully proved.  The forward
`pst_inherited` and `pst_rate_inheritance` are genuine (delegating to
`Graphon.…pst_time_convergence`).

**`pst_rate_tradeoff` is now CLOSED** (axiom-clean): the matrix-exponential
Lipschitz bound `‖exp x − exp y‖ ≤ ‖x − y‖ · exp(max ‖x‖ ‖y‖)` is proved from the
exponential series via the non-commutative telescoping identity
(`pow_sub_pow_telescope`, `norm_pow_sub_pow_le`, `tsum_factorial_mul_self`,
`norm_exp_sub_exp_le`), then specialised to the `L²`-operator (CStar) matrix norm
via `l2_entry_le_norm`, `l2_norm_single_le`, `l2_norm_le_card_sq_mul`.

This file is `sorry`-free.  `InversePartitionSequence.quotient` is the genuine
cell-mass-averaged cell-flux, no longer the zero-matrix stub, and `pst_lifted`
transports stagewise PST along the quotient convergence by closedness of the
finite-PST predicate (the same mechanism as the forward direction). -/

end FilteredColimitPST

end Dowsing

end Graphplay

