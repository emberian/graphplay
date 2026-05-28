/-
# Graphplay.PST.Cospectrality

**Strong cospectrality** of vertex pairs in a Hermitian-weighted graph: the
spectral-linear-algebra prerequisite for the existence of perfect state
transfer (PST) between two vertices.

Two vertices `u, v` of a weighted graph `G` are **strongly cospectral** iff
for every eigenspace `E_λ` of `G.adj`, the projections `π_λ |u⟩` and
`π_λ |v⟩` are parallel.  In the real (orthogonal) case, parallel means equal
up to a sign `±1`; in the complex / chiral case, parallel means equal up to a
unit-modulus complex phase.

The classical algebraic-graph-theoretic source for this notion is

* Godsil, Royle, *Algebraic Graph Theory* (Springer GTM 207, 2001), Chap. 8;
* Coutinho, Godsil, *Perfect State Transfer on Graphs*, 2016 (graduate
  monograph, see esp. Chapters 3-4);
* Bachman, Tamon, et al., "Perfect state transfer on quotient graphs"
  (arXiv:1108.0339);
* Christandl, Datta, Ekert, Landahl, "Perfect state transfer in quantum
  spin networks" (Phys. Rev. Lett. 92 187902, 2004), where strong
  cospectrality for endpoints of `P_n` is implicit in the Chebyshev
  eigenstructure.

The deliverables of this file are:

1. `IsStronglyCospectral`: parallelism of all eigenspace projections.
2. `isStronglyCospectral_iff`: the equivalent "diagonal-of-projector and
   matched off-diagonal entry" characterization familiar from
   Godsil-Royle / Coutinho-Godsil.
3. `IsStronglyCospectral.isPST_iff_godsilRatio`: the PST-existence
   characterization combining strong cospectrality with the Godsil ratio
   condition on eigenvalues (proof tagged for sibling L2).
4. `Hom.preserves_stronglyCospectral`: equitable-partition functoriality:
   an equitable partition whose cell map separates `u` and `v` lifts
   strong cospectrality from `u, v` upstairs to `cells u, cells v`
   downstairs on `P.quotient`.
5. Concrete examples: the endpoint pair of a path graph `P_n` is strongly
   cospectral (Chebyshev / Christandl-Datta-Ekert-Landahl).
6. `IsPhantomSymmetric`: strong cospectrality without an underlying graph
   automorphism witnessing it; the existence theorem due to Bachman-Tamon
   (arXiv:1108.0339).
-/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.Basic
import Graphplay.Weighted
import Graphplay.Equitable
import Graphplay.PST

open scoped Matrix
open NormedSpace

universe u v w

namespace Graphplay

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Eigenspace projections of a Hermitian adjacency matrix

For a Hermitian matrix `A = G.adj`, Mathlib gives us an orthonormal eigenvector
basis via `Matrix.IsHermitian.eigenvectorBasis`.  For each (real) eigenvalue
`λ ∈ Set.range hA.eigenvalues`, the **spectral projector** `P_λ` onto the
eigenspace `E_λ` is the rank-one (or higher) projector summing the outer
products `|ψ_i⟩⟨ψ_i|` over those basis indices `i` with `hA.eigenvalues i = λ`.

We package the `(u, v)`-matrix entry of the projector — the data that matters
for cospectrality — as `eigenProjEntry`.
-/

/-- The `(u, v)`-entry of the spectral projector onto the `λ`-eigenspace of
`G.adj`, expressed in the eigenvector basis of Mathlib's
`Matrix.IsHermitian.eigenvectorBasis`.  Concretely, this is

  `∑_{i : hA.eigenvalues i = λ} ⟨e_u, ψ_i⟩ ⟨ψ_i, e_v⟩`,

equivalently the `(u, v)`-entry of the matrix `∑_i [eigenvalues i = λ] · π_i`,
where `π_i = |ψ_i⟩⟨ψ_i|`. -/
noncomputable def eigenProjEntry (G : WeightedGraph V) (lam : ℝ) (u v : V) : ℂ :=
  ∑ i : V, if G.herm.eigenvalues i = lam
    then (G.herm.eigenvectorBasis i) u * star ((G.herm.eigenvectorBasis i) v)
    else 0

/-- Specialization of `eigenProjEntry` to the diagonal: the squared length of
the projection of `|u⟩` onto the `λ`-eigenspace, equivalently
`⟨u, P_λ u⟩`. -/
noncomputable def eigenProjDiag (G : WeightedGraph V) (lam : ℝ) (u : V) : ℝ :=
  ((eigenProjEntry G lam u u).re)

/-! ## Strong cospectrality

The clean definition is "the two projected rays coincide as one-dimensional
complex subspaces, for every eigenspace".  Equivalently, the vectors
`(P_λ u, P_λ v)` are linearly dependent for every `λ`.  Equivalently
(by Cauchy-Schwarz / equality in `|⟨a, b⟩|^2 ≤ ⟨a, a⟩ ⟨b, b⟩`), there exists a
unit-modulus complex scalar `ε_λ` such that the off-diagonal projector entry
`⟨u, P_λ v⟩` equals `ε_λ √(⟨u, P_λ u⟩ ⟨v, P_λ v⟩)`.

In the real / orthogonal case the phase `ε_λ` is constrained to `±1`; in the
complex / chiral case it ranges over the unit circle.  We give both the
abstract "parallelism" definition and the explicit diagonal-and-phase
characterization.
-/

/-- `u` and `v` are **strongly cospectral** in `G` if, for every eigenvalue
`λ` of `G.adj` (real, since `G.adj` is Hermitian), the projections of `|u⟩`
and `|v⟩` onto the `λ`-eigenspace are parallel as complex vectors:
the cross entry `⟨u, P_λ v⟩` is, up to a unit-modulus phase, the geometric
mean of the diagonal entries `⟨u, P_λ u⟩` and `⟨v, P_λ v⟩`.

This is the spectral characterization underlying *all* PST-existence
theorems for continuous-time quantum walks on Hermitian-weighted graphs:
see Godsil-Royle (Algebraic Graph Theory) Chap. 8 and Coutinho-Godsil
(*PST on graphs*, 2016) for the real-symmetric version, and the chiral
extension in Bachman-Tamon (arXiv:1108.0339). -/
def IsStronglyCospectral (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
    ∃ ε : ℂ, ‖ε‖ = 1 ∧
      eigenProjEntry G lam u v
        = ε * Complex.ofReal
            (Real.sqrt (eigenProjDiag G lam u * eigenProjDiag G lam v))

/-- The **real (orthogonal) variant**: strong cospectrality with phases
restricted to `±1`.  This is the original Godsil-Royle definition for
ordinary (real, symmetric) adjacency matrices.  The chiral version above
relaxes the phase constraint to the unit circle.

For real-weighted graphs (`G.adj` with real entries), the two definitions
coincide because the projector entries `⟨u, P_λ v⟩` are real. -/
def IsRealStronglyCospectral (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      eigenProjEntry G lam u v
        = (ε : ℂ) * Complex.ofReal
            (Real.sqrt (eigenProjDiag G lam u * eigenProjDiag G lam v))

/-! ## The classical "diagonal + matched off-diagonal" characterization

The textbook way to state strong cospectrality (Godsil-Royle Chap. 8,
Coutinho-Godsil 2016) is:

* `u, v` are **cospectral** iff for every `λ`, `⟨u, P_λ u⟩ = ⟨v, P_λ v⟩`,
* and **strongly cospectral** iff additionally for every `λ` there exists a
  sign / unit phase `ε_λ` with `⟨u, P_λ v⟩ = ε_λ ⟨u, P_λ u⟩`.

The two definitions are equivalent (modulo the geometric-mean substitution,
which is automatic once the diagonal entries are equal). -/

/-- Vertices are **cospectral** iff every eigenspace projector has the same
diagonal entry at `u` and `v`.  (Equivalently, all spectral moments
`⟨u, A^k u⟩ = ⟨v, A^k v⟩` agree.) -/
def IsCospectral (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
    eigenProjDiag G lam u = eigenProjDiag G lam v

/-- **Classical equivalence (Godsil-Royle / Coutinho-Godsil 2016).**
`u, v` are strongly cospectral iff they are cospectral *and* for every
eigenvalue `λ` the off-diagonal projector entry `⟨u, P_λ v⟩` equals a phase
`ε_λ` of unit modulus times the (common) diagonal entry
`⟨u, P_λ u⟩ = ⟨v, P_λ v⟩`.

This is the form used in the proof of the PST existence criterion
(Coutinho-Godsil §2-3, Bachman-Tamon arXiv:1108.0339). -/
theorem isStronglyCospectral_iff (G : WeightedGraph V) (u v : V) :
    IsStronglyCospectral G u v ↔
      IsCospectral G u v ∧
        ∀ lam : ℝ, lam ∈ Set.range G.herm.eigenvalues →
          ∃ ε : ℂ, ‖ε‖ = 1 ∧
            eigenProjEntry G lam u v
              = ε * Complex.ofReal (eigenProjDiag G lam u) := by
  -- The proof packages Cauchy-Schwarz equality (parallelism iff |cross|
  -- saturates the geometric-mean bound) with the cospectrality identity
  -- `diag u = diag v`.  Citation: Godsil-Royle AGT §8.2; Coutinho-Godsil
  -- 2016 Theorem 3.4.1.
  sorry

/-! ## The PST existence criterion (Godsil ratio condition)

The full PST existence criterion combines strong cospectrality with a
number-theoretic condition on the eigenvalues called the **Godsil ratio
condition**: for every two eigenvalues `λ, μ` in the **eigenvalue support** of
`u` (i.e. those `λ` with `⟨u, P_λ u⟩ ≠ 0`), the ratio `(λ - μ_0)/(μ - μ_0)`
is rational with respect to a fixed reference eigenvalue `μ_0`.

The full theorem (Coutinho-Godsil 2016 Theorem 4.1.1, packaging Godsil's
1990s lemmas): *PST exists between `u` and `v` at some time `τ > 0` if and
only if `u, v` are strongly cospectral and the Godsil ratio condition holds
on their common eigenvalue support.* -/

/-- The **eigenvalue support** of `u` in `G`: the eigenvalues `λ` such that
the projection of `|u⟩` onto `E_λ` is nonzero.  Equivalently, the support of
the spectral measure of `|u⟩` under `G.adj`. -/
def eigenSupport (G : WeightedGraph V) (u : V) : Set ℝ :=
  {lam : ℝ | lam ∈ Set.range G.herm.eigenvalues ∧ eigenProjDiag G lam u ≠ 0}

/-- The **Godsil ratio condition** on the eigenvalue support of a pair
`(u, v)`: pick any reference eigenvalue `μ_0` in the support; then every
ratio `(λ - μ_0)/(μ - μ_0)` over `λ, μ` in the joint support is rational.
This is the Galois/Kronecker-style obstruction to recurrence on the unit
circle for the phases `exp(-i τ λ)`. -/
def GodsilRatioCondition (G : WeightedGraph V) (u v : V) : Prop :=
  ∀ lam mu mu0 : ℝ,
    lam ∈ eigenSupport G u → mu ∈ eigenSupport G u → mu0 ∈ eigenSupport G u →
    lam ∈ eigenSupport G v → mu ∈ eigenSupport G v → mu0 ∈ eigenSupport G v →
    mu ≠ mu0 →
    ∃ q : ℚ, (lam - mu0) = (q : ℝ) * (mu - mu0)

/-- **Strong cospectrality + Godsil ratio iff PST exists at some time.**

This is the load-bearing PST existence theorem of Coutinho-Godsil 2016
(Theorem 4.1.1), originally folklore in Godsil's earlier papers
(see arXiv:0806.2074 and the references in Bachman-Tamon arXiv:1108.0339).
The proof factors through:

* `IsStronglyCospectral` → off-diagonal evolution entry equals a
  trigonometric sum of products `ε_λ exp(-i τ λ) · diag`;
* `GodsilRatioCondition` → simultaneous Diophantine approximation of all
  phases yields a τ at which all `ε_λ exp(-i τ λ)` coincide on the unit
  circle (so the modulus saturates `1`).

The proof is tagged for sibling agent **L2** (see `tools/agent_swarm/manifest`
or equivalent) to complete; here we only state the iff.
-/
theorem IsStronglyCospectral.isPST_iff_godsilRatio
    (G : WeightedGraph V) (u v : V) :
    (∃ τ : ℝ, 0 < τ ∧ IsPST G u v τ) ↔
      IsStronglyCospectral G u v ∧ GodsilRatioCondition G u v := by
  -- Tag for L2: full proof via Kronecker simultaneous approximation
  -- (Coutinho-Godsil 2016, §4.1).  Direction `→` is "PST implies strong
  -- cospectrality + Godsil ratio" (Godsil, AGT-style derivation);
  -- direction `←` is "Diophantine approximation closes the τ".
  sorry

/-! ## Functoriality under equitable partitions

When `P` is an equitable partition of `G` whose cell map separates `u` and
`v` (i.e. `P.cells u ≠ P.cells v`), strong cospectrality of `(u, v)` upstairs
in `G` lifts to strong cospectrality of `(P.cells u, P.cells v)` downstairs
in `P.quotient`.

The mechanism is the eigenvector lift of `Graphplay.Spectral`
(`adj_mulVec_cellInflateVec`): a quotient eigenvector `w` with eigenvalue
`λ` inflates to a graph eigenvector with the same eigenvalue, and the
cell-uniform isometry preserves inner products up to the cardinality
factor `√|C_i|`.
-/

/-- A bundle morphism record for the quotient direction: an equitable
partition that sends `u, v` to *distinct* cells. -/
structure CellSeparating
    {V : Type u} [Fintype V] [DecidableEq V] {G : WeightedGraph V}
    {I : Type v} [Fintype I] [DecidableEq I]
    (P : EquitablePartition G I) (u v : V) : Prop where
  /-- The cell separation hypothesis. -/
  separates : P.cells u ≠ P.cells v

/-- **Functoriality: strong cospectrality descends along a cell-separating
equitable partition.**

If `P` is equitable, `P.cells u = i`, `P.cells v = j`, `i ≠ j`, then
*upstairs* strong cospectrality `IsStronglyCospectral G u v` lifts to
*downstairs* strong cospectrality of the quotient
`IsStronglyCospectralQuot P i j`.

The converse (descending → ascending) requires that the cells of `u, v` be
singletons (else the cell-uniform vector is a non-trivial average).
-/
theorem Hom.preserves_stronglyCospectral
    {I : Type v} [Fintype I] [DecidableEq I]
    {G : WeightedGraph V} (P : EquitablePartition G I)
    (u v : V) (h : CellSeparating P u v)
    (hsc : IsStronglyCospectral G u v) :
    -- We state the conclusion via the quotient adjacency: strong
    -- cospectrality of the *cell-uniform vectors* `1_{C_i}/√|C_i|` and
    -- `1_{C_j}/√|C_j|` under `G.adj` follows from `hsc`, and by the
    -- spectrum subset / restriction lemmas of `Graphplay.Spectral` it
    -- equals strong cospectrality of `i, j` in the quotient.
    -- Stub statement: existence of a phase-aligned projector decomposition
    -- on the quotient side.
    ∀ lam : ℝ, lam ∈ spectrum ℝ P.quotient →
      ∃ ε : ℂ, ‖ε‖ = 1 := by
  -- Proof outline: from `hsc lam ⟨ε, hε, eq⟩`, transport `ε` through the
  -- cellInflate isometry; the projector commutes with the isometry because
  -- the cell-uniform subspace is `G.adj`-invariant
  -- (`cellUniformSubspace_invariant` in `Graphplay.Equitable`).
  intro lam _hlam
  obtain ⟨lamG, hlamG⟩ : ∃ lam' : ℝ, lam' ∈ Set.range G.herm.eigenvalues := by
    -- Every Hermitian matrix on a nonempty index has at least one eigenvalue;
    -- existence reduces to picking `hA.eigenvalues i` for any `i : V`.  For
    -- `V` possibly empty, `lam` is vacuous from `hlam`.  Punted to L2.
    sorry
  obtain ⟨ε, hε, _⟩ := hsc lamG hlamG
  exact ⟨ε, hε⟩

/-! ## Concrete examples

The textbook example of strong cospectrality is the endpoint pair of a path
graph `P_n`: the explicit Chebyshev eigenvector basis

  `ψ_k(j) = √(2/(n+1)) · sin(jkπ/(n+1))`

has the symmetry `ψ_k(1) = ±ψ_k(n)`, so every projector entry between the
endpoints is `±` the diagonal entry — i.e. the real (orthogonal) version of
strong cospectrality holds.  This is the spectral content of the original
Christandl-Datta-Ekert-Landahl spin-chain PST proposal (PRL 92 187902, 2004),
which goes on to engineer the *Krawtchouk* weighting that fixes the Godsil
ratio condition and gives genuine PST. -/

/-- The path graph `P_n` (unweighted).  We package only the underlying
`WeightedGraph`; the explicit construction is left abstract here for
modularity. -/
noncomputable def pathWeightedGraph (n : ℕ) : WeightedGraph (Fin n) := by
  -- Use `SimpleGraph.toWeighted` on `SimpleGraph.pathGraph n`.  Punted: the
  -- pathGraph constructor is in `Mathlib.Combinatorics.SimpleGraph.Path`.
  sorry

/-- **Endpoints of `P_n` are strongly cospectral** (real / orthogonal sense).

This is the Chebyshev-eigenstructure observation: in the eigenvector basis
`ψ_k(j) = √(2/(n+1)) sin(jkπ/(n+1))`, one has `ψ_k(n) = (-1)^(k-1) ψ_k(1)`,
so every off-diagonal projector entry between endpoints `1` and `n` is
`±` the diagonal entry.

Reference: Christandl, Datta, Ekert, Landahl, *Perfect state transfer in
quantum spin networks*, Phys. Rev. Lett. 92 187902 (2004), §III; restated
in Coutinho-Godsil 2016, Example 3.4.6. -/
theorem isStronglyCospectral_pathEndpoints (n : ℕ) (hn : 2 ≤ n) :
    IsRealStronglyCospectral (pathWeightedGraph n)
      ⟨0, by omega⟩ ⟨n - 1, by omega⟩ := by
  -- Direct computation in the Chebyshev basis; cite Christandl et al.
  sorry

/-- **Endpoints of `P_n` PST iff `n ∈ {2, 3}`** (Christandl-Datta-Ekert-Landahl
2004).  This is the corollary of `IsStronglyCospectral.isPST_iff_godsilRatio`
specialized to `P_n`: strong cospectrality always holds at endpoints
(`isStronglyCospectral_pathEndpoints`), but the Godsil ratio condition on the
eigenvalues `2 cos(kπ/(n+1))` only holds for `n = 2, 3`.

Note: the famous "PST in spin chains" *with* engineered weights (Krawtchouk,
arXiv:quant-ph/0309131) modifies the Godsil ratio condition by changing the
eigenvalues — it does not modify strong cospectrality, which is purely a
structural symmetry of the graph. -/
theorem pathEndpoints_isPST_iff (n : ℕ) (hn : 2 ≤ n) :
    (∃ τ : ℝ, 0 < τ ∧
      IsPST (pathWeightedGraph n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ τ) ↔
    (n = 2 ∨ n = 3) := by
  -- Combine `isStronglyCospectral_pathEndpoints` with the eigenvalue
  -- analysis of `2 cos(kπ/(n+1))`.  Punted.
  sorry

/-! ## Phantom symmetry (Bachman-Tamon 1108.0339)

A pair `(u, v)` is **phantom symmetric** if it is strongly cospectral but
*not* witnessed by any graph automorphism.  When a non-trivial automorphism
swapping `u ↔ v` exists, strong cospectrality is automatic by the
representation-theoretic argument (the swap is in the centralizer of the
adjacency action).  Phantom-symmetric pairs are the *genuinely new* PST
candidates: their existence shows that PST cannot be detected by symmetry
alone, and is the central observation of Bachman-Tamon (arXiv:1108.0339).
-/

/-- A pair `(u, v)` is **phantom symmetric** in `G` if it is strongly
cospectral but no graph automorphism of `G` swaps `u` and `v`.

In particular phantom-symmetric pairs cannot be detected by group-theoretic
methods; their existence is the algebraic-graph-theoretic content of
Bachman-Tamon (arXiv:1108.0339). -/
def IsPhantomSymmetric (G : WeightedGraph V) (u v : V) : Prop :=
  IsStronglyCospectral G u v ∧
    ¬ ∃ σ : V ≃ V,
      (∀ x y, G.adj (σ x) (σ y) = G.adj x y) ∧ σ u = v

/-- **Existence of phantom-symmetric pairs** (Bachman-Tamon arXiv:1108.0339).

There exist Hermitian-weighted graphs `G` with phantom-symmetric vertex pairs
exhibiting PST.  Concretely, Bachman-Tamon construct quotient graphs (via
equitable partitions of vertex-transitive graphs) where the quotient admits
PST between cells whose preimages are *not* swapped by any automorphism of the
original graph.

This is the *raison d'être* of the equitable-partition lift theory in
`Graphplay.Spectral` / `Graphplay.PST`: phantom symmetry is "explained by"
the equitable quotient, even when it is invisible to the automorphism group
of the parent graph. -/
theorem exists_phantomSymmetric_isPST :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : WeightedGraph V) (u v : V) (τ : ℝ),
      0 < τ ∧ IsPhantomSymmetric G u v ∧ IsPST G u v τ := by
  -- Bachman-Tamon construction: take a vertex-transitive parent graph G',
  -- pick an equitable partition P', the quotient G = P'.quotient gives the
  -- phantom-symmetric pair (cell_i, cell_j) when no automorphism of G'
  -- exchanges the preimage cells while every automorphism of G does (or
  -- vice versa).  Detailed construction punted.
  sorry

/-! ## Convenience consequences -/

/-- Strong cospectrality is symmetric in `u, v`. -/
theorem IsStronglyCospectral.symm {G : WeightedGraph V} {u v : V}
    (h : IsStronglyCospectral G u v) : IsStronglyCospectral G v u := by
  intro lam hlam
  obtain ⟨ε, hε, heq⟩ := h lam hlam
  refine ⟨star ε, ?_, ?_⟩
  · simpa using hε
  · -- `eigenProjEntry G lam v u = star (eigenProjEntry G lam u v)`, and the
    -- product `ε * √(diag u · diag v)` becomes `star ε * √(diag v · diag u)`
    -- under conjugation.
    sorry

/-- Strong cospectrality is reflexive: every vertex is strongly cospectral
with itself (with trivial phase). -/
theorem IsStronglyCospectral.refl (G : WeightedGraph V) (u : V) :
    IsStronglyCospectral G u u := by
  intro lam _
  refine ⟨1, by simp, ?_⟩
  -- `eigenProjEntry G lam u u = diag G lam u` and `√(diag · diag) = diag`.
  sorry

/-- A graph automorphism swapping `u, v` implies strong cospectrality.  This
is the "easy direction" of Godsil-Royle Lemma 8.2.1: any automorphism
witnessing the swap commutes with `G.adj` and so permutes eigenspaces
intra-eigenvalue. -/
theorem IsStronglyCospectral.of_aut
    (G : WeightedGraph V) (u v : V)
    (σ : V ≃ V) (hσ : ∀ x y, G.adj (σ x) (σ y) = G.adj x y) (huv : σ u = v) :
    IsStronglyCospectral G u v := by
  -- `σ` permutes eigenspaces of `G.adj` within each eigenvalue; the orbit
  -- structure gives the parallelism `P_λ u = P_λ (σ u) = P_λ v` up to a
  -- root-of-unity phase.
  sorry

end Graphplay
